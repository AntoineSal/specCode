"""
speccode — TUI
Terminal interface for the speccode pipeline.
"""

from __future__ import annotations

import os
import re
import select
import shutil
import subprocess
import sys
import termios
import threading
import time
import tty
from pathlib import Path

from rich.console import Console
from rich.layout import Layout
from rich.live import Live
from rich.panel import Panel
from rich.rule import Rule
from rich.syntax import Syntax
from rich.text import Text

from orchestrator import (
    LANGUAGE_CONFIGS,
    _infer_cpp_includes,
    check_stale,
    clean_lean_error,
    count_blocks,
    extract_signature,
    generate_main,
    generate_specs_md,
    init_context,
    load_api_key,
    load_context,
    parse_spec,
    run_pipeline,
    save_context,
    save_spec,
    topo_sort_specs,
)

console = Console()

SPINNERS = "⠋⠙⠹⠸⠼⠴⠦⠧⠇⠏"

CURRENT_LANGUAGE = "c++"

# Maps language key → Rich/Pygments lexer name
LANG_FENCE: dict[str, str] = {
    "c++": "cpp",
    "python": "python",
    "rust": "rust",
    "ocaml": "ocaml",
    "go": "go",
    "typescript": "typescript",
}


def _sp() -> str:
    return SPINNERS[int(time.time() * 10) % len(SPINNERS)]


def _read_key() -> str:
    """Read one keypress without waiting for Enter."""
    fd = sys.stdin.fileno()
    try:
        old = termios.tcgetattr(fd)
    except termios.error:
        return (sys.stdin.readline() or "q")[0]
    try:
        tty.setraw(fd)
        ch = sys.stdin.read(1)
    finally:
        termios.tcsetattr(fd, termios.TCSADRAIN, old)
    return ch


# ---------------------------------------------------------------------------
# Prerequisite check (silent — called once at startup)
# ---------------------------------------------------------------------------

def check_prerequisites() -> str | None:
    """Return an error message, or None if all good."""
    try:
        load_api_key()
    except RuntimeError as e:
        return str(e)
    return None


# ---------------------------------------------------------------------------
# Lean spec validation
# ---------------------------------------------------------------------------

_SORRY_WORDS = ("sorry", "declaration uses", "uses 'sorry'")


def validate_lean_spec(spec_content: str) -> tuple[bool, list[str]]:
    """
    Validate spec_content using pure Python — no lake, no subprocess.
    Returns (True, []) if valid, (False, errors) otherwise.
    """
    _LEAN_RESERVED = [
        "insert", "map", "length", "reverse", "append",
        "head", "tail", "init", "last", "get",
    ]

    # Strip single-line comments for syntactic checks
    stripped_lines = []
    for line in spec_content.splitlines():
        stripped_lines.append(re.sub(r"--.*$", "", line))
    stripped = "\n".join(stripped_lines)

    # ÉTAPE 1a — contenu non vide
    if not stripped.strip():
        return (False, ["spec is empty — add at least one `def`"])

    # ÉTAPE 1b — au moins un `def` OU un type (structure/inductive/abbrev/class)
    has_def = bool(re.search(r"^def\s+\w+", stripped, re.MULTILINE))
    has_type = bool(re.search(
        r"^(structure|inductive|abbrev|class)\s+\w+",
        stripped, re.MULTILINE
    ))
    if not has_def and not has_type:
        return (False, [
            "spec must define at least one function (`def`) "
            "or one type (`structure`, `inductive`, `class`)"
        ])

    # ÉTAPE 1d — pas de `def` sans nom
    for i, line in enumerate(stripped.splitlines(), start=1):
        if re.match(r"^\s*def\s*:=", line):
            return (False, [f"unnamed `def` on line {i} — every def must have a name"])

    # ÉTAPE 1c — chaque def/theorem/lemma doit contenir sorry
    block_pattern = re.compile(r"^(def|theorem|lemma)\s+\w+", re.MULTILINE)
    for m in block_pattern.finditer(stripped):
        line_no = stripped[: m.start()].count("\n") + 1
        keyword = m.group(1)
        name = m.group(0).split()[1]
        # Extraire le corps du bloc jusqu'au prochain bloc ou fin de fichier
        rest = stripped[m.start():]
        next_block = re.search(r"\n(?:def|theorem|lemma|#|end)\s+", rest[1:])
        body = rest[: next_block.start() + 1] if next_block else rest
        if not re.search(r":=\s*by\s+sorry|:=\s*sorry|\bsorry\b", body):
            return (False, [
                f"`{keyword} {name}` on line {line_no} is missing `:= sorry` "
                f"— stubs must not be fully implemented"
            ])

    # ÉTAPE 1e — parenthèses et crochets équilibrés
    depth_paren = 0
    depth_bracket = 0
    for i, line in enumerate(stripped.splitlines(), start=1):
        for ch in line:
            if ch == "(":
                depth_paren += 1
            elif ch == ")":
                depth_paren -= 1
                if depth_paren < 0:
                    return (False, [f"unbalanced parentheses on line {i}"])
            elif ch == "[":
                depth_bracket += 1
            elif ch == "]":
                depth_bracket -= 1
                if depth_bracket < 0:
                    return (False, [f"unbalanced brackets on line {i}"])
    if depth_paren != 0:
        return (False, ["unbalanced parentheses — check for missing `)`"])
    if depth_bracket != 0:
        return (False, ["unbalanced brackets — check for missing `]`"])

    # ÉTAPE 2a — les imports doivent être avant tout def/theorem
    first_def = re.search(r"^(?:def|theorem|lemma)\s+", spec_content, re.MULTILINE)
    if first_def:
        late_import = re.search(r"^import\s+", spec_content[first_def.start():], re.MULTILINE)
        if late_import:
            abs_pos = first_def.start() + late_import.start()
            line_no = spec_content[:abs_pos].count("\n") + 1
            return (False, [f"`import` on line {line_no} must appear before any `def` or `theorem`"])

    # ÉTAPE 2b — noms réservés (warning non bloquant, ignoré ici)
    # (pas d'erreur retournée)

    return (True, [])


def _strip_error_header(content: str) -> str:
    """Remove injected '-- ✗' error lines from the top of the content."""
    lines = content.splitlines(keepends=True)
    i = 0
    while i < len(lines) and lines[i].startswith("-- ✗"):
        i += 1
    return "".join(lines[i:]).strip()


def _inject_errors_into_file(path: Path, spec_content: str, errors: list[str]) -> None:
    """Prepend '-- ✗ ...' error lines to the spec file so the editor shows them."""
    parts = [f"-- ✗ {err}\n" for err in errors]
    parts.append("\n")
    parts.append(spec_content)
    path.write_text("".join(parts), encoding="utf-8")


# ---------------------------------------------------------------------------
# Shared display state
# ---------------------------------------------------------------------------

class DisplayState:
    """
    All mutable state for the live display, protected by a lock.
    Transitions: input → generating → done / error
    """

    def __init__(self):
        self._lock = threading.Lock()
        # spec content displayed in the left panel during generation
        self.spec_lines: list[str] = []
        # phase: "generating" | "done" | "error"
        self.phase = "generating"
        # generation phase
        self.stream_buf = ""
        self.start_time = 0.0
        self.retry_msg: str | None = None
        self.lang_fence = "cpp"
        # done phase
        self.code = ""
        self.code_path = ""
        self.spec_path = ""
        self.cost_total = 0.0
        self.tokens = 0
        self.duration = 0.0
        self.fn_name = ""
        # error phase
        self.error_msg = ""
        # validation phase
        self.validation_state: str | None = None  # None | "validating" | "valid" | "invalid"
        self.validation_errors: list[str] = []

    def handle_event(self, name: str, data: dict) -> None:
        with self._lock:
            if name == "generating":
                self.phase = "generating"
                self.stream_buf = ""
                self.start_time = time.time()
                self.retry_msg = None
            elif name == "streaming":
                self.stream_buf += data.get("chunk", "")
            elif name == "api_retry":
                status = data.get("status") or "timeout"
                wait = data["wait"]
                attempt = data["attempt"]
                max_r = data["max_retries"]
                self.retry_msg = (
                    f"API error ({status}) — retrying in {wait}s "
                    f"(attempt {attempt}/{max_r})..."
                )
            elif name == "done":
                self.phase = "done"
                self.code = data.get("code", "")
                self.fn_name = data.get("fn_name", "output")
                out = data.get("output_dir", ".")
                lang_ext = data.get("lang_ext", ".cpp")
                self.lang_fence = data.get("lang_fence", "cpp")
                self.code_path = data.get(
                    "src_file",
                    str(Path(out) / "src" / f"{self.fn_name}{lang_ext}"),
                )
                self.spec_path = data.get(
                    "spec_file",
                    str(Path(out) / "specs" / f"{self.fn_name}.lean"),
                )
                cost = data.get("cost", {})
                self.cost_total = cost.get("cost_total", 0.0)
                self.tokens = cost.get("codestral_tokens", 0)
                self.duration = time.time() - self.start_time
                self.retry_msg = None
            elif name == "error":
                self.phase = "error"
                self.error_msg = data.get("message", "Unknown error")
                self.duration = time.time() - self.start_time if self.start_time else 0.0

    # -- Renderers -----------------------------------------------------------

    def render_input_panel(self) -> Panel:
        with self._lock:
            lines = list(self.spec_lines)
            vstate = self.validation_state
            validation_errors = list(self.validation_errors)

        if lines:
            spec_text = "\n".join(lines)
            content = Syntax(spec_text, "text", theme="monokai",
                             word_wrap=True, background_color="default")
        else:
            content = Text("  Loading spec…\n", style="dim")

        if vstate == "validating":
            border = "rgb(100,140,180)"
            title = "[rgb(100,140,180)]spec — validating...[/rgb(100,140,180)]"
        elif vstate == "valid":
            border = "bright_green"
            title = "[bright_green]spec[/bright_green]"
        elif vstate == "invalid":
            border = "bright_red"
            title = "[bright_red]spec[/bright_red]"
            if validation_errors:
                err_text = Text("\n")
                for e in validation_errors:
                    err_text.append(f"  ✗ {e}\n", style="bright_red")
                from rich.console import Group
                content = Group(content, err_text)
        else:
            border = "dim"
            title = "[dim]spec[/dim]"

        return Panel(content, title=title, border_style=border)

    def render_output_panel(self) -> Panel:
        with self._lock:
            phase = self.phase
            buf = self.stream_buf
            code = self.code
            lang_fence = self.lang_fence
            elapsed = time.time() - self.start_time if self.start_time else 0.0
            retry = self.retry_msg
            cost = self.cost_total
            tokens = self.tokens
            dur = self.duration
            fn_name = self.fn_name
            err = self.error_msg
            vstate = self.validation_state

        if vstate in (None, "validating"):
            return Panel("", title="[dim]output[/dim]", border_style="dim")

        if vstate == "invalid":
            msg = Text()
            msg.append("✗ invalid spec — fix errors and try again", style="bright_red bold")
            return Panel(msg, title="[bright_red]output[/bright_red]", border_style="bright_red")

        if phase == "generating":
            header = Text()
            header.append(f"{_sp()} ", style="rgb(100,140,180)")
            header.append("Codestral is generating…", style="rgb(100,140,180) bold")
            header.append(f"  [{elapsed:.1f}s]\n\n", style="dim")
            if retry:
                header.append(f"  {retry}\n\n", style="yellow")

            if buf.strip():
                try:
                    code_display = Syntax(
                        buf, lang_fence, theme="monokai",
                        word_wrap=True, background_color="default",
                    )
                    from rich.console import Group
                    content = Group(header, code_display)
                except Exception:
                    header.append(buf, style="white")
                    content = header
            else:
                content = header

            return Panel(content, title="[rgb(100,140,180)]OUTPUT[/rgb(100,140,180)]", border_style="rgb(100,140,180)")

        if phase == "done":
            try:
                code_display = Syntax(
                    code, lang_fence, theme="monokai",
                    word_wrap=True, background_color="default",
                )
            except Exception:
                code_display = Text(code, style="white")

            status = Text()
            status.append("\n")
            status.append("✓ ", style="green bold")
            status.append(
                f"saved to src/{fn_name}  │  ${cost:.4f}  │  {dur:.1f}s",
                style="dim",
            )

            from rich.console import Group
            content = Group(code_display, status)
            return Panel(content, title="[bright_green]OUTPUT[/bright_green]", border_style="bright_green")

        # error
        content = Text()
        content.append("✗ ", style="bright_red bold")
        content.append(err, style="red")
        return Panel(content, title="[bright_red]ERROR[/bright_red]", border_style="bright_red")


# ---------------------------------------------------------------------------
# Layout builder
# ---------------------------------------------------------------------------

class _Renderable:
    """
    Thin wrapper so Rich Live can auto-refresh the display without explicit
    live.update() calls: __rich_console__ is invoked on every timer tick.
    """
    def __init__(self, state: DisplayState, stacked: bool):
        self._state = state
        self._stacked = stacked

    def __rich_console__(self, console, options):
        yield build_renderable(self._state, self._stacked)


def build_renderable(state: DisplayState, stacked: bool):
    input_panel = state.render_input_panel()
    output_panel = state.render_output_panel()

    if stacked:
        from rich.console import Group
        return Group(input_panel, output_panel)
    else:
        layout = Layout()
        layout.split_row(
            Layout(input_panel, name="input", ratio=45),
            Layout(output_panel, name="output", ratio=55),
        )
        return layout


# ---------------------------------------------------------------------------
# Menu prompts
# ---------------------------------------------------------------------------

def _print_intro() -> None:
    """One-time startup banner with figlet ASCII art identity."""
    _SPEC_HALVES = [
        "░██████╗██████╗░███████╗░█████╗░",
        "██╔════╝██╔══██╗██╔════╝██╔══██╗",
        "╚█████╗░██████╔╝█████╗░░██║░░╚═╝",
        "░╚═══██╗██╔═══╝░██╔══╝░░██║░░██╗",
        "██████╔╝██║░░░░░███████╗╚█████╔╝",
        "╚═════╝░╚═╝░░░░░╚══════╝░╚════╝░",
    ]
    _CODE_HALVES = [
        "░█████╗░░█████╗░██████╗░███████╗",
        "██╔══██╗██╔══██╗██╔══██╗██╔════╝",
        "██║░░╚═╝██║░░██║██║░░██║█████╗░░",
        "██║░░██╗██║░░██║██║░░██║██╔══╝░░",
        "╚█████╔╝╚█████╔╝██████╔╝███████╗",
        "░╚════╝░░╚════╝░╚═════╝░╚══════╝",
    ]
    deco = "color(69)"
    art_width = 66  # 32 (SPEC) + 2 (gap) + 32 (CODE)
    subtitle = "formally verified code from lean specifications"
    term_width, _ = shutil.get_terminal_size()
    pad = " " * max(0, (term_width - art_width) // 2)
    sub_pad = " " * max(0, (term_width - len(subtitle)) // 2)
    console.print()
    for s, c in zip(_SPEC_HALVES, _CODE_HALVES):
        line = Text(pad)
        for ch in s:
            line.append(ch, style="bold bright_white" if ch == "█" else deco)
        line.append("  ")
        for ch in c:
            line.append(ch, style="bold rgb(100,140,180)" if ch == "█" else deco)
        console.print(line)
    console.print()
    console.print(f"{sub_pad}[dim italic]{subtitle}[/dim italic]")
    console.print()


_menu_line_count: int = 0


def render_menu(project_dir: Path) -> str:
    """
    Load context, display project header + menu, wait for a keypress.
    Returns: 'edit', 'language', 'project', 'rebuild', or 'quit'.
    Updates CURRENT_LANGUAGE from context if available.
    """
    global CURRENT_LANGUAGE, _menu_line_count

    context = load_context(project_dir)
    has_context = context is not None
    n = 0

    if has_context:
        CURRENT_LANGUAGE = context.get("language", CURRENT_LANGUAGE)
        project_name = context.get("project", project_dir.name)
        all_entries = context.get("functions", [])
        n_total = len(all_entries)
        n_types = sum(1 for e in all_entries if e.get("kind") == "type")
        n_functions = n_total - n_types
        language = context.get("language", CURRENT_LANGUAGE)

        console.print(); n += 1
        header = Text("  ")
        header.append("◆ ", style="bold rgb(100,140,180)")
        header.append(project_name, style="bold bright_white")
        console.print(header); n += 1

        stats = Text("    ")
        stats.append(
            f"{n_total} specs  ·  {n_types} types  ·  {n_functions} functions  ·  {language}",
            style="dim",
        )
        console.print(stats); n += 1
    else:
        console.print(); n += 1
        no_proj = Text("  ")
        no_proj.append("◆ ", style="bold rgb(100,140,180)")
        no_proj.append("new project", style="dim")
        console.print(no_proj); n += 1

    # Build menu line
    items = [("e", "new spec")]
    if has_context:
        items += [("m", "modify"), ("b", "build"), ("p", "project"),
                  ("g", "generate main"), ("x", "run main")]
    items += [("l", "language"), ("q", "quit")]

    menu_text = Text("  ")
    for i, (key, label) in enumerate(items):
        if i > 0:
            menu_text.append("   ", style="dim")
        menu_text.append(f"[{key}]", style="rgb(100,140,180)")
        menu_text.append(f" {label}", style="dim")

    console.print(); n += 1
    console.print(menu_text); n += 1
    console.print(); n += 1

    _menu_line_count = n

    while True:
        try:
            key = _read_key()
        except (EOFError, KeyboardInterrupt):
            return "quit"
        if key in ("e", "E", "\r", "\n"):
            return "edit"
        if key in ("m", "M") and has_context:
            return "modify"
        if key in ("l", "L"):
            return "language"
        if key in ("p", "P") and has_context:
            return "project"
        if key in ("b", "B") and has_context:
            return "build"
        if key in ("g", "G") and has_context:
            return "generate_main"
        if key in ("x", "X") and has_context:
            return "run_main"
        if key in ("q", "Q", "\x03", "\x04"):  # q, Ctrl+C, Ctrl+D
            return "quit"
        # unknown key: wait for next


def _prompt_language() -> str:
    """Display language selector with ANSI navigation. Returns selected language."""
    lang_entries = [
        ("1", "c++"),
        ("2", "python"),
        ("3", "rust"),
        ("4", "ocaml"),
        ("5", "go"),
        ("6", "typescript"),
    ]
    current = CURRENT_LANGUAGE
    idx = next((i for i, (_, l) in enumerate(lang_entries) if l == current), 0)

    def render(i: int) -> list[str]:
        lines = [""]
        lines.append("  select language")
        lines.append("")
        for j, (key, lang) in enumerate(lang_entries):
            if j == i:
                lines.append(f"  \x1b[97;1m→ [{key}] {lang:<15}\x1b[0m")
            else:
                lines.append(f"  \x1b[2m  [{key}] {lang:<15}\x1b[0m")
        lines.append("")
        lines.append("  \x1b[2m↑↓ or key   Enter select   q cancel\x1b[0m")
        lines.append("")
        return lines

    lines = render(idx)
    for line in lines:
        sys.stdout.write(line + "\n")
    sys.stdout.flush()
    n_lines = len(lines)

    selected = None
    while True:
        key = _read_key_safe()
        if key in ("\x1b[A", "k"):
            idx = (idx - 1) % len(lang_entries)
        elif key in ("\x1b[B", "j"):
            idx = (idx + 1) % len(lang_entries)
        elif key == "\r":
            selected = lang_entries[idx][1]
            break
        elif key in ("q", "Q", "\x03"):
            break
        else:
            for i, (k, lang) in enumerate(lang_entries):
                if key == k:
                    selected = lang
                    idx = i
                    break
            if selected:
                break
            continue

        sys.stdout.write(f"\x1b[{n_lines}A\x1b[0J")
        lines = render(idx)
        for line in lines:
            sys.stdout.write(line + "\n")
        sys.stdout.flush()

    sys.stdout.write(f"\x1b[{n_lines}A\x1b[0J")
    sys.stdout.flush()
    return selected if selected else CURRENT_LANGUAGE


# ---------------------------------------------------------------------------
# Modify spec action
# ---------------------------------------------------------------------------

def _read_key_safe() -> str:
    """Read one keypress via /dev/tty; returns arrow sequences or decoded char."""
    with open("/dev/tty", "rb", buffering=0) as tty_f:
        fd = tty_f.fileno()
        old = termios.tcgetattr(fd)
        try:
            tty.setraw(fd)
            ch = tty_f.read(1)
            if ch == b"\x1b":
                seq = ch
                r, _, _ = select.select([tty_f], [], [], 0.1)
                if r:
                    seq += tty_f.read(1)
                    r2, _, _ = select.select([tty_f], [], [], 0.05)
                    if r2:
                        seq += tty_f.read(1)
                if seq == b"\x1b[A":
                    return "\x1b[A"
                if seq == b"\x1b[B":
                    return "\x1b[B"
                if seq == b"\x1b[C":
                    return "\x1b[C"
                if seq == b"\x1b[D":
                    return "\x1b[D"
                return "IGNORED"
            return ch.decode("utf-8", errors="replace")
        finally:
            termios.tcsetattr(fd, termios.TCSADRAIN, old)


def _build_spec_list(entries: list, idx: int) -> Panel:
    content = Text()
    content.append("  select spec to modify\n\n", style="dim")
    for j, entry in enumerate(entries):
        name = entry.get("name", "?")
        spec_file = entry.get("spec_file", f"specs/{name}.lean")
        if j == idx:
            content.append("  → ", style="rgb(100,140,180) bold")
            content.append(f"{name:<20}", style="bright_white")
            content.append(f"  {spec_file}\n", style="dim")
        else:
            content.append(f"    {name:<20}  {spec_file}\n", style="dim")
    content.append("\n  ↑↓   Enter select   q cancel", style="dim")
    return Panel(content, border_style="dim")


def _action_modify_spec(context: dict, project_dir: Path) -> None:
    """Show navigable spec list, open editor on selection, update hash."""
    entries = [e for e in context.get("functions", []) if e.get("kind") != "demo"]
    if not entries:
        console.print("  [yellow]No specs found.[/yellow]")
        return

    idx = 0

    def render(i: int) -> list[str]:
        lines = [""]
        lines.append("  select spec to modify")
        lines.append("")
        for j, entry in enumerate(entries):
            name = entry.get("name", "?")
            spec_file = entry.get("spec_file", f"specs/{name}.lean")
            if j == i:
                lines.append(f"  \x1b[97;1m→ {name:<20}  {spec_file}\x1b[0m")
            else:
                lines.append(f"  \x1b[2m  {name:<20}  {spec_file}\x1b[0m")
        lines.append("")
        lines.append("  \x1b[2m↑↓   Enter select   q cancel\x1b[0m")
        lines.append("")
        return lines

    lines = render(idx)
    for line in lines:
        sys.stdout.write(line + "\n")
    sys.stdout.flush()
    n_lines = len(lines)

    while True:
        key = _read_key_safe()
        if key in ("\x1b[A", "k"):
            idx = (idx - 1) % len(entries)
        elif key in ("\x1b[B", "j"):
            idx = (idx + 1) % len(entries)
        elif key == "\r":
            break
        elif key in ("q", "Q", "\x03"):
            idx = -1
            break
        else:
            continue

        sys.stdout.write(f"\x1b[{n_lines}A\x1b[0J")
        lines = render(idx)
        for line in lines:
            sys.stdout.write(line + "\n")
        sys.stdout.flush()

    sys.stdout.write(f"\x1b[{n_lines}A\x1b[0J")
    sys.stdout.flush()

    if idx == -1:
        return

    spec_path = project_dir / entries[idx].get("spec_file", f"specs/{entries[idx]['name']}.lean")
    if not spec_path.exists():
        console.print(f"  [red]Spec file not found: {spec_path}[/red]")
        return

    editor = os.environ.get("EDITOR", "nano")
    try:
        subprocess.run([editor, str(spec_path)])
    except FileNotFoundError:
        console.print(f"  [red]Editor not found: {editor}[/red]")
        return

    new_content = spec_path.read_text(encoding="utf-8")
    language = context.get("language", "c++")
    save_spec(new_content, project_dir, language)

    console.print("  [green]✓ spec updated — run [b] to build[/green]")
    time.sleep(1.5)


# ---------------------------------------------------------------------------
# Build submenu
# ---------------------------------------------------------------------------

_BUILD_ALL = "__build_all__"
_GEN_MAIN  = "__generate_main__"


def _spec_status(entry: dict, project_dir: Path) -> tuple[str, str]:
    """Return (icon, ansi_color) reflecting the build status of a spec entry."""
    code_file = entry.get("code_file", "")
    if not code_file or not (project_dir / code_file).exists():
        return "○", "\x1b[2m"        # no code yet
    if entry.get("stale"):
        return "~", "\x1b[33m"       # stale (spec changed after last build)
    return "✓", "\x1b[32m"           # up to date


def _action_build_menu(context: dict, project_dir: Path, language: str, stacked: bool) -> None:
    """Interactive build submenu: pick a spec, generate main, or build all."""
    spec_entries = [e for e in context.get("functions", []) if e.get("kind") != "demo"]

    # All navigable items: specs + separator-specials
    items: list[dict] = spec_entries + [
        {"name": _GEN_MAIN,  "_label": "generate main"},
        {"name": _BUILD_ALL, "_label": "build all"},
    ]

    idx = 0

    def render(i: int) -> list[str]:
        lines = ["", "  build", ""]
        for j, item in enumerate(items):
            sel = (j == i)
            arrow = "→ " if sel else "  "
            dim_on  = "\x1b[97;1m" if sel else "\x1b[2m"
            dim_off = "\x1b[0m"

            if "_label" in item:
                # Separator before special items
                if j == len(spec_entries):
                    lines.append("")
                lines.append(f"  {dim_on}{arrow}{item['_label']}{dim_off}")
            else:
                icon, col = _spec_status(item, project_dir)
                name = item.get("name", "?")
                spec_file = item.get("spec_file", f"specs/{name}.lean")
                icon_str = f"{col}{icon}\x1b[0m"
                lines.append(f"  {dim_on}{arrow}{dim_off}{icon_str}  {dim_on}{name:<20}{dim_off}  \x1b[2m{spec_file}\x1b[0m")

        lines.append("")
        lines.append("  \x1b[2m↑↓   Enter select   q cancel\x1b[0m")
        lines.append("")
        return lines

    lines = render(idx)
    for line in lines:
        sys.stdout.write(line + "\n")
    sys.stdout.flush()
    n_lines = len(lines)

    selected: dict | None = None
    while True:
        key = _read_key_safe()
        if key in ("\x1b[A", "k"):
            idx = (idx - 1) % len(items)
        elif key in ("\x1b[B", "j"):
            idx = (idx + 1) % len(items)
        elif key == "\r":
            selected = items[idx]
            break
        elif key in ("q", "Q", "\x03"):
            break
        else:
            continue
        sys.stdout.write(f"\x1b[{n_lines}A\x1b[0J")
        lines = render(idx)
        for line in lines:
            sys.stdout.write(line + "\n")
        sys.stdout.flush()

    sys.stdout.write(f"\x1b[{n_lines}A\x1b[0J")
    sys.stdout.flush()

    if selected is None:
        return

    name = selected["name"]

    if name == _GEN_MAIN:
        ctx = load_context(project_dir)
        if ctx:
            _action_generate_main(ctx, project_dir, language)

    elif name == _BUILD_ALL:
        ctx = load_context(project_dir)
        if not ctx:
            return
        ordered = topo_sort_specs(ctx)
        console.print(f"  [rgb(100,140,180)]Building {len(ordered)} spec(s)...[/rgb(100,140,180)]")
        for fn in ordered:
            fn_name = fn["name"]
            spec_path = project_dir / fn.get("spec_file", f"specs/{fn_name}.lean")
            if not spec_path.exists():
                console.print(f"  [yellow]skip {fn_name}: spec not found[/yellow]")
                continue
            console.print(f"  [dim]→ {fn_name}[/dim]")
            state = DisplayState()
            validate_and_generate(spec_path.read_text(encoding="utf-8"), state, stacked, language)
        ctx = load_context(project_dir)
        if ctx and any(f.get("kind") != "demo" for f in ctx.get("functions", [])):
            console.print("  [dim]→ main[/dim]")
            _action_generate_main(ctx, project_dir, language)
        ctx = load_context(project_dir)
        fn_count = len([f for f in ctx.get("functions", []) if f.get("kind") != "demo"]) if ctx else 0
        console.print(f"  [green]✓ build all done — {fn_count} spec(s) + main[/green]")

    else:
        # Single spec
        spec_path = project_dir / selected.get("spec_file", f"specs/{name}.lean")
        if not spec_path.exists():
            console.print(f"  [red]Spec not found: {spec_path}[/red]")
            return
        console.print(f"  [dim]→ {name}[/dim]")
        state = DisplayState()
        validate_and_generate(spec_path.read_text(encoding="utf-8"), state, stacked, language)


# ---------------------------------------------------------------------------
# Generate main action
# ---------------------------------------------------------------------------

def _action_generate_main(context: dict, project_dir: Path, language: str) -> None:
    """Stream-generate src/main.{ext} and display in a live panel."""
    cfg = LANGUAGE_CONFIGS.get(language, LANGUAGE_CONFIGS["c++"])
    lang_fence = LANG_FENCE.get(language, "cpp")
    ext = cfg["ext"]

    buf: list[str] = []
    done_event = threading.Event()
    error_holder: list[str] = []
    start = time.time()

    def on_chunk(chunk: str):
        buf.append(chunk)

    def _run():
        try:
            generate_main(context, project_dir, language, on_chunk=on_chunk)
        except Exception as exc:
            error_holder.append(str(exc))
        finally:
            done_event.set()

    class _Render:
        def __rich_console__(self, c, opts):
            code = "".join(buf)
            elapsed = time.time() - start
            if error_holder:
                msg = Text()
                msg.append("✗ ", style="bright_red bold")
                msg.append(error_holder[0], style="red")
                yield Panel(msg, title="[bright_red]error[/bright_red]", border_style="bright_red")
                return
            is_done = done_event.is_set()
            header = Text()
            if is_done:
                header.append("✓ ", style="green bold")
                header.append(f"src/main{ext} saved  │  {elapsed:.1f}s\n\n", style="dim")
            else:
                header.append(f"{_sp()} ", style="rgb(100,140,180)")
                header.append("Generating main…", style="rgb(100,140,180) bold")
                header.append(f"  [{elapsed:.1f}s]\n\n", style="dim")
            if code.strip():
                try:
                    from rich.console import Group
                    yield Panel(
                        Group(header, Syntax(code, lang_fence, theme="monokai",
                                             word_wrap=True, background_color="default")),
                        title="[bright_green]main[/bright_green]" if is_done else "[rgb(100,140,180)]main[/rgb(100,140,180)]",
                        border_style="bright_green" if is_done else "rgb(100,140,180)",
                    )
                except Exception:
                    header.append(code)
                    yield Panel(header, title="main", border_style="dim")
            else:
                yield Panel(header, title="main", border_style="dim")

    t = threading.Thread(target=_run, daemon=True)
    t.start()

    with Live(_Render(), console=console, refresh_per_second=15, transient=False):
        done_event.wait()

    t.join()


# ---------------------------------------------------------------------------
# Run main action
# ---------------------------------------------------------------------------

def _repair_cpp_headers(src_dir: Path) -> None:
    """
    For each src/*.cpp (except main), ensure a self-contained .hpp exists
    with the proper #include directives inferred from the signature.
    Repairs files generated before this fix was in place.
    """
    for cpp_file in sorted(src_dir.glob("*.cpp")):
        if cpp_file.stem == "main":
            continue
        try:
            code = cpp_file.read_text(encoding="utf-8")
        except OSError:
            continue
        sig = extract_signature(code, "c++")
        if not sig:
            continue
        hpp_file = src_dir / f"{cpp_file.stem}.hpp"
        includes = _infer_cpp_includes(sig)
        include_block = "".join(f"#include {h}\n" for h in includes)
        new_content = f"// Auto-generated by speccode\n#pragma once\n{include_block}{sig};\n"
        current = hpp_file.read_text(encoding="utf-8") if hpp_file.exists() else ""
        if new_content != current:
            hpp_file.write_text(new_content, encoding="utf-8")


def _ocaml_topo_sort(files: list[Path]) -> list[Path]:
    """
    Return OCaml source files sorted so each file comes after its dependencies.
    Dependency is detected via `open Modulename` statements.
    Main is always placed last.
    """
    # OCaml module name: first char uppercased, rest unchanged
    def mod_name(f: Path) -> str:
        s = f.stem
        return s[0].upper() + s[1:]

    mod_to_file: dict[str, Path] = {mod_name(f): f for f in files}

    # Build deps: stem -> list of stems this file opens
    deps: dict[str, list[str]] = {f.stem: [] for f in files}
    for f in files:
        try:
            content = f.read_text(encoding="utf-8")
        except OSError:
            continue
        for opened in re.findall(r"^open\s+(\w+)", content, re.MULTILINE):
            dep = mod_to_file.get(opened)
            if dep and dep.stem != f.stem:
                deps[f.stem].append(dep.stem)

    ordered: list[Path] = []
    visited: set[str] = set()
    in_progress: set[str] = set()

    def visit(stem: str) -> None:
        if stem in visited or stem in in_progress:
            return
        in_progress.add(stem)
        for dep in deps.get(stem, []):
            visit(dep)
        in_progress.discard(stem)
        visited.add(stem)
        for f in files:
            if f.stem == stem:
                ordered.append(f)
                break

    for f in files:
        visit(f.stem)

    # Guarantee main is last regardless of open statements
    non_main = [f for f in ordered if f.stem != "main"]
    main_files = [f for f in ordered if f.stem == "main"]
    return non_main + main_files


def _action_run_main(context: dict, project_dir: Path, language: str) -> None:
    """Compile (if needed) and run src/main.{ext}, display output or error."""
    cfg = LANGUAGE_CONFIGS.get(language, LANGUAGE_CONFIGS["c++"])
    ext = cfg["ext"]
    src_dir = project_dir / "src"
    main_file = src_dir / f"main{ext}"

    if not main_file.exists():
        console.print(f"  [yellow]No main file found ({main_file.relative_to(project_dir)})[/yellow]")
        console.print("  [dim]Run [g] generate main first.[/dim]")
        return

    tmp_bin = "/tmp/speccode_main_bin"

    # Map language → (required binary, install hint)
    _REQUIRED = {
        "c++":        ("g++",      "brew install gcc"),
        "python":     ("python3",  "brew install python"),
        "rust":       ("rustc",    "curl https://sh.rustup.rs -sSf | sh"),
        "go":         ("go",       "brew install go"),
        "ocaml":      ("ocamlopt", "brew install ocaml"),
        "typescript": ("npx",      "brew install node"),
    }
    if language in _REQUIRED:
        binary, hint = _REQUIRED[language]
        if not shutil.which(binary):
            console.print(f"  [red]{binary} not found.[/red]  [dim]Install with: {hint}[/dim]")
            return

    try:
        if language == "c++":
            _repair_cpp_headers(src_dir)
            cpp_files = sorted(src_dir.glob("*.cpp"))
            if not cpp_files:
                console.print("  [red]No .cpp files found in src/[/red]")
                return
            compile_result = subprocess.run(
                ["g++", "-std=c++17", f"-I{src_dir}"] + [str(f) for f in cpp_files] + ["-o", tmp_bin],
                capture_output=True, text=True, cwd=str(project_dir),
            )
            if compile_result.returncode != 0:
                err = compile_result.stderr or compile_result.stdout or "(no output)"
                console.print(Panel(err.strip(), title="[bright_red]compile error[/bright_red]",
                                    border_style="bright_red"))
                return
            run_result = subprocess.run([tmp_bin], capture_output=True, text=True, timeout=30)

        elif language == "python":
            run_result = subprocess.run(
                ["python3", str(main_file)],
                capture_output=True, text=True, cwd=str(project_dir), timeout=30,
            )

        elif language == "rust":
            # rustc only takes one crate entry point; main.rs must declare
            # the other modules with `mod name;` (generated by _build_main_imports).
            compile_result = subprocess.run(
                ["rustc", "--edition", "2021", str(main_file), "-o", tmp_bin],
                capture_output=True, text=True, cwd=str(src_dir),
            )
            if compile_result.returncode != 0:
                err = compile_result.stderr or compile_result.stdout or "(no output)"
                console.print(Panel(err.strip(), title="[bright_red]compile error[/bright_red]",
                                    border_style="bright_red"))
                return
            run_result = subprocess.run([tmp_bin], capture_output=True, text=True, timeout=30)

        elif language == "go":
            go_files = sorted(src_dir.glob("*.go"))
            run_result = subprocess.run(
                ["go", "run"] + [str(f) for f in go_files],
                capture_output=True, text=True, cwd=str(project_dir), timeout=30,
            )

        elif language == "ocaml":
            ml_files = sorted(src_dir.glob("*.ml"))
            ordered = _ocaml_topo_sort(ml_files)
            compile_result = subprocess.run(
                ["ocamlopt"] + [str(f) for f in ordered] + ["-o", tmp_bin],
                capture_output=True, text=True, cwd=str(project_dir),
            )
            if compile_result.returncode != 0:
                err = compile_result.stderr or compile_result.stdout or "(no output)"
                console.print(Panel(err.strip(), title="[bright_red]compile error[/bright_red]",
                                    border_style="bright_red"))
                return
            run_result = subprocess.run([tmp_bin], capture_output=True, text=True, timeout=30)

        elif language == "typescript":
            run_result = subprocess.run(
                ["npx", "ts-node", str(main_file)],
                capture_output=True, text=True, cwd=str(project_dir), timeout=60,
            )

        else:
            console.print(f"  [yellow]Run not supported for language: {language}[/yellow]")
            return

        if run_result.returncode == 0:
            output = run_result.stdout or "(no output)"
            console.print(Panel(output.strip(), title="[bright_green]output[/bright_green]",
                                border_style="bright_green"))
        else:
            err = run_result.stderr or run_result.stdout or "(no output)"
            console.print(Panel(err.strip(), title="[bright_red]runtime error[/bright_red]",
                                border_style="bright_red"))

    except subprocess.TimeoutExpired:
        console.print("  [red]Timeout: execution exceeded time limit.[/red]")
    except FileNotFoundError as exc:
        console.print(f"  [red]Command not found: {exc.filename}[/red]")
    except Exception as exc:
        console.print(f"  [red]Error: {exc}[/red]")


# ---------------------------------------------------------------------------
# Main run function
# ---------------------------------------------------------------------------

def run_once() -> str | None:
    """
    Open $EDITOR (or nano) on /tmp/speccode_input.lean.
    Returns raw file content (may include injected error comments), or None if editor not found.
    """
    tmp = Path("/tmp/speccode_input.lean")
    if not tmp.exists():
        tmp.write_text("", encoding="utf-8")

    editor = os.environ.get("EDITOR", "nano")
    console.print("[dim]Opening editor... (save and close to generate)[/dim]")
    try:
        subprocess.run([editor, str(tmp)])
    except FileNotFoundError:
        console.print(f"[red]Editor not found: {editor}[/red]")
        return None

    return tmp.read_text(encoding="utf-8") if tmp.exists() else ""


def generate(spec: str, state: DisplayState, stacked: bool, language: str = "c++") -> None:
    """Generation phase: streaming output with live display."""
    with state._lock:
        state.spec_lines = spec.splitlines()
        state.lang_fence = LANG_FENCE.get(language, "cpp")

    pipeline_done = threading.Event()

    def pipeline_thread():
        run_pipeline(
            spec,
            on_event=state.handle_event,
            target_language=language,
            project_dir=Path.cwd(),
        )
        pipeline_done.set()

    t = threading.Thread(target=pipeline_thread, daemon=True)
    t.start()

    with Live(
        _Renderable(state, stacked),
        console=console,
        refresh_per_second=15,
        transient=False,
    ) as live:
        pipeline_done.wait()
        live.update(build_renderable(state, stacked))  # final frame

    t.join()


def validate_and_generate(content: str, state: DisplayState, stacked: bool, language: str) -> str:
    """
    Validates the spec then, if valid, generates code — all within one Live layout.
    Returns "invalid" | "done" | "error".
    """
    with state._lock:
        state.spec_lines = content.splitlines()
        state.lang_fence = LANG_FENCE.get(language, "cpp")
        state.validation_state = "validating"

    validation_done = threading.Event()
    pipeline_done = threading.Event()
    validation_result: dict = {"valid": False, "errors": []}

    def _validate():
        v, e = validate_lean_spec(content)
        validation_result["valid"] = v
        validation_result["errors"] = e
        validation_done.set()

    def _pipeline():
        run_pipeline(
            content,
            on_event=state.handle_event,
            target_language=language,
            project_dir=Path.cwd(),
        )
        pipeline_done.set()

    with Live(
        _Renderable(state, stacked),
        console=console,
        refresh_per_second=15,
        transient=False,
    ) as live:
        vt = threading.Thread(target=_validate, daemon=True)
        vt.start()
        validation_done.wait()
        vt.join()

        valid = validation_result["valid"]
        errors = validation_result["errors"]

        with state._lock:
            state.validation_state = "valid" if valid else "invalid"
            state.validation_errors = errors

        live.update(build_renderable(state, stacked))

        if not valid:
            time.sleep(1.5)
            return "invalid"

        time.sleep(0.3)  # brief green flash before generation

        pt = threading.Thread(target=_pipeline, daemon=True)
        pt.start()
        pipeline_done.wait()
        live.update(build_renderable(state, stacked))
        pt.join()

    return state.phase  # "done" or "error"


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

def main():
    global CURRENT_LANGUAGE

    # Check prerequisites before anything
    err = check_prerequisites()
    if err:
        console.print(Panel(
            f"[red]{err}[/red]\nSet MISTRAL_API_KEY in .env",
            title="[red]Missing API Key[/red]",
            border_style="red",
        ))
        sys.exit(1)

    # Determine layout
    _, rows = shutil.get_terminal_size()
    stacked = rows > 40

    _print_intro()

    # Load project context
    project_dir = Path.cwd()
    context = load_context(project_dir)

    next_action: str | None = None
    has_validation_errors = False

    try:
        while True:
            if next_action is None:
                action = render_menu(project_dir)
                if _menu_line_count > 0:
                    sys.stdout.write(f"\x1b[{_menu_line_count}A\x1b[0J")
                    sys.stdout.flush()
            else:
                action, next_action = next_action, None

            if action == "quit":
                break

            if action == "language":
                CURRENT_LANGUAGE = _prompt_language()
                continue

            if action == "modify":
                context = load_context(project_dir)
                if context:
                    _action_modify_spec(context, project_dir)
                continue

            if action == "project":
                context = load_context(project_dir)
                if context:
                    lines = [f"  [bold]Project:[/bold] {context.get('project', project_dir.name)}"]
                    lines.append(f"  Language: {context.get('language', '?')}")
                    lines.append("")
                    all_entries = context.get("functions", [])
                    type_entries = [e for e in all_entries if e.get("kind") == "type"]
                    fn_entries = [e for e in all_entries if e.get("kind", "function") == "function"]
                    if type_entries:
                        lines.append(f"  [dim]Types ({len(type_entries)})[/dim]")
                        for fn in type_entries:
                            lines.append(
                                f"  [rgb(100,140,180)]{fn['name']}[/rgb(100,140,180)]"
                                f"         {fn.get('spec_file', '?')}"
                            )
                        lines.append("")
                    if fn_entries:
                        lines.append(f"  [dim]Functions ({len(fn_entries)})[/dim]")
                    for fn in fn_entries:
                        icon, _ = _spec_status(fn, project_dir)
                        thms = ", ".join(fn.get("theorems", [])) or "—"
                        deps = ", ".join(fn.get("depends_on", [])) or "—"
                        lines.append(f"  [rgb(100,140,180)]{fn['name']}[/rgb(100,140,180)]  [dim]{icon}[/dim]")
                        lines.append(f"    spec:    {fn.get('spec_file', '?')}")
                        lines.append(f"    depends: {deps}")
                        lines.append(f"    proves:  {thms}")
                        lines.append(f"    built:   {fn.get('generated_at', '—')}")
                    specs_md_path = project_dir / "SPECS.md"
                    if specs_md_path.exists():
                        lines.append("")
                        lines.append("  [green]SPECS.md up to date[/green]")
                    else:
                        lines.append("")
                        lines.append("  [yellow]SPECS.md missing — run [b] to build[/yellow]")
                    from rich.panel import Panel as _Panel
                    console.print(_Panel(
                        "\n".join(lines),
                        title="[bold]Project Summary[/bold]",
                        border_style="rgb(100,140,180)",
                    ))
                continue

            if action == "build":
                context = load_context(project_dir)
                if not context:
                    console.print("  [yellow]No context found.[/yellow]")
                    continue
                _action_build_menu(context, project_dir, CURRENT_LANGUAGE, stacked)
                continue

            if action == "generate_main":
                context = load_context(project_dir)
                if not context:
                    console.print("  [yellow]No context found.[/yellow]")
                    continue
                _action_generate_main(context, project_dir, CURRENT_LANGUAGE)
                continue

            if action == "run_main":
                context = load_context(project_dir)
                if not context:
                    console.print("  [yellow]No context found.[/yellow]")
                    continue
                _action_run_main(context, project_dir, CURRENT_LANGUAGE)
                continue

            # action == "edit"
            tmp_spec = Path("/tmp/speccode_input.lean")

            # A. Prepare temp file (empty for new spec, keep errors for retry)
            if not has_validation_errors:
                tmp_spec.write_text("", encoding="utf-8")

            raw = run_once()
            if raw is None:
                has_validation_errors = False
                continue

            spec_input = _strip_error_header(raw)
            if not spec_input.strip():
                has_validation_errors = False
                console.print("[yellow]No input.[/yellow]")
                continue

            # B. Validate (pure Python, no AI)
            valid, errors = validate_lean_spec(spec_input)

            if not valid:
                has_validation_errors = True
                from rich.console import Group as _Group
                spec_display = Syntax(spec_input, "text", theme="monokai",
                                      word_wrap=True, background_color="default")
                err_text = Text("\n")
                for e in errors:
                    err_text.append(f"  ✗ {e}\n", style="bright_red")
                console.print(Panel(_Group(spec_display, err_text),
                                    title="[bright_red]invalid spec[/bright_red]",
                                    border_style="bright_red"))

                action = render_menu(project_dir)
                if _menu_line_count > 0:
                    sys.stdout.write(f"\x1b[{_menu_line_count}A\x1b[0J")
                    sys.stdout.flush()
                if action == "edit":
                    _inject_errors_into_file(tmp_spec, spec_input, errors)
                    next_action = "edit"
                elif action == "language":
                    CURRENT_LANGUAGE = _prompt_language()
                    _inject_errors_into_file(tmp_spec, spec_input, errors)
                    next_action = "edit"
                elif action == "quit":
                    has_validation_errors = False
                    next_action = "quit"
                else:
                    next_action = action
                continue

            # C. Valid — save spec, parse depends, update context (no code generation)
            has_validation_errors = False
            fn_name, context = save_spec(spec_input, project_dir, CURRENT_LANGUAGE)

            console.print(Panel(
                Syntax(spec_input, "text", theme="monokai",
                       word_wrap=True, background_color="default"),
                title=f"[bright_green]spec saved → specs/{fn_name}.lean[/bright_green]",
                border_style="bright_green",
            ))

    except KeyboardInterrupt:
        pass

    console.print("\n[dim]Bye.[/dim]")
    sys.exit(0)


if __name__ == "__main__":
    main()
