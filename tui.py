"""
speccode — TUI
Terminal interface for the speccode pipeline.
"""

from __future__ import annotations

import hashlib
import os
import re
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
    check_stale,
    clean_lean_error,
    count_blocks,
    generate_main,
    generate_specs_md,
    init_context,
    LANGUAGE_CONFIGS,
    load_api_key,
    load_context,
    parse_spec,
    run_pipeline,
    save_context,
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


def select_spec(context: dict) -> str | None:
    """
    Rich Live keyboard-navigable spec selector.
    Returns the selected spec name, or None on Esc/q.
    """
    import readchar

    entries = [e for e in context.get("functions", []) if e.get("kind") != "demo"]
    if not entries:
        return None

    idx = 0

    def _render(current_idx: int):
        lines = Text()
        lines.append("\n  Select spec to modify:\n\n", style="bold")
        for i, entry in enumerate(entries):
            name = entry.get("name", "?")
            spec_file = entry.get("spec_file", f"specs/{name}.lean")
            if i == current_idx:
                lines.append("  → ", style="rgb(100,140,180) bold")
                lines.append(f"{name:<20}", style="bright_white")
                lines.append(f"  {spec_file}\n", style="dim")
            else:
                lines.append(f"    {name:<20}", style="dim")
                lines.append(f"  {spec_file}\n", style="dim")
        lines.append("\n  ↑↓ navigate   Enter select   Esc cancel\n", style="dim")
        return Panel(lines, border_style="dim")

    with Live(
        _render(idx),
        console=console,
        refresh_per_second=10,
        transient=True,
    ) as live:
        while True:
            key = readchar.readkey()
            if key == readchar.key.UP:
                idx = (idx - 1) % len(entries)
                live.update(_render(idx))
            elif key == readchar.key.DOWN:
                idx = (idx + 1) % len(entries)
                live.update(_render(idx))
            elif key in (readchar.key.ENTER, "\r", "\n"):
                return entries[idx]["name"]
            elif key in (readchar.key.ESC, "q", "\x03"):
                return None


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


def _menu_line(items: list[tuple[str, str]]) -> None:
    """Print a sub-menu line from (key, label) pairs."""
    menu_text = Text("  ")
    for i, (key, label) in enumerate(items):
        if i > 0:
            menu_text.append("   ", style="dim")
        menu_text.append(f"[{key}]", style="rgb(100,140,180)")
        menu_text.append(f" {label}", style="dim")
    console.print()
    console.print(menu_text)
    console.print()


def _menu_prompt() -> str:
    """Print the prompt and return one keypress (via readchar)."""
    import readchar
    console.print("  [rgb(100,140,180)]>[/rgb(100,140,180)] ", end="")
    key = readchar.readkey()
    console.print()
    return key


def _menu_specs(has_context: bool) -> str | None:
    """[s] specs sub-menu. Returns action or None for back."""
    items = [("e", "new"), ("m", "modify"), ("←", "back")]
    if not has_context:
        items = [("e", "new"), ("←", "back")]
    _menu_line(items)
    while True:
        key = _menu_prompt()
        if key in ("e", "E"):
            return "edit"
        if key in ("m", "M") and has_context:
            return "modify"
        if key in ("\x1b", "\x03", "\x04") or key in ("\x1b[D",):  # Esc / left arrow
            return None
        if key == "q":
            return None


def _menu_code() -> str | None:
    """[c] code sub-menu. Returns action or None for back."""
    _menu_line([("g", "generate main"), ("r", "rebuild"), ("k", "compile"), ("x", "run"), ("←", "back")])
    while True:
        key = _menu_prompt()
        if key in ("g", "G"):
            return "generate_main"
        if key in ("r", "R"):
            return "rebuild"
        if key in ("k", "K"):
            return "compile"
        if key in ("x", "X"):
            return "run"
        if key in ("\x1b", "\x03", "\x04") or key in ("\x1b[D",):
            return None
        if key == "q":
            return None


def _menu_project() -> str | None:
    """[p] project sub-menu. Returns action or None for back."""
    _menu_line([("v", "view summary"), ("l", "language"), ("←", "back")])
    while True:
        key = _menu_prompt()
        if key in ("v", "V"):
            return "project"
        if key in ("l", "L"):
            return "language"
        if key in ("\x1b", "\x03", "\x04") or key in ("\x1b[D",):
            return None
        if key == "q":
            return None


def render_menu(project_dir: Path) -> str:
    """
    Hierarchical main menu → sub-menus.
    Returns: 'edit', 'modify', 'generate_main', 'rebuild', 'compile', 'run',
             'language', 'project', or 'quit'.
    """
    global CURRENT_LANGUAGE

    while True:
        context = load_context(project_dir)
        has_context = context is not None

        if has_context:
            CURRENT_LANGUAGE = context.get("language", CURRENT_LANGUAGE)
            project_name = context.get("project", project_dir.name)
            all_entries = context.get("functions", [])
            n_total = len(all_entries)
            n_types = sum(1 for e in all_entries if e.get("kind") == "type")
            n_functions = n_total - n_types
            language = context.get("language", CURRENT_LANGUAGE)

            console.print()
            header = Text("  ")
            header.append("◆ ", style="bold rgb(100,140,180)")
            header.append(project_name, style="bold bright_white")
            console.print(header)

            stats = Text("    ")
            stats.append(
                f"{n_total} specs  ·  {n_types} types  ·  {n_functions} functions  ·  {language}",
                style="dim",
            )
            console.print(stats)
        else:
            console.print()
            no_proj = Text("  ")
            no_proj.append("◆ ", style="bold rgb(100,140,180)")
            no_proj.append("new project", style="dim")
            console.print(no_proj)

        # Main menu
        main_items = [("s", "specs")]
        if has_context:
            main_items += [("c", "code"), ("p", "project")]
        main_items += [("q", "quit")]

        menu_text = Text("  ")
        for i, (k, label) in enumerate(main_items):
            if i > 0:
                menu_text.append("   ", style="dim")
            menu_text.append(f"[{k}]", style="rgb(100,140,180)")
            menu_text.append(f" {label}", style="dim")

        console.print()
        console.print(menu_text)
        console.print()

        # Key loop for main menu
        while True:
            console.print("  [rgb(100,140,180)]>[/rgb(100,140,180)] ", end="")
            try:
                key = _read_key()
            except (EOFError, KeyboardInterrupt):
                console.print()
                return "quit"
            console.print()

            if key in ("s", "S"):
                result = _menu_specs(has_context)
                if result is not None:
                    return result
                break  # back → redraw main menu

            if key in ("c", "C") and has_context:
                result = _menu_code()
                if result is not None:
                    return result
                break

            if key in ("p", "P") and has_context:
                result = _menu_project()
                if result is not None:
                    return result
                break

            if key in ("q", "Q", "\x03", "\x04"):
                return "quit"
            # unknown key: re-show prompt


def _prompt_language() -> str:
    """
    Display language selection sub-menu.
    Returns the selected language key.
    """
    lang_map = {
        "1": "c++",
        "2": "python",
        "3": "rust",
        "4": "ocaml",
        "5": "go",
        "6": "typescript",
    }

    console.print()
    console.print("  Select output language:")
    console.print("  [1] c++        [2] python")
    console.print("  [3] rust       [4] ocaml")
    console.print("  [5] go         [6] typescript")
    console.print()

    while True:
        console.print("  > ", end="")
        try:
            key = _read_key()
        except (EOFError, KeyboardInterrupt):
            console.print()
            return "c++"
        console.print()
        if key in lang_map:
            return lang_map[key]
        # unknown key: reshow prompt only


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
            else:
                action, next_action = next_action, None

            if action == "quit":
                break

            if action in ("compile", "run"):
                continue  # not yet implemented

            if action == "language":
                CURRENT_LANGUAGE = _prompt_language()
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
                        thms = ", ".join(fn.get("theorems", [])) or "—"
                        lines.append(f"  [rgb(100,140,180)]{fn['name']}[/rgb(100,140,180)]")
                        lines.append(f"    spec: {fn.get('spec_file', '?')}")
                        lines.append(f"    theorems: {thms}")
                        lines.append(f"    generated: {fn.get('generated_at', '?')}")
                    specs_md_path = project_dir / "SPECS.md"
                    if specs_md_path.exists():
                        lines.append("")
                        lines.append("  [green]SPECS.md up to date[/green]")
                    else:
                        lines.append("")
                        lines.append("  [yellow]SPECS.md missing — regenerate with [r][/yellow]")
                    from rich.panel import Panel as _Panel
                    console.print(_Panel(
                        "\n".join(lines),
                        title="[bold]Project Summary[/bold]",
                        border_style="rgb(100,140,180)",
                    ))
                continue

            if action == "rebuild":
                context = load_context(project_dir)
                if not context:
                    console.print("  [yellow]No context found.[/yellow]")
                    continue
                functions = context.get("functions", [])
                console.print(f"  [rgb(100,140,180)]Rebuilding {len(functions)} function(s)...[/rgb(100,140,180)]")
                for fn in functions:
                    fn_name = fn["name"]
                    spec_path = project_dir / fn.get("spec_file", f"specs/{fn_name}.lean")
                    if not spec_path.exists():
                        console.print(f"  [yellow]skip {fn_name}: spec not found[/yellow]")
                        continue
                    console.print(f"  [dim]→ {fn_name}[/dim]")
                    spec_content = spec_path.read_text(encoding="utf-8")
                    state = DisplayState()
                    validate_and_generate(spec_content, state, stacked, CURRENT_LANGUAGE)
                context = load_context(project_dir)
                emit_ctx = {"fn_count": len(context.get("functions", [])) if context else 0}
                console.print(f"  [green]✓ rebuild done — {emit_ctx['fn_count']} function(s)[/green]")
                continue

            if action == "modify":
                context = load_context(project_dir)
                if not context:
                    continue
                fn_name = select_spec(context)
                if fn_name is None:
                    continue
                entry = next((e for e in context.get("functions", []) if e.get("name") == fn_name), None)
                spec_file_path = project_dir / (entry.get("spec_file", f"specs/{fn_name}.lean") if entry else f"specs/{fn_name}.lean")
                editor = os.environ.get("EDITOR", "nano")
                console.print(f"  [dim]Opening {spec_file_path.name}...[/dim]")
                try:
                    subprocess.run([editor, str(spec_file_path)])
                except FileNotFoundError:
                    console.print(f"  [red]Editor not found: {editor}[/red]")
                    continue
                if not spec_file_path.exists():
                    continue
                new_content = spec_file_path.read_text(encoding="utf-8")
                new_hash = hashlib.sha256(new_content.encode()).hexdigest()[:8]
                old_hash = entry.get("spec_hash", "") if entry else ""
                if new_hash != old_hash:
                    ctx2 = load_context(project_dir)
                    if ctx2:
                        for fn in ctx2.get("functions", []):
                            if fn.get("name") == fn_name:
                                fn["spec_hash"] = new_hash
                                fn["stale"] = True
                                break
                        save_context(project_dir, ctx2)
                    console.print("  [yellow]spec updated — run [r] to rebuild[/yellow]")
                context = load_context(project_dir)
                continue

            if action == "generate_main":
                context = load_context(project_dir)
                if not context:
                    continue
                lang = context.get("language", CURRENT_LANGUAGE)
                cfg_obj = LANGUAGE_CONFIGS.get(lang, LANGUAGE_CONFIGS["c++"])

                state = DisplayState()
                with state._lock:
                    state.validation_state = "valid"
                    state.lang_fence = LANG_FENCE.get(lang, "cpp")
                    state.fn_name = "main"
                state.handle_event("generating", {})

                gen_done = threading.Event()
                gen_error: list[str] = []

                def _gen(_ctx=context, _lang=lang, _cfg=cfg_obj, _state=state, _done=gen_done, _err=gen_error):
                    try:
                        def _on_chunk(chunk: str):
                            _state.handle_event("streaming", {"chunk": chunk})
                        code = generate_main(
                            _ctx,
                            project_dir,
                            target_language=_lang,
                            on_chunk=_on_chunk,
                        )
                        _state.handle_event("done", {
                            "code": code,
                            "fn_name": "main",
                            "src_file": str(project_dir / f"src/main{_cfg['ext']}"),
                            "spec_file": "",
                            "cost": {"cost_total": 0.0, "codestral_tokens": 0},
                            "lang_fence": LANG_FENCE.get(_lang, "cpp"),
                            "lang_ext": _cfg["ext"],
                            "output_dir": str(project_dir),
                        })
                    except Exception as e:
                        _err.append(str(e))
                        _state.handle_event("error", {"message": str(e)})
                    _done.set()

                t = threading.Thread(target=_gen, daemon=True)
                t.start()

                with Live(
                    _Renderable(state, stacked),
                    console=console,
                    refresh_per_second=15,
                    transient=False,
                ) as live:
                    gen_done.wait()
                    live.update(build_renderable(state, stacked))

                t.join()

                if not gen_error:
                    console.print(f"  [green]✓ saved to src/main{cfg_obj['ext']}[/green]")

                context = load_context(project_dir)
                continue

            # action == "edit"
            tmp_spec = Path("/tmp/speccode_input.lean")

            # A. Prepare the temp file: empty for new specs,
            #    or keep as-is (errors already injected) for validation retries.
            if not has_validation_errors:
                tmp_spec.write_text("", encoding="utf-8")

            # Open editor, read raw content
            raw = run_once()
            if raw is None:
                has_validation_errors = False
                continue  # editor not found — back to menu

            # B. Strip header comments; if nothing remains, back to menu
            content = _strip_error_header(raw)
            if not content.strip():
                has_validation_errors = False
                console.print("[yellow]No input.[/yellow]")
                continue

            # C/D. Show spec with "validating..." then validate and optionally generate
            state = DisplayState()
            result = validate_and_generate(content, state, stacked, CURRENT_LANGUAGE)

            # E. Invalid — show full menu; inject errors if user chooses to edit
            if result == "invalid":
                has_validation_errors = True
                with state._lock:
                    errors = list(state.validation_errors)

                action = render_menu(project_dir)
                if action == "edit":
                    _inject_errors_into_file(tmp_spec, content, errors)
                    next_action = "edit"
                elif action == "language":
                    CURRENT_LANGUAGE = _prompt_language()
                    _inject_errors_into_file(tmp_spec, content, errors)
                    next_action = "edit"
                elif action == "quit":
                    has_validation_errors = False
                    next_action = "quit"
                else:
                    next_action = action  # project or rebuild — pass through
                continue

            # F. Valid — pipeline ran (done or error); show full menu
            has_validation_errors = False
            context = load_context(project_dir)
            next_action = render_menu(project_dir)

    except KeyboardInterrupt:
        pass

    console.print("\n[dim]Bye.[/dim]")
    sys.exit(0)


if __name__ == "__main__":
    main()
