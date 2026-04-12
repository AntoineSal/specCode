"""
speccode — TUI
Terminal interface for the speccode pipeline.
"""

from __future__ import annotations

import hashlib
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


def _read_key_safe() -> str:
    """
    Read one key from stdin using readchar, with proper Esc detection on Mac.
    - Bare Esc (no follow-up chars within 50ms) → returns 'ESC'
    - Arrow sequences → returns '\x1b[A', '\x1b[B', '\x1b[C', '\x1b[D'
    - Any other char → returns it as-is
    """
    import readchar as _rc
    ch = _rc.readchar()
    if ch == "\x1b":
        if select.select([sys.stdin], [], [], 0.05)[0]:
            ch2 = _rc.readchar()
            if ch2 == "[":
                ch3 = _rc.readchar()
                return f"\x1b[{ch3}"
        return "ESC"
    return ch


# ---------------------------------------------------------------------------
# Menu — ANSI line clearing + plain print approach
# ---------------------------------------------------------------------------

def clear_lines(n: int) -> None:
    """Erase the last n lines printed to the terminal."""
    for _ in range(n):
        sys.stdout.write("\x1b[1A")  # move up one line
        sys.stdout.write("\x1b[2K")  # erase that line
    sys.stdout.flush()


def _kw(key: str, label: str) -> str:
    return f"[rgb(100,140,180)][{key}][/rgb(100,140,180)] [dim]{label}[/dim]"


def print_menu(state: dict) -> int:
    """Print the current menu state. Returns the number of lines printed."""
    menu = state["menu"]
    context = state.get("context")
    has_context = context is not None
    project_dir: Path = state["project_dir"]

    if has_context:
        project_name = context.get("project", project_dir.name)
        all_entries = context.get("functions", [])
        n_total = len(all_entries)
        n_types = sum(1 for e in all_entries if e.get("kind") == "type")
        n_fns = n_total - n_types
        language = context.get("language", CURRENT_LANGUAGE)
        stats_str = f"[dim]{n_total} specs  ·  {n_types} types  ·  {n_fns} fns  ·  {language}[/dim]"
    else:
        project_name = "new project"
        stats_str = ""

    crumb_map: dict[str, list[str]] = {
        "specs":       ["specs"],
        "code":        ["code"],
        "project":     ["project"],
        "language":    ["project", "language"],
        "select_spec": ["specs", "modify"],
    }
    title = (
        f"  [bold rgb(100,140,180)]◆[/bold rgb(100,140,180)]"
        f" [bold bright_white]{project_name}[/bold bright_white]"
    )
    for crumb in crumb_map.get(menu, []):
        title += f"  [dim]›  {crumb}[/dim]"

    n = 0

    def p(s: str = "") -> None:
        nonlocal n
        console.print(s)
        n += 1

    if menu == "main":
        p()
        p(title)
        p(f"    {stats_str}" if stats_str else "")
        p()
        items = [_kw("s", "specs")]
        if has_context:
            items += [_kw("c", "code"), _kw("p", "project")]
        items.append(_kw("q", "quit"))
        p("  " + "   ".join(items))
        p()
        p("  [dim]>[/dim]")
        p()
        p()
        # 9 lines

    elif menu == "specs":
        p()
        p(title)
        p()
        items = [_kw("e", "new")]
        if has_context:
            items.append(_kw("m", "modify"))
        p("  " + "   ".join(items))
        p()
        p("  [dim]Esc to go back[/dim]")
        p()
        # 7 lines

    elif menu == "code":
        p()
        p(title)
        p()
        p("  " + "   ".join([
            _kw("g", "generate main"), _kw("r", "rebuild"),
            _kw("k", "compile"), _kw("x", "run"),
        ]))
        p()
        p("  [dim]Esc to go back[/dim]")
        p()
        # 7 lines

    elif menu == "project":
        p()
        p(title)
        p()
        p("  " + "   ".join([_kw("v", "view summary"), _kw("l", "language")]))
        p()
        p("  [dim]Esc to go back[/dim]")
        p()
        # 7 lines

    elif menu == "language":
        current_lang = (context or {}).get("language", CURRENT_LANGUAGE)
        lang_items = [
            ("1", "c++"), ("2", "python"), ("3", "rust"),
            ("4", "ocaml"), ("5", "go"), ("6", "typescript"),
        ]
        p()
        p(title)
        p()
        for key_num, lang_name in lang_items:
            if lang_name == current_lang:
                p(f"  [rgb(100,140,180)][{key_num}][/rgb(100,140,180)]"
                  f" [bold bright_white]{lang_name}[/bold bright_white]  [dim]←[/dim]")
            else:
                p(f"  [rgb(100,140,180)][{key_num}][/rgb(100,140,180)] [dim]{lang_name}[/dim]")
        p()
        p("  [dim]Esc to go back[/dim]")
        p()
        # 12 lines

    elif menu == "select_spec":
        entries = state.get("spec_entries", [])
        idx = state.get("spec_idx", 0)
        p()
        p(title)
        p()
        for i, entry in enumerate(entries):
            name = entry.get("name", "?")
            spec_file = entry.get("spec_file", f"specs/{name}.lean")
            if i == idx:
                p(f"  [rgb(100,140,180) bold]→[/rgb(100,140,180) bold]"
                  f" [bright_white]{name:<20}[/bright_white]  [dim]{spec_file}[/dim]")
            else:
                p(f"    [dim]{name:<20}  {spec_file}[/dim]")
        p()
        p("  [dim]↑↓ navigate   Enter select   Esc to go back[/dim]")
        p()
        # 6 + len(entries) lines

    return n


def _transition(state: dict, key: str) -> str:
    """
    Update state["menu"] based on key.
    Returns an action string: "continue", "quit", "open_editor", "edit_spec",
    "show_project", "apply_language", "generate_main", "rebuild", "compile", "run".
    """
    menu = state["menu"]
    has_context = state.get("context") is not None

    if menu == "main":
        if key in ("s", "S"):
            state["menu"] = "specs"
        elif key in ("c", "C") and has_context:
            state["menu"] = "code"
        elif key in ("p", "P") and has_context:
            state["menu"] = "project"
        elif key in ("q", "Q", "ESC", "\x03", "\x04"):
            return "quit"

    elif menu == "specs":
        if key in ("e", "E"):
            return "open_editor"
        elif key in ("m", "M") and has_context:
            entries = [
                e for e in state["context"].get("functions", [])
                if e.get("kind") != "demo"
            ]
            state["spec_entries"] = entries
            state["spec_idx"] = 0
            state["menu"] = "select_spec"
        elif key in ("ESC", "\x03"):
            state["menu"] = "main"

    elif menu == "code":
        if key in ("g", "G"):
            return "generate_main"
        elif key in ("r", "R"):
            return "rebuild"
        elif key in ("k", "K"):
            return "compile"
        elif key in ("x", "X"):
            return "run"
        elif key in ("ESC", "\x03"):
            state["menu"] = "main"

    elif menu == "project":
        if key in ("v", "V"):
            return "show_project"
        elif key in ("l", "L"):
            state["menu"] = "language"
        elif key in ("ESC", "\x03"):
            state["menu"] = "main"

    elif menu == "language":
        lang_map = {
            "1": "c++", "2": "python", "3": "rust",
            "4": "ocaml", "5": "go", "6": "typescript",
        }
        if key in lang_map:
            state["selected_language"] = lang_map[key]
            state["menu"] = "main"
            return "apply_language"
        elif key in ("ESC", "\x03"):
            state["menu"] = "project"

    elif menu == "select_spec":
        entries = state.get("spec_entries", [])
        n = len(entries)
        if key == "\x1b[A" and n:
            state["spec_idx"] = (state["spec_idx"] - 1) % n
        elif key == "\x1b[B" and n:
            state["spec_idx"] = (state["spec_idx"] + 1) % n
        elif key in ("\r", "\n") and entries:
            return "edit_spec"
        elif key in ("ESC", "\x03"):
            state["menu"] = "specs"

    return "continue"


# ---------------------------------------------------------------------------
# Action handlers
# ---------------------------------------------------------------------------

def _action_edit(live_state: dict, project_dir: Path, stacked: bool) -> None:
    """Open editor for a new spec, validate, and generate."""
    tmp_spec = Path("/tmp/speccode_input.lean")
    if not live_state.get("has_validation_errors"):
        tmp_spec.write_text("", encoding="utf-8")

    raw = run_once()
    if raw is None:
        live_state["has_validation_errors"] = False
        live_state["menu"] = "specs"
        return

    content = _strip_error_header(raw)
    if not content.strip():
        live_state["has_validation_errors"] = False
        live_state["menu"] = "specs"
        return

    ds = DisplayState()
    result = validate_and_generate(content, ds, stacked, CURRENT_LANGUAGE)

    if result == "invalid":
        live_state["has_validation_errors"] = True
        with ds._lock:
            errors = list(ds.validation_errors)
        _inject_errors_into_file(tmp_spec, content, errors)
    else:
        live_state["has_validation_errors"] = False
        live_state["context"] = load_context(project_dir)

    live_state["menu"] = "specs"


def _action_edit_spec(live_state: dict, project_dir: Path) -> None:
    """Open editor on the selected spec, update hash if changed."""
    entries = live_state.get("spec_entries", [])
    idx = live_state.get("spec_idx", 0)
    if not entries or idx >= len(entries):
        live_state["menu"] = "specs"
        return

    entry = entries[idx]
    fn_name = entry.get("name", "")
    spec_file_path = project_dir / entry.get("spec_file", f"specs/{fn_name}.lean")

    editor = os.environ.get("EDITOR", "nano")
    try:
        subprocess.run([editor, str(spec_file_path)])
    except FileNotFoundError:
        console.print(f"  [red]Editor not found: {editor}[/red]")
        live_state["menu"] = "specs"
        return

    if not spec_file_path.exists():
        live_state["menu"] = "specs"
        return

    new_content = spec_file_path.read_text(encoding="utf-8")
    new_hash = hashlib.sha256(new_content.encode()).hexdigest()[:8]
    old_hash = entry.get("spec_hash", "")

    if new_hash != old_hash:
        ctx2 = load_context(project_dir)
        if ctx2:
            for fn in ctx2.get("functions", []):
                if fn.get("name") == fn_name:
                    fn["spec_hash"] = new_hash
                    fn["stale"] = True
                    break
            save_context(project_dir, ctx2)
        live_state["context"] = load_context(project_dir)
        console.print("  [yellow]spec updated — run [r] to rebuild[/yellow]")

    live_state["menu"] = "specs"


def _action_show_project(live_state: dict, project_dir: Path) -> None:
    """Display project summary, wait for keypress."""
    context = live_state.get("context")
    if not context:
        live_state["menu"] = "main"
        return

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
    lines.append("")
    if specs_md_path.exists():
        lines.append("  [green]SPECS.md up to date[/green]")
    else:
        lines.append("  [yellow]SPECS.md missing — regenerate with [r][/yellow]")

    console.print(Panel(
        "\n".join(lines),
        title="[bold]Project Summary[/bold]",
        border_style="rgb(100,140,180)",
    ))
    console.print("  [dim]Press any key to continue...[/dim]")
    _read_key_safe()
    live_state["menu"] = "main"


def _action_generate_main(state: dict, project_dir: Path, stacked: bool) -> None:
    """Stream generate_main in its own Live display."""
    context = state.get("context")
    if not context:
        state["menu"] = "main"
        return

    lang = context.get("language", CURRENT_LANGUAGE)
    cfg_obj = LANGUAGE_CONFIGS.get(lang, LANGUAGE_CONFIGS["c++"])

    ds = DisplayState()
    with ds._lock:
        ds.validation_state = "valid"
        ds.lang_fence = LANG_FENCE.get(lang, "cpp")
        ds.fn_name = "main"
    ds.handle_event("generating", {})

    done = threading.Event()

    def _run():
        try:
            def on_chunk(chunk: str):
                ds.handle_event("streaming", {"chunk": chunk})
            code = generate_main(context, project_dir, target_language=lang, on_chunk=on_chunk)
            ds.handle_event("done", {
                "code": code,
                "fn_name": "main",
                "src_file": str(project_dir / f"src/main{cfg_obj['ext']}"),
                "spec_file": "",
                "cost": {"cost_total": 0.0, "codestral_tokens": 0},
                "lang_fence": LANG_FENCE.get(lang, "cpp"),
                "lang_ext": cfg_obj["ext"],
                "output_dir": str(project_dir),
            })
        except Exception as e:
            ds.handle_event("error", {"message": str(e)})
        done.set()

    t = threading.Thread(target=_run, daemon=True)
    t.start()
    with Live(_Renderable(ds, stacked), console=console, refresh_per_second=15, transient=False) as live:
        done.wait()
        live.update(build_renderable(ds, stacked))
    t.join()
    time.sleep(1.5)
    state["context"] = load_context(project_dir)
    state["menu"] = "main"


def _action_rebuild(state: dict, project_dir: Path, stacked: bool) -> None:
    """Rebuild all specs, each in its own Live display."""
    context = state.get("context")
    if not context:
        state["menu"] = "main"
        return

    lang = CURRENT_LANGUAGE
    functions = [f for f in context.get("functions", []) if f.get("kind") != "demo"]

    for fn in functions:
        fn_name = fn["name"]
        spec_path = project_dir / fn.get("spec_file", f"specs/{fn_name}.lean")
        if not spec_path.exists():
            continue
        spec_content = spec_path.read_text(encoding="utf-8")

        ds = DisplayState()
        with ds._lock:
            ds.validation_state = "valid"
            ds.spec_lines = spec_content.splitlines()
            ds.lang_fence = LANG_FENCE.get(lang, "cpp")
            ds.fn_name = fn_name
        ds.handle_event("generating", {})

        done = threading.Event()

        def _run(_spec=spec_content, _ds=ds, _done=done):
            run_pipeline(_spec, on_event=_ds.handle_event,
                         target_language=lang, project_dir=project_dir)
            _done.set()

        t = threading.Thread(target=_run, daemon=True)
        t.start()
        with Live(_Renderable(ds, stacked), console=console, refresh_per_second=15, transient=False) as live:
            done.wait()
            live.update(build_renderable(ds, stacked))
        t.join()
        time.sleep(0.5)

    state["context"] = load_context(project_dir)
    state["menu"] = "main"


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

    err = check_prerequisites()
    if err:
        console.print(Panel(
            f"[red]{err}[/red]\nSet MISTRAL_API_KEY in .env",
            title="[red]Missing API Key[/red]",
            border_style="red",
        ))
        sys.exit(1)

    _, rows = shutil.get_terminal_size()
    stacked = rows > 40

    _print_intro()

    project_dir = Path.cwd()
    context = load_context(project_dir)
    if context:
        CURRENT_LANGUAGE = context.get("language", CURRENT_LANGUAGE)

    state: dict = {
        "menu": "main",
        "context": context,
        "project_dir": project_dir,
        "spec_idx": 0,
        "spec_entries": [],
        "has_validation_errors": False,
        "stacked": stacked,
    }

    last_n = 0

    try:
        while True:
            if last_n > 0:
                clear_lines(last_n)
            last_n = print_menu(state)

            key = _read_key_safe()
            action = _transition(state, key)

            if action == "quit":
                clear_lines(last_n)
                last_n = 0
                break

            elif action == "open_editor":
                clear_lines(last_n)
                last_n = 0
                _action_edit(state, project_dir, stacked)

            elif action == "edit_spec":
                clear_lines(last_n)
                last_n = 0
                _action_edit_spec(state, project_dir)

            elif action == "show_project":
                clear_lines(last_n)
                last_n = 0
                _action_show_project(state, project_dir)

            elif action == "apply_language":
                CURRENT_LANGUAGE = state.pop("selected_language", CURRENT_LANGUAGE)

            elif action == "generate_main":
                clear_lines(last_n)
                last_n = 0
                _action_generate_main(state, project_dir, stacked)

            elif action == "rebuild":
                clear_lines(last_n)
                last_n = 0
                _action_rebuild(state, project_dir, stacked)

            elif action in ("compile", "run"):
                pass  # not yet implemented

            # "continue" — redraw at top of loop

    except KeyboardInterrupt:
        if last_n > 0:
            clear_lines(last_n)

    console.print("\n[dim]Bye.[/dim]")
    sys.exit(0)


if __name__ == "__main__":
    main()
