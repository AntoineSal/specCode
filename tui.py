"""
speccode — TUI
Terminal interface for the speccode pipeline.
"""

from __future__ import annotations

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
    clean_lean_error,
    count_blocks,
    load_api_key,
    parse_spec,
    run_pipeline,
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
    Validate spec_content via lake build in lean_project/ (15s timeout).
    Returns (True, []) if valid, lake not found, timeout, or only sorry-related messages.
    Returns (False, errors) if there are real errors.
    """
    lean_project = Path(__file__).parent.resolve() / "lean_project"
    main_lean = lean_project / "Main.lean"

    if not lean_project.exists():
        return (True, [])

    original = main_lean.read_text(encoding="utf-8") if main_lean.exists() else ""
    main_lean.write_text(spec_content, encoding="utf-8")

    try:
        result = subprocess.run(
            ["lake", "build"],
            capture_output=True,
            text=True,
            timeout=15,
            cwd=str(lean_project),
        )
    except subprocess.TimeoutExpired:
        return (True, [])
    except FileNotFoundError:
        return (True, [])
    finally:
        main_lean.write_text(original, encoding="utf-8")

    if result.returncode == 0:
        return (True, [])

    output = (result.stdout + result.stderr).strip()
    errors = clean_lean_error(output)

    real_errors = [
        msg for msg in errors
        if not any(w in msg.lower() for w in _SORRY_WORDS)
    ]

    if not real_errors:
        return (True, [])

    return (False, real_errors)


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
                self.code_path = str(Path(out) / f"{self.fn_name}{lang_ext}")
                self.spec_path = str(Path(out) / f"{self.fn_name}_spec.lean")
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
            border = "bright_cyan"
            title = "[bright_cyan]spec — validating...[/bright_cyan]"
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
            header.append(f"{_sp()} ", style="bright_cyan")
            header.append("Codestral is generating…", style="bright_cyan bold")
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

            return Panel(content, title="[bright_cyan]OUTPUT[/bright_cyan]", border_style="bright_cyan")

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
                f"saved to ./{fn_name}/  │  ${cost:.4f}  │  {dur:.1f}s",
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
            line.append(ch, style="bold bright_cyan" if ch == "█" else deco)
        console.print(line)
    console.print()
    console.print(f"{sub_pad}[dim italic]{subtitle}[/dim italic]")
    console.print()


def _prompt_action(language: str) -> str:
    """
    Display the main menu and wait for a valid key.
    Returns 'edit', 'language', or 'quit'.
    """
    console.print()
    console.print("  [e] new spec    [l] language    [q] quit")
    console.print()

    while True:
        console.print("  > ", end="")
        try:
            key = _read_key()
        except (EOFError, KeyboardInterrupt):
            console.print()
            return "quit"
        console.print()
        if key in ("e", "E", "\r", "\n"):
            return "edit"
        if key in ("l", "L"):
            return "language"
        if key in ("q", "Q", "\x03", "\x04"):  # q, Ctrl+C, Ctrl+D
            return "quit"
        # unknown key: reshow prompt only


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
        run_pipeline(spec, on_event=state.handle_event, target_language=language)
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
        run_pipeline(content, on_event=state.handle_event, target_language=language)
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

    next_action: str | None = None
    has_validation_errors = False

    try:
        while True:
            if next_action is None:
                action = _prompt_action(CURRENT_LANGUAGE)
            else:
                action, next_action = next_action, None

            if action == "quit":
                break

            if action == "language":
                CURRENT_LANGUAGE = _prompt_language()
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

            # E. Invalid — show menu; reopen with injected errors only if user presses [e]
            if result == "invalid":
                has_validation_errors = True
                with state._lock:
                    errors = list(state.validation_errors)

                console.print()
                console.print("  [dim][e] edit spec    [l] language    [q] quit[/dim]")
                console.print()

                while True:
                    try:
                        key = _read_key()
                    except (EOFError, KeyboardInterrupt):
                        console.print()
                        next_action = "quit"
                        break
                    if key in ("e", "E", "\r", "\n"):
                        _inject_errors_into_file(tmp_spec, content, errors)
                        next_action = "edit"
                        break
                    if key in ("l", "L"):
                        CURRENT_LANGUAGE = _prompt_language()
                        _inject_errors_into_file(tmp_spec, content, errors)
                        next_action = "edit"
                        break
                    if key in ("q", "Q", "\x03", "\x04"):
                        has_validation_errors = False
                        next_action = "quit"
                        break
                continue

            # F. Valid — pipeline ran (done or error); show inline menu
            has_validation_errors = False
            console.print()
            console.print("  [dim][e] new spec    [l] language    [q] quit[/dim]")
            console.print()

            while True:
                try:
                    key = _read_key()
                except (EOFError, KeyboardInterrupt):
                    console.print()
                    next_action = "quit"
                    break
                if key in ("e", "E", "\r", "\n"):
                    next_action = "edit"
                    break
                if key in ("l", "L"):
                    CURRENT_LANGUAGE = _prompt_language()
                    next_action = "edit"
                    break
                if key in ("q", "Q", "\x03", "\x04"):
                    next_action = "quit"
                    break

    except KeyboardInterrupt:
        pass

    console.print("\n[dim]Bye.[/dim]")
    sys.exit(0)


if __name__ == "__main__":
    main()
