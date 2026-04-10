"""
speccode — TUI
Terminal interface for the speccode pipeline.
"""

from __future__ import annotations

import os
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

        content = Text()
        if lines:
            visible = lines[-20:]
            for line in visible:
                content.append(f"  {line}\n", style="white")
        else:
            content.append("  ", style="")
            content.append("Loading spec…\n", style="dim")

        return Panel(content, title="[dim]SPEC[/dim]", border_style="dim")

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
            Layout(input_panel, name="input"),
            Layout(output_panel, name="output"),
        )
        return layout


# ---------------------------------------------------------------------------
# Menu prompts
# ---------------------------------------------------------------------------

def _prompt_action(language: str) -> str:
    """
    Display the main menu and wait for a valid key.
    Returns 'edit', 'language', or 'quit'.
    """
    console.print()
    console.print(f"[bright_cyan]◆ speccode  —  lean specs → {language} code[/bright_cyan]")
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
    Returns the spec content, or None if the file is empty or editor not found.
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

    content = tmp.read_text(encoding="utf-8").strip() if tmp.exists() else ""
    if not content:
        console.print("[yellow]No input — file is empty.[/yellow]")
    return content or None


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

    try:
        while True:
            action = _prompt_action(CURRENT_LANGUAGE)

            if action == "quit":
                break

            if action == "language":
                CURRENT_LANGUAGE = _prompt_language()
                continue

            # action == "edit"
            spec = run_once()
            if not spec:
                continue  # back to menu

            # Generation
            state = DisplayState()
            generate(spec, state, stacked, CURRENT_LANGUAGE)

            with state._lock:
                phase = state.phase

            if phase == "error":
                time.sleep(3)

            console.print()
            console.print(Rule("[dim]New run[/dim]"))
            console.print()

    except KeyboardInterrupt:
        pass

    console.print("\n[dim]Bye.[/dim]")
    sys.exit(0)


if __name__ == "__main__":
    main()
