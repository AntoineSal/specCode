"""
speccode — orchestrator
Generates code from formal Lean 4 specifications.
"""

from __future__ import annotations

import os
import re
import time
from pathlib import Path
from dotenv import load_dotenv
from mistralai import Mistral

# ---------------------------------------------------------------------------
# Config
# ---------------------------------------------------------------------------

CODESTRAL_MODEL = "codestral-latest"
API_TIMEOUT = 120   # seconds per API call
API_MAX_RETRIES = 3
API_RETRY_DELAYS = [5, 15, 30]
API_RETRYABLE_CODES = {429, 502, 503}

# Cost per million tokens (USD)
CODESTRAL_COST_PER_MTOKEN = 0.2

SCRIPT_DIR = Path(__file__).parent.resolve()


# ---------------------------------------------------------------------------
# Language configs
# ---------------------------------------------------------------------------

LANGUAGE_CONFIGS = {
    "c++": {
        "display": "C++",
        "system_rules": (
            "Use modern C++17 (auto, range-for, structured bindings, std::optional, etc.)\n"
            "- No external dependencies — only standard library headers\n"
            "- Include all required headers (#include <vector>, #include <algorithm>, etc.)\n"
            "- Write standalone functions that closely match the spec signatures"
        ),
        "section": "C++ Implementation",
        "fence": "cpp",
        "ext": ".cpp",
    },
    "python": {
        "display": "Python",
        "system_rules": (
            "Use Python 3.10+, add type hints on all functions\n"
            "- Avoid unnecessary classes — prefer standalone functions\n"
            "- No external dependencies — only the standard library"
        ),
        "section": "Python Implementation",
        "fence": "python",
        "ext": ".py",
    },
    "rust": {
        "display": "Rust",
        "system_rules": (
            "Use stable Rust, idiomatic ownership and borrowing\n"
            "- No unsafe code\n"
            "- No external crates — only the standard library"
        ),
        "section": "Rust Implementation",
        "fence": "rust",
        "ext": ".rs",
    },
    "ocaml": {
        "display": "OCaml",
        "system_rules": (
            "Write purely functional OCaml, structural recursion\n"
            "- No mutation, no imperative loops\n"
            "- No external libraries — only the standard library"
        ),
        "section": "OCaml Implementation",
        "fence": "ocaml",
        "ext": ".ml",
    },
    "go": {
        "display": "Go",
        "system_rules": (
            "Use Go 1.21+, idiomatic style\n"
            "- No external packages — only the standard library\n"
            "- Write standalone functions with clear signatures"
        ),
        "section": "Go Implementation",
        "fence": "go",
        "ext": ".go",
    },
    "typescript": {
        "display": "TypeScript",
        "system_rules": (
            "Use TypeScript strict mode, explicit types on all functions\n"
            "- No external dependencies\n"
            "- Write standalone functions, avoid unnecessary classes"
        ),
        "section": "TypeScript Implementation",
        "fence": "typescript",
        "ext": ".ts",
    },
}


def get_codestral_system(target_language: str = "c++") -> str:
    cfg = LANGUAGE_CONFIGS.get(target_language, LANGUAGE_CONFIGS["c++"])
    return (
        f"You are an expert software engineer specializing in correct, efficient {cfg['display']}.\n"
        f"Your goal is to implement the functions described in the given Lean 4 specification.\n"
        f"\n"
        f"Rules for implementation:\n"
        f"- {cfg['system_rules']}\n"
        f"- Write standalone functions that closely match the spec signatures\n"
        f"- Use descriptive names that mirror the Lean spec\n"
        f"\n"
        f"Output format — ONE section, nothing else:\n"
        f"\n"
        f"### {cfg['section']}\n"
        f"```{cfg['fence']}\n"
        f"<complete {cfg['display']} implementation>\n"
        f"```\n"
    )


# ---------------------------------------------------------------------------
# API client
# ---------------------------------------------------------------------------

def load_api_key() -> str:
    """Search for .env in CWD, ~/.speccode/, then SCRIPT_DIR."""
    for candidate in [
        Path.cwd() / ".env",
        Path.home() / ".speccode" / ".env",
        SCRIPT_DIR / ".env",
    ]:
        if candidate.exists():
            load_dotenv(candidate)
            break
    key = os.environ.get("MISTRAL_API_KEY", "")
    if not key:
        raise RuntimeError(
            "MISTRAL_API_KEY not found. Set it in .env or as environment variable."
        )
    return key


def get_client() -> Mistral:
    return Mistral(api_key=load_api_key())


# ---------------------------------------------------------------------------
# Spec parsing
# ---------------------------------------------------------------------------

def parse_spec(spec_content: str) -> tuple[str, str, str]:
    """
    Split spec into (imports, fn_stubs, thm_stubs).
    Blocks are detected by lines starting with def/theorem/lemma.
    """
    lines = spec_content.splitlines(keepends=True)

    import_lines: list[str] = []
    fn_blocks: list[list[str]] = []
    thm_blocks: list[list[str]] = []

    current_block: list[str] | None = None
    current_type: str | None = None  # "fn" or "thm"

    def flush():
        nonlocal current_block, current_type
        if current_block is not None:
            text = "".join(current_block).rstrip() + "\n"
            if current_type == "fn":
                fn_blocks.append(text)
            elif current_type == "thm":
                thm_blocks.append(text)
        current_block = None
        current_type = None

    for line in lines:
        if line.startswith("import "):
            flush()
            import_lines.append(line)
        elif re.match(r"^def\s+", line):
            flush()
            current_type = "fn"
            current_block = [line]
        elif re.match(r"^(theorem|lemma)\s+", line):
            flush()
            current_type = "thm"
            current_block = [line]
        else:
            if current_block is not None:
                current_block.append(line)

    flush()

    imports = "".join(import_lines).rstrip()
    fn_stubs = "\n\n".join(b.rstrip() for b in fn_blocks)
    thm_stubs = "\n\n".join(b.rstrip() for b in thm_blocks)

    return imports, fn_stubs, thm_stubs


def count_blocks(text: str) -> int:
    """Count top-level def/theorem/lemma blocks."""
    return len(re.findall(r"^(?:def|theorem|lemma)\s+", text, re.MULTILINE))


def parse_theorem_stubs(thm_stubs: str) -> list[str]:
    """Split thm_stubs into a list of individual theorem/lemma blocks."""
    blocks: list[str] = []
    current: list[str] = []

    for line in thm_stubs.splitlines(keepends=True):
        if re.match(r"^(theorem|lemma)\s+", line) and current:
            blocks.append("".join(current).rstrip())
            current = [line]
        else:
            current.append(line)

    if current:
        blocks.append("".join(current).rstrip())

    return [b for b in blocks if b.strip()]


# ---------------------------------------------------------------------------
# Lean file assembly
# ---------------------------------------------------------------------------

def deduplicate_lean(code: str) -> str:
    """Remove duplicate def/theorem/lemma blocks, keeping only the first occurrence."""
    lines = code.splitlines(keepends=True)
    seen_names: set[str] = set()
    output_lines: list[str] = []
    skip = False

    for line in lines:
        m = re.match(r"^(def|theorem|lemma)\s+(\S+)", line)
        if m:
            name = m.group(2).split("(")[0].split(":")[0].split(" ")[0]
            if name in seen_names:
                skip = True
            else:
                seen_names.add(name)
                skip = False
        elif re.match(r"^(def|theorem|lemma|import|section|namespace|end)\s+", line):
            skip = False

        if not skip:
            output_lines.append(line)

    return "".join(output_lines)


def fix_reserved_names(code: str) -> str:
    """Replace `def insert ` (and all its call sites) with `def myInsert `."""
    if "def insert " not in code:
        return code
    return code.replace("def insert ", "def myInsert ").replace("insert ", "myInsert ")


def assemble_lean_file(imports: str, lean_impl: str, lean_proofs: str) -> str:
    parts = []
    if imports.strip():
        parts.append(imports.strip())
    if lean_impl.strip():
        parts.append(lean_impl.strip())
    if lean_proofs.strip():
        parts.append(lean_proofs.strip())
    assembled = "\n\n".join(parts) + "\n"
    assembled = fix_reserved_names(assembled)
    return deduplicate_lean(assembled)


# ---------------------------------------------------------------------------
# Code extraction helpers
# ---------------------------------------------------------------------------

def extract_section(text: str, header: str) -> str:
    """Extract fenced code block after a markdown ### header."""
    pattern = rf"###\s*{re.escape(header)}\s*\n```[a-zA-Z0-9_]*\n(.*?)```"
    m = re.search(pattern, text, re.DOTALL | re.IGNORECASE)
    if m:
        return m.group(1).strip()
    return ""


def extract_lean_block(text: str) -> str:
    """Extract the first ```lean ... ``` block, fallback to first fenced block."""
    m = re.search(r"```lean\n(.*?)```", text, re.DOTALL)
    if m:
        return m.group(1).strip()
    m = re.search(r"```[a-zA-Z]*\n(.*?)```", text, re.DOTALL)
    if m:
        return m.group(1).strip()
    return text.strip()


# ---------------------------------------------------------------------------
# API retry wrapper
# ---------------------------------------------------------------------------

def api_call_with_retry(fn, on_retry=None):
    """
    Call fn() with retry logic.
    fn must be a zero-argument callable that performs one API call.
    on_retry(status, wait, attempt, max_retries) is called before each sleep.
    Raises immediately on non-retryable errors.
    """
    import socket
    last_exc = None
    for attempt in range(1, API_MAX_RETRIES + 1):
        try:
            return fn()
        except Exception as exc:
            status = None
            is_timeout = isinstance(exc, (TimeoutError, socket.timeout))
            if hasattr(exc, "status_code"):
                status = exc.status_code
            elif hasattr(exc, "response") and hasattr(exc.response, "status_code"):
                status = exc.response.status_code

            retryable = is_timeout or (status in API_RETRYABLE_CODES)
            if not retryable or attempt == API_MAX_RETRIES:
                raise

            wait = API_RETRY_DELAYS[attempt - 1]
            if on_retry:
                on_retry(status, wait, attempt + 1, API_MAX_RETRIES)
            time.sleep(wait)
            last_exc = exc

    raise last_exc


# ---------------------------------------------------------------------------
# Codestral call with streaming
# ---------------------------------------------------------------------------

def call_codestral(
    client: Mistral,
    spec_content: str,
    token_usage: dict,
    target_language: str = "c++",
    on_chunk=None,
    on_retry=None,
) -> str:
    """
    Call Codestral with streaming. Emits each text chunk via on_chunk(text).
    Returns the generated code extracted from the language-specific section.
    """
    cfg = LANGUAGE_CONFIGS.get(target_language, LANGUAGE_CONFIGS["c++"])
    system_prompt = get_codestral_system(target_language)

    messages = [
        {"role": "system", "content": system_prompt},
        {"role": "user", "content": f"Partial Lean 4 specification:\n\n```lean\n{spec_content}\n```"},
    ]
    accumulated: list[str] = []

    def _call():
        accumulated.clear()
        stream = client.chat.stream(
            model=CODESTRAL_MODEL,
            messages=messages,
            timeout_ms=API_TIMEOUT * 1000,
        )
        for event in stream:
            chunk = event.data
            if chunk.choices:
                delta = chunk.choices[0].delta.content or ""
                if delta:
                    accumulated.append(delta)
                    if on_chunk:
                        on_chunk(delta)
            # Accumulate usage from final chunk
            if chunk.usage:
                token_usage["codestral_input"] += chunk.usage.prompt_tokens or 0
                token_usage["codestral_output"] += chunk.usage.completion_tokens or 0

    api_call_with_retry(_call, on_retry=on_retry)
    content = "".join(accumulated)

    code = extract_section(content, cfg["section"])
    if not code:
        m = re.search(rf"```(?:{re.escape(cfg['fence'])}|[a-zA-Z+]*)\n(.*?)```", content, re.DOTALL)
        if m:
            code = m.group(1).strip()
        else:
            code = extract_lean_block(content)  # fallback: first fenced block

    return code


# ---------------------------------------------------------------------------
# Output files
# ---------------------------------------------------------------------------

def detect_function_name(spec_content: str) -> str:
    """Extract first def name from spec for output directory naming."""
    m = re.search(r"^def\s+(\w+)", spec_content, re.MULTILINE)
    if m:
        return m.group(1)
    return "output"


def write_output_files(
    fn_name: str,
    code: str,
    spec_content: str,
    target_language: str = "c++",
) -> Path:
    cfg = LANGUAGE_CONFIGS.get(target_language, LANGUAGE_CONFIGS["c++"])
    out_dir = Path.cwd() / fn_name
    out_dir.mkdir(exist_ok=True)
    if code:
        (out_dir / f"{fn_name}{cfg['ext']}").write_text(code, encoding="utf-8")
    (out_dir / f"{fn_name}_spec.lean").write_text(spec_content, encoding="utf-8")
    return out_dir


# ---------------------------------------------------------------------------
# Cost estimation
# ---------------------------------------------------------------------------

def compute_cost(token_usage: dict) -> dict:
    ci = token_usage["codestral_input"]
    co = token_usage["codestral_output"]
    cost = (ci + co) * CODESTRAL_COST_PER_MTOKEN / 1_000_000
    return {
        "codestral_tokens": ci + co,
        "cost_codestral": cost,
        "cost_total": cost,
    }


# ---------------------------------------------------------------------------
# Pipeline
# ---------------------------------------------------------------------------

def run_pipeline(
    spec_content: str,
    on_event=None,
    target_language: str = "c++",
) -> dict:
    """
    3-step pipeline: parse → generate → write.
    Emits: spec_parsed, generating, streaming, api_retry, done, error.
    """
    cfg = LANGUAGE_CONFIGS.get(target_language, LANGUAGE_CONFIGS["c++"])

    def emit(name: str, data: dict = {}):
        if on_event:
            on_event(name, data)

    token_usage = {"codestral_input": 0, "codestral_output": 0}

    # Step 1: Parse
    imports, fn_stubs, thm_stubs = parse_spec(spec_content)
    fn_count = count_blocks(fn_stubs)
    thm_count = count_blocks(thm_stubs)
    fn_name = detect_function_name(spec_content)
    emit("spec_parsed", {"fn_count": fn_count, "thm_count": thm_count})

    # Step 2: Generate
    emit("generating", {})

    def on_chunk(chunk: str):
        emit("streaming", {"chunk": chunk})

    def on_retry(status, wait, attempt, max_retries):
        emit("api_retry", {"status": status, "wait": wait,
                           "attempt": attempt, "max_retries": max_retries})

    try:
        client = get_client()
        code = call_codestral(
            client, spec_content, token_usage,
            target_language=target_language,
            on_chunk=on_chunk, on_retry=on_retry,
        )
    except Exception as e:
        emit("error", {"message": str(e)})
        return {"success": False, "error": str(e)}

    # Step 3: Write files
    out_dir = write_output_files(fn_name, code, spec_content, target_language)
    cost = compute_cost(token_usage)

    emit("done", {
        "code": code,
        "output_dir": str(out_dir),
        "cost": cost,
        "fn_name": fn_name,
        "lang": target_language,
        "lang_ext": cfg["ext"],
        "lang_fence": cfg["fence"],
    })

    return {
        "success": True,
        "code": code,
        "output_dir": str(out_dir),
        "cost": cost,
        "token_usage": token_usage,
    }


# ---------------------------------------------------------------------------
# CLI fallback
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    import sys

    if len(sys.argv) < 2:
        print("Usage: python orchestrator.py <spec.lean> [language]")
        sys.exit(1)

    spec_path = Path(sys.argv[1])
    if not spec_path.exists():
        print(f"File not found: {spec_path}")
        sys.exit(1)

    lang = sys.argv[2] if len(sys.argv) > 2 else "c++"
    spec_content = spec_path.read_text(encoding="utf-8")

    def print_event(name, data):
        if name != "streaming":
            print(f"[{name}] {data}")

    result = run_pipeline(spec_content, on_event=print_event, target_language=lang)
    if result["success"]:
        print(f"\nOutput: {result['output_dir']}")
        cost = result["cost"]
        print(f"Cost: ${cost['cost_total']:.4f} ({cost['codestral_tokens']} tokens)")
    else:
        print(f"\nError: {result.get('error', '')}")
