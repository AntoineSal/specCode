"""
speccode — orchestrator
Generates code from formal Lean 4 specifications.
"""

from __future__ import annotations

import datetime
import hashlib
import json
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


LEAN_TYPE_MAP: dict[str, dict[str, str]] = {
    "c++":        {"Nat": "uint32_t", "Int": "int32_t", "Bool": "bool", "Float": "double", "String": "std::string"},
    "python":     {"Nat": "int", "Int": "int", "Bool": "bool", "Float": "float", "String": "str"},
    "rust":       {"Nat": "u32", "Int": "i32", "Bool": "bool", "Float": "f64", "String": "String"},
    "ocaml":      {"Nat": "int", "Int": "int", "Bool": "bool", "Float": "float", "String": "string"},
    "go":         {"Nat": "uint32", "Int": "int32", "Bool": "bool", "Float": "float64", "String": "string"},
    "typescript": {"Nat": "number", "Int": "number", "Bool": "boolean", "Float": "number", "String": "string"},
}


def _map_lean_type(lean_type: str, language: str) -> str:
    return LEAN_TYPE_MAP.get(language, LEAN_TYPE_MAP["c++"]).get(lean_type, lean_type)


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
        f"- When project context is provided, always include the specified headers/imports "
        f"at the top of your file. Never reimplement a function that is already available "
        f"in the project context.\n"
        f"\n"
        f"CRITICAL — theorems vs implementations:\n"
        f"- `def` blocks describe functions TO IMPLEMENT — generate code for these\n"
        f"- `theorem` and `lemma` blocks describe MATHEMATICAL PROPERTIES that the "
        f"implementation must satisfy — do NOT generate code or functions for these\n"
        f"- do NOT translate theorems into boolean functions\n"
        f"- do NOT add _mem, _sorted, _length functions derived from theorem names\n"
        f"- Theorems are proof obligations, not code.\n"
        f"\n"
        f"CRITICAL — type dependencies:\n"
        f"- If a `structure` is defined in the spec, translate it as a proper struct/class "
        f"in the target language\n"
        f"- Never replace a named struct with a generic container like vector<uint32_t> or tuple\n"
        f"- If `-- depends: X` is declared and X defines a structure, assume that structure "
        f"is available with its exact fields and use it directly by name\n"
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
# Lean error parsing
# ---------------------------------------------------------------------------

def clean_lean_error(output: str) -> list[str]:
    """Parse lake build output and return cleaned error messages (one per line)."""
    cleaned: list[str] = []
    for line in output.splitlines():
        if "error:" not in line:
            continue
        m = re.match(r".*?:(\d+):(\d+):\s*error:\s*(.*)", line)
        if m:
            cleaned.append(f"line {m.group(1)}, col {m.group(2)}: {m.group(3)}")
        else:
            cleaned.append(re.sub(r"^[^\s]*:\s*", "", line).strip())
    return cleaned


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
    context_block: str = "",
    kind: str = "function",
) -> str:
    """
    Call Codestral with streaming. Emits each text chunk via on_chunk(text).
    Returns the generated code extracted from the language-specific section.
    """
    cfg = LANGUAGE_CONFIGS.get(target_language, LANGUAGE_CONFIGS["c++"])
    system_prompt = get_codestral_system(target_language)

    if kind == "type":
        type_preamble = (
            "Generate ONLY a header file for this type. "
            "No implementation file needed. "
            "Include a proper struct/class definition with all fields from the Lean spec."
        )
        if context_block:
            user_content = (
                f"Project context:\n{context_block}\n\n"
                f"{type_preamble}\n\n"
                f"Spec:\n```lean\n{spec_content}\n```"
            )
        else:
            user_content = (
                f"{type_preamble}\n\n"
                f"Lean 4 type specification:\n\n```lean\n{spec_content}\n```"
            )
    elif context_block:
        user_content = (
            f"Project context:\n{context_block}\n\n"
            f"Spec:\n```lean\n{spec_content}\n```"
        )
    else:
        user_content = f"Partial Lean 4 specification:\n\n```lean\n{spec_content}\n```"

    messages = [
        {"role": "system", "content": system_prompt},
        {"role": "user", "content": user_content},
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

def detect_spec_kind(spec_content: str) -> str:
    """Return "type" if the spec defines a type with no functions, else "function"."""
    has_type = bool(re.search(r"^(structure|inductive|abbrev|class)\s+", spec_content, re.MULTILINE))
    has_def = bool(re.search(r"^def\s+", spec_content, re.MULTILINE))
    if has_type and not has_def:
        return "type"
    return "function"


def extract_type_fields(spec_content: str) -> list[str]:
    """Parse field names and types from a Lean structure block."""
    fields: list[str] = []
    in_structure = False
    for line in spec_content.splitlines():
        if re.match(r"^structure\s+\w+.*\bwhere\b", line):
            in_structure = True
            continue
        if in_structure:
            m = re.match(r"^\s+(\w+)\s*:\s*(.+)", line)
            if m:
                fields.append(f"{m.group(1)}: {m.group(2).strip()}")
            elif line.strip() == "" or re.match(r"^\S", line):
                in_structure = False
    return fields


def detect_function_name(spec_content: str) -> str:
    """Extract first def name from spec for output directory naming."""
    m = re.search(r"^def\s+(\w+)", spec_content, re.MULTILINE)
    if m:
        return m.group(1)
    return "output"


def detect_type_name(spec_content: str) -> str:
    """Extract the first structure/inductive/abbrev/class name from spec."""
    m = re.search(r"^(?:structure|inductive|abbrev|class)\s+(\w+)", spec_content, re.MULTILINE)
    if m:
        return m.group(1)
    return "output"


def write_output_files(
    fn_name: str,
    code: str,
    spec_content: str,
    target_language: str = "c++",
    project_dir: Path | None = None,
    kind: str = "function",
) -> Path:
    cfg = LANGUAGE_CONFIGS.get(target_language, LANGUAGE_CONFIGS["c++"])
    if project_dir is None:
        project_dir = Path.cwd()
    specs_dir = project_dir / "specs"
    src_dir = project_dir / "src"
    specs_dir.mkdir(exist_ok=True)
    src_dir.mkdir(exist_ok=True)
    if code:
        if kind == "type":
            # Type specs generate only a header — no implementation file
            (src_dir / f"{fn_name}.hpp").write_text(code, encoding="utf-8")
        else:
            (src_dir / f"{fn_name}{cfg['ext']}").write_text(code, encoding="utf-8")
            _write_header_file(src_dir, fn_name, code, target_language)
    (specs_dir / f"{fn_name}.lean").write_text(spec_content, encoding="utf-8")
    return project_dir


def _infer_cpp_includes(sig: str) -> list[str]:
    """Return #include directives inferred from a C++ signature."""
    seen: set[str] = set()
    result: list[str] = []

    def add(h: str) -> None:
        if h not in seen:
            seen.add(h)
            result.append(h)

    _STD = {
        "std::vector": "<vector>",
        "std::optional": "<optional>",
        "std::string": "<string>",
        "std::pair": "<utility>",
        "std::tuple": "<tuple>",
        "std::map": "<map>",
        "std::unordered_map": "<unordered_map>",
        "std::set": "<set>",
        "std::unordered_set": "<unordered_set>",
        "std::list": "<list>",
        "std::deque": "<deque>",
        "std::array": "<array>",
        "std::stack": "<stack>",
        "std::queue": "<queue>",
        "std::priority_queue": "<queue>",
        "std::function": "<functional>",
        "std::shared_ptr": "<memory>",
        "std::unique_ptr": "<memory>",
        "std::weak_ptr": "<memory>",
        "std::variant": "<variant>",
        "std::any": "<any>",
        "std::span": "<span>",
    }
    for pattern, header in _STD.items():
        if pattern in sig:
            add(header)

    if re.search(r"\b(?:u?int(?:8|16|32|64)_t|size_t)\b", sig):
        add("<cstdint>")

    # Custom types: uppercase-starting word not preceded by ::
    for t in dict.fromkeys(re.findall(r"(?<![:\w])([A-Z][A-Za-z0-9_]*)", sig)):
        add(f'"{t}.hpp"')

    return result


def _write_header_file(src_dir: Path, fn_name: str, code: str, language: str) -> None:
    """Generate a declaration/header file for the given function."""
    sig = extract_signature(code, language)

    if language == "c++":
        includes = _infer_cpp_includes(sig) if sig else []
        include_block = "".join(f"#include {h}\n" for h in includes)
        decl = f"{sig};\n" if sig else "// signature extraction failed\n"
        content = f"// Auto-generated by speccode\n#pragma once\n{include_block}{decl}"
        (src_dir / f"{fn_name}.hpp").write_text(content, encoding="utf-8")
    elif language == "python" and sig:
        content = f"# Auto-generated by speccode\n{sig}: ...\n"
        (src_dir / f"_{fn_name}_stub.pyi").write_text(content, encoding="utf-8")
    elif language == "rust" and sig:
        content = f"// Auto-generated by speccode\n{sig.rstrip()};\n"
        (src_dir / f"{fn_name}.rlib.stub").write_text(content, encoding="utf-8")
    elif language == "ocaml":
        content = f"(* Auto-generated by speccode *)\nval {fn_name} : 'a\n"
        (src_dir / f"{fn_name}.mli").write_text(content, encoding="utf-8")
    elif language == "go" and sig:
        content = f"// Auto-generated by speccode\n{sig}\n"
        (src_dir / f"{fn_name}_decl.go").write_text(content, encoding="utf-8")
    elif language == "typescript" and sig:
        content = f"// Auto-generated by speccode\nexport declare {sig};\n"
        (src_dir / f"{fn_name}.d.ts").write_text(content, encoding="utf-8")


# ---------------------------------------------------------------------------
# Project context
# ---------------------------------------------------------------------------

CONTEXT_FILE = "speccode.context"


def load_context(project_dir: Path) -> dict | None:
    """Read speccode.context if it exists, else return None."""
    path = project_dir / CONTEXT_FILE
    if not path.exists():
        return None
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return None


def save_context(project_dir: Path, context: dict) -> None:
    """Write speccode.context (indented JSON)."""
    context["updated_at"] = datetime.date.today().isoformat()
    path = project_dir / CONTEXT_FILE
    path.write_text(json.dumps(context, indent=2), encoding="utf-8")


def init_context(project_dir: Path, language: str) -> dict:
    """Create a new empty context for this project."""
    return {
        "project": project_dir.name,
        "language": language,
        "created_at": datetime.date.today().isoformat(),
        "updated_at": datetime.date.today().isoformat(),
        "functions": [],
    }


def update_context_entry(
    context: dict,
    fn_name: str,
    spec_file: str,
    spec_content: str,
    code_file: str,
    signature: str,
    language: str,
    theorems: list[str],
    kind: str = "function",
    fields: list[str] | None = None,
) -> dict:
    """Add or update an entry in context['functions']."""
    spec_hash = hashlib.sha256(spec_content.encode()).hexdigest()[:8]

    # Parse "-- depends: funcA, funcB" comments
    depends_on: list[str] = []
    for m in re.finditer(r"--\s*depends:\s*(.+)", spec_content):
        deps = [d.strip() for d in m.group(1).split(",") if d.strip()]
        depends_on.extend(deps)

    generated_at = datetime.datetime.now().isoformat(timespec="seconds")

    entry = {
        "name": fn_name,
        "spec_file": spec_file,
        "spec_hash": spec_hash,
        "code_file": code_file,
        "signature": signature,
        "depends_on": depends_on,
        "generated_at": generated_at,
        "language": language,
        "theorems": theorems,
        "kind": kind,
        "fields": fields or [],
    }

    # Replace existing entry with same name, or append
    functions = context.get("functions", [])
    for i, fn in enumerate(functions):
        if fn.get("name") == fn_name:
            functions[i] = entry
            context["functions"] = functions
            return context

    functions.append(entry)
    context["functions"] = functions
    return context


def extract_signature(code: str, language: str) -> str:
    """Extract the first function signature from generated code."""
    if language == "python":
        m = re.search(
            r"^(def\s+\w+\s*\([^)]*\)(?:\s*->\s*[\w\[\], |None]+)?)",
            code, re.MULTILINE,
        )
        return m.group(1).strip() if m else ""
    elif language == "rust":
        m = re.search(
            r"^((?:pub\s+)?fn\s+\w+[^{]+)",
            code, re.MULTILINE,
        )
        return m.group(1).strip().rstrip() if m else ""
    else:  # c++ and others
        m = re.search(
            r"^([\w:*&<>\[\]]+(?:\s+[\w:*&<>\[\]]+)*\s+\w+\s*\([^{;]*\))",
            code, re.MULTILINE,
        )
        return m.group(1).strip() if m else ""


def generate_specs_md(context: dict, project_dir: Path) -> str:
    """Generate the content of SPECS.md from the current context."""
    project_name = context.get("project", project_dir.name)
    language = context.get("language", "c++")
    cfg = LANGUAGE_CONFIGS.get(language, LANGUAGE_CONFIGS["c++"])
    ext = cfg["ext"].lstrip(".")

    lines = [
        f"# {project_name}",
        "",
        "> This project is defined by its specifications.",
        "> All code can be regenerated with `speccode --rebuild`.",
        "",
        "## Functions",
        "",
    ]

    for fn in context.get("functions", []):
        fn_name = fn["name"]
        spec_path = project_dir / fn.get("spec_file", f"specs/{fn_name}.lean")
        generated_at = fn.get("generated_at", "")

        try:
            spec_content = spec_path.read_text(encoding="utf-8")
        except FileNotFoundError:
            spec_content = ""

        lines += [
            f"### {fn_name}",
            f"**Spec:** `specs/{fn_name}.lean`  ",
            f"**Output:** `src/{fn_name}.{ext}` ({language})  ",
            f"**Generated:** {generated_at}",
            "",
            "```lean",
            spec_content.strip(),
            "```",
            "",
            "---",
            "",
        ]

    return "\n".join(lines)


def check_stale(context: dict, project_dir: Path) -> list[str]:
    """Return names of functions whose spec has changed since last generation."""
    stale: list[str] = []
    for fn in context.get("functions", []):
        fn_name = fn.get("name", "")
        stored_hash = fn.get("spec_hash", "")
        spec_file = project_dir / fn.get("spec_file", f"specs/{fn_name}.lean")
        try:
            current = spec_file.read_text(encoding="utf-8")
            current_hash = hashlib.sha256(current.encode()).hexdigest()[:8]
            if current_hash != stored_hash:
                stale.append(fn_name)
        except FileNotFoundError:
            stale.append(fn_name)
    return stale


def get_context_for_prompt(
    context: dict,
    spec_content: str,
    project_dir: Path,
    max_functions: int = 5,
    target_language: str = "c++",
    current_fn_name: str = "",
) -> str:
    """Build the context block to inject into the Codestral prompt."""
    functions = context.get("functions", [])
    if not functions:
        return ""

    # 1. Parse explicit dependencies
    explicit_deps: list[str] = []
    for m in re.finditer(r"--\s*depends:\s*(.+)", spec_content):
        explicit_deps.extend(d.strip() for d in m.group(1).split(",") if d.strip())

    # 2. Gather candidate functions
    selected: list[dict] = []
    seen: set[str] = set()

    # Priority: explicit deps first
    for fn in functions:
        if fn["name"] == current_fn_name:
            continue  # ne pas s'injecter soi-même
        if fn["name"] in explicit_deps and fn["name"] not in seen:
            selected.append(fn)
            seen.add(fn["name"])
            if len(selected) >= max_functions:
                break

    # Fill up to max_functions with functions whose name appears in spec_content
    for fn in functions:
        if len(selected) >= max_functions:
            break
        if fn["name"] == current_fn_name:
            continue  # ne pas s'injecter soi-même
        if fn["name"] not in seen and fn["name"] in spec_content:
            selected.append(fn)
            seen.add(fn["name"])

    if not selected:
        return ""

    # 3. Separate types and functions
    type_entries = [fn for fn in selected if fn.get("kind") == "type"]
    fn_entries = [fn for fn in selected if fn.get("kind", "function") == "function"]

    lines: list[str] = []

    if type_entries:
        lines.append("Available types in this project:")
        for fn in type_entries:
            name = fn["name"]
            raw_fields = fn.get("fields", [])
            mapped_fields: list[str] = []
            for f in raw_fields:
                if ":" in f:
                    fname, ftype = f.split(":", 1)
                    mapped_fields.append(f"{fname.strip()}: {_map_lean_type(ftype.strip(), target_language)}")
                else:
                    mapped_fields.append(f)
            lines.append(f" — {name} (struct)")
            if mapped_fields:
                lines.append(f"   fields: {', '.join(mapped_fields)}")
            lines.append(f'   include: #include "{name}.hpp"')
        lines.append("")

    if fn_entries:
        lines.append("Available functions in this project:")
        for fn in fn_entries:
            sig = fn.get("signature", "")
            theorems = fn.get("theorems", [])
            code_file = fn.get("code_file", "")
            thm_summary = ", ".join(theorems) if theorems else ""

            lines.append(f"  — {sig or fn['name']}")
            if thm_summary:
                lines.append(f"    spec: {thm_summary}")
            if code_file:
                lines.append(f"    file: {code_file}")
        lines.append("")
        lines.append("You may call these functions directly.")

        # 4. Build include/import instructions for functions
        include_lines = _build_include_lines(fn_entries, target_language)
        if include_lines:
            lines.append("")
            lines.append("Add these includes at the top of your file:")
            lines.extend(f"  {inc}" for inc in include_lines)

    return "\n".join(lines)


def _build_include_lines(selected: list[dict], language: str) -> list[str]:
    """Return the include/import lines for the selected functions."""
    lines: list[str] = []
    for fn in selected:
        name = fn["name"]
        if language == "c++":
            lines.append(f'#include "{name}.hpp"')
        elif language == "python":
            lines.append(f"from .{name} import {name}")
        elif language == "rust":
            lines.append(f"mod {name};")
            lines.append(f"use {name}::{name};")
        elif language == "ocaml":
            lines.append(f"open {name.capitalize()}")
        elif language == "go":
            lines.append(f"// {name} is available in this package")
        elif language == "typescript":
            lines.append(f'import {{ {name} }} from "./{name}";')
    return lines


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
    project_dir: Path | None = None,
) -> dict:
    """
    3-step pipeline: parse → generate → write.
    Emits: spec_parsed, generating, streaming, api_retry, done, error, context_updated.
    """
    cfg = LANGUAGE_CONFIGS.get(target_language, LANGUAGE_CONFIGS["c++"])

    if project_dir is None:
        project_dir = Path.cwd()

    def emit(name: str, data: dict = {}):
        if on_event:
            on_event(name, data)

    token_usage = {"codestral_input": 0, "codestral_output": 0}

    # Step 0: Load / init context
    context = load_context(project_dir)
    if context is None:
        context = init_context(project_dir, target_language)
    # Step 1: Parse
    kind = detect_spec_kind(spec_content)
    imports, fn_stubs, thm_stubs = parse_spec(spec_content)
    fn_count = count_blocks(fn_stubs)
    thm_count = count_blocks(thm_stubs)
    fn_name = detect_type_name(spec_content) if kind == "type" else detect_function_name(spec_content)

    context_block = get_context_for_prompt(
        context, spec_content, project_dir,
        target_language=target_language,
        current_fn_name=fn_name,
    )
    emit("spec_parsed", {"fn_count": fn_count, "thm_count": thm_count, "kind": kind})

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
            context_block=context_block,
            kind=kind,
        )
    except Exception as e:
        emit("error", {"message": str(e)})
        return {"success": False, "error": str(e)}

    # Step 3: Write files (specs/ and src/)
    out_dir = write_output_files(fn_name, code, spec_content, target_language, project_dir, kind=kind)
    cost = compute_cost(token_usage)

    # Step 4: Update context
    spec_file = f"specs/{fn_name}.lean"
    code_file = f"src/{fn_name}.hpp" if kind == "type" else f"src/{fn_name}{cfg['ext']}"
    signature = "" if kind == "type" else extract_signature(code, target_language)
    theorems = re.findall(r"^(?:theorem|lemma)\s+(\w+)", spec_content, re.MULTILINE)
    fields = extract_type_fields(spec_content) if kind == "type" else []
    context = update_context_entry(
        context,
        fn_name=fn_name,
        spec_file=spec_file,
        spec_content=spec_content,
        code_file=code_file,
        signature=signature,
        language=target_language,
        theorems=theorems,
        kind=kind,
        fields=fields,
    )
    save_context(project_dir, context)
    specs_md = generate_specs_md(context, project_dir)
    (project_dir / "SPECS.md").write_text(specs_md, encoding="utf-8")
    emit("context_updated", {"fn_count": len(context["functions"])})

    emit("done", {
        "code": code,
        "output_dir": str(out_dir),
        "src_file": str(out_dir / code_file),
        "spec_file": str(out_dir / spec_file),
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
# Demo main generation
# ---------------------------------------------------------------------------

def _build_main_imports(entries: list[dict], language: str) -> list[str]:
    """Return the mandatory import/include lines for a main file."""
    lines: list[str] = []
    for fn in entries:
        name = fn["name"]
        if language == "c++":
            lines.append(f'#include "{name}.hpp"')
        elif language == "python":
            lines.append(f"from {name} import {name}")
        elif language == "rust":
            lines.append(f"mod {name};")
            lines.append(f"use {name}::{name};")
        elif language == "ocaml":
            lines.append(f"open {name[0].upper() + name[1:]}")
        elif language == "typescript":
            lines.append(f'import {{ {name} }} from "./{name}";')
        # Go: same package, no imports needed
    return lines


def generate_main(
    context: dict,
    project_dir: Path,
    target_language: str = "c++",
    on_chunk=None,
) -> str:
    """
    Generate a demonstration main file illustrating all project functions.
    Writes src/main.{ext} and adds a kind="demo" entry to context.
    Returns the generated code.
    """
    cfg = LANGUAGE_CONFIGS.get(target_language, LANGUAGE_CONFIGS["c++"])

    all_entries = context.get("functions", [])
    type_entries = [f for f in all_entries if f.get("kind") == "type"]
    fn_entries = [f for f in all_entries if f.get("kind", "function") == "function"]
    callable_entries = type_entries + fn_entries

    # Read the actual source files so the model sees exact APIs
    existing_sources: list[str] = []
    for entry in callable_entries:
        code_path = project_dir / entry.get("code_file", "")
        if code_path.exists():
            src = code_path.read_text(encoding="utf-8").strip()
            existing_sources.append(
                f"=== {entry.get('code_file', entry['name'])} ===\n{src}"
            )

    # Build the mandatory import block
    import_lines = _build_main_imports(callable_entries, target_language)
    import_block = "\n".join(import_lines)

    # Describe each function to demonstrate
    fn_desc: list[str] = []
    for fn in fn_entries:
        sig = fn.get("signature", fn["name"])
        theorems = fn.get("theorems", [])
        fn_desc.append(f"  {sig}")
        if theorems:
            fn_desc.append(f"    // proves: {', '.join(theorems)}")

    system_prompt = (
        f"You are writing ONLY the main entry point for a {cfg['display']} project.\n"
        f"The other source files already exist and are complete — DO NOT redefine or copy any function.\n"
        f"\n"
        f"CRITICAL RULES:\n"
        f"- Your file must start with EXACTLY these imports (copy them verbatim):\n"
        + "\n".join(f"  {l}" for l in import_lines) + "\n"
        f"- After the imports, define only main() (or equivalent entry point)\n"
        f"- NEVER redefine, copy, or re-implement any function from the existing files\n"
        f"- Call each function with realistic example data and print the results\n"
        f"- The file must compile and run alongside the existing source files without modifications\n"
    )

    sources_section = (
        "\n\nExisting source files (already compiled alongside main — use them, do not copy them):\n\n"
        + "\n\n".join(existing_sources)
    ) if existing_sources else ""

    user_content = (
        f"Project: {context.get('project', 'project')}\n"
        f"Language: {cfg['display']}\n"
        f"\nFunctions to demonstrate:\n" + "\n".join(fn_desc)
        + sources_section
        + f"\n\nWrite the {cfg['display']} main file. Start with the imports listed above."
    )

    messages = [
        {"role": "system", "content": system_prompt},
        {"role": "user", "content": user_content},
    ]

    client = get_client()
    token_usage = {"codestral_input": 0, "codestral_output": 0}
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
            if chunk.usage:
                token_usage["codestral_input"] += chunk.usage.prompt_tokens or 0
                token_usage["codestral_output"] += chunk.usage.completion_tokens or 0

    api_call_with_retry(_call)
    raw = "".join(accumulated)

    # Extract first fenced code block
    m = re.search(rf"```(?:{re.escape(cfg['fence'])}|[a-zA-Z+]*)\n(.*?)```", raw, re.DOTALL)
    code = m.group(1).strip() if m else raw.strip()

    # Write src/main.{ext}
    src_dir = project_dir / "src"
    src_dir.mkdir(exist_ok=True)
    (src_dir / f"main{cfg['ext']}").write_text(code, encoding="utf-8")

    # Add/update demo entry in context
    demo_entry = {
        "name": "main",
        "kind": "demo",
        "code_file": f"src/main{cfg['ext']}",
        "generated_at": datetime.datetime.now().isoformat(timespec="seconds"),
        "language": target_language,
    }
    fns = context.get("functions", [])
    for i, fn in enumerate(fns):
        if fn.get("name") == "main" and fn.get("kind") == "demo":
            fns[i] = demo_entry
            break
    else:
        fns.append(demo_entry)
    context["functions"] = fns
    save_context(project_dir, context)

    return code


# ---------------------------------------------------------------------------
# CLI fallback
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    import sys

    if len(sys.argv) < 2:
        print("Usage: python orchestrator.py <spec.lean> [language]")
        print("       python orchestrator.py --rebuild [language]")
        sys.exit(1)

    def print_event(name, data):
        if name != "streaming":
            print(f"[{name}] {data}")

    if sys.argv[1] == "--rebuild":
        lang = sys.argv[2] if len(sys.argv) > 2 else "c++"
        project_dir = Path.cwd()
        context = load_context(project_dir)
        if context is None:
            print("No speccode.context found in current directory.")
            sys.exit(1)

        functions = context.get("functions", [])
        print(f"Rebuilding {len(functions)} function(s) in {project_dir.name}...")
        for fn in functions:
            fn_name = fn["name"]
            spec_path = project_dir / fn.get("spec_file", f"specs/{fn_name}.lean")
            if not spec_path.exists():
                print(f"  [skip] {fn_name}: spec file not found ({spec_path})")
                continue
            print(f"  [{fn_name}] regenerating...")
            spec_content = spec_path.read_text(encoding="utf-8")
            result = run_pipeline(
                spec_content,
                on_event=print_event,
                target_language=lang,
                project_dir=project_dir,
            )
            if result["success"]:
                cost = result["cost"]
                print(f"  [{fn_name}] done — ${cost['cost_total']:.4f}")
            else:
                print(f"  [{fn_name}] error: {result.get('error', '')}")
        print("Rebuild complete.")
        sys.exit(0)

    spec_path = Path(sys.argv[1])
    if not spec_path.exists():
        print(f"File not found: {spec_path}")
        sys.exit(1)

    lang = sys.argv[2] if len(sys.argv) > 2 else "c++"
    spec_content = spec_path.read_text(encoding="utf-8")

    result = run_pipeline(
        spec_content,
        on_event=print_event,
        target_language=lang,
        project_dir=Path.cwd(),
    )
    if result["success"]:
        print(f"\nOutput: {result['output_dir']}")
        cost = result["cost"]
        print(f"Cost: ${cost['cost_total']:.4f} ({cost['codestral_tokens']} tokens)")
    else:
        print(f"\nError: {result.get('error', '')}")
