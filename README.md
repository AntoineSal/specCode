# speccode

> Write what your function must do. Get correct code back.

![Python 3.9+](https://img.shields.io/badge/python-3.9%2B-blue?style=flat-square)
![Lean 4](https://img.shields.io/badge/Lean-4-purple?style=flat-square)
![Mistral API](https://img.shields.io/badge/Mistral-Codestral-orange?style=flat-square)
![License: MIT](https://img.shields.io/badge/license-MIT-green?style=flat-square)
[![GitHub](https://img.shields.io/badge/GitHub-AntoineSal%2FspecCode-lightgrey?style=flat-square&logo=github)](https://github.com/AntoineSal/specCode)

---

**speccode** is a command-line tool that generates code from formal Lean 4 specifications.
Instead of describing what you want in natural language, you write a mathematically precise
specification — and speccode generates the implementation.

## Philosophy

Most AI coding tools take natural language as input.
Natural language is ambiguous.

speccode takes **Lean 4 formal specifications** as input —
function signatures and mathematical theorems that describe
exactly what the code must do. No ambiguity. No hand-waving.

This is **spec coding**: shift the programmer's work from
writing code to modeling concepts as formal specifications.
The machine handles the implementation.

speccode is not just a code generator — it is a project management system centered on
specifications. A speccode project IS its specs. The generated code is a derived artifact,
like a compiled binary. At any point, the entire project can be rebuilt from its
specifications with a single command.

The long-term vision: when a spec is submitted, speccode will not only generate the
implementation but formally prove it correct using Lean 4's type-checker and Mathlib4.
Every theorem in the spec becomes a machine-checked guarantee. The code is not just
generated — it is proven.

## Example

### Single function

Write this spec in your editor:

```lean
def insertionSort (l : List Int) : List Int := sorry

theorem insertionSort_sorted (l : List Int) :
    List.Sorted (· ≤ ·) (insertionSort l) := sorry

theorem insertionSort_perm (l : List Int) :
    insertionSort l ~ l := sorry
```

Get back verified C++ (or Python, Rust, OCaml, Go, TypeScript).

### Multi-function project with dependencies

Once `myInsert` exists in your project, write a spec that declares its dependency:

```lean
-- language: c++
-- depends: myInsert
def insertionSort (l : List Int) : List Int := sorry

theorem insertionSort_sorted (l : List Int) :
    List.Sorted (· ≤ ·) (insertionSort l) := sorry

theorem insertionSort_perm (l : List Int) :
    insertionSort l ~ l := sorry
```

speccode detects that `insertionSort` depends on `myInsert`, injects its signature into
the prompt, and generates code that calls `myInsert` directly — without you having to
explain how.

## Installation

```bash
git clone https://github.com/AntoineSal/specCode.git
cd specCode
./setup.sh
```

Add your Mistral API key to `.env`:

```
MISTRAL_API_KEY=your_key_here
```

Get a free key at [console.mistral.ai](https://console.mistral.ai).

## Usage

```bash
speccode
```

The interactive TUI opens with an ASCII art banner, then the main menu:

```
  [e] new spec    [l] language    [q] quit
```

- **[e]** — open your editor, write a Lean 4 spec, save and close
- **[l]** — choose the output language (C++, Python, Rust, OCaml, Go, TypeScript)
- **[q]** — quit

### Validation

Before generating, speccode validates your spec with a pure-Python Lean 4 checker.
If there are errors (missing `sorry`, unbalanced parentheses, late imports…), they are
shown inline and injected as comments at the top of the editor file when you press **[e]**
to retry:

```
-- ✗ line 3, col 5: unknown identifier 'Lst'

def myFunction ...
```

`sorry` entries are intentional — they mark stubs and unproven theorems and are not treated
as errors.

### Project mode

When you run `speccode` in a directory containing a `speccode.context` file, project mode
activates automatically:

```
◆ project: myapp  ·  3 functions  ·  c++

  [e] new spec    [r] rebuild    [p] project    [l] language    [q] quit
```

- **[p]** — view all specs, functions, theorems, and dependencies
- **[r]** — rebuild all functions from their specs in dependency order

If any spec file has changed since its last generation, speccode warns you before the menu:

```
⚠ 1 spec(s) have changed — run [r] to rebuild
```

### Project structure

speccode organises your project automatically:

```
myapp/
├── speccode.context     ← project index (auto-maintained)
├── specs/               ← what YOU write
│   ├── myInsert.lean
│   └── insertionSort.lean
├── src/                 ← generated code (artifact)
│   ├── myInsert.cpp
│   ├── myInsert.hpp
│   └── insertionSort.cpp
└── SPECS.md             ← auto-generated documentation
```

`SPECS.md` is regenerated automatically after every run — a human-readable summary of
every function, its spec, and its mathematical guarantees. It is the living documentation
of your project, derived entirely from the specs you wrote.

### Rebuild

From the command line, regenerate all functions in a project:

```bash
speccode --rebuild          # use project language
speccode --rebuild python   # override language
```

speccode reads `speccode.context`, processes every function in order, and rewrites `src/`
and `SPECS.md` entirely.

## Spec annotations

Lean specs support two optional header comments:

| Annotation | Example | Effect |
|------------|---------|--------|
| `-- language:` | `-- language: rust` | Override the project language for this spec |
| `-- depends:` | `-- depends: myInsert, myFind` | Declare dependencies — their signatures are injected into the prompt |

Dependencies are resolved automatically. speccode reads `speccode.context`, finds the
signatures of declared dependencies, and passes them to the model along with the
corresponding include or import directives. The generated code can call them directly.

## Supported output languages

| Key | Language | File |
|-----|----------|------|
| 1   | C++17    | `.cpp` |
| 2   | Python 3.10+ | `.py` |
| 3   | Rust (stable) | `.rs` |
| 4   | OCaml (functional) | `.ml` |
| 5   | Go 1.21+ | `.go` |
| 6   | TypeScript (strict) | `.ts` |

## Requirements

- Python 3.9+
- [Lean 4](https://leanprover.github.io/) + [Mathlib](https://leanprover-community.github.io/mathlib4_docs/)
- A [Mistral API key](https://console.mistral.ai) (Codestral model)
- `git` (for project context)
- `nano` or any `$EDITOR` (for spec editing)

## Roadmap

- [x] Code generation from Lean 4 specs
- [x] Multi-language output (C++, Python, Rust, OCaml, Go, TypeScript)
- [x] Project context — dependency injection between functions
- [x] Automatic `SPECS.md` documentation
- [x] Stale detection and rebuild
- [x] Lean spec validation before generation
- [ ] Tier 1 — automated proof tactics (`aesop`, `omega`, `simp_all`)
- [ ] Tier 2 — LeanDojo interactive proof search
- [ ] Tier 3 — LLM + Mathlib RAG for complex proofs
- [ ] `speccode --explain` — natural language explanation of any spec
- [ ] Auto-generated tests from theorem statements
- [ ] Full formal verification — proven correct code from specs

## About

speccode was built on the conviction that the hardest part of programming is not writing
code — it is precisely specifying what the code must do.

Formal specifications force clarity. They eliminate ambiguity. And when the tooling
matures, they will make correctness machine-checkable.

Until then, speccode is a daily driver for spec-first development: write the math, get
the code.

## License

MIT
