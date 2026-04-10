# speccode

> Write what your function must do. Get correct code back.

**speccode** is a command-line tool that generates code from
formal Lean 4 specifications. Instead of describing what you
want in natural language, you write a mathematically precise
specification — and speccode generates the implementation.

## Philosophy

Most AI coding tools take natural language as input.
Natural language is ambiguous.

speccode takes **Lean 4 formal specifications** as input —
function signatures and mathematical theorems that describe
exactly what the code must do. No ambiguity. No hand-waving.

This is **spec coding** : shift the programmer's work from
writing code to modeling concepts as formal specifications.
The machine handles the implementation.

Formally verified proofs are coming — when the tooling matures,
speccode will not only generate the code but prove it correct.

## Example

Write this spec in your editor:

```lean
def insertionSort (l : List Int) : List Int := sorry

theorem insertionSort_sorted (l : List Int) :
    List.Sorted (· ≤ ·) (insertionSort l) := sorry

theorem insertionSort_perm (l : List Int) :
    insertionSort l ~ l := sorry
```

Get back verified C++ (or Python, Rust, OCaml, Go, TypeScript).

## Installation

```bash
git clone https://github.com/AntoineSal/specCode.git
cd specCode
./setup.sh
```

Add your Mistral API key to `.env` :

```
MISTRAL_API_KEY=your_key_here
```

Get a free key at [console.mistral.ai](https://console.mistral.ai).

## Usage

```bash
speccode
```

The interactive TUI opens. From the main menu:

```
◆ speccode  —  lean specs → c++ code

  [e] new spec    [l] language    [q] quit
```

- **[e]** — open your editor, write a Lean 4 spec, save and close → code is generated
- **[l]** — choose the output language (C++, Python, Rust, OCaml, Go, TypeScript)
- **[q]** — quit

### Output

For a spec with `def insertionSort ...`, running the pipeline creates:

```
insertionSort/
  insertionSort.cpp       ← generated implementation
  insertionSort_spec.lean ← your original spec
```

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

- Python 3.10+
- [Lean 4](https://leanprover.github.io/) + [Mathlib](https://leanprover-community.github.io/mathlib4_docs/)
- A [Mistral API key](https://console.mistral.ai) (Codestral model)

## License

MIT
