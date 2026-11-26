---
name: build
description: Use when building the project or checking that proofs go through. The "test suite" of this project is the build itself: every module must compile under rocq (proofs check), plus QuickChick and extraction tests where used. Thin pointer to docs/developer.md for the exact commands; keeps the machine-specific pitfalls.
---

# Build

What the build is (dune with the Rocq build language: `dune build`, the
independent `rocqchk` re-check, `dune build @doc`) and where the exact
commands live are documented in `docs/developer.md`. Read that section before
running anything. This skill keeps only the machine-specific notes and the
Rocq-specific framing below.

## The build IS the test suite

A module that compiles under `rocq` has all of its definitions and proofs
checked by the kernel. There is no separate "run the tests" step for a theorem:

- **`dune build`** — compile every `.v` in dependency order. Green means every
  proof checks. This is the primary gate.
- **`rocqchk`** — re-verifies the compiled `.vo` files independently. The
  stronger, slower check (exact invocation in `docs/developer.md`).
- **`dune build @doc`** — rocqdoc renders the docs; also catches malformed
  comments.

QuickChick properties and extraction tests run *inside* the build (a
`QuickCheck` is a compile-time tactic; extracted files are emitted by
`dune build`), so they fail `dune build` when they fail. See
`docs/developer.md` for how to add them.

## Machine-specific notes

- **Build before validating.** `rocqchk` reads the compiled `.vo` files from
  the dune build tree. Run `dune build` first; validating a stale or missing
  `.vo` set reports spurious errors.
- **Bytecode vs native.** `dune build` builds bytecode (`.vo`). For large
  definitional work where the build is slow, `(mode vos)` in the
  `rocq.theory` stanza builds native (`.vos`) and skips proof checking — use
  it only for development, never for the gate; `rocqchk` works on either. Do
  not mix half-bytecode/half-native trees — `dune clean` first if you switch.
- **Library root.** The `rocq.theory` stanza's `name` (currently `LamaGraph`
  in `src/dune`) is the library root: only `.v` files under that theory's
  directory are in the library. A `.v` placed elsewhere is invisible to the
  build; put it under `src/` (or a sub-theory directory with its own `dune`
  file — see the `add-theory` skill).
- **QuickChick not installed.** If a module does `Require Import QuickChick`
  and the build fails on that import, the package is missing: `opam install
  coq-quickchick`, then rebuild. Do not delete the import to make the build
  green.
- **Stale state.** If the build behaves inconsistently after manual edits or
  partial deletes, `dune clean` and rebuild from scratch rather than debugging
  phantom dependencies.
