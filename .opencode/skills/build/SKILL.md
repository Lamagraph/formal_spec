---
name: build
description: Use when building the project or checking that proofs go through. The "test suite" of this project is the build itself: every module must compile under coqc (proofs check), plus QuickChick and extraction tests where used. Thin pointer to docs/developer.md for the exact commands; keeps the machine-specific pitfalls.
---

# Build

What the build is (coq_makefile, the `make` / `make validate` / `make html`
targets) and where the exact commands live are documented in
`docs/developer.md`. Read that section before running anything. This skill keeps
only the machine-specific notes and the Coq-specific framing below.

## The build IS the test suite

A module that compiles under `coqc` has all of its definitions and proofs
checked by the kernel. There is no separate "run the tests" step for a theorem:

- **`make`** — compile every `.v` in `CoqProject`. Green means every proof
  checks. This is the primary gate.
- **`make validate`** — `coqchk` re-verifies the compiled `.vo` files
  independently. The stronger, slower check.
- **`make html`** — coqdoc renders the docs; also catches malformed comments.

QuickChick properties and extraction tests run *inside* the build (a
`QuickCheck` is a compile-time tactic; an extracted file is emitted by `make`),
so they fail `make` when they fail. See `docs/developer.md` for how to add them.

## Machine-specific notes

- **Build before validating.** `make validate` (coqchk) reads the compiled
  `.vo` files. Run `make` first; validating a stale or missing `.vo` set reports
  spurious errors.
- **Bytecode vs native.** `make` builds bytecode (`.vo`). For large proofs where
  the build is slow, `make opt` builds native (`.vos`) and is faster; `coqchk`
  works on either. Do not mix half-bytecode/half-native trees — `make clean`
  first if you switch.
- **Library root.** `-R src LamaGraph` in `CoqProject` means only files under
  `src/` are in the library. A `.v` placed elsewhere is invisible to the build;
  put it under `src/` and list it in `CoqProject`.
- **QuickChick not installed.** If a module does `Require Import QuickChick`
  and the build fails on that import, the package is missing: `opam install
  coq-quickchick`, then rebuild. Do not delete the import to make the build
  green.
- **Stale state.** If the build behaves inconsistently after manual edits or
  partial deletes, `make cleanall` and rebuild from scratch rather than
  debugging phantom dependencies.
