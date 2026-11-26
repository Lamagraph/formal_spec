# tests/

Empirical checks for **definitions** — the places where random or executable
checking adds value beyond a proof. Theorems do not live here: a checked proof
in `src/` is the verification for a theorem.

Two kinds of test, both run as part of the build (see `docs/developer.md`):

- **QuickChick** — property-based (random) testing of Coq definitions. A
  `QuickCheck` is a compile-time tactic, so a failing property fails `make`.
  Requires `opam install coq-quickchick`.
- **Extraction** — extract a definition to OCaml and run it against reference
  behavior / test vectors.

Add a test here only when it guards a *definition* (an encoding, a function, a
data structure) — not a theorem. Keep the test's target named after the
definition it guards.
