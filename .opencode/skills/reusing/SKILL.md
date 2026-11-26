---
name: reusing
description: Use before creating any new code, definitions, lemmas, or documentation. Run this reuse checklist to find existing material to reuse or generalize instead of duplicating — including existing Rocq/Coq libraries (the ecosystem). Enforces the "one source of truth / no duplicates" principle.
---

# Reusing

Before writing new Coq or docs, search for existing material and reuse or
generalize it. Duplicating an existing definition, lemma, notation, or doc
section violates the project's single-source-of-truth principle.

## Checklist

Run through these before creating new material:

- [ ] **Existing theories** — search `src/` for an existing definition, record,
      or lemma that already does (or nearly does) the job. Prefer generalizing
      the existing one over adding a near-copy.
- [ ] **Basics** — check `src/Basics.v` for a notation, import, or foundational
      lemma to reuse rather than re-declare in a module.
- [ ] **INet layer** — check `src/INet/` for an existing encoding of agents,
      nets, or the rewrite relation before re-encoding it in `Arch`.
- [ ] **Lemmas** — check for an existing inversion/injectivity/induction lemma
      that a new proof can call, instead of re-proving it inline.
- [ ] **Tactics** — check for an existing custom tactic or proof pattern to
      reuse rather than re-deriving it.
- [ ] **Tests** — check `tests/` for existing QuickChick properties or
      extraction harnesses to extend rather than duplicate.
- [ ] **Docs** — check `docs/` and existing coqdoc comments for a section to
      update rather than add a new page.
- [ ] **External libraries** — before defining foundational material
      (arithmetic, orders, relations, containers, …), check whether an
      existing Rocq/Coq library provides it (see "External libraries" below).

## External libraries

The checklist extends to the ecosystem: before defining foundational
material, prefer an existing Rocq/Coq library over a local re-implementation
(the "adopt existing libraries" principle in `AGENTS.md`).

- **Search:** `opam search` (opam-coq-archive is the canonical registry for
  Rocq/Coq packages), GitHub, the Rocq/Coq community.
- **Evaluate:** compatibility with the pinned toolchain (Rocq 9.3, dune >=
  3.24 — check the library's opam bounds and CI); maintenance status; license
  compatibility (the project is MIT); fit (does it provide the
  statements/abstractions the development needs?); weight (dependency size,
  CI build time — Mathlib-class dependencies are heavy).
- **Adopt:** add it as an opam dependency (bounds are floors — the
  manual-opam decision in `docs/developer.md`); `Require Import` it in the
  consuming module. External libraries sit below all project layers (like
  Stdlib), so the layering rule is preserved.
- **Record:** a non-trivial adoption (large/central library) is a design
  decision — record it in `docs/design.md` under "Standing design decisions"
  (per the `documentation` skill's mapping). If nothing fits, roll your own
  minimally and record why existing libraries didn't fit (subtask plan /
  commit message).

## Rules

- If a close match exists, **generalize it** (make it polymorphic enough to
  cover both cases) rather than copy-paste.
- Respect the layering in `docs/design.md`: reuse flows downward (a higher layer
  reuses a lower one), never upward.
- Record what is reused in each subtask's **Code** section of
  `tasks/detailed_plan.md`.
- When in doubt, prefer the existing abstraction; only create new material when
  no reasonable generalization is possible.
