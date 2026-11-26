---
name: reusing
description: Use before creating any new code, definitions, lemmas, or documentation. Run this reuse checklist to find existing material to reuse or generalize instead of duplicating. Enforces the "one source of truth / no duplicates" principle.
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

## Rules

- If a close match exists, **generalize it** (make it polymorphic enough to
  cover both cases) rather than copy-paste.
- Respect the layering in `docs/design.md`: reuse flows downward (a higher layer
  reuses a lower one), never upward.
- Record what is reused in each subtask's **Code** section of
  `tasks/detailed_plan.md`.
- When in doubt, prefer the existing abstraction; only create new material when
  no reasonable generalization is possible.
