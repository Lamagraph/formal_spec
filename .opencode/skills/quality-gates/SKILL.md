---
name: quality-gates
description: Use before merging a task to dev. Defines the hard gate that must pass (build + coqchk + coqdoc) and how to interpret its result. References docs/developer.md for the exact commands.
---

# Quality Gates

The hard gate a task must pass before merging. It has exactly two terminal
states: **PASS** or **BLOCKED**. There is no "pass with exceptions".

## What the gate is

The gate is the combination of the build, the independent re-check, and the
docs build. The exact commands live in `docs/developer.md`; this skill defines
only the gate semantics.

- **Build** — `make`. Every `.v` in `CoqProject` must compile under `coqc` with
  **zero** `Admitted`/`Admit`/`Abort`. This is the core check: a proof that
  compiles is verified.
- **Independent re-check** — `make validate` (coqchk). Must report no errors.
- **Docs build** — `make html` (coqdoc). Must exit 0.

The CI workflow (`.github/workflows/ci.yml`) is the source of truth for what the
gate runs in CI; this skill only defines the gate semantics.

## Procedure

1. Run `make`. It must succeed with zero `Admitted`/`Admit`/`Abort`.
2. Run `make validate`. It must report no errors.
3. Run `make html`. It must exit 0.
4. Interpret the result:
   - All clean → **PASS**. Proceed to merge (see `git-workflow`).
   - Any failure → **BLOCKED**.

## On BLOCKED

- STOP. Do not merge. Do not mark the task done.
- Do **not** assess whether a failure is pre-existing or unrelated to your
  changes — fix it regardless.
- Do **not** weaken a statement, `Admit` a goal, or skip a check to make the
  build green (see the Blocked Work Protocol in the `subtask-loop` skill).
- Fix every failure and re-run until **PASS**.
