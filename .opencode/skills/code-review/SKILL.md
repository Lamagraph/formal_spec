---
name: code-review
description: Use after all subtasks are committed and before merging a task to dev. Perform a whole-repo review of the task's changes, iterate to zero findings.
---

# Code Review

Run after all subtasks are committed, before the quality gate and merge. Review
the entire repo's diff for the task and iterate until there are zero findings.

## Procedure

1. Determine the task's changes: `git diff --stat dev...HEAD` and
   `git diff dev...HEAD`.
2. Review against the checklist below.
3. For every finding, fix it in a follow-up commit on the same feature branch
   (one commit per subtask/fix as per `git-workflow`).
4. Repeat until zero findings.

## Checklist

- [ ] **Correctness** — every clause of the task issue (#N) is traceable to
      committed, checked Coq. No `Admitted`/`Admit`/`Abort`.
- [ ] **Statements** — theorem/definition statements are as general as the task
      requires and no weaker than needed; no accidentally-overstrong hypotheses.
- [ ] **Proofs** — proofs are complete and not weakened; no goal discharged by
      `admit`/`exact I` on a wrong term.
- [ ] **Docs** — coqdoc comments updated per the `documentation` skill; each
      public item states its contract.
- [ ] **Duplication** — no copy-pasted or near-identical lemmas/encodings (see
      `reusing`).
- [ ] **Layering** — dependency direction in `docs/design.md` respected
      (`INet` never depends on `Arch`; `Basics` depends on neither).
- [ ] **Style** — `code-style` conventions clean; naming consistent with the
      codebase.
- [ ] **Dead code** — no unused imports, definitions, or commented-out proof
      blocks.
- [ ] **Scope** — changes touch only what the task requires; no unrelated edits.

Zero findings means all boxes pass. Do not merge with known findings.
