---
name: subtask-loop
description: Use when executing an atomic subtask from the detailed plan: implement -> prove/test -> document -> pre-commit checks -> quality checks -> commit -> mark done. Covers the full execution cycle, proof-quality checks, commit rules, blocked work protocol, and completion tracking.
---

# Subtask Execution Loop

Each atomic subtask from `tasks/detailed_plan.md` is executed as a
self-contained cycle.

## Cycle Steps

Execute these steps in order. **Do not skip steps. Do not proceed past a step
until it is verified complete.**

### Documentation-Only Subtasks

When a subtask modifies only `.md` files (no `.v` files), the cycle is adapted:

| Step | Action |
|------|--------|
| 1. Implement | Write documentation |
| 2. Prove / Test | **Skip** — no code to check |
| 3. Update Docs | The implementation IS the documentation; verify links are updated |
| 4. Pre-Commit Check | **Skip** — no source files to check |
| 5. Quality Checks | **Skip** — no code to check |
| 6. Commit | **Follow exactly** — one commit per subtask, single SN identifier |
| 7. Mark Done | **Follow exactly** |

The absence of code changes **never** justifies batching multiple subtasks into
a single commit.

### 1. Implement

Write the Coq specified in the subtask's **Code** section (definitions,
records, theorems, tactics).

### 2. Prove / Test

Complete the proofs and add the QuickChick / extraction tests specified in the
subtask's **Tests** section. **The gate for this step is `dune build`
succeeding** —
every proof in the touched modules checks, and any `QuickCheck` runs pass. See
the `build` skill. No `Admitted`, `Admit`, or `Abort` may remain.

### 3. Update Documentation

**Load the `documentation` skill before updating any docs.** Update all
task-related coqdoc comments per that skill.

**Hard gate — this step is not complete until:**

- [ ] At least one coqdoc comment was created or updated for this subtask
- [ ] Documentation completeness is verified per the `documentation` skill's
      procedure

### 4. Pre-Commit Check

Run the Coq conventions check per the `code-style` skill. Do not commit until
it passes.

### 5. Quality Checks

- **Duplication check**: scan for accidental duplication (the same lemma or
  encoding under different names, copy-pasted proof blocks). Consolidate if
  found.
- **Generality check**: verify new code reuses existing abstractions and is
  polymorphic where the task requires, instead of a bespoke re-implementation.
- **Equivalence check**: if the subtask is a variant of an existing encoding or
  algorithm, ensure an equivalence lemma exists relating it to the reference.
- **Layering check**: verify the dependency direction in `docs/design.md` is
  respected — `INet` does not depend on `Arch`, `Basics` depends on neither.

### 6. Commit

**Load the `git-workflow` skill before committing.** The commit message format
lives in the "Contribution guidelines" section of `docs/developer.md`; the
operational procedure (validation, merge) lives in the skill.

### 7. Mark Completed

Mark the subtask as completed in `tasks/detailed_plan.md` (`[done]` suffix +
commit hash on the subtask heading), then mirror the file onto the plan comment
of the task issue:

```bash
python3 scripts/sync_plan_comment.py <N>
```

The local file is the single source of truth; the comment is a pure mirror.

If at any point in steps 1–7 you hit an unresolvable problem that prevents 100%
completion, **STOP the cycle immediately** and follow the Blocked Work Protocol
below. Do NOT attempt to "complete" the subtask with `Admitted` goals, reverted
work, or known limitations. Do NOT proceed to the next subtask.

## Subtask Outcome

A subtask has exactly two valid outcomes:

- **Resolved**: implemented, proved, docs updated, committed. Record the commit
  hash in `tasks/detailed_plan.md`.
- **Blocked**: a proof-theoretic or design problem prevents 100% completion. Do
  NOT commit partial work. Do NOT proceed to the next subtask. Follow the
  Blocked Work Protocol.

There is no third state. "Left an `Admitted` as a known limitation" is not a
valid outcome — it means the subtask is blocked. Report it.

Never silently skip a subtask. If a subtask was attempted, reverted, and its
planned changes were not committed, the subtask is incomplete. Do not mark it
done. Do not proceed. Report it as blocked.

## Per-Subtask Execution Tracking

For each subtask, use the todo tool to track cycle steps as separate items.
**No subtask may be committed with any step still `pending`.**

Example for subtask S1:

```
- "S1: Implement" -> in_progress -> completed
- "S1: Prove / Test (dune build green)" -> in_progress -> completed
- "S1: Update documentation" -> in_progress -> completed
- "S1: Pre-Commit Check (code-style)" -> in_progress -> completed
- "S1: Quality checks" -> in_progress -> completed
- "S1: Commit" -> in_progress -> completed
```

## Multi-Subtask Discipline

When a task has multiple subtasks (S1, S2, S3, ...), execute them **strictly
sequentially**:

1. Complete all cycle steps for S1 (Implement → Prove/Test → Docs → Pre-Commit
   Check → Quality → Commit → Mark Done).
2. Only after S1 is committed, start S2.
3. Never mark multiple subtasks `completed` in the todo tool before committing
   each individually.

## Blocked Work Protocol

If you encounter a proof-theoretic problem that you cannot resolve to 100%
correctness, **STOP**. Do not commit. Do not merge. Do not weaken a statement
or `Admit` a goal to make the build green. Instead:

1. Stay on the feature branch.
2. Report the problem concretely to the user:
   - Which goal is stuck and why (the exact `Goal` state).
   - What proof-theoretic gap exists (e.g., "inversion on `rule` is not
     injective for the parallel case").
   - What you've tried and what remains unresolved.
3. Ask the user for guidance: additional subtasks, a different encoding,
   descoping, or splitting the task.
4. **Transfer user guidance to the task** per the `user-guidance-transfer`
   skill — post it verbatim as a comment on the task issue.
5. Append a `## Design Notes` section to `tasks/detailed_plan.md`. See the
   `planning` skill for the full template. Minimum required content:

   - **Correct Design**: the encoding/design as confirmed by the user —
     invariants, representations. Quote the user's design guidance verbatim
     where available.
   - **Blocked Subtasks**: which subtasks are blocked and why.
   - **Root Causes**: why each goal is stuck, with the concrete `Goal` state.
   - **Approaches Tried**: what was attempted and why it didn't fully work.
   - **Remaining Work**: concrete, actionable items — not vague goals.
   - **Admitted Goals**: list any `Admitted` goals and the reason.

   Commit this summary so the plan serves as a persistent design record for
   future task refinement.
6. Post the block report (the `## Design Notes` content) as a comment on the
   task issue, so the block is visible in the task record.

## Task Completion Verification

This section is the **single source of truth** for what "done" means. Before a
task is considered done — its last subtask's commit carries `Closes #<N>` (the
task's own issue) and is merged to `dev` — verify:

- [ ] Every clause in the task description is traceable to implemented and
      committed Coq.
- [ ] No subtask was reverted without resolution.
- [ ] No requirement was silently skipped or deferred.
- [ ] `dune build` succeeds with **zero** `Admitted`/`Admit`/`Abort` anywhere.
- [ ] All quality gates pass (see the `quality-gates` skill).
- [ ] The plan comment on the task issue is in sync with
      `tasks/detailed_plan.md` (pure mirror — `python3
      scripts/sync_plan_comment.py <N> --check` must exit 0).
- [ ] If any of the above fails, the task is NOT done — it is blocked. Follow
      the Blocked Work Protocol. Do NOT close it with known unresolved
      limitations.

Partial completion is not completion. "All proofs go through for the parts I
did" does not mean the task is done if other parts were reverted or `Admitted`.

## Marking Complete

A task is complete when its last subtask's commit carries `Closes #<N>` (the
task's own issue number) as a standalone line; GitHub closes the issue when the
release containing the task lands on `main`. Never edit the issue body — it is
user-authored and immutable.

Complete means COMPLETE: every requirement met, every proof checked, every edge
case handled. Never close a task with known failures or unresolved limitations.
