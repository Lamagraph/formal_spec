---
name: subtask-loop
description: Use when executing an atomic subtask from the detailed plan. Every subtask runs in a fresh subagent (sequential, depth 1): the parent composes a self-contained prompt with the accumulated context digest and verifies/ingests the child's structured report; the child runs implement -> prove/test -> document -> pre-commit checks -> quality checks -> commit -> mark done -> report. Covers the execution model, proof-quality checks, commit rules, blocked work protocol, and completion tracking.
---

# Subtask Execution Loop

Each atomic subtask from `tasks/detailed_plan.md` is executed as a
self-contained cycle — by a **fresh subagent**, not by the parent inline.

## Execution Model

Every subtask — including doc-only ones — is executed by a **fresh
subagent** spawned by the parent (main) agent.

Rules:

- **Sequential.** One subagent at a time. Start S(n+1) only after S(n)'s
  subagent has finished and its report has been verified. No concurrency.
- **Fresh.** Every subtask gets a new subagent. Never continue or reuse a
  previous child session.
- **Depth 1.** A subtask subagent must not spawn subagents of its own. No
  tree-like structure, no parallelism.
- **The parent is the sole interface to the user.** A subagent that needs a
  decision reports *Blocked* (see the Blocked Work Protocol); the parent
  relays the report to the user and feeds the resulting guidance into the
  next fresh subagent's prompt. Subagents never contact the user directly.

Not delegated: the code review and the quality gate are task-level steps the
parent performs after all subtasks (see the `code-review` and
`quality-gates` skills). The per-subtask gate remains `dune build` (child);
the full gate (rocqchk + `@doc`) remains task-level (parent).

### Parent duties (per subtask)

1. Take the next subtask from `tasks/detailed_plan.md`.
2. Compose a **self-contained prompt** containing:
   - the subtask's full spec (Code/Tests/Docs/Spec) from the plan;
   - task context: issue number, feature branch, commit convention
     (`<type>(<N>-S<n>)`, with `Closes #<N>` as a standalone line on the last
     subtask), plan file location;
   - the **accumulated context digest** — distilled from all prior subtask
     reports: artifact names/signatures, key invariants, proof techniques
     that worked, pitfalls/dead ends, module-map changes. The standard: the
     child must never need to re-investigate what a prior report already
     states;
   - the instruction to load this skill, follow the cycle, and end with the
     structured report.
3. Spawn the fresh subagent and wait for it to finish.
4. **Verify the report against reality**: the commit exists with the
   expected message, `dune build` is green, the plan is marked done, and the
   mirror is in sync (`python3 scripts/sync_plan_comment.py <N> --check`).
5. **Ingest the report**: append its "Context for subsequent subtasks" to
   the accumulated digest used in the next prompt.

### Child duties

Run the cycle below (steps 1–8) exactly, then end with the structured report
(step 8). The child's final message is the report — the parent receives it
when the child goes idle.

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
| 8. Report | **Follow exactly** |

The absence of code changes **never** justifies batching multiple subtasks into
a single commit.

### 1. Implement

Write the Rocq specified in the subtask's **Code** section (definitions,
records, theorems, tactics).

### 2. Prove / Test

Complete the proofs and add the QuickChick / extraction tests specified in the
subtask's **Tests** section. **The gate for this step is `dune build`
succeeding** —
every proof in the touched modules checks, and any `QuickCheck` runs pass. See
the `build` skill. No `Admitted`, `Admit`, or `Abort` may remain.

### 3. Update Documentation

**Load the `documentation` skill before updating any docs.** Update all
task-related rocqdoc comments per that skill.

**Hard gate — this step is not complete until:**

- [ ] At least one rocqdoc comment was created or updated for this subtask
- [ ] Documentation completeness is verified per the `documentation` skill's
      procedure

### 4. Pre-Commit Check

Run the Rocq conventions check per the `code-style` skill. Do not commit until
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

### 8. Report

End with a structured report as the final message:

```
## Subtask Report — S<n>

- **Status:** Resolved | Blocked
- **Commit:** <hash> (<subject line>)
- **Artifacts:** names + signatures of the definitions, records, and lemmas
  introduced or changed (the API surface for subsequent subtasks)
- **Context for subsequent subtasks:**
  - invariants / facts established
  - proof techniques that worked (tactic patterns, lemmas to reuse)
  - pitfalls / dead ends (what not to retry)
  - module/file map changes
- **Gate:** `dune build` status
```

For a **Blocked** subtask, replace Commit/Artifacts with the Blocked Work
Protocol details (stuck goal with exact `Goal` state, the proof-theoretic
gap, approaches tried).

The report is the anti-re-investigation channel: it must contain everything a
fresh subagent for the next subtask needs, so that no prior investigation is
repeated.

If at any point in steps 1–8 you hit an unresolvable problem that prevents 100%
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
- "S1: Report" -> in_progress -> completed
```

## Multi-Subtask Discipline

Subtasks are executed **strictly sequentially** per the Execution Model: one
fresh subagent per subtask, S(n+1) starting only after S(n)'s report has been
verified. Within a subtask:

1. Complete all cycle steps (Implement → Prove/Test → Docs → Pre-Commit Check
   → Quality → Commit → Mark Done → Report) before the subagent ends.
2. Never mark multiple subtasks `completed` in the todo tool before committing
   each individually.

## Blocked Work Protocol

If you encounter a proof-theoretic problem that you cannot resolve to 100%
correctness, **STOP**. Do not commit partial work. Do not merge. Do not weaken
a statement or `Admit` a goal to make the build green.

The subagent (child):

1. Stay on the feature branch.
2. Append a `## Design Notes` section to `tasks/detailed_plan.md`. See the
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
3. Post the block report (the `## Design Notes` content) as a comment on the
   task issue, so the block is visible in the task record.
4. End with the final report: **Status: Blocked**, the stuck goal with its
   exact `Goal` state, the proof-theoretic gap, and what was tried.

The parent:

5. Relays the report to the user and asks for guidance: additional subtasks,
   a different encoding, descoping, or splitting the task.
6. Transfers the user guidance to the task per the `user-guidance-transfer`
   skill — posted verbatim as a comment on the task issue.
7. Starts a **fresh** subagent whose prompt includes the guidance and the
   Design Notes.

## Task Completion Verification

This section is the **single source of truth** for what "done" means. Before a
task is considered done — its last subtask's commit carries `Closes #<N>` (the
task's own issue) and is merged to `dev` — verify:

- [ ] Every clause in the task description is traceable to implemented and
      committed Rocq.
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
