---
name: planning
description: Use when planning tasks: creating global plans across multiple tasks, decomposing a task into atomic subtasks, or authoring new task descriptions. Covers multi-task planning, detailed plan format, atomic subtask requirements, and task authoring guidelines.
---

# Planning

## Multi-task Planning

When the user asks to work on a **set of tasks** (several task IDs), do NOT jump
directly into implementation. First create a high-level global plan in
`tasks/global_plan.md`.

The global plan must:

- List all tasks to be done with their IDs and brief descriptions.
- Identify dependencies between tasks (which must be done before which).
- Identify potential conflicts or overlapping changes (e.g., two tasks
  modifying the same `.v` module).
- Identify shared infrastructure (definitions, notations, helper lemmas) that
  multiple tasks need. Create shared modules to avoid duplication across tasks.
- Identify existing reusable abstractions (definitions, lemmas, tactics) that
  new tasks should use rather than reinvent.
- **Reuse analysis**: load the `reusing` skill and run the reuse checklist
  against existing code and documentation before creating new material.
- Align tasks with the target module layout in `docs/design.md`.
- Propose an execution order that minimizes rework and avoids conflicts.

After the global plan is created, proceed with the normal working loop: one
task at a time, feature branch per task, detailed plan in
`tasks/detailed_plan.md` for each.

## Detailed Plan (Atomic Subtasks)

`tasks/detailed_plan.md` MUST decompose the task into atomic subtasks. Each
subtask:

- Is small enough to complete in a single focused work session (typically
  30–90 minutes).
- Produces a **compilable increment** — after it, `dune build` succeeds and no
  partial/`Admitted`/`Abort`ed proof is left uncommitted.
- Has a unique identifier (e.g., "S1", "S2") used in commit messages and plan
  tracking.
- Has a **self-contained spec**: a fresh agent holding only the detailed plan
  and prior subtask reports must be able to execute it — no unstated
  assumptions from the planning session (subtasks are executed by fresh
  subagents; see the `subtask-loop` skill).

If a task is ambiguous or underspecified **during planning** (conflicting
requirements, unclear scope, missing constraints), do not guess. Ask the user
for clarification, then transfer the guidance to the task per the
`user-guidance-transfer` skill before proceeding with decomposition.

Before writing the detailed plan, load the `reusing` skill and run the reuse
checklist: search existing documentation and code for definitions, lemmas, and
doc sections that can be reused or generalized. Record what is reused in each
subtask's **Code** section.

### Subtask Format

Each subtask in `tasks/detailed_plan.md` MUST include these four sections. **A
subtask with missing Code, Tests, or Docs sections is incomplete and must not
be executed.**

```
### SN: <title>

**Code:** <.v files to create or modify, definitions/theorems to add>
**Tests:** <proofs to complete, QuickChick properties, or extraction tests to
           add; "none — pure refactoring" if not applicable>
**Docs:** <rocqdoc comments to write/update. Use the `documentation` skill to
         determine which docs are affected.>

**Spec:**
- <detailed implementation specification>
```

Example:

```
### S1: Define the agent signature and a binary agent

**Code:** New file `src/INet/Agent.v` with `Definition agent_sig` and
          `Record BinaryAgent`
**Tests:** Proof that a sample binary agent satisfies `agent_sig`; QuickChick
          property on the arity invariant
**Docs:** rocqdoc comment block on `BinaryAgent` stating the invariant and an
          example

**Spec:**
- An agent is a pair (arity, rule); a binary agent has arity (2, 1) ...
```

### Documentation Mapping

For the mapping of source changes to required doc actions, load the
`documentation` skill — it is the single source of truth. Use it when writing
the **Docs** section of each subtask.

### Granularity

If a subtask cannot be committed as a self-contained, compilable increment, it
is too large — split it further. The commit message format lives in the
"Contribution guidelines" section of `docs/developer.md`; the operational
commit procedure lives in the `git-workflow` skill.

### Bounded uncommitted work

Uncommitted work on a feature branch must never exceed one atomic subtask. If a
session is interrupted, the loss is bounded to that single subtask.

## Post-Implementation Design Notes

When a task hits a proof-theoretic or modeling limitation — partially
completed, with `Admitted` goals or remaining work — append a `## Design Notes`
section to `tasks/detailed_plan.md`. This serves as persistent design knowledge
for future task refinement. The section must be structured as follows:

```
## Design Notes (discovered during implementation)

### <Topic Title>

Design rationale, encodings, invariants — as confirmed by the user.

### <Failure Topic Title>

- Root causes with concrete examples (e.g., "the inversion lemma fails for the
  rule R because the premise is not injective on ...")
- What was attempted and why it didn't fully work
- Remaining work: concrete, actionable items
- Admitted goals: list them and the reason
```

Requirements:

- Every proof-theoretic limitation MUST be traceable to a concrete goal, a
  concrete lemma/definition, and a concrete proof attempt.
- Never write vague descriptions like "some goals are stuck" — specify which
  goal, which hypothesis is missing, and which tactic sequence was tried.
- Remaining work items must be actionable (e.g., "add an injectivity lemma for
  `rule` and retry the inversion") — not vague goals.
- If the user provided design guidance (e.g., an encoding choice, an invariant),
  record it verbatim in the `### <Topic>` section as the authoritative
  reference.

## Task Authoring Guidelines

When creating a new task issue (`gh issue create`, label `task`), follow these
rules (they apply to the issue body):

- **Specify the statement upfront.** If the task introduces a definition or
  theorem, include the exact Rocq signature (types, parameters) in the task
  description.
- **Keep tasks single-responsibility.** A task should do one thing. If it
  requires more than 5 sub-items or spans multiple unrelated concerns, split it
  into multiple tasks.
- **Specify equivalence requirements.** For any new encoding or algorithm
  variant, explicitly state "must be equivalent to X" so the equivalence lemma
  is built from the start.
- **Specify generality.** If a definition must be polymorphic (over agent
  arities, over the memory model, etc.), state it explicitly.
- **Specify reuse expectations.** If the task builds on existing infrastructure
  (e.g., "reuse the notations from `LamaGraph.Basics`"), name the dependencies.
  This prevents reinvention.

## Task Completeness Verification

See the `subtask-loop` skill — it is the single source of truth for verifying
task completion before a task is considered done.
