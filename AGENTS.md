# AGENTS.md

LamaGraph **formal_spec** is a Rocq development (Rocq 9.3, dune build, MIT)
giving a formal specification of an **interaction-nets-based co-processor
(accelerator) architecture**: the abstract interaction-net model, the concrete
architecture, and the equivalence between them.

This file is an **entrypoint / TOC only** — details live in the skills linked
below and in `docs/`.

## Start here

At the start of every session, load the `workflow-management` skill
(`.opencode/skills/workflow-management/SKILL.md`) first, before doing anything
else. It drives the loop: plan → feature branch → subtasks → review → quality
gate → merge, and points to the other workflow skills below.

## Main Principles

* **Documentation is about "What" and "Why". Skills are about "How".**
* This file is a short entry point for a fast, cold, error-free start.
* **Only one source of truth. No duplicates.** Each thing — in code, issues,
  PR descriptions, and docs — is described exactly once. Use generalization,
  cross-references, and links to avoid duplication. Find what you can to reuse
  before creating something new.
* **Source-of-truth hierarchy: code (`.v`), scripts, CI configs > docs.** If a
  fact can be extracted from the sources, scripts, or CI configs, it is not
  duplicated in docs. Docs hold only what cannot be unambiguously reconstructed
  from code: design decisions, non-trivial constraints. Skills stay thin
  pointers to docs, code, or CI — they never re-describe them.
* **A proof that compiles is the unit of verification.** A module that checks
  under `rocq` has all its definitions and proofs verified. There is no
  separate "test run" for a theorem. QuickChick and extraction tests apply to
  *definitions* where empirical checking adds value.
* **Tools, not instructions.** If an existing tool does the job, run the tool.
  No long manual procedures for regular tasks. If a regular task has no tool,
  the tool must be installed and configured appropriately.
* **Always learn, never forget** — encode patterns before the session ends.
* **Issues, pull requests, and their comments are a knowledge base.** Log
  task-related findings in the descriptions or comments of the respective
  issues/PRs. When facing a problem, first check whether a similar problem was
  already solved or described.

## Module layout

The target layout and the standing design decisions live in
[`docs/design.md`](docs/design.md) — the single source of truth for the
architecture. In short: `src/Basics.v` (leaf) → `src/INet/` (abstract model) →
`src/Arch/` (concrete co-processor) → `src/Correctness.v` (the equivalence).
Dependency direction is acyclic and points downward; `INet` never depends on
`Arch`.

## Skills

### Domain

| Skill | When to use |
|---|---|
| `.opencode/skills/build` | Building the project (compile + check) and running QuickChick / extraction tests |
| `.opencode/skills/add-theory` | Adding a new `.v` module to the specification |
| `.opencode/skills/build-docs` | Rendering the rocqdoc documentation |
| `.opencode/skills/code-style` | Rocq conventions before commit |

### Workflow / process

| Skill | When to use |
|---|---|
| `.opencode/skills/workflow-management` | Driving the overall task loop |
| `.opencode/skills/planning` | Global plans, atomic subtasks, task authoring |
| `.opencode/skills/subtask-loop` | Executing one atomic subtask |
| `.opencode/skills/git-workflow` | Branching, commits, merging |
| `.opencode/skills/reusing` | Finding existing code/docs to reuse, not duplicate |
| `.opencode/skills/user-guidance-transfer` | Recording user guidance verbatim |
| `.opencode/skills/documentation` | Mapping source changes to doc updates |
| `.opencode/skills/quality-gates` | The pre-merge gate that must pass |
| `.opencode/skills/code-review` | Whole-repo review before merge |
| `.opencode/skills/release` | Cutting a version of the specification |

Contribution templates (tasks, bugs, features) live under `.github/` and are
the source of truth for the required fields.
