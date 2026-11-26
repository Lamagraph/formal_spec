# tasks/

Working plans. These are **ephemeral working documents**, not durable
documentation — durable design knowledge goes to `docs/design.md` (decisions)
or the task issue (findings).

Two files, at most one of each active at a time:

- **`global_plan.md`** — created when the user requests a *set* of tasks. Lists
  all tasks (by issue number), their dependencies, conflicts, shared
  infrastructure, and the proposed execution order. See the `planning` skill.
- **`detailed_plan.md`** — created per task, on its feature branch. Decomposes
  the single task into atomic subtasks (S1, S2, ...), each with **Code /
  Tests / Docs / Spec** sections. Mirrored as a comment on the task issue. See
  the `planning` and `subtask-loop` skills.

Neither file is committed to a long-lived branch as a record of *what was
decided* — that lives in `docs/design.md` and the issue. They are the scratch
pad for *how the current work is being executed*.
