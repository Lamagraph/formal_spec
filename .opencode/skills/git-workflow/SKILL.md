---
name: git-workflow
description: Use when doing git operations: committing, merging, rebasing. Covers the operational procedure (commit validation, merge to dev, pre-merge checks); the branching/commit model lives in docs/developer.md.
---

# Git Workflow

The model (branching scheme, commit message format, merge strategy, quality
gate) is documented in the "Contribution guidelines" section of
`docs/developer.md` (single source of truth). This skill keeps only the
operational procedure.

## Commits

**Pre-commit validation**: before running `git commit`, verify the prepared
message follows the format from the docs — Conventional Commits with exactly
one subtask identifier (`feat(<task>-S<n>): ...`; ranges, lists, or commas are
forbidden). If the message mentions multiple subtask identifiers, STOP — split
the changes into individual commits. One commit per completed atomic subtask.

**Issue-closing validation**: every completed task carries the closing keyword
for its own issue (`Closes #<task>`) plus one per linked issue it fully resolves
(`Fixes #N` for defects, `Closes #N` otherwise) — all as standalone lines in
exactly one commit: the last subtask's commit. Verify on the feature branch:

```bash
git log dev..HEAD --format=%B | grep -cE '^(Fixes|Closes) #[0-9]+$'
```

must print `0` before the last subtask's commit and, afterwards, exactly one
line per fully resolved issue including the task's own (no more). A task that
only partially addresses a linked issue uses a bare `#N` reference (no
keyword). The model and closing timing live in the "Contribution guidelines"
section of `docs/developer.md`.

### Pre-commit checklist

1. Run the commit gate: `code-style` conventions, `dune build` (build), and
   the `rocqchk` re-check.

### Commit scope

- Each commit is a self-contained, compilable increment (`dune build`
  succeeds).
- Commit messages must be detailed enough to understand why changes were
  required.

## Merging to dev

### Pre-merge checks

Run the quality gate (see the `quality-gates` skill). All checks MUST pass
before merging. **This is absolute — no exceptions, no self-assessment.**

### Merge strategy

Rebase the feature branch onto `dev`, then fast-forward `dev` to it. The
individual subtask commits are preserved and the history of `dev` stays linear.
Never squash: squashing destroys the per-subtask commit structure that the
commit message format is built around (each commit already carries its own
detailed message, so no combined merge message is needed).

```bash
git checkout dev
# only if dev has new commits since the branch was created:
git checkout feature/<task>-<desc> && git rebase dev && git checkout dev
git merge --ff-only feature/<task>-<desc>
git branch -d feature/<task>-<desc>
```

If `dev` has not moved, skip the rebase — the fast-forward alone is enough.
Delete the merged feature branch (safe delete only).

## Rules

- No emergency fixes.
- All work is local; `push` only happens at release (see the `release` skill).
