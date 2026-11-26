---
name: release
description: Use when cutting a version of the specification — finalizing the changelog, merging dev to main, and tagging. Covers the procedure and recovery.
---

# Release

Cut a version of the specification. Unlike a published package, this project has
no artifact registry to publish to: a release is a **tagged, merged state of
`main`** plus a changelog entry. The model lives in the "Contribution
guidelines" section of `docs/developer.md`; this skill is the procedure.

## Procedure

1. Ensure `dev` is green: the quality gate (see `quality-gates`) passes and all
   open `task` issues that should be in this release are merged to `dev`.
2. Finalize the changelog: promote the `[Unreleased]` section of
   `CHANGELOG.md` to `## [X.Y.Z] - <today>`, listing the merged tasks (by issue
   number) and any notable design decisions.
3. Commit the changelog on `dev` (`chore: release X.Y.Z`).
4. Merge `dev` into `main` via a pull request (`main` is protected; do not
   squash). The user reviews and merges the PR manually; proceed only after they
   confirm the merge.
5. Tag the merged commit and push the tag:

   ```bash
   git fetch origin
   git tag -a vX.Y.Z -m "Release vX.Y.Z" origin/main
   git push origin vX.Y.Z
   ```

6. Verify: the tag points at the merged commit, and the GitHub Release (created
   from the tag) carries the `[X.Y.Z]` changelog section.

## Versioning

- **Patch** (`0.0.z`) — proof refactors, doc fixes, no change to stated
  theorems.
- **Minor** (`0.y.0`) — new theorems/definitions added; existing statements
  unchanged.
- **Major** (`x.0.0`) — a stated theorem or core encoding changes in a
  backward-incompatible way.

## Recovery

Use the `gh` CLI (installed and authenticated on this machine; if a new machine
is not, run `gh auth login` first).

### Tag pushed but the release is wrong

Nothing downstream depends on the tag except the GitHub Release, so it can be
replaced:

```bash
git push origin :refs/tags/vX.Y.Z   # delete the tag
```

Fix the failure, merge the fix to `main` (PR + user merge), then re-tag the new
`origin/main` and push again.

## Notes

- Releasing is the deliberate exception to the "no push" convention (it merges
  to `main` and pushes a tag).
- If a GitHub remote is not yet configured, steps 4–6 are deferred until one is;
  the local tag and changelog commit still stand.
