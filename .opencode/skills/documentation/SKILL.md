---
name: documentation
description: Use when determining which docs to update for a source change. Maps source changes to required documentation actions and defines documentation completeness verification. The single source of truth for doc conventions in this project.
---

# Documentation

Documentation in this project is **coqdoc comments in the `.v` sources** plus
the prose pages under `docs/`. coqdoc renders the `{** ... *}` comments; there
is no separate API-reference tree to keep in sync. This skill is the single
source of truth for what docs to update when source changes.

## Mapping: source change -> doc action

| Source change | Required doc action |
|---|---|
| New public definition/record/theorem | Write a coqdoc comment block above it: what it is, its invariant/contract, and a short example |
| Changed public definition/theorem | Update its coqdoc comment (statement, invariants, example) |
| New module | Add a module-header comment block stating the module's single responsibility and its place in the `docs/design.md` layout |
| Removed/renamed API | Update every coqdoc comment and `docs/` page that references it |
| New standing design decision | Record it in `docs/design.md` under "Standing design decisions" |
| Architecture change | Update the target layout in `docs/design.md` |

## Comment conventions

- Use `{** ... *}` blocks (rendered by coqdoc) for documentation; use `(* ... *)`
  for private proof scratch that should not be rendered.
- State the **invariant or contract**, not just the type. A reader should
  understand *why* the definition is shaped that way.
- Keep examples small and self-contained.
- Cross-references: refer to modules by their qualified name (e.g.
  `LamaGraph.INet.Net`); coqdoc does not resolve `[@ ...]` links the way Sphinx
  does, so keep references textual and unambiguous.

## Completeness verification

A documentation update is complete when:

- [ ] At least one coqdoc comment (or `docs/` page) was created or updated for
      the change.
- [ ] Every new public definition/theorem has a comment stating its contract.
- [ ] Any new standing decision is recorded in `docs/design.md`.
- [ ] `make html` succeeds (coqdoc renders without error).

To build and check the docs, see the `build-docs` skill.
