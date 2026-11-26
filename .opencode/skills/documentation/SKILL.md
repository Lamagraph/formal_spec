---
name: documentation
description: Use when determining which docs to update for a source change. Maps source changes to required documentation actions and defines documentation completeness verification. The single source of truth for doc conventions in this project.
---

# Documentation

Documentation in this project is **rocqdoc comments in the `.v` sources** plus
the prose pages under `docs/`. rocqdoc renders the `{** ... *}` comments; there
is no separate API-reference tree to keep in sync. This skill is the single
source of truth for what docs to update when source changes.

## Mapping: source change -> doc action

| Source change | Required doc action |
|---|---|
| New public definition/record/theorem | Write a rocqdoc comment block above it: what it is, its invariant/contract, and a short example |
| Changed public definition/theorem | Update its rocqdoc comment (statement, invariants, example) |
| New module | Add a module-header comment block stating the module's single responsibility, its place in the `docs/design.md` layout, and its architecture-related design decisions (see the `add-theory` skill) |
| Removed/renamed API | Update every rocqdoc comment and `docs/` page that references it |
| New architecture-related design decision | Document it in the `.v` file where it is realized (module header / above the relevant definition); do not duplicate it in `docs/design.md` |
| New non-architecture (build/process) design decision | Record it in `docs/design.md` under "Standing design decisions" |
| Architecture change | Update the target layout in `docs/design.md` and the affected `.v` module headers |

## Comment conventions

The rendered (rocqdoc) form of the code *is* the specification's
documentation — there is no separate spec document. Comments must therefore
be descriptive enough that a reader grasps the *what* and *why* of each
public item from the rendered output alone (self-contained, human-readable).

- Use `{** ... *}` blocks (rendered by rocqdoc) for documentation; use `(* ... *)`
  for private proof scratch that should not be rendered.
- State the **invariant or contract**, not just the type. A reader should
  understand *why* the definition is shaped that way.
- Keep examples small and self-contained.
- Cross-references: refer to modules by their qualified name (e.g.
  `LamaGraph.INet.Net`); rocqdoc does not resolve `[@ ...]` links the way Sphinx
  does, so keep references textual and unambiguous.

## Completeness verification

A documentation update is complete when:

- [ ] At least one rocqdoc comment (or `docs/` page) was created or updated for
      the change.
- [ ] Every new public definition/theorem has a comment stating its contract.
- [ ] Any new architecture-related decision is documented in the `.v` file
      where it is realized; any new non-architecture (build/process) decision
      is recorded in `docs/design.md`.
- [ ] `dune build @doc` succeeds (rocqdoc renders without error).

To build and check the docs, see the `build-docs` skill.
