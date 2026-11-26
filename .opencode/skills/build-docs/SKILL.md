---
name: build-docs
description: Use when rendering the coqdoc documentation. Thin pointer to the "Documentation (coqdoc)" section of docs/developer.md, which holds the exact commands; keeps the agent-specific notes.
---

# Build docs

The model (coqdoc renders `{** ... *}` comments from the `.v` sources) and where
the exact commands live are documented in the "Documentation (coqdoc)" section
of `docs/developer.md` — do not duplicate them here. Read that section before
running anything. This skill keeps only the agent-specific notes below.

## Notes

- **Comments are the docs.** There is no separate API-reference tree. If a
  public item is undocumented, fix the coqdoc comment in the source — do not
  write a parallel doc page.
- **`make html` is the check.** It must exit 0. A malformed `{** ... *}` block
  or an unbalanced comment fails the render.
- **`html/` is build output** and is git-ignored. Never commit it.
- **Fresh-state check.** coqdoc does not cache the way Sphinx does, but if the
  rendered output looks stale after renaming modules, run `make clean` and
  rebuild before trusting it.
- After adding or removing modules, confirm `toc.html` / `index.html` list them
  (they are generated from `CoqProject`).
