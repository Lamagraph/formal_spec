---
name: code-style
description: Use before committing to check Rocq conventions. There is no standard Rocq formatter; this skill defines the conventions the project enforces by review. Thin pointer to docs/developer.md for the build that must stay green.
---

# Code style

Coq has no canonical auto-formatter the way Python has `ruff`/`black`. Style is
enforced by **review** (see the `code-review` skill) against the conventions
below, plus the hard requirement that the build stays green (`dune build`,
per `docs/developer.md`).

## Conventions

- **Naming.** Names are the spec's vocabulary — the code *is* the
  specification, so a name must read as spec prose in the rendered (rocqdoc)
  output, not just be a short internal label.
  - Modules: `CamelCase`, one word per concept (`Net`, `Schedule`).
  - Definitions/records/theorems: `snake_case`, named for their contract
    (`rewrite_step`, `agent_is_well_formed`), not for the proof that produced
    them.
  - Hypotheses in proofs: short, meaningful (`Hstep`, `Hinj`); avoid `H`, `H0`.
- **One responsibility per module.** If a module mixes concerns (e.g. an
  encoding *and* its correctness), split it (see `add-theory`).
- **Layering.** Imports point downward only, per `docs/design.md`. A forward
  dependency is a review finding.
- **No `Admitted` / `Admit` / `Abort`** in committed code, ever.
- **Proofs.** Prefer readable, structured proofs. Factor repeated tactic
  sequences into named `Lemma`s or a small custom tactic rather than
  copy-pasting. Keep `Set`/`Unset` flags local to where they are needed.
- **Comments.** `{** ... *}` for rendered documentation; `(* ... *)` for private
  proof scratch. No commented-out dead code or abandoned proof attempts in
  committed files.
- **Imports.** `Require Import` only what the module uses; no unused imports.

## Pre-commit

Run `dune build` (and the `rocqchk` re-check for the commit gate, per
`git-workflow`). The build must be green. There is no separate lint/format
command to run.
