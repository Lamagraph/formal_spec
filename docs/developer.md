# Developer Guide

The single source of truth for **how to build, verify, and document** this
project. Skills under `.opencode/skills/` are thin pointers to this page and to
the CI workflow — they do not restate the commands here.

## Prerequisites

- **Rocq 9.3** (managed by opam, package `rocq-prover`). The project pins this
  version; CI uses the same (prebuilt image). Note: the Coq project was
  renamed to Rocq — on opam `coq` is now a compatibility metapackage over
  `rocq-core`/`rocq-stdlib`, and in sources `From Coq` is deprecated in favor
  of `From Stdlib` (since Rocq 9.0).
- **dune ≥ 3.24** — the build tool. The Rocq build language
  (`(using rocq …)` in `dune-project`) requires it; dune 3.24+ removed the
  old Coq build language.
- `rocqchk` (independent checker) — ships with the Rocq packages.
- `odoc` — required by the `@doc` gate (documents any OCaml, e.g. extracted
  test code).
- Optional: `coq-quickchick` (property-based testing) — `opam install
  coq-quickchick`. Not required for the core build.

There is no virtualenv-style isolation: the opam `default` switch is the
environment. If a tool is missing, `opam install` it rather than working
around it (see the "Tools, not instructions" principle in `AGENTS.md`).

## Build

```sh
dune build        # compile every .v (byte-code .vo), in dependency order
```

`dune build` is the primary gate: a module that compiles under `rocq` has all
of its definitions and proofs checked. **A proof that compiles is the unit of
verification in this project** — there is no separate "test run" for a
theorem.

dune discovers `.v` files automatically from the `rocq.theory` stanzas (see
`src/dune`); there is no manifest to update when adding a module.

## Verify (independent re-check)

```sh
MODS=$(cd _build/default/src && find . -name '*.vo' | sed 's|^\./||; s|\.vo$||; s|/|.|g' | sed 's|^|LamaGraph.|' | tr '\n' ' ')
rocqchk -R _build/default/src LamaGraph $MODS
```

`rocqchk` re-verifies the compiled kernel objects independently of the
original `rocq` run. It is the stronger, slower check and is part of the
quality gate. The module list is derived from the build tree, so new modules
are covered automatically.

## Documentation (rocqdoc)

```sh
dune build @doc           # rocqdoc HTML (+ odoc) for every theory
dune build @rocqproject   # regenerate _RocqProject (IDE support)
```

rocqdoc renders the `{** ... *}` comments in the `.v` sources. Comments are
the documentation: write them in the source, not in a separate file. The HTML
lands in `_build/` (git-ignored build output).

## Documentation website

The documentation site is at
<https://lamagraph.github.io/formal_spec/>. It serves the start page
(`site/index.html`, the only hand-written page) and the rocqdoc output
extracted from the `.v` sources (under `/doc/`).

`.github/workflows/deploy-docs.yml` is the source of truth for the deployment
setup; this section covers the decisions and day-to-day use.

- **Trigger:** push to `main` — the site reflects the *released* spec, so it
  updates at each release. `workflow_dispatch` allows manual runs, but only
  once the workflow is on the default branch (the dispatch API resolves
  workflows from `main` only).
- **Local preview:** `dune build @doc`, then open
  `_build/default/src/LamaGraph.html/index.html`. On the site, the start page
  sits at the root and the rocqdoc output under `/doc/`.

## Property-based testing (QuickChick)

For definitions (not theorems) where you want random counterexample hunting
before or alongside a proof, use QuickChick:

```sh
opam install coq-quickchick
```

Then in a `.v` file:

```coq
Require Import QuickChick.
Set QuickChick MaxRuns 1000.

Property my_prop (x y : nat) : ... .
Proof. ... Qed.

QuickCheck my_prop.
```

`QuickCheck` runs as part of the build (it is a tactic invoked at compile
time), so a failing property fails `dune build`. See the `build` skill.

## Extraction (OCaml)

To extract executable OCaml from definitions and test it against reference
behavior, add a `rocq.extraction` stanza next to the theory (see the dune
Rocq language documentation for its fields) and use `Extract` directives in
the source:

```coq
Require Import ExtrOcamlBasic.
Extract Inductive bool.
Extract Inlined Constant Nat.add => "+".
Extract "lamagraph.ml" MyModule.
```

`dune build` then emits the extracted OCaml in the build tree; compile and
run it with OCaml. Extraction tests live under `tests/`. See the `build`
skill.

## Clean

```sh
dune clean        # remove the _build/ tree (all build artifacts)
```

## Contribution guidelines

The branching model and commit format. The operational procedure (validation,
merge steps) lives in the `git-workflow` skill; this section is the single
source of truth for the *model*.

### Branching model

- `main` — the release branch. Protected. Only receives merges from `dev` via
  pull request.
- `dev` — the integration branch. Feature branches are created from `dev` and
  merged back into `dev`.
- `feature/<task-id>-<short-description>` — one per task. A task is done when
  its subtask commits are on `dev`.

### Commit message format

Conventional Commits, with **exactly one** subtask identifier in the scope:

```
<type>(<task-id>-S<n>): <imperative summary>

<detailed body: why the change was required>
```

- `<type>` ∈ `feat | fix | refactor | docs | test | chore`.
- `<task-id>` is the GitHub issue number; `S<n>` is the atomic subtask id from
  `tasks/detailed_plan.md`.
- One commit per completed atomic subtask. Ranges, lists, or multiple
  subtask ids in one commit are forbidden — split the changes.

### Issue-closing keywords

Every completed task carries `Closes #<task-id>` (its own issue) as a
standalone line in the **last subtask's commit**, plus one keyword per linked
issue it fully resolves (`Fixes #N` for defects, `Closes #N` otherwise). A
task that only partially addresses a linked issue uses a bare `#N` reference
(no keyword).

### Dependabot

`.github/dependabot.yml` is the source of truth for the exact settings; this
subsection covers only the conventions and the decisions behind them.

- **Scope:** GitHub Actions only.
- **Handling a Dependabot PR:** squash-merge to `dev` after CI is green —
  the workflow's `pull_request` trigger runs the full quality gate on every
  bot PR automatically. Skim the changelog on major bumps before merging.
  Bot PRs do not use the task/subtask commit model; the squash-merged
  commit message (the PR title) is the record.
- **Opam dependencies are manual on purpose.** Dependabot has no opam
  ecosystem. The prover version is pinned by the CI image tag
  (`rocq/rocq-prover:9.3`); the opam bounds are floors for fresh
  environments. Bump them deliberately, paired with the image-tag bump.
- **Activation:** Dependabot reads its config from the default branch
  (`main`), so the configuration takes effect at the next release.

## CI as source of truth

`.github/workflows/ci.yml` is the source of truth for what the quality gate
runs in CI (build + rocqchk + docs), executed inside the prebuilt
`rocq/rocq-prover:9.3` image via docker-coq-action. If a command here and the
workflow disagree, the workflow wins for CI behavior; keep them in sync. See
the `quality-gates` skill for the gate's semantics (PASS / BLOCKED).
