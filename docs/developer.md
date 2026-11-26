# Developer Guide

The single source of truth for **how to build, verify, and document** this
project. Skills under `.opencode/skills/` are thin pointers to this page and to
the CI workflow — they do not restate the commands here.

## Prerequisites

- **Coq 8.20.1** (managed by opam). The project pins this version; CI installs
  the same.
- `coq_makefile`, `coqdoc`, `coqchk`, `coqtop` — all ship with the `coq`
  opam package.
- Optional: `coq-quickchick` (property-based testing) — `opam install
  coq-quickchick`. Not required for the core build.

There is no virtualenv-style isolation: the opam `default` switch is the
environment. If a tool is missing, `opam install` it rather than working
around it (see the "Tools, not instructions" principle in `AGENTS.md`).

## Build

```sh
make            # compile every .v in CoqProject (byte-code .vo)
```

`make` is the primary gate: a module that compiles under `coqc` has all of its
definitions and proofs checked. **A proof that compiles is the unit of
verification in this project** — there is no separate "test run" for a theorem.

Regenerate the Makefile after editing `CoqProject` (e.g. after adding a theory):

```sh
coq_makefile -f CoqProject -o Makefile
```

## Verify (independent re-check)

```sh
make validate   # runs coqchk over the compiled .vo files
```

`coqchk` re-verifies the compiled kernel objects independently of the original
`coqc` run. It is the stronger, slower check and is part of the quality gate.

## Documentation (coqdoc)

```sh
make html       # coqdoc -> html/  (LamaGraph.<Module>.html, index.html, toc.html)
make all.pdf    # coqdoc -> all.pdf
```

coqdoc renders the `{** ... *}` comments in the `.v` sources. Comments are the
documentation: write them in the source, not in a separate file. `html/` is
git-ignored build output.

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

`QuickCheck` runs as part of the build (it is a tactic invoked at compile time),
so a failing property fails `make`. See the `build` skill.

## Extraction (OCaml)

To extract executable OCaml from definitions and test it against reference
behavior:

```coq
Require Import ExtrOcamlBasic.
Extract Inductive bool.
Extract Inlined Constant Nat.add => "+".
Extract "lamagraph.ml" MyModule.
```

`make` then emits `lamagraph.ml` alongside the sources; compile and run it with
OCaml. Extraction tests live under `tests/`. See the `build` skill.

## Clean

```sh
make clean      # remove .vo/.vos/.glob/.aux and other build artifacts
make cleanall   # also remove extracted files and docs
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
issue it fully resolves (`Fixes #N` for defects, `Closes #N` otherwise). A task
that only partially addresses a linked issue uses a bare `#N` reference (no
keyword).

## CI as source of truth

`.github/workflows/ci.yml` is the source of truth for what the quality gate
runs in CI (build + coqchk + coqdoc). If a command here and the workflow
disagree, the workflow wins for CI behavior; keep them in sync. See the
`quality-gates` skill for the gate's semantics (PASS / BLOCKED).
