---
name: add-theory
description: Use when adding a new .v module (theory) to the specification. Covers where the file goes, the dune wiring, module conventions, layering, and the mirroring test/doc requirements.
---

# Add a theory

A "theory" is a new `.v` module in the specification. This is the core domain
operation of the project (the analogue of adding a graph or grammar in a data
project).

## Where it goes

Place the file under `src/` according to the target layout in
`docs/design.md`:

- `src/Basics.v` — only for genuinely shared, dependency-free material.
- `src/INet/` — the abstract interaction-net model.
- `src/Arch/` — the concrete co-processor architecture.
- `src/Correctness.v` — the equivalence layer.

If the right home is unclear, or the layout needs a new subdirectory, that is a
design decision: record it in `docs/design.md` (see the `documentation` skill)
before creating the file.

## Wiring

dune discovers `.v` files automatically — there is no manifest to update.

1. Create the `.v` file under `src/` (or a sub-theory directory).
2. If it is in a **new subdirectory**, add a `dune` file there with a
   `rocq.theory` stanza: `name` is the qualified module prefix (e.g.
   `LamaGraph.INet` for `src/INet/`), and the `theories` field lists the
   theories this one depends on (e.g. `(theories LamaGraph.INet)` in
   `src/Arch/dune`).
3. `dune build` must succeed.

## Module conventions

Each new module must:

1. Open with a `{** ... *}` header comment stating the module's **single
   responsibility** and its place in the `docs/design.md` layout.
2. `Require Import` only what it uses, and only from **lower** layers (respect
   the dependency direction — `INet` never depends on `Arch`, `Basics` depends
   on neither).
3. Give public definitions/lemmas names that express their **contract**, not
   the local proof that motivated them — they are the module's API and will be
   reused.
4. Carry a rocqdoc comment on every public item stating its invariant/contract
   (see the `documentation` skill).
5. Have a mirroring test where it adds value: a QuickChick property for a
   definition, or an extraction test (see the `build` skill and
   `docs/developer.md`).

## Reuse first

Before writing the module, run the `reusing` skill's checklist. If a close
match exists in a lower layer, generalize and reuse it rather than
re-encoding. Record what is reused in the subtask's **Code** section of
`tasks/detailed_plan.md`.

## Verify

`dune build` (build), then the `rocqchk` re-check, then `dune build @doc`
(rocqdoc) — see the `build` and `build-docs` skills. All three must be clean.
