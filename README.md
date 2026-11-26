# LamaGraph — Formal Specification

A formal specification, developed in **Rocq** (the former Coq), of an
**interaction-nets-based co-processor (accelerator) architecture**.

The specification has two layers and the equivalence between them:

- **The interaction-net model** — the abstract computational semantics
  (agents, rules, nets, redexes, rewriting).
- **The architecture** — the concrete co-processor (memory, control, datapath,
  scheduling).

The central goal is to prove that executing the architecture realizes the
abstract interaction-net semantics.

## Layout

| Path | Purpose |
|---|---|
| `src/` | The Rocq theories (`.v` files). See `docs/design.md` for the target layout. |
| `docs/` | The *what/why*: `design.md` (architecture) and `developer.md` (build/verify). |
| `tests/` | QuickChick / extraction tests for definitions. |
| `tasks/` | Working plans: `global_plan.md` (multi-task) and `detailed_plan.md` (per task). |
| `.opencode/skills/` | The *how*: procedural skills for the development workflow. |
| `dune-project`, `src/dune`, `*.opam` | Build configuration (dune + opam). |

## Quick start

```sh
dune build        # build (compile + check all proofs)
dune build @doc   # render docs with rocqdoc
```

The full quality gate (build + independent `rocqchk` re-check + docs) and the
prerequisites live in [`docs/developer.md`](docs/developer.md).

## Working in this repo

This repository is driven by an agent workflow. **Start every session by
reading [`AGENTS.md`](AGENTS.md)** — it is the entry point and points to the
skills that define how work is planned, executed, reviewed, and merged.

- Documentation is the *what/why*; skills are the *how*.
- There is one source of truth per fact — no duplicates.
- A proof that compiles is the unit of verification.

## License

MIT — see [`LICENSE`](LICENSE).
