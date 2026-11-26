# Design

The **what** and **why** of the specification. This page holds design decisions
and the non-trivial constraints that cannot be reconstructed from the `.v`
sources. It is the north star that the `add-theory` skill and the planning
phase align to.

## What we are specifying

A formal specification of an **interaction-nets-based co-processor
(accelerator) architecture**. Two layers, and the relationship between them:

1. **The interaction-net model** — the abstract computational semantics:
   agents, rewrite rules, nets, redexes, and the rewriting relation. This is
   the "meaning" the hardware must realize.
2. **The architecture** — the concrete co-processor: memory organization,
   control, datapath, and scheduling. This is the "implementation" we prove
   correct.

The central correctness goal is an **equivalence**: executing the architecture
on a net yields the same observable result as applying the abstract
interaction-net rewrite relation. Everything in this repo exists to state and
prove that (and the lemmas that make it tractable).

## Target module layout

This is the intended shape of `src/`. It is a target, not a mandate — the
planning phase decides the exact decomposition per task. Keep the dependency
direction acyclic and pointing downward:

```
src/
├── Basics.v            # shared imports, notations, foundational lemmas (leaf)
├── INet/               # the interaction-net model (abstract semantics)
│   ├── Agent.v         #   agents and their rewrite rules
│   ├── Net.v           #   nets, redexes, the rewrite step
│   └── Rewrite.v       #   the rewrite relation + its basic properties
├── Arch/               # the co-processor architecture (concrete)
│   ├── Memory.v        #   net/agent storage
│   ├── Control.v       #   control state and transitions
│   ├── Datapath.v      #   datapath / rule application
│   └── Schedule.v      #   scheduling of redex firing
└── Correctness.v       # Arch execution ≡ INet rewriting (the main theorem)
```

Rules of thumb:

- **`Basics` is a leaf.** It must not depend on `INet` or `Arch`.
- **`INet` must not depend on `Arch`.** The model is independent of the
  hardware; correctness is proved *about* the model, not by it.
- **One concern per module.** If a module grows past a single responsibility,
  split it (see the `reusing` and `code-style` skills).
- **Names are the API.** A module's exported constants/lemmas are its public
  interface; name them for reuse, not for the local proof that motivated them.

## Standing design decisions

Record decisions here as they are made, so they survive the session that made
them. Format: a short title, the decision, and the *why*.

- **Coq 8.20.1, coq_makefile build.** Chosen for a proofs-centric spec: minimal
  setup, standard for pure `.v` work. Revisit only if heavy OCaml extraction or
  opam-library dependencies make `dune` clearly better.
- **Proofs are the tests.** We do not maintain a separate unit-test suite for
  theorems; a checked proof is the verification. QuickChick and extraction
  tests are used for *definitions* where random/empirical checking adds value
  (see `docs/developer.md`).

## Open questions

- Exact agent/rule encoding for the target interaction-net calculus (binary
  agents? explicit rule tables?).
- Memory model granularity (per-agent cells vs. packed representation).
- Whether scheduling is specified deterministically or up to a fairness
  condition.

These are to be resolved in the first planning task, not assumed here.
