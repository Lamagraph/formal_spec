# Design

The **what** and **why** of the specification. This page holds design decisions
and the non-trivial constraints that cannot be reconstructed from the `.v`
sources. It is the north star that the `add-theory` skill and the planning
phase align to.

## What we are specifying

A formal specification of an **interaction-nets-based co-processor
(accelerator) architecture**. It has two top-level parts, and the
relationship between them:

1. **The math** — the implementation-detail-free foundations the
   specification and its proofs are built on: any abstract,
   hardware-independent material the development needs. Today its core is the
   formal interaction-net model (agents, rewrite rules, nets, redexes, the
   rewriting relation) — the abstract semantics the hardware must realize —
   but it is not limited to that.
2. **The RTL-like model** — a cycle-accurate and cycle-precise model of the
   concrete co-processor: memory organization, control, datapath, and
   scheduling. These quality properties are proved in the spec, not assumed
   (see the corresponding principle in `AGENTS.md`). This is the
   "implementation" we prove correct.

The central correctness goal is an **equivalence**: executing the RTL-like
model on a net yields the same observable result as applying the abstract
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

- **Rocq 9.3, dune build.** The prover is Rocq (the Coq project was renamed;
  on opam `coq` is a compatibility metapackage over `rocq-core`/
  `rocq-stdlib`), and the build is dune with the Rocq build language
  (`(using rocq …)` in `dune-project`, `rocq.theory` stanzas per directory).
  dune 3.24+ removed the old Coq build language, so a Coq 8.20.1 + dune
  combination is no longer viable; dune also provides native docs
  (`dune build @doc`), `.expected`-file testing, and IDE project files.
  Sources use `From Stdlib` (`From Coq` is deprecated since Rocq 9.0), and
  theory stanzas declare `(theories Stdlib)` because dune adds Corelib
  implicitly but not Stdlib.
- **Proofs are the tests.** We do not maintain a separate unit-test suite for
  theorems; a checked proof is the verification. QuickChick and extraction
  tests are used for *definitions* where random/empirical checking adds value
  (see `docs/developer.md`).

- **INet encoding (task #9).** The interaction-net model is encoded as
  `Net A = { nt_agents : list (nat * A); nt_links : list (port_ref * port_ref) }`
  — agents and links as *separate* data (faithful to the graph definition; no
  symmetry invariant), with `port_ref = nat * nat` (agent id, port number; port
  `0` = main, `1..n` = aux for arity `n`). A `well_formed A Ar N` predicate
  enforces unique agent ids, links referencing in-range ports of existing
  agents, port-injectivity, and distinct link ends. Nets are compared **up to
  renaming** via an explicit isomorphism `net_iso` (a label- and link-preserving
  bijection on agents); `step` is defined modulo `net_iso` and every theorem is
  stated modulo it, so the hard commutation lemma is an *isomorphism to
  exhibit* (no canonicalization function). The label type `A : Type`, the arity
  function `Ar : A -> nat`, and the rule table are parameters: every theorem is
  `forall (A : Type) (S : System A), …`.
- **Library survey (task #9).** Per "adopt, don't reinvent", no existing
  Rocq/Coq interaction-net formalization was found, so the model is built on
  **Stdlib only** (no new opam dependencies): `ReflTransCl` (`→*`),
  `Relations.Relation_Definitions`, `Classes.RelationalClasses` (`net_iso`),
  `Lists.Permutation` (commutation), `Perm.Perm` (iso witnesses), and
  `Arith`/`micromega` (port-index arithmetic). Heavy candidates (category-theory
  libraries for adhesive categories, and the CoLoR libraries for interaction
  nets) were surveyed and rejected: none models nets *up to renaming* with an
  explicit isomorphism, and adopting one would drag in a dependency for a small,
  self-contained model. Adhesive-category semantics and CoLoR are cited as
  related work, not dependencies.
- **Strong confluence + unique NFs (task #9).** The key structural fact is that
  any two active pairs in a well-formed net are **disjoint** (an active pair
  joins two agents by their *main* ports, and each agent has exactly one main
  port). Hence reducing one pair preserves every other active pair, and two
  reductions at disjoint pairs commute (up to renaming). This yields the
  one-step diamond, then confluence, then unique normal forms (4.7(2)), for
  **general rules** (RHS may contain active pairs). The swapped-orientation
  subcase (firing `(a,b)` vs `(b,a)` of a same-label rule) is joinable under the
  `orientation_symmetric` condition (the two splices are isomorphic) — strictly
  weaker than `distinct_lhs`, and satisfied by the λ-calculus (its `δ⊗δ` rule's
  RHS is symmetric under swapping the two interface halves).
- **4.7(1) (normalizable ⇒ SN) is an open conjecture (task #9).** The spec's
  4.7(1) — normalizable nets are strongly normalizable — is *not* proved. It is
  false for the general model (the λ/Ω loop needs duplication, a same-label
  LHS), and under the 4.9 restriction (`pair_free_rhs`) it is believed true but
  unproved: an executable model found no counterexample in 30,000 randomized
  iterations, and the only diverging constructions are "pump"-like self-
  sustaining cycles that are immortal (hence not normalizable). The proof is
  stuck on a global argument (infinite sequence ⇒ pump; normalizable ⇒ no pump)
  that a net-local well-founded measure cannot supply. Recorded as a conjecture;
  not part of the delivered result.

## Open questions

- Memory model granularity (per-agent cells vs. packed representation).
- Whether scheduling is specified deterministically or up to a fairness
  condition.

The agent/rule encoding question is resolved by task #9 (see "INet encoding"
above). The remaining questions concern the architecture layer and are to be
resolved in the first architecture task, not assumed here.
