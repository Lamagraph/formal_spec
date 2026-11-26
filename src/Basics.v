(**
 * Basics — root module of the LamaGraph formal specification.
 *
 * Holds shared imports, notations, and foundational lemmas that every other
 * theory imports. Keep this dependency-light: it sits at the bottom of the
 * module DAG, so it must not depend on {@ INet} or {@ Arch}.
 *
 * See {@ docs/design.md} for the target module layout.
 *)

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.Classical.

(**
 * Sanity check: the toolchain type-checks and verifies proofs.
 *
 * A proof that compiles under [coqc] is, in this project, the unit of
 * verification — there is no separate "test run" for a theorem.
 *)
Example sanity_check : 1 + 1 = 2.
Proof.
  reflexivity.
Qed.
