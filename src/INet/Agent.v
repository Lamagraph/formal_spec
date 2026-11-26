(**
 * Agent — interaction systems: arities and rule tables.
 *
 * Defines the [Rule] and [System] records. An interaction system is an arity
 * function on agent labels together with a validated rule table: at most one
 * rule per unordered agent pair, each rule well-formed and carrying the
 * correct interface. The [sys_valid_*] lemmas expose the individual
 * validation conjuncts for use in [Rewrite].
 *
 * This module sits in the middle of the [INet] stack in the
 * {@ docs/design.md} layout: it depends on [Net] and is depended on by
 * [Rewrite].
 *)

Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.Lists.List.
Require Import Net.

(* [Net] opens [type_scope] globally, and that opens transitively here. In
   Rocq 9.3 the notation [/\] is declared only in [type_scope], so it must
   stay open; but an open [type_scope] makes the infix [+] resolve to a
   type-level operator rather than [Nat.add], which would break the
   arity-sum condition in [sys_valid] below. Opening [nat_scope] afterwards
   restores [+] to [Nat.add] (later-opened scopes win), while [/\] remains
   available from [type_scope]. The product type [*] in [ru_lhs] is
   unaffected: it appears in a type position, where it is interpreted as
   [prod] regardless of the open scopes. *)
Open Scope nat_scope.

(**************************************************************************)
(** ** Rules *)

(** A rule of an interaction system (§4.1): the raw data of one rewrite.
    * [ru_lhs] — the two agent labels that interact;
    * [ru_rhs] — the replacement net fragment;
    * [ru_iface] — the rule's interface: the free ports of [ru_rhs].

    The record carries no proofs: the invariants that make a rule meaningful
    (well-formedness of the RHS, exactness of the interface, the rule being
    for its pair) are validated by the enclosing [System] (§4.4). *)
Record Rule (A : Type) := mkRule {
  ru_lhs   : A * A;
  ru_rhs   : Net A;
  ru_iface : list port_ref
}.

(* [A] is recoverable from a [Rule] (through [ru_rhs]), so make it implicit
   in the projections and the constructor: [ru_lhs r], [ru_rhs r],
   [ru_iface r], and [mkRule lhs rhs iface] read naturally. *)
Arguments ru_lhs {A} _.
Arguments ru_rhs {A} _.
Arguments ru_iface {A} _.
Arguments mkRule {A} _ _ _.

(**************************************************************************)
(** ** Systems *)

(** An interaction system (§4.1, §4.4): an arity function on agent labels
    together with a validated rule table.
    * [sys_arity] — the arity of each label (the number of its auxiliary
      ports);
    * [sys_rules] — the rule table: for each ordered pair of labels, the
      rule for that pair, or [None];
    * [sys_sym] — the table is symmetric in its arguments: at most one rule
      per unordered agent pair (§4.4);
    * [sys_valid] — every rule in the table is valid for the pair it is
      looked up under (§4.4): the RHS is well-formed under [sys_arity]; the
      declared interface is exactly the RHS's free ports ([interface], in
      the right quantity — its [length] is the sum of the two arities); and
      the rule's LHS is that pair, in either order. *)
Record System (A : Type) := mkSystem {
  sys_arity : A -> nat;
  sys_rules : A -> A -> option (Rule A);
  sys_sym   : forall α β, sys_rules α β = sys_rules β α;
  sys_valid : forall α β (r : Rule A),
              sys_rules α β = Some r ->
                well_formed A sys_arity (ru_rhs r)
                /\ ru_iface r = interface A sys_arity (ru_rhs r)
                /\ length (ru_iface r)
                   = sys_arity (fst (ru_lhs r)) + sys_arity (snd (ru_lhs r))
                /\ (ru_lhs r = (α, β) \/ ru_lhs r = (β, α))
}.

(* [A] is recoverable from a [System], so make it implicit in the projections
   and the constructor: [sys_arity S], [sys_rules S α β], [sys_sym S α β],
   [sys_valid S α β r H], and [mkSystem arity rules sym valid] read
   naturally. *)
Arguments sys_arity {A} _.
Arguments sys_rules {A} _.
Arguments sys_sym {A} _.
Arguments sys_valid {A} _.
Arguments mkSystem {A} _ _ _ _.

(**************************************************************************)
(** ** The validation conjuncts *)

(** The RHS of a rule in the table is well-formed under the system's arity
    (§4.4). *)
Lemma sys_valid_wf (A : Type) (S : System A) (α β : A) (r : Rule A)
      (H : sys_rules S α β = Some r) :
  well_formed A (sys_arity S) (ru_rhs r).
Proof.
  destruct (sys_valid S α β r H) as [Hwf _].
  exact Hwf.
Qed.

(** The declared interface of a rule in the table is exactly the free ports
    of its RHS (§4.4). *)
Lemma sys_valid_iface (A : Type) (S : System A) (α β : A) (r : Rule A)
      (H : sys_rules S α β = Some r) :
  ru_iface r = interface A (sys_arity S) (ru_rhs r).
Proof.
  destruct (sys_valid S α β r H) as [_ [Hiface _]].
  exact Hiface.
Qed.

(** The interface of a rule in the table has the right quantity: its length
    is the sum of the arities of the two labels it interacts (§4.4). *)
Lemma sys_valid_len (A : Type) (S : System A) (α β : A) (r : Rule A)
      (H : sys_rules S α β = Some r) :
  length (ru_iface r)
    = sys_arity S (fst (ru_lhs r)) + sys_arity S (snd (ru_lhs r)).
Proof.
  destruct (sys_valid S α β r H) as [_ [_ [Hlen _]]].
  exact Hlen.
Qed.

(** A rule in the table is for the pair it is looked up under: its LHS is
    that pair, in either order (§4.4). *)
Lemma sys_valid_lhs (A : Type) (S : System A) (α β : A) (r : Rule A)
      (H : sys_rules S α β = Some r) :
  ru_lhs r = (α, β) \/ ru_lhs r = (β, α).
Proof.
  destruct (sys_valid S α β r H) as [_ [_ [_ Hlhs]]].
  exact Hlhs.
Qed.
