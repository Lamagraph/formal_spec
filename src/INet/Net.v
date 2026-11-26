(**
 * Net — the interaction-net data model.
 *
 * Defines nets as graphs of agents joined by links: the [Net] record, the
 * [well_formed] predicate, free ports and the net interface, active pairs,
 * and [net_iso], the up-to-renaming isomorphism under which every reduction
 * result in this theory is stated.
 *
 * This module is the bottom of the [INet] stack in the {@ docs/design.md}
 * layout: it depends on nothing inside [INet] and is depended on by
 * [Agent] and [Rewrite].
 *)

Require Import Stdlib.Lists.List.

(* [Stdlib.Lists.List] transitively opens [nat_scope] (via [PeanoNat]), which
   would read the infix [*] as natural-number multiplication. Reopen
   [type_scope] so that [*] denotes the product type throughout this module. *)
Open Scope type_scope.

(**************************************************************************)
(** ** Port references *)

(** A port reference identifies one port of one agent: the pair of the
    agent's id and the port number. Port [0] is the agent's main port; ports
    [1..n] are its auxiliary ports, where [n] is the agent's arity. *)
Definition port_ref := nat * nat.

(** The agent id of a port reference. *)
Definition agent_of (pr : port_ref) : nat := fst pr.

(** The port number of a port reference. *)
Definition port_of (pr : port_ref) : nat := snd pr.

(**************************************************************************)
(** ** Nets *)

(** A net over the label type [A] (the signature [Σ]) is a graph of labelled
    agents joined by undirected links.
    * [nt_agents] stores the agents as a list of (id, label) pairs;
    * [nt_links] stores the links as a list of pairs of port references.

    Agents and links are kept as separate data, faithful to the graph
    definition: no symmetry invariant is imposed on [nt_links] (a link may be
    stored in either orientation), and the invariants that make a net
    meaningful are captured by the [well_formed] predicate below. *)
Record Net (A : Type) := mkNet {
  nt_agents : list (nat * A);
  nt_links  : list (port_ref * port_ref)
}.

(* The label type [A] is recoverable from the net, so make it implicit in the
   projections: [nt_agents N] and [nt_links N] read naturally. *)
Arguments nt_agents {A} _.
Arguments nt_links {A} _.

(**************************************************************************)
(** ** Lookup helpers *)

(** [agent_label_lookup A a l] scans the agent list [l] for an entry whose id
    is [a] and returns its label, or [None] if no such entry exists. This is
    the list-level routine that [agent_label] delegates to. *)
Fixpoint agent_label_lookup (A : Type) (a : nat) (l : list (nat * A)) : option A :=
  match l with
  | nil => None
  | (id, lbl) :: rest => if Nat.eqb id a then Some lbl else agent_label_lookup A a rest
  end.

(** [agent_label A N a] is the label of agent [a] in [N], or [None] if [a] is
    not an agent of [N]. When [N] is well-formed ([wf_ids]), the label is
    well-defined: every occurrence of [a] in [nt_agents N] carries the same
    label, so the result does not depend on which occurrence is found. *)
Definition agent_label (A : Type) (N : Net A) (a : nat) : option A :=
  agent_label_lookup A a (nt_agents N).

(** [has_agent A N a] holds when [a] is the id of an agent of [N]. *)
Definition has_agent (A : Type) (N : Net A) (a : nat) : Prop :=
  agent_label A N a <> None.

(** [has_link A N pr1 pr2] holds when the port references [pr1] and [pr2] are
    joined by a link of [N]. Links are undirected: the pair may appear in
    either orientation in [nt_links N]. *)
Definition has_link (A : Type) (N : Net A) (pr1 pr2 : port_ref) : Prop :=
  In (pr1, pr2) (nt_links N) \/ In (pr2, pr1) (nt_links N).

(** [link_end l pr] holds when [pr] is one of the two ends of the link [l]. *)
Definition link_end (l : port_ref * port_ref) (pr : port_ref) : Prop :=
  fst l = pr \/ snd l = pr.

(** [port_used A N pr] holds when [pr] is an end of some link of [N]. *)
Definition port_used (A : Type) (N : Net A) (pr : port_ref) : Prop :=
  exists l, In l (nt_links N) /\ link_end l pr.

(**************************************************************************)
(** ** Well-formedness *)

(** [well_formed A Ar N] is the well-formedness predicate for a net [N] of
    label type [A] under the arity function [Ar : A -> nat] (the arity of a
    label is the number of its auxiliary ports; the port-range check needs it,
    which is why [Ar] is a parameter).

    It is a record whose four fields are the four well-formedness conditions,
    each exposed as a named projection so that later modules can address them
    individually (this is the "projection lemma" for each condition — no
    separate lemma is needed, [wf_ids H], [wf_links H], [wf_ports H] and
    [wf_ends H] extract the corresponding conjunct from a proof [H]):
    * [wf_ids] — unique agent ids: no agent id carries two different labels,
      so the label of a present agent is well-defined;
    * [wf_links] — valid links: every link joins two present agents, and each
      end's port number is in range for that agent's arity;
    * [wf_ports] — port-injectivity: no port is an end of two distinct links;
    * [wf_ends] — distinct link ends: the two ends of each link differ. *)
Record well_formed (A : Type) (Ar : A -> nat) (N : Net A) : Prop := mkWellFormed {
  wf_ids : forall a l1 l2,
    In (a, l1) (nt_agents N) -> In (a, l2) (nt_agents N) -> l1 = l2;
  wf_links : forall a b p q,
    In ((a, p), (b, q)) (nt_links N)
    -> has_agent A N a
    /\ has_agent A N b
    /\ forall la lb,
         agent_label A N a = Some la -> agent_label A N b = Some lb
         -> p <= Ar la /\ q <= Ar lb;
  wf_ports : forall pr l1 l2,
    In l1 (nt_links N) -> In l2 (nt_links N) -> l1 <> l2
    -> ~(link_end l1 pr /\ link_end l2 pr);
  wf_ends : forall l, In l (nt_links N) -> fst l <> snd l
}.

(* The parameters [A], [Ar], [N] are recoverable from a [well_formed] proof,
   so make them implicit in the projections: [wf_ids H], [wf_links H],
   [wf_ports H] and [wf_ends H] read naturally. *)
Arguments wf_ids {A Ar N} _.
Arguments wf_links {A Ar N} _.
Arguments wf_ports {A Ar N} _.
Arguments wf_ends {A Ar N} _.

(**************************************************************************)
(** ** Basic facts *)

(** [has_link] is symmetric: a link between [pr1] and [pr2] is the same as a
    link between [pr2] and [pr1]. *)
Lemma has_link_sym (A : Type) (N : Net A) (pr1 pr2 : port_ref) :
  has_link A N pr1 pr2 <-> has_link A N pr2 pr1.
Proof.
  split.
  - intros H; destruct H as [H|H]; [ right; exact H | left; exact H ].
  - intros H; destruct H as [H|H]; [ right; exact H | left; exact H ].
Qed.

(** The two endpoint agents of a link in a well-formed net are present. This
    is the existence part of [wf_links], isolated for use in later modules
    (active pairs, splice). *)
Lemma wf_link_agents (A : Type) (Ar : A -> nat) (N : Net A) (H : well_formed A Ar N)
      (a b : nat) (p q : nat) (Hl : In ((a, p), (b, q)) (nt_links N)) :
  has_agent A N a /\ has_agent A N b.
Proof.
  destruct (wf_links H a b p q Hl) as [Ha [Hb _]]; exact (conj Ha Hb).
Qed.
