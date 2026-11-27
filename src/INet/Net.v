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

Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Lists.Finite.
Require Import Stdlib.Logic.Classical.
Require Import Stdlib.Logic.Description.
Require Import Stdlib.Logic.ClassicalDescription.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Sorting.Mergesort.
Require Import Stdlib.Sorting.Permutation.
Require Import Stdlib.Sorting.Sorted.
Require Import Stdlib.Structures.Orders.

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
    well-defined: agent ids are unique, so [a] occurs at most once in
    [nt_agents N] and the result does not depend on which occurrence is found. *)
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
    * [wf_ids] — unique agent ids: no agent id appears more than once in the
      agent list. This makes the label of a present agent well-defined (the
      consequence [wf_ids_functional]: no id carries two labels) and is what
      lets [interface] enumerate the agents' ports without duplicates;
    * [wf_links] — valid links: every link joins two present agents, and each
      end's port number is in range for that agent's arity;
    * [wf_ports] — port-injectivity: no port is an end of two distinct links;
    * [wf_ends] — distinct link ends: the two ends of each link differ. *)
Record well_formed (A : Type) (Ar : A -> nat) (N : Net A) : Prop := mkWellFormed {
  wf_ids : NoDup (map fst (nt_agents N));
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

(**************************************************************************)
(** ** List facts used by the well-formedness consequences *)

(** If [x] occurs in [L], then [f x] occurs in [map f L]. The stdlib has no
    named [In_map], so we state it here for reuse. *)
Lemma In_map {A B : Type} (f : A -> B) (L : list A) (x : A) :
  In x L -> In (f x) (map f L).
Proof.
  induction L as [|z rest IH]; intros H.
  - simpl in H. inversion H.
  - simpl in H. destruct H as [H|H].
    + subst z. simpl. left. reflexivity.
    + right. apply IH. exact H.
Qed.

(** A [NoDup] list built by cons-ing [x] does not already contain [x]. This is
    the [NoDup_cons] constructor's premise, isolated for reuse. *)
Lemma NoDup_cons_notin (A : Type) (x : A) (l : list A) :
  NoDup (x :: l) -> ~ In x l.
Proof.
  intros H. inversion H. assumption.
Qed.

(** A [NoDup] list built by cons-ing [x] over [l] has [l] itself [NoDup]. This
    is the [NoDup_cons] constructor's tail premise, isolated for reuse. *)
Lemma NoDup_cons_nodup (A : Type) (x : A) (l : list A) :
  NoDup (x :: l) -> NoDup l.
Proof.
  intros H. inversion H. assumption.
Qed.

(** If [map f L] has no duplicates, then [f] is injective on the elements of
    [L]: two elements of [L] with the same image under [f] are equal. This is
    the multiplicity-free form of "NoDup of the image implies injectivity on
    the preimage elements". *)
Lemma nodup_map_inj (A B : Type) (f : A -> B) (L : list A) (Hn : NoDup (map f L))
      (x y : A) (Hx : In x L) (Hy : In y L) (Hf : f x = f y) : x = y.
Proof.
  revert Hx Hy Hf.
  induction L as [|z rest IH]; intros Hx Hy Hf.
  - simpl in Hx. inversion Hx.
  - simpl in Hx. destruct Hx as [Hx|Hx].
    + (* Hx : z = x *)
      simpl in Hy. destruct Hy as [Hy|Hy].
      * (* Hy : z = y *)
        subst z. exact Hy.
      * (* Hy : In y rest *)
        subst z.
        exfalso.
        assert (Hnotin : ~ In (f x) (map f rest)).
        { exact (NoDup_cons_notin _ _ _ Hn). }
        assert (Hin : In (f x) (map f rest)).
        { rewrite Hf. apply In_map. exact Hy. }
        contradiction.
    + (* Hx : In x rest *)
      simpl in Hy. destruct Hy as [Hy|Hy].
      * (* Hy : z = y *)
        subst z.
        exfalso.
        assert (Hnotin : ~ In (f y) (map f rest)).
        { exact (NoDup_cons_notin _ _ _ Hn). }
        assert (Hin : In (f y) (map f rest)).
        { rewrite <- Hf. apply In_map. exact Hx. }
        contradiction.
      * (* Hy : In y rest *)
        eapply IH; [exact (NoDup_cons_nodup _ _ _ Hn) | exact Hx | exact Hy | exact Hf].
Qed.

(**************************************************************************)
(** ** Free ports and the net interface *)

(** [is_free A Ar N pr] holds when the port reference [pr] is a free port of
    the net [N]: the agent it refers to is present in [N], the port number is
    in range for that agent's arity, and the port is not an end of any link.
    The agent's presence is witnessed by the existence of its label [la],
    which simultaneously supplies the arity bound [Ar la]. *)
Definition is_free (A : Type) (Ar : A -> nat) (N : Net A) (pr : port_ref) : Prop :=
  exists la, agent_label A N (agent_of pr) = Some la
             /\ port_of pr <= Ar la
             /\ ~ port_used A N pr.

(**************************************************************************)
(** ** Boolean mirrors for filtering *)

(** [filter] takes a [bool] predicate, but [link_end] and [port_used] are
    propositions. These boolean mirrors compute the same facts decidablely:
    each is [true] exactly when the corresponding proposition holds (see the
    [_spec] lemmas). They exist solely to build [free_ports_of] below. *)

(** Boolean mirror of [link_end]. *)
Definition link_end_b (l : port_ref * port_ref) (pr : port_ref) : bool :=
  match l, pr with
  | ((a1, p1), (a2, p2)), (a3, p3) =>
      (Nat.eqb a1 a3 && Nat.eqb p1 p3) || (Nat.eqb a2 a3 && Nat.eqb p2 p3)
  end.

(** Boolean mirror of [port_used]. *)
Definition port_used_b (A : Type) (N : Net A) (pr : port_ref) : bool :=
  existsb (fun l => link_end_b l pr) (nt_links N).

(** Boolean mirror of [link_end]: [link_end_b l pr = true] iff [link_end l pr]. *)
Lemma link_end_b_spec (l : port_ref * port_ref) (pr : port_ref) :
  link_end_b l pr = true <-> link_end l pr.
Proof.
  destruct l as [[a1 p1] [a2 p2]]; destruct pr as [a3 p3]; simpl.
  rewrite orb_true_iff, andb_true_iff, andb_true_iff.
  repeat rewrite Nat.eqb_eq.
  split.
  - intro H. destruct H as [H | H].
    + left. destruct H as [H1 H2]. subst. reflexivity.
    + right. destruct H as [H1 H2]. subst. reflexivity.
  - intro H. destruct H as [H | H].
    + left. injection H as -> ->. split; reflexivity.
    + right. injection H as -> ->. split; reflexivity.
Qed.

(** Boolean mirror of [port_used]: [port_used_b A N pr = true] iff
    [port_used A N pr]. *)
Lemma port_used_b_spec (A : Type) (N : Net A) (pr : port_ref) :
  port_used_b A N pr = true <-> port_used A N pr.
Proof.
  unfold port_used_b.
  rewrite existsb_exists.
  split.
  - intro H. destruct H as [l [Hl Hle]].
    exists l. split; [exact Hl | ].
    simpl in Hle.
    rewrite link_end_b_spec in Hle.
    exact Hle.
  - intro H. destruct H as [l [Hl Hle]].
    exists l. split; [exact Hl | ].
    simpl.
    rewrite link_end_b_spec.
    exact Hle.
Qed.

(**************************************************************************)
(** ** Free ports of one agent, and the net interface *)

(** [free_ports_of A Ar N a alpha] is the list of the free ports of agent [a]
    (whose label is [alpha]), in increasing port-number order: the ports
    [0 .. Ar alpha] that are not an end of any link of [N]. *)
Definition free_ports_of (A : Type) (Ar : A -> nat) (N : Net A) (a : nat) (alpha : A) : list port_ref :=
  map (fun p => (a, p))
      (filter (fun p => negb (port_used_b A N (a, p))) (seq 0 (S (Ar alpha)))).

(**************************************************************************)
(** ** Lexicographic order on port references *)

(** [PortRefOrder] is the lexicographic order on port references — agent id
    first, then port number — as a total boolean order, the interface required
    by the stdlib sorting functor. *)
Module PortRefOrder <: TotalLeBool'.
  Definition t := port_ref.
  Definition leb (x y : port_ref) : bool :=
    match x, y with
    | (a1, p1), (a2, p2) =>
        if Nat.eqb a1 a2 then Nat.leb p1 p2 else Nat.ltb a1 a2
    end.
  Infix "<=?" := leb (at level 70, no associativity).

  (** [leb] computes the lexicographic order: [leb x y = true] exactly when
      [x] precedes [y] (agent id first, then port number). *)
  Lemma leb_rel (a1 p1 a2 p2 : nat) :
    leb (a1, p1) (a2, p2) = true <-> a1 < a2 \/ (a1 = a2 /\ p1 <= p2).
  Proof.
    simpl.
    case_eq (Nat.eqb a1 a2); intros Hb.
    - apply (Nat.eqb_eq a1 a2) in Hb.
      subst a2.
      split.
      + intro H. rewrite Nat.leb_le in H. right. split; [reflexivity | exact H].
      + intro H. destruct H as [Hlt | [Heq Hle]].
        * exfalso. apply Nat.lt_irrefl in Hlt. contradiction.
        * rewrite Nat.leb_le. exact Hle.
    - assert (Hne : a1 <> a2).
      { intro Ha. subst a2.
        assert (Htrue : Nat.eqb a1 a1 = true) by (apply (Nat.eqb_eq a1 a1); reflexivity).
        rewrite Htrue in Hb.
        discriminate Hb. }
      split.
      + intro H. rewrite Nat.ltb_lt in H. left. exact H.
      + intro H. destruct H as [Hlt | [Heq Hle]].
        * rewrite Nat.ltb_lt. exact Hlt.
        * exfalso. apply Hne. exact Heq.
  Qed.

  Theorem leb_total : forall x y, (x <=? y) = true \/ (y <=? x) = true.
  Proof.
    intros x y. destruct x as [a1 p1]; destruct y as [a2 p2].
    rewrite (leb_rel a1 p1 a2 p2), (leb_rel a2 p2 a1 p1).
    lia.
  Qed.
End PortRefOrder.

(** [PortRefSort] is the stdlib mergesort instantiated with [PortRefOrder]:
    [PortRefSort.sort l] is a permutation of [l] that is sorted in
    lexicographic (agent id, port number) order. *)
Module PortRefSort := Mergesort.Sort PortRefOrder.

(** The lexicographic order on port references, as a [Prop]: [port_ref_le x y]
    holds when [x] precedes [y] or equals it (agent id first, then port
    number). This is the relation in which [interface] is sorted. *)
Definition port_ref_le (x y : port_ref) : Prop :=
  match x, y with
  | (a1, p1), (a2, p2) => a1 < a2 \/ (a1 = a2 /\ p1 <= p2)
  end.

(** [PortRefOrder.leb] computes [port_ref_le]. *)
Lemma port_ref_leb_spec (x y : port_ref) :
  PortRefOrder.leb x y = true <-> port_ref_le x y.
Proof.
  destruct x as [a1 p1]; destruct y as [a2 p2]; simpl.
  exact (PortRefOrder.leb_rel a1 p1 a2 p2).
Qed.

(** Changing the relation of a [Sorted.HdRel] / [Sorted.Sorted] proof: if [R]
    and [R'] agree pointwise, a list that is [R]-sorted is also [R']-sorted.
    This moves the sortedness certificate from the boolean order
    [PortRefOrder.leb] (what the sort functor certifies) to the propositional
    [port_ref_le]. *)
Lemma HdRel_rel_change (A : Type) (R R' : A -> A -> Prop) (x : A) (l : list A)
      (H : forall x y, R x y <-> R' x y) :
  Sorted.HdRel R x l -> Sorted.HdRel R' x l.
Proof.
  intros Hh. induction Hh as [|y l Hy]; constructor.
  - rewrite (H x y) in Hy. exact Hy.
Qed.

(** Sortedness is preserved when the ordering relation is replaced by an
    equivalent one. *)
Lemma Sorted_rel_change (A : Type) (R R' : A -> A -> Prop) (l : list A)
      (H : forall x y, R x y <-> R' x y) :
  Sorted.Sorted R l -> Sorted.Sorted R' l.
Proof.
  intros Hs.
  revert Hs.
  induction l as [|a tail IHl]; intros Hs.
  - constructor.
  - inversion Hs.
    constructor.
    + apply IHl. assumption.
    + eapply HdRel_rel_change; eassumption.
Qed.

(** [interface A Ar N] is the list of all free ports of [N], in canonical
    order: sorted by (agent id, port number). It is total and deterministic —
    a pure function of [N] — the stable enumeration of free ports that the
    architecture layer schedules over. *)
Definition interface (A : Type) (Ar : A -> nat) (N : Net A) : list port_ref :=
  PortRefSort.sort
    (flat_map (fun p => free_ports_of A Ar N (fst p) (snd p)) (nt_agents N)).

(**************************************************************************)
(** ** Facts about the lookup and the free-port lists *)

(** If [a] occurs in the agent list [l] with label [alpha], and [l] is
    functional on [a] (every occurrence of [a] carries the same label), then
    the lookup returns [Some alpha]. *)
Lemma agent_label_lookup_In (A : Type) (a : nat) (l : list (nat * A)) (alpha : A)
      (Ha : In (a, alpha) l)
      (Hfun : forall l1 l2, In (a, l1) l -> In (a, l2) l -> l1 = l2) :
  agent_label_lookup A a l = Some alpha.
Proof.
  revert Ha Hfun.
  induction l as [|(id, lbl) rest IH]; intros Ha Hfun.
  - inversion Ha.
  - destruct (Nat.eqb id a) eqn:Hb.
    + apply (Nat.eqb_eq id a) in Hb. subst id.
      simpl.
      assert (Heq : Nat.eqb a a = true) by (apply (Nat.eqb_eq a a); reflexivity).
      rewrite Heq. simpl.
      apply f_equal.
      apply Hfun.
      * apply in_eq.
      * exact Ha.
    + simpl. rewrite Hb. simpl.
      destruct Ha as [H | H].
      * exfalso.
        injection H as -> ->.
        assert (Htrue : Nat.eqb a a = true) by (apply (Nat.eqb_eq a a); reflexivity).
        rewrite Htrue in Hb.
        discriminate Hb.
      * apply (IH H).
        intros l1 l2 H1 H2.
        apply Hfun; [apply in_cons; exact H1 | apply in_cons; exact H2].
Qed.

(** In a well-formed net, an agent id carries at most one label: two entries
    of the agent list with the same id have the same label. This is the
    functional-labels consequence of the unique-ids condition [wf_ids] (NoDup
    of the ids), isolated for use where a label's uniqueness is needed. *)
Lemma wf_ids_functional (A : Type) (Ar : A -> nat) (N : Net A) (H : well_formed A Ar N)
      (a : nat) (l1 l2 : A) :
  In (a, l1) (nt_agents N) -> In (a, l2) (nt_agents N) -> l1 = l2.
Proof.
  intros H1 H2.
  exact (f_equal snd
           (nodup_map_inj _ _ (fun p => fst p) (nt_agents N) (wf_ids H)
             (a, l1) (a, l2) H1 H2 (reflexivity _))).
Qed.

(* [A], [Ar], [N] are recoverable, so make them implicit: [wf_ids_functional
   H a] reads naturally. *)
Arguments wf_ids_functional {A Ar N} _ _ _ _.

(** In a well-formed net, the label of a present agent is the label stored in
    the agent list. *)
Lemma agent_label_In (A : Type) (Ar : A -> nat) (N : Net A) (H : well_formed A Ar N)
      (a : nat) (alpha : A) (Ha : In (a, alpha) (nt_agents N)) :
  agent_label A N a = Some alpha.
Proof.
  unfold agent_label.
  exact (agent_label_lookup_In A a (nt_agents N) alpha Ha (wf_ids_functional H a)).
Qed.

(** If the lookup of [a] in [l] returns [Some la], then [(a, la)] occurs in
    [l]. No well-formedness is needed: the lookup only returns labels that are
    actually stored in the list. *)
Lemma agent_label_lookup_Some_In (A : Type) (a : nat) (l : list (nat * A)) (la : A)
      (Hal : agent_label_lookup A a l = Some la) :
  In (a, la) l.
Proof.
  revert Hal.
  induction l as [|(id, lbl) rest IH]; intros Hal.
  - simpl in Hal. inversion Hal.
  - destruct (Nat.eqb id a) eqn:Hb.
    + apply (Nat.eqb_eq id a) in Hb. subst id.
      simpl in Hal.
      assert (Heq : Nat.eqb a a = true) by (apply (Nat.eqb_eq a a); reflexivity).
      rewrite Heq in Hal. simpl in Hal.
      injection Hal as ->.
      apply in_eq.
    + simpl in Hal. rewrite Hb in Hal. simpl in Hal.
      apply in_cons.
      exact (IH Hal).
Qed.

(** If [a]'s label is found in [N], then [(a, la)] is in the agent list. *)
Lemma agent_label_Some_In (A : Type) (N : Net A) (a : nat) (la : A)
      (Hal : agent_label A N a = Some la) :
  In (a, la) (nt_agents N).
Proof.
  unfold agent_label.
  exact (agent_label_lookup_Some_In A a (nt_agents N) la Hal).
Qed.

(** The free ports of one agent are distinct: the port numbers
    [0 .. Ar alpha] are distinct, filtering preserves that, and pairing with
    [a] is injective. *)
Lemma free_ports_of_NoDup (A : Type) (Ar : A -> nat) (N : Net A) (a : nat) (alpha : A) :
  NoDup (free_ports_of A Ar N a alpha).
Proof.
  unfold free_ports_of.
  apply Injective_map_NoDup.
  - intros p1 p2 H. injection H as ->. reflexivity.
  - apply NoDup_filter.
    apply seq_NoDup.
Qed.

(** The free-port lists of two distinct agents are disjoint: a port reference
    in the list of agent [a] has agent id [a]. *)
Lemma free_ports_of_disjoint (A : Type) (Ar : A -> nat) (N : Net A)
      (a a' : nat) (alpha alpha' : A) (Hne : a <> a') (pr : port_ref) :
  In pr (free_ports_of A Ar N a alpha) -> ~ In pr (free_ports_of A Ar N a' alpha').
Proof.
  unfold free_ports_of.
  intros Hin Hin'.
  destruct pr as [a3 p3].
  apply in_map_iff in Hin as [p [Hpe Hp]].
  apply in_map_iff in Hin' as [p' [Hpe' Hp']].
  injection Hpe as ->.
  injection Hpe' as ->.
  exact (Hne eq_refl).
Qed.

(** If the agent ids of [agents] are unique, then the concatenation of their
    free-port lists (as computed by [flat_map]) has no duplicates. This is the
    NoDup core of [interface_nodup], stated over an explicit list so that the
    induction does not fight the [nt_agents] projection. *)
Lemma fpo_flat_NoDup (A : Type) (Ar : A -> nat) (N : Net A)
      (agents : list (nat * A)) (Huid : NoDup (map fst agents)) :
  NoDup (flat_map (fun p => free_ports_of A Ar N (fst p) (snd p)) agents).
Proof.
  induction agents as [|(a, alpha) rest IH]; simpl.
  - apply NoDup_nil.
  - apply NoDup_cons_iff in Huid.
    destruct Huid as [Hnotin Huid'].
    apply NoDup_app.
    + apply free_ports_of_NoDup.
    + apply IH. exact Huid'.
    + intros pr Hin Hflat.
      apply in_flat_map in Hflat as [pair [Hagent Hfree']].
      destruct pair as [a' alpha'].
      assert (Hne : a <> a').
      { intro Heq. subst a'.
        apply Hnotin.
        apply in_map_iff.
        exists (a, alpha').
        split; [reflexivity | exact Hagent]. }
      apply (free_ports_of_disjoint A Ar N a a' alpha alpha' Hne pr) in Hin as Hcontra.
      exact (Hcontra Hfree').
Qed.

(**************************************************************************)
(** ** The interface lemmas *)

(** Every port reference listed in [interface] is free. *)
Lemma interface_free (A : Type) (Ar : A -> nat) (N : Net A) (H : well_formed A Ar N)
      (pr : port_ref) (Hin : In pr (interface A Ar N)) :
  is_free A Ar N pr.
Proof.
  unfold interface, is_free.
  apply (Permutation_in pr (Permutation_sym (PortRefSort.Permuted_sort _))) in Hin.
  destruct pr as [a p].
  apply in_flat_map in Hin as [pair [Hagent Hfree]].
  destruct pair as [a' alpha].
  apply in_map_iff in Hfree as [p' [Hpe Hp]].
  injection Hpe as ->.
  subst p'.
  apply filter_In in Hp as [Hpseq Hpu].
  apply in_seq in Hpseq as [Hlo Hhi].
  change (p < S (Ar alpha)) in Hhi.
  exists alpha.
  split; [ | split; [ | ]].
  + exact (agent_label_In A Ar N H a alpha Hagent).
  + simpl.
    apply (proj1 (Nat.lt_succ_r p (Ar alpha))) in Hhi.
    exact Hhi.
  + assert (Hnot : ~ port_used A N (a, p)).
    { intro Hused.
      simpl in Hpu.
      apply port_used_b_spec in Hused.
      rewrite negb_true_iff in Hpu.
      rewrite Hused in Hpu.
      discriminate Hpu. }
    exact Hnot.
Qed.

(** Every free port appears in [interface]. *)
Lemma free_in_interface (A : Type) (Ar : A -> nat) (N : Net A) (H : well_formed A Ar N)
      (pr : port_ref) (Hf : is_free A Ar N pr) :
  In pr (interface A Ar N).
Proof.
  unfold interface, is_free in Hf.
  destruct Hf as [la [Hal [Hrange Hpu]]].
  destruct pr as [a p].
  simpl in Hal.
  assert (Hagent : In (a, la) (nt_agents N)).
  { exact (agent_label_Some_In A N a la Hal). }
  assert (Hfree : In (a, p) (free_ports_of A Ar N a la)).
  { unfold free_ports_of.
    apply in_map_iff.
    exists p.
    split.
    - reflexivity.
    - apply filter_In.
      split.
      + apply in_seq.
        split; [lia | (simpl in Hrange; apply (proj2 (Nat.lt_succ_r p (Ar la))); exact Hrange)].
      + assert (Hnotb : port_used_b A N (a, p) = false).
        { destruct (port_used_b A N (a, p)) eqn:Hb.
          - apply port_used_b_spec in Hb.
            exfalso.
            exact (Hpu Hb).
          - reflexivity. }
        rewrite negb_true_iff.
        exact Hnotb. }
  apply (Permutation_in (a, p) (PortRefSort.Permuted_sort _)).
  apply in_flat_map.
  exists (a, la).
  split; [exact Hagent | exact Hfree].
Qed.

(** [interface] has no duplicates (in a well-formed net, whose agent ids are
    unique). *)
Lemma interface_nodup (A : Type) (Ar : A -> nat) (N : Net A) (H : well_formed A Ar N) :
  NoDup (interface A Ar N).
Proof.
  unfold interface.
  apply (Permutation_NoDup (PortRefSort.Permuted_sort _)).
  apply fpo_flat_NoDup.
  exact (wf_ids H).
Qed.

(** [interface] is sorted by (agent id, port number) — for any net, no
    well-formedness needed. *)
Lemma interface_sorted (A : Type) (Ar : A -> nat) (N : Net A) :
  Sorted.Sorted port_ref_le (interface A Ar N).
Proof.
  unfold interface.
  apply (Sorted_rel_change _ (fun x y => PortRefOrder.leb x y = true) port_ref_le _ port_ref_leb_spec).
  apply PortRefSort.Sorted_sort.
Qed.

(**************************************************************************)
(** ** Active pairs *)

(** An [active pair] is a pair of distinct agents joined by a link between
    their main ports (port [0]). It is the reducible unit of an interaction
    net: a reduction step fires on exactly one active pair. [Ar] is carried
    for signature uniformity with the other net predicates ([well_formed],
    [is_free], [interface]); [is_active_pair] itself does not consult it. *)
Definition is_active_pair (A : Type) (Ar : A -> nat) (N : Net A) (a b : nat) : Prop :=
  a <> b /\ has_agent A N a /\ has_agent A N b /\ has_link A N (a, 0) (b, 0).

(** In a well-formed net, a port is the end of at most one link: if [pr1] is
    linked to [pr2] and to [pr3], then [pr2 = pr3]. This restates the
    port-injectivity condition [wf_ports] for linked ports and is the key fact
    behind the disjointness of active pairs. *)
Lemma link_unique (A : Type) (Ar : A -> nat) (N : Net A) (H : well_formed A Ar N)
      (pr1 pr2 pr3 : port_ref) :
  has_link A N pr1 pr2 -> has_link A N pr1 pr3 -> pr2 = pr3.
Proof.
  intros H12 H13.
  (* H12 : In (pr1,pr2) \/ In (pr2,pr1); H13 : In (pr1,pr3) \/ In (pr3,pr1).
     In each case pr1 is an end of two links, l1 and l2. Either l1 = l2, in
     which case the equality of the pairs yields the result, or l1 <> l2, in
     which case wf_ports (port-injectivity) contradicts both ending at pr1. *)
  destruct H12 as [H12|H12]; destruct H13 as [H13|H13].
  - (* l1 = (pr1,pr2) [pr1 = fst], l2 = (pr1,pr3) [pr1 = fst] *)
    destruct (classic ((pr1, pr2) = (pr1, pr3))) as [Heq|Hneq].
    + injection Heq as H23. exact H23.
    + exfalso.
      apply (wf_ports H pr1 (pr1, pr2) (pr1, pr3) H12 H13 Hneq).
      split; [left; reflexivity | left; reflexivity].
  - (* l1 = (pr1,pr2) [pr1 = fst], l2 = (pr3,pr1) [pr1 = snd] *)
    destruct (classic ((pr1, pr2) = (pr3, pr1))) as [Heq|Hneq].
    + injection Heq as Hf Hs. subst pr3. exact Hs.
    + exfalso.
      apply (wf_ports H pr1 (pr1, pr2) (pr3, pr1) H12 H13 Hneq).
      split; [left; reflexivity | right; reflexivity].
  - (* l1 = (pr2,pr1) [pr1 = snd], l2 = (pr1,pr3) [pr1 = fst] *)
    destruct (classic ((pr2, pr1) = (pr1, pr3))) as [Heq|Hneq].
    + injection Heq as Hf Hs. subst pr2. exact Hs.
    + exfalso.
      apply (wf_ports H pr1 (pr2, pr1) (pr1, pr3) H12 H13 Hneq).
      split; [right; reflexivity | left; reflexivity].
  - (* l1 = (pr2,pr1) [pr1 = snd], l2 = (pr3,pr1) [pr1 = snd] *)
    destruct (classic ((pr2, pr1) = (pr3, pr1))) as [Heq|Hneq].
    + injection Heq as H23. exact H23.
    + exfalso.
      apply (wf_ports H pr1 (pr2, pr1) (pr3, pr1) H12 H13 Hneq).
      split; [right; reflexivity | right; reflexivity].
Qed.

(** Two active pairs in a well-formed net that share an agent are the same
    pair: if [a = c] then [b = d]. Consequently, DISTINCT active pairs share
    no agents at all — they are disjoint. This disjointness is the key
    ingredient of the strong-confluence proof: reducing one active pair leaves
    every other active pair intact, so two reductions at disjoint pairs
    commute. *)
Lemma pair_disjoint (A : Type) (Ar : A -> nat) (N : Net A) (H : well_formed A Ar N)
      (a b c d : nat)
      (Hab : is_active_pair A Ar N a b)
      (Hcd : is_active_pair A Ar N c d) :
  a = c -> b = d.
Proof.
  intros Hac.
  unfold is_active_pair in Hab, Hcd.
  destruct Hab as [Haneq Hrest]. destruct Hrest as [Haa Hrest2].
  destruct Hrest2 as [Hba Hablink].
  destruct Hcd as [Hcneq Hcrest]. destruct Hcrest as [Hca Hcrest2].
  destruct Hcrest2 as [Hda Hcdlink].
  subst c.
  (* Hablink : has_link (a,0) (b,0); Hcdlink : has_link (a,0) (d,0). *)
  exact (f_equal fst (link_unique A Ar N H (a, 0) (b, 0) (d, 0) Hablink Hcdlink)).
Qed.

(**************************************************************************)
(** ** Net isomorphism (equality up to renaming) *)

(** Two nets are [net_iso] when one can be obtained from the other by
    renaming agent ids: a function [ni_map] that bijects the agent sets
    (distinct agents of [N1] get distinct names in [N2], and every agent of
    [N2] is the image of a unique agent of [N1]) while carrying the links
    along. [Ar] is carried for signature uniformity with the other net
    predicates; [net_iso] itself does not consult it.

    The clauses are [Permutation]s of the agent and link lists, not pointwise
    statements: the multiset of (id, label) pairs of [N2] is exactly the
    image, under [ni_map], of that of [N1], and likewise for links. This pins
    down multiplicities and forbids extra or missing links, which is what
    makes [net_iso] a genuine equivalence on well-formed nets (see
    [net_iso_reflexive], [net_iso_symmetric], [net_iso_transitive]) and what
    lets a well-formed source yield a well-formed target
    ([net_iso_pres_wf]). *)
Record net_iso (A : Type) (Ar : A -> nat) (N1 N2 : Net A) := mkNetIso {
  ni_map : nat -> nat;
  ni_agents : Permutation
                (map (fun p => (ni_map (fst p), snd p)) (nt_agents N1))
                (nt_agents N2);
  ni_inj : forall a1 a2,
    has_agent A N1 a1 -> has_agent A N1 a2
    -> ni_map a1 = ni_map a2 -> a1 = a2;
  ni_links : Permutation
               (map (fun l => ((ni_map (fst (fst l)), snd (fst l)),
                               (ni_map (fst (snd l)), snd (snd l))))
                   (nt_links N1))
               (nt_links N2)
}.

(* The parameters [A], [Ar], [N1], [N2] are recoverable from a [net_iso]
   proof, so make them implicit in the projections: [ni_map H], [ni_agents H],
   [ni_inj H], [ni_links H] read naturally. *)
Arguments ni_map {A Ar N1 N2} _.
Arguments ni_agents {A Ar N1 N2} _.
Arguments ni_inj {A Ar N1 N2} _.
Arguments ni_links {A Ar N1 N2} _.
Arguments mkNetIso {A Ar N1 N2} _ _ _ _.

(**************************************************************************)
(** ** List and lookup facts used by the isomorphism *)

(** [map f (map g l) = map (fun x => f (g x)) l]. The stdlib has no named
    [map_comp]. *)
Lemma map_comp {A B C : Type} (f : B -> C) (g : A -> B) (l : list A) :
  map f (map g l) = map (fun x => f (g x)) l.
Proof.
  induction l as [|x rest IH]; simpl; [ reflexivity | f_equal; assumption ].
Qed.

(** If [f] acts as the identity on every element of [l], then [map f l = l]. *)
Lemma map_id_on_elements {A : Type} (f : A -> A) (l : list A)
      (Hid : forall x, In x l -> f x = x) : map f l = l.
Proof.
  induction l as [|x rest IH]; simpl.
  - reflexivity.
  - assert (Hx : f x = x).
    { apply Hid. left. reflexivity. }
    rewrite Hx.
    f_equal.
    apply IH.
    intros y Hy. apply Hid. right. exact Hy.
Qed.

(** If [b] occurs in [map f l], then it is the image of an element of [l]. *)
Lemma In_map_inv {A B : Type} (f : A -> B) (l : list A) (b : B) :
  In b (map f l) -> exists a, In a l /\ f a = b.
Proof.
  induction l as [|x rest IH]; intros H.
  - simpl in H. inversion H.
  - simpl in H. destruct H as [H|H].
    + exists x. split; [ left; reflexivity | exact H ].
    + destruct (IH H) as [a [Ha Hfa]]. exists a. split; [ right; exact Ha | exact Hfa ].
Qed.

(** If [a] occurs among the ids of [l], the lookup finds some label for it. *)
Lemma agent_label_In_map (A : Type) (a : nat) (l : list (nat * A)) :
  In a (map fst l) -> agent_label_lookup A a l <> None.
Proof.
  induction l as [| (id, lbl) rest IH]; intros H.
  - simpl in H. inversion H.
  - simpl in H. destruct H as [H|H].
    + subst a.
      unfold agent_label_lookup.
      assert (Hb : Nat.eqb id id = true) by (apply (proj2 (Nat.eqb_eq id id)); reflexivity).
      rewrite Hb. simpl. intro Heq. discriminate Heq.
    + destruct (Nat.eqb id a) eqn:Hb.
      * unfold agent_label_lookup.
        rewrite Hb. simpl. intro Heq. discriminate Heq.
      * unfold agent_label_lookup.
        rewrite Hb. simpl. apply IH. exact H.
Qed.

(** [has_agent] is membership of the id in the agent list. *)
Lemma has_agent_In (A : Type) (N : Net A) (a : nat) :
  has_agent A N a <-> In a (map fst (nt_agents N)).
Proof.
  unfold has_agent, agent_label.
  split.
  - intros H.
    assert (Hpos : exists la, agent_label_lookup A a (nt_agents N) = Some la).
    { destruct (agent_label_lookup A a (nt_agents N)) as [la|].
      + exists la. reflexivity.
      + exfalso. apply H. reflexivity. }
    destruct Hpos as [la Hal].
    apply (In_map fst (nt_agents N) (a, la)).
    exact (agent_label_Some_In A N a la Hal).
  - intros H.
    apply agent_label_In_map.
    exact H.
Qed.

(** Agents of [N1] are carried to agents of [N2] by [ni_map]. *)
Lemma net_iso_agent_fwd (A : Type) (Ar : A -> nat) (N1 N2 : Net A)
      (H : net_iso A Ar N1 N2) (a : nat) :
  has_agent A N1 a -> has_agent A N2 (ni_map H a).
Proof.
  intros Ha.
  apply (proj1 (has_agent_In A N1 a)) in Ha.
  apply In_map_inv in Ha as [p [Hp Hpa]].
  destruct p as [x lx].
  simpl in Hpa.
  subst x.
  apply (In_map (fun p => (ni_map H (fst p), snd p)) (nt_agents N1) (a, lx)) in Hp.
  apply (Permutation_in _ (ni_agents H)) in Hp.
  apply (proj2 (has_agent_In A N2 (ni_map H a))).
  apply (In_map fst (nt_agents N2) (ni_map H a, lx)).
  exact Hp.
Qed.

(** Every agent of [N2] is the image, under [ni_map], of an agent of [N1]
    (unique, by [ni_inj]). Together with [net_iso_agent_fwd], [ni_map] is a
    bijection between the agent sets. *)
Lemma net_iso_surj (A : Type) (Ar : A -> nat) (N1 N2 : Net A)
      (H : net_iso A Ar N1 N2) (b : nat) :
  has_agent A N2 b -> exists a, has_agent A N1 a /\ ni_map H a = b.
Proof.
  intros Hb.
  apply (proj1 (has_agent_In A N2 b)) in Hb.
  apply In_map_inv in Hb as [p [Hp Hpb]].
  destruct p as [x lx].
  simpl in Hpb.
  subst x.
  apply (Permutation_in _ (Permutation_sym (ni_agents H))) in Hp.
  apply (In_map_inv (fun p : nat * A => (ni_map H (fst p), snd p)) (nt_agents N1) (b, lx))
         in Hp as [q [Hq Hfq]].
  destruct q as [a la].
  injection Hfq as Hf _.
  exists a.
  split.
  - apply (proj2 (has_agent_In A N1 a)).
    apply (In_map fst (nt_agents N1) (a, la)).
    exact Hq.
  - exact Hf.
Qed.

(**************************************************************************)
(** ** The inverse of an isomorphism map *)

(** The largest agent id occurring in [N]'s agent list; [max_agent_id N + 1]
    is therefore an id that is not an agent of [N]. Used to define the
    inverse of an isomorphism map outside the agent sets. *)
Definition max_agent_id (A : Type) (N : Net A) : nat :=
  list_max (map fst (nt_agents N)).

(** Transitivity of [<=] on [nat]. *)
Lemma nat_le_trans (a b c : nat) : a <= b -> b <= c -> a <= c.
Proof.
  intros H1 H2. induction H2 as [|c' Hc' IH].
  - exact H1.
  - apply (le_S a c'). exact IH.
Qed.

(** An element of a list is at most its [list_max]. *)
Lemma list_max_upper_bound (l : list nat) (x : nat) :
  In x l -> x <= list_max l.
Proof.
  induction l as [|h t IH]; intros Hx.
  - simpl in Hx. inversion Hx.
  - simpl in Hx. destruct Hx as [Hx|Hx].
    + subst x. simpl. apply Nat.le_max_l.
    + apply (nat_le_trans x (list_max t) (list_max (h :: t))).
      * apply IH. exact Hx.
      * simpl. apply Nat.le_max_r.
Qed.

(** [max_agent_id A N + 1] is not an agent id of [N]. *)
Lemma max_agent_id_notin (A : Type) (N : Net A) :
  ~ has_agent A N (max_agent_id A N + 1).
Proof.
  intros H.
  apply (proj1 (has_agent_In A N (max_agent_id A N + 1))) in H.
  specialize (list_max_upper_bound (map fst (nt_agents N)) (max_agent_id A N + 1) H) as Hle.
  unfold max_agent_id in Hle.
  exfalso. lia.
Qed.

(** For [b] an agent of [N2], the preimage of [b] under [f] in [N1]'s agent
    set exists and is unique. *)
Lemma net_iso_preimage_unique (A : Type) (Ar : A -> nat) (N1 N2 : Net A)
      (f : nat -> nat)
      (Hfwd : forall a, has_agent A N1 a -> has_agent A N2 (f a))
      (Hinje : forall a1 a2,
                 has_agent A N1 a1 -> has_agent A N1 a2
                 -> f a1 = f a2 -> a1 = a2)
      (Hsurj : forall b,
                 has_agent A N2 b -> exists a, has_agent A N1 a /\ f a = b)
      (b : nat) (Hb : has_agent A N2 b) :
  exists! a, has_agent A N1 a /\ f a = b.
Proof.
  destruct (Hsurj b Hb) as [a0 [Ha0 Hf0]].
  refine (ex_intro _ a0 _).
  split.
  - exact (conj Ha0 Hf0).
  - intros a1 H1.
    destruct H1 as [Ha1 Hf1].
    symmetry.
    exact (Hinje a1 a0 Ha1 Ha0 (eq_trans Hf1 (eq_sym Hf0))).
Qed.

(** The inverse of an isomorphism map [f] between the agent sets of [N1] and
    [N2]: for [b] an agent of [N2], the unique agent [a] of [N1] with
    [f a = b]; for [b] outside [N2]'s agent set, an id outside [N1]'s agent
    set (so the result still respects the agent sets). The case split uses
    [excluded_middle_informative] (a [Type]-valued sum) rather than [classic]
    ([Prop]-valued), because the result is a [nat] and [Prop] cannot be
    eliminated to build one. *)
Definition net_iso_inv_map (A : Type) (Ar : A -> nat) (N1 N2 : Net A)
      (f : nat -> nat)
      (Hfwd : forall a, has_agent A N1 a -> has_agent A N2 (f a))
      (Hinje : forall a1 a2,
                 has_agent A N1 a1 -> has_agent A N1 a2
                 -> f a1 = f a2 -> a1 = a2)
      (Hsurj : forall b,
                 has_agent A N2 b -> exists a, has_agent A N1 a /\ f a = b)
      (b : nat) : nat :=
  match excluded_middle_informative (has_agent A N2 b) with
  | left Hb =>
    proj1_sig (constructive_definite_description
               (fun a => has_agent A N1 a /\ f a = b)
               (net_iso_preimage_unique A Ar N1 N2 f Hfwd Hinje Hsurj b Hb))
  | right _ =>
    max_agent_id A N1 + 1
  end.

(** On agents of [N2], the inverse map lands in [N1]'s agent set and [f]
    restores [b]. *)
Lemma net_iso_inv_map_spec (A : Type) (Ar : A -> nat) (N1 N2 : Net A)
      (f : nat -> nat)
      (Hfwd : forall a, has_agent A N1 a -> has_agent A N2 (f a))
      (Hinje : forall a1 a2,
                 has_agent A N1 a1 -> has_agent A N1 a2
                 -> f a1 = f a2 -> a1 = a2)
      (Hsurj : forall b,
                 has_agent A N2 b -> exists a, has_agent A N1 a /\ f a = b)
      (b : nat) (Hb : has_agent A N2 b) :
  has_agent A N1 (net_iso_inv_map A Ar N1 N2 f Hfwd Hinje Hsurj b)
  /\ f (net_iso_inv_map A Ar N1 N2 f Hfwd Hinje Hsurj b) = b.
Proof.
  unfold net_iso_inv_map.
  destruct (excluded_middle_informative (has_agent A N2 b)) as [Hb'|Hb'].
  - exact (proj2_sig (constructive_definite_description _
         (net_iso_preimage_unique A Ar N1 N2 f Hfwd Hinje Hsurj b Hb'))).
  - exfalso. apply Hb'. exact Hb.
Qed.

(**************************************************************************)
(** ** net_iso is an equivalence (on well-formed nets) *)

(** [net_iso] is reflexive. *)
Lemma net_iso_reflexive (A : Type) (Ar : A -> nat) (N : Net A) :
  net_iso A Ar N N.
Proof.
  refine (mkNetIso (fun a : nat => a) _ _ _).
  - simpl.
    assert (Heq : map (fun p : nat * A => (fst p, snd p)) (nt_agents N)
                   = nt_agents N).
    { apply map_id_on_elements.
      intros p _. destruct p as [a la]. reflexivity. }
    rewrite Heq. apply Permutation_refl.
  - intros a1 a2 _ _ Heq. simpl in Heq. exact Heq.
  - change (Permutation (map (fun l : port_ref * port_ref =>
                              ((fst (fst l), snd (fst l)),
                               (fst (snd l), snd (snd l))))
                             (nt_links N)) (nt_links N)).
    assert (Heq : map (fun l : port_ref * port_ref =>
                        ((fst (fst l), snd (fst l)),
                         (fst (snd l), snd (snd l))))
                   (nt_links N) = nt_links N).
    { apply map_id_on_elements.
      intros l _. destruct l as [[a p] [b q]]. reflexivity. }
    rewrite Heq. apply Permutation_refl.
Qed.

(** [net_iso] is transitive. *)
Lemma net_iso_transitive (A : Type) (Ar : A -> nat) (N1 N2 N3 : Net A)
      (H12 : net_iso A Ar N1 N2) (H23 : net_iso A Ar N2 N3) :
  net_iso A Ar N1 N3.
Proof.
  set (f := ni_map H12).
  set (g := ni_map H23).
  set (mapf := fun p : nat * A => (f (fst p), snd p)).
  set (mapg := fun p : nat * A => (g (fst p), snd p)).
  set (mapfg := fun p : nat * A => (g (f (fst p)), snd p)).
  set (imgf := fun l : (nat * nat) * (nat * nat) =>
                 ((f (fst (fst l)), snd (fst l)), (f (fst (snd l)), snd (snd l)))).
  set (imgg := fun l : (nat * nat) * (nat * nat) =>
                 ((g (fst (fst l)), snd (fst l)), (g (fst (snd l)), snd (snd l)))).
  set (imgfg := fun l : (nat * nat) * (nat * nat) =>
                  ((g (f (fst (fst l))), snd (fst l)),
                   (g (f (fst (snd l))), snd (snd l)))).
  refine (mkNetIso (fun a => g (f a)) _ _ _).
  - (* ni_agents *)
    change (Permutation (map mapfg (nt_agents N1)) (nt_agents N3)).
    assert (Heq : map mapfg (nt_agents N1) = map mapg (map mapf (nt_agents N1))).
    { rewrite (map_comp mapg mapf (nt_agents N1)).
      f_equal. }
    rewrite Heq.
    apply (Permutation_trans (Permutation_map mapg (ni_agents H12))
                             (ni_agents H23)).
  - (* ni_inj *)
    intros a1 a2 Ha1 Ha2 Heq.
    apply (ni_inj H12 a1 a2 Ha1 Ha2).
    apply (ni_inj H23 (f a1) (f a2)
           (net_iso_agent_fwd A Ar N1 N2 H12 a1 Ha1)
           (net_iso_agent_fwd A Ar N1 N2 H12 a2 Ha2)) in Heq.
    exact Heq.
  - (* ni_links *)
    change (Permutation (map imgfg (nt_links N1)) (nt_links N3)).
    assert (Heq : map imgfg (nt_links N1) = map imgg (map imgf (nt_links N1))).
    { rewrite (map_comp imgg imgf (nt_links N1)).
      f_equal. }
    rewrite Heq.
    apply (Permutation_trans (Permutation_map imgg (ni_links H12))
                             (ni_links H23)).
Qed.

(** [net_iso] is symmetric on well-formed sources: the inverse of the
    renaming (constructed by [net_iso_inv_map]) witnesses the isomorphism in
    the other direction. The well-formedness of [N1] is used to ensure the
    link endpoints are agents, so that the inverse map acts as a true inverse
    on them. *)
Lemma net_iso_symmetric (A : Type) (Ar : A -> nat) (N1 N2 : Net A)
      (H : net_iso A Ar N1 N2) (Hwf : well_formed A Ar N1) :
  net_iso A Ar N2 N1.
Proof.
  set (f := ni_map H).
  set (Hfwd := fun a : nat => net_iso_agent_fwd A Ar N1 N2 H a).
  set (Hsurj := fun b : nat => net_iso_surj A Ar N1 N2 H b).
  set (g := net_iso_inv_map A Ar N1 N2 f Hfwd (ni_inj H) Hsurj).
  set (agf := fun p : nat * A => (f (fst p), snd p)).
  set (agg := fun p : nat * A => (g (fst p), snd p)).
  set (imgf := fun l : (nat * nat) * (nat * nat) =>
                 ((f (fst (fst l)), snd (fst l)), (f (fst (snd l)), snd (snd l)))).
  set (imgg := fun l : (nat * nat) * (nat * nat) =>
                 ((g (fst (fst l)), snd (fst l)), (g (fst (snd l)), snd (snd l)))).
  refine (mkNetIso g _ _ _).
  - (* ni_agents: Permutation (map agg (nt_agents N2)) (nt_agents N1) *)
    assert (Hcomp : forall p, In p (nt_agents N1) -> (g (f (fst p)), snd p) = p).
    { intros p Hp.
      destruct p as [a la].
      change ((g (f a), la) = (a, la)).
      assert (Ha : has_agent A N1 a).
      { apply (proj2 (has_agent_In A N1 a)).
        apply (In_map fst (nt_agents N1) (a, la)).
        exact Hp. }
      assert (Hfa : has_agent A N2 (f a)).
      { exact (net_iso_agent_fwd A Ar N1 N2 H a Ha). }
      pose proof (net_iso_inv_map_spec A Ar N1 N2 f Hfwd (ni_inj H) Hsurj (f a) Hfa) as Hspec.
      assert (Hga : g (f a) = a).
      { apply (ni_inj H (g (f a)) a).
        - exact (proj1 Hspec).
        - exact Ha.
        - exact (proj2 Hspec). }
      f_equal. exact Hga. }
    change (Permutation (map agg (nt_agents N2)) (nt_agents N1)).
    assert (Hmc : map agg (map agf (nt_agents N1)) = nt_agents N1).
    { rewrite (map_comp agg agf (nt_agents N1)).
      apply map_id_on_elements.
      intros p Hp. exact (Hcomp p Hp). }
    rewrite <- Hmc.
    exact (Permutation_sym (Permutation_map agg (ni_agents H))).
  - (* ni_inj *)
    intros b1 b2 Hb1 Hb2 Heq.
    pose proof (net_iso_inv_map_spec A Ar N1 N2 f Hfwd (ni_inj H) Hsurj b1 Hb1) as Hs1.
    pose proof (net_iso_inv_map_spec A Ar N1 N2 f Hfwd (ni_inj H) Hsurj b2 Hb2) as Hs2.
    rewrite <- (proj2 Hs1).
    rewrite <- (proj2 Hs2).
    f_equal. exact Heq.
  - (* ni_links: Permutation (map imgg (nt_links N2)) (nt_links N1) *)
    assert (Hcomp : forall l, In l (nt_links N1) -> imgg (imgf l) = l).
    { intros l Hl.
      destruct l as [[a p] [b q]].
      destruct (wf_links Hwf a b p q Hl) as [Ha [Hb _]].
      assert (Hfa : has_agent A N2 (f a)).
      { exact (net_iso_agent_fwd A Ar N1 N2 H a Ha). }
      assert (Hfb : has_agent A N2 (f b)).
      { exact (net_iso_agent_fwd A Ar N1 N2 H b Hb). }
      pose proof (net_iso_inv_map_spec A Ar N1 N2 f Hfwd (ni_inj H) Hsurj (f a) Hfa) as Hsa.
      pose proof (net_iso_inv_map_spec A Ar N1 N2 f Hfwd (ni_inj H) Hsurj (f b) Hfb) as Hsb.
      assert (Hga : g (f a) = a).
      { apply (ni_inj H (g (f a)) a).
        - exact (proj1 Hsa).
        - exact Ha.
        - exact (proj2 Hsa). }
      assert (Hgb : g (f b) = b).
      { apply (ni_inj H (g (f b)) b).
        - exact (proj1 Hsb).
        - exact Hb.
        - exact (proj2 Hsb). }
      assert (H1 : (g (f a), p) = (a, p)).
      { f_equal. exact Hga. }
      assert (H2 : (g (f b), q) = (b, q)).
      { f_equal. exact Hgb. }
      change (((g (f a), p), (g (f b), q)) = ((a, p), (b, q))).
      f_equal.
      + exact H1.
      + exact H2. }
    change (Permutation (map imgg (nt_links N2)) (nt_links N1)).
    assert (Hmc : map imgg (map imgf (nt_links N1)) = nt_links N1).
    { rewrite (map_comp imgg imgf (nt_links N1)).
      apply map_id_on_elements.
      intros l Hl. exact (Hcomp l Hl). }
    rewrite <- Hmc.
    exact (Permutation_sym (Permutation_map imgg (ni_links H))).
Qed.

(**************************************************************************)
(** ** Well-formed nets *)

(** A well-formed net: a [Net] bundled with its [well_formed] proof. This is
    the domain on which [net_iso] is an equivalence relation (see
    [net_iso_equivalence]): symmetry of [net_iso] requires the source to be
    well-formed ([net_iso_symmetric]), so the equivalence is registered over
    well-formed nets rather than over all nets. *)
Record WfNet (A : Type) (Ar : A -> nat) := mkWfNet {
  wfn_net : Net A;
  wfn_well_formed : well_formed A Ar wfn_net
}.

(* The parameters [A], [Ar] are recoverable from a [WfNet], so make them
   implicit in the projections: [wfn_net N], [wfn_well_formed N] read
   naturally. *)
Arguments wfn_net {A Ar} _.
Arguments wfn_well_formed {A Ar} _.
Arguments mkWfNet {A Ar} _ _.

(**************************************************************************)
(** ** net_iso is an equivalence (on well-formed nets) *)

(** [net_iso] is an equivalence relation on well-formed nets: it is reflexive
    and transitive on all nets, and symmetric when the source is well-formed
    ([net_iso_symmetric]). The [Equivalence] class carries all three
    properties, so the instance is registered over [WfNet] (the subtype of
    well-formed nets), where symmetry is available. *)

(** The [Prop]-valued form of [net_iso] on well-formed nets. The [net_iso]
    record itself lives in [Set] (it carries the map [ni_map : nat -> nat]),
    while [Equivalence] requires a [Prop]-valued relation; this definition
    states the same three clauses with the map existentially quantified.
    [net_iso_to_on_wfnet] translates the record form to this one. The reverse
    direction is not a standalone lemma (the witness map cannot be extracted
    from a [Prop] existential into a [Set] record), but it is used internally
    in [net_iso_equivalence], where the goal is [Prop] and the destructed
    witness map can be rebuilt into a record. *)
Definition net_iso_on_wfnet (A : Type) (Ar : A -> nat) (N1 N2 : WfNet A Ar) : Prop :=
  exists (f : nat -> nat),
    Permutation (map (fun p => (f (fst p), snd p)) (nt_agents (wfn_net N1)))
                (nt_agents (wfn_net N2))
    /\ (forall a1 a2,
         has_agent A (wfn_net N1) a1 -> has_agent A (wfn_net N1) a2
         -> f a1 = f a2 -> a1 = a2)
    /\ Permutation (map (fun l => ((f (fst (fst l)), snd (fst l)),
                                   (f (fst (snd l)), snd (snd l))))
                      (nt_links (wfn_net N1)))
                  (nt_links (wfn_net N2)).

(** The record form implies the [Prop] form: the witness map is [ni_map]. *)
Lemma net_iso_to_on_wfnet (A : Type) (Ar : A -> nat) (N1 N2 : WfNet A Ar)
      (H : net_iso A Ar (wfn_net N1) (wfn_net N2)) :
  net_iso_on_wfnet A Ar N1 N2.
Proof.
  exists (ni_map H).
  split.
  - exact (ni_agents H).
  - split.
    + exact (ni_inj H).
    + exact (ni_links H).
Qed.

(** The [Equivalence] instance for [net_iso_on_wfnet]: [net_iso] is
    reflexive, symmetric, and transitive on well-formed nets. *)
Instance net_iso_equivalence (A : Type) (Ar : A -> nat) :
  Equivalence (net_iso_on_wfnet A Ar).
Proof.
  split.
  - (* reflexive: the identity map. *)
    intros N.
    apply (net_iso_to_on_wfnet A Ar N N).
    apply (net_iso_reflexive A Ar (wfn_net N)).
  - (* symmetric: unpack the witness map, rebuild the record, and apply
       [net_iso_symmetric] (which needs the source well-formed). The goal is
       [Prop], so destructing the existential is a legal elimination. *)
    intros N1 N2 H.
    destruct H as [f [Ha [Hi Hl]]].
    assert (Hrec : net_iso A Ar (wfn_net N1) (wfn_net N2)).
    { refine (mkNetIso f _ _ _).
      - exact Ha.
      - exact Hi.
      - exact Hl. }
    apply (net_iso_to_on_wfnet A Ar N2 N1).
    apply (net_iso_symmetric A Ar (wfn_net N1) (wfn_net N2) Hrec).
    exact (wfn_well_formed N1).
  - (* transitive: unpack both witness maps and rebuild both records. *)
    intros N1 N2 N3 H12 H23.
    destruct H12 as [f12 [Ha12 [Hi12 Hl12]]].
    destruct H23 as [f23 [Ha23 [Hi23 Hl23]]].
    assert (Hrec12 : net_iso A Ar (wfn_net N1) (wfn_net N2)).
    { refine (mkNetIso f12 _ _ _).
      - exact Ha12.
      - exact Hi12.
      - exact Hl12. }
    assert (Hrec23 : net_iso A Ar (wfn_net N2) (wfn_net N3)).
    { refine (mkNetIso f23 _ _ _).
      - exact Ha23.
      - exact Hi23.
      - exact Hl23. }
    apply (net_iso_to_on_wfnet A Ar N1 N3).
    apply (net_iso_transitive A Ar (wfn_net N1) (wfn_net N2) (wfn_net N3)
           Hrec12 Hrec23).
Qed.

(**************************************************************************)
(** ** Label and port preservation under an isomorphism *)

(** [net_iso] preserves agent labels: for an agent [a] of [N1], the label of
    [ni_map H a] in [N2] is the label of [a] in [N1]. The well-formedness of
    [N1] (unique agent ids) is what makes the label well-defined and lets the
    argument go through: any occurrence of the id [ni_map H a] in [N2]'s
    agent list is the image of the unique occurrence of [a] in [N1]'s. *)
Lemma net_iso_label (A : Type) (Ar : A -> nat) (N1 N2 : Net A)
      (H : net_iso A Ar N1 N2) (Hwf : well_formed A Ar N1)
      (a : nat) (Ha : has_agent A N1 a) :
  agent_label A N2 (ni_map H a) = agent_label A N1 a.
Proof.
  set (f := ni_map H).
  set (agentmap := fun p : nat * A => (f (fst p), snd p)).
  destruct (agent_label A N1 a) as [la|] eqn:Hlook.
  - (* Hlook : agent_label N1 a = Some la; the goal is already
       [agent_label N2 (f a) = Some la] (the destructed term was rewritten). *)
    assert (Hagent : In (a, la) (nt_agents N1)).
    { exact (agent_label_Some_In A N1 a la Hlook). }
    assert (Himg : In (f a, la) (map agentmap (nt_agents N1))).
    { apply (In_map agentmap (nt_agents N1) (a, la)). exact Hagent. }
    assert (Hn2 : In (f a, la) (nt_agents N2)).
    { apply (Permutation_in _ (ni_agents H)) in Himg. exact Himg. }
    apply (agent_label_lookup_In A (f a) (nt_agents N2) la Hn2).
    intros l1 l2 H1 H2.
    apply (Permutation_in _ (Permutation_sym (ni_agents H))) in H1.
    apply (Permutation_in _ (Permutation_sym (ni_agents H))) in H2.
    apply In_map_inv in H1 as [p1 [Hp1 Hf1]].
    apply In_map_inv in H2 as [p2 [Hp2 Hf2]].
    destruct p1 as [a1 la1].
    destruct p2 as [a2 la2].
    injection Hf1 as Hf1a Hf1l.
    injection Hf2 as Hf2a Hf2l.
    subst l1 l2.
    assert (Ha1 : has_agent A N1 a1).
    { apply (proj2 (has_agent_In A N1 a1)).
      apply (In_map fst (nt_agents N1) (a1, la1)).
      exact Hp1. }
    assert (Ha2 : has_agent A N1 a2).
    { apply (proj2 (has_agent_In A N1 a2)).
      apply (In_map fst (nt_agents N1) (a2, la2)).
      exact Hp2. }
    assert (Heq1 : a1 = a).
    { exact (ni_inj H a1 a Ha1 Ha Hf1a). }
    assert (Heq2 : a2 = a).
    { exact (ni_inj H a2 a Ha2 Ha Hf2a). }
    subst a1 a2.
    exact (wf_ids_functional Hwf a la1 la2 Hp1 Hp2).
  - (* Hlook : agent_label N1 a = None: impossible, [a] is an agent of [N1]. *)
    exfalso.
    apply Ha.
    exact Hlook.
Qed.

(** [net_iso] preserves port usage: for an agent [a] of [N1], the port [p] is
    an end of some link of [N1] iff it is an end of some link of [N2] at agent
    [ni_map H a]. The forward direction follows a link of [N1] to its image in
    [N2]; the backward direction pulls a link of [N2] back to its unique
    preimage in [N1] (the link map is injective on the links of a well-formed
    [N1], by [ni_inj] on the link endpoints, which [wf_links] guarantees are
    agents). *)
Lemma net_iso_port_used (A : Type) (Ar : A -> nat) (N1 N2 : Net A)
      (H : net_iso A Ar N1 N2) (Hwf : well_formed A Ar N1)
      (a : nat) (Ha : has_agent A N1 a) (p : nat) :
  port_used A N1 (a, p) <-> port_used A N2 (ni_map H a, p).
Proof.
  set (f := ni_map H).
  set (imgf := fun l : (nat * nat) * (nat * nat) =>
                 ((f (fst (fst l)), snd (fst l)),
                  (f (fst (snd l)), snd (snd l)))).
  split.
  - (* forward: a link of [N1] ending at (a,p) maps to a link of [N2]
       ending at (f a, p). *)
    intro Hpu1.
    destruct Hpu1 as [l1 [Hl1 Hle1]].
    exists (imgf l1).
    split.
    + apply (Permutation_in _ (ni_links H)).
      apply (In_map imgf (nt_links N1) l1).
      exact Hl1.
    + destruct l1 as [[a1 p1] [b1 q1]].
      destruct Hle1 as [Hle1|Hle1].
      * (* fst l1 = (a, p) *)
        injection Hle1 as Hap Hpp.
        subst a1 p1.
        left.
        reflexivity.
      * (* snd l1 = (a, p) *)
        injection Hle1 as Hap Hpp.
        subst b1 q1.
        right.
        reflexivity.
  - (* backward: a link of [N2] ending at (f a, p) has a unique preimage link
       of [N1] ending at (a, p). *)
    intro Hpu2.
    destruct Hpu2 as [l2 [Hl2 Hle2]].
    apply (Permutation_in _ (Permutation_sym (ni_links H))) in Hl2.
    apply In_map_inv in Hl2 as [l1 [Hl1 Hle1]].
    subst l2.
    destruct l1 as [[a1 p1] [b1 q1]].
    destruct Hle2 as [Hle2|Hle2].
    * (* (f a, p) = (f a1, p1) *)
      injection Hle2 as Hfa Hpa.
      subst p.
      assert (Ha1 : has_agent A N1 a1).
      { destruct (wf_links Hwf a1 b1 p1 q1 Hl1) as [Ha1 _]. exact Ha1. }
      assert (Heq : a = a1).
      { exact (ni_inj H a a1 Ha Ha1 (eq_sym Hfa)). }
      exists ((a1, p1), (b1, q1)).
      split.
      + exact Hl1.
      + subst a1.
        left.
        reflexivity.
    * (* (f a, p) = (f b1, q1) *)
      injection Hle2 as Hfa Hpa.
      subst p.
      assert (Hb1 : has_agent A N1 b1).
      { destruct (wf_links Hwf a1 b1 p1 q1 Hl1) as [_ [Hb1 _]]. exact Hb1. }
      assert (Heq : a = b1).
      { exact (ni_inj H a b1 Ha Hb1 (eq_sym Hfa)). }
      exists ((a1, p1), (b1, q1)).
      split.
      + exact Hl1.
      + subst b1.
        right.
        reflexivity.
Qed.

(** [net_iso] preserves freeness of ports: for an agent [a] of [N1] and any
    port [p], [p] is a free port of [a] in [N1] iff it is a free port of
    [ni_map H a] in [N2]. The three ingredients of [is_free] are each carried
    over: the label ([net_iso_label]), the arity bound (the same label), and
    port usage ([net_iso_port_used]). This is the core fact behind
    [net_iso_pres_interface]. *)
Lemma net_iso_is_free (A : Type) (Ar : A -> nat) (N1 N2 : Net A)
      (H : net_iso A Ar N1 N2) (Hwf : well_formed A Ar N1)
      (a : nat) (Ha : has_agent A N1 a) (p : nat) :
  is_free A Ar N1 (a, p) <-> is_free A Ar N2 (ni_map H a, p).
Proof.
  set (f := ni_map H).
  split.
  - (* forward *)
    intro Hf1.
    destruct Hf1 as [la [Hal [Hrange Hpu]]].
    exists la.
    split.
    + rewrite <- Hal.
      exact (net_iso_label A Ar N1 N2 H Hwf a Ha).
    + split.
      * exact Hrange.
      * intro Hpu2.
        apply Hpu.
        exact (proj2 (net_iso_port_used A Ar N1 N2 H Hwf a Ha p) Hpu2).
  - (* backward *)
    intro Hf2.
    destruct Hf2 as [la [Hal [Hrange Hpu]]].
    exists la.
    split.
    + change (agent_label A N1 a = Some la).
      rewrite <- (net_iso_label A Ar N1 N2 H Hwf a Ha).
      exact Hal.
    + split.
      * exact Hrange.
      * intro Hpu1.
        apply Hpu.
        exact (proj1 (net_iso_port_used A Ar N1 N2 H Hwf a Ha p) Hpu1).
Qed.

(**************************************************************************)
(** ** Preservation of well-formedness, active pairs, and the interface *)

(** A well-formed net is mapped to a well-formed net by an isomorphism: each
    of the four well-formedness conditions is carried along by the agent and
    link permutations. Unique ids survive because [ni_map] is injective on the
    source agent set ([ni_inj]); valid links survive because a link of [N2]
    pulls back to a valid link of [N1]; port-injectivity and distinct ends
    survive because the link map is a bijection on the links of a well-formed
    net. (§4.2: the net invariants are invariant under renaming.) *)
Lemma net_iso_pres_wf (A : Type) (Ar : A -> nat) (N1 N2 : Net A)
      (H : net_iso A Ar N1 N2) (Hwf : well_formed A Ar N1) :
  well_formed A Ar N2.
Proof.
  set (f := ni_map H).
  set (agentmap := fun p : nat * A => (f (fst p), snd p)).
  set (imgf := fun l : (nat * nat) * (nat * nat) =>
                 ((f (fst (fst l)), snd (fst l)),
                  (f (fst (snd l)), snd (snd l)))).
  refine (mkWellFormed A Ar N2 _ _ _ _).
  - (* wf_ids: NoDup (map fst (nt_agents N2)) *)
    assert (Hperm : Permutation (map (fun p : nat * A => f (fst p)) (nt_agents N1))
                                 (map fst (nt_agents N2))).
    { assert (Heq : map (fun p : nat * A => fst p) (map agentmap (nt_agents N1))
                       = map (fun p : nat * A => f (fst p)) (nt_agents N1)).
      { now rewrite (map_comp (fun p : nat * A => fst p) agentmap (nt_agents N1)). }
      rewrite <- Heq.
      apply (Permutation_map (fun p : nat * A => fst p) (ni_agents H)). }
    apply (Permutation_NoDup Hperm).
    rewrite <- (map_comp f fst (nt_agents N1)).
    apply Injective_map_NoDup_in.
    + intros x y Hx Hy Hf.
      assert (Hax : has_agent A N1 x).
      { apply (proj2 (has_agent_In A N1 x)). exact Hx. }
      assert (Hay : has_agent A N1 y).
      { apply (proj2 (has_agent_In A N1 y)). exact Hy. }
      exact (ni_inj H x y Hax Hay Hf).
    + exact (wf_ids Hwf).
  - (* wf_links *)
    intros a b p q Hl.
    apply (Permutation_in _ (Permutation_sym (ni_links H))) in Hl.
    apply In_map_inv in Hl as [l [Hl1 Hle]].
    destruct l as [[a1 p1] [b1 q1]].
    change (((f a1, p1), (f b1, q1)) = (a, p, (b, q))) in Hle.
    inversion Hle.
    destruct (wf_links Hwf a1 b1 p1 q1 Hl1) as [Ha1 [Hb1 Hbounds]].
    split.
    + exact (net_iso_agent_fwd A Ar N1 N2 H a1 Ha1).
    + split.
      * exact (net_iso_agent_fwd A Ar N1 N2 H b1 Hb1).
      * intros la lb Hal Halb.
        change (agent_label A N2 (ni_map H a1) = Some la) in Hal.
        change (agent_label A N2 (ni_map H b1) = Some lb) in Halb.
        assert (Hla : agent_label A N1 a1 = Some la).
        { rewrite (net_iso_label A Ar N1 N2 H Hwf a1 Ha1) in Hal.
          exact Hal. }
        assert (Hlb : agent_label A N1 b1 = Some lb).
        { rewrite (net_iso_label A Ar N1 N2 H Hwf b1 Hb1) in Halb.
          exact Halb. }
        rewrite <- H2, <- H4.
        exact (Hbounds la lb Hla Hlb).
  - (* wf_ports *)
    intros pr l1 l2 Hl1 Hl2 Hneq.
    intro Hcontra.
    destruct Hcontra as [Hl1pr Hl2pr].
    apply (Permutation_in _ (Permutation_sym (ni_links H))) in Hl1.
    apply (Permutation_in _ (Permutation_sym (ni_links H))) in Hl2.
    apply In_map_inv in Hl1 as [l1' [Hl1' Hle1]].
    apply In_map_inv in Hl2 as [l2' [Hl2' Hle2]].
    destruct l1' as [[a1 p1] [b1 q1]].
    destruct l2' as [[a2 p2] [b2 q2]].
    subst l1 l2.
    assert (Ha1 : has_agent A N1 a1).
    { exact (proj1 (wf_link_agents A Ar N1 Hwf a1 b1 p1 q1 Hl1')). }
    assert (Hb1 : has_agent A N1 b1).
    { exact (proj2 (wf_link_agents A Ar N1 Hwf a1 b1 p1 q1 Hl1')). }
    assert (Ha2 : has_agent A N1 a2).
    { exact (proj1 (wf_link_agents A Ar N1 Hwf a2 b2 p2 q2 Hl2')). }
    assert (Hb2 : has_agent A N1 b2).
    { exact (proj2 (wf_link_agents A Ar N1 Hwf a2 b2 p2 q2 Hl2')). }
    assert (Hneq' : ((a1, p1), (b1, q1)) <> ((a2, p2), (b2, q2))).
    { intro Heq.
      exfalso.
      apply Hneq.
      change (imgf ((a1, p1), (b1, q1)) = imgf ((a2, p2), (b2, q2))).
      f_equal.
      exact Heq. }
    destruct Hl1pr as [Hl1pr|Hl1pr]; destruct Hl2pr as [Hl2pr|Hl2pr].
    + (* pr = (f a1, p1) = (f a2, p2) *)
      change ((f a1, p1) = pr) in Hl1pr.
      change ((f a2, p2) = pr) in Hl2pr.
      assert (Heq : (f a1, p1) = (f a2, p2)).
      { rewrite Hl1pr, <- Hl2pr. reflexivity. }
      injection Heq as Hfa Hpa.
      subst p2.
      assert (Heq' : a1 = a2).
      { exact (ni_inj H a1 a2 Ha1 Ha2 Hfa). }
      subst a2.
      exfalso.
      apply (wf_ports Hwf (a1, p1) ((a1, p1), (b1, q1)) ((a1, p1), (b2, q2))
                      Hl1' Hl2' Hneq').
      split; [left; reflexivity | left; reflexivity].
    + (* pr = (f a1, p1) = (f b2, q2) *)
      change ((f a1, p1) = pr) in Hl1pr.
      change ((f b2, q2) = pr) in Hl2pr.
      assert (Heq : (f a1, p1) = (f b2, q2)).
      { rewrite Hl1pr, <- Hl2pr. reflexivity. }
      injection Heq as Hfa Hpa.
      subst q2.
      assert (Heq' : a1 = b2).
      { exact (ni_inj H a1 b2 Ha1 Hb2 Hfa). }
      subst b2.
      exfalso.
      apply (wf_ports Hwf (a1, p1) ((a1, p1), (b1, q1)) ((a2, p2), (a1, p1))
                      Hl1' Hl2' Hneq').
      split; [left; reflexivity | right; reflexivity].
    + (* pr = (f b1, q1) = (f a2, p2) *)
      change ((f b1, q1) = pr) in Hl1pr.
      change ((f a2, p2) = pr) in Hl2pr.
      assert (Heq : (f b1, q1) = (f a2, p2)).
      { rewrite Hl1pr, <- Hl2pr. reflexivity. }
      injection Heq as Hfa Hqa.
      subst p2.
      assert (Heq' : b1 = a2).
      { exact (ni_inj H b1 a2 Hb1 Ha2 Hfa). }
      subst a2.
      exfalso.
      apply (wf_ports Hwf (b1, q1) ((a1, p1), (b1, q1)) ((b1, q1), (b2, q2))
                      Hl1' Hl2' Hneq').
      split; [right; reflexivity | left; reflexivity].
    + (* pr = (f b1, q1) = (f b2, q2) *)
      change ((f b1, q1) = pr) in Hl1pr.
      change ((f b2, q2) = pr) in Hl2pr.
      assert (Heq : (f b1, q1) = (f b2, q2)).
      { rewrite Hl1pr, <- Hl2pr. reflexivity. }
      injection Heq as Hfa Hqa.
      subst q2.
      assert (Heq' : b1 = b2).
      { exact (ni_inj H b1 b2 Hb1 Hb2 Hfa). }
      subst b2.
      exfalso.
      apply (wf_ports Hwf (b1, q1) ((a1, p1), (b1, q1)) ((a2, p2), (b1, q1))
                      Hl1' Hl2' Hneq').
      split; [right; reflexivity | right; reflexivity].
  - (* wf_ends *)
    intros l Hl.
    intro Heq.
    apply (Permutation_in _ (Permutation_sym (ni_links H))) in Hl.
    apply In_map_inv in Hl as [l1 [Hl1 Hle]].
    destruct l1 as [[a1 p1] [b1 q1]].
    subst l.
    injection Heq as Hfa Hpa.
    assert (Ha1 : has_agent A N1 a1).
    { exact (proj1 (wf_link_agents A Ar N1 Hwf a1 b1 p1 q1 Hl1)). }
    assert (Hb1 : has_agent A N1 b1).
    { exact (proj2 (wf_link_agents A Ar N1 Hwf a1 b1 p1 q1 Hl1)). }
    assert (Heq1 : a1 = b1).
    { exact (ni_inj H a1 b1 Ha1 Hb1 Hfa). }
    assert (Hends : (a1, p1) = (b1, q1)).
    { f_equal.
      + exact Heq1.
      + exact Hpa. }
    exfalso.
    apply (wf_ends Hwf ((a1, p1), (b1, q1)) Hl1).
    exact Hends.
Qed.

(** [net_iso] preserves active pairs: if [a] and [b] form an active pair in
    [N1], then their images form an active pair in [N2]. Distinctness survives
    by [ni_inj] (the images of two distinct agents of [N1] differ); the agent
    conditions survive by [net_iso_agent_fwd]; and the link between port 0 of
    [a] and port 0 of [b] is carried to the corresponding link of [N2] by the
    link permutation [ni_links]. (§4.3: reduction steps are preserved.) *)
Lemma net_iso_pres_active_pair (A : Type) (Ar : A -> nat) (N1 N2 : Net A)
      (H : net_iso A Ar N1 N2) (a b : nat) :
  is_active_pair A Ar N1 a b -> is_active_pair A Ar N2 (ni_map H a) (ni_map H b).
Proof.
  set (f := ni_map H).
  set (imgf := fun l : (nat * nat) * (nat * nat) =>
                 ((f (fst (fst l)), snd (fst l)),
                  (f (fst (snd l)), snd (snd l)))).
  intro Hap.
  destruct Hap as [Hneq [Haa [Hba Hablink]]].
  unfold is_active_pair.
  refine (conj _ (conj _ (conj _ _))).
  - (* f a <> f b: the images of two distinct agents of [N1] differ. *)
    intro Heq.
    apply Hneq.
    exact (ni_inj H a b Haa Hba Heq).
  - exact (net_iso_agent_fwd A Ar N1 N2 H a Haa).
  - exact (net_iso_agent_fwd A Ar N1 N2 H b Hba).
  - (* the link (a,0)-(b,0) of [N1] maps to the link (f a,0)-(f b,0) of [N2]. *)
    destruct Hablink as [Hl|Hl].
    + left.
      apply (Permutation_in _ (ni_links H)).
      apply (In_map imgf (nt_links N1) ((a, 0), (b, 0))).
      exact Hl.
    + right.
      apply (Permutation_in _ (ni_links H)).
      apply (In_map imgf (nt_links N1) ((b, 0), (a, 0))).
      exact Hl.
Qed.

(** [net_iso] preserves the interface: the free ports of [N1], with their agent
    ids renamed by [ni_map], are exactly the free ports of [N2] (as a
    [Permutation]). The forward direction sends a free port of [N1] to its
    image, which is free in [N2] by [net_iso_is_free]; the backward direction
    pulls a free port of [N2] back to the unique free port of [N1] mapping to
    it (surjectivity of [ni_map] on agents, [net_iso_surj]). Both interfaces
    are duplicate-free, so the elementwise inclusion yields a [Permutation].
    (§4.3: the observable boundary of the net is invariant under renaming.) *)
Lemma net_iso_pres_interface (A : Type) (Ar : A -> nat) (N1 N2 : Net A)
      (H : net_iso A Ar N1 N2) (Hwf : well_formed A Ar N1) :
  Permutation (map (fun pr : port_ref => (ni_map H (fst pr), snd pr))
                  (interface A Ar N1))
              (interface A Ar N2).
Proof.
  set (f := ni_map H).
  set (mapf := fun pr : port_ref => (f (fst pr), snd pr)).
  assert (Hwf2 : well_formed A Ar N2).
  { exact (net_iso_pres_wf A Ar N1 N2 H Hwf). }
  (* forward: a free port of [N1] maps to a free port of [N2]. *)
  assert (Hfwd : forall pr, In pr (interface A Ar N1) -> In (mapf pr) (interface A Ar N2)).
  { intros pr Hin.
    destruct pr as [a p].
    assert (Hfree : is_free A Ar N1 (a, p)).
    { exact (interface_free A Ar N1 Hwf (a, p) Hin). }
    destruct Hfree as [la [Hal Hrest]].
    destruct Hrest as [Hrange Hpu].
    assert (Ha : has_agent A N1 a).
    { unfold has_agent.
      intro Hnone.
      change (agent_label A N1 a = Some la) in Hal.
      rewrite Hal in Hnone.
      discriminate Hnone. }
    apply (free_in_interface A Ar N2 Hwf2 (f a, p)).
    apply (proj1 (net_iso_is_free A Ar N1 N2 H Hwf a Ha p)).
    exists la.
    split.
    + exact Hal.
    + split.
      * exact Hrange.
      * exact Hpu. }
  (* backward: a free port of [N2] is the image of a free port of [N1]. *)
  assert (Hbwd : forall pr, In pr (interface A Ar N2) ->
                         exists pr', In pr' (interface A Ar N1) /\ mapf pr' = pr).
  { intros pr Hin.
    assert (Hfree : is_free A Ar N2 pr).
    { exact (interface_free A Ar N2 Hwf2 pr Hin). }
    destruct Hfree as [la [Hal Hrest]].
    destruct Hrest as [Hrange Hpu].
    destruct pr as [b q].
    assert (Ha2 : has_agent A N2 b).
    { unfold has_agent.
      intro Hnone.
      change (agent_label A N2 b = Some la) in Hal.
      rewrite Hal in Hnone.
      discriminate Hnone. }
    destruct (net_iso_surj A Ar N1 N2 H b Ha2) as [a [Ha1 Heq]].
    change (f a = b) in Heq.
    exists (a, q).
    split.
    - (* (a, q) is a free port of [N1]. *)
      apply (free_in_interface A Ar N1 Hwf (a, q)).
      apply (proj2 (net_iso_is_free A Ar N1 N2 H Hwf a Ha1 q)).
      exists la.
      split.
      + change (agent_label A N2 (f a) = Some la).
        rewrite Heq.
        exact Hal.
      + split.
        * exact Hrange.
        * change (~ port_used A N2 (f a, q)).
          rewrite Heq.
          exact Hpu.
    - (* mapf (a, q) = (b, q). *)
      change ((f a, q) = (b, q)).
      rewrite Heq.
      reflexivity. }
  (* [mapf] is injective on the interface of [N1] (its agent ids are unique). *)
  assert (Hinj : forall x y, In x (interface A Ar N1) -> In y (interface A Ar N1) ->
                         mapf x = mapf y -> x = y).
  { intros x y Hx Hy Hmfeq.
    destruct x as [a1 p1].
    destruct y as [a2 p2].
    assert (Hfree1 : is_free A Ar N1 (a1, p1)).
    { exact (interface_free A Ar N1 Hwf (a1, p1) Hx). }
    assert (Hfree2 : is_free A Ar N1 (a2, p2)).
    { exact (interface_free A Ar N1 Hwf (a2, p2) Hy). }
    destruct Hfree1 as [la1 [Hal1 _]].
    destruct Hfree2 as [la2 [Hal2 _]].
    assert (Ha1 : has_agent A N1 a1).
    { unfold has_agent. intro Hn.
      change (agent_label A N1 a1 = Some la1) in Hal1.
      rewrite Hal1 in Hn. discriminate Hn. }
    assert (Ha2 : has_agent A N1 a2).
    { unfold has_agent. intro Hn.
      change (agent_label A N1 a2 = Some la2) in Hal2.
      rewrite Hal2 in Hn. discriminate Hn. }
    change ((f a1, p1) = (f a2, p2)) in Hmfeq.
    injection Hmfeq as Hfa Hpa.
    subst p2.
    assert (Heq : a1 = a2).
    { exact (ni_inj H a1 a2 Ha1 Ha2 Hfa). }
    subst a2.
    reflexivity. }
  (* the image list is duplicate-free. *)
  assert (Hnodupm : NoDup (map mapf (interface A Ar N1))).
  { apply Injective_map_NoDup_in.
    + exact Hinj.
    + exact (interface_nodup A Ar N1 Hwf). }
  (* both lists are duplicate-free and elementwise equivalent: a [Permutation]. *)
  apply NoDup_Permutation.
  - exact Hnodupm.
  - exact (interface_nodup A Ar N2 Hwf2).
  - intros y.
    split.
    + (* In y (map mapf (interface N1)) -> In y (interface N2) *)
      intro Hy.
      apply In_map_inv in Hy as [pr [Hpr Hye]].
      subst y.
      exact (Hfwd pr Hpr).
    + (* In y (interface N2) -> In y (map mapf (interface N1)) *)
      intro Hy.
      destruct (Hbwd y Hy) as [pr [Hpr Hye]].
      subst y.
      apply (In_map mapf (interface A Ar N1) pr).
      exact Hpr.
Qed.
