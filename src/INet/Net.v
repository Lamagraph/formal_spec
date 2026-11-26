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
