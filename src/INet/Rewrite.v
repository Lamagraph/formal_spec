(**
 * Rewrite — reduction on interaction nets.
 *
 * Defines the rewrite step ([raw_splice], [step]), its reflexive-transitive
 * closure [step_star], normal forms, and the confluence results (diamond,
 * confluence, unique normal forms), all stated modulo [net_iso].
 *
 * This module sits at the top of the [INet] stack in the
 * {@ docs/design.md} layout: it depends on [Net] and [Agent] and is depended
 * on by nothing inside [INet].
 *)

Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Lists.Finite.
Require Import Stdlib.Logic.Classical.
Require Import Stdlib.Sorting.Permutation.
Require Import Stdlib.micromega.Lia.
Require Import Net.
Require Import Agent.

(* [Net] opens [type_scope] globally, and that opens transitively here. In
   Rocq 9.3 the notation [/\] is declared only in [type_scope], so it must
   stay open; but an open [type_scope] makes the infix [+] resolve to a
   type-level operator rather than [Nat.add], which would break the
   freshening arithmetic below. Opening [nat_scope] afterwards restores [+]
   to [Nat.add] (later-opened scopes win), while [/\] remains available from
   [type_scope]. The product type [*] is unaffected: it appears in a type
   position, where it is interpreted as [prod] regardless of the open scopes. *)
Open Scope nat_scope.

(**************************************************************************)
(** ** Freshening *)

(** [fresh_id A N a] shifts an agent id [a] of the RHS above every agent id of
    [N]: the result is strictly greater than [max_agent_id A N], so the
    freshened ids are disjoint from [N]'s. This is the freshening scheme used
    by [raw_splice] (§4.5a). *)
Definition fresh_id (A : Type) (N : Net A) (a : nat) : nat :=
  max_agent_id A N + 1 + a.

(** [freshen_pr A N pr] freshens the agent component of a port reference,
    leaving the port number unchanged. *)
Definition freshen_pr (A : Type) (N : Net A) (pr : port_ref) : port_ref :=
  (fresh_id A N (fst pr), snd pr).

(**************************************************************************)
(** ** Endpoint rewiring *)

(** [is_main_main_link a1 a2 l] is [true] exactly when [l] is the main–main
    link between [a1] and [a2], in either orientation. This is the link that
    [raw_splice] removes. *)
Definition is_main_main_link (a1 a2 : nat) (l : port_ref * port_ref) : bool :=
  match l with
  | ((x, u), (y, v)) =>
      (Nat.eqb x a1 && Nat.eqb u 0 && Nat.eqb y a2 && Nat.eqb v 0)
      || (Nat.eqb x a2 && Nat.eqb u 0 && Nat.eqb y a1 && Nat.eqb v 0)
  end.

(** [rewire_endpoint A Ar N a1 a2 r e] redirects one endpoint [e] of a link of
    [N] according to the boundary convention of [raw_splice]:
    * if [e = (a1, p)] with [1 <= p <= Ar (fst (ru_lhs r))], it is replaced by
      the freshened RHS free port at boundary position [p - 1];
    * if [e = (a2, p)] with [1 <= p <= Ar (snd (ru_lhs r))], it is replaced by
      the freshened RHS free port at boundary position
      [Ar (fst (ru_lhs r)) + (p - 1)];
    * otherwise [e] is kept unchanged.

    The boundary position [i] (0-based) corresponds positionally to the
    [i]-th element of [ru_iface r] (the RHS interface). Out-of-range indices
    are impossible under the well-formedness and length premises of
    [raw_splice_wf]; the [nth] default keeps this Definition total. *)
Definition rewire_endpoint (A : Type) (Ar : A -> nat) (N : Net A) (a1 a2 : nat) (r : Rule A) (e : port_ref) : port_ref :=
  match e with
  | (x, p) =>
    if Nat.eqb x a1 then
      if Nat.leb 1 p && Nat.leb p (Ar (fst (ru_lhs r))) then
        freshen_pr A N (nth (p - 1) (ru_iface r) (0, 0))
      else e
    else if Nat.eqb x a2 then
      if Nat.leb 1 p && Nat.leb p (Ar (snd (ru_lhs r))) then
        freshen_pr A N (nth (Ar (fst (ru_lhs r)) + (p - 1)) (ru_iface r) (0, 0))
      else e
    else e
  end.

(** [rewire_link A Ar N a1 a2 r l] rewires both endpoints of the link [l]. *)
Definition rewire_link (A : Type) (Ar : A -> nat) (N : Net A) (a1 a2 : nat) (r : Rule A) (l : port_ref * port_ref) : port_ref * port_ref :=
  (rewire_endpoint A Ar N a1 a2 r (fst l), rewire_endpoint A Ar N a1 a2 r (snd l)).

(**************************************************************************)
(** ** The raw splice *)

(** The agents of [raw_splice A Ar N a1 a2 r]: the agents of [N] other than
    [a1] and [a2], followed by the freshened agents of the RHS of [r]. *)
Definition splice_agents (A : Type) (N : Net A) (a1 a2 : nat) (r : Rule A) : list (nat * A) :=
  filter (fun p => negb (Nat.eqb (fst p) a1) && negb (Nat.eqb (fst p) a2)) (nt_agents N)
  ++ map (fun p => (fresh_id A N (fst p), snd p)) (nt_agents (ru_rhs r)).

(** The links of [raw_splice A Ar N a1 a2 r]: the links of [N] other than the
    main–main link, with their endpoints rewired, followed by the freshened
    links of the RHS of [r]. *)
Definition splice_links (A : Type) (Ar : A -> nat) (N : Net A) (a1 a2 : nat) (r : Rule A) : list (port_ref * port_ref) :=
  map (rewire_link A Ar N a1 a2 r)
      (filter (fun l => negb (is_main_main_link a1 a2 l)) (nt_links N))
  ++ map (fun l => (freshen_pr A N (fst l), freshen_pr A N (snd l))) (nt_links (ru_rhs r)).

(** [raw_splice A Ar N a1 a2 r] is the raw rewrite step on the net [N] at the
    active pair ([a1], [a2]) using the rule [r]: it removes the agents [a1]
    and [a2] and the main–main link between them, inserts the RHS of [r] with
    fresh agent ids (disjoint from [N]'s, by [fresh_id]), and rewires every
    link of [N] incident to a boundary port to the matching freshened RHS free
    port.

    **Orientation convention.** [a1] is the agent whose label is
    [fst (ru_lhs r)] and [a2] the agent whose label is [snd (ru_lhs r)].
    Callers enforce this ([step_intro] pins it with an explicit premise).

    **Boundary convention.** The boundary of the pair is the list of the aux
    ports of [a1] in port order [1 .. Ar (fst (ru_lhs r))], followed by the aux
    ports of [a2] in port order [1 .. Ar (snd (ru_lhs r))]. Its length is
    [Ar (fst (ru_lhs r)) + Ar (snd (ru_lhs r))] = [length (ru_iface r)] (by
    [sys_valid_len]), and position [i] (0-based) of the boundary corresponds
    positionally to the [i]-th element of [ru_iface r].

    The result is well-formed under the premises of [raw_splice_wf]. *)
Definition raw_splice (A : Type) (Ar : A -> nat) (N : Net A) (a1 a2 : nat) (r : Rule A) : Net A :=
  mkNet A (splice_agents A N a1 a2 r) (splice_links A Ar N a1 a2 r).

(**************************************************************************)
(** ** Freshening facts *)

(** A freshened id is strictly above every id of [N]. *)
Lemma fresh_id_gt_max (A : Type) (N : Net A) (a : nat) :
  max_agent_id A N < fresh_id A N a.
Proof.
  unfold fresh_id. lia.
Qed.

(** A freshened id is not an agent id of [N]. *)
Lemma fresh_id_notin_N (A : Type) (N : Net A) (a : nat) :
  ~ In (fresh_id A N a) (map fst (nt_agents N)).
Proof.
  intros H.
  set (M := list_max (map fst (nt_agents N))).
  specialize (list_max_upper_bound (map fst (nt_agents N)) (fresh_id A N a) H) as Hle.
  change (fresh_id A N a <= M) in Hle.
  unfold fresh_id, max_agent_id in Hle.
  lia.
Qed.

(** The freshening shift is injective. *)
Lemma fresh_id_inj (A : Type) (N : Net A) (a b : nat) :
  fresh_id A N a = fresh_id A N b -> a = b.
Proof.
  intros H. unfold fresh_id in H. lia.
Qed.

(** Freshening a port reference is injective. *)
Lemma freshen_pr_inj (A : Type) (N : Net A) (pr1 pr2 : port_ref) :
  freshen_pr A N pr1 = freshen_pr A N pr2 -> pr1 = pr2.
Proof.
  intros H.
  destruct pr1 as [x p]; destruct pr2 as [y q].
  unfold freshen_pr in H.
  injection H as H1 H2.
  subst q.
  apply (fresh_id_inj A N x y) in H1.
  subst y.
  reflexivity.
Qed.

(**************************************************************************)
(** ** Lookup on a concatenation *)

(** The left-to-right lookup in a concatenation: it is the lookup in the first
    list when that finds the id, and the lookup in the second list otherwise. *)
Lemma agent_label_lookup_app (A : Type) (a : nat) (l1 l2 : list (nat * A)) :
  agent_label_lookup A a (l1 ++ l2) =
    match agent_label_lookup A a l1 with
    | Some _ => agent_label_lookup A a l1
    | None => agent_label_lookup A a l2
    end.
Proof.
  induction l1 as [|(id, lbl) rest IH]; simpl.
  - reflexivity.
  - destruct (Nat.eqb id a) eqn:Hb.
    + apply (Nat.eqb_eq id a) in Hb. subst id.
      simpl. reflexivity.
    + simpl.
      rewrite IH.
      reflexivity.
Qed.

(** [negb (Nat.eqb a b) = true] exactly when [a <> b]. *)
Lemma negb_eqb_true (a b : nat) : negb (Nat.eqb a b) = true <-> a <> b.
Proof.
  split.
  - intro H. intro Heq. rewrite <- Heq in H.
    assert (Ht : Nat.eqb a a = true). { apply (proj2 (Nat.eqb_eq a a)). reflexivity. }
    rewrite Ht in H. simpl in H. discriminate H.
  - intro Hneq. destruct (Nat.eqb a b) eqn:Hb.
    + exfalso. apply Hneq. apply (proj1 (Nat.eqb_eq a b)). exact Hb.
    + simpl. reflexivity.
Qed.

(** If the id is absent from the list, the lookup returns [None]. *)
Lemma agent_label_lookup_None (A : Type) (a : nat) (l : list (nat * A)) :
  ~ In a (map fst l) -> agent_label_lookup A a l = None.
Proof.
  intros Hnot.
  destruct (agent_label_lookup A a l) as [x|] eqn:Hlook.
  - exfalso.
    apply Hnot.
    apply (In_map fst l (a, x)).
    exact (agent_label_lookup_Some_In A a l x Hlook).
  - reflexivity.
Qed.

(**************************************************************************)
(** ** Agent labels in the splice *)

(** The label of a freshened RHS agent in [raw_splice] is the label of the
    original agent in the RHS. *)
Lemma raw_splice_agent_label_fresh (A : Type) (Ar : A -> nat) (N : Net A) (a1 a2 : nat) (r : Rule A)
      (Hrhs : well_formed A Ar (ru_rhs r))
      (x : nat) (la : A) (Hx : In (x, la) (nt_agents (ru_rhs r))) :
  agent_label A (raw_splice A Ar N a1 a2 r) (fresh_id A N x) = Some la.
Proof.
  unfold agent_label, raw_splice.
  set (fresh := fun p : nat * A => (fresh_id A N (fst p), snd p)).
  change (agent_label_lookup A (fresh_id A N x)
            (splice_agents A N a1 a2 r) = Some la).
  unfold splice_agents.
  set (P := fun p : nat * A => negb (Nat.eqb (fst p) a1) && negb (Nat.eqb (fst p) a2)).
  change (agent_label_lookup A (fresh_id A N x)
            (filter P (nt_agents N) ++ map fresh (nt_agents (ru_rhs r))) = Some la).
  (* The freshened id is not in the filtered part of [N]'s agents. *)
  assert (Hnot : ~ In (fresh_id A N x) (map fst (filter P (nt_agents N)))).
  { intros H.
    apply (In_map_inv fst (filter P (nt_agents N)) (fresh_id A N x)) in H as [p [Hp Hfp]].
    apply (proj1 (filter_In P p (nt_agents N))) in Hp.
    destruct Hp as [Hp _].
    assert (Hmap : In (fst p) (map fst (nt_agents N))).
    { apply (In_map fst (nt_agents N) p). exact Hp. }
    rewrite Hfp in Hmap.
    apply (fresh_id_notin_N A N x).
    exact Hmap. }
  (* The lookup in the concatenation reduces to the lookup in the freshened
     RHS part (the id is absent from the filtered part). *)
  rewrite (agent_label_lookup_app A (fresh_id A N x) (filter P (nt_agents N))
                            (map fresh (nt_agents (ru_rhs r)))).
  (* The lookup in the filtered part is None (the freshened id is absent). *)
  assert (Hnone : agent_label_lookup A (fresh_id A N x) (filter P (nt_agents N)) = None).
  { exact (agent_label_lookup_None A (fresh_id A N x) (filter P (nt_agents N)) Hnot). }
  rewrite Hnone.
  simpl.
  (* The freshened agent (fresh_id A N x, la) is present in the freshened RHS
     part, and the part is functional on it (unique RHS ids + injective shift). *)
  apply (agent_label_lookup_In A (fresh_id A N x) (map fresh (nt_agents (ru_rhs r))) la).
  - (* In (fresh_id A N x, la) (map fresh (nt_agents (ru_rhs r))) *)
    apply (In_map fresh (nt_agents (ru_rhs r)) (x, la)).
    exact Hx.
  - (* functional on (fresh_id A N x) *)
    intros l1 l2 H1 H2.
    apply (In_map_inv fresh (nt_agents (ru_rhs r)) (fresh_id A N x, l1)) in H1 as [p1 [Hp1 Hf1]].
    apply (In_map_inv fresh (nt_agents (ru_rhs r)) (fresh_id A N x, l2)) in H2 as [p2 [Hp2 Hf2]].
    destruct p1 as [x1 la1]; destruct p2 as [x2 la2].
    unfold fresh in Hf1, Hf2.
    injection Hf1 as Hf1a Hf1l.
    injection Hf2 as Hf2a Hf2l.
    subst l1 l2.
    apply (fresh_id_inj A N x1 x) in Hf1a.
    apply (fresh_id_inj A N x2 x) in Hf2a.
    subst x1 x2.
    exact (wf_ids_functional Hrhs x la1 la2 Hp1 Hp2).
Qed.

(** The label of a kept agent (neither [a1] nor [a2]) in [raw_splice] is the
    same as in [N]. *)
Lemma raw_splice_agent_label_kept (A : Type) (Ar : A -> nat) (N : Net A) (a1 a2 : nat) (r : Rule A)
      (Hwf : well_formed A Ar N)
      (x : nat) (la : A)
      (Hx1 : x <> a1) (Hx2 : x <> a2)
      (Hlab : agent_label A N x = Some la) :
  agent_label A (raw_splice A Ar N a1 a2 r) x = Some la.
Proof.
  unfold agent_label, raw_splice.
  set (fresh := fun p : nat * A => (fresh_id A N (fst p), snd p)).
  change (agent_label_lookup A x (splice_agents A N a1 a2 r) = Some la).
  unfold splice_agents.
  set (P := fun p : nat * A => negb (Nat.eqb (fst p) a1) && negb (Nat.eqb (fst p) a2)).
  change (agent_label_lookup A x
            (filter P (nt_agents N) ++ map fresh (nt_agents (ru_rhs r))) = Some la).
  (* (x, la) is in the filtered part. *)
  assert (Hin : In (x, la) (filter P (nt_agents N))).
  { apply (proj2 (filter_In P (x, la) (nt_agents N))).
    split.
    - exact (agent_label_Some_In A N x la Hlab).
    - simpl.
      apply andb_true_iff.
      split.
      + apply (proj2 (negb_eqb_true x a1)). exact Hx1.
      + apply (proj2 (negb_eqb_true x a2)). exact Hx2. }
  (* The lookup in the filtered part is Some la. *)
  assert (Hlook : agent_label_lookup A x (filter P (nt_agents N)) = Some la).
  { apply (agent_label_lookup_In A x (filter P (nt_agents N)) la Hin).
    intros l1 l2 H1 H2.
    apply (wf_ids_functional Hwf x l1 l2).
    - apply (proj1 (filter_In P (x, l1) (nt_agents N))) in H1. destruct H1 as [H1' _]. exact H1'.
    - apply (proj1 (filter_In P (x, l2) (nt_agents N))) in H2. destruct H2 as [H2' _]. exact H2'. }
  (* x is not in the freshened RHS part. *)
  assert (Hnot : ~ In x (map fst (map fresh (nt_agents (ru_rhs r))))).
  { intros H.
    apply (In_map_inv fst (map fresh (nt_agents (ru_rhs r))) x) in H as [q [Hq Hqx]].
    apply (In_map_inv fresh (nt_agents (ru_rhs r)) q) in Hq as [p [Hp Hqp]].
    subst q.
    simpl in Hqx.
    apply (fresh_id_notin_N A N (fst p)).
    rewrite Hqx.
    apply (proj1 (has_agent_In A N x)).
    unfold has_agent.
    intro Hnone.
    rewrite Hlab in Hnone.
    discriminate Hnone. }
  (* The lookup in the concatenation is the lookup in the filtered part (the
     id is present there), which is Some la. *)
  rewrite (agent_label_lookup_app A x (filter P (nt_agents N))
                            (map fresh (nt_agents (ru_rhs r)))).
  change (match agent_label_lookup A x (filter P (nt_agents N)) with
          | Some _ => agent_label_lookup A x (filter P (nt_agents N))
          | None => agent_label_lookup A x (map fresh (nt_agents (ru_rhs r)))
          end = Some la).
  rewrite Hlook.
  simpl.
  reflexivity.
Qed.

(**************************************************************************)
(** ** List facts for the well-formedness proof *)

(** Mapping [fst] over a filter whose predicate depends only on [fst] commutes
    with filtering the id list: [map fst (filter (Q o fst) l)] is the id list
    [map fst l] filtered by [Q]. This lets [wf_ids] of the kept part of the
    splice be read off directly from [wf_ids] of [N] (via [NoDup_filter])
    without first showing the kept agent list is [NoDup] as a list of pairs. *)
Lemma map_fst_filter_fst (A : Type) (Q : nat -> bool) (l : list (nat * A)) :
  map fst (filter (fun p => Q (fst p)) l) = filter Q (map fst l).
Proof.
  induction l as [|(x, la) rest IH]; simpl.
  - reflexivity.
  - destruct (Q x) eqn:Hq.
    + simpl. f_equal. apply IH.
    + simpl. f_equal. apply IH.
Qed.

(** Unique ids as a list of pairs imply the pair list itself is [NoDup]: two
    equal pairs have equal ids, and a [NoDup] id list forbids a repeated id. *)
Lemma nodup_fst_nodup (A : Type) (l : list (nat * A)) :
  NoDup (map fst l) -> NoDup l.
Proof.
  induction l as [|(x, la) rest IH]; intros Hnd.
  - apply NoDup_nil.
  - apply NoDup_cons_iff.
    split.
    + (* ~ In (x, la) rest *)
      intros Hin.
      apply (NoDup_cons_notin nat x (map fst rest) Hnd).
      apply (In_map fst rest (x, la)).
      exact Hin.
    + (* NoDup rest *)
      apply IH.
      apply (NoDup_cons_nodup nat x (map fst rest) Hnd).
Qed.

(**************************************************************************)
(** ** The main port is used only by the main link *)

(** [is_main_main_link] recognizes the main–main link in either orientation. *)
Lemma is_main_main_link_pos (a1 a2 : nat) :
  is_main_main_link a1 a2 ((a1, 0), (a2, 0)) = true.
Proof.
  unfold is_main_main_link. simpl.
  apply (proj2 (orb_true_iff _ _)).
  left.
  repeat (
    try (apply (proj2 (andb_true_iff _ _)); split);
    try (apply (proj2 (Nat.eqb_eq _ _)); reflexivity);
    try reflexivity
  ).
Qed.

Lemma is_main_main_link_neg (a1 a2 : nat) :
  is_main_main_link a1 a2 ((a2, 0), (a1, 0)) = true.
Proof.
  unfold is_main_main_link. simpl.
  apply (proj2 (orb_true_iff _ _)).
  right.
  repeat (
    try (apply (proj2 (andb_true_iff _ _)); split);
    try (apply (proj2 (Nat.eqb_eq _ _)); reflexivity);
    try reflexivity
  ).
Qed.
(**************************************************************************)
(** ** The main port is used only by the main link *)

(** In a well-formed net with active pair ([a1], [a2]), the only link ending at
    a main port of the pair — [(a1, 0)] or [(a2, 0)] — is the main–main link.
    Port-injectivity ([link_unique]) forces any two links ending at the same
    port to share their other end, and the active pair supplies the main–main
    link as one such link. This is what makes every other link incident to [a1]
    (resp. [a2]) land on an auxiliary port in range, so that [raw_splice]
    rewires it. *)
Lemma main_port_only_main_link (A : Type) (Ar : A -> nat) (N : Net A) (a1 a2 : nat)
      (Hwf : well_formed A Ar N)
      (Hap : is_active_pair A Ar N a1 a2)
      (l : port_ref * port_ref)
      (Hl : In l (nt_links N))
      (m : port_ref)
      (Hm : m = (a1, 0) \/ m = (a2, 0))
      (He : link_end l m) :
  is_main_main_link a1 a2 l = true.
Proof.
  unfold is_active_pair in Hap.
  destruct Hap as [Hneq [Haa [Hba Hablink]]].
  (* The main–main link joins (a1,0) and (a2,0), in both orientations. *)
  assert (Hhe12 : has_link A N (a1, 0) (a2, 0)). { exact Hablink. }
  assert (Hhe21 : has_link A N (a2, 0) (a1, 0)).
  { exact (proj1 (has_link_sym A N (a1, 0) (a2, 0)) Hablink). }
  destruct Hm as [Hm|Hm].
  - (* m = (a1, 0) *)
    subst m.
    destruct He as [He|He].
    + (* fst l = (a1,0): l = ((a1,0),(b,q)). *)
      change (fst l = (a1, 0)) in He.
      destruct l as [[a p] [b q]].
      injection He as Ha Hpp. subst a p.
      assert (Hl1 : has_link A N (a1, 0) (b, q)).
      { left. exact Hl. }
      assert (Heq : (b, q) = (a2, 0)).
      { exact (link_unique A Ar N Hwf (a1, 0) (b, q) (a2, 0) Hl1 Hhe12). }
      injection Heq as Hb Hq. subst b q.
      change (is_main_main_link a1 a2 ((a1, 0), (a2, 0)) = true).
      exact (is_main_main_link_pos a1 a2).
    + (* snd l = (a1,0): l = ((b,q),(a1,0)). *)
      change (snd l = (a1, 0)) in He.
      destruct l as [[a p] [b q]].
      injection He as Hb Hqq. subst b q.
      assert (Hl1 : has_link A N (a1, 0) (a, p)).
      { right. exact Hl. }
      assert (Heq : (a, p) = (a2, 0)).
      { exact (link_unique A Ar N Hwf (a1, 0) (a, p) (a2, 0) Hl1 Hhe12). }
      injection Heq as Ha Hp. subst a p.
      change (is_main_main_link a1 a2 ((a2, 0), (a1, 0)) = true).
      exact (is_main_main_link_neg a1 a2).
  - (* m = (a2, 0) *)
    subst m.
    destruct He as [He|He].
    + (* fst l = (a2,0): l = ((a2,0),(b,q)). *)
      change (fst l = (a2, 0)) in He.
      destruct l as [[a p] [b q]].
      injection He as Ha Hpp. subst a p.
      assert (Hl1 : has_link A N (a2, 0) (b, q)).
      { left. exact Hl. }
      assert (Heq : (b, q) = (a1, 0)).
      { exact (link_unique A Ar N Hwf (a2, 0) (b, q) (a1, 0) Hl1 Hhe21). }
      injection Heq as Hb Hq. subst b q.
      change (is_main_main_link a1 a2 ((a2, 0), (a1, 0)) = true).
      exact (is_main_main_link_neg a1 a2).
    + (* snd l = (a2,0): l = ((b,q),(a2,0)). *)
      change (snd l = (a2, 0)) in He.
      destruct l as [[a p] [b q]].
      injection He as Hb Hqq. subst b q.
      assert (Hl1 : has_link A N (a2, 0) (a, p)).
      { right. exact Hl. }
      assert (Heq : (a, p) = (a1, 0)).
      { exact (link_unique A Ar N Hwf (a2, 0) (a, p) (a1, 0) Hl1 Hhe21). }
      injection Heq as Ha Hp. subst a p.
      change (is_main_main_link a1 a2 ((a1, 0), (a2, 0)) = true).
      exact (is_main_main_link_pos a1 a2).
Qed.

(**************************************************************************)
(** ** Characterizing [rewire_endpoint] *)

(** The three clauses of [rewire_endpoint], made explicit as equalities. These
    pin down exactly which port reference an endpoint is sent to, and are the
    computational backbone of the well-formedness proof: [rewire_endpoint_valid]
    (the rewired port is a valid splice port) and [rewire_endpoint_inj] (two
    distinct links do not rewire onto a shared port) both reduce to these.

    The proofs evaluate the nested [if]s: the agent test is decided by
    [Nat.eqb_eq] (or by [a1 <> a2] in the [a2] clause), and the port-range test
    by the [Nat.leb] premises. *)

(** An endpoint at [a1] on an in-range auxiliary port [1 .. Ar (fst (ru_lhs r))]
    is sent to the freshened RHS free port at boundary position [p - 1]. *)
Lemma rewire_endpoint_a1 (A : Type) (Ar : A -> nat) (N : Net A) (a1 a2 : nat) (r : Rule A)
      (p : nat)
      (Hlo : Nat.leb 1 p = true)
      (Hhi : Nat.leb p (Ar (fst (ru_lhs r))) = true) :
  rewire_endpoint A Ar N a1 a2 r (a1, p)
    = freshen_pr A N (nth (p - 1) (ru_iface r) (0, 0)).
Proof.
  unfold rewire_endpoint.
  simpl.
  assert (Heq : Nat.eqb a1 a1 = true). { apply (proj2 (Nat.eqb_eq a1 a1)). reflexivity. }
  rewrite Heq.
  simpl in Hlo.
  rewrite Hlo, Hhi.
  simpl.
  reflexivity.
Qed.

(** An endpoint at [a2] on an in-range auxiliary port [1 .. Ar (snd (ru_lhs r))]
    is sent to the freshened RHS free port at boundary position
    [Ar (fst (ru_lhs r)) + (p - 1)]. The premise [a1 <> a2] decides the first
    agent test against [a1]. *)
Lemma rewire_endpoint_a2 (A : Type) (Ar : A -> nat) (N : Net A) (a1 a2 : nat) (r : Rule A)
      (Hneq : a1 <> a2)
      (p : nat)
      (Hlo : Nat.leb 1 p = true)
      (Hhi : Nat.leb p (Ar (snd (ru_lhs r))) = true) :
  rewire_endpoint A Ar N a1 a2 r (a2, p)
    = freshen_pr A N (nth (Ar (fst (ru_lhs r)) + (p - 1)) (ru_iface r) (0, 0)).
Proof.
  unfold rewire_endpoint.
  simpl.
  assert (Hneqb : Nat.eqb a2 a1 = false).
  { apply (not_true_is_false (Nat.eqb a2 a1)).
    intro H.
    apply (proj1 (Nat.eqb_eq a2 a1)) in H.
    apply Hneq. symmetry. exact H. }
  rewrite Hneqb.
  simpl.
  assert (Heq : Nat.eqb a2 a2 = true). { apply (proj2 (Nat.eqb_eq a2 a2)). reflexivity. }
  rewrite Heq.
  simpl in Hlo.
  rewrite Hlo, Hhi.
  simpl.
  reflexivity.
Qed.

(** An endpoint at an agent that is neither [a1] nor [a2] is kept unchanged. *)
Lemma rewire_endpoint_kept (A : Type) (Ar : A -> nat) (N : Net A) (a1 a2 : nat) (r : Rule A)
      (x p : nat)
      (Hx1 : Nat.eqb x a1 = false)
      (Hx2 : Nat.eqb x a2 = false) :
  rewire_endpoint A Ar N a1 a2 r (x, p) = (x, p).
Proof.
  unfold rewire_endpoint.
  simpl.
  rewrite Hx1, Hx2.
  simpl.
  reflexivity.
Qed.

(**************************************************************************)
(** ** Rewired endpoints are valid splice ports *)

(** Every endpoint of a non-main–main link of [N] rewires to a valid port of
    the splice: the agent it refers to is present in the splice, and the port
    number is in range for that agent's arity. This is the per-endpoint
    ingredient of the [wf_links] field of [raw_splice_wf].

    The proof splits on the agent [x] of the endpoint [(x, p)]:
    * [x] is neither [a1] nor [a2]: the endpoint is kept ([rewire_endpoint_kept])
      and inherits its label and port bound from [N];
    * [x = a1] (resp. [x = a2]): the endpoint must sit on an auxiliary port in
      range — port [0] would make the link the main–main link (excluded by
      [Hnotmm] via [main_port_only_main_link]), and a port above the arity is
      excluded by [wf_links] — so it is rewired ([rewire_endpoint_a1] /
      [rewire_endpoint_a2]) to a freshened RHS free port, whose label and bound
      come from the RHS interface. *)
Lemma rewire_endpoint_valid (A : Type) (Ar : A -> nat) (N : Net A) (a1 a2 : nat) (r : Rule A)
      (α β : A)
      (Hla : agent_label A N a1 = Some α)
      (Hlb : agent_label A N a2 = Some β)
      (Hlhs : ru_lhs r = (α, β))
      (Hwf : well_formed A Ar N)
      (Hap : is_active_pair A Ar N a1 a2)
      (Hrhs : well_formed A Ar (ru_rhs r))
      (Hiface : ru_iface r = interface A Ar (ru_rhs r))
      (Hlen : length (ru_iface r) = Ar α + Ar β)
      (l : port_ref * port_ref)
      (Hl : In l (nt_links N))
      (Hnotmm : is_main_main_link a1 a2 l = false)
      (e : port_ref)
      (He : link_end l e) :
  exists la, agent_label A (raw_splice A Ar N a1 a2 r) (agent_of (rewire_endpoint A Ar N a1 a2 r e)) = Some la
            /\ port_of (rewire_endpoint A Ar N a1 a2 r e) <= Ar la.
Proof.
  set (sp := raw_splice A Ar N a1 a2 r).
  set (rw := fun e : port_ref => rewire_endpoint A Ar N a1 a2 r e).
  destruct e as [x p].
  (* (x, p) is an endpoint of l, so x is an agent of N and p is in range for
     x's arity: p <= Ar la whenever agent_label N x = Some la. *)
  assert (Hxbound : forall la, agent_label A N x = Some la -> p <= Ar la).
  {
    intros la Hal.
    destruct l as [[a pa] [b pb]].
    destruct He as [He|He].
    - (* e = fst l = (a, pa) *)
      injection He as Ha Hpa. subst a pa.
      destruct (wf_link_agents A Ar N Hwf x b p pb Hl) as [Hxa Hxb].
      destruct (agent_label A N b) as [lb|] eqn:Hlbl.
      + destruct (wf_links Hwf x b p pb Hl) as [_ [_ Hbnd]].
        exact (proj1 (Hbnd la lb Hal Hlbl)).
      + exfalso. apply Hxb. exact Hlbl.
    - (* e = snd l = (b, pb) *)
      injection He as Hb Hpb. subst b pb.
      destruct (wf_link_agents A Ar N Hwf a x pa p Hl) as [Hxa Hxx].
      destruct (agent_label A N a) as [laa|] eqn:Halaa.
      + destruct (wf_links Hwf a x pa p Hl) as [_ [_ Hbnd]].
        exact (proj2 (Hbnd laa la Halaa Hal)).
      + exfalso. apply Hxa. exact Halaa.
  }
  (* Split on whether x is a1, a2, or neither. *)
  destruct (Nat.eqb x a1) eqn:Hx1.
  - (* x = a1 *)
    apply (Nat.eqb_eq x a1) in Hx1. subst x.
    destruct (Nat.leb 1 p) eqn:Hlo.
    + (* p >= 1 *)
      destruct (Nat.leb p (Ar (fst (ru_lhs r)))) eqn:Hhi.
      * (* 1 <= p <= Ar (fst (ru_lhs r)): rewired to the RHS free port at p - 1 *)
        assert (Hrw : rw (a1, p) = freshen_pr A N (nth (p - 1) (ru_iface r) (0, 0))).
        { exact (rewire_endpoint_a1 A Ar N a1 a2 r p Hlo Hhi). }
        (* The index p - 1 is in range: p - 1 < Ar α <= Ar α + Ar β = length. *)
        assert (Har : Ar (fst (ru_lhs r)) = Ar α). { rewrite Hlhs. simpl. reflexivity. }
        rewrite Har in Hhi.
        assert (Hi : p - 1 < length (ru_iface r)).
        {
          apply (proj1 (Nat.leb_le p (Ar α))) in Hhi.
          apply (proj1 (Nat.leb_le 1 p)) in Hlo.
          rewrite Hlen.
          lia.
        }
        set (pr' := nth (p - 1) (ru_iface r) (0, 0)).
        assert (Hpr : In pr' (ru_iface r)).
        { exact (nth_In (ru_iface r) (0, 0) Hi). }
        rewrite Hiface in Hpr.
        assert (Hfree : is_free A Ar (ru_rhs r) pr').
        { exact (interface_free A Ar (ru_rhs r) Hrhs pr' Hpr). }
        destruct Hfree as [la' [Hal' [Hpb _]]].
        assert (Hagent : In (agent_of pr', la') (nt_agents (ru_rhs r))).
        { exact (agent_label_Some_In A (ru_rhs r) (agent_of pr') la' Hal'). }
        exists la'; split; [
          rewrite Hrw;
          exact (raw_splice_agent_label_fresh A Ar N a1 a2 r Hrhs (agent_of pr') la' Hagent)
        |
          rewrite Hrw;
          exact Hpb
        ].
      * (* p > Ar (fst (ru_lhs r)): kept as (a1, p) — impossible *)
        assert (Har : Ar (fst (ru_lhs r)) = Ar α). { rewrite Hlhs. simpl. reflexivity. }
        rewrite Har in Hhi.
        change (Nat.leb p (Ar α) = false) in Hhi.
        assert (Hle : p <= Ar α). { exact (Hxbound α Hla). }
        assert (Ht : Nat.leb p (Ar α) = true).
        { apply (proj2 (Nat.leb_le p (Ar α))). exact Hle. }
        rewrite Ht in Hhi. discriminate Hhi.
    + (* p = 0: kept as (a1, 0) — impossible (would be the main–main link) *)
      (* Nat.leb 1 p = false means p = 0. *)
      assert (Hp0 : p = 0).
      { destruct p eqn:Hp.
        - reflexivity.
        - simpl in Hlo. discriminate Hlo. }
      subst p.
      (* Now e = (a1, 0), so l ends at (a1, 0). *)
      assert (Hmm : is_main_main_link a1 a2 l = true).
      { exact (main_port_only_main_link A Ar N a1 a2 Hwf Hap l Hl (a1, 0) (or_introl (eq_refl : (a1, 0) = (a1, 0))) He). }
      rewrite Hmm in Hnotmm. discriminate Hnotmm.
  - (* x ≠ a1 *)
    destruct (Nat.eqb x a2) eqn:Hx2.
    + (* x = a2 *)
      apply (Nat.eqb_eq x a2) in Hx2. subst x.
      destruct (Nat.leb 1 p) eqn:Hlo.
      * (* p >= 1 *)
        { destruct (Nat.leb p (Ar (snd (ru_lhs r)))) eqn:Hhi.
        - (* 1 <= p <= Ar (snd (ru_lhs r)): rewired to the RHS free port at
              Ar α + (p - 1) *)
          assert (Hneq : a1 <> a2).
          { unfold is_active_pair in Hap. destruct Hap as [Hneq _]. exact Hneq. }
          assert (Hrw : rw (a2, p)
                     = freshen_pr A N (nth (Ar (fst (ru_lhs r)) + (p - 1)) (ru_iface r) (0, 0))).
          { exact (rewire_endpoint_a2 A Ar N a1 a2 r Hneq p Hlo Hhi). }
          (* The index Ar α + (p - 1) is in range: Ar α + (p - 1) < Ar α + Ar β. *)
          assert (Har : Ar (snd (ru_lhs r)) = Ar β). { rewrite Hlhs. simpl. reflexivity. }
          rewrite Har in Hhi.
          assert (Hi : Ar (fst (ru_lhs r)) + (p - 1) < length (ru_iface r)).
          {
            apply (proj1 (Nat.leb_le p (Ar β))) in Hhi.
            apply (proj1 (Nat.leb_le 1 p)) in Hlo.
            assert (Har1 : Ar (fst (ru_lhs r)) = Ar α). { rewrite Hlhs. simpl. reflexivity. }
            rewrite Har1.
            rewrite Hlen.
            lia.
          }
          set (pr' := nth (Ar (fst (ru_lhs r)) + (p - 1)) (ru_iface r) (0, 0)).
          assert (Hpr : In pr' (ru_iface r)).
          { exact (nth_In (ru_iface r) (0, 0) Hi). }
          rewrite Hiface in Hpr.
          assert (Hfree : is_free A Ar (ru_rhs r) pr').
          { exact (interface_free A Ar (ru_rhs r) Hrhs pr' Hpr). }
          destruct Hfree as [la' [Hal' [Hpb _]]].
          assert (Hagent : In (agent_of pr', la') (nt_agents (ru_rhs r))).
          { exact (agent_label_Some_In A (ru_rhs r) (agent_of pr') la' Hal'). }
          exists la'; split; [
            rewrite Hrw;
            exact (raw_splice_agent_label_fresh A Ar N a1 a2 r Hrhs (agent_of pr') la' Hagent)
          |
            rewrite Hrw;
            exact Hpb
          ].
        - (* p > Ar (snd (ru_lhs r)): kept as (a2, p) — impossible *)
          assert (Har : Ar (snd (ru_lhs r)) = Ar β). { rewrite Hlhs. simpl. reflexivity. }
          rewrite Har in Hhi.
          change (Nat.leb p (Ar β) = false) in Hhi.
          assert (Hle : p <= Ar β). { exact (Hxbound β Hlb). }
          assert (Ht : Nat.leb p (Ar β) = true).
          { apply (proj2 (Nat.leb_le p (Ar β))). exact Hle. }
          rewrite Ht in Hhi. discriminate Hhi.
        }
      * (* p = 0: kept as (a2, 0) — impossible (would be the main–main link) *)
        (* Nat.leb 1 p = false means p = 0. *)
        assert (Hp0 : p = 0).
        { destruct p eqn:Hp.
          - reflexivity.
          - simpl in Hlo. discriminate Hlo. }
        subst p.
        (* Now e = (a2, 0), so l ends at (a2, 0). *)
        assert (Hmm : is_main_main_link a1 a2 l = true).
        { exact (main_port_only_main_link A Ar N a1 a2 Hwf Hap l Hl (a2, 0) (or_intror (eq_refl : (a2, 0) = (a2, 0))) He). }
        rewrite Hmm in Hnotmm. discriminate Hnotmm.
    + (* x ≠ a2: kept *)
      (* The endpoint is kept unchanged. *)
      assert (Hrw : rw (x, p) = (x, p)).
      { exact (rewire_endpoint_kept A Ar N a1 a2 r x p Hx1 Hx2). }
      (* x is an agent of N (an endpoint agent of l). *)
      assert (Hxa : has_agent A N x).
      {
        destruct l as [[a pa] [b pb]].
        destruct He as [He|He].
        + injection He as Ha Hpa. subst a pa.
          exact (proj1 (wf_link_agents A Ar N Hwf x b p pb Hl)).
        + injection He as Hb Hpb. subst b pb.
          exact (proj2 (wf_link_agents A Ar N Hwf a x pa p Hl)).
      }
      destruct (agent_label A N x) as [la|] eqn:Hal.
      * (* x has label la in N; it is kept in the splice with the same label. *)
        assert (Hx1p : x <> a1).
        { intro H. subst x.
          assert (Ht : Nat.eqb a1 a1 = true). { apply (proj2 (Nat.eqb_eq a1 a1)). reflexivity. }
          rewrite Ht in Hx1. discriminate Hx1. }
        assert (Hx2p : x <> a2).
        { intro H. subst x.
          assert (Ht : Nat.eqb a2 a2 = true). { apply (proj2 (Nat.eqb_eq a2 a2)). reflexivity. }
          rewrite Ht in Hx2. discriminate Hx2. }
        exists la; split; [
          (* agent_label sp x = Some la *)
          rewrite Hrw;
          exact (raw_splice_agent_label_kept A Ar N a1 a2 r Hwf x la Hx1p Hx2p Hal)
        |
          (* p <= Ar la *)
          rewrite Hrw;
          exact (Hxbound la eq_refl)
        ].
      * (* x has no label in N — impossible (x is an agent of N). *)
        exfalso. apply Hxa. exact Hal.
Qed.

(**************************************************************************)
(** ** Distinct links do not rewire onto a shared port *)

(** The interface of the RHS has no duplicates (it is the interface of a
    well-formed net). *)
Lemma iface_nodup (A : Type) (Ar : A -> nat) (N : Net A) (a1 a2 : nat) (r : Rule A)
      (Hrhs : well_formed A Ar (ru_rhs r))
      (Hiface : ru_iface r = interface A Ar (ru_rhs r)) :
  NoDup (ru_iface r).
Proof.
  rewrite Hiface.
  exact (interface_nodup A Ar (ru_rhs r) Hrhs).
Qed.

(** Two distinct links of a well-formed net do not share an endpoint. This is
    the [wf_ports] condition applied to a single shared port. *)
Lemma distinct_links_no_shared_end (A : Type) (Ar : A -> nat) (N : Net A)
      (Hwf : well_formed A Ar N)
      (l1 l2 : port_ref * port_ref)
      (Hl1 : In l1 (nt_links N)) (Hl2 : In l2 (nt_links N))
      (Hneq : l1 <> l2) (e : port_ref)
      (He1 : link_end l1 e) (He2 : link_end l2 e) : False.
Proof.
  exfalso.
  apply (wf_ports Hwf e l1 l2 Hl1 Hl2 Hneq).
  exact (conj He1 He2).
Qed.

(** A freshened port reference is not an endpoint at an agent of [N]: its agent
    is a fresh id, absent from [N]'s agent list. *)
Lemma freshen_pr_not_agent_of_N (A : Type) (N : Net A) (pr : port_ref) (y q : nat)
      (H : freshen_pr A N pr = (y, q)) (Hy : has_agent A N y) : False.
Proof.
  unfold freshen_pr in H.
  injection H as Hy' Hq. subst y.
  apply (fresh_id_notin_N A N (fst pr)).
  apply (proj1 (has_agent_In A N (fresh_id A N (fst pr)))).
  exact Hy.
Qed.

(** The agent of an endpoint of a link of a well-formed net is present in the
    net. This is the existence part of [wf_links] for a single endpoint. *)
Lemma link_end_agent_present (A : Type) (Ar : A -> nat) (N : Net A)
      (Hwf : well_formed A Ar N)
      (l : port_ref * port_ref) (Hl : In l (nt_links N))
      (e : port_ref) (He : link_end l e) :
  has_agent A N (agent_of e).
Proof.
  destruct e as [x p].
  destruct l as [[a pa] [b pb]].
  destruct He as [He|He].
  - injection He as Ha Hpa. subst a pa.
    exact (proj1 (wf_link_agents A Ar N Hwf x b p pb Hl)).
  - injection He as Hb Hpb. subst b pb.
    exact (proj2 (wf_link_agents A Ar N Hwf a x pa p Hl)).
Qed.

(** An endpoint at [a1] on an out-of-range auxiliary port
    [p > Ar (fst (ru_lhs r))] is kept unchanged (the in-range test fails). The
    main port [p = 0] also falls through to [kept], but is excluded separately
    by the non-main–main premise. *)
Lemma rewire_endpoint_a1_out (A : Type) (Ar : A -> nat) (N : Net A) (a1 a2 : nat) (r : Rule A)
      (p : nat)
      (Hhi : Nat.leb p (Ar (fst (ru_lhs r))) = false) :
  rewire_endpoint A Ar N a1 a2 r (a1, p) = (a1, p).
Proof.
  unfold rewire_endpoint.
  simpl.
  assert (Heq : Nat.eqb a1 a1 = true). { apply (proj2 (Nat.eqb_eq a1 a1)). reflexivity. }
  rewrite Heq.
  simpl.
  (* The in-range test is false, so the whole condition is false. The
     condition's low test is shown in its reduced form to match the goal. *)
  assert (Hcond : (match p with 0 => false | S _ => true end)
                  && Nat.leb p (Ar (fst (ru_lhs r))) = false).
  {
    rewrite Hhi.
    destruct p as [|p'].
    - simpl. reflexivity.
    - simpl. reflexivity.
  }
  rewrite Hcond.
  simpl.
  reflexivity.
Qed.

(** An endpoint at [a2] on an out-of-range auxiliary port
    [p > Ar (snd (ru_lhs r))] is kept unchanged. The premise [a1 <> a2] decides
    the first agent test against [a1]. *)
Lemma rewire_endpoint_a2_out (A : Type) (Ar : A -> nat) (N : Net A) (a1 a2 : nat) (r : Rule A)
      (Hneq : a1 <> a2)
      (p : nat)
      (Hhi : Nat.leb p (Ar (snd (ru_lhs r))) = false) :
  rewire_endpoint A Ar N a1 a2 r (a2, p) = (a2, p).
Proof.
  unfold rewire_endpoint.
  simpl.
  assert (Hneqb : Nat.eqb a2 a1 = false).
  { apply (not_true_is_false (Nat.eqb a2 a1)).
    intro H.
    apply (proj1 (Nat.eqb_eq a2 a1)) in H.
    apply Hneq. symmetry. exact H. }
  rewrite Hneqb.
  simpl.
  assert (Heq : Nat.eqb a2 a2 = true). { apply (proj2 (Nat.eqb_eq a2 a2)). reflexivity. }
  rewrite Heq.
  simpl.
  (* The in-range test is false, so the whole condition is false. *)
  assert (Hcond : (match p with 0 => false | S _ => true end)
                  && Nat.leb p (Ar (snd (ru_lhs r))) = false).
  {
    rewrite Hhi.
    destruct p as [|p'].
    - simpl. reflexivity.
    - simpl. reflexivity.
  }
  rewrite Hcond.
  simpl.
  reflexivity.
Qed.

(** Two distinct non-main–main links of [N] do not rewire onto a shared port:
    if [l1] and [l2] are distinct non-main–main links and [e1], [e2] are
    endpoints of [l1], [l2] respectively, then [rewire_endpoint e1] and
    [rewire_endpoint e2] differ. This is the [N]-origin ingredient of the
    [wf_ports] field of [raw_splice_wf].

    The proof splits on the agent of each endpoint. An endpoint is either
    *kept* (its agent is neither [a1] nor [a2], or it sits on an out-of-range
    or main port) or *rewired* (it sits on an in-range auxiliary port of [a1]
    or [a2] and is sent to a freshened RHS free port). The combinations
    contradict:
    * kept + kept: the endpoints coincide, so [l1] and [l2] share an end
      ([distinct_links_no_shared_end]);
    * kept + rewired (either order): a fresh id would be an agent of [N]
      ([freshen_pr_not_agent_of_N]);
    * rewired + rewired, same source agent: the endpoints coincide
      ([freshen_pr_inj] + [NoDup_nth] + [distinct_links_no_shared_end]);
    * rewired + rewired, different source agents: the boundary index ranges
      are disjoint, so the freshened ports differ. *)
Lemma rewire_endpoint_inj (A : Type) (Ar : A -> nat) (N : Net A) (a1 a2 : nat) (r : Rule A)
      (α β : A)
      (Hla : agent_label A N a1 = Some α) (Hlb : agent_label A N a2 = Some β)
      (Hlhs : ru_lhs r = (α, β))
      (Hwf : well_formed A Ar N) (Hap : is_active_pair A Ar N a1 a2)
      (Hrhs : well_formed A Ar (ru_rhs r))
      (Hiface : ru_iface r = interface A Ar (ru_rhs r))
      (Hlen : length (ru_iface r) = Ar α + Ar β)
      (l1 l2 : port_ref * port_ref)
      (Hl1 : In l1 (nt_links N)) (Hl2 : In l2 (nt_links N))
      (Hneq : l1 <> l2)
      (Hnm1 : is_main_main_link a1 a2 l1 = false)
      (Hnm2 : is_main_main_link a1 a2 l2 = false)
      (e1 : port_ref) (He1 : link_end l1 e1)
      (e2 : port_ref) (He2 : link_end l2 e2) :
  rewire_endpoint A Ar N a1 a2 r e1 <> rewire_endpoint A Ar N a1 a2 r e2.
Proof.
  intro Heq.
  set (rw := fun e : port_ref => rewire_endpoint A Ar N a1 a2 r e).
  change (rw e1 = rw e2) in Heq.
  assert (Hneq12 : a1 <> a2).
  { unfold is_active_pair in Hap. destruct Hap as [Hneq12 _]. exact Hneq12. }
  destruct e1 as [x p].
  destruct e2 as [y q].
  (* ================= x = a1 ================= *)
  destruct (Nat.eqb x a1) eqn:Hx1.
  - apply (Nat.eqb_eq x a1) in Hx1. subst x.
    destruct (Nat.leb 1 p) eqn:Hlo.
    + (* p >= 1 *)
      assert (Har : Ar (fst (ru_lhs r)) = Ar α). { rewrite Hlhs. simpl. reflexivity. }
      destruct (Nat.leb p (Ar (fst (ru_lhs r)))) eqn:Hhi.
      * (* e1 REWIRED to iface[p-1] *)
        {
          assert (Hrw1 : rw (a1, p) = freshen_pr A N (nth (p - 1) (ru_iface r) (0, 0))).
          { exact (rewire_endpoint_a1 A Ar N a1 a2 r p Hlo Hhi). }
          rewrite Hrw1 in Heq.
          rewrite Har in Hhi.
          (* ---- y = a1 ---- *)
          destruct (Nat.eqb y a1) eqn:Hy1.
          - apply (Nat.eqb_eq y a1) in Hy1. subst y.
            destruct (Nat.leb 1 q) eqn:Hlo2.
            * (* q >= 1 *)
              assert (Har2 : Ar (fst (ru_lhs r)) = Ar α). { rewrite Hlhs. simpl. reflexivity. }
              destruct (Nat.leb q (Ar (fst (ru_lhs r)))) eqn:Hhi2.
              ** (* e2 REWIRED to iface[q-1]: fresh-fresh, same source agent *)
                {
                  assert (Hrw2 : rw (a1, q) = freshen_pr A N (nth (q - 1) (ru_iface r) (0, 0))).
                  { exact (rewire_endpoint_a1 A Ar N a1 a2 r q Hlo2 Hhi2). }
                  rewrite Hrw2 in Heq.
                  rewrite Har2 in Hhi2.
                  apply (freshen_pr_inj A N (nth (p - 1) (ru_iface r) (0, 0)) (nth (q - 1) (ru_iface r) (0, 0))) in Heq.
                  assert (Hin1 : p - 1 < length (ru_iface r)).
                  { apply (proj1 (Nat.leb_le p (Ar α))) in Hhi.
                    apply (proj1 (Nat.leb_le 1 p)) in Hlo.
                    rewrite Hlen. lia. }
                  assert (Hin2 : q - 1 < length (ru_iface r)).
                  { apply (proj1 (Nat.leb_le q (Ar α))) in Hhi2.
                    apply (proj1 (Nat.leb_le 1 q)) in Hlo2.
                    rewrite Hlen. lia. }
                  assert (Hidx : p - 1 = q - 1).
                  { apply (proj1 (NoDup_nth (ru_iface r) (0, 0))).
                    - exact (iface_nodup A Ar N a1 a2 r Hrhs Hiface).
                    - exact Hin1.
                    - exact Hin2.
                    - exact Heq. }
                  (* p, q >= 1 and p - 1 = q - 1 give p = q, so e1 = e2. *)
                  assert (Hpq : p = q).
                  {
                    destruct p as [|p'].
                    - exfalso.
                      assert (Ht : Nat.leb 1 0 = false). { simpl. reflexivity. }
                      rewrite Ht in Hlo. discriminate Hlo.
                    - destruct q as [|q'].
                      + exfalso.
                        assert (Ht : Nat.leb 1 0 = false). { simpl. reflexivity. }
                        rewrite Ht in Hlo2. discriminate Hlo2.
                      + simpl in Hidx.
                        f_equal.
                        rewrite !Nat.sub_0_r in Hidx.
                        exact Hidx.
                  }
                  exfalso.
                  apply (distinct_links_no_shared_end A Ar N Hwf l1 l2 Hl1 Hl2 Hneq (a1, p)).
                  - exact He1.
                  - subst q. exact He2.
                }
              ** (* e2 KEPT as (a1, q): fresh-kept *)
                {
                  assert (Hrw2 : rw (a1, q) = (a1, q)).
                  { exact (rewire_endpoint_a1_out A Ar N a1 a2 r q Hhi2). }
                  rewrite Hrw2 in Heq.
                  exfalso.
                  apply (freshen_pr_not_agent_of_N A N (nth (p - 1) (ru_iface r) (0, 0)) a1 q).
                  - exact Heq.
                  - exact (link_end_agent_present A Ar N Hwf l2 Hl2 (a1, q) He2).
                }
            * (* q = 0: l2 is the main–main link *)
              {
                assert (Hq0 : q = 0).
                { destruct q eqn:Hq.
                  - reflexivity.
                  - simpl in Hlo2. discriminate Hlo2. }
                subst q.
                assert (Hmm : is_main_main_link a1 a2 l2 = true).
                { exact (main_port_only_main_link A Ar N a1 a2 Hwf Hap l2 Hl2 (a1, 0) (or_introl (eq_refl : (a1, 0) = (a1, 0))) He2). }
                rewrite Hmm in Hnm2. discriminate Hnm2.
              }
          - (* y ≠ a1 *)
            destruct (Nat.eqb y a2) eqn:Hy2.
            + (* y = a2 *)
              apply (Nat.eqb_eq y a2) in Hy2. subst y.
              destruct (Nat.leb 1 q) eqn:Hlo2.
              * (* q >= 1 *)
                assert (Har2 : Ar (snd (ru_lhs r)) = Ar β). { rewrite Hlhs. simpl. reflexivity. }
                destruct (Nat.leb q (Ar (snd (ru_lhs r)))) eqn:Hhi2.
                ** (* e2 REWIRED to iface[Ar α + q - 1]: fresh-fresh, different source agents *)
                  {
                    assert (Hrw2 : rw (a2, q) = freshen_pr A N (nth (Ar (fst (ru_lhs r)) + (q - 1)) (ru_iface r) (0, 0))).
                    { exact (rewire_endpoint_a2 A Ar N a1 a2 r Hneq12 q Hlo2 Hhi2). }
                    rewrite Hrw2 in Heq.
                    rewrite Har2 in Hhi2.
                    apply (freshen_pr_inj A N (nth (p - 1) (ru_iface r) (0, 0)) (nth (Ar (fst (ru_lhs r)) + (q - 1)) (ru_iface r) (0, 0))) in Heq.
                    assert (Hin1 : p - 1 < length (ru_iface r)).
                    { apply (proj1 (Nat.leb_le p (Ar α))) in Hhi.
                      apply (proj1 (Nat.leb_le 1 p)) in Hlo.
                      rewrite Hlen. lia. }
                    assert (Har1 : Ar (fst (ru_lhs r)) = Ar α). { rewrite Hlhs. simpl. reflexivity. }
                    assert (Hin2 : Ar (fst (ru_lhs r)) + (q - 1) < length (ru_iface r)).
                    { apply (proj1 (Nat.leb_le q (Ar β))) in Hhi2.
                      apply (proj1 (Nat.leb_le 1 q)) in Hlo2.
                      rewrite Har1.
                      rewrite Hlen. lia. }
                    assert (Hidx : p - 1 = Ar (fst (ru_lhs r)) + (q - 1)).
                    { apply (proj1 (NoDup_nth (ru_iface r) (0, 0))).
                      - exact (iface_nodup A Ar N a1 a2 r Hrhs Hiface).
                      - exact Hin1.
                      - exact Hin2.
                      - exact Heq. }
                    (* p - 1 = Ar α + (q - 1) >= Ar α, so p >= Ar α + 1, but p <= Ar α. *)
                    assert (Hp : p <= Ar α). { apply (proj1 (Nat.leb_le p (Ar α))). exact Hhi. }
                    assert (Hp1 : 1 <= p). { apply (proj1 (Nat.leb_le 1 p)). exact Hlo. }
                    assert (Hq1 : 1 <= q). { apply (proj1 (Nat.leb_le 1 q)). exact Hlo2. }
                    exfalso.
                    rewrite Har1 in Hidx.
                    lia.
                  }
                ** (* e2 KEPT as (a2, q): fresh-kept *)
                  {
                    assert (Hrw2 : rw (a2, q) = (a2, q)).
                    { exact (rewire_endpoint_a2_out A Ar N a1 a2 r Hneq12 q Hhi2). }
                    rewrite Hrw2 in Heq.
                    exfalso.
                    apply (freshen_pr_not_agent_of_N A N (nth (p - 1) (ru_iface r) (0, 0)) a2 q).
                    - exact Heq.
                    - exact (link_end_agent_present A Ar N Hwf l2 Hl2 (a2, q) He2).
                  }
              * (* q = 0: l2 is the main–main link *)
                {
                  assert (Hq0 : q = 0).
                  { destruct q eqn:Hq.
                    - reflexivity.
                    - simpl in Hlo2. discriminate Hlo2. }
                  subst q.
                  assert (Hmm : is_main_main_link a1 a2 l2 = true).
                  { exact (main_port_only_main_link A Ar N a1 a2 Hwf Hap l2 Hl2 (a2, 0) (or_intror (eq_refl : (a2, 0) = (a2, 0))) He2). }
                  rewrite Hmm in Hnm2. discriminate Hnm2.
                }
            + (* y ≠ a2: e2 KEPT *)
              {
                assert (Hrw2 : rw (y, q) = (y, q)).
                { exact (rewire_endpoint_kept A Ar N a1 a2 r y q Hy1 Hy2). }
                rewrite Hrw2 in Heq.
                exfalso.
                apply (freshen_pr_not_agent_of_N A N (nth (p - 1) (ru_iface r) (0, 0)) y q).
                - exact Heq.
                - exact (link_end_agent_present A Ar N Hwf l2 Hl2 (y, q) He2).
              }
        }
      * (* e1 KEPT as (a1, p) [p > Ar α] *)
        {
          assert (Hrw1 : rw (a1, p) = (a1, p)).
          { exact (rewire_endpoint_a1_out A Ar N a1 a2 r p Hhi). }
          rewrite Hrw1 in Heq.
          (* ---- y = a1 ---- *)
          destruct (Nat.eqb y a1) eqn:Hy1.
          - apply (Nat.eqb_eq y a1) in Hy1. subst y.
            destruct (Nat.leb 1 q) eqn:Hlo2.
            * (* q >= 1 *)
              assert (Har2 : Ar (fst (ru_lhs r)) = Ar α). { rewrite Hlhs. simpl. reflexivity. }
              destruct (Nat.leb q (Ar (fst (ru_lhs r)))) eqn:Hhi2.
              ** (* e2 REWIRED to iface[q-1]: kept-fresh *)
                {
                  assert (Hrw2 : rw (a1, q) = freshen_pr A N (nth (q - 1) (ru_iface r) (0, 0))).
                  { exact (rewire_endpoint_a1 A Ar N a1 a2 r q Hlo2 Hhi2). }
                  rewrite Hrw2 in Heq.
                  exfalso.
                  apply (freshen_pr_not_agent_of_N A N (nth (q - 1) (ru_iface r) (0, 0)) a1 p).
                  - symmetry. exact Heq.
                  - exact (link_end_agent_present A Ar N Hwf l1 Hl1 (a1, p) He1).
                }
              ** (* e2 KEPT as (a1, q): kept-kept *)
                {
                  assert (Hrw2 : rw (a1, q) = (a1, q)).
                  { exact (rewire_endpoint_a1_out A Ar N a1 a2 r q Hhi2). }
                  rewrite Hrw2 in Heq.
                  exfalso.
                  apply (distinct_links_no_shared_end A Ar N Hwf l1 l2 Hl1 Hl2 Hneq (a1, p)).
                  - exact He1.
                  - rewrite <- Heq in He2. exact He2.
                }
            * (* q = 0: l2 is the main–main link *)
              {
                assert (Hq0 : q = 0).
                { destruct q eqn:Hq.
                  - reflexivity.
                  - simpl in Hlo2. discriminate Hlo2. }
                subst q.
                assert (Hmm : is_main_main_link a1 a2 l2 = true).
                { exact (main_port_only_main_link A Ar N a1 a2 Hwf Hap l2 Hl2 (a1, 0) (or_introl (eq_refl : (a1, 0) = (a1, 0))) He2). }
                rewrite Hmm in Hnm2. discriminate Hnm2.
              }
          - (* y ≠ a1 *)
            destruct (Nat.eqb y a2) eqn:Hy2.
            + (* y = a2 *)
              apply (Nat.eqb_eq y a2) in Hy2. subst y.
              destruct (Nat.leb 1 q) eqn:Hlo2.
              * (* q >= 1 *)
                assert (Har2 : Ar (snd (ru_lhs r)) = Ar β). { rewrite Hlhs. simpl. reflexivity. }
                destruct (Nat.leb q (Ar (snd (ru_lhs r)))) eqn:Hhi2.
                ** (* e2 REWIRED to iface[Ar α + q - 1]: kept-fresh *)
                  {
                    assert (Hrw2 : rw (a2, q) = freshen_pr A N (nth (Ar (fst (ru_lhs r)) + (q - 1)) (ru_iface r) (0, 0))).
                    { exact (rewire_endpoint_a2 A Ar N a1 a2 r Hneq12 q Hlo2 Hhi2). }
                    rewrite Hrw2 in Heq.
                    exfalso.
                    apply (freshen_pr_not_agent_of_N A N (nth (Ar (fst (ru_lhs r)) + (q - 1)) (ru_iface r) (0, 0)) a1 p).
                    - symmetry. exact Heq.
                    - exact (link_end_agent_present A Ar N Hwf l1 Hl1 (a1, p) He1).
                  }
                ** (* e2 KEPT as (a2, q): kept-kept *)
                  {
                    assert (Hrw2 : rw (a2, q) = (a2, q)).
                    { exact (rewire_endpoint_a2_out A Ar N a1 a2 r Hneq12 q Hhi2). }
                    rewrite Hrw2 in Heq.
                    exfalso.
                    apply (distinct_links_no_shared_end A Ar N Hwf l1 l2 Hl1 Hl2 Hneq (a1, p)).
                    - exact He1.
                    - rewrite <- Heq in He2. exact He2.
                  }
              * (* q = 0: l2 is the main–main link *)
                {
                  assert (Hq0 : q = 0).
                  { destruct q eqn:Hq.
                    - reflexivity.
                    - simpl in Hlo2. discriminate Hlo2. }
                  subst q.
                  assert (Hmm : is_main_main_link a1 a2 l2 = true).
                  { exact (main_port_only_main_link A Ar N a1 a2 Hwf Hap l2 Hl2 (a2, 0) (or_intror (eq_refl : (a2, 0) = (a2, 0))) He2). }
                  rewrite Hmm in Hnm2. discriminate Hnm2.
                }
            + (* y ≠ a2: e2 KEPT: kept-kept *)
              {
                assert (Hrw2 : rw (y, q) = (y, q)).
                { exact (rewire_endpoint_kept A Ar N a1 a2 r y q Hy1 Hy2). }
                rewrite Hrw2 in Heq.
                exfalso.
                apply (distinct_links_no_shared_end A Ar N Hwf l1 l2 Hl1 Hl2 Hneq (a1, p)).
                - exact He1.
                - rewrite <- Heq in He2. exact He2.
              }
        }
    + (* p = 0: l1 is the main–main link *)
      {
        assert (Hp0 : p = 0).
        { destruct p eqn:Hp.
          - reflexivity.
          - simpl in Hlo. discriminate Hlo. }
        subst p.
        assert (Hmm : is_main_main_link a1 a2 l1 = true).
        { exact (main_port_only_main_link A Ar N a1 a2 Hwf Hap l1 Hl1 (a1, 0) (or_introl (eq_refl : (a1, 0) = (a1, 0))) He1). }
        rewrite Hmm in Hnm1. discriminate Hnm1.
      }
  - (* ================= x ≠ a1 ================= *)
    destruct (Nat.eqb x a2) eqn:Hx2.
    + (* x = a2 *)
      apply (Nat.eqb_eq x a2) in Hx2. subst x.
      destruct (Nat.leb 1 p) eqn:Hlo.
      * (* p >= 1 *)
        assert (Har : Ar (snd (ru_lhs r)) = Ar β). { rewrite Hlhs. simpl. reflexivity. }
        destruct (Nat.leb p (Ar (snd (ru_lhs r)))) eqn:Hhi.
        ** (* e1 REWIRED to iface[Ar α + p - 1] *)
          {
            assert (Hrw1 : rw (a2, p) = freshen_pr A N (nth (Ar (fst (ru_lhs r)) + (p - 1)) (ru_iface r) (0, 0))).
            { exact (rewire_endpoint_a2 A Ar N a1 a2 r Hneq12 p Hlo Hhi). }
            rewrite Hrw1 in Heq.
            rewrite Har in Hhi.
            (* ---- y = a1 ---- *)
            destruct (Nat.eqb y a1) eqn:Hy1.
            - apply (Nat.eqb_eq y a1) in Hy1. subst y.
              destruct (Nat.leb 1 q) eqn:Hlo2.
              * (* q >= 1 *)
                assert (Har2 : Ar (fst (ru_lhs r)) = Ar α). { rewrite Hlhs. simpl. reflexivity. }
                destruct (Nat.leb q (Ar (fst (ru_lhs r)))) eqn:Hhi2.
                ** (* e2 REWIRED to iface[q-1]: fresh-fresh, different source agents *)
                  {
                    assert (Hrw2 : rw (a1, q) = freshen_pr A N (nth (q - 1) (ru_iface r) (0, 0))).
                    { exact (rewire_endpoint_a1 A Ar N a1 a2 r q Hlo2 Hhi2). }
                    rewrite Hrw2 in Heq.
                    rewrite Har2 in Hhi2.
                    apply (freshen_pr_inj A N (nth (Ar (fst (ru_lhs r)) + (p - 1)) (ru_iface r) (0, 0)) (nth (q - 1) (ru_iface r) (0, 0))) in Heq.
                    assert (Har1 : Ar (fst (ru_lhs r)) = Ar α). { rewrite Hlhs. simpl. reflexivity. }
                    assert (Hin1 : Ar (fst (ru_lhs r)) + (p - 1) < length (ru_iface r)).
                    { apply (proj1 (Nat.leb_le p (Ar β))) in Hhi.
                      apply (proj1 (Nat.leb_le 1 p)) in Hlo.
                      rewrite Har1.
                      rewrite Hlen. lia. }
                    assert (Hin2 : q - 1 < length (ru_iface r)).
                    { apply (proj1 (Nat.leb_le q (Ar α))) in Hhi2.
                      apply (proj1 (Nat.leb_le 1 q)) in Hlo2.
                      rewrite Hlen. lia. }
                    assert (Hidx : Ar (fst (ru_lhs r)) + (p - 1) = q - 1).
                    { apply (proj1 (NoDup_nth (ru_iface r) (0, 0))).
                      - exact (iface_nodup A Ar N a1 a2 r Hrhs Hiface).
                      - exact Hin1.
                      - exact Hin2.
                      - exact Heq. }
                    (* Ar α + (p - 1) = q - 1, so q = Ar α + p >= Ar α + 1, but q <= Ar α. *)
                    assert (Hq : q <= Ar α). { apply (proj1 (Nat.leb_le q (Ar α))). exact Hhi2. }
                    assert (Hp1 : 1 <= p). { apply (proj1 (Nat.leb_le 1 p)). exact Hlo. }
                    assert (Hq1 : 1 <= q). { apply (proj1 (Nat.leb_le 1 q)). exact Hlo2. }
                    exfalso.
                    rewrite Har1 in Hidx.
                    lia.
                  }
                ** (* e2 KEPT as (a1, q): fresh-kept *)
                  {
                    assert (Hrw2 : rw (a1, q) = (a1, q)).
                    { exact (rewire_endpoint_a1_out A Ar N a1 a2 r q Hhi2). }
                    rewrite Hrw2 in Heq.
                    exfalso.
                    apply (freshen_pr_not_agent_of_N A N (nth (Ar (fst (ru_lhs r)) + (p - 1)) (ru_iface r) (0, 0)) a1 q).
                    - exact Heq.
                    - exact (link_end_agent_present A Ar N Hwf l2 Hl2 (a1, q) He2).
                  }
              * (* q = 0: l2 is the main–main link *)
                {
                  assert (Hq0 : q = 0).
                  { destruct q eqn:Hq.
                    - reflexivity.
                    - simpl in Hlo2. discriminate Hlo2. }
                  subst q.
                  assert (Hmm : is_main_main_link a1 a2 l2 = true).
                  { exact (main_port_only_main_link A Ar N a1 a2 Hwf Hap l2 Hl2 (a1, 0) (or_introl (eq_refl : (a1, 0) = (a1, 0))) He2). }
                  rewrite Hmm in Hnm2. discriminate Hnm2.
                }
            - (* y ≠ a1 *)
              destruct (Nat.eqb y a2) eqn:Hy2.
              + (* y = a2 *)
                apply (Nat.eqb_eq y a2) in Hy2. subst y.
                destruct (Nat.leb 1 q) eqn:Hlo2.
                * (* q >= 1 *)
                  assert (Har2 : Ar (snd (ru_lhs r)) = Ar β). { rewrite Hlhs. simpl. reflexivity. }
                  destruct (Nat.leb q (Ar (snd (ru_lhs r)))) eqn:Hhi2.
                  ** (* e2 REWIRED to iface[Ar α + q - 1]: fresh-fresh, same source agent *)
                    {
                      assert (Hrw2 : rw (a2, q) = freshen_pr A N (nth (Ar (fst (ru_lhs r)) + (q - 1)) (ru_iface r) (0, 0))).
                      { exact (rewire_endpoint_a2 A Ar N a1 a2 r Hneq12 q Hlo2 Hhi2). }
                      rewrite Hrw2 in Heq.
                      rewrite Har2 in Hhi2.
                      apply (freshen_pr_inj A N (nth (Ar (fst (ru_lhs r)) + (p - 1)) (ru_iface r) (0, 0)) (nth (Ar (fst (ru_lhs r)) + (q - 1)) (ru_iface r) (0, 0))) in Heq.
                      assert (Har1 : Ar (fst (ru_lhs r)) = Ar α). { rewrite Hlhs. simpl. reflexivity. }
                      assert (Hin1 : Ar (fst (ru_lhs r)) + (p - 1) < length (ru_iface r)).
                      { apply (proj1 (Nat.leb_le p (Ar β))) in Hhi.
                        apply (proj1 (Nat.leb_le 1 p)) in Hlo.
                        rewrite Har1.
                        rewrite Hlen. lia. }
                      assert (Hin2 : Ar (fst (ru_lhs r)) + (q - 1) < length (ru_iface r)).
                      { apply (proj1 (Nat.leb_le q (Ar β))) in Hhi2.
                        apply (proj1 (Nat.leb_le 1 q)) in Hlo2.
                        rewrite Har1.
                        rewrite Hlen. lia. }
                      assert (Hidx : Ar (fst (ru_lhs r)) + (p - 1) = Ar (fst (ru_lhs r)) + (q - 1)).
                      { apply (proj1 (NoDup_nth (ru_iface r) (0, 0))).
                        - exact (iface_nodup A Ar N a1 a2 r Hrhs Hiface).
                        - exact Hin1.
                        - exact Hin2.
                        - exact Heq. }
                      (* Ar α + (p - 1) = Ar α + (q - 1), so p - 1 = q - 1, so p = q, so e1 = e2. *)
                      assert (Hpq : p = q).
                      {
                        apply Nat.add_cancel_l in Hidx.
                        destruct p as [|p'].
                        - exfalso.
                          assert (Ht : Nat.leb 1 0 = false). { simpl. reflexivity. }
                          rewrite Ht in Hlo. discriminate Hlo.
                        - destruct q as [|q'].
                          + exfalso.
                            assert (Ht : Nat.leb 1 0 = false). { simpl. reflexivity. }
                            rewrite Ht in Hlo2. discriminate Hlo2.
                          + simpl in Hidx.
                            f_equal.
                            rewrite !Nat.sub_0_r in Hidx.
                            exact Hidx.
                      }
                      exfalso.
                      apply (distinct_links_no_shared_end A Ar N Hwf l1 l2 Hl1 Hl2 Hneq (a2, p)).
                      - exact He1.
                      - subst q. exact He2.
                    }
                  ** (* e2 KEPT as (a2, q): fresh-kept *)
                    {
                      assert (Hrw2 : rw (a2, q) = (a2, q)).
                      { exact (rewire_endpoint_a2_out A Ar N a1 a2 r Hneq12 q Hhi2). }
                      rewrite Hrw2 in Heq.
                      exfalso.
                      apply (freshen_pr_not_agent_of_N A N (nth (Ar (fst (ru_lhs r)) + (p - 1)) (ru_iface r) (0, 0)) a2 q).
                      - exact Heq.
                      - exact (link_end_agent_present A Ar N Hwf l2 Hl2 (a2, q) He2).
                    }
                * (* q = 0: l2 is the main–main link *)
                  {
                    assert (Hq0 : q = 0).
                    { destruct q eqn:Hq.
                      - reflexivity.
                      - simpl in Hlo2. discriminate Hlo2. }
                    subst q.
                    assert (Hmm : is_main_main_link a1 a2 l2 = true).
                    { exact (main_port_only_main_link A Ar N a1 a2 Hwf Hap l2 Hl2 (a2, 0) (or_intror (eq_refl : (a2, 0) = (a2, 0))) He2). }
                    rewrite Hmm in Hnm2. discriminate Hnm2.
                  }
              + (* y ≠ a2: e2 KEPT *)
                {
                  assert (Hrw2 : rw (y, q) = (y, q)).
                  { exact (rewire_endpoint_kept A Ar N a1 a2 r y q Hy1 Hy2). }
                  rewrite Hrw2 in Heq.
                  exfalso.
                  apply (freshen_pr_not_agent_of_N A N (nth (Ar (fst (ru_lhs r)) + (p - 1)) (ru_iface r) (0, 0)) y q).
                  - exact Heq.
                  - exact (link_end_agent_present A Ar N Hwf l2 Hl2 (y, q) He2).
                }
          }
        ** (* e1 KEPT as (a2, p) [p > Ar β] *)
          {
            assert (Hrw1 : rw (a2, p) = (a2, p)).
            { exact (rewire_endpoint_a2_out A Ar N a1 a2 r Hneq12 p Hhi). }
            rewrite Hrw1 in Heq.
            (* ---- y = a1 ---- *)
            destruct (Nat.eqb y a1) eqn:Hy1.
            - apply (Nat.eqb_eq y a1) in Hy1. subst y.
              destruct (Nat.leb 1 q) eqn:Hlo2.
              * (* q >= 1 *)
                assert (Har2 : Ar (fst (ru_lhs r)) = Ar α). { rewrite Hlhs. simpl. reflexivity. }
                destruct (Nat.leb q (Ar (fst (ru_lhs r)))) eqn:Hhi2.
                ** (* e2 REWIRED to iface[q-1]: kept-fresh *)
                  {
                    assert (Hrw2 : rw (a1, q) = freshen_pr A N (nth (q - 1) (ru_iface r) (0, 0))).
                    { exact (rewire_endpoint_a1 A Ar N a1 a2 r q Hlo2 Hhi2). }
                    rewrite Hrw2 in Heq.
                    exfalso.
                    apply (freshen_pr_not_agent_of_N A N (nth (q - 1) (ru_iface r) (0, 0)) a2 p).
                    - symmetry. exact Heq.
                    - exact (link_end_agent_present A Ar N Hwf l1 Hl1 (a2, p) He1).
                  }
                ** (* e2 KEPT as (a1, q): kept-kept *)
                  {
                    assert (Hrw2 : rw (a1, q) = (a1, q)).
                    { exact (rewire_endpoint_a1_out A Ar N a1 a2 r q Hhi2). }
                    rewrite Hrw2 in Heq.
                    exfalso.
                    apply (distinct_links_no_shared_end A Ar N Hwf l1 l2 Hl1 Hl2 Hneq (a2, p)).
                    - exact He1.
                    - rewrite <- Heq in He2. exact He2.
                  }
              * (* q = 0: l2 is the main–main link *)
                {
                  assert (Hq0 : q = 0).
                  { destruct q eqn:Hq.
                    - reflexivity.
                    - simpl in Hlo2. discriminate Hlo2. }
                  subst q.
                  assert (Hmm : is_main_main_link a1 a2 l2 = true).
                  { exact (main_port_only_main_link A Ar N a1 a2 Hwf Hap l2 Hl2 (a1, 0) (or_introl (eq_refl : (a1, 0) = (a1, 0))) He2). }
                  rewrite Hmm in Hnm2. discriminate Hnm2.
                }
            - (* y ≠ a1 *)
              destruct (Nat.eqb y a2) eqn:Hy2.
              + (* y = a2 *)
                apply (Nat.eqb_eq y a2) in Hy2. subst y.
                destruct (Nat.leb 1 q) eqn:Hlo2.
                * (* q >= 1 *)
                  assert (Har2 : Ar (snd (ru_lhs r)) = Ar β). { rewrite Hlhs. simpl. reflexivity. }
                  destruct (Nat.leb q (Ar (snd (ru_lhs r)))) eqn:Hhi2.
                  ** (* e2 REWIRED to iface[Ar α + q - 1]: kept-fresh *)
                    {
                      assert (Hrw2 : rw (a2, q) = freshen_pr A N (nth (Ar (fst (ru_lhs r)) + (q - 1)) (ru_iface r) (0, 0))).
                      { exact (rewire_endpoint_a2 A Ar N a1 a2 r Hneq12 q Hlo2 Hhi2). }
                      rewrite Hrw2 in Heq.
                      exfalso.
                      apply (freshen_pr_not_agent_of_N A N (nth (Ar (fst (ru_lhs r)) + (q - 1)) (ru_iface r) (0, 0)) a2 p).
                      - symmetry. exact Heq.
                      - exact (link_end_agent_present A Ar N Hwf l1 Hl1 (a2, p) He1).
                    }
                  ** (* e2 KEPT as (a2, q): kept-kept *)
                    {
                      assert (Hrw2 : rw (a2, q) = (a2, q)).
                      { exact (rewire_endpoint_a2_out A Ar N a1 a2 r Hneq12 q Hhi2). }
                      rewrite Hrw2 in Heq.
                      exfalso.
                      apply (distinct_links_no_shared_end A Ar N Hwf l1 l2 Hl1 Hl2 Hneq (a2, p)).
                      - exact He1.
                      - rewrite <- Heq in He2. exact He2.
                    }
                * (* q = 0: l2 is the main–main link *)
                  {
                    assert (Hq0 : q = 0).
                    { destruct q eqn:Hq.
                      - reflexivity.
                      - simpl in Hlo2. discriminate Hlo2. }
                    subst q.
                    assert (Hmm : is_main_main_link a1 a2 l2 = true).
                    { exact (main_port_only_main_link A Ar N a1 a2 Hwf Hap l2 Hl2 (a2, 0) (or_intror (eq_refl : (a2, 0) = (a2, 0))) He2). }
                    rewrite Hmm in Hnm2. discriminate Hnm2.
                  }
              + (* y ≠ a2: e2 KEPT: kept-kept *)
                {
                  assert (Hrw2 : rw (y, q) = (y, q)).
                  { exact (rewire_endpoint_kept A Ar N a1 a2 r y q Hy1 Hy2). }
                  rewrite Hrw2 in Heq.
                  exfalso.
                  apply (distinct_links_no_shared_end A Ar N Hwf l1 l2 Hl1 Hl2 Hneq (a2, p)).
                  - exact He1.
                  - rewrite <- Heq in He2. exact He2.
                }
          }
      * (* p = 0: l1 is the main–main link *)
        {
          assert (Hp0 : p = 0).
          { destruct p eqn:Hp.
            - reflexivity.
            - simpl in Hlo. discriminate Hlo. }
          subst p.
          assert (Hmm : is_main_main_link a1 a2 l1 = true).
          { exact (main_port_only_main_link A Ar N a1 a2 Hwf Hap l1 Hl1 (a2, 0) (or_intror (eq_refl : (a2, 0) = (a2, 0))) He1). }
          rewrite Hmm in Hnm1. discriminate Hnm1.
        }
    + (* x ≠ a2: e1 KEPT *)
      {
        assert (Hrw1 : rw (x, p) = (x, p)).
        { exact (rewire_endpoint_kept A Ar N a1 a2 r x p Hx1 Hx2). }
        rewrite Hrw1 in Heq.
        (* ---- y = a1 ---- *)
        destruct (Nat.eqb y a1) eqn:Hy1.
        - apply (Nat.eqb_eq y a1) in Hy1. subst y.
          destruct (Nat.leb 1 q) eqn:Hlo2.
          * (* q >= 1 *)
            assert (Har2 : Ar (fst (ru_lhs r)) = Ar α). { rewrite Hlhs. simpl. reflexivity. }
            destruct (Nat.leb q (Ar (fst (ru_lhs r)))) eqn:Hhi2.
            ** (* e2 REWIRED to iface[q-1]: kept-fresh *)
              {
                assert (Hrw2 : rw (a1, q) = freshen_pr A N (nth (q - 1) (ru_iface r) (0, 0))).
                { exact (rewire_endpoint_a1 A Ar N a1 a2 r q Hlo2 Hhi2). }
                rewrite Hrw2 in Heq.
                exfalso.
                apply (freshen_pr_not_agent_of_N A N (nth (q - 1) (ru_iface r) (0, 0)) x p).
                - symmetry. exact Heq.
                - exact (link_end_agent_present A Ar N Hwf l1 Hl1 (x, p) He1).
              }
            ** (* e2 KEPT as (a1, q): kept-kept *)
              {
                assert (Hrw2 : rw (a1, q) = (a1, q)).
                { exact (rewire_endpoint_a1_out A Ar N a1 a2 r q Hhi2). }
                rewrite Hrw2 in Heq.
                exfalso.
                apply (distinct_links_no_shared_end A Ar N Hwf l1 l2 Hl1 Hl2 Hneq (x, p)).
                - exact He1.
                - rewrite <- Heq in He2. exact He2.
              }
          * (* q = 0: l2 is the main–main link *)
            {
              assert (Hq0 : q = 0).
              { destruct q eqn:Hq.
                - reflexivity.
                - simpl in Hlo2. discriminate Hlo2. }
              subst q.
              assert (Hmm : is_main_main_link a1 a2 l2 = true).
              { exact (main_port_only_main_link A Ar N a1 a2 Hwf Hap l2 Hl2 (a1, 0) (or_introl (eq_refl : (a1, 0) = (a1, 0))) He2). }
              rewrite Hmm in Hnm2. discriminate Hnm2.
            }
        - (* y ≠ a1 *)
          destruct (Nat.eqb y a2) eqn:Hy2.
          + (* y = a2 *)
            apply (Nat.eqb_eq y a2) in Hy2. subst y.
            destruct (Nat.leb 1 q) eqn:Hlo2.
            * (* q >= 1 *)
              assert (Har2 : Ar (snd (ru_lhs r)) = Ar β). { rewrite Hlhs. simpl. reflexivity. }
              destruct (Nat.leb q (Ar (snd (ru_lhs r)))) eqn:Hhi2.
              ** (* e2 REWIRED to iface[Ar α + q - 1]: kept-fresh *)
                {
                  assert (Hrw2 : rw (a2, q) = freshen_pr A N (nth (Ar (fst (ru_lhs r)) + (q - 1)) (ru_iface r) (0, 0))).
                  { exact (rewire_endpoint_a2 A Ar N a1 a2 r Hneq12 q Hlo2 Hhi2). }
                  rewrite Hrw2 in Heq.
                  exfalso.
                  apply (freshen_pr_not_agent_of_N A N (nth (Ar (fst (ru_lhs r)) + (q - 1)) (ru_iface r) (0, 0)) x p).
                  - symmetry. exact Heq.
                  - exact (link_end_agent_present A Ar N Hwf l1 Hl1 (x, p) He1).
                }
              ** (* e2 KEPT as (a2, q): kept-kept *)
                {
                  assert (Hrw2 : rw (a2, q) = (a2, q)).
                  { exact (rewire_endpoint_a2_out A Ar N a1 a2 r Hneq12 q Hhi2). }
                  rewrite Hrw2 in Heq.
                  exfalso.
                  apply (distinct_links_no_shared_end A Ar N Hwf l1 l2 Hl1 Hl2 Hneq (x, p)).
                  - exact He1.
                  - rewrite <- Heq in He2. exact He2.
                }
            * (* q = 0: l2 is the main–main link *)
              {
                assert (Hq0 : q = 0).
                { destruct q eqn:Hq.
                  - reflexivity.
                  - simpl in Hlo2. discriminate Hlo2. }
                subst q.
                assert (Hmm : is_main_main_link a1 a2 l2 = true).
                { exact (main_port_only_main_link A Ar N a1 a2 Hwf Hap l2 Hl2 (a2, 0) (or_intror (eq_refl : (a2, 0) = (a2, 0))) He2). }
                rewrite Hmm in Hnm2. discriminate Hnm2.
              }
          + (* y ≠ a2: e2 KEPT: kept-kept *)
            {
              assert (Hrw2 : rw (y, q) = (y, q)).
              { exact (rewire_endpoint_kept A Ar N a1 a2 r y q Hy1 Hy2). }
              rewrite Hrw2 in Heq.
              exfalso.
              apply (distinct_links_no_shared_end A Ar N Hwf l1 l2 Hl1 Hl2 Hneq (x, p)).
              - exact He1.
              - rewrite <- Heq in He2. exact He2.
            }
      }
Qed.

(** A rewired endpoint of a non-main–main link of [N] is never equal to a
    freshened endpoint of a link of the RHS: if the endpoint is kept, its agent
    is an agent of [N] (but a freshened port's agent is a fresh id, absent from
    [N]); if it is rewired, it lands on a freshened RHS free port, whereas an
    endpoint of a link of the RHS is a used port. This is the [N]-vs-[RHS]
    ingredient of the [wf_ports] field of [raw_splice_wf]. *)
Lemma rewire_endpoint_neq_fresh_link_end (A : Type) (Ar : A -> nat) (N : Net A) (a1 a2 : nat) (r : Rule A)
      (α β : A)
      (Hla : agent_label A N a1 = Some α) (Hlb : agent_label A N a2 = Some β)
      (Hlhs : ru_lhs r = (α, β))
      (Hwf : well_formed A Ar N) (Hap : is_active_pair A Ar N a1 a2)
      (Hrhs : well_formed A Ar (ru_rhs r))
      (Hiface : ru_iface r = interface A Ar (ru_rhs r))
      (Hlen : length (ru_iface r) = Ar α + Ar β)
      (l1 : port_ref * port_ref) (Hl1 : In l1 (nt_links N))
      (Hnm1 : is_main_main_link a1 a2 l1 = false)
      (e1 : port_ref) (He1 : link_end l1 e1)
      (l2 : port_ref * port_ref) (Hl2 : In l2 (nt_links (ru_rhs r)))
      (e2 : port_ref) (He2 : link_end l2 e2) :
  rewire_endpoint A Ar N a1 a2 r e1 <> freshen_pr A N e2.
Proof.
  intro Heq.
  set (rw := fun e : port_ref => rewire_endpoint A Ar N a1 a2 r e).
  change (rw e1 = freshen_pr A N e2) in Heq.
  assert (Hneq12 : a1 <> a2).
  { unfold is_active_pair in Hap. destruct Hap as [Hneq12 _]. exact Hneq12. }
  destruct e1 as [x p].
  (* ================= x = a1 ================= *)
  destruct (Nat.eqb x a1) eqn:Hx1.
  - apply (Nat.eqb_eq x a1) in Hx1. subst x.
    destruct (Nat.leb 1 p) eqn:Hlo.
    + (* p >= 1 *)
      assert (Har : Ar (fst (ru_lhs r)) = Ar α). { rewrite Hlhs. simpl. reflexivity. }
      destruct (Nat.leb p (Ar (fst (ru_lhs r)))) eqn:Hhi.
      * (* e1 REWIRED to iface[p-1]: a freshened RHS free port, but e2 is a used RHS port *)
        {
          assert (Hrw1 : rw (a1, p) = freshen_pr A N (nth (p - 1) (ru_iface r) (0, 0))).
          { exact (rewire_endpoint_a1 A Ar N a1 a2 r p Hlo Hhi). }
          rewrite Hrw1 in Heq.
          rewrite Har in Hhi.
          set (pr' := nth (p - 1) (ru_iface r) (0, 0)).
          apply (freshen_pr_inj A N pr' e2) in Heq.
          (* e2 is a used port of the RHS *)
          assert (Hused : port_used A (ru_rhs r) e2).
          { exists l2. split; [exact Hl2 | exact He2]. }
          rewrite <- Heq in Hused.
          (* The index p - 1 is in range: p - 1 < Ar α <= Ar α + Ar β = length. *)
          assert (Hir : p - 1 < length (ru_iface r)).
          { apply (proj1 (Nat.leb_le p (Ar α))) in Hhi.
            apply (proj1 (Nat.leb_le 1 p)) in Hlo.
            rewrite Hlen. lia. }
          assert (Hpr : In pr' (ru_iface r)).
          { exact (nth_In (ru_iface r) (0, 0) Hir). }
          rewrite Hiface in Hpr.
          assert (Hfree : is_free A Ar (ru_rhs r) pr').
          { exact (interface_free A Ar (ru_rhs r) Hrhs pr' Hpr). }
          destruct Hfree as [la [Hal [Hpb Hnotused]]].
          exact (Hnotused Hused).
        }
      * (* e1 KEPT as (a1, p): a fresh id would be an agent of N *)
        {
          assert (Hrw1 : rw (a1, p) = (a1, p)).
          { exact (rewire_endpoint_a1_out A Ar N a1 a2 r p Hhi). }
          rewrite Hrw1 in Heq.
          exfalso.
          apply (freshen_pr_not_agent_of_N A N e2 a1 p).
          - exact (eq_sym Heq).
          - exact (link_end_agent_present A Ar N Hwf l1 Hl1 (a1, p) He1).
        }
    + (* p = 0: l1 is the main–main link *)
      {
        assert (Hp0 : p = 0).
        { destruct p eqn:Hp.
          - reflexivity.
          - simpl in Hlo. discriminate Hlo. }
        subst p.
        assert (Hmm : is_main_main_link a1 a2 l1 = true).
        { exact (main_port_only_main_link A Ar N a1 a2 Hwf Hap l1 Hl1 (a1, 0) (or_introl (eq_refl : (a1, 0) = (a1, 0))) He1). }
        rewrite Hmm in Hnm1. discriminate Hnm1.
      }
  - (* ================= x ≠ a1 ================= *)
    destruct (Nat.eqb x a2) eqn:Hx2.
    + (* x = a2 *)
      apply (Nat.eqb_eq x a2) in Hx2. subst x.
      destruct (Nat.leb 1 p) eqn:Hlo.
      * (* p >= 1 *)
        assert (Har : Ar (snd (ru_lhs r)) = Ar β). { rewrite Hlhs. simpl. reflexivity. }
        destruct (Nat.leb p (Ar (snd (ru_lhs r)))) eqn:Hhi.
        ** (* e1 REWIRED to iface[Ar α + p - 1]: a freshened RHS free port *)
          {
            assert (Hrw1 : rw (a2, p) = freshen_pr A N (nth (Ar (fst (ru_lhs r)) + (p - 1)) (ru_iface r) (0, 0))).
            { exact (rewire_endpoint_a2 A Ar N a1 a2 r Hneq12 p Hlo Hhi). }
            rewrite Hrw1 in Heq.
            rewrite Har in Hhi.
            set (pr' := nth (Ar (fst (ru_lhs r)) + (p - 1)) (ru_iface r) (0, 0)).
            apply (freshen_pr_inj A N pr' e2) in Heq.
            assert (Hused : port_used A (ru_rhs r) e2).
            { exists l2. split; [exact Hl2 | exact He2]. }
            rewrite <- Heq in Hused.
            (* The index Ar α + (p - 1) is in range: Ar α + (p - 1) < Ar α + Ar β. *)
            assert (Har1 : Ar (fst (ru_lhs r)) = Ar α). { rewrite Hlhs. simpl. reflexivity. }
            assert (Hir : Ar (fst (ru_lhs r)) + (p - 1) < length (ru_iface r)).
            { apply (proj1 (Nat.leb_le p (Ar β))) in Hhi.
              apply (proj1 (Nat.leb_le 1 p)) in Hlo.
              rewrite Har1.
              rewrite Hlen. lia. }
            assert (Hpr : In pr' (ru_iface r)).
            { exact (nth_In (ru_iface r) (0, 0) Hir). }
            rewrite Hiface in Hpr.
            assert (Hfree : is_free A Ar (ru_rhs r) pr').
            { exact (interface_free A Ar (ru_rhs r) Hrhs pr' Hpr). }
            destruct Hfree as [la [Hal [Hpb Hnotused]]].
            exact (Hnotused Hused).
          }
        ** (* e1 KEPT as (a2, p): a fresh id would be an agent of N *)
          {
            assert (Hrw1 : rw (a2, p) = (a2, p)).
            { exact (rewire_endpoint_a2_out A Ar N a1 a2 r Hneq12 p Hhi). }
            rewrite Hrw1 in Heq.
            exfalso.
            apply (freshen_pr_not_agent_of_N A N e2 a2 p).
            - exact (eq_sym Heq).
            - exact (link_end_agent_present A Ar N Hwf l1 Hl1 (a2, p) He1).
          }
      * (* p = 0: l1 is the main–main link *)
        {
          assert (Hp0 : p = 0).
          { destruct p eqn:Hp.
            - reflexivity.
            - simpl in Hlo. discriminate Hlo. }
          subst p.
          assert (Hmm : is_main_main_link a1 a2 l1 = true).
          { exact (main_port_only_main_link A Ar N a1 a2 Hwf Hap l1 Hl1 (a2, 0) (or_intror (eq_refl : (a2, 0) = (a2, 0))) He1). }
          rewrite Hmm in Hnm1. discriminate Hnm1.
        }
    + (* x ≠ a2: e1 KEPT: a fresh id would be an agent of N *)
      {
        assert (Hrw1 : rw (x, p) = (x, p)).
        { exact (rewire_endpoint_kept A Ar N a1 a2 r x p Hx1 Hx2). }
        rewrite Hrw1 in Heq.
        exfalso.
        apply (freshen_pr_not_agent_of_N A N e2 x p).
        - exact (eq_sym Heq).
        - exact (link_end_agent_present A Ar N Hwf l1 Hl1 (x, p) He1).
      }
Qed.

(** The two ends of a single non-main–main link of [N] do not rewire onto the
    same port: if [l] is a non-main–main link of [N], then
    [rewire_endpoint (fst l)] and [rewire_endpoint (snd l)] differ. This is the
    [N]-origin ingredient of the [wf_ends] field of [raw_splice_wf].

    The proof splits on the agent of each end exactly as
    [rewire_endpoint_inj] does; the kept-kept and fresh-fresh-same-source
    leaves contradict the distinctness of the two ends of [l] ([wf_ends])
    instead of the distinctness of two links. *)
Lemma rewire_endpoint_distinct_ends (A : Type) (Ar : A -> nat) (N : Net A) (a1 a2 : nat) (r : Rule A)
      (α β : A)
      (Hla : agent_label A N a1 = Some α) (Hlb : agent_label A N a2 = Some β)
      (Hlhs : ru_lhs r = (α, β))
      (Hwf : well_formed A Ar N) (Hap : is_active_pair A Ar N a1 a2)
      (Hrhs : well_formed A Ar (ru_rhs r))
      (Hiface : ru_iface r = interface A Ar (ru_rhs r))
      (Hlen : length (ru_iface r) = Ar α + Ar β)
      (l : port_ref * port_ref) (Hl : In l (nt_links N))
      (Hnm : is_main_main_link a1 a2 l = false) :
  rewire_endpoint A Ar N a1 a2 r (fst l) <> rewire_endpoint A Ar N a1 a2 r (snd l).
Proof.
  intro Heq.
  set (rw := fun e : port_ref => rewire_endpoint A Ar N a1 a2 r e).
  change (rw (fst l) = rw (snd l)) in Heq.
  assert (Hneq12 : a1 <> a2).
  { unfold is_active_pair in Hap. destruct Hap as [Hneq12 _]. exact Hneq12. }
  assert (Hends : fst l <> snd l).
  { exact (wf_ends Hwf l Hl). }
  (* [lp] tracks the components of [l] through the destruct (and the later
     [subst]s of [p] and [q]): set-binders are transparent to conversion, so
     [link_end lp e] reduces to a statement about the components. *)
  set (lp := l).
  destruct l as [[x p] [y q]].
  change (rw (x, p) = rw (y, q)) in Heq.
  simpl in Hends.
  (* ================= x = a1 ================= *)
  destruct (Nat.eqb x a1) eqn:Hx1.
  - apply (Nat.eqb_eq x a1) in Hx1. subst x.
    destruct (Nat.leb 1 p) eqn:Hlo.
    + (* p >= 1 *)
      assert (Har : Ar (fst (ru_lhs r)) = Ar α). { rewrite Hlhs. simpl. reflexivity. }
      destruct (Nat.leb p (Ar (fst (ru_lhs r)))) eqn:Hhi.
      * (* e1 REWIRED to iface[p-1] *)
        {
          assert (Hrw1 : rw (a1, p) = freshen_pr A N (nth (p - 1) (ru_iface r) (0, 0))).
          { exact (rewire_endpoint_a1 A Ar N a1 a2 r p Hlo Hhi). }
          rewrite Hrw1 in Heq.
          rewrite Har in Hhi.
          (* ---- y = a1 ---- *)
          destruct (Nat.eqb y a1) eqn:Hy1.
          - apply (Nat.eqb_eq y a1) in Hy1. subst y.
            destruct (Nat.leb 1 q) eqn:Hlo2.
            * (* q >= 1 *)
              assert (Har2 : Ar (fst (ru_lhs r)) = Ar α). { rewrite Hlhs. simpl. reflexivity. }
              destruct (Nat.leb q (Ar (fst (ru_lhs r)))) eqn:Hhi2.
              ** (* e2 REWIRED to iface[q-1]: fresh-fresh, same source agent *)
                {
                  assert (Hrw2 : rw (a1, q) = freshen_pr A N (nth (q - 1) (ru_iface r) (0, 0))).
                  { exact (rewire_endpoint_a1 A Ar N a1 a2 r q Hlo2 Hhi2). }
                  rewrite Hrw2 in Heq.
                  rewrite Har2 in Hhi2.
                  apply (freshen_pr_inj A N (nth (p - 1) (ru_iface r) (0, 0)) (nth (q - 1) (ru_iface r) (0, 0))) in Heq.
                  assert (Hin1 : p - 1 < length (ru_iface r)).
                  { apply (proj1 (Nat.leb_le p (Ar α))) in Hhi.
                    apply (proj1 (Nat.leb_le 1 p)) in Hlo.
                    rewrite Hlen. lia. }
                  assert (Hin2 : q - 1 < length (ru_iface r)).
                  { apply (proj1 (Nat.leb_le q (Ar α))) in Hhi2.
                    apply (proj1 (Nat.leb_le 1 q)) in Hlo2.
                    rewrite Hlen. lia. }
                  assert (Hidx : p - 1 = q - 1).
                  { apply (proj1 (NoDup_nth (ru_iface r) (0, 0))).
                    - exact (iface_nodup A Ar N a1 a2 r Hrhs Hiface).
                    - exact Hin1.
                    - exact Hin2.
                    - exact Heq. }
                  (* p, q >= 1 and p - 1 = q - 1 give p = q, so e1 = e2. *)
                  assert (Hpq : p = q).
                  {
                    destruct p as [|p'].
                    - exfalso.
                      assert (Ht : Nat.leb 1 0 = false). { simpl. reflexivity. }
                      rewrite Ht in Hlo. discriminate Hlo.
                    - destruct q as [|q'].
                      + exfalso.
                        assert (Ht : Nat.leb 1 0 = false). { simpl. reflexivity. }
                        rewrite Ht in Hlo2. discriminate Hlo2.
                      + simpl in Hidx.
                        f_equal.
                        rewrite !Nat.sub_0_r in Hidx.
                        exact Hidx.
                  }
                  exfalso.
                  apply Hends.
                  subst q.
                  reflexivity.
                }
              ** (* e2 KEPT as (a1, q): fresh-kept *)
                {
                  assert (Hrw2 : rw (a1, q) = (a1, q)).
                  { exact (rewire_endpoint_a1_out A Ar N a1 a2 r q Hhi2). }
                  rewrite Hrw2 in Heq.
                  exfalso.
                  apply (freshen_pr_not_agent_of_N A N (nth (p - 1) (ru_iface r) (0, 0)) a1 q).
                  - exact Heq.
                  - exact (link_end_agent_present A Ar N Hwf lp Hl (a1, q) (or_intror eq_refl)).
                }
            * (* q = 0: l is the main–main link *)
              {
                assert (Hq0 : q = 0).
                { destruct q eqn:Hq.
                  - reflexivity.
                  - simpl in Hlo2. discriminate Hlo2. }
                subst q.
                assert (Hmm : is_main_main_link a1 a2 lp = true).
                { exact (main_port_only_main_link A Ar N a1 a2 Hwf Hap lp Hl (a1, 0) (or_introl (eq_refl : (a1, 0) = (a1, 0))) (or_intror eq_refl)). }
                change (is_main_main_link a1 a2 lp = false) in Hnm.
                rewrite Hmm in Hnm. discriminate Hnm.
              }
          - (* y ≠ a1 *)
            destruct (Nat.eqb y a2) eqn:Hy2.
            + (* y = a2 *)
              apply (Nat.eqb_eq y a2) in Hy2. subst y.
              destruct (Nat.leb 1 q) eqn:Hlo2.
              * (* q >= 1 *)
                assert (Har2 : Ar (snd (ru_lhs r)) = Ar β). { rewrite Hlhs. simpl. reflexivity. }
                destruct (Nat.leb q (Ar (snd (ru_lhs r)))) eqn:Hhi2.
                ** (* e2 REWIRED to iface[Ar α + q - 1]: fresh-fresh, different source agents *)
                  {
                    assert (Hrw2 : rw (a2, q) = freshen_pr A N (nth (Ar (fst (ru_lhs r)) + (q - 1)) (ru_iface r) (0, 0))).
                    { exact (rewire_endpoint_a2 A Ar N a1 a2 r Hneq12 q Hlo2 Hhi2). }
                    rewrite Hrw2 in Heq.
                    rewrite Har2 in Hhi2.
                    apply (freshen_pr_inj A N (nth (p - 1) (ru_iface r) (0, 0)) (nth (Ar (fst (ru_lhs r)) + (q - 1)) (ru_iface r) (0, 0))) in Heq.
                    assert (Hin1 : p - 1 < length (ru_iface r)).
                    { apply (proj1 (Nat.leb_le p (Ar α))) in Hhi.
                      apply (proj1 (Nat.leb_le 1 p)) in Hlo.
                      rewrite Hlen. lia. }
                    assert (Har1 : Ar (fst (ru_lhs r)) = Ar α). { rewrite Hlhs. simpl. reflexivity. }
                    assert (Hin2 : Ar (fst (ru_lhs r)) + (q - 1) < length (ru_iface r)).
                    { apply (proj1 (Nat.leb_le q (Ar β))) in Hhi2.
                      apply (proj1 (Nat.leb_le 1 q)) in Hlo2.
                      rewrite Har1.
                      rewrite Hlen. lia. }
                    assert (Hidx : p - 1 = Ar (fst (ru_lhs r)) + (q - 1)).
                    { apply (proj1 (NoDup_nth (ru_iface r) (0, 0))).
                      - exact (iface_nodup A Ar N a1 a2 r Hrhs Hiface).
                      - exact Hin1.
                      - exact Hin2.
                      - exact Heq. }
                    (* p - 1 = Ar α + (q - 1) >= Ar α, so p >= Ar α + 1, but p <= Ar α. *)
                    assert (Hp : p <= Ar α). { apply (proj1 (Nat.leb_le p (Ar α))). exact Hhi. }
                    assert (Hp1 : 1 <= p). { apply (proj1 (Nat.leb_le 1 p)). exact Hlo. }
                    assert (Hq1 : 1 <= q). { apply (proj1 (Nat.leb_le 1 q)). exact Hlo2. }
                    exfalso.
                    rewrite Har1 in Hidx.
                    lia.
                  }
                ** (* e2 KEPT as (a2, q): fresh-kept *)
                  {
                    assert (Hrw2 : rw (a2, q) = (a2, q)).
                    { exact (rewire_endpoint_a2_out A Ar N a1 a2 r Hneq12 q Hhi2). }
                    rewrite Hrw2 in Heq.
                    exfalso.
                    apply (freshen_pr_not_agent_of_N A N (nth (p - 1) (ru_iface r) (0, 0)) a2 q).
                    - exact Heq.
                    - exact (link_end_agent_present A Ar N Hwf lp Hl (a2, q) (or_intror eq_refl)).
                  }
              * (* q = 0: l is the main–main link *)
                {
                  assert (Hq0 : q = 0).
                  { destruct q eqn:Hq.
                    - reflexivity.
                    - simpl in Hlo2. discriminate Hlo2. }
                  subst q.
                  assert (Hmm : is_main_main_link a1 a2 lp = true).
                  { exact (main_port_only_main_link A Ar N a1 a2 Hwf Hap lp Hl (a2, 0) (or_intror (eq_refl : (a2, 0) = (a2, 0))) (or_intror eq_refl)). }
                  change (is_main_main_link a1 a2 lp = false) in Hnm.
                  rewrite Hmm in Hnm. discriminate Hnm.
                }
            + (* y ≠ a2: e2 KEPT *)
              {
                assert (Hrw2 : rw (y, q) = (y, q)).
                { exact (rewire_endpoint_kept A Ar N a1 a2 r y q Hy1 Hy2). }
                rewrite Hrw2 in Heq.
                exfalso.
                apply (freshen_pr_not_agent_of_N A N (nth (p - 1) (ru_iface r) (0, 0)) y q).
                - exact Heq.
                - exact (link_end_agent_present A Ar N Hwf lp Hl (y, q) (or_intror eq_refl)).
              }
        }
      * (* e1 KEPT as (a1, p) [p > Ar α] *)
        {
          assert (Hrw1 : rw (a1, p) = (a1, p)).
          { exact (rewire_endpoint_a1_out A Ar N a1 a2 r p Hhi). }
          rewrite Hrw1 in Heq.
          (* ---- y = a1 ---- *)
          destruct (Nat.eqb y a1) eqn:Hy1.
          - apply (Nat.eqb_eq y a1) in Hy1. subst y.
            destruct (Nat.leb 1 q) eqn:Hlo2.
            * (* q >= 1 *)
              assert (Har2 : Ar (fst (ru_lhs r)) = Ar α). { rewrite Hlhs. simpl. reflexivity. }
              destruct (Nat.leb q (Ar (fst (ru_lhs r)))) eqn:Hhi2.
              ** (* e2 REWIRED to iface[q-1]: kept-fresh *)
                {
                  assert (Hrw2 : rw (a1, q) = freshen_pr A N (nth (q - 1) (ru_iface r) (0, 0))).
                  { exact (rewire_endpoint_a1 A Ar N a1 a2 r q Hlo2 Hhi2). }
                  rewrite Hrw2 in Heq.
                  exfalso.
                  apply (freshen_pr_not_agent_of_N A N (nth (q - 1) (ru_iface r) (0, 0)) a1 p).
                  - symmetry. exact Heq.
                  - exact (link_end_agent_present A Ar N Hwf lp Hl (a1, p) (or_introl eq_refl)).
                }
              ** (* e2 KEPT as (a1, q): kept-kept *)
                {
                  assert (Hrw2 : rw (a1, q) = (a1, q)).
                  { exact (rewire_endpoint_a1_out A Ar N a1 a2 r q Hhi2). }
                  rewrite Hrw2 in Heq.
                  exfalso.
                  apply Hends.
                  exact Heq.
                }
            * (* q = 0: l is the main–main link *)
              {
                assert (Hq0 : q = 0).
                { destruct q eqn:Hq.
                  - reflexivity.
                  - simpl in Hlo2. discriminate Hlo2. }
                subst q.
                assert (Hmm : is_main_main_link a1 a2 lp = true).
                { exact (main_port_only_main_link A Ar N a1 a2 Hwf Hap lp Hl (a1, 0) (or_introl (eq_refl : (a1, 0) = (a1, 0))) (or_intror eq_refl)). }
                change (is_main_main_link a1 a2 lp = false) in Hnm.
                rewrite Hmm in Hnm. discriminate Hnm.
              }
          - (* y ≠ a1 *)
            destruct (Nat.eqb y a2) eqn:Hy2.
            + (* y = a2 *)
              apply (Nat.eqb_eq y a2) in Hy2. subst y.
              destruct (Nat.leb 1 q) eqn:Hlo2.
              * (* q >= 1 *)
                assert (Har2 : Ar (snd (ru_lhs r)) = Ar β). { rewrite Hlhs. simpl. reflexivity. }
                destruct (Nat.leb q (Ar (snd (ru_lhs r)))) eqn:Hhi2.
                ** (* e2 REWIRED to iface[Ar α + q - 1]: kept-fresh *)
                  {
                    assert (Hrw2 : rw (a2, q) = freshen_pr A N (nth (Ar (fst (ru_lhs r)) + (q - 1)) (ru_iface r) (0, 0))).
                    { exact (rewire_endpoint_a2 A Ar N a1 a2 r Hneq12 q Hlo2 Hhi2). }
                    rewrite Hrw2 in Heq.
                    exfalso.
                    apply (freshen_pr_not_agent_of_N A N (nth (Ar (fst (ru_lhs r)) + (q - 1)) (ru_iface r) (0, 0)) a1 p).
                    - symmetry. exact Heq.
                    - exact (link_end_agent_present A Ar N Hwf lp Hl (a1, p) (or_introl eq_refl)).
                  }
                ** (* e2 KEPT as (a2, q): kept-kept *)
                  {
                    assert (Hrw2 : rw (a2, q) = (a2, q)).
                    { exact (rewire_endpoint_a2_out A Ar N a1 a2 r Hneq12 q Hhi2). }
                    rewrite Hrw2 in Heq.
                    exfalso.
                    apply Hends.
                    exact Heq.
                  }
              * (* q = 0: l is the main–main link *)
                {
                  assert (Hq0 : q = 0).
                  { destruct q eqn:Hq.
                    - reflexivity.
                    - simpl in Hlo2. discriminate Hlo2. }
                  subst q.
                  assert (Hmm : is_main_main_link a1 a2 lp = true).
                  { exact (main_port_only_main_link A Ar N a1 a2 Hwf Hap lp Hl (a2, 0) (or_intror (eq_refl : (a2, 0) = (a2, 0))) (or_intror eq_refl)). }
                  change (is_main_main_link a1 a2 lp = false) in Hnm.
                  rewrite Hmm in Hnm. discriminate Hnm.
                }
            + (* y ≠ a2: e2 KEPT: kept-kept *)
              {
                assert (Hrw2 : rw (y, q) = (y, q)).
                { exact (rewire_endpoint_kept A Ar N a1 a2 r y q Hy1 Hy2). }
                rewrite Hrw2 in Heq.
                exfalso.
                apply Hends.
                exact Heq.
              }
        }
    + (* p = 0: l is the main–main link *)
      {
        assert (Hp0 : p = 0).
        { destruct p eqn:Hp.
          - reflexivity.
          - simpl in Hlo. discriminate Hlo. }
        subst p.
        assert (Hmm : is_main_main_link a1 a2 lp = true).
        { exact (main_port_only_main_link A Ar N a1 a2 Hwf Hap lp Hl (a1, 0) (or_introl (eq_refl : (a1, 0) = (a1, 0))) (or_introl eq_refl)). }
        change (is_main_main_link a1 a2 lp = false) in Hnm.
        rewrite Hmm in Hnm. discriminate Hnm.
      }
  - (* ================= x ≠ a1 ================= *)
    destruct (Nat.eqb x a2) eqn:Hx2.
    + (* x = a2 *)
      apply (Nat.eqb_eq x a2) in Hx2. subst x.
      destruct (Nat.leb 1 p) eqn:Hlo.
      * (* p >= 1 *)
        assert (Har : Ar (snd (ru_lhs r)) = Ar β). { rewrite Hlhs. simpl. reflexivity. }
        destruct (Nat.leb p (Ar (snd (ru_lhs r)))) eqn:Hhi.
        ** (* e1 REWIRED to iface[Ar α + p - 1] *)
          {
            assert (Hrw1 : rw (a2, p) = freshen_pr A N (nth (Ar (fst (ru_lhs r)) + (p - 1)) (ru_iface r) (0, 0))).
            { exact (rewire_endpoint_a2 A Ar N a1 a2 r Hneq12 p Hlo Hhi). }
            rewrite Hrw1 in Heq.
            rewrite Har in Hhi.
            (* ---- y = a1 ---- *)
            destruct (Nat.eqb y a1) eqn:Hy1.
            - apply (Nat.eqb_eq y a1) in Hy1. subst y.
              destruct (Nat.leb 1 q) eqn:Hlo2.
              * (* q >= 1 *)
                assert (Har2 : Ar (fst (ru_lhs r)) = Ar α). { rewrite Hlhs. simpl. reflexivity. }
                destruct (Nat.leb q (Ar (fst (ru_lhs r)))) eqn:Hhi2.
                ** (* e2 REWIRED to iface[q-1]: fresh-fresh, different source agents *)
                  {
                    assert (Hrw2 : rw (a1, q) = freshen_pr A N (nth (q - 1) (ru_iface r) (0, 0))).
                    { exact (rewire_endpoint_a1 A Ar N a1 a2 r q Hlo2 Hhi2). }
                    rewrite Hrw2 in Heq.
                    rewrite Har2 in Hhi2.
                    apply (freshen_pr_inj A N (nth (Ar (fst (ru_lhs r)) + (p - 1)) (ru_iface r) (0, 0)) (nth (q - 1) (ru_iface r) (0, 0))) in Heq.
                    assert (Har1 : Ar (fst (ru_lhs r)) = Ar α). { rewrite Hlhs. simpl. reflexivity. }
                    assert (Hin1 : Ar (fst (ru_lhs r)) + (p - 1) < length (ru_iface r)).
                    { apply (proj1 (Nat.leb_le p (Ar β))) in Hhi.
                      apply (proj1 (Nat.leb_le 1 p)) in Hlo.
                      rewrite Har1.
                      rewrite Hlen. lia. }
                    assert (Hin2 : q - 1 < length (ru_iface r)).
                    { apply (proj1 (Nat.leb_le q (Ar α))) in Hhi2.
                      apply (proj1 (Nat.leb_le 1 q)) in Hlo2.
                      rewrite Hlen. lia. }
                    assert (Hidx : Ar (fst (ru_lhs r)) + (p - 1) = q - 1).
                    { apply (proj1 (NoDup_nth (ru_iface r) (0, 0))).
                      - exact (iface_nodup A Ar N a1 a2 r Hrhs Hiface).
                      - exact Hin1.
                      - exact Hin2.
                      - exact Heq. }
                    (* Ar α + (p - 1) = q - 1, so q = Ar α + p >= Ar α + 1, but q <= Ar α. *)
                    assert (Hq : q <= Ar α). { apply (proj1 (Nat.leb_le q (Ar α))). exact Hhi2. }
                    assert (Hp1 : 1 <= p). { apply (proj1 (Nat.leb_le 1 p)). exact Hlo. }
                    assert (Hq1 : 1 <= q). { apply (proj1 (Nat.leb_le 1 q)). exact Hlo2. }
                    exfalso.
                    rewrite Har1 in Hidx.
                    lia.
                  }
                ** (* e2 KEPT as (a1, q): fresh-kept *)
                  {
                    assert (Hrw2 : rw (a1, q) = (a1, q)).
                    { exact (rewire_endpoint_a1_out A Ar N a1 a2 r q Hhi2). }
                    rewrite Hrw2 in Heq.
                    exfalso.
                    apply (freshen_pr_not_agent_of_N A N (nth (Ar (fst (ru_lhs r)) + (p - 1)) (ru_iface r) (0, 0)) a1 q).
                    - exact Heq.
                    - exact (link_end_agent_present A Ar N Hwf lp Hl (a1, q) (or_intror eq_refl)).
                  }
              * (* q = 0: l is the main–main link *)
                {
                  assert (Hq0 : q = 0).
                  { destruct q eqn:Hq.
                    - reflexivity.
                    - simpl in Hlo2. discriminate Hlo2. }
                  subst q.
                  assert (Hmm : is_main_main_link a1 a2 lp = true).
                  { exact (main_port_only_main_link A Ar N a1 a2 Hwf Hap lp Hl (a1, 0) (or_introl (eq_refl : (a1, 0) = (a1, 0))) (or_intror eq_refl)). }
                  change (is_main_main_link a1 a2 lp = false) in Hnm.
                  rewrite Hmm in Hnm. discriminate Hnm.
                }
            - (* y ≠ a1 *)
              destruct (Nat.eqb y a2) eqn:Hy2.
              + (* y = a2 *)
                apply (Nat.eqb_eq y a2) in Hy2. subst y.
                destruct (Nat.leb 1 q) eqn:Hlo2.
                * (* q >= 1 *)
                  assert (Har2 : Ar (snd (ru_lhs r)) = Ar β). { rewrite Hlhs. simpl. reflexivity. }
                  destruct (Nat.leb q (Ar (snd (ru_lhs r)))) eqn:Hhi2.
                  ** (* e2 REWIRED to iface[Ar α + q - 1]: fresh-fresh, same source agent *)
                    {
                      assert (Hrw2 : rw (a2, q) = freshen_pr A N (nth (Ar (fst (ru_lhs r)) + (q - 1)) (ru_iface r) (0, 0))).
                      { exact (rewire_endpoint_a2 A Ar N a1 a2 r Hneq12 q Hlo2 Hhi2). }
                      rewrite Hrw2 in Heq.
                      rewrite Har2 in Hhi2.
                      apply (freshen_pr_inj A N (nth (Ar (fst (ru_lhs r)) + (p - 1)) (ru_iface r) (0, 0)) (nth (Ar (fst (ru_lhs r)) + (q - 1)) (ru_iface r) (0, 0))) in Heq.
                      assert (Har1 : Ar (fst (ru_lhs r)) = Ar α). { rewrite Hlhs. simpl. reflexivity. }
                      assert (Hin1 : Ar (fst (ru_lhs r)) + (p - 1) < length (ru_iface r)).
                      { apply (proj1 (Nat.leb_le p (Ar β))) in Hhi.
                        apply (proj1 (Nat.leb_le 1 p)) in Hlo.
                        rewrite Har1.
                        rewrite Hlen. lia. }
                      assert (Hin2 : Ar (fst (ru_lhs r)) + (q - 1) < length (ru_iface r)).
                      { apply (proj1 (Nat.leb_le q (Ar β))) in Hhi2.
                        apply (proj1 (Nat.leb_le 1 q)) in Hlo2.
                        rewrite Har1.
                        rewrite Hlen. lia. }
                      assert (Hidx : Ar (fst (ru_lhs r)) + (p - 1) = Ar (fst (ru_lhs r)) + (q - 1)).
                      { apply (proj1 (NoDup_nth (ru_iface r) (0, 0))).
                        - exact (iface_nodup A Ar N a1 a2 r Hrhs Hiface).
                        - exact Hin1.
                        - exact Hin2.
                        - exact Heq. }
                      (* Ar α + (p - 1) = Ar α + (q - 1), so p - 1 = q - 1, so p = q, so e1 = e2. *)
                      assert (Hpq : p = q).
                      {
                        apply Nat.add_cancel_l in Hidx.
                        destruct p as [|p'].
                        - exfalso.
                          assert (Ht : Nat.leb 1 0 = false). { simpl. reflexivity. }
                          rewrite Ht in Hlo. discriminate Hlo.
                        - destruct q as [|q'].
                          + exfalso.
                            assert (Ht : Nat.leb 1 0 = false). { simpl. reflexivity. }
                            rewrite Ht in Hlo2. discriminate Hlo2.
                          + simpl in Hidx.
                            f_equal.
                            rewrite !Nat.sub_0_r in Hidx.
                            exact Hidx.
                      }
                      exfalso.
                      apply Hends.
                      subst q.
                      reflexivity.
                    }
                  ** (* e2 KEPT as (a2, q): fresh-kept *)
                    {
                      assert (Hrw2 : rw (a2, q) = (a2, q)).
                      { exact (rewire_endpoint_a2_out A Ar N a1 a2 r Hneq12 q Hhi2). }
                      rewrite Hrw2 in Heq.
                      exfalso.
                      apply (freshen_pr_not_agent_of_N A N (nth (Ar (fst (ru_lhs r)) + (p - 1)) (ru_iface r) (0, 0)) a2 q).
                      - exact Heq.
                      - exact (link_end_agent_present A Ar N Hwf lp Hl (a2, q) (or_intror eq_refl)).
                    }
                * (* q = 0: l is the main–main link *)
                  {
                    assert (Hq0 : q = 0).
                    { destruct q eqn:Hq.
                      - reflexivity.
                      - simpl in Hlo2. discriminate Hlo2. }
                    subst q.
                    assert (Hmm : is_main_main_link a1 a2 lp = true).
                    { exact (main_port_only_main_link A Ar N a1 a2 Hwf Hap lp Hl (a2, 0) (or_intror (eq_refl : (a2, 0) = (a2, 0))) (or_intror eq_refl)). }
                    change (is_main_main_link a1 a2 lp = false) in Hnm.
                    rewrite Hmm in Hnm. discriminate Hnm.
                  }
              + (* y ≠ a2: e2 KEPT *)
                {
                  assert (Hrw2 : rw (y, q) = (y, q)).
                  { exact (rewire_endpoint_kept A Ar N a1 a2 r y q Hy1 Hy2). }
                  rewrite Hrw2 in Heq.
                  exfalso.
                  apply (freshen_pr_not_agent_of_N A N (nth (Ar (fst (ru_lhs r)) + (p - 1)) (ru_iface r) (0, 0)) y q).
                  - exact Heq.
                  - exact (link_end_agent_present A Ar N Hwf lp Hl (y, q) (or_intror eq_refl)).
                }
          }
        ** (* e1 KEPT as (a2, p) [p > Ar β] *)
          {
            assert (Hrw1 : rw (a2, p) = (a2, p)).
            { exact (rewire_endpoint_a2_out A Ar N a1 a2 r Hneq12 p Hhi). }
            rewrite Hrw1 in Heq.
            (* ---- y = a1 ---- *)
            destruct (Nat.eqb y a1) eqn:Hy1.
            - apply (Nat.eqb_eq y a1) in Hy1. subst y.
              destruct (Nat.leb 1 q) eqn:Hlo2.
              * (* q >= 1 *)
                assert (Har2 : Ar (fst (ru_lhs r)) = Ar α). { rewrite Hlhs. simpl. reflexivity. }
                destruct (Nat.leb q (Ar (fst (ru_lhs r)))) eqn:Hhi2.
                ** (* e2 REWIRED to iface[q-1]: kept-fresh *)
                  {
                    assert (Hrw2 : rw (a1, q) = freshen_pr A N (nth (q - 1) (ru_iface r) (0, 0))).
                    { exact (rewire_endpoint_a1 A Ar N a1 a2 r q Hlo2 Hhi2). }
                    rewrite Hrw2 in Heq.
                    exfalso.
                    apply (freshen_pr_not_agent_of_N A N (nth (q - 1) (ru_iface r) (0, 0)) a2 p).
                    - symmetry. exact Heq.
                    - exact (link_end_agent_present A Ar N Hwf lp Hl (a2, p) (or_introl eq_refl)).
                  }
                ** (* e2 KEPT as (a1, q): kept-kept *)
                  {
                    assert (Hrw2 : rw (a1, q) = (a1, q)).
                    { exact (rewire_endpoint_a1_out A Ar N a1 a2 r q Hhi2). }
                    rewrite Hrw2 in Heq.
                    exfalso.
                    apply Hends.
                    exact Heq.
                  }
              * (* q = 0: l is the main–main link *)
                {
                  assert (Hq0 : q = 0).
                  { destruct q eqn:Hq.
                    - reflexivity.
                    - simpl in Hlo2. discriminate Hlo2. }
                  subst q.
                  assert (Hmm : is_main_main_link a1 a2 lp = true).
                  { exact (main_port_only_main_link A Ar N a1 a2 Hwf Hap lp Hl (a1, 0) (or_introl (eq_refl : (a1, 0) = (a1, 0))) (or_intror eq_refl)). }
                  change (is_main_main_link a1 a2 lp = false) in Hnm.
                  rewrite Hmm in Hnm. discriminate Hnm.
                }
            - (* y ≠ a1 *)
              destruct (Nat.eqb y a2) eqn:Hy2.
              + (* y = a2 *)
                apply (Nat.eqb_eq y a2) in Hy2. subst y.
                destruct (Nat.leb 1 q) eqn:Hlo2.
                * (* q >= 1 *)
                  assert (Har2 : Ar (snd (ru_lhs r)) = Ar β). { rewrite Hlhs. simpl. reflexivity. }
                  destruct (Nat.leb q (Ar (snd (ru_lhs r)))) eqn:Hhi2.
                  ** (* e2 REWIRED to iface[Ar α + q - 1]: kept-fresh *)
                    {
                      assert (Hrw2 : rw (a2, q) = freshen_pr A N (nth (Ar (fst (ru_lhs r)) + (q - 1)) (ru_iface r) (0, 0))).
                      { exact (rewire_endpoint_a2 A Ar N a1 a2 r Hneq12 q Hlo2 Hhi2). }
                      rewrite Hrw2 in Heq.
                      exfalso.
                      apply (freshen_pr_not_agent_of_N A N (nth (Ar (fst (ru_lhs r)) + (q - 1)) (ru_iface r) (0, 0)) a2 p).
                      - symmetry. exact Heq.
                      - exact (link_end_agent_present A Ar N Hwf lp Hl (a2, p) (or_introl eq_refl)).
                    }
                  ** (* e2 KEPT as (a2, q): kept-kept *)
                    {
                      assert (Hrw2 : rw (a2, q) = (a2, q)).
                      { exact (rewire_endpoint_a2_out A Ar N a1 a2 r Hneq12 q Hhi2). }
                      rewrite Hrw2 in Heq.
                      exfalso.
                      apply Hends.
                      exact Heq.
                    }
                * (* q = 0: l is the main–main link *)
                  {
                    assert (Hq0 : q = 0).
                    { destruct q eqn:Hq.
                      - reflexivity.
                      - simpl in Hlo2. discriminate Hlo2. }
                    subst q.
                    assert (Hmm : is_main_main_link a1 a2 lp = true).
                    { exact (main_port_only_main_link A Ar N a1 a2 Hwf Hap lp Hl (a2, 0) (or_intror (eq_refl : (a2, 0) = (a2, 0))) (or_intror eq_refl)). }
                    change (is_main_main_link a1 a2 lp = false) in Hnm.
                    rewrite Hmm in Hnm. discriminate Hnm.
                  }
              + (* y ≠ a2: e2 KEPT: kept-kept *)
                {
                  assert (Hrw2 : rw (y, q) = (y, q)).
                  { exact (rewire_endpoint_kept A Ar N a1 a2 r y q Hy1 Hy2). }
                  rewrite Hrw2 in Heq.
                  exfalso.
                  apply Hends.
                  exact Heq.
                }
          }
      * (* p = 0: l is the main–main link *)
        {
          assert (Hp0 : p = 0).
          { destruct p eqn:Hp.
            - reflexivity.
            - simpl in Hlo. discriminate Hlo. }
          subst p.
          assert (Hmm : is_main_main_link a1 a2 lp = true).
          { exact (main_port_only_main_link A Ar N a1 a2 Hwf Hap lp Hl (a2, 0) (or_intror (eq_refl : (a2, 0) = (a2, 0))) (or_introl eq_refl)). }
          change (is_main_main_link a1 a2 lp = false) in Hnm.
          rewrite Hmm in Hnm. discriminate Hnm.
        }
    + (* x ≠ a2: e1 KEPT *)
      {
        assert (Hrw1 : rw (x, p) = (x, p)).
        { exact (rewire_endpoint_kept A Ar N a1 a2 r x p Hx1 Hx2). }
        rewrite Hrw1 in Heq.
        (* ---- y = a1 ---- *)
        destruct (Nat.eqb y a1) eqn:Hy1.
        - apply (Nat.eqb_eq y a1) in Hy1. subst y.
          destruct (Nat.leb 1 q) eqn:Hlo2.
          * (* q >= 1 *)
            assert (Har2 : Ar (fst (ru_lhs r)) = Ar α). { rewrite Hlhs. simpl. reflexivity. }
            destruct (Nat.leb q (Ar (fst (ru_lhs r)))) eqn:Hhi2.
            ** (* e2 REWIRED to iface[q-1]: kept-fresh *)
              {
                assert (Hrw2 : rw (a1, q) = freshen_pr A N (nth (q - 1) (ru_iface r) (0, 0))).
                { exact (rewire_endpoint_a1 A Ar N a1 a2 r q Hlo2 Hhi2). }
                rewrite Hrw2 in Heq.
                exfalso.
                apply (freshen_pr_not_agent_of_N A N (nth (q - 1) (ru_iface r) (0, 0)) x p).
                - symmetry. exact Heq.
                - exact (link_end_agent_present A Ar N Hwf lp Hl (x, p) (or_introl eq_refl)).
              }
            ** (* e2 KEPT as (a1, q): kept-kept *)
              {
                assert (Hrw2 : rw (a1, q) = (a1, q)).
                { exact (rewire_endpoint_a1_out A Ar N a1 a2 r q Hhi2). }
                rewrite Hrw2 in Heq.
                exfalso.
                apply Hends.
                exact Heq.
              }
          * (* q = 0: l is the main–main link *)
            {
              assert (Hq0 : q = 0).
              { destruct q eqn:Hq.
                - reflexivity.
                - simpl in Hlo2. discriminate Hlo2. }
              subst q.
              assert (Hmm : is_main_main_link a1 a2 lp = true).
              { exact (main_port_only_main_link A Ar N a1 a2 Hwf Hap lp Hl (a1, 0) (or_introl (eq_refl : (a1, 0) = (a1, 0))) (or_intror eq_refl)). }
              change (is_main_main_link a1 a2 lp = false) in Hnm.
              rewrite Hmm in Hnm. discriminate Hnm.
            }
        - (* y ≠ a1 *)
          destruct (Nat.eqb y a2) eqn:Hy2.
          + (* y = a2 *)
            apply (Nat.eqb_eq y a2) in Hy2. subst y.
            destruct (Nat.leb 1 q) eqn:Hlo2.
            * (* q >= 1 *)
              assert (Har2 : Ar (snd (ru_lhs r)) = Ar β). { rewrite Hlhs. simpl. reflexivity. }
              destruct (Nat.leb q (Ar (snd (ru_lhs r)))) eqn:Hhi2.
              ** (* e2 REWIRED to iface[Ar α + q - 1]: kept-fresh *)
                {
                  assert (Hrw2 : rw (a2, q) = freshen_pr A N (nth (Ar (fst (ru_lhs r)) + (q - 1)) (ru_iface r) (0, 0))).
                  { exact (rewire_endpoint_a2 A Ar N a1 a2 r Hneq12 q Hlo2 Hhi2). }
                  rewrite Hrw2 in Heq.
                  exfalso.
                  apply (freshen_pr_not_agent_of_N A N (nth (Ar (fst (ru_lhs r)) + (q - 1)) (ru_iface r) (0, 0)) x p).
                  - symmetry. exact Heq.
                  - exact (link_end_agent_present A Ar N Hwf lp Hl (x, p) (or_introl eq_refl)).
                }
              ** (* e2 KEPT as (a2, q): kept-kept *)
                {
                  assert (Hrw2 : rw (a2, q) = (a2, q)).
                  { exact (rewire_endpoint_a2_out A Ar N a1 a2 r Hneq12 q Hhi2). }
                  rewrite Hrw2 in Heq.
                  exfalso.
                  apply Hends.
                  exact Heq.
                }
            * (* q = 0: l is the main–main link *)
              {
                assert (Hq0 : q = 0).
                { destruct q eqn:Hq.
                  - reflexivity.
                  - simpl in Hlo2. discriminate Hlo2. }
                subst q.
                assert (Hmm : is_main_main_link a1 a2 lp = true).
                { exact (main_port_only_main_link A Ar N a1 a2 Hwf Hap lp Hl (a2, 0) (or_intror (eq_refl : (a2, 0) = (a2, 0))) (or_intror eq_refl)). }
                change (is_main_main_link a1 a2 lp = false) in Hnm.
                rewrite Hmm in Hnm. discriminate Hnm.
              }
          + (* y ≠ a2: e2 KEPT: kept-kept *)
            {
              assert (Hrw2 : rw (y, q) = (y, q)).
              { exact (rewire_endpoint_kept A Ar N a1 a2 r y q Hy1 Hy2). }
              rewrite Hrw2 in Heq.
              exfalso.
              apply Hends.
              exact Heq.
            }
      }
Qed.

(** The raw splice of a well-formed net at an active pair, using a rule whose
    RHS is well-formed and whose interface matches the RHS, is well-formed.
    This is the central correctness lemma of §4.5a: [step_pres_wf] invokes it
    with the system-validity premises supplying the RHS premises.

    The four fields are proved by origin: every agent or link of the splice is
    either *kept* from [N] (or *rewired*, in the case of links) or *freshened*
    from the RHS. The freshening scheme ([fresh_id]) makes the freshened part
    disjoint from [N]'s, and the boundary convention makes the rewired
    endpoints land on freshened RHS free ports, which no link of the RHS uses. *)
Lemma raw_splice_wf (A : Type) (Ar : A -> nat) (N : Net A) (a1 a2 : nat) (r : Rule A)
      (α β : A)
      (Hla : agent_label A N a1 = Some α) (Hlb : agent_label A N a2 = Some β)
      (Hlhs : ru_lhs r = (α, β))
      (Hwf : well_formed A Ar N) (Hap : is_active_pair A Ar N a1 a2)
      (Hrhs : well_formed A Ar (ru_rhs r))
      (Hiface : ru_iface r = interface A Ar (ru_rhs r))
      (Hlen : length (ru_iface r) = Ar α + Ar β) :
  well_formed A Ar (raw_splice A Ar N a1 a2 r).
Proof.
  set (sp := raw_splice A Ar N a1 a2 r).
  set (rw := fun e : port_ref => rewire_endpoint A Ar N a1 a2 r e).
  set (rwlink := fun l : port_ref * port_ref => rewire_link A Ar N a1 a2 r l).
  set (frlink := fun l : port_ref * port_ref => (freshen_pr A N (fst l), freshen_pr A N (snd l))).
  set (fresh := fun p : nat * A => (fresh_id A N (fst p), snd p)).
  set (Q := fun l : port_ref * port_ref => negb (is_main_main_link a1 a2 l)).
  set (Qid := fun a : nat => negb (Nat.eqb a a1) && negb (Nat.eqb a a2)).
  change (well_formed A Ar sp).
  constructor.
  (* ==================== wf_ids ==================== *)
  - (* NoDup (map fst (nt_agents sp)) *)
    simpl.
    unfold splice_agents.
    change (NoDup (map fst (filter (fun p : nat * A => Qid (fst p)) (nt_agents N) ++ map fresh (nt_agents (ru_rhs r))))).
    rewrite map_app.
    rewrite (map_fst_filter_fst A Qid (nt_agents N)).
    apply NoDup_app.
    + (* kept part: NoDup is inherited from N *)
      apply NoDup_filter.
      exact (wf_ids Hwf).
    + (* freshened RHS part: freshening is injective on the RHS ids *)
      rewrite (map_map fresh fst (nt_agents (ru_rhs r))).
      simpl.
      apply (Injective_map_NoDup_in (fun p : nat * A => fresh_id A N (fst p))).
      * intros p1 p2 Hp1 Hp2 H.
        apply (fresh_id_inj A N (fst p1) (fst p2)) in H.
        destruct p1 as [x la1]; destruct p2 as [x' la2].
        simpl in H.
        subst x'.
        assert (Hlaeq : la1 = la2).
        { exact (wf_ids_functional Hrhs x la1 la2 Hp1 Hp2). }
        subst la2.
        reflexivity.
      * exact (nodup_fst_nodup A (nt_agents (ru_rhs r)) (wf_ids Hrhs)).
    + (* disjoint: a fresh id is not an id of N *)
      intros x Hx1 Hx2.
      rewrite (map_map fresh fst (nt_agents (ru_rhs r))) in Hx2.
      simpl in Hx2.
      apply (In_map_inv (fun p : nat * A => fresh_id A N (fst p)) (nt_agents (ru_rhs r)) x) in Hx2 as [p [Hp Hxp]].
      apply (fresh_id_notin_N A N (fst p)).
      rewrite Hxp.
      apply (proj1 (filter_In Qid x (map fst (nt_agents N)))) in Hx1.
      destruct Hx1 as [Hx1' _].
      exact Hx1'.
  (* ==================== wf_links ==================== *)
  - (* every link joins present agents with in-range ports *)
    intros a b p q Hl.
    simpl in Hl.
    apply (in_app_or (map rwlink (filter Q (nt_links N))) (map frlink (nt_links (ru_rhs r))) ((a, p), (b, q))) in Hl.
    destruct Hl as [Hl|Hl].
    + (* N-origin: ((a,p),(b,q)) = rwlink l' for a non-main–main link l' of N *)
      apply (In_map_inv rwlink (filter Q (nt_links N)) ((a, p), (b, q))) in Hl as [l' [Hl' Hrw]].
      apply (proj1 (filter_In Q l' (nt_links N))) in Hl' as [Hln Hqn].
      set (lp := l').
      assert (Hqn' : is_main_main_link a1 a2 lp = false).
      { unfold Q in Hqn.
        exact (proj1 (negb_true_iff (is_main_main_link a1 a2 lp)) Hqn). }
      destruct l' as [[x u] [y v]].
      apply eq_sym in Hrw.
      change (((a, p), (b, q)) = (rw (x, u), rw (y, v))) in Hrw.
      injection Hrw as Heqa Heqb.
      assert (Ha : a = agent_of (rw (x, u))).
      { simpl. rewrite <- Heqa. reflexivity. }
      assert (Hpa : p = port_of (rw (x, u))).
      { simpl. rewrite <- Heqa. reflexivity. }
      assert (Hb : b = agent_of (rw (y, v))).
      { simpl. rewrite <- Heqb. reflexivity. }
      assert (Hqb : q = port_of (rw (y, v))).
      { simpl. rewrite <- Heqb. reflexivity. }
      rewrite Ha, Hpa, Hb, Hqb.
      destruct (rewire_endpoint_valid A Ar N a1 a2 r α β Hla Hlb Hlhs Hwf Hap Hrhs Hiface Hlen lp Hln Hqn' (x, u) (or_introl eq_refl)) as [la1 [Hla1 Hpb1]].
      destruct (rewire_endpoint_valid A Ar N a1 a2 r α β Hla Hlb Hlhs Hwf Hap Hrhs Hiface Hlen lp Hln Hqn' (y, v) (or_intror eq_refl)) as [la2 [Hla2 Hpb2]].
      split.
      * unfold has_agent.
        intro Hnone.
        change (agent_label A (raw_splice A Ar N a1 a2 r) (agent_of (rewire_endpoint A Ar N a1 a2 r (x, u))) = None) in Hnone.
        rewrite Hla1 in Hnone.
        discriminate Hnone.
      * split.
        { unfold has_agent.
          intro Hnone.
          change (agent_label A (raw_splice A Ar N a1 a2 r) (agent_of (rewire_endpoint A Ar N a1 a2 r (y, v))) = None) in Hnone.
          rewrite Hla2 in Hnone.
          discriminate Hnone. }
        { intros la lb Hal Halb.
          split.
          { change (agent_label A (raw_splice A Ar N a1 a2 r) (agent_of (rewire_endpoint A Ar N a1 a2 r (x, u))) = Some la) in Hal.
            rewrite Hla1 in Hal.
            injection Hal as Hal1. subst la.
            exact Hpb1. }
          { change (agent_label A (raw_splice A Ar N a1 a2 r) (agent_of (rewire_endpoint A Ar N a1 a2 r (y, v))) = Some lb) in Halb.
            rewrite Hla2 in Halb.
            injection Halb as Halb1. subst lb.
            exact Hpb2. } }
    + (* RHS-origin: ((a,p),(b,q)) = frlink l' for a link l' of the RHS *)
      apply (In_map_inv frlink (nt_links (ru_rhs r)) ((a, p), (b, q))) in Hl as [l' [Hlr Hrw]].
      destruct l' as [[x u] [y v]].
      apply eq_sym in Hrw.
      change (((a, p), (b, q)) = (freshen_pr A N (x, u), freshen_pr A N (y, v))) in Hrw.
      injection Hrw as Hax0 Hpx0 Hbx0 Hqx0.
      rewrite Hax0, Hbx0, Hpx0, Hqx0.
      destruct (wf_links Hrhs x y u v Hlr) as [Hax [Hby Hbnd]].
      destruct (agent_label A (ru_rhs r) x) as [la'|] eqn:Halx.
      * (* label of x present *)
        destruct (agent_label A (ru_rhs r) y) as [lb'|] eqn:Haly.
        { (* both labels present *)
          assert (Hagentx : In (x, la') (nt_agents (ru_rhs r))).
          { exact (agent_label_Some_In A (ru_rhs r) x la' Halx). }
          assert (Hagenty : In (y, lb') (nt_agents (ru_rhs r))).
          { exact (agent_label_Some_In A (ru_rhs r) y lb' Haly). }
          split.
          { unfold has_agent.
            intro Hnone.
            change (agent_label A (raw_splice A Ar N a1 a2 r) (fresh_id A N x) = None) in Hnone.
            rewrite (raw_splice_agent_label_fresh A Ar N a1 a2 r Hrhs x la' Hagentx) in Hnone.
            discriminate Hnone. }
          { split.
            { unfold has_agent.
              intro Hnone.
              change (agent_label A (raw_splice A Ar N a1 a2 r) (fresh_id A N y) = None) in Hnone.
              rewrite (raw_splice_agent_label_fresh A Ar N a1 a2 r Hrhs y lb' Hagenty) in Hnone.
              discriminate Hnone. }
            { intros la lb Hal Halb.
              split.
              { change (agent_label A (raw_splice A Ar N a1 a2 r) (fresh_id A N x) = Some la) in Hal.
                rewrite (raw_splice_agent_label_fresh A Ar N a1 a2 r Hrhs x la' Hagentx) in Hal.
                injection Hal as Hal1. subst la.
                exact (proj1 (Hbnd la' lb' eq_refl eq_refl)). }
              { change (agent_label A (raw_splice A Ar N a1 a2 r) (fresh_id A N y) = Some lb) in Halb.
                rewrite (raw_splice_agent_label_fresh A Ar N a1 a2 r Hrhs y lb' Hagenty) in Halb.
                injection Halb as Halb1. subst lb.
                exact (proj2 (Hbnd la' lb' eq_refl eq_refl)). } } } }
        { (* label of y absent *)
          exfalso.
          apply Hby.
          exact Haly. }
      * (* label of x absent *)
        exfalso.
        apply Hax.
        exact Halx.
  (* ==================== wf_ports ==================== *)
  - (* no port is an end of two distinct links *)
    intros pr l1 l2 Hl1 Hl2 Hneq.
    simpl in Hl1, Hl2.
    apply (in_app_or (map rwlink (filter Q (nt_links N))) (map frlink (nt_links (ru_rhs r))) l1) in Hl1.
    apply (in_app_or (map rwlink (filter Q (nt_links N))) (map frlink (nt_links (ru_rhs r))) l2) in Hl2.
    destruct Hl1 as [Hl1|Hl1].
    + (* l1 is N-origin *)
      apply (In_map_inv rwlink (filter Q (nt_links N)) l1) in Hl1 as [l1n [Hl1n Hrw1]].
      apply (proj1 (filter_In Q l1n (nt_links N))) in Hl1n as [Hl1n' Hq1].
      assert (Hq1' : is_main_main_link a1 a2 l1n = false).
      { unfold Q in Hq1.
        exact (proj1 (negb_true_iff (is_main_main_link a1 a2 l1n)) Hq1). }
      destruct Hl2 as [Hl2|Hl2].
      * (* l2 is N-origin *)
        apply (In_map_inv rwlink (filter Q (nt_links N)) l2) in Hl2 as [l2n [Hl2n Hrw2]].
        apply (proj1 (filter_In Q l2n (nt_links N))) in Hl2n as [Hl2n' Hq2].
        assert (Hq2' : is_main_main_link a1 a2 l2n = false).
        { unfold Q in Hq2.
          exact (proj1 (negb_true_iff (is_main_main_link a1 a2 l2n)) Hq2). }
        (* l1 <> l2 implies l1n <> l2n *)
        assert (Hneqn : l1n <> l2n).
        { intro Heq.
          apply Hneq.
          rewrite <- Hrw1, <- Hrw2.
          f_equal.
          exact Heq. }
        intro Hends.
        destruct Hends as [He1 He2].
        rewrite <- Hrw1 in He1.
        rewrite <- Hrw2 in He2.
        destruct l1n as [[x u] [y v]].
        destruct l2n as [[x' u'] [y' v']].
        simpl in He1, He2.
        destruct He1 as [He1|He1].
        { (* pr = rw (x, u) *)
          destruct He2 as [He2|He2].
          { rewrite <- He2 in He1.
            exact (rewire_endpoint_inj A Ar N a1 a2 r α β Hla Hlb Hlhs Hwf Hap Hrhs Hiface Hlen ((x, u), (y, v)) ((x', u'), (y', v')) Hl1n' Hl2n' Hneqn Hq1' Hq2' (x, u) (or_introl eq_refl) (x', u') (or_introl eq_refl) He1). }
          { rewrite <- He2 in He1.
            exact (rewire_endpoint_inj A Ar N a1 a2 r α β Hla Hlb Hlhs Hwf Hap Hrhs Hiface Hlen ((x, u), (y, v)) ((x', u'), (y', v')) Hl1n' Hl2n' Hneqn Hq1' Hq2' (x, u) (or_introl eq_refl) (y', v') (or_intror eq_refl) He1). } }
        { (* pr = rw (y, v) *)
          destruct He2 as [He2|He2].
          { rewrite <- He2 in He1.
            exact (rewire_endpoint_inj A Ar N a1 a2 r α β Hla Hlb Hlhs Hwf Hap Hrhs Hiface Hlen ((x, u), (y, v)) ((x', u'), (y', v')) Hl1n' Hl2n' Hneqn Hq1' Hq2' (y, v) (or_intror eq_refl) (x', u') (or_introl eq_refl) He1). }
          { rewrite <- He2 in He1.
            exact (rewire_endpoint_inj A Ar N a1 a2 r α β Hla Hlb Hlhs Hwf Hap Hrhs Hiface Hlen ((x, u), (y, v)) ((x', u'), (y', v')) Hl1n' Hl2n' Hneqn Hq1' Hq2' (y, v) (or_intror eq_refl) (y', v') (or_intror eq_refl) He1). } }
      * (* l2 is RHS-origin *)
        apply (In_map_inv frlink (nt_links (ru_rhs r)) l2) in Hl2 as [l2r [Hl2r Hrw2]].
        intro Hends.
        destruct Hends as [He1 He2].
        rewrite <- Hrw1 in He1.
        rewrite <- Hrw2 in He2.
        destruct l1n as [[x u] [y v]].
        destruct l2r as [[x' u'] [y' v']].
        simpl in He1, He2.
        destruct He1 as [He1|He1].
        { (* pr = rw (x, u) *)
          destruct He2 as [He2|He2].
          { rewrite <- He2 in He1.
            exact (rewire_endpoint_neq_fresh_link_end A Ar N a1 a2 r α β Hla Hlb Hlhs Hwf Hap Hrhs Hiface Hlen ((x, u), (y, v)) Hl1n' Hq1' (x, u) (or_introl eq_refl) ((x', u'), (y', v')) Hl2r (x', u') (or_introl eq_refl) He1). }
          { rewrite <- He2 in He1.
            exact (rewire_endpoint_neq_fresh_link_end A Ar N a1 a2 r α β Hla Hlb Hlhs Hwf Hap Hrhs Hiface Hlen ((x, u), (y, v)) Hl1n' Hq1' (x, u) (or_introl eq_refl) ((x', u'), (y', v')) Hl2r (y', v') (or_intror eq_refl) He1). } }
        { (* pr = rw (y, v) *)
          destruct He2 as [He2|He2].
          { rewrite <- He2 in He1.
            exact (rewire_endpoint_neq_fresh_link_end A Ar N a1 a2 r α β Hla Hlb Hlhs Hwf Hap Hrhs Hiface Hlen ((x, u), (y, v)) Hl1n' Hq1' (y, v) (or_intror eq_refl) ((x', u'), (y', v')) Hl2r (x', u') (or_introl eq_refl) He1). }
          { rewrite <- He2 in He1.
            exact (rewire_endpoint_neq_fresh_link_end A Ar N a1 a2 r α β Hla Hlb Hlhs Hwf Hap Hrhs Hiface Hlen ((x, u), (y, v)) Hl1n' Hq1' (y, v) (or_intror eq_refl) ((x', u'), (y', v')) Hl2r (y', v') (or_intror eq_refl) He1). } }
    + (* l1 is RHS-origin *)
      apply (In_map_inv frlink (nt_links (ru_rhs r)) l1) in Hl1 as [l1r [Hl1r Hrw1]].
      destruct Hl2 as [Hl2|Hl2].
      * (* l2 is N-origin: symmetric to the N-vs-RHS case above *)
        apply (In_map_inv rwlink (filter Q (nt_links N)) l2) in Hl2 as [l2n [Hl2n Hrw2]].
        apply (proj1 (filter_In Q l2n (nt_links N))) in Hl2n as [Hl2n' Hq2].
        assert (Hq2' : is_main_main_link a1 a2 l2n = false).
        { unfold Q in Hq2.
          exact (proj1 (negb_true_iff (is_main_main_link a1 a2 l2n)) Hq2). }
        intro Hends.
        destruct Hends as [He1 He2].
        rewrite <- Hrw1 in He1.
        rewrite <- Hrw2 in He2.
        destruct l1r as [[x u] [y v]].
        destruct l2n as [[x' u'] [y' v']].
        simpl in He1, He2.
        destruct He1 as [He1|He1].
        { (* pr = freshen_pr (x, u) *)
          destruct He2 as [He2|He2].
          { rewrite <- He1 in He2.
            exact (rewire_endpoint_neq_fresh_link_end A Ar N a1 a2 r α β Hla Hlb Hlhs Hwf Hap Hrhs Hiface Hlen ((x', u'), (y', v')) Hl2n' Hq2' (x', u') (or_introl eq_refl) ((x, u), (y, v)) Hl1r (x, u) (or_introl eq_refl) He2). }
          { rewrite <- He1 in He2.
            exact (rewire_endpoint_neq_fresh_link_end A Ar N a1 a2 r α β Hla Hlb Hlhs Hwf Hap Hrhs Hiface Hlen ((x', u'), (y', v')) Hl2n' Hq2' (y', v') (or_intror eq_refl) ((x, u), (y, v)) Hl1r (x, u) (or_introl eq_refl) He2). } }
        { (* pr = freshen_pr (y, v) *)
          destruct He2 as [He2|He2].
          { rewrite <- He1 in He2.
            exact (rewire_endpoint_neq_fresh_link_end A Ar N a1 a2 r α β Hla Hlb Hlhs Hwf Hap Hrhs Hiface Hlen ((x', u'), (y', v')) Hl2n' Hq2' (x', u') (or_introl eq_refl) ((x, u), (y, v)) Hl1r (y, v) (or_intror eq_refl) He2). }
          { rewrite <- He1 in He2.
            exact (rewire_endpoint_neq_fresh_link_end A Ar N a1 a2 r α β Hla Hlb Hlhs Hwf Hap Hrhs Hiface Hlen ((x', u'), (y', v')) Hl2n' Hq2' (y', v') (or_intror eq_refl) ((x, u), (y, v)) Hl1r (y, v) (or_intror eq_refl) He2). } }
      * (* l2 is RHS-origin *)
        apply (In_map_inv frlink (nt_links (ru_rhs r)) l2) in Hl2 as [l2r [Hl2r Hrw2]].
        (* l1 <> l2 implies l1r <> l2r *)
        assert (Hneqr : l1r <> l2r).
        { intro Heq.
          apply Hneq.
          rewrite <- Hrw1, <- Hrw2.
          f_equal.
          exact Heq. }
        intro Hends.
        destruct Hends as [He1 He2].
        rewrite <- Hrw1 in He1.
        rewrite <- Hrw2 in He2.
        destruct l1r as [[x u] [y v]].
        destruct l2r as [[x' u'] [y' v']].
        simpl in He1, He2.
        destruct He1 as [He1|He1].
        { (* pr = freshen_pr (x, u) *)
          destruct He2 as [He2|He2].
          { rewrite <- He2 in He1.
            apply (freshen_pr_inj A N (x, u) (x', u')) in He1.
            injection He1 as Hx Hu. subst x. subst u.
            apply (wf_ports Hrhs (x', u') ((x', u'), (y, v)) ((x', u'), (y', v')) Hl1r Hl2r Hneqr).
            split.
            { exact (or_introl eq_refl). }
            { exact (or_introl eq_refl). } }
          { rewrite <- He2 in He1.
            apply (freshen_pr_inj A N (x, u) (y', v')) in He1.
            injection He1 as Hx Hu. subst x. subst u.
            apply (wf_ports Hrhs (y', v') ((y', v'), (y, v)) ((x', u'), (y', v')) Hl1r Hl2r Hneqr).
            split.
            { exact (or_introl eq_refl). }
            { exact (or_intror eq_refl). } } }
        { (* pr = freshen_pr (y, v) *)
          destruct He2 as [He2|He2].
          { rewrite <- He2 in He1.
            apply (freshen_pr_inj A N (y, v) (x', u')) in He1.
            injection He1 as Hx Hy. subst y. subst v.
            apply (wf_ports Hrhs (x', u') ((x, u), (x', u')) ((x', u'), (y', v')) Hl1r Hl2r Hneqr).
            split.
            { exact (or_intror eq_refl). }
            { exact (or_introl eq_refl). } }
          { rewrite <- He2 in He1.
            apply (freshen_pr_inj A N (y, v) (y', v')) in He1.
            injection He1 as Hx Hy. subst y. subst v.
            apply (wf_ports Hrhs (y', v') ((x, u), (y', v')) ((x', u'), (y', v')) Hl1r Hl2r Hneqr).
            split.
            { exact (or_intror eq_refl). }
            { exact (or_intror eq_refl). } } }
  (* ==================== wf_ends ==================== *)
  - (* the two ends of each link differ *)
    intros l Hl.
    simpl in Hl.
    apply (in_app_or (map rwlink (filter Q (nt_links N))) (map frlink (nt_links (ru_rhs r))) l) in Hl.
    destruct Hl as [Hl|Hl].
    + (* N-origin: the two ends of a non-main–main link of N rewire apart *)
      apply (In_map_inv rwlink (filter Q (nt_links N)) l) in Hl as [ln [Hln Hrw]].
      apply (proj1 (filter_In Q ln (nt_links N))) in Hln as [Hln' Hq].
      assert (Hq' : is_main_main_link a1 a2 ln = false).
      { unfold Q in Hq.
        exact (proj1 (negb_true_iff (is_main_main_link a1 a2 ln)) Hq). }
      intro Heq.
      rewrite <- Hrw in Heq.
      simpl in Heq.
      exact (rewire_endpoint_distinct_ends A Ar N a1 a2 r α β Hla Hlb Hlhs Hwf Hap Hrhs Hiface Hlen ln Hln' Hq' Heq).
    + (* RHS-origin: freshening is injective, so the distinct ends of a RHS link stay distinct *)
      apply (In_map_inv frlink (nt_links (ru_rhs r)) l) in Hl as [lr [Hlr Hrw]].
      intro Heq.
      rewrite <- Hrw in Heq.
      simpl in Heq.
      apply (freshen_pr_inj A N (fst lr) (snd lr)) in Heq.
      exact (wf_ends Hrhs lr Hlr Heq).
Qed.

(**************************************************************************)
(** ** The step relation *)

(** [is_active_pair] is symmetric in its two agents: the main–main link
    joining them is undirected. *)
Lemma is_active_pair_sym (A : Type) (Ar : A -> nat) (N : Net A) (a b : nat)
      (H : is_active_pair A Ar N a b) : is_active_pair A Ar N b a.
Proof.
  unfold is_active_pair in H.
  unfold is_active_pair.
  destruct H as [Hneq H1].
  destruct H1 as [Ha H2].
  destruct H2 as [Hb Hl].
  unfold has_link in Hl.
  unfold has_link.
  split.
  { intro Heq. exact (Hneq (eq_sym Heq)). }
  split.
  { exact Hb. }
  split.
  { exact Ha. }
  { destruct Hl as [Hl|Hl].
    { right. exact Hl. }
    { left. exact Hl. } }
Qed.

(** [step A S N N'] holds when [N'] is obtained from [N] by firing one rule
    of the system [S]: for some active pair ([a], [b]) of [N] whose labels
    are ([α], [β]) in the orientation of the rule's LHS, with
    [sys_rules S α β = Some r] and [ru_lhs r = (α, β)], the net [N'] is
    isomorphic to the raw splice of [N] at ([a], [b]) with [r].

    The orientation premise [ru_lhs r = (α, β)] pins which agent of the pair
    plays the "first" role of the rule (see the orientation convention of
    [raw_splice]); [sys_valid_lhs] alone yields only the disjunction of the
    two orders. The final premise lets [N'] be any representative of the
    isomorphism class of the raw splice; [step_iso_compat_r] exploits this.

    [step] is [Type]-sorted (not [Prop]) because its constructor carries the
    computational [net_iso] witness and the fired [Rule]; this lets a proof
    that packages such witnesses (e.g. the [Type]-sorted [step_star_iso] used
    by the diamond) be built by destructing a [step]. *)
Inductive step (A : Type) (S : System A) : Net A -> Net A -> Type :=
step_intro : forall (N N' : Net A) (a b : nat) (α β : A) (r : Rule A),
  well_formed A (sys_arity S) N
  -> is_active_pair A (sys_arity S) N a b
  -> agent_label A N a = Some α
  -> agent_label A N b = Some β
  -> sys_rules S α β = Some r
  -> ru_lhs r = (α, β)
  -> net_iso A (sys_arity S) (raw_splice A (sys_arity S) N a b r) N'
  -> step A S N N'.

(** Firing a rule of [S] on a well-formed net yields a well-formed net. *)
Lemma step_pres_wf (A : Type) (S : System A) (N N' : Net A)
      (H : step A S N N') : well_formed A (sys_arity S) N'.
Proof.
  set (Ar := sys_arity S).
  destruct H as [N N' a b α β r Hwf Hap Hla Hlb Hr Hlhs Hiso].
  assert (Hrhs : well_formed A Ar (ru_rhs r)).
  { exact (sys_valid_wf A S α β r Hr). }
  assert (Hiface : ru_iface r = interface A Ar (ru_rhs r)).
  { exact (sys_valid_iface A S α β r Hr). }
  assert (Hlen := sys_valid_len A S α β r Hr).
  rewrite !Hlhs in Hlen. simpl in Hlen.
  assert (Hsp : well_formed A Ar (raw_splice A Ar N a b r)).
  { exact (raw_splice_wf A Ar N a b r α β Hla Hlb Hlhs Hwf Hap Hrhs Hiface Hlen). }
  exact (net_iso_pres_wf A Ar (raw_splice A Ar N a b r) N' Hiso Hsp).
Qed.

(** A step starts from a well-formed net: the well-formedness premise of
    [step_intro] is recorded in the step itself. *)
Lemma step_pres_wf_source (A : Type) (S : System A) (N N' : Net A)
      (H : step A S N N') : well_formed A (sys_arity S) N.
Proof.
  destruct H as [N N' a b α β r Hwf Hap Hla Hlb Hr Hlhs Hiso].
  exact Hwf.
Qed.

(** [step] is compatible with isomorphism of the target: if [N] steps to
    [N'] and [N''] is isomorphic to [N'], then [N] steps to [N'']. *)
Lemma step_iso_compat_r (A : Type) (S : System A) (N N' N'' : Net A)
      (H : step A S N N') (Hiso : net_iso A (sys_arity S) N' N'') :
  step A S N N''.
Proof.
  set (Ar := sys_arity S).
  destruct H as [N N' a b α β r Hwf Hap Hla Hlb Hr Hlhs Hiso0].
  refine (step_intro A S N N'' a b α β r Hwf Hap Hla Hlb Hr Hlhs _).
  exact (net_iso_transitive A Ar (raw_splice A Ar N a b r) N' N'' Hiso0 Hiso).
Qed.

(**************************************************************************)
(** ** The star closure *)

(** [step_star A S N M] holds when [M] is reachable from [N] by a finite
    (possibly empty) sequence of steps of [S]. Defined as its own inductive
    rather than via [ReflTransCl], which is not available in this Stdlib.

    [step_star] is [Type]-sorted (not [Prop]) so that the confluence proof,
    whose goal is a [Type]-sorted sig, can induct on a [step_star] hypothesis:
    a [Prop] inductive cannot be eliminated into a [Type] goal. This makes
    [normalizes_to] and [is_normalizable] [Type]-sorted as well (see below). *)
Inductive step_star (A : Type) (S : System A) : Net A -> Net A -> Type :=
| step_star_refl : forall (N : Net A), step_star A S N N
| step_star_cons : forall (N N' M : Net A),
    step A S N N' -> step_star A S N' M -> step_star A S N M.

(** [step_star] is transitive. *)
Lemma step_star_trans (A : Type) (S : System A) (N M P : Net A)
      (H1 : step_star A S N M) (H2 : step_star A S M P) :
  step_star A S N P.
Proof.
  induction H1 as [N | N N' M Hstep Hstar IH].
  { exact H2. }
  { exact (step_star_cons A S N N' P Hstep (IH H2)). }
Qed.

(** [step_star] closes under a further step, up to isomorphism of the
    target: a star sequence from [N] to [M] followed by one step from [M]
    to [M'] reaches any net isomorphic to [M'] (in particular [M'] itself,
    by [net_iso_reflexive]).

    This is the correct replacement for the naive statement "a star
    sequence is invariant under isomorphism of its target" ([step_star N M]
    and [net_iso M M'] implying [step_star N M']), which is false in the
    zero-step case: in a rule-free system [N] star-reaches only itself, yet
    [N] is isomorphic to other nets. *)
Lemma step_star_step_iso (A : Type) (S : System A) (N M M' M'' : Net A)
      (Hstar : step_star A S N M)
      (Hstep : step A S M M')
      (Hiso : net_iso A (sys_arity S) M' M'') :
  step_star A S N M''.
Proof.
  assert (Hstep' : step A S M M'').
  { exact (step_iso_compat_r A S M M' M'' Hstep Hiso). }
  induction Hstar as [N | N N' M Hstep0 Hstar IH].
  { exact (step_star_cons A S N M'' M'' Hstep' (step_star_refl A S M'')). }
  { exact (step_star_cons A S N N' M'' Hstep0 (IH Hstep Hstep')). }
Qed.

(** [step_star_iso A S N1 N2] holds when [N2] is reachable from [N1] by a
    finite (possibly empty) sequence of steps of [S], up to renaming: some
    concrete net [M] with [N1 ->* M] is isomorphic to [N2]. This is the
    reachability notion appropriate for the "nets up to renaming" model: the
    concrete [step_star] is not closed under isomorphism of its target in the
    zero-step case (see [step_star_step_iso]), so a diamond stated with
    [step_star] is false when two steps fire the same pair and yield distinct
    representatives of one isomorphism class. [step_star_iso] fixes this by
    allowing the target to be matched up to [net_iso]. *)
Definition step_star_iso (A : Type) (S : System A) (N1 N2 : Net A) : Type :=
  { M : Net A & step_star A S N1 M * net_iso A (sys_arity S) M N2 }.

(**************************************************************************)
(** ** Normal forms and normalizability *)

(** [is_normal_form A Ar N] holds when [N] contains no active (reducible)
    pair: no rule can fire on it (§4.6). *)
Definition is_normal_form (A : Type) (Ar : A -> nat) (N : Net A) : Prop :=
  forall a b, ~ is_active_pair A Ar N a b.

(** [normalizes_to A S N N'] holds when [N'] is a normal form reachable
    from [N] by a (possibly empty) sequence of steps of [S] (§4.6).
    [Type]-sorted (a pair of the normal-form proof and the star witness)
    because [step_star] is [Type]-sorted; a [Prop] conjunction cannot hold a
    [Type] component. *)
Definition normalizes_to (A : Type) (S : System A) (N N' : Net A) : Type :=
  is_normal_form A (sys_arity S) N' * step_star A S N N'.

(** [is_normalizable A S N] holds when some normal form is reachable from
    [N] by a (possibly empty) sequence of steps of [S] (§4.6). [Type]-sorted
    (a sig carrying the witnessing normal form) because [normalizes_to] is
    [Type]-sorted; a [Prop] existential cannot hold a [Type] component. *)
Definition is_normalizable (A : Type) (S : System A) (N : Net A) : Type :=
  { N' : Net A & normalizes_to A S N N' }.

(** [is_strongly_normalizable A S N] holds when no infinite step-sequence
    starts from [N] — equivalently, every reduction sequence from [N] is
    finite (§4.6). This is the "no infinite sequence" characterization,
    chosen over the inductive one because it is the form used by the §4.7(1)
    result. *)
Definition is_strongly_normalizable (A : Type) (S : System A) (N : Net A) : Prop :=
  forall (f : nat -> Net A), f 0 = N -> (forall n, step A S (f n) (f (n + 1))) -> False.

(** A normal form has no outgoing step: no rule can fire on it. *)
Lemma nf_no_step (A : Type) (S : System A) (N N' : Net A)
      (Hnf : is_normal_form A (sys_arity S) N) :
  step A S N N' -> False.
Proof.
  intro Hstep.
  destruct Hstep as [N N' a b α β r Hwf Hap _ _ _ _ _].
  apply Hnf in Hap.
  exact Hap.
Qed.

(** A single step is a (one-element) star sequence. *)
Lemma step_star_step (A : Type) (S : System A) (N N' : Net A)
      (H : step A S N N') : step_star A S N N'.
Proof.
  exact (step_star_cons A S N N' N' H (step_star_refl A S N')).
Qed.

(** A normal form normalizes to itself (the empty sequence). *)
Lemma normalizes_to_of_nf (A : Type) (S : System A) (N : Net A)
      (Hnf : is_normal_form A (sys_arity S) N) :
  normalizes_to A S N N.
Proof.
  exact (pair Hnf (step_star_refl A S N)).
Qed.

(** A normal form is normalizable (to itself). *)
Lemma is_normalizable_of_nf (A : Type) (S : System A) (N : Net A)
      (Hnf : is_normal_form A (sys_arity S) N) :
  is_normalizable A S N.
Proof.
  exact (existT (fun N' => normalizes_to A S N N') N (normalizes_to_of_nf A S N Hnf)).
Qed.

(**************************************************************************)
(** ** Pair preservation and commutation (§4.7 setup) *)

(** Two DISTINCT active pairs in a well-formed net share no agents at all:
    they are pairwise disjoint. This is the four-inequality form of
    [pair_disjoint] and is the disjointness precondition for
    [raw_splice_pres_pair] and [step_commuting]. The premise [Hdist] says the
    two pairs are not the same pair in either orientation. *)
Lemma pair_disjoint_full (A : Type) (Ar : A -> nat) (N : Net A) (H : well_formed A Ar N)
      (a b c d : nat)
      (Hab : is_active_pair A Ar N a b)
      (Hcd : is_active_pair A Ar N c d)
      (Hdist : ~ ((a = c /\ b = d) \/ (a = d /\ b = c))) :
  a <> c /\ a <> d /\ b <> c /\ b <> d.
Proof.
  split; [ | split; [ | split; [ | ]]].
  - (* a <> c *)
    intro Hac.
    apply Hdist. left. split; [exact Hac | ].
    apply (pair_disjoint A Ar N H a b c d Hab Hcd). exact Hac.
  - (* a <> d *)
    intro Had.
    apply Hdist. right. split; [exact Had | ].
    apply (pair_disjoint A Ar N H a b d c Hab (is_active_pair_sym A Ar N c d Hcd)).
    exact Had.
  - (* b <> c *)
    intro Hbc.
    apply Hdist. right. split.
    + apply (pair_disjoint A Ar N H b a c d (is_active_pair_sym A Ar N a b Hab) Hcd).
      exact Hbc.
    + exact Hbc.
  - (* b <> d *)
    intro Hbd.
    apply Hdist. left. split.
    + apply (pair_disjoint A Ar N H b a d c
         (is_active_pair_sym A Ar N a b Hab) (is_active_pair_sym A Ar N c d Hcd)).
      exact Hbd.
    + exact Hbd.
Qed.

(** A link of [N] whose two ends sit on agents other than [a] and [b] is kept
    unchanged by [raw_splice N a b r]: it is not the main–main link (so it
    survives the filter) and both of its endpoints are off the boundary (so
    [rewire_endpoint_kept] leaves them fixed). This is the link-level form of
    the disjointness preservation. *)
Lemma raw_splice_link_kept (A : Type) (Ar : A -> nat) (N : Net A) (a b : nat) (r : Rule A)
      (l : port_ref * port_ref)
      (Hl : In l (nt_links N))
      (Hnotmm : is_main_main_link a b l = false)
      (Hend : forall e, link_end l e -> agent_of e <> a /\ agent_of e <> b) :
  In l (nt_links (raw_splice A Ar N a b r)).
Proof.
  change (In l (splice_links A Ar N a b r)).
  unfold splice_links.
  apply in_or_app. left.
  (* rewire_link l = l: both endpoints are off the boundary. *)
  assert (Hrw : rewire_link A Ar N a b r l = l).
  { unfold rewire_link.
    assert (Hf : rewire_endpoint A Ar N a b r (fst l) = fst l).
    { destruct (fst l) as [x p] eqn:Hfl.
      assert (Hle : link_end l (x, p)). { left. exact Hfl. }
      apply (rewire_endpoint_kept A Ar N a b r x p).
      + apply (not_true_is_false (Nat.eqb x a)).
        intro Heq.
        apply (proj1 (Hend (x, p) Hle)).
        apply (proj1 (Nat.eqb_eq x a)) in Heq. exact Heq.
      + apply (not_true_is_false (Nat.eqb x b)).
        intro Heq.
        apply (proj2 (Hend (x, p) Hle)).
        apply (proj1 (Nat.eqb_eq x b)) in Heq. exact Heq. }
    assert (Hs : rewire_endpoint A Ar N a b r (snd l) = snd l).
    { destruct (snd l) as [x p] eqn:Hsl.
      assert (Hle : link_end l (x, p)). { right. exact Hsl. }
      apply (rewire_endpoint_kept A Ar N a b r x p).
      + apply (not_true_is_false (Nat.eqb x a)).
        intro Heq.
        apply (proj1 (Hend (x, p) Hle)).
        apply (proj1 (Nat.eqb_eq x a)) in Heq. exact Heq.
      + apply (not_true_is_false (Nat.eqb x b)).
        intro Heq.
        apply (proj2 (Hend (x, p) Hle)).
        apply (proj1 (Nat.eqb_eq x b)) in Heq. exact Heq. }
    rewrite Hf, Hs.
    destruct l as [[x1 p1] [x2 p2]]. reflexivity. }
  (* l survives the filter: it is a link of N and not the main–main link. *)
  assert (Hin : In (rewire_link A Ar N a b r l)
         (map (rewire_link A Ar N a b r)
            (filter (fun l => negb (is_main_main_link a b l)) (nt_links N)))).
  { apply (In_map (rewire_link A Ar N a b r)
         (filter (fun l => negb (is_main_main_link a b l)) (nt_links N)) l).
    apply (proj2 (filter_In (fun l => negb (is_main_main_link a b l)) l (nt_links N))).
    split.
    - exact Hl.
    - change (negb (is_main_main_link a b l) = true).
      apply (proj2 (negb_true_iff _)). exact Hnotmm. }
  rewrite Hrw in Hin.
  exact Hin.
Qed.

(** Reducing an active pair ([a], [b]) leaves every OTHER active pair intact:
    if ([c], [d]) is an active pair of [N] disjoint from ([a], [b]), then
    ([c], [d]) is still an active pair of [raw_splice N a b r] — the agents
    [c], [d] and their main link are untouched by the splice, which only
    removes ([a], [b]) and rewires links incident to the pair's boundary.
    Concrete (same ids), no isomorphism needed. This disjointness-driven
    preservation gates the commuting lemma. *)
Lemma raw_splice_pres_pair (A : Type) (Ar : A -> nat) (N : Net A) (a b c d : nat) (r : Rule A)
      (Hwf : well_formed A Ar N)
      (Hap_ab : is_active_pair A Ar N a b)
      (Hap_cd : is_active_pair A Ar N c d)
      (Hdisj : a <> c /\ a <> d /\ b <> c /\ b <> d) :
  is_active_pair A Ar (raw_splice A Ar N a b r) c d.
Proof.
  set (M := raw_splice A Ar N a b r).
  unfold is_active_pair.
  destruct Hap_cd as [Hcd_neq [Hc_ag [Hd_ag Hcd_link]]].
  destruct Hdisj as [Hac [Had [Hbc Hbd]]].
  refine (conj Hcd_neq (conj _ (conj _ _))).
  - (* has_agent M c: c is an agent of N, c <> a, c <> b, so it survives. *)
    apply (proj2 (has_agent_In A M c)).
    change (In c (map fst (splice_agents A N a b r))).
    unfold splice_agents.
    rewrite map_app.
    apply in_or_app. left.
    apply (proj2 (in_map_iff (fun p : nat * A => fst p)
           (filter (fun p => negb (Nat.eqb (fst p) a) && negb (Nat.eqb (fst p) b)) (nt_agents N)) c)).
    apply (proj1 (has_agent_In A N c)) in Hc_ag.
    apply (proj1 (in_map_iff (fun p : nat * A => fst p) (nt_agents N) c)) in Hc_ag.
    destruct Hc_ag as [p [Hpc Hin]].
    exists p.
    split.
    + exact Hpc.
    + apply (proj2 (filter_In (fun p => negb (Nat.eqb (fst p) a) && negb (Nat.eqb (fst p) b)) p (nt_agents N))).
      split.
      * exact Hin.
      * { rewrite Hpc.
          change (negb (Nat.eqb c a) && negb (Nat.eqb c b) = true).
          apply (proj2 (andb_true_iff _ _)); split.
          - apply (proj2 (negb_true_iff _)).
            destruct (Nat.eqb c a) eqn:Hb.
            + apply (proj1 (Nat.eqb_eq c a)) in Hb.
              exfalso.
              apply Hac. symmetry. exact Hb.
            + reflexivity.
          - apply (proj2 (negb_true_iff _)).
            destruct (Nat.eqb c b) eqn:Hb.
            + apply (proj1 (Nat.eqb_eq c b)) in Hb.
              exfalso.
              apply Hbc. symmetry. exact Hb.
            + reflexivity. }
  - (* has_agent M d: symmetric. *)
    apply (proj2 (has_agent_In A M d)).
    change (In d (map fst (splice_agents A N a b r))).
    unfold splice_agents.
    rewrite map_app.
    apply in_or_app. left.
    apply (proj2 (in_map_iff (fun p : nat * A => fst p)
           (filter (fun p => negb (Nat.eqb (fst p) a) && negb (Nat.eqb (fst p) b)) (nt_agents N)) d)).
    apply (proj1 (has_agent_In A N d)) in Hd_ag.
    apply (proj1 (in_map_iff (fun p : nat * A => fst p) (nt_agents N) d)) in Hd_ag.
    destruct Hd_ag as [p [Hpd Hin]].
    exists p.
    split.
    + exact Hpd.
    + apply (proj2 (filter_In (fun p => negb (Nat.eqb (fst p) a) && negb (Nat.eqb (fst p) b)) p (nt_agents N))).
      split.
      * exact Hin.
      * { rewrite Hpd.
          change (negb (Nat.eqb d a) && negb (Nat.eqb d b) = true).
          apply (proj2 (andb_true_iff _ _)); split.
          - apply (proj2 (negb_true_iff _)).
            destruct (Nat.eqb d a) eqn:Hb.
            + apply (proj1 (Nat.eqb_eq d a)) in Hb.
              exfalso.
              apply Had. symmetry. exact Hb.
            + reflexivity.
          - apply (proj2 (negb_true_iff _)).
            destruct (Nat.eqb d b) eqn:Hb.
            + apply (proj1 (Nat.eqb_eq d b)) in Hb.
              exfalso.
              apply Hbd. symmetry. exact Hb.
            + reflexivity. }
  - (* has_link M (c,0) (d,0): the main link of (c,d) survives unchanged. *)
    unfold has_link in Hcd_link.
    destruct Hcd_link as [Hl|Hl].
    + (* l = ((c,0),(d,0)) is a link of N. *)
      left.
      assert (Hca_f : Nat.eqb c a = false). { destruct (Nat.eqb c a) eqn:Hb. - exfalso. apply (proj1 (Nat.eqb_eq c a)) in Hb. apply Hac. symmetry. exact Hb. - reflexivity. }
      assert (Hdb_f : Nat.eqb d b = false). { destruct (Nat.eqb d b) eqn:Hb. - exfalso. apply (proj1 (Nat.eqb_eq d b)) in Hb. apply Hbd. symmetry. exact Hb. - reflexivity. }
      assert (Hcb_f : Nat.eqb c b = false). { destruct (Nat.eqb c b) eqn:Hb. - exfalso. apply (proj1 (Nat.eqb_eq c b)) in Hb. apply Hbc. symmetry. exact Hb. - reflexivity. }
      assert (Hda_f : Nat.eqb d a = false). { destruct (Nat.eqb d a) eqn:Hb. - exfalso. apply (proj1 (Nat.eqb_eq d a)) in Hb. apply Had. symmetry. exact Hb. - reflexivity. }
      assert (Hnotmm : is_main_main_link a b ((c, 0), (d, 0)) = false).
      { unfold is_main_main_link. cbn.
        rewrite Hca_f, Hdb_f, Hcb_f, Hda_f.
        simpl. reflexivity. }
      assert (Hend : forall e, link_end ((c, 0), (d, 0)) e -> agent_of e <> a /\ agent_of e <> b).
      { intros e He.
        destruct He as [He|He].
        - rewrite <- He. split.
          + intro H. apply Hac. symmetry. exact H.
          + intro H. apply Hbc. symmetry. exact H.
        - rewrite <- He. split.
          + intro H. apply Had. symmetry. exact H.
          + intro H. apply Hbd. symmetry. exact H. }
      exact (raw_splice_link_kept A Ar N a b r ((c, 0), (d, 0)) Hl Hnotmm Hend).
    + (* l = ((d,0),(c,0)) is a link of N. *)
      right.
      assert (Hca_f : Nat.eqb c a = false). { destruct (Nat.eqb c a) eqn:Hb. - exfalso. apply (proj1 (Nat.eqb_eq c a)) in Hb. apply Hac. symmetry. exact Hb. - reflexivity. }
      assert (Hdb_f : Nat.eqb d b = false). { destruct (Nat.eqb d b) eqn:Hb. - exfalso. apply (proj1 (Nat.eqb_eq d b)) in Hb. apply Hbd. symmetry. exact Hb. - reflexivity. }
      assert (Hcb_f : Nat.eqb c b = false). { destruct (Nat.eqb c b) eqn:Hb. - exfalso. apply (proj1 (Nat.eqb_eq c b)) in Hb. apply Hbc. symmetry. exact Hb. - reflexivity. }
      assert (Hda_f : Nat.eqb d a = false). { destruct (Nat.eqb d a) eqn:Hb. - exfalso. apply (proj1 (Nat.eqb_eq d a)) in Hb. apply Had. symmetry. exact Hb. - reflexivity. }
      assert (Hnotmm : is_main_main_link a b ((d, 0), (c, 0)) = false).
      { unfold is_main_main_link. cbn.
        rewrite Hca_f, Hdb_f, Hcb_f, Hda_f.
        simpl. reflexivity. }
      assert (Hend : forall e, link_end ((d, 0), (c, 0)) e -> agent_of e <> a /\ agent_of e <> b).
      { intros e He.
        destruct He as [He|He].
        - rewrite <- He. split.
          + intro H. apply Had. symmetry. exact H.
          + intro H. apply Hbd. symmetry. exact H.
        - rewrite <- He. split.
          + intro H. apply Hac. symmetry. exact H.
          + intro H. apply Hbc. symmetry. exact H. }
      exact (raw_splice_link_kept A Ar N a b r ((d, 0), (c, 0)) Hl Hnotmm Hend).
Qed.

(** Reducing one active pair ([a], [b]) leaves every other active pair
    ([c], [d]) intact, up to the isomorphism by which the reduction's target
    [N'] represents the raw splice of [N] at ([a], [b]) with [r]. This is the
    step-level form of [raw_splice_pres_pair]: a [step] is exactly a raw
    splice plus an isomorphism, so we state the preservation in terms of the
    raw splice [raw_splice N a b r] and the isomorphism [Hiso] to [N']
    (rather than the [step] inductive, which hides which pair was fired).
    The preserved pair in [N'] is ([ni_map Hiso c], [ni_map Hiso d]): the
    isomorphism's map carries the surviving agents ([c], [d]) to their images
    in [N']. (Injectivity of the map on the raw splice's agents is available
    to callers directly from [ni_inj Hiso].) Uses [net_iso_pres_active_pair]. *)
Lemma step_preserves_pair (A : Type) (S : System A) (N N' : Net A)
      (a b c d : nat) (r : Rule A)
      (Hiso : net_iso A (sys_arity S) (raw_splice A (sys_arity S) N a b r) N')
      (Hwf : well_formed A (sys_arity S) N)
      (Hap_ab : is_active_pair A (sys_arity S) N a b)
      (Hap_cd : is_active_pair A (sys_arity S) N c d)
      (Hdisj : a <> c /\ a <> d /\ b <> c /\ b <> d) :
  is_active_pair A (sys_arity S) N' (ni_map Hiso c) (ni_map Hiso d).
Proof.
  set (Ar := sys_arity S).
  apply (net_iso_pres_active_pair A Ar (raw_splice A Ar N a b r) N' Hiso c d).
  apply (raw_splice_pres_pair A Ar N a b c d r Hwf Hap_ab Hap_cd Hdisj).
Qed.

(**************************************************************************)
(** ** Disjoint-pair commutation (§4.7) *)

(** [shift a b x] is the signed translation [x + (a - b)] computed in [nat]:
    it adds [a - b] when [a >= b] and subtracts [b - a] otherwise. The two
    double-splices in [step_commuting] freshen the same RHS relative to
    different base maxima, so the corresponding agents differ by a possibly
    negative shift; [shift] makes that translation total. *)
Definition shift (a b x : nat) : nat :=
  if Nat.leb b a then x + (a - b) else x - (b - a).

(** The renaming witnessing [step_commuting]. With
    [M = max_agent_id N], [M1 = max_agent_id (raw_splice N a b r1)],
    [M2 = max_agent_id (raw_splice N c d r2)], the agents of
    [raw_splice (raw_splice N a b r1) c d r2] split into three id-disjoint
    blocks: the common agents of [N] (ids [<= min M M1]), the freshened
    [r1]-RHS agents (ids in [(min M M1, M1]], present only when [M1 > M]),
    and the freshened [r2]-RHS agents (ids [> M1]). The map is the identity
    on the common block, shifts the [r1]-RHS block by [M2 - M] (landing it on
    the [r1]-RHS block of the other order), and shifts the [r2]-RHS block by
    [M - M1] (landing it on the [r2]-RHS block of the other order). *)
Definition comm_map (M M1 M2 : nat) (x : nat) : nat :=
  if Nat.leb x (Nat.min M M1) then x
  else if Nat.leb x M1 then shift M2 M x
  else shift M M1 x.

(** A freshened id of [N] is strictly greater than every agent id of [N]. *)
Lemma fresh_id_above_all (A : Type) (N : Net A) (x y : nat) :
  has_agent A N y -> fresh_id A N x > y.
Proof.
  intros Hy.
  apply (proj1 (has_agent_In A N y)) in Hy.
  specialize (list_max_upper_bound (map fst (nt_agents N)) y Hy) as Hle.
  unfold fresh_id, max_agent_id in *. lia.
Qed.

(** Filtering the freshened RHS agents of [r] (relative to [N]) by "id not in
    {[c, d]}\" keeps them all: every freshened id is above every agent id of
    [N], in particular above [c] and [d]. *)
Lemma splice_keep_keeps_fresh (A : Type) (N : Net A) (c d : nat) (r : Rule A)
      (Hc : has_agent A N c) (Hd : has_agent A N d) :
  filter (fun p : nat * A => negb (Nat.eqb (fst p) c) && negb (Nat.eqb (fst p) d))
      (map (fun p => (fresh_id A N (fst p), snd p)) (nt_agents (ru_rhs r)))
  = map (fun p => (fresh_id A N (fst p), snd p)) (nt_agents (ru_rhs r)).
Proof.
  set (P := fun p : nat * A => negb (Nat.eqb (fst p) c) && negb (Nat.eqb (fst p) d)).
  set (L := map (fun p => (fresh_id A N (fst p), snd p)) (nt_agents (ru_rhs r))).
  assert (Hext : filter P L = filter (fun _ : nat * A => true) L).
  { apply (filter_ext_in P (fun _ : nat * A => true) L).
    intros p Hp.
    apply (proj1 (in_map_iff (fun q : nat * A => (fresh_id A N (fst q), snd q))
           (nt_agents (ru_rhs r)) p)) in Hp.
    destruct Hp as [q [Hpq Hq]].
    subst p.
    change (negb (Nat.eqb (fresh_id A N (fst q)) c) && negb (Nat.eqb (fresh_id A N (fst q)) d) = true).
    apply (proj2 (andb_true_iff _ _)); split.
    - apply (proj2 (negb_true_iff _)).
      destruct (Nat.eqb (fresh_id A N (fst q)) c) eqn:Hb.
      + exfalso.
        apply (proj1 (Nat.eqb_eq (fresh_id A N (fst q)) c)) in Hb.
        assert (Hgt : fresh_id A N (fst q) > c).
        { exact (fresh_id_above_all A N (fst q) c Hc). }
        rewrite <- Hb in Hgt. lia.
      + reflexivity.
    - apply (proj2 (negb_true_iff _)).
      destruct (Nat.eqb (fresh_id A N (fst q)) d) eqn:Hb.
      + exfalso.
        apply (proj1 (Nat.eqb_eq (fresh_id A N (fst q)) d)) in Hb.
        assert (Hgt : fresh_id A N (fst q) > d).
        { exact (fresh_id_above_all A N (fst q) d Hd). }
        rewrite <- Hb in Hgt. lia.
      + reflexivity. }
  rewrite Hext.
  apply filter_true.
Qed.

(**************************************************************************)
(** ** Disjoint-pair commutation: the isomorphism witness (§4.7) *)

(** Reducing two DISJOINT active pairs commutes up to renaming: the two
    double-splices [raw_splice (raw_splice N a b r1) c d r2] and
    [raw_splice (raw_splice N c d r2) a b r1] are isomorphic. This Section
    builds that isomorphism as a [net_iso] record, witnessing
    [step_commuting].

    The agents of the first double-splice split into three id-disjoint blocks:
    the COMMON agents of [N] (those other than [a, b, c, d]), the freshened
    [r1]-RHS agents, and the freshened [r2]-RHS agents. The second
    double-splice has the same three blocks, with the [r1]- and [r2]-RHS
    blocks freshened relative to different base maxima. [comm_map] is the
    identity on the common block and a (possibly negative) shift on each RHS
    block, landing it on the corresponding block of the other order. The
    links follow by the endpoint-rewiring facts. *)

Section Commutation.
  Variable (A : Type) (Ar : A -> nat) (N : Net A) (a b c d : nat) (r1 r2 : Rule A).
  Hypothesis Hwf : well_formed A Ar N.
  Hypothesis Hap_ab : is_active_pair A Ar N a b.
  Hypothesis Hap_cd : is_active_pair A Ar N c d.
  Hypothesis Hdisj : a <> c /\ a <> d /\ b <> c /\ b <> d.

  (* The two rules are valid in the usual sense: their RHS is well-formed and
     their declared interface is the RHS's free ports (the [sys_valid_wf] and
     [sys_valid_iface] conjuncts). The orientation premises pin each fired
     agent to its role in the rule's LHS (as [step_intro] does). Together they
     ensure that every kept link endpoint on [a b c d] is in the rewiring
     range, and that every freshened endpoint id is an agent id of the
     corresponding RHS. *)
  Hypothesis Hr1 : well_formed A Ar (ru_rhs r1).
  Hypothesis Hr2 : well_formed A Ar (ru_rhs r2).
  Hypothesis Hi1 : ru_iface r1 = interface A Ar (ru_rhs r1).
  Hypothesis Hi2 : ru_iface r2 = interface A Ar (ru_rhs r2).
  Hypothesis Hol1 : agent_label A N a = Some (fst (ru_lhs r1)).
  Hypothesis Hol2 : agent_label A N b = Some (snd (ru_lhs r1)).
  Hypothesis Hol3 : agent_label A N c = Some (fst (ru_lhs r2)).
  Hypothesis Hol4 : agent_label A N d = Some (snd (ru_lhs r2)).

  (* The declared interface of [r1] covers its full boundary: its length is at
     least the sum of the arities of the two LHS labels (the [sys_valid_len]
     conjunct, as an inequality). This ensures that the [nth] lookups in
     [rewire_endpoint] hit real interface entries for every in-range boundary
     port of [r1], so the freshened endpoint ids are agent ids of the RHS.
     (No analogous premise is needed for [r2]: the corresponding [comm_map]
     direction, [cm_fresh2p], is unconditional.) *)
  Hypothesis Hlen1 : Ar (fst (ru_lhs r1)) + Ar (snd (ru_lhs r1)) <= length (ru_iface r1).

  (* The four agents of the two pairs are present in [N], and each pair is
     joined by its main–main link. *)
  Local Lemma Ha : has_agent A N a.
  Proof. exact (proj1 (proj2 Hap_ab)). Qed.
  Local Lemma Hb : has_agent A N b.
  Proof. exact (proj1 (proj2 (proj2 Hap_ab))). Qed.
  Local Lemma Hc : has_agent A N c.
  Proof. exact (proj1 (proj2 Hap_cd)). Qed.
  Local Lemma Hd : has_agent A N d.
  Proof. exact (proj1 (proj2 (proj2 Hap_cd))). Qed.
  Local Lemma Hlink_ab : has_link A N (a, 0) (b, 0).
  Proof. exact (proj2 (proj2 (proj2 Hap_ab))). Qed.
  Local Lemma Hlink_cd : has_link A N (c, 0) (d, 0).
  Proof. exact (proj2 (proj2 (proj2 Hap_cd))). Qed.

  (* The single and double splices, and their base maxima. *)
  Definition sc_N1  := raw_splice A Ar N a b r1.
  Definition sc_N2  := raw_splice A Ar N c d r2.
  Definition sc_N12 := raw_splice A Ar sc_N1 c d r2.
  Definition sc_N21 := raw_splice A Ar sc_N2 a b r1.
  Local Definition sc_M  := max_agent_id A N.
  Local Definition sc_M1 := max_agent_id A sc_N1.
  Local Definition sc_M2 := max_agent_id A sc_N2.

  (* [sc_rem2 x y p] is [true] when the agent id of [p] is neither [x] nor [y]. *)
  Local Definition sc_rem2 (x y : nat) (p : nat * A) : bool :=
    negb (Nat.eqb (fst p) x) && negb (Nat.eqb (fst p) y).

  (* The three agent blocks of the double-splices. [sc_C] is the common block
     (present, identically, in both orders); [sc_F1]/[sc_F2] are the [r1]/[r2]
     RHS freshened relative to [N]; [sc_F1p]/[sc_F2p] are the [r1]/[r2] RHS
     freshened relative to [sc_N2]/[sc_N1] (the other order's base). *)
  Local Definition sc_C   := filter (sc_rem2 a b) (filter (sc_rem2 c d) (nt_agents N)).
  Local Definition sc_F1  := map (fun p => (fresh_id A N (fst p), snd p)) (nt_agents (ru_rhs r1)).
  Local Definition sc_F2  := map (fun p => (fresh_id A N (fst p), snd p)) (nt_agents (ru_rhs r2)).
  Local Definition sc_F1p := map (fun p => (fresh_id A sc_N2 (fst p), snd p)) (nt_agents (ru_rhs r1)).
  Local Definition sc_F2p := map (fun p => (fresh_id A sc_N1 (fst p), snd p)) (nt_agents (ru_rhs r2)).

  (* [Nat.min sc_M sc_M1] is bounded by each argument. *)
  Local Lemma sc_min_le_l : Nat.min sc_M sc_M1 <= sc_M.
  Proof.
    destruct (Nat.leb sc_M sc_M1) eqn:Hb.
    - apply (proj1 (Nat.leb_le sc_M sc_M1)) in Hb.
      rewrite (Nat.min_l sc_M sc_M1 Hb). lia.
    - assert (Hnot : ~ sc_M <= sc_M1).
      { intro Hle. apply (proj2 (Nat.leb_le sc_M sc_M1)) in Hle.
        rewrite Hle in Hb. discriminate Hb. }
      assert (Hle : sc_M1 <= sc_M). { lia. }
      rewrite (Nat.min_r sc_M sc_M1 Hle). lia.
  Qed.

  Local Lemma sc_min_le_r : Nat.min sc_M sc_M1 <= sc_M1.
  Proof.
    destruct (Nat.leb sc_M sc_M1) eqn:Hb.
    - apply (proj1 (Nat.leb_le sc_M sc_M1)) in Hb.
      rewrite (Nat.min_l sc_M sc_M1 Hb). lia.
    - assert (Hnot : ~ sc_M <= sc_M1).
      { intro Hle. apply (proj2 (Nat.leb_le sc_M sc_M1)) in Hle.
        rewrite Hle in Hb. discriminate Hb. }
      assert (Hle : sc_M1 <= sc_M). { lia. }
      rewrite (Nat.min_r sc_M sc_M1 Hle). lia.
  Qed.

  (* --- [comm_map] pointwise behaviour on the three blocks --- *)

  Local Lemma cm_id (x : nat) : x <= Nat.min sc_M sc_M1 -> comm_map sc_M sc_M1 sc_M2 x = x.
  Proof.
    intros Hx. unfold comm_map.
    assert (Hb : Nat.leb x (Nat.min sc_M sc_M1) = true).
    { apply (proj2 (Nat.leb_le x (Nat.min sc_M sc_M1))). exact Hx. }
    rewrite Hb. reflexivity.
  Qed.

  Local Lemma cm_r1 (x : nat) : sc_M < x -> x <= sc_M1 -> comm_map sc_M sc_M1 sc_M2 x = shift sc_M2 sc_M x.
  Proof.
    intros Hlo Hhi. unfold comm_map.
    assert (Hb1 : Nat.leb x (Nat.min sc_M sc_M1) = false).
    { destruct (Nat.leb x (Nat.min sc_M sc_M1)) eqn:Hd.
      - exfalso.
        apply (proj1 (Nat.leb_le x (Nat.min sc_M sc_M1))) in Hd.
        assert (Hmn : Nat.min sc_M sc_M1 <= sc_M). { exact sc_min_le_l. }
        lia.
      - reflexivity. }
    rewrite Hb1.
    assert (Hb2 : Nat.leb x sc_M1 = true).
    { apply (proj2 (Nat.leb_le x sc_M1)). exact Hhi. }
    rewrite Hb2. reflexivity.
  Qed.

  Local Lemma cm_r2 (x : nat) : x > sc_M1 -> comm_map sc_M sc_M1 sc_M2 x = shift sc_M sc_M1 x.
  Proof.
    intros Hx. unfold comm_map.
    assert (Hb1 : Nat.leb x (Nat.min sc_M sc_M1) = false).
    { destruct (Nat.leb x (Nat.min sc_M sc_M1)) eqn:Hd.
      - exfalso.
        apply (proj1 (Nat.leb_le x (Nat.min sc_M sc_M1))) in Hd.
        assert (Hmn : Nat.min sc_M sc_M1 <= sc_M1). { exact sc_min_le_r. }
        lia.
      - reflexivity. }
    rewrite Hb1.
    assert (Hb2 : Nat.leb x sc_M1 = false).
    { destruct (Nat.leb x sc_M1) eqn:Hd.
      - exfalso.
        apply (proj1 (Nat.leb_le x sc_M1)) in Hd.
        lia.
      - reflexivity. }
    rewrite Hb2. reflexivity.
  Qed.

  (* The shifts land the RHS blocks exactly on the other order's RHS blocks. *)
  Local Lemma shift_r1 (u : nat) : shift sc_M2 sc_M (u + sc_M + 1) = u + sc_M2 + 1.
  Proof.
    unfold shift. destruct (Nat.leb sc_M sc_M2) eqn:Hb.
    - apply (proj1 (Nat.leb_le sc_M sc_M2)) in Hb. lia.
    - assert (Hnot : ~ sc_M <= sc_M2).
      { intro Hle. apply (proj2 (Nat.leb_le sc_M sc_M2)) in Hle.
        rewrite Hle in Hb. discriminate Hb. }
      lia.
  Qed.

  Local Lemma shift_r2 (v : nat) : shift sc_M sc_M1 (v + sc_M1 + 1) = v + sc_M + 1.
  Proof.
    unfold shift. destruct (Nat.leb sc_M1 sc_M) eqn:Hb.
    - apply (proj1 (Nat.leb_le sc_M1 sc_M)) in Hb. lia.
    - assert (Hnot : ~ sc_M1 <= sc_M).
      { intro Hle. apply (proj2 (Nat.leb_le sc_M1 sc_M)) in Hle.
        rewrite Hle in Hb. discriminate Hb. }
      lia.
  Qed.

  (* --- Filter fusion and commutation (for the common-agent block) --- *)

  Local Lemma filter_fusion (P Q : (nat * A) -> bool) (l : list (nat * A)) :
    filter P (filter Q l) = filter (fun x => P x && Q x) l.
  Proof.
    induction l as [|h t IH].
    - reflexivity.
    - cbn [filter].
      destruct (Q h) eqn:Hq; destruct (P h) eqn:Hp; cbn [filter].
      + rewrite Hp. cbn [filter]. rewrite IH. reflexivity.
      + rewrite Hp. cbn [filter]. rewrite IH. reflexivity.
      + rewrite IH. reflexivity.
      + rewrite IH. reflexivity.
  Qed.

  Local Lemma filter_comm (P Q : (nat * A) -> bool) (l : list (nat * A)) :
    filter P (filter Q l) = filter Q (filter P l).
  Proof.
    rewrite (filter_fusion P Q l), (filter_fusion Q P l).
    apply (filter_ext_in (fun x => P x && Q x) (fun x => Q x && P x) l).
    intros x Hx.
    change ((P x && Q x) = (Q x && P x)).
    destruct (P x) eqn:Hp; destruct (Q x) eqn:Hq; simpl; reflexivity.
  Qed.

  (* --- Structural decomposition of the double-splices' agent lists --- *)

  Local Lemma sc_agents_N1 : nt_agents sc_N1 = filter (sc_rem2 a b) (nt_agents N) ++ sc_F1.
  Proof.
    unfold sc_N1, raw_splice, splice_agents, sc_F1, sc_rem2. reflexivity.
  Qed.

  Local Lemma sc_agents_N2 : nt_agents sc_N2 = filter (sc_rem2 c d) (nt_agents N) ++ sc_F2.
  Proof.
    unfold sc_N2, raw_splice, splice_agents, sc_F2, sc_rem2. reflexivity.
  Qed.

  (* The freshened RHS blocks survive the "remove the other pair" filter. *)
  Local Lemma sc_keep_fresh_cd : filter (sc_rem2 c d) sc_F1 = sc_F1.
  Proof.
    change (filter (fun p : nat * A => negb (Nat.eqb (fst p) c) && negb (Nat.eqb (fst p) d)) sc_F1 = sc_F1).
    exact (splice_keep_keeps_fresh A N c d r1 Hc Hd).
  Qed.

  Local Lemma sc_keep_fresh_ab : filter (sc_rem2 a b) sc_F2 = sc_F2.
  Proof.
    change (filter (fun p : nat * A => negb (Nat.eqb (fst p) a) && negb (Nat.eqb (fst p) b)) sc_F2 = sc_F2).
    exact (splice_keep_keeps_fresh A N a b r2 Ha Hb).
  Qed.

  Local Lemma sc_agents_N12 : nt_agents sc_N12 = (sc_C ++ sc_F1) ++ sc_F2p.
  Proof.
    assert (HL : nt_agents sc_N12 = (filter (sc_rem2 c d) (filter (sc_rem2 a b) (nt_agents N)) ++ sc_F1) ++ sc_F2p).
    { unfold sc_N12, raw_splice, splice_agents.
      change (filter (sc_rem2 c d) (nt_agents sc_N1) ++ sc_F2p
              = (filter (sc_rem2 c d) (filter (sc_rem2 a b) (nt_agents N)) ++ sc_F1) ++ sc_F2p).
      rewrite sc_agents_N1.
      rewrite (filter_app (sc_rem2 c d) (filter (sc_rem2 a b) (nt_agents N)) sc_F1).
      rewrite sc_keep_fresh_cd.
      reflexivity. }
    assert (HR : (sc_C ++ sc_F1) ++ sc_F2p = (filter (sc_rem2 c d) (filter (sc_rem2 a b) (nt_agents N)) ++ sc_F1) ++ sc_F2p).
    { unfold sc_C.
      rewrite (filter_comm (sc_rem2 a b) (sc_rem2 c d) (nt_agents N)).
      reflexivity. }
    rewrite HL, HR. reflexivity.
  Qed.

  Local Lemma sc_agents_N21 : nt_agents sc_N21 = (sc_C ++ sc_F2) ++ sc_F1p.
  Proof.
    assert (HL : nt_agents sc_N21 = (filter (sc_rem2 a b) (filter (sc_rem2 c d) (nt_agents N)) ++ sc_F2) ++ sc_F1p).
    { unfold sc_N21, raw_splice, splice_agents.
      change (filter (sc_rem2 a b) (nt_agents sc_N2) ++ sc_F1p
              = (filter (sc_rem2 a b) (filter (sc_rem2 c d) (nt_agents N)) ++ sc_F2) ++ sc_F1p).
      rewrite sc_agents_N2.
      rewrite (filter_app (sc_rem2 a b) (filter (sc_rem2 c d) (nt_agents N)) sc_F2).
      rewrite sc_keep_fresh_ab.
      reflexivity. }
    assert (HR : (sc_C ++ sc_F2) ++ sc_F1p = (filter (sc_rem2 a b) (filter (sc_rem2 c d) (nt_agents N)) ++ sc_F2) ++ sc_F1p).
    { unfold sc_C. reflexivity. }
    rewrite HL, HR. reflexivity.
  Qed.

  (* --- The renaming applied to an agent pair, and map helpers --- *)

  (* Shift the id by [comm_map], keep the label. *)
  Local Definition cm_pair (p : nat * A) : nat * A :=
    (comm_map sc_M sc_M1 sc_M2 (fst p), snd p).

  (* [x <= u] and [x <= v] imply [x <= min u v]. *)
  Local Lemma nat_le_min (x u v : nat) : x <= u -> x <= v -> x <= Nat.min u v.
  Proof.
    intros Hxu Hxv.
    destruct (Nat.leb u v) eqn:Huv.
    - apply (proj1 (Nat.leb_le u v)) in Huv.
      rewrite (Nat.min_l u v Huv). exact Hxu.
    - assert (Hnot : ~ u <= v).
      { intro H. apply (proj2 (Nat.leb_le u v)) in H. rewrite H in Huv. discriminate. }
      assert (Hle : v <= u). { lia. }
      rewrite (Nat.min_r u v Hle). exact Hxv.
  Qed.

  (* Pointwise equality on the elements of [l] implies equality of the maps. *)
  Local Lemma map_ptw (f g : nat * A -> nat * A) (l : list (nat * A)) :
    (forall x, In x l -> f x = g x) -> map f l = map g l.
  Proof.
    induction l as [|h t IH]; intros Hpt; simpl.
    - reflexivity.
    - assert (Hh : f h = g h). { exact (Hpt h (in_eq h t)). }
      rewrite Hh.
      assert (Ht : forall x, In x t -> f x = g x).
      { intros x Hx. exact (Hpt x (in_cons h x t Hx)). }
      rewrite (IH Ht). reflexivity.
  Qed.

  (* A freshened id of [N] (relative to the [r1] RHS) is an agent of [sc_N1],
     hence bounded by [sc_M1]. *)
  Local Lemma sc_M1_ge_fresh1 (q : nat * A) (Hq : In q (nt_agents (ru_rhs r1))) :
    fresh_id A N (fst q) <= sc_M1.
  Proof.
    unfold sc_M1, max_agent_id.
    assert (Hag : In (fresh_id A N (fst q), snd q) (nt_agents sc_N1)).
    { unfold sc_N1, raw_splice, splice_agents.
      apply in_or_app. right.
      apply (proj2 (in_map_iff (fun p : nat * A => (fresh_id A N (fst p), snd p))
             (nt_agents (ru_rhs r1)) (fresh_id A N (fst q), snd q))).
      exists q. split.
      - reflexivity.
      - exact Hq. }
    exact (list_max_upper_bound (map fst (nt_agents sc_N1)) (fresh_id A N (fst q))
           (In_map fst (nt_agents sc_N1) (fresh_id A N (fst q), snd q) Hag)).
  Qed.

  (* --- [cm_pair] acts as the identity on the common block --- *)

  Local Lemma sc_map_C : map cm_pair sc_C = sc_C.
  Proof.
    assert (Hpt : forall p, In p sc_C -> cm_pair p = p).
    { intros p Hp.
      destruct p as [pid plbl].
      unfold cm_pair.
      f_equal.
      apply cm_id.
      apply nat_le_min.
      - apply (proj1 (filter_In (sc_rem2 a b) (pid, plbl) (filter (sc_rem2 c d) (nt_agents N)))) in Hp.
        destruct Hp as [Hp _].
        apply (proj1 (filter_In (sc_rem2 c d) (pid, plbl) (nt_agents N))) in Hp.
        destruct Hp as [Hp _].
        specialize (list_max_upper_bound (map fst (nt_agents N)) pid
                   (In_map fst (nt_agents N) (pid, plbl) Hp)) as HleM.
        unfold sc_M, max_agent_id in HleM.
        exact HleM.
      - apply (proj1 (filter_In (sc_rem2 a b) (pid, plbl) (filter (sc_rem2 c d) (nt_agents N)))) in Hp.
        destruct Hp as [Hp Hab].
        apply (proj1 (filter_In (sc_rem2 c d) (pid, plbl) (nt_agents N))) in Hp.
        destruct Hp as [Hp _].
        assert (Hp_ab : In (pid, plbl) (filter (sc_rem2 a b) (nt_agents N))).
        { apply (proj2 (filter_In (sc_rem2 a b) (pid, plbl) (nt_agents N))). split.
          - exact Hp.
          - exact Hab. }
        assert (Hp_N1 : In (pid, plbl) (nt_agents sc_N1)).
        { unfold sc_N1, raw_splice, splice_agents.
          apply in_or_app. left. exact Hp_ab. }
        specialize (list_max_upper_bound (map fst (nt_agents sc_N1)) pid
                   (In_map fst (nt_agents sc_N1) (pid, plbl) Hp_N1)) as HleM1.
        unfold sc_M1, max_agent_id in HleM1.
        exact HleM1. }
    assert (H1 : map cm_pair sc_C = map (fun p : nat * A => p) sc_C).
    { exact (map_ptw cm_pair (fun p : nat * A => p) sc_C Hpt). }
    rewrite H1.
    apply map_id.
  Qed.

  (* --- [cm_pair] lands the [r1]-RHS block on the other order's [r1]-RHS block --- *)

  Local Lemma sc_map_F1 : map cm_pair sc_F1 = sc_F1p.
  Proof.
    unfold sc_F1, sc_F1p.
    rewrite (map_map (fun q : nat * A => (fresh_id A N (fst q), snd q)) cm_pair (nt_agents (ru_rhs r1))).
    apply (map_ptw (fun q : nat * A => cm_pair (fresh_id A N (fst q), snd q))
                   (fun q : nat * A => (fresh_id A sc_N2 (fst q), snd q))
                   (nt_agents (ru_rhs r1))).
    intros q Hq.
    unfold cm_pair.
    simpl.
    f_equal.
    assert (Hcm : comm_map sc_M sc_M1 sc_M2 (fresh_id A N (fst q)) = shift sc_M2 sc_M (fresh_id A N (fst q))).
    { apply cm_r1.
      - unfold fresh_id, sc_M, max_agent_id. lia.
      - exact (sc_M1_ge_fresh1 q Hq). }
    rewrite Hcm.
    change (shift sc_M2 sc_M (sc_M + 1 + fst q) = sc_M2 + 1 + fst q).
    assert (Harg : sc_M + 1 + fst q = fst q + sc_M + 1). { lia. }
    rewrite Harg.
    rewrite (shift_r1 (fst q)).
    lia.
  Qed.

  (* --- [cm_pair] lands the [r2]-RHS block on the other order's [r2]-RHS block --- *)

  Local Lemma sc_map_F2p : map cm_pair sc_F2p = sc_F2.
  Proof.
    unfold sc_F2p, sc_F2.
    rewrite (map_map (fun q : nat * A => (fresh_id A sc_N1 (fst q), snd q)) cm_pair (nt_agents (ru_rhs r2))).
    apply (map_ptw (fun q : nat * A => cm_pair (fresh_id A sc_N1 (fst q), snd q))
                   (fun q : nat * A => (fresh_id A N (fst q), snd q))
                   (nt_agents (ru_rhs r2))).
    intros q Hq.
    unfold cm_pair.
    simpl.
    f_equal.
    assert (Hcm : comm_map sc_M sc_M1 sc_M2 (fresh_id A sc_N1 (fst q)) = shift sc_M sc_M1 (fresh_id A sc_N1 (fst q))).
    { apply cm_r2.
      - unfold fresh_id, sc_M1, max_agent_id. lia. }
    rewrite Hcm.
    change (shift sc_M sc_M1 (sc_M1 + 1 + fst q) = sc_M + 1 + fst q).
    assert (Harg : sc_M1 + 1 + fst q = fst q + sc_M1 + 1). { lia. }
    rewrite Harg.
    rewrite (shift_r2 (fst q)).
    lia.
  Qed.

  (* --- Swapping the two RHS blocks (the common block stays put) --- *)

  Local Lemma sc_perm_blocks : Permutation ((sc_C ++ sc_F1p) ++ sc_F2) ((sc_C ++ sc_F2) ++ sc_F1p).
  Proof.
    rewrite <- app_assoc.
    rewrite <- app_assoc.
    apply Permutation_app_head.
    apply Permutation_app_comm.
  Qed.

  (* --- The [ni_agents] field: the renamed agents of [sc_N12] permute [sc_N21] --- *)

  Local Lemma sc_ni_agents : Permutation (map cm_pair (nt_agents sc_N12)) (nt_agents sc_N21).
  Proof.
    rewrite sc_agents_N12, sc_agents_N21.
    rewrite (map_app cm_pair (sc_C ++ sc_F1) sc_F2p).
    rewrite (map_app cm_pair sc_C sc_F1).
    rewrite sc_map_C, sc_map_F1, sc_map_F2p.
    exact sc_perm_blocks.
  Qed.

  (* --- [ni_inj]: [comm_map] is injective on the agents of [sc_N12] --- *)

  (* The three blocks of [sc_N12]'s agents, by id. *)
  Local Definition ids_C   := map fst sc_C.
  Local Definition ids_F1  := map fst sc_F1.
  Local Definition ids_F2p := map fst sc_F2p.

  (* [x] in the [r1]-RHS id block means [x = fresh_id A N (fst p)] for some [p]
     in the [r1] RHS (two-level [in_map_iff] through [sc_F1]). *)
  Local Lemma in_ids_F1 (x : nat) (Hx : In x ids_F1) :
    exists p, In p (nt_agents (ru_rhs r1)) /\ x = fresh_id A N (fst p).
  Proof.
    unfold ids_F1 in Hx.
    apply (proj1 (in_map_iff fst sc_F1 x)) in Hx.
    destruct Hx as [q [Hqx Hq]].
    unfold sc_F1 in Hq.
    apply (proj1 (in_map_iff (fun p : nat * A => (fresh_id A N (fst p), snd p)) (nt_agents (ru_rhs r1)) q)) in Hq.
    destruct Hq as [p [Hqp Hp]].
    exists p.
    split.
    - exact Hp.
    - subst q.
      simpl in Hqx.
      symmetry.
      exact Hqx.
  Qed.

  (* Same for the [r2]-RHS id block, relative to [sc_N1]. *)
  Local Lemma in_ids_F2p (x : nat) (Hx : In x ids_F2p) :
    exists p, In p (nt_agents (ru_rhs r2)) /\ x = fresh_id A sc_N1 (fst p).
  Proof.
    unfold ids_F2p in Hx.
    apply (proj1 (in_map_iff fst sc_F2p x)) in Hx.
    destruct Hx as [q [Hqx Hq]].
    unfold sc_F2p in Hq.
    apply (proj1 (in_map_iff (fun p : nat * A => (fresh_id A sc_N1 (fst p), snd p)) (nt_agents (ru_rhs r2)) q)) in Hq.
    destruct Hq as [p [Hqp Hp]].
    exists p.
    split.
    - exact Hp.
    - subst q.
      simpl in Hqx.
      symmetry.
      exact Hqx.
  Qed.

  (* [x] in the common block: [comm_map] fixes it. *)
  Local Lemma blkC (x : nat) : In x ids_C -> comm_map sc_M sc_M1 sc_M2 x = x.
  Proof.
    intros Hx.
    unfold ids_C in Hx.
    apply (proj1 (in_map_iff fst sc_C x)) in Hx.
    destruct Hx as [p [Hpx Hp]].
    subst x.
    apply cm_id.
    apply nat_le_min.
    - apply (proj1 (filter_In (sc_rem2 a b) p (filter (sc_rem2 c d) (nt_agents N)))) in Hp.
      destruct Hp as [Hp _].
      apply (proj1 (filter_In (sc_rem2 c d) p (nt_agents N))) in Hp.
      destruct Hp as [Hp _].
      specialize (list_max_upper_bound (map fst (nt_agents N)) (fst p)
                 (In_map fst (nt_agents N) p Hp)) as HleM.
      unfold sc_M, max_agent_id in HleM.
      exact HleM.
    - apply (proj1 (filter_In (sc_rem2 a b) p (filter (sc_rem2 c d) (nt_agents N)))) in Hp.
      destruct Hp as [Hp Hab].
      apply (proj1 (filter_In (sc_rem2 c d) p (nt_agents N))) in Hp.
      destruct Hp as [Hp _].
      assert (Hp_ab : In p (filter (sc_rem2 a b) (nt_agents N))).
      { apply (proj2 (filter_In (sc_rem2 a b) p (nt_agents N))). split.
        - exact Hp.
        - exact Hab. }
      assert (Hp_N1 : In p (nt_agents sc_N1)).
      { unfold sc_N1, raw_splice, splice_agents.
        apply in_or_app. left. exact Hp_ab. }
      specialize (list_max_upper_bound (map fst (nt_agents sc_N1)) (fst p)
                 (In_map fst (nt_agents sc_N1) p Hp_N1)) as HleM1.
      unfold sc_M1, max_agent_id in HleM1.
      exact HleM1.
  Qed.

  (* [x] in the [r1]-RHS block: [comm_map] shifts it by [sc_M2 - sc_M]. *)
  Local Lemma blkF1 (x : nat) : In x ids_F1 -> comm_map sc_M sc_M1 sc_M2 x = shift sc_M2 sc_M x.
  Proof.
    intros Hx.
    destruct (in_ids_F1 x Hx) as [p [Hp Hxp]].
    subst x.
    apply cm_r1.
    - unfold fresh_id, sc_M, max_agent_id. lia.
    - exact (sc_M1_ge_fresh1 p Hp).
  Qed.

  (* [x] in the [r2]-RHS block: [comm_map] shifts it by [sc_M - sc_M1]. *)
  Local Lemma blkF2p (x : nat) : In x ids_F2p -> comm_map sc_M sc_M1 sc_M2 x = shift sc_M sc_M1 x.
  Proof.
    intros Hx.
    destruct (in_ids_F2p x Hx) as [p [Hp Hxp]].
    subst x.
    apply cm_r2.
    - unfold fresh_id, sc_M1, max_agent_id. lia.
  Qed.

  (* The common block's ids are bounded by [sc_M2] (it is a subset of [sc_N2]). *)
  Local Lemma C_le_M2 (x : nat) : In x ids_C -> x <= sc_M2.
  Proof.
    intros Hx.
    unfold ids_C in Hx.
    apply (proj1 (in_map_iff fst sc_C x)) in Hx.
    destruct Hx as [p [Hpx Hp]].
    subst x.
    assert (Hp_N2 : In p (nt_agents sc_N2)).
    { unfold sc_N2, raw_splice, splice_agents.
      apply in_or_app. left.
      apply (proj2 (filter_In (sc_rem2 c d) p (nt_agents N))). split.
      - apply (proj1 (filter_In (sc_rem2 a b) p (filter (sc_rem2 c d) (nt_agents N)))) in Hp.
        destruct Hp as [Hp _].
        apply (proj1 (filter_In (sc_rem2 c d) p (nt_agents N))) in Hp.
        destruct Hp as [Hp _].
        exact Hp.
      - apply (proj1 (filter_In (sc_rem2 a b) p (filter (sc_rem2 c d) (nt_agents N)))) in Hp.
        destruct Hp as [Hp _].
        apply (proj1 (filter_In (sc_rem2 c d) p (nt_agents N))) in Hp.
        destruct Hp as [_ Hcd].
        exact Hcd. }
    specialize (list_max_upper_bound (map fst (nt_agents sc_N2)) (fst p)
               (In_map fst (nt_agents sc_N2) p Hp_N2)) as HleM2.
    unfold sc_M2, max_agent_id in HleM2.
    exact HleM2.
  Qed.

  (* Image bounds: the three blocks land in pairwise disjoint id ranges. *)
  Local Lemma img_C (x : nat) : In x ids_C -> comm_map sc_M sc_M1 sc_M2 x <= sc_M2.
  Proof.
    intros Hx. rewrite (blkC x Hx). exact (C_le_M2 x Hx).
  Qed.

  Local Lemma img_F1 (x : nat) : In x ids_F1 -> comm_map sc_M sc_M1 sc_M2 x > sc_M2.
  Proof.
    intros Hx.
    destruct (in_ids_F1 x Hx) as [p [Hp Hxp]].
    subst x.
    assert (Hcm : comm_map sc_M sc_M1 sc_M2 (fresh_id A N (fst p)) = shift sc_M2 sc_M (fresh_id A N (fst p))).
    { apply cm_r1.
      - unfold fresh_id, sc_M, max_agent_id. lia.
      - exact (sc_M1_ge_fresh1 p Hp). }
    rewrite Hcm.
    change (shift sc_M2 sc_M (sc_M + 1 + fst p) > sc_M2).
    assert (Harg : sc_M + 1 + fst p = fst p + sc_M + 1). { lia. }
    rewrite Harg.
    rewrite (shift_r1 (fst p)).
    lia.
  Qed.

  Local Lemma img_F2p (x : nat) : In x ids_F2p -> comm_map sc_M sc_M1 sc_M2 x > sc_M.
  Proof.
    intros Hx.
    destruct (in_ids_F2p x Hx) as [p [Hp Hxp]].
    subst x.
    assert (Hcm : comm_map sc_M sc_M1 sc_M2 (fresh_id A sc_N1 (fst p)) = shift sc_M sc_M1 (fresh_id A sc_N1 (fst p))).
    { apply cm_r2.
      - unfold fresh_id, sc_M1, max_agent_id. lia. }
    rewrite Hcm.
    change (shift sc_M sc_M1 (sc_M1 + 1 + fst p) > sc_M).
    assert (Harg : sc_M1 + 1 + fst p = fst p + sc_M1 + 1). { lia. }
    rewrite Harg.
    rewrite (shift_r2 (fst p)).
    lia.
  Qed.

  (* The [r2]-RHS block's image is also bounded by [sc_M2] (so it is disjoint
     from the [r1]-RHS block's image, which lies above [sc_M2]). *)
  Local Lemma img_F2p_le_M2 (x : nat) : In x ids_F2p -> comm_map sc_M sc_M1 sc_M2 x <= sc_M2.
  Proof.
    intros Hx.
    destruct (in_ids_F2p x Hx) as [p [Hp Hxp]].
    subst x.
    assert (Hcm : comm_map sc_M sc_M1 sc_M2 (fresh_id A sc_N1 (fst p)) = sc_M + 1 + fst p).
    { assert (Hcm1 : comm_map sc_M sc_M1 sc_M2 (fresh_id A sc_N1 (fst p)) = shift sc_M sc_M1 (fresh_id A sc_N1 (fst p))).
      { apply cm_r2.
        unfold fresh_id, sc_M1, max_agent_id. lia. }
      rewrite Hcm1.
      change (shift sc_M sc_M1 (sc_M1 + 1 + fst p) = sc_M + 1 + fst p).
      assert (Harg : sc_M1 + 1 + fst p = fst p + sc_M1 + 1). { lia. }
      rewrite Harg.
      rewrite (shift_r2 (fst p)).
      lia. }
    rewrite Hcm.
    change (fresh_id A N (fst p) <= sc_M2).
    assert (Hag : In (fresh_id A N (fst p), snd p) (nt_agents sc_N2)).
    { unfold sc_N2, raw_splice, splice_agents.
      apply in_or_app. right.
      apply (proj2 (in_map_iff (fun q : nat * A => (fresh_id A N (fst q), snd q))
             (nt_agents (ru_rhs r2)) (fresh_id A N (fst p), snd p))).
      exists p. split.
      - reflexivity.
      - exact Hp. }
    specialize (list_max_upper_bound (map fst (nt_agents sc_N2)) (fresh_id A N (fst p))
               (In_map fst (nt_agents sc_N2) (fresh_id A N (fst p), snd p) Hag)) as Hle.
    unfold sc_M2, max_agent_id in Hle.
    exact Hle.
  Qed.

  (* The common block's image is bounded by [sc_M] (sharper than [img_C]; needed
     to separate it from the [r2]-RHS block's image, which lies above [sc_M]). *)
  Local Lemma img_C_le_M (x : nat) : In x ids_C -> comm_map sc_M sc_M1 sc_M2 x <= sc_M.
  Proof.
    intros Hx.
    rewrite (blkC x Hx).
    unfold ids_C in Hx.
    apply (proj1 (in_map_iff fst sc_C x)) in Hx.
    destruct Hx as [p [Hpx Hp]].
    subst x.
    apply (proj1 (filter_In (sc_rem2 a b) p (filter (sc_rem2 c d) (nt_agents N)))) in Hp.
    destruct Hp as [Hp _].
    apply (proj1 (filter_In (sc_rem2 c d) p (nt_agents N))) in Hp.
    destruct Hp as [Hp _].
    specialize (list_max_upper_bound (map fst (nt_agents N)) (fst p)
               (In_map fst (nt_agents N) p Hp)) as HleM.
    unfold sc_M, max_agent_id in HleM.
    exact HleM.
  Qed.

  (* --- Exact image values on the two RHS blocks (for within-block injectivity) --- *)

  Local Lemma cm_F1_val (p : nat * A) (Hp : In p (nt_agents (ru_rhs r1))) :
    comm_map sc_M sc_M1 sc_M2 (fresh_id A N (fst p)) = fst p + sc_M2 + 1.
  Proof.
    assert (Hin : In (fresh_id A N (fst p)) ids_F1).
    { unfold ids_F1.
      apply (proj2 (in_map_iff fst sc_F1 (fresh_id A N (fst p)))).
      exists (fresh_id A N (fst p), snd p).
      split.
      - reflexivity.
      - unfold sc_F1.
        apply (proj2 (in_map_iff (fun q : nat * A => (fresh_id A N (fst q), snd q)) (nt_agents (ru_rhs r1)) (fresh_id A N (fst p), snd p))).
        exists p.
        split.
        + reflexivity.
        + exact Hp. }
    assert (Hcm : comm_map sc_M sc_M1 sc_M2 (fresh_id A N (fst p)) = shift sc_M2 sc_M (fresh_id A N (fst p))).
    { exact (blkF1 (fresh_id A N (fst p)) Hin). }
    rewrite Hcm.
    unfold fresh_id.
    assert (Harg : max_agent_id A N + 1 + fst p = fst p + sc_M + 1). { unfold sc_M. lia. }
    rewrite Harg.
    rewrite (shift_r1 (fst p)).
    reflexivity.
  Qed.

  Local Lemma cm_F2p_val (p : nat * A) (Hp : In p (nt_agents (ru_rhs r2))) :
    comm_map sc_M sc_M1 sc_M2 (fresh_id A sc_N1 (fst p)) = fst p + sc_M + 1.
  Proof.
    assert (Hin : In (fresh_id A sc_N1 (fst p)) ids_F2p).
    { unfold ids_F2p.
      apply (proj2 (in_map_iff fst sc_F2p (fresh_id A sc_N1 (fst p)))).
      exists (fresh_id A sc_N1 (fst p), snd p).
      split.
      - reflexivity.
      - unfold sc_F2p.
        apply (proj2 (in_map_iff (fun q : nat * A => (fresh_id A sc_N1 (fst q), snd q)) (nt_agents (ru_rhs r2)) (fresh_id A sc_N1 (fst p), snd p))).
        exists p.
        split.
        + reflexivity.
        + exact Hp. }
    assert (Hcm : comm_map sc_M sc_M1 sc_M2 (fresh_id A sc_N1 (fst p)) = shift sc_M sc_M1 (fresh_id A sc_N1 (fst p))).
    { exact (blkF2p (fresh_id A sc_N1 (fst p)) Hin). }
    rewrite Hcm.
    unfold fresh_id.
    assert (Harg : max_agent_id A sc_N1 + 1 + fst p = fst p + sc_M1 + 1). { unfold sc_M1. lia. }
    rewrite Harg.
    rewrite (shift_r2 (fst p)).
    reflexivity.
  Qed.

  (* --- [comm_map] is injective on each block --- *)

  Local Lemma inj_C (a1 a2 : nat) : In a1 ids_C -> In a2 ids_C ->
    comm_map sc_M sc_M1 sc_M2 a1 = comm_map sc_M sc_M1 sc_M2 a2 -> a1 = a2.
  Proof.
    intros H1 H2 Heq.
    rewrite (blkC a1 H1), (blkC a2 H2) in Heq.
    exact Heq.
  Qed.

  Local Lemma inj_F1 (a1 a2 : nat) : In a1 ids_F1 -> In a2 ids_F1 ->
    comm_map sc_M sc_M1 sc_M2 a1 = comm_map sc_M sc_M1 sc_M2 a2 -> a1 = a2.
  Proof.
    intros H1 H2 Heq.
    destruct (in_ids_F1 a1 H1) as [p1 [Hp1 H1e]].
    destruct (in_ids_F1 a2 H2) as [p2 [Hp2 H2e]].
    subst a1 a2.
    rewrite (cm_F1_val p1 Hp1), (cm_F1_val p2 Hp2) in Heq.
    assert (Hcancel : fst p1 = fst p2). { lia. }
    exact (f_equal (fresh_id A N) Hcancel).
  Qed.

  Local Lemma inj_F2p (a1 a2 : nat) : In a1 ids_F2p -> In a2 ids_F2p ->
    comm_map sc_M sc_M1 sc_M2 a1 = comm_map sc_M sc_M1 sc_M2 a2 -> a1 = a2.
  Proof.
    intros H1 H2 Heq.
    destruct (in_ids_F2p a1 H1) as [p1 [Hp1 H1e]].
    destruct (in_ids_F2p a2 H2) as [p2 [Hp2 H2e]].
    subst a1 a2.
    rewrite (cm_F2p_val p1 Hp1), (cm_F2p_val p2 Hp2) in Heq.
    assert (Hcancel : fst p1 = fst p2). { lia. }
    exact (f_equal (fresh_id A sc_N1) Hcancel).
  Qed.

  (* --- Decomposing membership in the union of the three id blocks --- *)

  Local Definition ids_N12 := (ids_C ++ ids_F1) ++ ids_F2p.

  Local Lemma in_ids_N12 (x : nat) : In x ids_N12 -> In x ids_C \/ In x ids_F1 \/ In x ids_F2p.
  Proof.
    intros Hx.
    unfold ids_N12.
    apply in_app_or in Hx.
    destruct Hx as [Hleft|Hright].
    - apply in_app_or in Hleft.
      destruct Hleft as [Hc|Hf1].
      + left. exact Hc.
      + right. left. exact Hf1.
    - right. right. exact Hright.
  Qed.

  Local Lemma ids_N12_eq :
    map fst (nt_agents sc_N12) = ids_N12.
  Proof.
    unfold ids_N12, ids_C, ids_F1, ids_F2p.
    rewrite sc_agents_N12.
    rewrite (map_app fst (sc_C ++ sc_F1) sc_F2p).
    rewrite (map_app fst sc_C sc_F1).
    reflexivity.
  Qed.

  (* --- [ni_inj]: [comm_map] is injective on the agents of [sc_N12] --- *)

  Local Lemma sc_ni_inj : forall a1 a2,
    has_agent A sc_N12 a1 -> has_agent A sc_N12 a2 ->
    comm_map sc_M sc_M1 sc_M2 a1 = comm_map sc_M sc_M1 sc_M2 a2 -> a1 = a2.
  Proof.
    intros a1 a2 H1 H2 Heq.
    apply (proj1 (has_agent_In A sc_N12 a1)) in H1.
    apply (proj1 (has_agent_In A sc_N12 a2)) in H2.
    rewrite ids_N12_eq in H1, H2.
    assert (H1b : In a1 ids_C \/ In a1 ids_F1 \/ In a1 ids_F2p). { exact (in_ids_N12 a1 H1). }
    assert (H2b : In a2 ids_C \/ In a2 ids_F1 \/ In a2 ids_F2p). { exact (in_ids_N12 a2 H2). }
    destruct H1b as [H1c|H1rest].
    - (* a1 in the common block *)
      destruct H2b as [H2c|H2rest].
      + (* a2 in the common block *)
        exact (inj_C a1 a2 H1c H2c Heq).
      + (* a2 in an RHS block *)
        destruct H2rest as [H2f1|H2f2p].
        * (* a2 in the [r1]-RHS block *)
          exfalso.
          assert (Hc : comm_map sc_M sc_M1 sc_M2 a1 <= sc_M2). { exact (img_C a1 H1c). }
          assert (Hf : sc_M2 < comm_map sc_M sc_M1 sc_M2 a2). { exact (img_F1 a2 H2f1). }
          rewrite Heq in Hc. lia.
        * (* a2 in the [r2]-RHS block *)
          exfalso.
          assert (Hc : comm_map sc_M sc_M1 sc_M2 a1 <= sc_M). { exact (img_C_le_M a1 H1c). }
          assert (Hf : sc_M < comm_map sc_M sc_M1 sc_M2 a2). { exact (img_F2p a2 H2f2p). }
          rewrite Heq in Hc. lia.
    - (* a1 in an RHS block *)
      destruct H1rest as [H1f1|H1f2p].
      * (* a1 in the [r1]-RHS block *)
        destruct H2b as [H2c|H2rest].
        + (* a2 in the common block *)
          exfalso.
          assert (Hf : sc_M2 < comm_map sc_M sc_M1 sc_M2 a1). { exact (img_F1 a1 H1f1). }
          assert (Hc : comm_map sc_M sc_M1 sc_M2 a2 <= sc_M2). { exact (img_C a2 H2c). }
          rewrite <- Heq in Hc. lia.
        + (* a2 in an RHS block *)
          { destruct H2rest as [H2f1|H2f2p].
            - (* a2 in the [r1]-RHS block *)
              exact (inj_F1 a1 a2 H1f1 H2f1 Heq).
            - (* a2 in the [r2]-RHS block *)
              exfalso.
              assert (Hf : sc_M2 < comm_map sc_M sc_M1 sc_M2 a1). { exact (img_F1 a1 H1f1). }
              assert (Hf2 : comm_map sc_M sc_M1 sc_M2 a2 <= sc_M2). { exact (img_F2p_le_M2 a2 H2f2p). }
              rewrite <- Heq in Hf2. lia. }
      * (* a1 in the [r2]-RHS block *)
        destruct H2b as [H2c|H2rest].
        + (* a2 in the common block *)
          exfalso.
          assert (Hf : sc_M < comm_map sc_M sc_M1 sc_M2 a1). { exact (img_F2p a1 H1f2p). }
          assert (Hc : comm_map sc_M sc_M1 sc_M2 a2 <= sc_M). { exact (img_C_le_M a2 H2c). }
          rewrite <- Heq in Hc. lia.
        + (* a2 in an RHS block *)
          { destruct H2rest as [H2f1|H2f2p].
            - (* a2 in the [r1]-RHS block *)
              exfalso.
              assert (Hf2 : comm_map sc_M sc_M1 sc_M2 a1 <= sc_M2). { exact (img_F2p_le_M2 a1 H1f2p). }
              assert (Hf : sc_M2 < comm_map sc_M sc_M1 sc_M2 a2). { exact (img_F1 a2 H2f1). }
              rewrite Heq in Hf2. lia.
            - (* a2 in the [r2]-RHS block *)
              exact (inj_F2p a1 a2 H1f2p H2f2p Heq). }
  Qed.

  (* ========================================================================== *)
  (* Stage 5: the [ni_links] field.                                             *)
  (*                                                                            *)
  (* The links of [sc_N12] decompose into three blocks: the kept links (from    *)
  (* [N], surviving both fired pairs), the [r1]-RHS fresh links, and the        *)
  (* [r2]-RHS fresh links. The renaming [comm_map] carries the kept block to    *)
  (* the kept block of [sc_N21] (the crux: the endpoint correspondence) and     *)
  (* swaps the two fresh blocks.                                                *)
  (* ========================================================================== *)

  (* Rename both endpoints of a link by [comm_map]. *)
  Local Definition cm_pair_link (l : port_ref * port_ref) : port_ref * port_ref :=
    ((comm_map sc_M sc_M1 sc_M2 (fst (fst l)), snd (fst l)),
     (comm_map sc_M sc_M1 sc_M2 (fst (snd l)), snd (snd l))).

  (* The four rewire maps (by [r1] or [r2], relative to [N], [sc_N1], or [sc_N2]). *)
  Local Definition rw1  (l : port_ref * port_ref) : port_ref * port_ref := rewire_link A Ar N a b r1 l.
  Local Definition rw2' (l : port_ref * port_ref) : port_ref * port_ref := rewire_link A Ar N c d r2 l.
  Local Definition rw2  (l : port_ref * port_ref) : port_ref * port_ref := rewire_link A Ar sc_N1 c d r2 l.
  Local Definition rw1' (l : port_ref * port_ref) : port_ref * port_ref := rewire_link A Ar sc_N2 a b r1 l.

  (* The fresh-link blocks (RHS links, freshened relative to the indicated net). *)
  Local Definition fl1  := map (fun l : port_ref * port_ref => (freshen_pr A N (fst l), freshen_pr A N (snd l))) (nt_links (ru_rhs r1)).
  Local Definition fl2  := map (fun l : port_ref * port_ref => (freshen_pr A N (fst l), freshen_pr A N (snd l))) (nt_links (ru_rhs r2)).
  Local Definition fl1p := map (fun l : port_ref * port_ref => (freshen_pr A sc_N2 (fst l), freshen_pr A sc_N2 (snd l))) (nt_links (ru_rhs r1)).
  Local Definition fl2p := map (fun l : port_ref * port_ref => (freshen_pr A sc_N1 (fst l), freshen_pr A sc_N1 (snd l))) (nt_links (ru_rhs r2)).

  (* The kept links: links of [N] that are neither of the two fired main–main links. *)
  Local Definition Lk :=
    filter (fun l : port_ref * port_ref =>
             negb (is_main_main_link a b l) && negb (is_main_main_link c d l)) (nt_links N).

  (* --- Foundational facts --- *)

  (* A fresh id of [N] is strictly above [sc_M], hence distinct from [a b c d]. *)
  Local Lemma fresh_id_gt_scM (x : nat) : fresh_id A N x > sc_M.
  Proof.
    unfold fresh_id, sc_M, max_agent_id. lia.
  Qed.

  (* [a b c d] are agents of [N], hence bounded by [sc_M]. *)
  Local Lemma abcd_le_scM (x : nat) (Hx : has_agent A N x) : x <= sc_M.
  Proof.
    apply (proj1 (has_agent_In A N x)) in Hx.
    specialize (list_max_upper_bound (map fst (nt_agents N)) x Hx) as Hle.
    unfold sc_M, max_agent_id in Hle.
    exact Hle.
  Qed.

  (* [rewire_endpoint ... a1 a2 r] leaves [(x, p)] unchanged when [x] is neither [a1] nor [a2]. *)
  Local Lemma rewire_endpoint_fixed (a1 a2 : nat) (r : Rule A) (x : nat) (p : nat)
        (Hx1 : x <> a1) (Hx2 : x <> a2) :
    rewire_endpoint A Ar N a1 a2 r (x, p) = (x, p).
  Proof.
    unfold rewire_endpoint.
    destruct (Nat.eqb x a1) eqn:H1.
    - exfalso. apply (proj1 (Nat.eqb_eq x a1)) in H1. apply Hx1. exact H1.
    - destruct (Nat.eqb x a2) eqn:H2.
      + exfalso. apply (proj1 (Nat.eqb_eq x a2)) in H2. apply Hx2. exact H2.
      + reflexivity.
  Qed.

  (* [rewire_endpoint ... a1 a2 r] cannot produce a main port [(t, 0)] with [t <= sc_M]
     unless the input already was [(t, 0)]: a rewired endpoint is a fresh id (> [sc_M]). *)
  Local Lemma rewire_endpoint_t0 (a1 a2 : nat) (r : Rule A) (e : port_ref) (t : nat) (Ht : t <= sc_M) :
    rewire_endpoint A Ar N a1 a2 r e = (t, 0) -> e = (t, 0).
  Proof.
    intros H.
    destruct e as [x p].
    unfold rewire_endpoint in H.
    destruct (Nat.eqb x a1) eqn:Hxa.
    - destruct (Nat.leb 1 p && Nat.leb p (Ar (fst (ru_lhs r)))) eqn:Hr.
      + simpl in H.
        destruct (nth (p - 1) (ru_iface r) (0, 0)) as [ia pa].
        change ((fresh_id A N ia, pa) = (t, 0)) in H.
        injection H as Ht0 Hp0.
        unfold fresh_id in Ht0.
        unfold sc_M in Ht.
        lia.
      + simpl in H.
        injection H as Hx Hp0.
        subst x. subst p.
        reflexivity.
    - destruct (Nat.eqb x a2) eqn:Hxb.
      + destruct (Nat.leb 1 p && Nat.leb p (Ar (snd (ru_lhs r)))) eqn:Hr.
        * simpl in H.
          destruct (nth (Ar (fst (ru_lhs r)) + (p - 1)) (ru_iface r) (0, 0)) as [ib pb].
          change ((fresh_id A N ib, pb) = (t, 0)) in H.
          injection H as Ht0 Hp0.
          unfold fresh_id in Ht0.
          unfold sc_M in Ht.
          lia.
        * simpl in H.
          injection H as Hx Hp0.
          subst x. subst p.
          reflexivity.
      + simpl in H.
        injection H as Hx Hp0.
        subst x. subst p.
        reflexivity.
  Qed.

  (* The cross-disjointness facts, in the orientations the rewiring lemmas need. *)
  Local Lemma Hca : c <> a.
  Proof. intro H. apply (proj1 Hdisj). symmetry. exact H. Qed.
  Local Lemma Hcb : c <> b.
  Proof. intro H. apply (proj1 (proj2 (proj2 Hdisj))). symmetry. exact H. Qed.
  Local Lemma Hda : d <> a.
  Proof. intro H. apply (proj1 (proj2 Hdisj)). symmetry. exact H. Qed.
  Local Lemma Hdb : d <> b.
  Proof. intro H. apply (proj2 (proj2 Hdisj)). symmetry. exact H. Qed.
  Local Lemma Hac : a <> c.
  Proof. exact (proj1 Hdisj). Qed.
  Local Lemma Had : a <> d.
  Proof. exact (proj1 (proj2 Hdisj)). Qed.
  Local Lemma Hbc : b <> c.
  Proof. exact (proj1 (proj2 (proj2 Hdisj))). Qed.
  Local Lemma Hbd : b <> d.
  Proof. exact (proj2 (proj2 (proj2 Hdisj))). Qed.

  (* The two agents of each fired pair are distinct (the first conjunct of
     [is_active_pair]), in both orientations. *)
  Local Lemma Hab : a <> b.
  Proof.
    change (a <> b /\ has_agent A N a /\ has_agent A N b /\ has_link A N (a, 0) (b, 0)) in Hap_ab.
    exact (proj1 Hap_ab).
  Qed.
  Local Lemma Hba : b <> a.
  Proof. intro H. apply Hab. symmetry. exact H. Qed.
  Local Lemma Hcd : c <> d.
  Proof.
    change (c <> d /\ has_agent A N c /\ has_agent A N d /\ has_link A N (c, 0) (d, 0)) in Hap_cd.
    exact (proj1 Hap_cd).
  Qed.
  Local Lemma Hdc : d <> c.
  Proof. intro H. apply Hcd. symmetry. exact H. Qed.

  (* [rewire_endpoint ... a b r1] cannot produce [(c, 0)] or [(d, 0)] unless the
     input already was that port: a rewired endpoint carries a fresh id (> [sc_M]),
     while [c] and [d] are bounded by [sc_M]. *)
  Local Lemma rw1_fixes_c0 (e : port_ref) :
    rewire_endpoint A Ar N a b r1 e = (c, 0) -> e = (c, 0).
  Proof.
    intro H.
    apply (rewire_endpoint_t0 a b r1 e c (abcd_le_scM c Hc)) in H.
    exact H.
  Qed.
  Local Lemma rw1_fixes_d0 (e : port_ref) :
    rewire_endpoint A Ar N a b r1 e = (d, 0) -> e = (d, 0).
  Proof.
    intro H.
    apply (rewire_endpoint_t0 a b r1 e d (abcd_le_scM d Hd)) in H.
    exact H.
  Qed.

  (* A link with [is_main_main_link c d l = true] has both [(c, 0)] and [(d, 0)] as endpoints. *)
  Local Lemma mm_cd_endpoints (l : port_ref * port_ref) (H : is_main_main_link c d l = true) :
    link_end l (c, 0) /\ link_end l (d, 0).
  Proof.
    destruct l as [[x u] [y v]].
    unfold is_main_main_link in H.
    simpl in H.
    destruct (Nat.eqb x c) eqn:Hxc.
    - (* x = c: the first disjunct holds *)
      apply (proj1 (Nat.eqb_eq x c)) in Hxc.
      assert (Hxd : Nat.eqb x d = false).
      { destruct (Nat.eqb x d) eqn:Hb.
        - exfalso.
          apply (proj1 (Nat.eqb_eq x d)) in Hb.
          change (c <> d /\ has_agent A N c /\ has_agent A N d /\ has_link A N (c, 0) (d, 0)) in Hap_cd.
          apply (proj1 Hap_cd).
          rewrite Hxc in Hb.
          exact Hb.
        - reflexivity. }
      rewrite Hxd in H.
      simpl in H.
      { destruct (Nat.eqb u 0) eqn:Hu0.
        - destruct (Nat.eqb y d) eqn:Hyd.
          + destruct (Nat.eqb v 0) eqn:Hv0.
            * { split.
                - left.
                  apply (proj1 (Nat.eqb_eq u 0)) in Hu0.
                  subst x. subst u.
                  reflexivity.
                - right.
                  apply (proj1 (Nat.eqb_eq y d)) in Hyd.
                  apply (proj1 (Nat.eqb_eq v 0)) in Hv0.
                  subst y. subst v.
                  reflexivity. }
            * exfalso. simpl in H. discriminate H.
          + exfalso. simpl in H. discriminate H.
        - exfalso. simpl in H. discriminate H. }
    - (* x <> c: the second disjunct holds *)
      simpl in H.
      { destruct (Nat.eqb x d) eqn:Hxd.
        - destruct (Nat.eqb u 0) eqn:Hu0.
          + destruct (Nat.eqb y c) eqn:HyC.
            * { destruct (Nat.eqb v 0) eqn:Hv0.
                + split.
                  - right.
                    apply (proj1 (Nat.eqb_eq y c)) in HyC.
                    apply (proj1 (Nat.eqb_eq v 0)) in Hv0.
                    subst y. subst v.
                    reflexivity.
                  - left.
                    apply (proj1 (Nat.eqb_eq x d)) in Hxd.
                    apply (proj1 (Nat.eqb_eq u 0)) in Hu0.
                    subst x. subst u.
                    reflexivity.
                + exfalso. simpl in H. discriminate H. }
            * exfalso. simpl in H. discriminate H.
          + exfalso. simpl in H. discriminate H.
        - exfalso. simpl in H. discriminate H. }
  Qed.

  (* [rewire_endpoint ... c d r2] cannot produce [(a, 0)] or [(b, 0)] unless the
     input already was that port (symmetric to [rw1_fixes_c0]/[rw1_fixes_d0]). *)
  Local Lemma rw2'_fixes_a0 (e : port_ref) :
    rewire_endpoint A Ar N c d r2 e = (a, 0) -> e = (a, 0).
  Proof.
    intro H.
    apply (rewire_endpoint_t0 c d r2 e a (abcd_le_scM a Ha)) in H.
    exact H.
  Qed.
  Local Lemma rw2'_fixes_b0 (e : port_ref) :
    rewire_endpoint A Ar N c d r2 e = (b, 0) -> e = (b, 0).
  Proof.
    intro H.
    apply (rewire_endpoint_t0 c d r2 e b (abcd_le_scM b Hb)) in H.
    exact H.
  Qed.

  (* A link with [is_main_main_link a b l = true] has both [(a, 0)] and [(b, 0)]
     as endpoints (symmetric to [mm_cd_endpoints]). *)
  Local Lemma mm_ab_endpoints (l : port_ref * port_ref) (H : is_main_main_link a b l = true) :
    link_end l (a, 0) /\ link_end l (b, 0).
  Proof.
    destruct l as [[x u] [y v]].
    unfold is_main_main_link in H.
    simpl in H.
    destruct (Nat.eqb x a) eqn:Hxa.
    - (* x = a: the first disjunct holds *)
      apply (proj1 (Nat.eqb_eq x a)) in Hxa.
      assert (Hxb : Nat.eqb x b = false).
      { destruct (Nat.eqb x b) eqn:Hb.
        - exfalso.
          apply (proj1 (Nat.eqb_eq x b)) in Hb.
          change (a <> b /\ has_agent A N a /\ has_agent A N b /\ has_link A N (a, 0) (b, 0)) in Hap_ab.
          apply (proj1 Hap_ab).
          rewrite Hxa in Hb.
          exact Hb.
        - reflexivity. }
      rewrite Hxb in H.
      simpl in H.
      { destruct (Nat.eqb u 0) eqn:Hu0.
        - destruct (Nat.eqb y b) eqn:Hyb.
          + destruct (Nat.eqb v 0) eqn:Hv0.
            * { split.
                - left.
                  apply (proj1 (Nat.eqb_eq u 0)) in Hu0.
                  subst x. subst u.
                  reflexivity.
                - right.
                  apply (proj1 (Nat.eqb_eq y b)) in Hyb.
                  apply (proj1 (Nat.eqb_eq v 0)) in Hv0.
                  subst y. subst v.
                  reflexivity. }
            * exfalso. simpl in H. discriminate H.
          + exfalso. simpl in H. discriminate H.
        - exfalso. simpl in H. discriminate H. }
    - (* x <> a: the second disjunct holds *)
      simpl in H.
      { destruct (Nat.eqb x b) eqn:Hxb.
        - destruct (Nat.eqb u 0) eqn:Hu0.
          + destruct (Nat.eqb y a) eqn:HyA.
            * { destruct (Nat.eqb v 0) eqn:Hv0.
                + split.
                  - right.
                    apply (proj1 (Nat.eqb_eq y a)) in HyA.
                    apply (proj1 (Nat.eqb_eq v 0)) in Hv0.
                    subst y. subst v.
                    reflexivity.
                  - left.
                    apply (proj1 (Nat.eqb_eq x b)) in Hxb.
                    apply (proj1 (Nat.eqb_eq u 0)) in Hu0.
                    subst x. subst u.
                    reflexivity.
                + exfalso. simpl in H. discriminate H. }
            * exfalso. simpl in H. discriminate H.
          + exfalso. simpl in H. discriminate H.
        - exfalso. simpl in H. discriminate H. }
  Qed.

  (* The main–main tests compute to [true] on the two concrete orientations
     (the [eqb]s on the variable agents [c d] / [a b] do not compute, so the
     equalities are proved by [Nat.eqb_eq] and the disjointness). *)
  Local Lemma mm_cd_true_concrete :
    is_main_main_link c d ((c, 0), (d, 0)) = true
    /\ is_main_main_link c d ((d, 0), (c, 0)) = true.
  Proof.
    split.
    - unfold is_main_main_link. simpl.
      assert (Hcc : Nat.eqb c c = true). { apply (proj2 (Nat.eqb_eq c c)). reflexivity. }
      assert (Hdd : Nat.eqb d d = true). { apply (proj2 (Nat.eqb_eq d d)). reflexivity. }
      assert (Hcd_f : Nat.eqb c d = false).
      { destruct (Nat.eqb c d) eqn:Hb.
        - exfalso. apply (proj1 (Nat.eqb_eq c d)) in Hb.
          change (c <> d /\ has_agent A N c /\ has_agent A N d /\ has_link A N (c, 0) (d, 0)) in Hap_cd.
          apply (proj1 Hap_cd). exact Hb.
        - reflexivity. }
      rewrite Hcc, Hdd, Hcd_f.
      simpl.
      reflexivity.
    - unfold is_main_main_link. simpl.
      assert (Hcc : Nat.eqb c c = true). { apply (proj2 (Nat.eqb_eq c c)). reflexivity. }
      assert (Hdd : Nat.eqb d d = true). { apply (proj2 (Nat.eqb_eq d d)). reflexivity. }
      assert (Hdc_f : Nat.eqb d c = false).
      { destruct (Nat.eqb d c) eqn:Hb.
        - exfalso. apply (proj1 (Nat.eqb_eq d c)) in Hb.
          change (c <> d /\ has_agent A N c /\ has_agent A N d /\ has_link A N (c, 0) (d, 0)) in Hap_cd.
          apply (proj1 Hap_cd). symmetry. exact Hb.
        - reflexivity. }
      rewrite Hcc, Hdd, Hdc_f.
      simpl.
      reflexivity.
  Qed.

  Local Lemma mm_ab_true_concrete :
    is_main_main_link a b ((a, 0), (b, 0)) = true
    /\ is_main_main_link a b ((b, 0), (a, 0)) = true.
  Proof.
    split.
    - unfold is_main_main_link. simpl.
      assert (Haa : Nat.eqb a a = true). { apply (proj2 (Nat.eqb_eq a a)). reflexivity. }
      assert (Hbb : Nat.eqb b b = true). { apply (proj2 (Nat.eqb_eq b b)). reflexivity. }
      assert (Hab_f : Nat.eqb a b = false).
      { destruct (Nat.eqb a b) eqn:Hb.
        - exfalso. apply (proj1 (Nat.eqb_eq a b)) in Hb.
          change (a <> b /\ has_agent A N a /\ has_agent A N b /\ has_link A N (a, 0) (b, 0)) in Hap_ab.
          apply (proj1 Hap_ab). exact Hb.
        - reflexivity. }
      rewrite Haa, Hbb, Hab_f.
      simpl.
      reflexivity.
    - unfold is_main_main_link. simpl.
      assert (Haa : Nat.eqb a a = true). { apply (proj2 (Nat.eqb_eq a a)). reflexivity. }
      assert (Hbb : Nat.eqb b b = true). { apply (proj2 (Nat.eqb_eq b b)). reflexivity. }
      assert (Hba_f : Nat.eqb b a = false).
      { destruct (Nat.eqb b a) eqn:Hb.
        - exfalso. apply (proj1 (Nat.eqb_eq b a)) in Hb.
          change (a <> b /\ has_agent A N a /\ has_agent A N b /\ has_link A N (a, 0) (b, 0)) in Hap_ab.
          apply (proj1 Hap_ab). symmetry. exact Hb.
        - reflexivity. }
      rewrite Haa, Hbb, Hba_f.
      simpl.
      reflexivity.
  Qed.

  (* --- [rw1] preserves the [c d] main–main test --- *)

  (* If [rw1 l] is the [c d] main–main link, so is [l]: each endpoint of [rw1 l]
     is either the original endpoint or a fresh id (> [sc_M]), and [c d] are
     bounded by [sc_M]. *)
  Local Lemma rw1_mm_cd_true (l : port_ref * port_ref) :
    is_main_main_link c d (rw1 l) = true -> is_main_main_link c d l = true.
  Proof.
    intro H.
    destruct l as [[x u] [y v]].
    set (e1 := rewire_endpoint A Ar N a b r1 (x, u)).
    set (e2 := rewire_endpoint A Ar N a b r1 (y, v)).
    change (is_main_main_link c d (e1, e2) = true) in H.
    assert (Hep : link_end (e1, e2) (c, 0) /\ link_end (e1, e2) (d, 0)).
    { exact (mm_cd_endpoints (e1, e2) H). }
    destruct Hep as [Hc0 Hd0].
    destruct Hc0 as [Hcf|Hcs].
    - (* e1 = (c, 0) *)
      assert (Hxf : (x, u) = (c, 0)).
      { exact (rw1_fixes_c0 (x, u) Hcf). }
      destruct Hd0 as [Hdf|Hds].
      + (* e1 = (d, 0) as well: forces [c = d]. *)
        assert (Hxd : (x, u) = (d, 0)).
        { exact (rw1_fixes_d0 (x, u) Hdf). }
        exfalso.
        rewrite Hxf in Hxd.
        injection Hxd as Hcd.
        change (c <> d /\ has_agent A N c /\ has_agent A N d /\ has_link A N (c, 0) (d, 0)) in Hap_cd.
        apply (proj1 Hap_cd).
        exact Hcd.
      + (* e2 = (d, 0): [l] is the [c d] main–main link. *)
        assert (Hys : (y, v) = (d, 0)).
        { exact (rw1_fixes_d0 (y, v) Hds). }
        injection Hxf as Hx Hu.
        subst x. subst u.
        injection Hys as Hy Hv.
        subst y. subst v.
        exact (proj1 mm_cd_true_concrete).
    - (* e2 = (c, 0) *)
      assert (Hys : (y, v) = (c, 0)).
      { exact (rw1_fixes_c0 (y, v) Hcs). }
      destruct Hd0 as [Hdf|Hds].
      + (* e1 = (d, 0): [l] is the [c d] main–main link (swapped). *)
        assert (Hxf : (x, u) = (d, 0)).
        { exact (rw1_fixes_d0 (x, u) Hdf). }
        injection Hxf as Hx Hu.
        subst x. subst u.
        injection Hys as Hy Hv.
        subst y. subst v.
        exact (proj2 mm_cd_true_concrete).
      + (* e2 = (d, 0) as well: forces [c = d]. *)
        assert (Hyd : (y, v) = (d, 0)).
        { exact (rw1_fixes_d0 (y, v) Hds). }
        exfalso.
        rewrite Hys in Hyd.
        injection Hyd as Hcd.
        change (c <> d /\ has_agent A N c /\ has_agent A N d /\ has_link A N (c, 0) (d, 0)) in Hap_cd.
        apply (proj1 Hap_cd).
        exact Hcd.
  Qed.

  (* If [l] is the [c d] main–main link, so is [rw1 l]: [c d] are neither [a]
     nor [b], so [rw1] fixes both endpoints. *)
  Local Lemma rw1_mm_cd_false (l : port_ref * port_ref) :
    is_main_main_link c d l = true -> is_main_main_link c d (rw1 l) = true.
  Proof.
    intro H.
    destruct l as [[x u] [y v]].
    assert (Hep : link_end ((x, u), (y, v)) (c, 0) /\ link_end ((x, u), (y, v)) (d, 0)).
    { exact (mm_cd_endpoints ((x, u), (y, v)) H). }
    destruct Hep as [Hc0 Hd0].
    destruct Hc0 as [Hcf|Hcs].
    - (* (x, u) = (c, 0) *)
      injection Hcf as Hx Hu.
      subst x. subst u.
      destruct Hd0 as [Hdf|Hds].
      + (* (c, 0) = (d, 0): impossible. *)
        exfalso.
        injection Hdf as Hcd.
        change (c <> d /\ has_agent A N c /\ has_agent A N d /\ has_link A N (c, 0) (d, 0)) in Hap_cd.
        apply (proj1 Hap_cd).
        exact Hcd.
      + (* (y, v) = (d, 0): [rw1] fixes both endpoints, so [rw1 l = l]. *)
        injection Hds as Hy Hv.
        subst y. subst v.
        assert (Hrw : rw1 ((c, 0), (d, 0)) = ((c, 0), (d, 0))).
        { unfold rw1, rewire_link.
          f_equal.
          - exact (rewire_endpoint_fixed a b r1 c 0 Hca Hcb).
          - exact (rewire_endpoint_fixed a b r1 d 0 Hda Hdb). }
        exact (eq_trans (f_equal (is_main_main_link c d) Hrw)
                        (proj1 mm_cd_true_concrete)).
    - (* (y, v) = (c, 0) *)
      injection Hcs as Hy Hv.
      subst y. subst v.
      destruct Hd0 as [Hdf|Hds].
      + (* (x, u) = (d, 0): [rw1] fixes both endpoints, so [rw1 l = l]. *)
        injection Hdf as Hx Hu.
        subst x. subst u.
        assert (Hrw : rw1 ((d, 0), (c, 0)) = ((d, 0), (c, 0))).
        { unfold rw1, rewire_link.
          f_equal.
          - exact (rewire_endpoint_fixed a b r1 d 0 Hda Hdb).
          - exact (rewire_endpoint_fixed a b r1 c 0 Hca Hcb). }
        exact (eq_trans (f_equal (is_main_main_link c d) Hrw)
                        (proj2 mm_cd_true_concrete)).
      + (* (c, 0) = (d, 0): impossible. *)
        exfalso.
        injection Hds as Hcd.
        change (c <> d /\ has_agent A N c /\ has_agent A N d /\ has_link A N (c, 0) (d, 0)) in Hap_cd.
        apply (proj1 Hap_cd).
        exact Hcd.
  Qed.

  Local Lemma rw1_pres_mm_cd (l : port_ref * port_ref) :
    is_main_main_link c d (rw1 l) = is_main_main_link c d l.
  Proof.
    destruct (is_main_main_link c d (rw1 l)) eqn:H1.
    - destruct (is_main_main_link c d l) eqn:H2.
      + reflexivity.
      + exfalso.
        apply (rw1_mm_cd_true l) in H1.
        rewrite H1 in H2.
        discriminate H2.
    - destruct (is_main_main_link c d l) eqn:H2.
      + exfalso.
        apply (rw1_mm_cd_false l) in H2.
        rewrite H2 in H1.
        discriminate H1.
      + reflexivity.
  Qed.

  (* The symmetric facts for [rw2'] and the [a b] main–main test. *)

  Local Lemma rw2'_mm_ab_true (l : port_ref * port_ref) :
    is_main_main_link a b (rw2' l) = true -> is_main_main_link a b l = true.
  Proof.
    intro H.
    destruct l as [[x u] [y v]].
    set (e1 := rewire_endpoint A Ar N c d r2 (x, u)).
    set (e2 := rewire_endpoint A Ar N c d r2 (y, v)).
    change (is_main_main_link a b (e1, e2) = true) in H.
    assert (Hep : link_end (e1, e2) (a, 0) /\ link_end (e1, e2) (b, 0)).
    { exact (mm_ab_endpoints (e1, e2) H). }
    destruct Hep as [Ha0 Hb0].
    destruct Ha0 as [Haf|Has].
    - (* e1 = (a, 0) *)
      assert (Hxf : (x, u) = (a, 0)).
      { exact (rw2'_fixes_a0 (x, u) Haf). }
      destruct Hb0 as [Hbf|Hbs].
      + (* e1 = (b, 0) as well: forces [a = b]. *)
        assert (Hxb : (x, u) = (b, 0)).
        { exact (rw2'_fixes_b0 (x, u) Hbf). }
        exfalso.
        rewrite Hxf in Hxb.
        injection Hxb as Hab.
        change (a <> b /\ has_agent A N a /\ has_agent A N b /\ has_link A N (a, 0) (b, 0)) in Hap_ab.
        apply (proj1 Hap_ab).
        exact Hab.
      + (* e2 = (b, 0): [l] is the [a b] main–main link. *)
        assert (Hys : (y, v) = (b, 0)).
        { exact (rw2'_fixes_b0 (y, v) Hbs). }
        injection Hxf as Hx Hu.
        subst x. subst u.
        injection Hys as Hy Hv.
        subst y. subst v.
        exact (proj1 mm_ab_true_concrete).
    - (* e2 = (a, 0) *)
      assert (Hys : (y, v) = (a, 0)).
      { exact (rw2'_fixes_a0 (y, v) Has). }
      destruct Hb0 as [Hbf|Hbs].
      + (* e1 = (b, 0): [l] is the [a b] main–main link (swapped). *)
        assert (Hxf : (x, u) = (b, 0)).
        { exact (rw2'_fixes_b0 (x, u) Hbf). }
        injection Hxf as Hx Hu.
        subst x. subst u.
        injection Hys as Hy Hv.
        subst y. subst v.
        exact (proj2 mm_ab_true_concrete).
      + (* e2 = (b, 0) as well: forces [a = b]. *)
        assert (Hyb : (y, v) = (b, 0)).
        { exact (rw2'_fixes_b0 (y, v) Hbs). }
        exfalso.
        rewrite Hys in Hyb.
        injection Hyb as Hab.
        change (a <> b /\ has_agent A N a /\ has_agent A N b /\ has_link A N (a, 0) (b, 0)) in Hap_ab.
        apply (proj1 Hap_ab).
        exact Hab.
  Qed.

  Local Lemma rw2'_mm_ab_false (l : port_ref * port_ref) :
    is_main_main_link a b l = true -> is_main_main_link a b (rw2' l) = true.
  Proof.
    intro H.
    destruct l as [[x u] [y v]].
    assert (Hep : link_end ((x, u), (y, v)) (a, 0) /\ link_end ((x, u), (y, v)) (b, 0)).
    { exact (mm_ab_endpoints ((x, u), (y, v)) H). }
    destruct Hep as [Ha0 Hb0].
    destruct Ha0 as [Haf|Has].
    - (* (x, u) = (a, 0) *)
      injection Haf as Hx Hu.
      subst x. subst u.
      destruct Hb0 as [Hbf|Hbs].
      + (* (a, 0) = (b, 0): impossible. *)
        exfalso.
        injection Hbf as Hab.
        change (a <> b /\ has_agent A N a /\ has_agent A N b /\ has_link A N (a, 0) (b, 0)) in Hap_ab.
        apply (proj1 Hap_ab).
        exact Hab.
      + (* (y, v) = (b, 0): [rw2'] fixes both endpoints, so [rw2' l = l]. *)
        injection Hbs as Hy Hv.
        subst y. subst v.
        assert (Hrw : rw2' ((a, 0), (b, 0)) = ((a, 0), (b, 0))).
        { unfold rw2', rewire_link.
          f_equal.
          - exact (rewire_endpoint_fixed c d r2 a 0 Hac Had).
          - exact (rewire_endpoint_fixed c d r2 b 0 Hbc Hbd). }
        exact (eq_trans (f_equal (is_main_main_link a b) Hrw)
                        (proj1 mm_ab_true_concrete)).
    - (* (y, v) = (a, 0) *)
      injection Has as Hy Hv.
      subst y. subst v.
      destruct Hb0 as [Hbf|Hbs].
      + (* (x, u) = (b, 0): [rw2'] fixes both endpoints, so [rw2' l = l]. *)
        injection Hbf as Hx Hu.
        subst x. subst u.
        assert (Hrw : rw2' ((b, 0), (a, 0)) = ((b, 0), (a, 0))).
        { unfold rw2', rewire_link.
          f_equal.
          - exact (rewire_endpoint_fixed c d r2 b 0 Hbc Hbd).
          - exact (rewire_endpoint_fixed c d r2 a 0 Hac Had). }
        exact (eq_trans (f_equal (is_main_main_link a b) Hrw)
                        (proj2 mm_ab_true_concrete)).
      + (* (a, 0) = (b, 0): impossible. *)
        exfalso.
        injection Hbs as Hab.
        change (a <> b /\ has_agent A N a /\ has_agent A N b /\ has_link A N (a, 0) (b, 0)) in Hap_ab.
        apply (proj1 Hap_ab).
        exact Hab.
  Qed.

  Local Lemma rw2'_pres_mm_ab (l : port_ref * port_ref) :
    is_main_main_link a b (rw2' l) = is_main_main_link a b l.
  Proof.
    destruct (is_main_main_link a b (rw2' l)) eqn:H1.
    - destruct (is_main_main_link a b l) eqn:H2.
      + reflexivity.
      + exfalso.
        apply (rw2'_mm_ab_true l) in H1.
        rewrite H1 in H2.
        discriminate H2.
    - destruct (is_main_main_link a b l) eqn:H2.
      + exfalso.
        apply (rw2'_mm_ab_false l) in H2.
        rewrite H2 in H1.
        discriminate H1.
      + reflexivity.
  Qed.

  (* ========================================================================== *)
  (* Stage 5 (cont.): fresh-link facts and filter machinery.                    *)
  (* ========================================================================== *)

  (* Pointwise equality on the elements of [l] implies equality of the maps
     (the [port_ref * port_ref] analogue of [map_ptw]). *)
  Local Lemma map_ptw_link
      (f g : port_ref * port_ref -> port_ref * port_ref) (l : list (port_ref * port_ref)) :
    (forall x, In x l -> f x = g x) -> map f l = map g l.
  Proof.
    induction l as [|h t IH]; intros Hpt; simpl.
    - reflexivity.
    - assert (Hh : f h = g h). { exact (Hpt h (in_eq h t)). }
      rewrite Hh.
      assert (Ht : forall x, In x t -> f x = g x).
      { intros x Hx. exact (Hpt x (in_cons h x t Hx)). }
      rewrite (IH Ht). reflexivity.
  Qed.

  (* [rw2] fixes the fresh links of [r1] (relative to [N]): their agent ids are
     fresh ids of [N] (> [sc_M]), hence distinct from [c d]. *)
  Local Lemma rw2_fresh_fixed (x p : nat) :
    rewire_endpoint A Ar sc_N1 c d r2 (fresh_id A N x, p) = (fresh_id A N x, p).
  Proof.
    assert (Hc_le : c <= sc_M). { exact (abcd_le_scM c Hc). }
    assert (Hd_le : d <= sc_M). { exact (abcd_le_scM d Hd). }
    assert (Hgt : fresh_id A N x > sc_M). { exact (fresh_id_gt_scM x). }
    unfold rewire_endpoint.
    destruct (Nat.eqb (fresh_id A N x) c) eqn:H1.
    - exfalso.
      apply (proj1 (Nat.eqb_eq (fresh_id A N x) c)) in H1.
      unfold fresh_id, sc_M in H1, Hgt, Hc_le.
      lia.
    - destruct (Nat.eqb (fresh_id A N x) d) eqn:H2.
      + exfalso.
        apply (proj1 (Nat.eqb_eq (fresh_id A N x) d)) in H2.
        unfold fresh_id, sc_M in H2, Hgt, Hd_le.
        lia.
      + reflexivity.
  Qed.

  (* [rw1'] fixes the fresh links of [r2] (relative to [N]): their agent ids are
     fresh ids of [N] (> [sc_M]), hence distinct from [a b]. *)
  Local Lemma rw1'_fresh_fixed (x p : nat) :
    rewire_endpoint A Ar sc_N2 a b r1 (fresh_id A N x, p) = (fresh_id A N x, p).
  Proof.
    assert (Ha_le : a <= sc_M). { exact (abcd_le_scM a Ha). }
    assert (Hb_le : b <= sc_M). { exact (abcd_le_scM b Hb). }
    assert (Hgt : fresh_id A N x > sc_M). { exact (fresh_id_gt_scM x). }
    unfold rewire_endpoint.
    destruct (Nat.eqb (fresh_id A N x) a) eqn:H1.
    - exfalso.
      apply (proj1 (Nat.eqb_eq (fresh_id A N x) a)) in H1.
      unfold fresh_id, sc_M in H1, Hgt, Ha_le.
      lia.
    - destruct (Nat.eqb (fresh_id A N x) b) eqn:H2.
      + exfalso.
        apply (proj1 (Nat.eqb_eq (fresh_id A N x) b)) in H2.
        unfold fresh_id, sc_M in H2, Hgt, Hb_le.
        lia.
      + reflexivity.
  Qed.

  (* [rw2] is the identity on the fresh links of [r1] (elementwise). *)
  Local Lemma rw2_fixes_fl1_elem (l : port_ref * port_ref) :
    rw2 ((freshen_pr A N (fst l), freshen_pr A N (snd l)))
      = (freshen_pr A N (fst l), freshen_pr A N (snd l)).
  Proof.
    unfold rw2, rewire_link.
    destruct l as [[x u] [y v]].
    simpl.
    f_equal.
    - exact (rw2_fresh_fixed x u).
    - exact (rw2_fresh_fixed y v).
  Qed.

  Local Lemma map_rw2_fl1_gen (L : list (port_ref * port_ref)) :
    map rw2 (map (fun l : port_ref * port_ref =>
             (freshen_pr A N (fst l), freshen_pr A N (snd l))) L)
      = map (fun l : port_ref * port_ref =>
             (freshen_pr A N (fst l), freshen_pr A N (snd l))) L.
  Proof.
    induction L as [|h t IH]; simpl.
    - reflexivity.
    - assert (Hh : rw2 ((freshen_pr A N (fst h), freshen_pr A N (snd h)))
               = (freshen_pr A N (fst h), freshen_pr A N (snd h))).
      { exact (rw2_fixes_fl1_elem h). }
      rewrite Hh.
      rewrite IH.
      reflexivity.
  Qed.

  Local Lemma map_rw2_fl1 : map rw2 fl1 = fl1.
  Proof.
    unfold fl1.
    exact (map_rw2_fl1_gen (nt_links (ru_rhs r1))).
  Qed.

  (* [rw1'] is the identity on the fresh links of [r2] (elementwise). *)
  Local Lemma rw1'_fixes_fl2_elem (l : port_ref * port_ref) :
    rw1' ((freshen_pr A N (fst l), freshen_pr A N (snd l)))
      = (freshen_pr A N (fst l), freshen_pr A N (snd l)).
  Proof.
    unfold rw1', rewire_link.
    destruct l as [[x u] [y v]].
    simpl.
    f_equal.
    - exact (rw1'_fresh_fixed x u).
    - exact (rw1'_fresh_fixed y v).
  Qed.

  Local Lemma map_rw1'_fl2_gen (L : list (port_ref * port_ref)) :
    map rw1' (map (fun l : port_ref * port_ref =>
             (freshen_pr A N (fst l), freshen_pr A N (snd l))) L)
      = map (fun l : port_ref * port_ref =>
             (freshen_pr A N (fst l), freshen_pr A N (snd l))) L.
  Proof.
    induction L as [|h t IH]; simpl.
    - reflexivity.
    - assert (Hh : rw1' ((freshen_pr A N (fst h), freshen_pr A N (snd h)))
               = (freshen_pr A N (fst h), freshen_pr A N (snd h))).
      { exact (rw1'_fixes_fl2_elem h). }
      rewrite Hh.
      rewrite IH.
      reflexivity.
  Qed.

  Local Lemma map_rw1'_fl2 : map rw1' fl2 = fl2.
  Proof.
    unfold fl2.
    exact (map_rw1'_fl2_gen (nt_links (ru_rhs r2))).
  Qed.

  (* A fresh link of [r1] is never the [c d] main–main link: both endpoint agent
     ids are fresh ids of [N] (> [sc_M]), while [c d] are bounded by [sc_M]. *)
  Local Lemma fl1_mm_cd_false (x y p q : nat) :
    is_main_main_link c d ((fresh_id A N x, p), (fresh_id A N y, q)) = false.
  Proof.
    assert (Hc_le : c <= sc_M). { exact (abcd_le_scM c Hc). }
    assert (Hd_le : d <= sc_M). { exact (abcd_le_scM d Hd). }
    assert (Hgt : fresh_id A N x > sc_M). { exact (fresh_id_gt_scM x). }
    unfold is_main_main_link. simpl.
    assert (Hxc : Nat.eqb (fresh_id A N x) c = false).
    { destruct (Nat.eqb (fresh_id A N x) c) eqn:Hb.
      - exfalso. apply (proj1 (Nat.eqb_eq (fresh_id A N x) c)) in Hb.
        unfold fresh_id, sc_M in Hb, Hgt, Hc_le. lia.
      - reflexivity. }
    assert (Hxd : Nat.eqb (fresh_id A N x) d = false).
    { destruct (Nat.eqb (fresh_id A N x) d) eqn:Hb.
      - exfalso. apply (proj1 (Nat.eqb_eq (fresh_id A N x) d)) in Hb.
        unfold fresh_id, sc_M in Hb, Hgt, Hd_le. lia.
      - reflexivity. }
    rewrite Hxc, Hxd.
    simpl.
    reflexivity.
  Qed.

  (* A fresh link of [r2] is never the [a b] main–main link (symmetric). *)
  Local Lemma fl2_mm_ab_false (x y p q : nat) :
    is_main_main_link a b ((fresh_id A N x, p), (fresh_id A N y, q)) = false.
  Proof.
    assert (Ha_le : a <= sc_M). { exact (abcd_le_scM a Ha). }
    assert (Hb_le : b <= sc_M). { exact (abcd_le_scM b Hb). }
    assert (Hgt : fresh_id A N x > sc_M). { exact (fresh_id_gt_scM x). }
    unfold is_main_main_link. simpl.
    assert (Hxa : Nat.eqb (fresh_id A N x) a = false).
    { destruct (Nat.eqb (fresh_id A N x) a) eqn:Hb.
      - exfalso. apply (proj1 (Nat.eqb_eq (fresh_id A N x) a)) in Hb.
        unfold fresh_id, sc_M in Hb, Hgt, Ha_le. lia.
      - reflexivity. }
    assert (Hxb : Nat.eqb (fresh_id A N x) b = false).
    { destruct (Nat.eqb (fresh_id A N x) b) eqn:Hb.
      - exfalso. apply (proj1 (Nat.eqb_eq (fresh_id A N x) b)) in Hb.
        unfold fresh_id, sc_M in Hb, Hgt, Hb_le. lia.
      - reflexivity. }
    rewrite Hxa, Hxb.
    simpl.
    reflexivity.
  Qed.

  (* The [c d] main–main filter keeps all of [fl1] (and the [a b] filter keeps
     all of [fl2]). *)
  Local Lemma filter_fl1_mm_cd :
    filter (fun l : port_ref * port_ref => negb (is_main_main_link c d l)) fl1 = fl1.
  Proof.
    rewrite <- filter_true.
    apply filter_ext_in.
    intros l Hl.
    apply (proj1 (in_map_iff (fun l' : port_ref * port_ref =>
             (freshen_pr A N (fst l'), freshen_pr A N (snd l')))
           (nt_links (ru_rhs r1)) l)) in Hl.
    destruct Hl as [l' [Hleq Hlin]].
    subst l.
    destruct l' as [[x u] [y v]].
    simpl.
    exact (proj2 (negb_true_iff
             (is_main_main_link c d ((fresh_id A N x, u), (fresh_id A N y, v))))
             (fl1_mm_cd_false x y u v)).
  Qed.

  Local Lemma filter_fl2_mm_ab :
    filter (fun l : port_ref * port_ref => negb (is_main_main_link a b l)) fl2 = fl2.
  Proof.
    rewrite <- filter_true.
    apply filter_ext_in.
    intros l Hl.
    apply (proj1 (in_map_iff (fun l' : port_ref * port_ref =>
             (freshen_pr A N (fst l'), freshen_pr A N (snd l')))
           (nt_links (ru_rhs r2)) l)) in Hl.
    destruct Hl as [l' [Hleq Hlin]].
    subst l.
    destruct l' as [[x u] [y v]].
    simpl.
    exact (proj2 (negb_true_iff
             (is_main_main_link a b ((fresh_id A N x, u), (fresh_id A N y, v))))
             (fl2_mm_ab_false x y u v)).
  Qed.

  (* --- Filter machinery --- *)

  (* Filtering twice is filtering with the conjunction (the [port_ref * port_ref]
     analogue of [filter_fusion]). *)
  Local Lemma filter_fusion_link (f g : (port_ref * port_ref) -> bool)
      (l : list (port_ref * port_ref)) :
    filter g (filter f l) = filter (fun x => f x && g x) l.
  Proof.
    induction l as [|h t IH]; simpl.
    - reflexivity.
    - destruct (f h) eqn:Hf.
      + destruct (g h) eqn:Hg.
        * change ((if g h then h :: filter g (filter f t) else filter g (filter f t))
                  = h :: filter (fun x : port_ref * port_ref => f x && g x) t).
          rewrite Hg. rewrite IH. reflexivity.
        * change ((if g h then h :: filter g (filter f t) else filter g (filter f t))
                  = filter (fun x : port_ref * port_ref => f x && g x) t).
          rewrite Hg. rewrite IH. reflexivity.
      + change (filter g (filter f t)
                = filter (fun x : port_ref * port_ref => f x && g x) t).
        rewrite IH. reflexivity.
  Qed.

  (* [rw1] commutes with the [c d] main–main filter: [rw1] preserves the test
     ([rw1_pres_mm_cd]), so a link survives the filter after [rw1] iff it did
     before. *)
  Local Lemma filter_map_rw1 (L : list (port_ref * port_ref)) :
    filter (fun l : port_ref * port_ref => negb (is_main_main_link c d l)) (map rw1 L)
      = map rw1 (filter (fun l : port_ref * port_ref => negb (is_main_main_link c d l)) L).
  Proof.
    set (P := fun l : port_ref * port_ref => negb (is_main_main_link c d l)).
    induction L as [|h t IH]; simpl.
    - reflexivity.
    - change ((if P (rw1 h) then rw1 h :: filter P (map rw1 t) else filter P (map rw1 t))
              = map rw1 (if P h then h :: filter P t else filter P t)).
      assert (HP : P (rw1 h) = P h).
      { unfold P. exact (f_equal negb (rw1_pres_mm_cd h)). }
      rewrite HP.
      destruct (P h) eqn:HpH.
      + simpl. rewrite IH. reflexivity.
      + simpl. rewrite IH. reflexivity.
  Qed.

  (* [rw2'] commutes with the [a b] main–main filter (symmetric). *)
  Local Lemma filter_map_rw2' (L : list (port_ref * port_ref)) :
    filter (fun l : port_ref * port_ref => negb (is_main_main_link a b l)) (map rw2' L)
      = map rw2' (filter (fun l : port_ref * port_ref => negb (is_main_main_link a b l)) L).
  Proof.
    set (P := fun l : port_ref * port_ref => negb (is_main_main_link a b l)).
    induction L as [|h t IH]; simpl.
    - reflexivity.
    - change ((if P (rw2' h) then rw2' h :: filter P (map rw2' t) else filter P (map rw2' t))
              = map rw2' (if P h then h :: filter P t else filter P t)).
      assert (HP : P (rw2' h) = P h).
      { unfold P. exact (f_equal negb (rw2'_pres_mm_ab h)). }
      rewrite HP.
      destruct (P h) eqn:HpH.
      + simpl. rewrite IH. reflexivity.
      + simpl. rewrite IH. reflexivity.
  Qed.

  (* [filter P (filter Q l)] commutes (the [port_ref * port_ref] analogue of
     [filter_comm]). *)
  Local Lemma filter_comm_link (P Q : (port_ref * port_ref) -> bool)
      (l : list (port_ref * port_ref)) :
    filter P (filter Q l) = filter Q (filter P l).
  Proof.
    rewrite (filter_fusion_link P Q l), (filter_fusion_link Q P l).
    apply (filter_ext_in (fun x => Q x && P x) (fun x => P x && Q x) l).
    intros x Hx.
    change ((Q x && P x) = (P x && Q x)).
    destruct (P x) eqn:Hp; destruct (Q x) eqn:Hq; simpl; reflexivity.
  Qed.

  (* --- Link block decompositions --- *)

  (* The links of [sc_N1]: the rewired kept links of [N] (minus the [a b]
     main–main link), followed by the fresh links of the [r1] RHS. *)
  Local Lemma sc_links_N1 :
    nt_links sc_N1
      = map rw1 (filter (fun l : port_ref * port_ref => negb (is_main_main_link a b l)) (nt_links N))
        ++ fl1.
  Proof.
    change (map rw1 (filter (fun l : port_ref * port_ref => negb (is_main_main_link a b l)) (nt_links N))
           ++ fl1
           = map rw1 (filter (fun l : port_ref * port_ref => negb (is_main_main_link a b l)) (nt_links N))
             ++ fl1).
    reflexivity.
  Qed.

  (* Symmetric for [sc_N2]. *)
  Local Lemma sc_links_N2 :
    nt_links sc_N2
      = map rw2' (filter (fun l : port_ref * port_ref => negb (is_main_main_link c d l)) (nt_links N))
        ++ fl2.
  Proof.
    change (map rw2' (filter (fun l : port_ref * port_ref => negb (is_main_main_link c d l)) (nt_links N))
           ++ fl2
           = map rw2' (filter (fun l : port_ref * port_ref => negb (is_main_main_link c d l)) (nt_links N))
             ++ fl2).
    reflexivity.
  Qed.

  (* The links of [sc_N12] (= splice [r2] over [sc_N1]): the kept links of [N]
     rewired by [rw1] then [rw2], followed by the [r1] fresh links (untouched
     by [rw2]) and the [r2] fresh links (freshened relative to [sc_N1]). *)
  Local Lemma sc_links_N12 :
    nt_links sc_N12
      = map (fun l : port_ref * port_ref => rw2 (rw1 l)) Lk ++ fl1 ++ fl2p.
  Proof.
    change (map rw2 (filter (fun l : port_ref * port_ref => negb (is_main_main_link c d l)) (nt_links sc_N1))
           ++ fl2p
           = map (fun l : port_ref * port_ref => rw2 (rw1 l)) Lk ++ fl1 ++ fl2p).
    rewrite sc_links_N1.
    rewrite filter_app.
    rewrite filter_fl1_mm_cd.
    rewrite filter_map_rw1.
    rewrite filter_fusion_link.
    unfold Lk.
    rewrite map_app.
    rewrite map_map.
    rewrite map_rw2_fl1.
    rewrite <- app_assoc.
    reflexivity.
  Qed.

  (* Symmetric for [sc_N21] (= splice [r1] over [sc_N2]). *)
  Local Lemma sc_links_N21 :
    nt_links sc_N21
      = map (fun l : port_ref * port_ref => rw1' (rw2' l)) Lk ++ fl2 ++ fl1p.
  Proof.
    change (map rw1' (filter (fun l : port_ref * port_ref => negb (is_main_main_link a b l)) (nt_links sc_N2))
           ++ fl1p
           = map (fun l : port_ref * port_ref => rw1' (rw2' l)) Lk ++ fl2 ++ fl1p).
    rewrite sc_links_N2.
    rewrite filter_app.
    rewrite filter_fl2_mm_ab.
    rewrite filter_map_rw2'.
    rewrite filter_comm_link.
    rewrite filter_fusion_link.
    unfold Lk.
    rewrite map_app.
    rewrite map_map.
    rewrite map_rw1'_fl2.
    rewrite <- app_assoc.
    reflexivity.
  Qed.

  (* --- Fresh-block map equalities --- *)

  (* A fresh id of [N] (relative to the [r1] RHS) is mapped by [comm_map] to
     the corresponding fresh id of [sc_N2] (relative to the [r1] RHS). *)
  Local Lemma cm_fresh1 (x : nat) (Hx : In x (map fst (nt_agents (ru_rhs r1)))) :
    comm_map sc_M sc_M1 sc_M2 (fresh_id A N x) = fresh_id A sc_N2 x.
  Proof.
    apply (proj1 (in_map_iff fst (nt_agents (ru_rhs r1)) x)) in Hx.
    destruct Hx as [q [Hqx Hqin]].
    subst x.
    assert (Hle : fresh_id A N (fst q) <= sc_M1). { exact (sc_M1_ge_fresh1 q Hqin). }
    assert (Hgt : sc_M < fresh_id A N (fst q)). { exact (fresh_id_gt_scM (fst q)). }
    assert (Hcm : comm_map sc_M sc_M1 sc_M2 (fresh_id A N (fst q))
               = shift sc_M2 sc_M (fresh_id A N (fst q))).
    { apply cm_r1. exact Hgt. exact Hle. }
    rewrite Hcm.
    unfold fresh_id, sc_M, sc_M2.
    assert (Harg : max_agent_id A N + 1 + fst q = fst q + max_agent_id A N + 1). { lia. }
    rewrite Harg.
    change (shift sc_M2 sc_M (fst q + sc_M + 1) = max_agent_id A sc_N2 + 1 + fst q).
    rewrite (shift_r1 (fst q)).
    unfold sc_M2.
    lia.
  Qed.

  (* [cm_pair_link] sends the [r1] fresh links (freshened rel. [N]) to the
     [r1] fresh links freshened rel. [sc_N2] (= [fl1p]). *)
  Local Lemma map_cm_fl1 : map cm_pair_link fl1 = fl1p.
  Proof.
    unfold fl1, fl1p.
    rewrite map_map.
    apply map_ptw_link.
    intros l Hl.
    destruct l as [[x u] [y v]].
    assert (Hx : In x (map fst (nt_agents (ru_rhs r1)))).
    { apply (proj1 (has_agent_In A (ru_rhs r1) x)).
      exact (proj1 (wf_links Hr1 x y u v Hl)). }
    assert (Hy : In y (map fst (nt_agents (ru_rhs r1)))).
    { apply (proj1 (has_agent_In A (ru_rhs r1) y)).
      exact (proj1 (proj2 (wf_links Hr1 x y u v Hl))). }
    assert (Hcx : cm_pair_link ((fresh_id A N x, u), (fresh_id A N y, v))
             = ((fresh_id A sc_N2 x, u), (fresh_id A sc_N2 y, v))).
    { unfold cm_pair_link.
      simpl.
      assert (H1 : comm_map sc_M sc_M1 sc_M2 (fresh_id A N x) = fresh_id A sc_N2 x).
      { apply cm_fresh1. exact Hx. }
      assert (H2 : comm_map sc_M sc_M1 sc_M2 (fresh_id A N y) = fresh_id A sc_N2 y).
      { apply cm_fresh1. exact Hy. }
      rewrite H1, H2.
      reflexivity. }
    exact Hcx.
  Qed.

  (* A fresh id of [sc_N1] is strictly above [sc_M1]. *)
  Local Lemma fresh_id_scN1_gt_scM1 (x : nat) : fresh_id A sc_N1 x > sc_M1.
  Proof.
    unfold fresh_id, sc_M1, max_agent_id. lia.
  Qed.

  (* A fresh id of [sc_N1] (relative to the [r2] RHS) is mapped by [comm_map]
     to the corresponding fresh id of [N] (relative to the [r2] RHS). No
     premise is needed: such ids are above [sc_M1] by construction. *)
  Local Lemma cm_fresh2p (x : nat) :
    comm_map sc_M sc_M1 sc_M2 (fresh_id A sc_N1 x) = fresh_id A N x.
  Proof.
    assert (Hgt : fresh_id A sc_N1 x > sc_M1). { exact (fresh_id_scN1_gt_scM1 x). }
    assert (Hcm : comm_map sc_M sc_M1 sc_M2 (fresh_id A sc_N1 x)
               = shift sc_M sc_M1 (fresh_id A sc_N1 x)).
    { apply cm_r2. exact Hgt. }
    rewrite Hcm.
    unfold fresh_id, sc_M, sc_M1.
    assert (Harg : max_agent_id A sc_N1 + 1 + x = x + max_agent_id A sc_N1 + 1). { lia. }
    rewrite Harg.
    change (shift sc_M sc_M1 (x + sc_M1 + 1) = max_agent_id A N + 1 + x).
    rewrite (shift_r2 x).
    unfold sc_M.
    lia.
  Qed.

  (* [cm_pair_link] sends the [r2] fresh links (freshened rel. [sc_N1]) back
     to the [r2] fresh links freshened rel. [N] (= [fl2]). *)
  Local Lemma map_cm_fl2p : map cm_pair_link fl2p = fl2.
  Proof.
    unfold fl2p, fl2.
    rewrite map_map.
    apply map_ptw_link.
    intros l Hl.
    destruct l as [[x u] [y v]].
    assert (Hcx : cm_pair_link ((fresh_id A sc_N1 x, u), (fresh_id A sc_N1 y, v))
             = ((fresh_id A N x, u), (fresh_id A N y, v))).
    { unfold cm_pair_link.
      simpl.
      assert (H1 : comm_map sc_M sc_M1 sc_M2 (fresh_id A sc_N1 x) = fresh_id A N x).
      { exact (cm_fresh2p x). }
      assert (H2 : comm_map sc_M sc_M1 sc_M2 (fresh_id A sc_N1 y) = fresh_id A N y).
      { exact (cm_fresh2p y). }
      rewrite H1, H2.
      reflexivity. }
    exact Hcx.
  Qed.

  (* --- The crux: renaming commutes with the two rewirings on kept links --- *)

  (* Endpoint-level versions of the four rewire maps. *)
  Local Definition rw1e  (e : port_ref) : port_ref := rewire_endpoint A Ar N a b r1 e.
  Local Definition rw2e  (e : port_ref) : port_ref := rewire_endpoint A Ar sc_N1 c d r2 e.
  Local Definition rw1'e (e : port_ref) : port_ref := rewire_endpoint A Ar sc_N2 a b r1 e.
  Local Definition rw2'e (e : port_ref) : port_ref := rewire_endpoint A Ar N c d r2 e.

  (* [rewire_endpoint] is the identity off its two agents, for any net. *)
  Local Lemma rewire_endpoint_fixed_net (M : Net A) (a1 a2 : nat) (r : Rule A) (x : nat) (p : nat)
        (Hx1 : x <> a1) (Hx2 : x <> a2) :
    rewire_endpoint A Ar M a1 a2 r (x, p) = (x, p).
  Proof.
    unfold rewire_endpoint.
    destruct (Nat.eqb x a1) eqn:H1.
    - exfalso. apply (proj1 (Nat.eqb_eq x a1)) in H1. apply Hx1. exact H1.
    - destruct (Nat.eqb x a2) eqn:H2.
      + exfalso. apply (proj1 (Nat.eqb_eq x a2)) in H2. apply Hx2. exact H2.
      + reflexivity.
  Qed.

  (* The agent of an endpoint of a link of [N] is an agent of [N]. *)
  Local Lemma kept_ep_agent (l : port_ref * port_ref) (Hln : In l (nt_links N)) (e : port_ref)
        (He : link_end l e) :
    has_agent A N (fst e).
  Proof.
    destruct l as [[lx lu] [ly lv]].
    destruct e as [x p].
    destruct He as [He1 | He2].
    - injection He1 as Hlx Hlu. subst lx. subst lu.
      exact (proj1 (wf_links Hwf x ly p lv Hln)).
    - injection He2 as Hly Hlv. subst ly. subst lv.
      exact (proj1 (proj2 (wf_links Hwf lx x lu p Hln))).
  Qed.

  (* The port of an endpoint of a link of [N] is bounded by the arity of the
     label of its agent. *)
  Local Lemma kept_ep_port (l : port_ref * port_ref) (Hln : In l (nt_links N)) (e : port_ref)
        (He : link_end l e) (la : A) (Hla : agent_label A N (fst e) = Some la) :
    snd e <= Ar la.
  Proof.
    destruct l as [[lx lu] [ly lv]].
    destruct e as [x p].
    destruct He as [He1 | He2].
    - injection He1 as Hlx Hlu. subst lx. subst lu.
      destruct (wf_links Hwf x ly p lv Hln) as [_ Hrest].
      destruct Hrest as [Hly Hw].
      destruct (agent_label A N ly) as [lb |] eqn:Hlbl.
      + exact (proj1 (Hw la lb Hla (eq_refl (Some lb)))).
      + exfalso. apply Hly. exact Hlbl.
    - injection He2 as Hly Hlv. subst ly. subst lv.
      destruct (wf_links Hwf lx x lu p Hln) as [Hlx Hrest].
      destruct Hrest as [_ Hw].
      destruct (agent_label A N lx) as [lb |] eqn:Hlbl.
      + exact (proj2 (Hw lb la (eq_refl (Some lb)) Hla)).
      + exfalso. apply Hlx. exact Hlbl.
  Qed.

  (* An agent of [N] other than [a b] survives in [sc_N1], hence is bounded
     by [sc_M1]. *)
  Local Lemma surv_scN1 (x : nat) (Hx : has_agent A N x) (Hxa : x <> a) (Hxb : x <> b) :
    x <= sc_M1.
  Proof.
    apply (proj1 (has_agent_In A N x)) in Hx.
    apply (proj1 (in_map_iff fst (nt_agents N) x)) in Hx.
    destruct Hx as [q [Hqx Hqin]].
    subst x.
    assert (Hqf : In q (filter (fun p : nat * A => negb (Nat.eqb (fst p) a) && negb (Nat.eqb (fst p) b)) (nt_agents N))).
    { apply (proj2 (filter_In (fun p : nat * A => negb (Nat.eqb (fst p) a) && negb (Nat.eqb (fst p) b)) q (nt_agents N))).
      split.
      - exact Hqin.
      - assert (Hna : negb (Nat.eqb (fst q) a) = true).
        { destruct (Nat.eqb (fst q) a) eqn:Hb.
          + exfalso. apply (proj1 (Nat.eqb_eq (fst q) a)) in Hb. apply Hxa. exact Hb.
          + reflexivity. }
        assert (Hnb : negb (Nat.eqb (fst q) b) = true).
        { destruct (Nat.eqb (fst q) b) eqn:Hb.
          + exfalso. apply (proj1 (Nat.eqb_eq (fst q) b)) in Hb. apply Hxb. exact Hb.
          + reflexivity. }
        rewrite Hna, Hnb.
        simpl.
        reflexivity. }
    assert (HxN1 : In (fst q) (map fst (nt_agents sc_N1))).
    { change (In (fst q) (map fst (filter (fun p : nat * A => negb (Nat.eqb (fst p) a) && negb (Nat.eqb (fst p) b)) (nt_agents N)
                                     ++ map (fun p : nat * A => (fresh_id A N (fst p), snd p)) (nt_agents (ru_rhs r1))))).
      rewrite map_app.
      apply in_or_app. left.
      apply (proj2 (in_map_iff fst (filter (fun p : nat * A => negb (Nat.eqb (fst p) a) && negb (Nat.eqb (fst p) b)) (nt_agents N)) (fst q))).
      exists q.
      split.
      - reflexivity.
      - exact Hqf. }
    specialize (list_max_upper_bound (map fst (nt_agents sc_N1)) (fst q) HxN1) as Hle.
    unfold sc_M1, max_agent_id in Hle.
    exact Hle.
  Qed.

  (* The crux, endpoint form: for a kept link [l] and one of its endpoints
     [e], renaming the agent of [rw2 (rw1 e)] yields the agent of
     [rw1' (rw2' e)], with the port unchanged on both sides. *)
  Local Lemma crux_ep (l : port_ref * port_ref) (Hl : In l Lk) (e : port_ref) (He : link_end l e) :
    (comm_map sc_M sc_M1 sc_M2 (fst (rw2e (rw1e e))), snd (rw2e (rw1e e))) = rw1'e (rw2'e e).
  Proof.
    destruct e as [x p].
    (* Kept-link facts: [l] is a link of [N], not either fired main--main link. *)
    apply (proj1 (filter_In (fun k : port_ref * port_ref =>
           negb (is_main_main_link a b k) && negb (is_main_main_link c d k)) l (nt_links N))) in Hl.
    destruct Hl as [Hln HPl].
    apply (proj1 (andb_true_iff (negb (is_main_main_link a b l)) (negb (is_main_main_link c d l)))) in HPl.
    destruct HPl as [Hmab Hmcd].
    apply (proj1 (negb_true_iff (is_main_main_link a b l))) in Hmab.
    apply (proj1 (negb_true_iff (is_main_main_link c d l))) in Hmcd.
    (* Case split on the agent of the endpoint. *)
    destruct (Nat.eqb x a) eqn:Hxa.
    - (* x = a *)
      apply (proj1 (Nat.eqb_eq x a)) in Hxa.
      subst x.
      destruct (Nat.eqb p 0) eqn:Hpz.
      + (* p = 0: [l] touches (a, 0), hence [l] is the [a b] main--main link. *)
        exfalso.
        apply (proj1 (Nat.eqb_eq p 0)) in Hpz.
        subst p.
        destruct l as [[lx lu] [ly lv]].
        destruct He as [He1 | He2].
        * injection He1 as Hlx Hlu. subst lx. subst lu.
          assert (Hhl : has_link A N (a, 0) (ly, lv)).
          { left. exact Hln. }
          assert (Heq : (b, 0) = (ly, lv)).
          { exact (link_unique A Ar N Hwf (a, 0) (b, 0) (ly, lv) Hlink_ab Hhl). }
          injection Heq as Hly Hlv. subst ly. subst lv.
          simpl in Hmab.
          assert (Haa : Nat.eqb a a = true). { apply (proj2 (Nat.eqb_eq a a)). reflexivity. }
          assert (Hbb : Nat.eqb b b = true). { apply (proj2 (Nat.eqb_eq b b)). reflexivity. }
          assert (Hab_f : Nat.eqb a b = false).
          { destruct (Nat.eqb a b) eqn:Hb.
            - exfalso. apply (proj1 (Nat.eqb_eq a b)) in Hb. apply Hab. exact Hb.
            - reflexivity. }
          assert (Hba_f : Nat.eqb b a = false).
          { destruct (Nat.eqb b a) eqn:Hb.
            - exfalso. apply (proj1 (Nat.eqb_eq b a)) in Hb. apply Hba. exact Hb.
            - reflexivity. }
          rewrite Haa, Hbb, Hab_f, Hba_f in Hmab.
          simpl in Hmab.
          discriminate Hmab.
        * injection He2 as Hly Hlv. subst ly. subst lv.
          assert (Hhl : has_link A N (a, 0) (lx, lu)).
          { right. exact Hln. }
          assert (Heq : (b, 0) = (lx, lu)).
          { exact (link_unique A Ar N Hwf (a, 0) (b, 0) (lx, lu) Hlink_ab Hhl). }
          injection Heq as Hlx Hlu. subst lx. subst lu.
          simpl in Hmab.
          assert (Haa : Nat.eqb a a = true). { apply (proj2 (Nat.eqb_eq a a)). reflexivity. }
          assert (Hbb : Nat.eqb b b = true). { apply (proj2 (Nat.eqb_eq b b)). reflexivity. }
          assert (Hab_f : Nat.eqb a b = false).
          { destruct (Nat.eqb a b) eqn:Hb.
            - exfalso. apply (proj1 (Nat.eqb_eq a b)) in Hb. apply Hab. exact Hb.
            - reflexivity. }
          assert (Hba_f : Nat.eqb b a = false).
          { destruct (Nat.eqb b a) eqn:Hb.
            - exfalso. apply (proj1 (Nat.eqb_eq b a)) in Hb. apply Hba. exact Hb.
            - reflexivity. }
          rewrite Haa, Hbb, Hab_f, Hba_f in Hmab.
          simpl in Hmab.
          discriminate Hmab.
      + (* 1 <= p *)
        assert (Hnz : p <> 0).
        { intro Heq. rewrite Heq in Hpz. simpl in Hpz. discriminate Hpz. }
        assert (H1 : (1 <=? p) = true).
        { apply (proj2 (Nat.leb_le 1 p)). lia. }
        destruct (Nat.leb p (Ar (fst (ru_lhs r1)))) eqn:H2.
        * (* 1 <= p <= Ar (fst (ru_lhs r1)): in range. *)
          set (ipr := nth (p - 1) (ru_iface r1) (0, 0)).
          set (ia := fst ipr).
          set (ipp := snd ipr).
          assert (Hr1e : rw1e (a, p) = (fresh_id A N ia, ipp)).
          { unfold rw1e, rewire_endpoint.
            assert (Heqa : Nat.eqb a a = true).
            { apply (proj2 (Nat.eqb_eq a a)). reflexivity. }
            rewrite Heqa, H1, H2.
            simpl.
            unfold freshen_pr.
            reflexivity. }
          assert (Hr2e : rw2e (fresh_id A N ia, ipp) = (fresh_id A N ia, ipp)).
          { unfold rw2e.
            apply rewire_endpoint_fixed_net.
            - intro Heq.
              assert (HcM : c <= sc_M). { exact (abcd_le_scM c Hc). }
              rewrite <- Heq in HcM.
              assert (Hgt : fresh_id A N ia > sc_M). { exact (fresh_id_gt_scM ia). }
              lia.
            - intro Heq.
              assert (HdM : d <= sc_M). { exact (abcd_le_scM d Hd). }
              rewrite <- Heq in HdM.
              assert (Hgt : fresh_id A N ia > sc_M). { exact (fresh_id_gt_scM ia). }
              lia. }
          assert (Hr2'e : rw2'e (a, p) = (a, p)).
          { unfold rw2'e.
            apply rewire_endpoint_fixed.
            - exact Hac.
            - exact Had. }
          assert (Hr1'e : rw1'e (a, p) = (fresh_id A sc_N2 ia, ipp)).
          { unfold rw1'e, rewire_endpoint.
            assert (Heqa : Nat.eqb a a = true).
            { apply (proj2 (Nat.eqb_eq a a)). reflexivity. }
            rewrite Heqa, H1, H2.
            simpl.
            unfold freshen_pr.
            reflexivity. }
          assert (Hia : In ia (map fst (nt_agents (ru_rhs r1)))).
          { assert (Hlen : p - 1 < length (ru_iface r1)).
            { apply (proj1 (Nat.leb_le 1 p)) in H1.
              apply (proj1 (Nat.leb_le p (Ar (fst (ru_lhs r1))))) in H2.
              lia. }
            assert (Hin : In ipr (ru_iface r1)).
            { apply nth_In. exact Hlen. }
            rewrite Hi1 in Hin.
            assert (Hfree : is_free A Ar (ru_rhs r1) ipr).
            { apply interface_free. exact Hr1. exact Hin. }
            destruct Hfree as [la [Hal _]].
            apply (proj2 (in_map_iff fst (nt_agents (ru_rhs r1)) (fst ipr))).
            exists (fst ipr, la).
            split.
            - reflexivity.
            - exact (agent_label_Some_In A (ru_rhs r1) (fst ipr) la Hal). }
          assert (Hcm : comm_map sc_M sc_M1 sc_M2 (fresh_id A N ia) = fresh_id A sc_N2 ia).
          { apply cm_fresh1. exact Hia. }
          rewrite Hr1e.
          rewrite Hr2e.
          rewrite Hr2'e.
          rewrite Hr1'e.
          exact (f_equal (fun q : nat => (q, ipp)) Hcm).
        * (* p > Ar (fst (ru_lhs r1)): contradicts the well-formedness bound. *)
          exfalso.
          assert (Hnot : ~ (p <= Ar (fst (ru_lhs r1)))).
          { intro Hle.
            assert (Ht : (p <=? Ar (fst (ru_lhs r1))) = true).
            { apply (proj2 (Nat.leb_le p (Ar (fst (ru_lhs r1))))). exact Hle. }
            assert (Hcontra : false = true).
            { exact (eq_trans (eq_sym H2) Ht). }
            discriminate Hcontra. }
          assert (Hle : p <= Ar (fst (ru_lhs r1))).
          { exact (kept_ep_port l Hln (a, p) He (fst (ru_lhs r1)) Hol1). }
          apply Hnot. exact Hle.
    - (* x <> a *)
      destruct (Nat.eqb x b) eqn:Hxb.
      + (* x = b *)
        apply (proj1 (Nat.eqb_eq x b)) in Hxb.
        subst x.
        destruct (Nat.eqb p 0) eqn:Hpz.
        * (* p = 0: [l] touches (b, 0), hence [l] is the [a b] main--main link. *)
          exfalso.
          apply (proj1 (Nat.eqb_eq p 0)) in Hpz.
          subst p.
          destruct l as [[lx lu] [ly lv]].
          destruct He as [He1 | He2].
          { injection He1 as Hlx Hlu. subst lx. subst lu.
            assert (Hhl : has_link A N (b, 0) (ly, lv)).
            { left. exact Hln. }
            assert (Hhl0 : has_link A N (b, 0) (a, 0)).
            { exact (proj1 (has_link_sym A N (a, 0) (b, 0)) Hlink_ab). }
            assert (Heq : (a, 0) = (ly, lv)).
            { exact (link_unique A Ar N Hwf (b, 0) (a, 0) (ly, lv) Hhl0 Hhl). }
            injection Heq as Hly Hlv. subst ly. subst lv.
            simpl in Hmab.
            assert (Haa : Nat.eqb a a = true). { apply (proj2 (Nat.eqb_eq a a)). reflexivity. }
            assert (Hbb : Nat.eqb b b = true). { apply (proj2 (Nat.eqb_eq b b)). reflexivity. }
            assert (Hab_f : Nat.eqb a b = false).
            { destruct (Nat.eqb a b) eqn:Hb.
              - exfalso. apply (proj1 (Nat.eqb_eq a b)) in Hb. apply Hab. exact Hb.
              - reflexivity. }
            assert (Hba_f : Nat.eqb b a = false).
            { destruct (Nat.eqb b a) eqn:Hb.
              - exfalso. apply (proj1 (Nat.eqb_eq b a)) in Hb. apply Hba. exact Hb.
              - reflexivity. }
            rewrite Haa, Hbb, Hab_f, Hba_f in Hmab.
            simpl in Hmab.
            discriminate Hmab. }
          { injection He2 as Hly Hlv. subst ly. subst lv.
            assert (Hhl : has_link A N (b, 0) (lx, lu)).
            { right. exact Hln. }
            assert (Hhl0 : has_link A N (b, 0) (a, 0)).
            { exact (proj1 (has_link_sym A N (a, 0) (b, 0)) Hlink_ab). }
            assert (Heq : (a, 0) = (lx, lu)).
            { exact (link_unique A Ar N Hwf (b, 0) (a, 0) (lx, lu) Hhl0 Hhl). }
            injection Heq as Hlx Hlu. subst lx. subst lu.
            simpl in Hmab.
            assert (Haa : Nat.eqb a a = true). { apply (proj2 (Nat.eqb_eq a a)). reflexivity. }
            assert (Hbb : Nat.eqb b b = true). { apply (proj2 (Nat.eqb_eq b b)). reflexivity. }
            assert (Hab_f : Nat.eqb a b = false).
            { destruct (Nat.eqb a b) eqn:Hb.
              - exfalso. apply (proj1 (Nat.eqb_eq a b)) in Hb. apply Hab. exact Hb.
              - reflexivity. }
            assert (Hba_f : Nat.eqb b a = false).
            { destruct (Nat.eqb b a) eqn:Hb.
              - exfalso. apply (proj1 (Nat.eqb_eq b a)) in Hb. apply Hba. exact Hb.
              - reflexivity. }
            rewrite Haa, Hbb, Hab_f, Hba_f in Hmab.
            simpl in Hmab.
            discriminate Hmab. }
        * (* 1 <= p *)
          assert (Hnz : p <> 0).
          { intro Heq. rewrite Heq in Hpz. simpl in Hpz. discriminate Hpz. }
          assert (H1 : (1 <=? p) = true).
          { apply (proj2 (Nat.leb_le 1 p)). lia. }
          destruct (Nat.leb p (Ar (snd (ru_lhs r1)))) eqn:H2.
          { (* 1 <= p <= Ar (snd (ru_lhs r1)): in range. *)
            set (ipr := nth (Ar (fst (ru_lhs r1)) + (p - 1)) (ru_iface r1) (0, 0)).
            set (ib := fst ipr).
            set (ipp := snd ipr).
            assert (Hr1e : rw1e (b, p) = (fresh_id A N ib, ipp)).
            { unfold rw1e, rewire_endpoint.
              assert (Heqb : Nat.eqb b b = true).
              { apply (proj2 (Nat.eqb_eq b b)). reflexivity. }
              assert (Heqba : Nat.eqb b a = false).
              { destruct (Nat.eqb b a) eqn:Hb.
                + exfalso. apply (proj1 (Nat.eqb_eq b a)) in Hb. apply Hba. exact Hb.
                + reflexivity. }
              rewrite Heqb, Heqba, H1, H2.
              simpl.
              unfold freshen_pr.
              reflexivity. }
            assert (Hr2e : rw2e (fresh_id A N ib, ipp) = (fresh_id A N ib, ipp)).
            { unfold rw2e.
              apply rewire_endpoint_fixed_net.
              - intro Heq.
                assert (HcM : c <= sc_M). { exact (abcd_le_scM c Hc). }
                rewrite <- Heq in HcM.
                assert (Hgt : fresh_id A N ib > sc_M). { exact (fresh_id_gt_scM ib). }
                lia.
              - intro Heq.
                assert (HdM : d <= sc_M). { exact (abcd_le_scM d Hd). }
                rewrite <- Heq in HdM.
                assert (Hgt : fresh_id A N ib > sc_M). { exact (fresh_id_gt_scM ib). }
                lia. }
            assert (Hr2'e : rw2'e (b, p) = (b, p)).
            { unfold rw2'e.
              apply rewire_endpoint_fixed.
              - exact Hbc.
              - exact Hbd. }
            assert (Hr1'e : rw1'e (b, p) = (fresh_id A sc_N2 ib, ipp)).
            { unfold rw1'e, rewire_endpoint.
              assert (Heqb : Nat.eqb b b = true).
              { apply (proj2 (Nat.eqb_eq b b)). reflexivity. }
              assert (Heqba : Nat.eqb b a = false).
              { destruct (Nat.eqb b a) eqn:Hb.
                + exfalso. apply (proj1 (Nat.eqb_eq b a)) in Hb. apply Hba. exact Hb.
                + reflexivity. }
              rewrite Heqb, Heqba, H1, H2.
              simpl.
              unfold freshen_pr.
              reflexivity. }
            assert (Hib : In ib (map fst (nt_agents (ru_rhs r1)))).
            { assert (Hlen : Ar (fst (ru_lhs r1)) + (p - 1) < length (ru_iface r1)).
              { apply (proj1 (Nat.leb_le 1 p)) in H1.
                apply (proj1 (Nat.leb_le p (Ar (snd (ru_lhs r1))))) in H2.
                lia. }
              assert (Hin : In ipr (ru_iface r1)).
              { apply nth_In. exact Hlen. }
              rewrite Hi1 in Hin.
              assert (Hfree : is_free A Ar (ru_rhs r1) ipr).
              { apply interface_free. exact Hr1. exact Hin. }
              destruct Hfree as [la [Hal _]].
              apply (proj2 (in_map_iff fst (nt_agents (ru_rhs r1)) (fst ipr))).
              exists (fst ipr, la).
              split.
              - reflexivity.
              - exact (agent_label_Some_In A (ru_rhs r1) (fst ipr) la Hal). }
            assert (Hcm : comm_map sc_M sc_M1 sc_M2 (fresh_id A N ib) = fresh_id A sc_N2 ib).
            { apply cm_fresh1. exact Hib. }
            rewrite Hr1e.
            rewrite Hr2e.
            rewrite Hr2'e.
            rewrite Hr1'e.
            exact (f_equal (fun q : nat => (q, ipp)) Hcm). }
          { (* p > Ar (snd (ru_lhs r1)): contradicts the well-formedness bound. *)
            exfalso.
            assert (Hnot : ~ (p <= Ar (snd (ru_lhs r1)))).
            { intro Hle.
              assert (Ht : (p <=? Ar (snd (ru_lhs r1))) = true).
              { apply (proj2 (Nat.leb_le p (Ar (snd (ru_lhs r1))))). exact Hle. }
              rewrite Ht in H2.
              discriminate H2. }
            assert (Hle : p <= Ar (snd (ru_lhs r1))).
            { exact (kept_ep_port l Hln (b, p) He (snd (ru_lhs r1)) Hol2). }
            apply Hnot. exact Hle. }
      + (* x <> b *)
        destruct (Nat.eqb x c) eqn:Hxc.
        * (* x = c *)
          apply (proj1 (Nat.eqb_eq x c)) in Hxc.
          subst x.
          destruct (Nat.eqb p 0) eqn:Hpz.
          { (* p = 0: [l] touches (c, 0), hence [l] is the [c d] main--main link. *)
            exfalso.
            apply (proj1 (Nat.eqb_eq p 0)) in Hpz.
            subst p.
            destruct l as [[lx lu] [ly lv]].
            destruct He as [He1 | He2].
            { injection He1 as Hlx Hlu. subst lx. subst lu.
              assert (Hhl : has_link A N (c, 0) (ly, lv)).
              { left. exact Hln. }
              assert (Heq : (d, 0) = (ly, lv)).
              { exact (link_unique A Ar N Hwf (c, 0) (d, 0) (ly, lv) Hlink_cd Hhl). }
              injection Heq as Hly Hlv. subst ly. subst lv.
              simpl in Hmcd.
              assert (Hcc : Nat.eqb c c = true). { apply (proj2 (Nat.eqb_eq c c)). reflexivity. }
              assert (Hdd : Nat.eqb d d = true). { apply (proj2 (Nat.eqb_eq d d)). reflexivity. }
              assert (Hcd_f : Nat.eqb c d = false).
              { destruct (Nat.eqb c d) eqn:Hb.
                - exfalso. apply (proj1 (Nat.eqb_eq c d)) in Hb. apply Hcd. exact Hb.
                - reflexivity. }
              assert (Hdc_f : Nat.eqb d c = false).
              { destruct (Nat.eqb d c) eqn:Hb.
                - exfalso. apply (proj1 (Nat.eqb_eq d c)) in Hb. apply Hdc. exact Hb.
                - reflexivity. }
              rewrite Hcc, Hdd, Hcd_f, Hdc_f in Hmcd.
              simpl in Hmcd.
              discriminate Hmcd. }
            { injection He2 as Hly Hlv. subst ly. subst lv.
              assert (Hhl : has_link A N (c, 0) (lx, lu)).
              { right. exact Hln. }
              assert (Heq : (d, 0) = (lx, lu)).
              { exact (link_unique A Ar N Hwf (c, 0) (d, 0) (lx, lu) Hlink_cd Hhl). }
              injection Heq as Hlx Hlu. subst lx. subst lu.
              simpl in Hmcd.
              assert (Hcc : Nat.eqb c c = true). { apply (proj2 (Nat.eqb_eq c c)). reflexivity. }
              assert (Hdd : Nat.eqb d d = true). { apply (proj2 (Nat.eqb_eq d d)). reflexivity. }
              assert (Hcd_f : Nat.eqb c d = false).
              { destruct (Nat.eqb c d) eqn:Hb.
                - exfalso. apply (proj1 (Nat.eqb_eq c d)) in Hb. apply Hcd. exact Hb.
                - reflexivity. }
              assert (Hdc_f : Nat.eqb d c = false).
              { destruct (Nat.eqb d c) eqn:Hb.
                - exfalso. apply (proj1 (Nat.eqb_eq d c)) in Hb. apply Hdc. exact Hb.
                - reflexivity. }
              rewrite Hcc, Hdd, Hcd_f, Hdc_f in Hmcd.
              simpl in Hmcd.
              discriminate Hmcd. } }
          { (* 1 <= p *)
            assert (Hnz : p <> 0).
            { intro Heq. rewrite Heq in Hpz. simpl in Hpz. discriminate Hpz. }
            assert (H1 : (1 <=? p) = true).
            { apply (proj2 (Nat.leb_le 1 p)). lia. }
            destruct (Nat.leb p (Ar (fst (ru_lhs r2)))) eqn:H2.
            { (* 1 <= p <= Ar (fst (ru_lhs r2)): in range. *)
              set (ipr := nth (p - 1) (ru_iface r2) (0, 0)).
              set (ic := fst ipr).
              set (ipc := snd ipr).
              assert (Hr1e : rw1e (c, p) = (c, p)).
              { unfold rw1e.
                apply rewire_endpoint_fixed.
                - exact Hca.
                - exact Hcb. }
              assert (Hr2e : rw2e (c, p) = (fresh_id A sc_N1 ic, ipc)).
              { unfold rw2e, rewire_endpoint.
                assert (Heqc : Nat.eqb c c = true).
                { apply (proj2 (Nat.eqb_eq c c)). reflexivity. }
                rewrite Heqc, H1, H2.
                simpl.
                unfold freshen_pr.
                reflexivity. }
              assert (Hr2'e : rw2'e (c, p) = (fresh_id A N ic, ipc)).
              { unfold rw2'e, rewire_endpoint.
                assert (Heqc : Nat.eqb c c = true).
                { apply (proj2 (Nat.eqb_eq c c)). reflexivity. }
                rewrite Heqc, H1, H2.
                simpl.
                unfold freshen_pr.
                reflexivity. }
              assert (Hr1'e : rw1'e (fresh_id A N ic, ipc) = (fresh_id A N ic, ipc)).
              { unfold rw1'e.
                apply rewire_endpoint_fixed_net.
                - intro Heq.
                  assert (HaM : a <= sc_M). { exact (abcd_le_scM a Ha). }
                  rewrite <- Heq in HaM.
                  assert (Hgt : fresh_id A N ic > sc_M). { exact (fresh_id_gt_scM ic). }
                  lia.
                - intro Heq.
                  assert (HbM : b <= sc_M). { exact (abcd_le_scM b Hb). }
                  rewrite <- Heq in HbM.
                  assert (Hgt : fresh_id A N ic > sc_M). { exact (fresh_id_gt_scM ic). }
                  lia. }
              rewrite Hr1e.
              rewrite Hr2e.
              rewrite Hr2'e.
              rewrite Hr1'e.
              exact (f_equal (fun q : nat => (q, ipc)) (cm_fresh2p ic)). }
            { (* p > Ar (fst (ru_lhs r2)): contradicts the well-formedness bound. *)
              exfalso.
              assert (Hnot : ~ (p <= Ar (fst (ru_lhs r2)))).
              { intro Hle.
                assert (Ht : (p <=? Ar (fst (ru_lhs r2))) = true).
                { apply (proj2 (Nat.leb_le p (Ar (fst (ru_lhs r2))))). exact Hle. }
                rewrite Ht in H2.
                discriminate H2. }
              assert (Hle : p <= Ar (fst (ru_lhs r2))).
              { exact (kept_ep_port l Hln (c, p) He (fst (ru_lhs r2)) Hol3). }
              apply Hnot. exact Hle. } }
        * (* x <> c *)
          destruct (Nat.eqb x d) eqn:Hxd.
          { (* x = d *)
            apply (proj1 (Nat.eqb_eq x d)) in Hxd.
            subst x.
            destruct (Nat.eqb p 0) eqn:Hpz.
            { (* p = 0: [l] touches (d, 0), hence [l] is the [c d] main--main link. *)
              exfalso.
              apply (proj1 (Nat.eqb_eq p 0)) in Hpz.
              subst p.
              destruct l as [[lx lu] [ly lv]].
              destruct He as [He1 | He2].
              { injection He1 as Hlx Hlu. subst lx. subst lu.
                assert (Hhl : has_link A N (d, 0) (ly, lv)).
                { left. exact Hln. }
                assert (Hhl0 : has_link A N (d, 0) (c, 0)).
                { exact (proj1 (has_link_sym A N (c, 0) (d, 0)) Hlink_cd). }
                assert (Heq : (c, 0) = (ly, lv)).
                { exact (link_unique A Ar N Hwf (d, 0) (c, 0) (ly, lv) Hhl0 Hhl). }
                injection Heq as Hly Hlv. subst ly. subst lv.
                simpl in Hmcd.
                assert (Hcc : Nat.eqb c c = true). { apply (proj2 (Nat.eqb_eq c c)). reflexivity. }
                assert (Hdd : Nat.eqb d d = true). { apply (proj2 (Nat.eqb_eq d d)). reflexivity. }
                assert (Hcd_f : Nat.eqb c d = false).
                { destruct (Nat.eqb c d) eqn:Hb.
                  - exfalso. apply (proj1 (Nat.eqb_eq c d)) in Hb. apply Hcd. exact Hb.
                  - reflexivity. }
                assert (Hdc_f : Nat.eqb d c = false).
                { destruct (Nat.eqb d c) eqn:Hb.
                  - exfalso. apply (proj1 (Nat.eqb_eq d c)) in Hb. apply Hdc. exact Hb.
                  - reflexivity. }
                rewrite Hcc, Hdd, Hcd_f, Hdc_f in Hmcd.
                simpl in Hmcd.
                discriminate Hmcd. }
              { injection He2 as Hly Hlv. subst ly. subst lv.
                assert (Hhl : has_link A N (d, 0) (lx, lu)).
                { right. exact Hln. }
                assert (Hhl0 : has_link A N (d, 0) (c, 0)).
                { exact (proj1 (has_link_sym A N (c, 0) (d, 0)) Hlink_cd). }
                assert (Heq : (c, 0) = (lx, lu)).
                { exact (link_unique A Ar N Hwf (d, 0) (c, 0) (lx, lu) Hhl0 Hhl). }
                injection Heq as Hlx Hlu. subst lx. subst lu.
                simpl in Hmcd.
                assert (Hcc : Nat.eqb c c = true). { apply (proj2 (Nat.eqb_eq c c)). reflexivity. }
                assert (Hdd : Nat.eqb d d = true). { apply (proj2 (Nat.eqb_eq d d)). reflexivity. }
                assert (Hcd_f : Nat.eqb c d = false).
                { destruct (Nat.eqb c d) eqn:Hb.
                  - exfalso. apply (proj1 (Nat.eqb_eq c d)) in Hb. apply Hcd. exact Hb.
                  - reflexivity. }
                assert (Hdc_f : Nat.eqb d c = false).
                { destruct (Nat.eqb d c) eqn:Hb.
                  - exfalso. apply (proj1 (Nat.eqb_eq d c)) in Hb. apply Hdc. exact Hb.
                  - reflexivity. }
                rewrite Hcc, Hdd, Hcd_f, Hdc_f in Hmcd.
                simpl in Hmcd.
                discriminate Hmcd. } }
            { (* 1 <= p *)
              assert (Hnz : p <> 0).
              { intro Heq. rewrite Heq in Hpz. simpl in Hpz. discriminate Hpz. }
              assert (H1 : (1 <=? p) = true).
              { apply (proj2 (Nat.leb_le 1 p)). lia. }
              destruct (Nat.leb p (Ar (snd (ru_lhs r2)))) eqn:H2.
              { (* 1 <= p <= Ar (snd (ru_lhs r2)): in range. *)
                set (ipr := nth (Ar (fst (ru_lhs r2)) + (p - 1)) (ru_iface r2) (0, 0)).
                set (id := fst ipr).
                set (ipd := snd ipr).
                assert (Hr1e : rw1e (d, p) = (d, p)).
                { unfold rw1e.
                  apply rewire_endpoint_fixed.
                  - exact Hda.
                  - exact Hdb. }
                assert (Hr2e : rw2e (d, p) = (fresh_id A sc_N1 id, ipd)).
                { unfold rw2e, rewire_endpoint.
                  assert (Heqd : Nat.eqb d d = true).
                  { apply (proj2 (Nat.eqb_eq d d)). reflexivity. }
                  assert (Heqdc : Nat.eqb d c = false).
                  { destruct (Nat.eqb d c) eqn:Hb.
                    + exfalso. apply (proj1 (Nat.eqb_eq d c)) in Hb. apply Hdc. exact Hb.
                    + reflexivity. }
                  rewrite Heqd, Heqdc, H1, H2.
                  simpl.
                  unfold freshen_pr.
                  reflexivity. }
                assert (Hr2'e : rw2'e (d, p) = (fresh_id A N id, ipd)).
                { unfold rw2'e, rewire_endpoint.
                  assert (Heqd : Nat.eqb d d = true).
                  { apply (proj2 (Nat.eqb_eq d d)). reflexivity. }
                  assert (Heqdc : Nat.eqb d c = false).
                  { destruct (Nat.eqb d c) eqn:Hb.
                    + exfalso. apply (proj1 (Nat.eqb_eq d c)) in Hb. apply Hdc. exact Hb.
                    + reflexivity. }
                  rewrite Heqd, Heqdc, H1, H2.
                  simpl.
                  unfold freshen_pr.
                  reflexivity. }
                assert (Hr1'e : rw1'e (fresh_id A N id, ipd) = (fresh_id A N id, ipd)).
                { unfold rw1'e.
                  apply rewire_endpoint_fixed_net.
                  - intro Heq.
                    assert (HaM : a <= sc_M). { exact (abcd_le_scM a Ha). }
                    rewrite <- Heq in HaM.
                    assert (Hgt : fresh_id A N id > sc_M). { exact (fresh_id_gt_scM id). }
                    lia.
                  - intro Heq.
                    assert (HbM : b <= sc_M). { exact (abcd_le_scM b Hb). }
                    rewrite <- Heq in HbM.
                    assert (Hgt : fresh_id A N id > sc_M). { exact (fresh_id_gt_scM id). }
                    lia. }
                rewrite Hr1e.
                rewrite Hr2e.
                rewrite Hr2'e.
                rewrite Hr1'e.
                exact (f_equal (fun q : nat => (q, ipd)) (cm_fresh2p id)). }
              { (* p > Ar (snd (ru_lhs r2)): contradicts the well-formedness bound. *)
                exfalso.
                assert (Hnot : ~ (p <= Ar (snd (ru_lhs r2)))).
                { intro Hle.
                  assert (Ht : (p <=? Ar (snd (ru_lhs r2))) = true).
                  { apply (proj2 (Nat.leb_le p (Ar (snd (ru_lhs r2))))). exact Hle. }
                  rewrite Ht in H2.
                  discriminate H2. }
                assert (Hle : p <= Ar (snd (ru_lhs r2))).
                { exact (kept_ep_port l Hln (d, p) He (snd (ru_lhs r2)) Hol4). }
                apply Hnot. exact Hle. } } }
          { (* x is none of [a b c d]: all four rewirings fix the endpoint. *)
            assert (Hne1 : x <> a).
            { intro Heq.
              assert (Ht : (x =? a) = true).
              { apply (proj2 (Nat.eqb_eq x a)). exact Heq. }
              rewrite Ht in Hxa.
              discriminate Hxa. }
            assert (Hne2 : x <> b).
            { intro Heq.
              assert (Ht : (x =? b) = true).
              { apply (proj2 (Nat.eqb_eq x b)). exact Heq. }
              rewrite Ht in Hxb.
              discriminate Hxb. }
            assert (Hne3 : x <> c).
            { intro Heq.
              assert (Ht : (x =? c) = true).
              { apply (proj2 (Nat.eqb_eq x c)). exact Heq. }
              rewrite Ht in Hxc.
              discriminate Hxc. }
            assert (Hne4 : x <> d).
            { intro Heq.
              assert (Ht : (x =? d) = true).
              { apply (proj2 (Nat.eqb_eq x d)). exact Heq. }
              rewrite Ht in Hxd.
              discriminate Hxd. }
            assert (Hr1e : rw1e (x, p) = (x, p)).
            { unfold rw1e.
              apply rewire_endpoint_fixed.
              - exact Hne1.
              - exact Hne2. }
            assert (Hr2e : rw2e (x, p) = (x, p)).
            { unfold rw2e.
              apply rewire_endpoint_fixed_net.
              - exact Hne3.
              - exact Hne4. }
            assert (Hr2'e : rw2'e (x, p) = (x, p)).
            { unfold rw2'e.
              apply rewire_endpoint_fixed.
              - exact Hne3.
              - exact Hne4. }
            assert (Hr1'e : rw1'e (x, p) = (x, p)).
            { unfold rw1'e.
              apply rewire_endpoint_fixed_net.
              - exact Hne1.
              - exact Hne2. }
            rewrite Hr1e.
            rewrite Hr2e.
            rewrite Hr2'e.
            rewrite Hr1'e.
            assert (HxM : x <= sc_M).
            { apply abcd_le_scM. exact (kept_ep_agent l Hln (x, p) He). }
            assert (HxM1 : x <= sc_M1).
            { apply surv_scN1.
              - exact (kept_ep_agent l Hln (x, p) He).
              - exact Hne1.
              - exact Hne2. }
            assert (Hcm : comm_map sc_M sc_M1 sc_M2 x = x).
            { apply cm_id. apply nat_le_min. exact HxM. exact HxM1. }
            exact (f_equal (fun q : nat => (q, p)) Hcm). }
  Qed.

  (* The link-level crux: a kept link, rewired by [r1] then [r2] and renamed by
     [comm_map], equals the same kept link rewired by [r2] then [r1]. This is
     the endpoint crux ([crux_ep]) applied to both endpoints and paired. *)
  Local Lemma sc_crux (l : port_ref * port_ref) (Hl : In l Lk) :
    cm_pair_link (rw2 (rw1 l)) = rw1' (rw2' l).
  Proof.
    destruct l as [[x u] [y v]].
    set (e1 := (x, u)).
    set (e2 := (y, v)).
    unfold cm_pair_link, rw1, rw2, rw1', rw2', rewire_link.
    assert (H1 : (comm_map sc_M sc_M1 sc_M2 (fst (rw2e (rw1e e1))), snd (rw2e (rw1e e1))) = rw1'e (rw2'e e1)).
    { apply (crux_ep ((x, u), (y, v)) Hl e1). left. reflexivity. }
    assert (H2 : (comm_map sc_M sc_M1 sc_M2 (fst (rw2e (rw1e e2))), snd (rw2e (rw1e e2))) = rw1'e (rw2'e e2)).
    { apply (crux_ep ((x, u), (y, v)) Hl e2). right. reflexivity. }
    exact (eq_trans
             (f_equal (fun q : port_ref => (q, (comm_map sc_M sc_M1 sc_M2 (fst (rw2e (rw1e e2))), snd (rw2e (rw1e e2))))) H1)
             (f_equal (fun r : port_ref => (rw1'e (rw2'e e1), r)) H2)).
  Qed.

  (* The [ni_links] field: renaming the links of [sc_N12] by [comm_map] permutes
     them into the links of [sc_N21]. The kept block is carried pointwise by the
     crux; the two fresh blocks are swapped. *)
  Local Lemma sc_ni_links :
    Permutation (map cm_pair_link (nt_links sc_N12)) (nt_links sc_N21).
  Proof.
    rewrite sc_links_N12, sc_links_N21.
    rewrite map_app.
    rewrite map_app.
    rewrite (map_map (fun l : port_ref * port_ref => rw2 (rw1 l)) cm_pair_link Lk).
    rewrite map_cm_fl1.
    rewrite map_cm_fl2p.
    assert (Hcommon : map (fun l : port_ref * port_ref => cm_pair_link (rw2 (rw1 l))) Lk
                     = map (fun l : port_ref * port_ref => rw1' (rw2' l)) Lk).
    { apply map_ptw_link. intros l Hl. exact (sc_crux l Hl). }
    rewrite Hcommon.
    apply (Permutation_app_head (map (fun l : port_ref * port_ref => rw1' (rw2' l)) Lk)).
    apply Permutation_app_comm.
  Qed.

  (* The commutation isomorphism: splicing [r2] over [sc_N1] and splicing [r1]
     over [sc_N2] yield isomorphic nets, related by [comm_map]. *)
  Definition step_commuting : net_iso A Ar sc_N12 sc_N21 :=
    mkNetIso (comm_map sc_M sc_M1 sc_M2) sc_ni_agents sc_ni_inj sc_ni_links.

  End Commutation.


(**************************************************************************)
(** ** Raw splice commutes with isomorphism (§4.7 setup) *)

(** Splicing a rule at a pair of [Y] and at the corresponding pair of an
    isomorphic net [X] yield isomorphic nets. This is the single-splice
    counterpart of [step_commuting] and is what lets a [step] be lifted across
    an isomorphism of its source (the "left" iso-compatibility of [step]).
    The witnessing renaming is [ni_map H] on the surviving agents and a
    [shift] on the freshened RHS block (which sits strictly above
    [max_agent_id Y]). *)
Section RawSpliceIso.
  Variables (A : Type) (Ar : A -> nat) (Y X : Net A) (H : net_iso A Ar Y X)
            (a b : nat) (r : Rule A)
            (Ha : has_agent A Y a) (Hb : has_agent A Y b)
            (HwfY : well_formed A Ar Y).

  Local Definition M  := max_agent_id A Y.
  Local Definition Mx := max_agent_id A X.

  (* The witnessing renaming: [ni_map H] on ids at or below [M] (the surviving
     agents of [Y]) and the [shift] from base [M] to base [Mx] above it (the
     freshened RHS block). *)
  Local Definition rs_map (x : nat) : nat :=
    if M <? x then shift Mx M x else ni_map H x.

  Local Definition rsY : Net A := raw_splice A Ar Y a b r.
  Local Definition rsX : Net A := raw_splice A Ar X (@ni_map A Ar Y X H a) (@ni_map A Ar Y X H b) r.

  (* The freshened block of [rsY] is carried positionally to that of [rsX]:
     [rs_map (fresh_id A Y i) = fresh_id A X i]. *)
  Local Lemma rs_map_fresh (i : nat) :
    rs_map (fresh_id A Y i) = fresh_id A X i.
  Proof.
    unfold rs_map, fresh_id, M, Mx.
    assert (Ht : (max_agent_id A Y <? max_agent_id A Y + 1 + i) = true).
    { apply (proj2 (Nat.ltb_lt (max_agent_id A Y) (max_agent_id A Y + 1 + i))). lia. }
    rewrite Ht.
    unfold shift.
    destruct (Nat.leb (max_agent_id A Y) (max_agent_id A X)) eqn:Hlm.
    - apply (proj1 (Nat.leb_le (max_agent_id A Y) (max_agent_id A X))) in Hlm. lia.
    - assert (Hnot : ~ (max_agent_id A Y <= max_agent_id A X)).
      { intro Hle.
        assert (Ht2 : (max_agent_id A Y <=? max_agent_id A X) = true).
        { apply (proj2 (Nat.leb_le (max_agent_id A Y) (max_agent_id A X))). exact Hle. }
        rewrite Ht2 in Hlm. discriminate Hlm. }
      assert (Hmx : max_agent_id A X < max_agent_id A Y). { lia. }
      lia.
  Qed.

  (* Filtering both sides of a permutation by the same boolean predicate
     preserves the permutation. This is the workhorse for stripping the
     images of [a] and [b] from the [ni_agents] permutation when passing to
     the surviving-agent blocks. *)
  Local Lemma perm_filter {T} (P : T -> bool) (L1 L2 : list T)
        (Hperm : Permutation L1 L2) :
    Permutation (filter P L1) (filter P L2).
  Proof.
    induction Hperm as [|x0 l l' Hpl IH | x0 y0 l | l0 l1 l2 Hpre1 IHpre1 Hpre2 IHpre2].
    - simpl. apply Permutation_refl.
    - simpl. destruct (P x0) eqn:Hpx.
      + simpl. apply perm_skip. exact IH.
      + simpl. exact IH.
    - simpl. destruct (P x0) eqn:Hpx; destruct (P y0) eqn:HpY; simpl.
      + exact (perm_swap x0 y0 (filter P l)).
      + reflexivity.
      + reflexivity.
      + reflexivity.
    - apply (Permutation_trans IHpre1 IHpre2).
  Qed.

  (* [map F] and [filter] commute when the source predicate [Q] and the
     target predicate [P] agree on the image: [Q p = P (F p)] for every
     [p] in [L]. No injectivity of [F] is needed. *)
  Local Lemma map_filter_commute {T U} (F : T -> U) (Q : T -> bool) (P : U -> bool)
        (L : list T) (Hqp : forall p, In p L -> Q p = P (F p)) :
    map F (filter Q L) = filter P (map F L).
  Proof.
    induction L as [|h l IH].
    - simpl. reflexivity.
    - assert (IHl : map F (filter Q l) = filter P (map F l)).
      { apply IH. intros p Hpin. exact (Hqp p (in_cons h p l Hpin)). }
      simpl. destruct (Q h) eqn:Hqh.
      + assert (Hpf : P (F h) = true).
        { rewrite <- (Hqp h (in_eq h l)). exact Hqh. }
        rewrite Hpf. simpl. rewrite IHl. reflexivity.
      + assert (Hpf : P (F h) = false).
        { rewrite <- (Hqp h (in_eq h l)). exact Hqh. }
        rewrite Hpf. simpl. rewrite IHl. reflexivity.
  Qed.

  (* Pointwise-equal functions induce equal maps. *)
  Local Lemma rs_map_ptw (f g : nat * A -> nat * A) (l : list (nat * A)) :
    (forall x, In x l -> f x = g x) -> map f l = map g l.
  Proof.
    induction l as [|h t IH]; intros Hpt; simpl.
    - reflexivity.
    - assert (Hh : f h = g h). { exact (Hpt h (in_eq h t)). }
      rewrite Hh.
      assert (Ht : forall x, In x t -> f x = g x).
      { intros x Hx. exact (Hpt x (in_cons h x t Hx)). }
      rewrite (IH Ht). reflexivity.
  Qed.

  (* The iso map [F] on agents of [Y]; the "surviving in [X]" predicate [P]
     (an agent of [X] survives the splice at [ma, mb] iff its id is neither
     [ma] nor [mb]); the surviving-agent blocks [surv_Y]/[surv_X] and the
     freshened RHS blocks [rhs_Y]/[rhs_X] of [rsY]/[rsX]; and [G], the
     witnessing renaming applied to the agents of [rsY]. *)
  Local Definition F (p : nat * A) : nat * A := (ni_map H (fst p), snd p).
  Local Definition P (q : nat * A) : bool :=
    negb (Nat.eqb (fst q) (ni_map H a)) && negb (Nat.eqb (fst q) (ni_map H b)).
  Local Definition surv_Y : list (nat * A) :=
    filter (fun p => negb (Nat.eqb (fst p) a) && negb (Nat.eqb (fst p) b)) (nt_agents Y).
  Local Definition surv_X : list (nat * A) := filter P (nt_agents X).
  Local Definition rhs_Y : list (nat * A) :=
    map (fun p => (fresh_id A Y (fst p), snd p)) (nt_agents (ru_rhs r)).
  Local Definition rhs_X : list (nat * A) :=
    map (fun p => (fresh_id A X (fst p), snd p)) (nt_agents (ru_rhs r)).
  Local Definition G (p : nat * A) : nat * A := (rs_map (fst p), snd p).

  (* [ni_map H] preserves the equality test against a fixed agent [c] of [Y]:
     for an agent [p] of [Y], [fst p = c] iff [ni_map H (fst p) = ni_map H c]
     (by injectivity of [ni_map H] on agents of [Y]). *)
  Local Lemma ni_map_eqb (p : nat * A) (Hpin : In p (nt_agents Y)) (c : nat)
        (Hc : has_agent A Y c) :
    Nat.eqb (fst p) c = Nat.eqb (ni_map H (fst p)) (ni_map H c).
  Proof.
    destruct (Nat.eqb (fst p) c) eqn:H1;
    destruct (Nat.eqb (ni_map H (fst p)) (ni_map H c)) eqn:H2;
    [ (* H1=true, H2=true *)
      reflexivity
    | (* H1=true, H2=false: fst p = c but ni_map H (fst p) <> ni_map H c. *)
      exfalso;
      apply (proj1 (Nat.eqb_eq (fst p) c)) in H1;
      rewrite H1 in H2;
      assert (Ht : (ni_map H c =? ni_map H c) = true) by
        (apply (proj2 (Nat.eqb_eq (ni_map H c) (ni_map H c))); reflexivity);
      rewrite Ht in H2; discriminate H2
    | (* H1=false, H2=true: ni_map H (fst p) = ni_map H c forces fst p = c. *)
      exfalso;
      assert (H2eq : ni_map H (fst p) = ni_map H c) by
        (apply (proj1 (Nat.eqb_eq (ni_map H (fst p)) (ni_map H c))); exact H2);
      assert (Hha : has_agent A Y (fst p)) by
        (apply (proj2 (has_agent_In A Y (fst p)));
         apply (In_map fst (nt_agents Y) p); exact Hpin);
      assert (Hpa : fst p = c) by
        (exact (ni_inj H (fst p) c Hha Hc H2eq));
      assert (Ht : (fst p =? c) = true) by
        (apply (proj2 (Nat.eqb_eq (fst p) c)); exact Hpa);
      rewrite Ht in H1; discriminate H1
    | (* H1=false, H2=false *)
      reflexivity ].
  Qed.

  (* On the surviving agents of [Y], the witnessing map [G] coincides with the
     iso map [F]: a survivor has id [<= M], so [rs_map] takes the [ni_map H]
     branch. *)
  Local Lemma G_eq_F_on_surv (p : nat * A) (Hpin : In p surv_Y) : G p = F p.
  Proof.
    unfold G, F, rs_map, M.
    assert (Hle : fst p <= max_agent_id A Y).
    { apply (list_max_upper_bound (map fst (nt_agents Y)) (fst p)).
      apply (In_map fst (nt_agents Y) p).
      exact (proj1 (proj1 (filter_In
              (fun q : nat * A => negb (Nat.eqb (fst q) a) && negb (Nat.eqb (fst q) b))
              p (nt_agents Y)) Hpin)). }
    destruct (max_agent_id A Y <? fst p) eqn:Hltb.
    - exfalso.
      apply (proj1 (Nat.ltb_lt (max_agent_id A Y) (fst p))) in Hltb.
      lia.
    - simpl. reflexivity.
  Qed.

  (* [map F] over the surviving block of [Y] equals filtering the full image
     [map F (nt_agents Y)] by [P]: the source predicate (id not a/b) and the
     target predicate [P] (id not ma/mb) agree on the image by [ni_map_eqb]. *)
  Local Lemma mapF_surv_eq : map F surv_Y = filter P (map F (nt_agents Y)).
  Proof.
    unfold surv_Y.
    apply (map_filter_commute F
           (fun p => negb (Nat.eqb (fst p) a) && negb (Nat.eqb (fst p) b))
           P (nt_agents Y)).
    intros p Hpin.
    unfold P, F.
    assert (Hqa : Nat.eqb (fst p) a = Nat.eqb (ni_map H (fst p)) (ni_map H a)).
    { exact (ni_map_eqb p Hpin a Ha). }
    assert (Hqb : Nat.eqb (fst p) b = Nat.eqb (ni_map H (fst p)) (ni_map H b)).
    { exact (ni_map_eqb p Hpin b Hb). }
    rewrite Hqa, Hqb.
    reflexivity.
  Qed.

  (* The surviving block of [rsX] is exactly [filter P (nt_agents X)]. *)
  Local Lemma survX_eq : surv_X = filter P (nt_agents X).
  Proof.
    unfold surv_X. reflexivity.
  Qed.

  (* The freshened RHS block of [rsY], under [G], is carried positionally to
     that of [rsX] (by [rs_map_fresh]). *)
  Local Lemma mapG_rhs_eq : map G rhs_Y = rhs_X.
  Proof.
    unfold rhs_Y, rhs_X, G.
    rewrite map_map.
    simpl.
    apply rs_map_ptw. intros p Hpin.
    f_equal.
    exact (rs_map_fresh (fst p)).
  Qed.

  (* The surviving block of [rsY], under [G], is [map F surv_Y] (by
     [G_eq_F_on_surv]). *)
  Local Lemma mapG_surv_eq : map G surv_Y = map F surv_Y.
  Proof.
    apply (rs_map_ptw G F surv_Y). intros p Hpin. exact (G_eq_F_on_surv p Hpin).
  Qed.

  (* The [ni_agents] field: the agents of [rsY] under [G] are a permutation of
     the agents of [rsX]. Both split into a surviving block (related by
     [perm_filter] applied to [ni_agents H]) and a shared freshened RHS block. *)
  Local Lemma rs_ni_agents :
    Permutation (map G (nt_agents rsY)) (nt_agents rsX).
  Proof.
    change (Permutation (map G (surv_Y ++ rhs_Y)) (surv_X ++ rhs_X)).
    rewrite map_app.
    rewrite mapG_surv_eq.
    rewrite mapG_rhs_eq.
    apply Permutation_app.
    - rewrite mapF_surv_eq.
      rewrite survX_eq.
      apply (perm_filter P _ _ (ni_agents H)).
    - apply Permutation_refl.
  Qed.

  (* --- Facts about the agents of [rsY] and the action of [rs_map] --- *)

  (* [rs_map] on an id [<= M] is [ni_map H]. *)
  Local Lemma rs_map_surv (x : nat) (Hle : x <= M) : rs_map x = ni_map H x.
  Proof.
    unfold rs_map, M.
    destruct (max_agent_id A Y <? x) eqn:Hltb.
    - exfalso. apply (proj1 (Nat.ltb_lt (max_agent_id A Y) x)) in Hltb.
      change (x <= max_agent_id A Y) in Hle. lia.
    - simpl. reflexivity.
  Qed.

  (* [rs_map] on an id [> M] is the [shift] to base [Mx]. *)
  Local Lemma rs_map_shift (x : nat) (Hgt : M < x) : rs_map x = shift Mx M x.
  Proof.
    unfold rs_map, M.
    assert (Ht : (max_agent_id A Y <? x) = true).
    { apply (proj2 (Nat.ltb_lt (max_agent_id A Y) x)).
      change (max_agent_id A Y < x) in Hgt. exact Hgt. }
    rewrite Ht. simpl. reflexivity.
  Qed.

  (* A surviving agent of [rsY] (id [<= M]) is an agent of [Y]. *)
  Local Lemma rsY_surv_is_Y_agent (x : nat) (Hx : has_agent A rsY x) (Hle : x <= M) :
    has_agent A Y x.
  Proof.
    apply (proj1 (has_agent_In A rsY x)) in Hx.
    change (In x (map fst (surv_Y ++ rhs_Y))) in Hx.
    rewrite map_app in Hx.
    apply in_app_or in Hx as [Hs|Hr].
    - apply (proj2 (has_agent_In A Y x)).
      apply (proj1 (in_map_iff fst surv_Y x)) in Hs as [p [Hfp Hpin]].
      rewrite <- Hfp.
      apply (In_map fst (nt_agents Y) p).
      apply (proj1 (filter_In
               (fun q : nat * A => negb (Nat.eqb (fst q) a) && negb (Nat.eqb (fst q) b))
               p (nt_agents Y))).
      exact Hpin.
    - exfalso.
      change (In x (map fst rhs_Y)) in Hr.
      unfold rhs_Y in Hr.
      rewrite map_map in Hr. simpl in Hr.
      apply (proj1 (in_map_iff (fun p : nat * A => fresh_id A Y (fst p))
                                (nt_agents (ru_rhs r)) x)) in Hr as [p0 [Hfp Hpin]].
      rewrite <- Hfp in Hle.
      unfold fresh_id, M in Hle.
      lia.
  Qed.

  (* An agent of [rsY] with id [> M] is a freshened RHS id. *)
  Local Lemma rsY_rhs_form (x : nat) (Hx : has_agent A rsY x) (Hgt : M < x) :
    exists i, x = fresh_id A Y i.
  Proof.
    apply (proj1 (has_agent_In A rsY x)) in Hx.
    change (In x (map fst (surv_Y ++ rhs_Y))) in Hx.
    rewrite map_app in Hx.
    apply in_app_or in Hx as [Hs|Hr].
    - exfalso.
      apply (proj1 (in_map_iff fst surv_Y x)) in Hs as [p [Hfp Hpin]].
      assert (Hle : fst p <= M).
      { apply (list_max_upper_bound (map fst (nt_agents Y)) (fst p)).
        apply (In_map fst (nt_agents Y) p).
        apply (proj1 (filter_In
               (fun q : nat * A => negb (Nat.eqb (fst q) a) && negb (Nat.eqb (fst q) b))
               p (nt_agents Y))).
        exact Hpin. }
      rewrite Hfp in Hle. lia.
    - change (In x (map fst rhs_Y)) in Hr.
      unfold rhs_Y in Hr.
      rewrite map_map in Hr. simpl in Hr.
      apply (proj1 (in_map_iff (fun p : nat * A => fresh_id A Y (fst p))
                                (nt_agents (ru_rhs r)) x)) in Hr as [p0 [Hfp Hpin]].
      exists (fst p0). symmetry. exact Hfp.
  Qed.

  (* [ni_map H] of an agent of [Y] is an agent of [X], hence [<= Mx]. *)
  Local Lemma ni_map_bound (x : nat) (Hx : has_agent A Y x) : ni_map H x <= Mx.
  Proof.
    apply (net_iso_agent_fwd A Ar Y X H x) in Hx.
    apply (proj1 (has_agent_In A X (ni_map H x))) in Hx.
    apply (list_max_upper_bound (map fst (nt_agents X)) (ni_map H x)).
    exact Hx.
  Qed.

  (* [(n <=? m) = false] means [m < n]. *)
  Local Lemma leb_false_to_lt (n m : nat) (Hf : (n <=? m) = false) : m < n.
  Proof.
    assert (Hnot : ~ (n <= m)).
    { intro Hle.
      assert (Ht : (n <=? m) = true). { apply (proj2 (Nat.leb_le n m)). exact Hle. }
      rewrite Ht in Hf. discriminate Hf. }
    lia.
  Qed.

  (* The [shift] carries a freshened RHS id of [Y] to the corresponding one of
     [X]: [shift Mx M (fresh_id A Y i) = fresh_id A X i]. *)
  Local Lemma shift_fresh (i : nat) : shift Mx M (fresh_id A Y i) = fresh_id A X i.
  Proof.
    assert (Hgt : M < fresh_id A Y i). { unfold fresh_id, M. lia. }
    rewrite <- (rs_map_shift (fresh_id A Y i) Hgt).
    exact (rs_map_fresh i).
  Qed.

  (* The [ni_inj] field: [rs_map] is injective on the agents of [rsY]. The
     agents split into survivors (ids [<= M], carried by [ni_map H], injective
     by [ni_inj H]) and the freshened RHS block (ids [> M], carried by the
     [shift], which is a translation and hence injective); the two image ranges
     are disjoint (survivors land [<= Mx], the RHS block lands [> Mx]). *)
  Local Lemma rs_ni_inj :
    forall a1 a2, has_agent A rsY a1 -> has_agent A rsY a2
      -> rs_map a1 = rs_map a2 -> a1 = a2.
  Proof.
    intros a1 a2 Ha1 Ha2 Heq.
    destruct (Nat.leb a1 M) eqn:H1; destruct (Nat.leb a2 M) eqn:H2.
    - (* a1 <= M, a2 <= M: both survivors. *)
      apply (proj1 (Nat.leb_le a1 M)) in H1.
      apply (proj1 (Nat.leb_le a2 M)) in H2.
      assert (Hya1 : has_agent A Y a1). { exact (rsY_surv_is_Y_agent a1 Ha1 H1). }
      assert (Hya2 : has_agent A Y a2). { exact (rsY_surv_is_Y_agent a2 Ha2 H2). }
      rewrite (rs_map_surv a1 H1), (rs_map_surv a2 H2) in Heq.
      exact (ni_inj H a1 a2 Hya1 Hya2 Heq).
    - (* a1 <= M, a2 > M: a1 survivor, a2 RHS. *)
      apply (proj1 (Nat.leb_le a1 M)) in H1.
      apply (leb_false_to_lt a2 M) in H2.
      exfalso.
      rewrite (rs_map_surv a1 H1) in Heq.
      rewrite (rs_map_shift a2 H2) in Heq.
      assert (Hb1 : ni_map H a1 <= Mx). { exact (ni_map_bound a1 (rsY_surv_is_Y_agent a1 Ha1 H1)). }
      assert (Hs2 : Mx < shift Mx M a2).
      { destruct (rsY_rhs_form a2 Ha2 H2) as [i Hfi].
        rewrite Hfi.
        rewrite shift_fresh.
        unfold fresh_id, Mx. lia. }
      lia.
    - (* a1 > M, a2 <= M: a1 RHS, a2 survivor. *)
      apply (leb_false_to_lt a1 M) in H1.
      apply (proj1 (Nat.leb_le a2 M)) in H2.
      exfalso.
      rewrite (rs_map_shift a1 H1) in Heq.
      rewrite (rs_map_surv a2 H2) in Heq.
      assert (Hb2 : ni_map H a2 <= Mx). { exact (ni_map_bound a2 (rsY_surv_is_Y_agent a2 Ha2 H2)). }
      assert (Hs1 : Mx < shift Mx M a1).
      { destruct (rsY_rhs_form a1 Ha1 H1) as [i Hfi].
        rewrite Hfi.
        rewrite shift_fresh.
        unfold fresh_id, Mx. lia. }
      lia.
    - (* a1 > M, a2 > M: both RHS. *)
      apply (leb_false_to_lt a1 M) in H1.
      apply (leb_false_to_lt a2 M) in H2.
      destruct (rsY_rhs_form a1 Ha1 H1) as [i1 Hf1].
      destruct (rsY_rhs_form a2 Ha2 H2) as [i2 Hf2].
      rewrite Hf1, Hf2 in Heq.
      rewrite (rs_map_fresh i1), (rs_map_fresh i2) in Heq.
      unfold fresh_id, Mx in Heq.
      assert (Hii : i1 = i2). { lia. }
      rewrite Hf1, Hf2.
      rewrite Hii.
      reflexivity.
  Qed.

  (* ========================================================================== *)
  (* Link-level machinery for the [ni_links] field.                             *)
  (* ========================================================================== *)

  (* Rewiring one endpoint of a kept link of [Y] (resp. [X]) by the splice at
     [a, b] (resp. at the images [ma, mb]). *)
  Local Definition ma := ni_map H a.
  Local Definition mb := ni_map H b.
  Local Definition rwYe (e : port_ref) : port_ref := rewire_endpoint A Ar Y a b r e.
  Local Definition rwXe (e : port_ref) : port_ref := rewire_endpoint A Ar X ma mb r e.

  (* The iso renaming applied to one endpoint (agent renamed, port kept). *)
  Local Definition H_ep (e : port_ref) : port_ref := (ni_map H (fst e), snd e).

  (* The witnessing renaming applied to a whole link (both endpoints). *)
  Local Definition G_link (l : port_ref * port_ref) : port_ref * port_ref :=
    ((rs_map (fst (fst l)), snd (fst l)), (rs_map (fst (snd l)), snd (snd l))).

  (* The iso renaming applied to a whole link. *)
  Local Definition H_link (l : port_ref * port_ref) : port_ref * port_ref :=
    ((ni_map H (fst (fst l)), snd (fst l)), (ni_map H (fst (snd l)), snd (snd l))).

  (* The kept-link and fresh-link blocks of [rsY] and [rsX]. *)
  Local Definition kept_Y : list (port_ref * port_ref) :=
    filter (fun k => negb (is_main_main_link a b k)) (nt_links Y).
  Local Definition kept_X : list (port_ref * port_ref) :=
    filter (fun k => negb (is_main_main_link ma mb k)) (nt_links X).
  Local Definition fresh_Y : list (port_ref * port_ref) :=
    map (fun l => (freshen_pr A Y (fst l), freshen_pr A Y (snd l))) (nt_links (ru_rhs r)).
  Local Definition fresh_X : list (port_ref * port_ref) :=
    map (fun l => (freshen_pr A X (fst l), freshen_pr A X (snd l))) (nt_links (ru_rhs r)).
  Local Definition rwYl (l : port_ref * port_ref) : port_ref * port_ref := rewire_link A Ar Y a b r l.
  Local Definition rwXl (l : port_ref * port_ref) : port_ref * port_ref := rewire_link A Ar X ma mb r l.

  (* [nt_links rsY] and [nt_links rsX] decompose into kept and fresh blocks. *)
  Local Lemma rsY_links_decomp : nt_links rsY = map rwYl kept_Y ++ fresh_Y.
  Proof.
    unfold rsY, raw_splice, splice_links, kept_Y, fresh_Y, rwYl.
    reflexivity.
  Qed.

  Local Lemma rsX_links_decomp : nt_links rsX = map rwXl kept_X ++ fresh_X.
  Proof.
    unfold rsX, raw_splice, splice_links, kept_X, fresh_X, rwXl.
    reflexivity.
  Qed.

  (* Applying the same function to both sides of a permutation preserves the
     permutation (the image multiset is unchanged). *)
  Local Lemma Permutation_map {T U} (f : T -> U) (L1 L2 : list T)
        (Hperm : Permutation L1 L2) :
    Permutation (map f L1) (map f L2).
  Proof.
    induction Hperm as [|x0 l l' Hpl IH | x0 y0 l | l0 l1 l2 Hpre1 IHpre1 Hpre2 IHpre2].
    - simpl. apply Permutation_refl.
    - simpl. apply perm_skip. exact IH.
    - simpl. apply perm_swap.
    - apply (Permutation_trans IHpre1 IHpre2).
  Qed.

  (* [ni_map H] preserves the equality test against a fixed agent [c] of [Y],
     stated directly on agent ids (rather than agent pairs). *)
  Local Lemma ni_map_eqb_agent (x c : nat) (Hx : has_agent A Y x) (Hc : has_agent A Y c) :
    Nat.eqb x c = Nat.eqb (ni_map H x) (ni_map H c).
  Proof.
    apply (proj1 (has_agent_In A Y x)) in Hx.
    apply (proj1 (in_map_iff fst (nt_agents Y) x)) in Hx as [p [Hfp Hpin]].
    rewrite <- Hfp.
    exact (ni_map_eqb p Hpin c Hc).
  Qed.

  (* The main--main test is preserved by the iso renaming: for a link [l]
     of [Y], [l] is the [a b] main--main link iff its image [H_link l] is the
     [ma mb] main--main link. This lets [perm_filter] strip the fired link from
     both sides of [ni_links H]. *)
  Local Lemma mm_pres (l : port_ref * port_ref) (Hl : In l (nt_links Y)) :
    is_main_main_link a b l = is_main_main_link ma mb (H_link l).
  Proof.
    destruct l as [[x1 u1] [x2 u2]].
    unfold H_link, ma, mb.
    assert (Hx1 : has_agent A Y x1).
    { exact (proj1 (wf_link_agents A Ar Y HwfY x1 x2 u1 u2 Hl)). }
    assert (Hx2 : has_agent A Y x2).
    { exact (proj2 (wf_link_agents A Ar Y HwfY x1 x2 u1 u2 Hl)). }
    assert (He1 : Nat.eqb x1 a = Nat.eqb (ni_map H x1) (ni_map H a)).
    { exact (ni_map_eqb_agent x1 a Hx1 Ha). }
    assert (He2 : Nat.eqb x1 b = Nat.eqb (ni_map H x1) (ni_map H b)).
    { exact (ni_map_eqb_agent x1 b Hx1 Hb). }
    assert (He3 : Nat.eqb x2 a = Nat.eqb (ni_map H x2) (ni_map H a)).
    { exact (ni_map_eqb_agent x2 a Hx2 Ha). }
    assert (He4 : Nat.eqb x2 b = Nat.eqb (ni_map H x2) (ni_map H b)).
    { exact (ni_map_eqb_agent x2 b Hx2 Hb). }
    simpl.
    rewrite He1, He2, He3, He4.
    reflexivity.
  Qed.

  (* The endpoint crux: rewiring one endpoint [e] of a kept link of [Y] by the
     splice at [a, b], then renaming by [rs_map], equals renaming [e] by the iso
     and rewiring by the splice at [ma, mb]. This is the single-splice analogue
     of the commutation crux. *)
  Local Lemma rs_crux_ep (l : port_ref * port_ref) (Hl : In l kept_Y) (e : port_ref) (He : link_end l e) :
    (rs_map (fst (rwYe e)), snd (rwYe e)) = rwXe (H_ep e).
  Proof.
    destruct e as [x p].
    (* [l] is a kept link of [Y]: a link of [Y], not the [a b] main--main link. *)
    apply (proj1 (filter_In (fun k : port_ref * port_ref => negb (is_main_main_link a b k)) l (nt_links Y))) in Hl.
    destruct Hl as [Hln _].
    destruct l as [[x1 u1] [x2 u2]].
    (* [x] is an agent of [Y] (endpoint of a link of a well-formed net). *)
    assert (Hx : has_agent A Y x).
    { simpl in He.
      destruct He as [He1 | He2].
      - injection He1 as Hx1 Hu1. subst x1. subst u1.
        exact (proj1 (wf_link_agents A Ar Y HwfY x x2 p u2 Hln)).
      - injection He2 as Hx2 Hu2. subst x2. subst u2.
        exact (proj2 (wf_link_agents A Ar Y HwfY x1 x u1 p Hln)). }
    (* [x <= M], since [x] is an agent of [Y]. *)
    assert (Hlx : x <= M).
    { unfold M.
      apply (list_max_upper_bound (map fst (nt_agents Y)) x).
      apply (proj1 (has_agent_In A Y x)).
      exact Hx. }
    (* Case split on the agent of the endpoint. *)
    destruct (Nat.eqb x a) eqn:Hxa.
    - (* x = a *)
      apply (proj1 (Nat.eqb_eq x a)) in Hxa. subst x.
      assert (Hlea : a <= M).
      { unfold M.
        apply (list_max_upper_bound (map fst (nt_agents Y)) a).
        apply (proj1 (has_agent_In A Y a)).
        exact Ha. }
      assert (Hep : H_ep (a, p) = (ma, p)).
      { unfold H_ep, ma. simpl. reflexivity. }
      rewrite Hep.
      destruct (Nat.leb 1 p && Nat.leb p (Ar (fst (ru_lhs r)))) eqn:Hrange.
      + (* in range: both sides freshen to the same RHS port. *)
        set (ipr := nth (p - 1) (ru_iface r) (0, 0)).
        set (ia := fst ipr).
        set (ipp := snd ipr).
        assert (HrYe : rwYe (a, p) = (fresh_id A Y ia, ipp)).
        { unfold rwYe, rewire_endpoint.
          assert (Heqa : Nat.eqb a a = true). { apply (proj2 (Nat.eqb_eq a a)). reflexivity. }
          rewrite Heqa, Hrange. simpl. unfold freshen_pr. reflexivity. }
        assert (HrXe : rwXe (ma, p) = (fresh_id A X ia, ipp)).
        { unfold rwXe, rewire_endpoint.
          assert (Hema : Nat.eqb ma ma = true). { apply (proj2 (Nat.eqb_eq ma ma)). reflexivity. }
          rewrite Hema, Hrange. simpl. unfold freshen_pr. reflexivity. }
        rewrite HrYe, HrXe.
        f_equal.
        exact (rs_map_fresh ia).
      + (* out of range: both sides keep the endpoint. *)
        assert (HrYe : rwYe (a, p) = (a, p)).
        { unfold rwYe, rewire_endpoint.
          assert (Heqa : Nat.eqb a a = true). { apply (proj2 (Nat.eqb_eq a a)). reflexivity. }
          rewrite Heqa, Hrange. simpl. reflexivity. }
        assert (HrXe : rwXe (ma, p) = (ma, p)).
        { unfold rwXe, rewire_endpoint.
          assert (Hema : Nat.eqb ma ma = true). { apply (proj2 (Nat.eqb_eq ma ma)). reflexivity. }
          rewrite Hema, Hrange. simpl. reflexivity. }
        rewrite HrYe, HrXe.
        f_equal.
        exact (rs_map_surv a Hlea).
    - (* x <> a *)
      destruct (Nat.eqb x b) eqn:Hxb.
      + (* x = b *)
        apply (proj1 (Nat.eqb_eq x b)) in Hxb.
        (* b <> a, so the [a] branch of [rwYe] does not fire; and
           ni_map H b <> ni_map H a, so the [ma] branch of [rwXe] does not fire. *)
        assert (Hba_f : Nat.eqb b a = false).
        { destruct (Nat.eqb b a) eqn:Hbeq.
          - exfalso. apply (proj1 (Nat.eqb_eq b a)) in Hbeq.
            rewrite Hxb in Hxa.
            rewrite Hbeq in Hxa.
            assert (Ht : Nat.eqb a a = true).
            { apply (proj2 (Nat.eqb_eq a a)). reflexivity. }
            rewrite Ht in Hxa. discriminate Hxa.
          - reflexivity. }
        subst x.
        assert (Hleb : b <= M).
        { unfold M.
          apply (list_max_upper_bound (map fst (nt_agents Y)) b).
          apply (proj1 (has_agent_In A Y b)).
          exact Hb. }
        assert (Hep : H_ep (b, p) = (mb, p)).
        { unfold H_ep, mb. simpl. reflexivity. }
        rewrite Hep.
        assert (Hmb_ma_f : Nat.eqb mb ma = false).
        { unfold mb, ma.
          destruct (Nat.eqb (ni_map H b) (ni_map H a)) eqn:Hm.
          - exfalso.
            apply (proj1 (Nat.eqb_eq (ni_map H b) (ni_map H a))) in Hm.
            assert (Hba_eq : b = a). { exact (ni_inj H b a Hb Ha Hm). }
            assert (Hba_ne : b <> a).
            { intro Heq. rewrite Heq in Hba_f.
              assert (Ht : Nat.eqb a a = true). { apply (proj2 (Nat.eqb_eq a a)). reflexivity. }
              rewrite Ht in Hba_f. discriminate Hba_f. }
            exfalso. apply Hba_ne. exact Hba_eq.
          - reflexivity. }
        destruct (Nat.leb 1 p && Nat.leb p (Ar (snd (ru_lhs r)))) eqn:Hrange.
        * (* in range: both sides freshen to the same RHS port. *)
          set (ipr := nth (Ar (fst (ru_lhs r)) + (p - 1)) (ru_iface r) (0, 0)).
          set (ia := fst ipr).
          set (ipp := snd ipr).
          assert (HrYe : rwYe (b, p) = (fresh_id A Y ia, ipp)).
          { unfold rwYe, rewire_endpoint.
            assert (Hba_b : Nat.eqb b a = false). exact Hba_f.
            assert (Hbb : Nat.eqb b b = true). { apply (proj2 (Nat.eqb_eq b b)). reflexivity. }
            rewrite Hba_b, Hbb, Hrange. simpl. unfold freshen_pr. reflexivity. }
          assert (HrXe : rwXe (mb, p) = (fresh_id A X ia, ipp)).
          { unfold rwXe, rewire_endpoint.
            assert (Hmb_ma_b : Nat.eqb mb ma = false). exact Hmb_ma_f.
            assert (Hmbmb : Nat.eqb mb mb = true). { apply (proj2 (Nat.eqb_eq mb mb)). reflexivity. }
            rewrite Hmb_ma_b, Hmbmb, Hrange. simpl. unfold freshen_pr. reflexivity. }
          rewrite HrYe, HrXe.
          f_equal.
          exact (rs_map_fresh ia).
        * (* out of range: both sides keep the endpoint. *)
          assert (HrYe : rwYe (b, p) = (b, p)).
          { unfold rwYe, rewire_endpoint.
            assert (Hba_b : Nat.eqb b a = false). exact Hba_f.
            assert (Hbb : Nat.eqb b b = true). { apply (proj2 (Nat.eqb_eq b b)). reflexivity. }
            rewrite Hba_b, Hbb, Hrange. simpl. reflexivity. }
          assert (HrXe : rwXe (mb, p) = (mb, p)).
          { unfold rwXe, rewire_endpoint.
            assert (Hmb_ma_b : Nat.eqb mb ma = false). exact Hmb_ma_f.
            assert (Hmbmb : Nat.eqb mb mb = true). { apply (proj2 (Nat.eqb_eq mb mb)). reflexivity. }
            rewrite Hmb_ma_b, Hmbmb, Hrange. simpl. reflexivity. }
          rewrite HrYe, HrXe.
          f_equal.
          exact (rs_map_surv b Hleb).
      + (* x <> a, x <> b: both sides keep the endpoint. *)
        assert (Hxa_f : x <> a).
        { intro Heq. rewrite Heq in Hxa.
          assert (Ht : Nat.eqb a a = true). { apply (proj2 (Nat.eqb_eq a a)). reflexivity. }
          rewrite Ht in Hxa. discriminate Hxa. }
        assert (Hxb_f : x <> b).
        { intro Heq. rewrite Heq in Hxb.
          assert (Ht : Nat.eqb b b = true). { apply (proj2 (Nat.eqb_eq b b)). reflexivity. }
          rewrite Ht in Hxb. discriminate Hxb. }
        assert (HrYe : rwYe (x, p) = (x, p)).
        { unfold rwYe, rewire_endpoint.
          rewrite Hxa, Hxb. simpl. reflexivity. }
        assert (Hnx_ma : Nat.eqb (ni_map H x) ma = false).
        { unfold ma.
          destruct (Nat.eqb (ni_map H x) (ni_map H a)) eqn:Hm.
          - exfalso.
            apply (proj1 (Nat.eqb_eq (ni_map H x) (ni_map H a))) in Hm.
            assert (Hxa_eq : x = a). { exact (ni_inj H x a Hx Ha Hm). }
            exfalso. apply Hxa_f. exact Hxa_eq.
          - reflexivity. }
        assert (Hnx_mb : Nat.eqb (ni_map H x) mb = false).
        { unfold mb.
          destruct (Nat.eqb (ni_map H x) (ni_map H b)) eqn:Hm.
          - exfalso.
            apply (proj1 (Nat.eqb_eq (ni_map H x) (ni_map H b))) in Hm.
            assert (Hxb_eq : x = b). { exact (ni_inj H x b Hx Hb Hm). }
            exfalso. apply Hxb_f. exact Hxb_eq.
          - reflexivity. }
        assert (HrXe : rwXe (ni_map H x, p) = (ni_map H x, p)).
        { unfold rwXe, rewire_endpoint.
          rewrite Hnx_ma, Hnx_mb. simpl. reflexivity. }
        assert (Hep : H_ep (x, p) = (ni_map H x, p)).
        { unfold H_ep. simpl. reflexivity. }
        rewrite Hep, HrYe, HrXe.
        f_equal.
        exact (rs_map_surv x Hlx).
  Qed.

  (* The link-level crux: a kept link of [Y], rewired by the splice at [a, b]
     and renamed by [rs_map], equals the same link renamed by the iso and rewired
     by the splice at [ma, mb]. Follows from the endpoint crux on both ends. *)
  Local Lemma rs_crux_link (l : port_ref * port_ref) (Hl : In l kept_Y) :
    G_link (rwYl l) = rwXl (H_link l).
  Proof.
    unfold G_link, rwYl, rwXl, H_link, rewire_link, rwYe, rwXe, H_ep.
    simpl.
    assert (He1 : link_end l (fst l)). { left. reflexivity. }
    assert (He2 : link_end l (snd l)). { right. reflexivity. }
    assert (H1 : (rs_map (fst (rewire_endpoint A Ar Y a b r (fst l))), snd (rewire_endpoint A Ar Y a b r (fst l))) = rewire_endpoint A Ar X ma mb r (ni_map H (fst (fst l)), snd (fst l))).
    { exact (rs_crux_ep l Hl (fst l) He1). }
    assert (H2 : (rs_map (fst (rewire_endpoint A Ar Y a b r (snd l))), snd (rewire_endpoint A Ar Y a b r (snd l))) = rewire_endpoint A Ar X ma mb r (ni_map H (fst (snd l)), snd (snd l))).
    { exact (rs_crux_ep l Hl (snd l) He2). }
    rewrite H1, H2.
    reflexivity.
  Qed.

  (* Pointwise-equal functions induce equal maps (link version). *)
  Local Lemma rs_map_ptw_link (f g : port_ref * port_ref -> port_ref * port_ref) (l : list (port_ref * port_ref)) :
    (forall x, In x l -> f x = g x) -> map f l = map g l.
  Proof.
    induction l as [|h t IH]; intros Hpt; simpl.
    - reflexivity.
    - assert (Hh : f h = g h). { exact (Hpt h (in_eq h t)). }
      rewrite Hh.
      assert (Ht : forall x, In x t -> f x = g x).
      { intros x Hx. exact (Hpt x (in_cons h x t Hx)). }
      rewrite (IH Ht). reflexivity.
  Qed.

  (* The freshened link block of [rsY], under [G_link], is carried positionally
     to that of [rsX] (by [rs_map_fresh] on each endpoint). *)
  Local Lemma mapG_link_fresh_eq : map G_link fresh_Y = fresh_X.
  Proof.
    unfold fresh_Y, fresh_X, G_link, freshen_pr.
    rewrite map_map.
    apply (rs_map_ptw_link
           (fun l : port_ref * port_ref => G_link (freshen_pr A Y (fst l), freshen_pr A Y (snd l)))
           (fun l : port_ref * port_ref => (freshen_pr A X (fst l), freshen_pr A X (snd l)))
           (nt_links (ru_rhs r))).
    intros l Hl.
    unfold G_link, freshen_pr.
    simpl.
    rewrite (rs_map_fresh (fst (fst l))), (rs_map_fresh (fst (snd l))).
    reflexivity.
  Qed.

  (* The [ni_links] field: the links of [rsY] under [G_link] are a permutation
     of the links of [rsX]. Both split into a kept block (related by transporting
     [ni_links H] through the rewiring) and a shared freshened block. *)
  Local Lemma rs_ni_links :
    Permutation (map G_link (nt_links rsY)) (nt_links rsX).
  Proof.
    rewrite rsY_links_decomp, rsX_links_decomp.
    rewrite map_app.
    rewrite map_map.
    rewrite mapG_link_fresh_eq.
    (* Goal: Permutation (map (fun l => G_link (rwYl l)) kept_Y ++ fresh_X)
                  (map rwXl kept_X ++ fresh_X). *)
    apply Permutation_app.
    - (* Permutation (map (fun l => G_link (rwYl l)) kept_Y) (map rwXl kept_X). *)
      (* The kept block of [rsX] is the image, under [H_link], of the kept block
         of [Y] (the main--main test is preserved by [H_link]). *)
      assert (Hmf : map H_link kept_Y = filter (fun l : port_ref * port_ref => negb (is_main_main_link ma mb l)) (map H_link (nt_links Y))).
      { unfold kept_Y.
        apply (map_filter_commute H_link
               (fun l : port_ref * port_ref => negb (is_main_main_link a b l))
               (fun l : port_ref * port_ref => negb (is_main_main_link ma mb l))
               (nt_links Y)).
        intros l Hl.
        f_equal.
        exact (mm_pres l Hl). }
      assert (Hperm_kept : Permutation (map H_link kept_Y) kept_X).
      { rewrite Hmf.
        apply (perm_filter (fun l : port_ref * port_ref => negb (is_main_main_link ma mb l))
                           (map H_link (nt_links Y)) (nt_links X) (ni_links H)). }
      (* Rewiring commutes with the iso renaming on kept links. *)
      assert (Hpt : map (fun l => G_link (rwYl l)) kept_Y = map (fun l => rwXl (H_link l)) kept_Y).
      { apply (rs_map_ptw_link (fun l => G_link (rwYl l)) (fun l => rwXl (H_link l)) kept_Y).
        intros l Hl.
        exact (rs_crux_link l Hl). }
      rewrite Hpt.
      rewrite <- map_map.
      exact (Permutation_map rwXl (map H_link kept_Y) kept_X Hperm_kept).
    - apply Permutation_refl.
  Qed.

  (**************************************************************************)
  (** ** The main result: splicing commutes with the iso renaming. *)

  (** Splicing [Y] at [a, b] is isomorphic to splicing [X] at the images of
      [a, b] under the iso [H : net_iso Y X]. The witnessing renaming is
      [rs_map]: the iso map on the surviving agents (ids [<= M]) and the
      [shift] to the freshened RHS block (ids [> M]). This is the single-splice
      analogue of the two-splice commutation ([step_commuting]). *)
  Theorem raw_splice_iso_compat :
    net_iso A Ar rsY rsX.
  Proof.
    exact (@mkNetIso A Ar rsY rsX rs_map rs_ni_agents rs_ni_inj rs_ni_links).
  Qed.

  End RawSpliceIso.

(**************************************************************************)
(** ** Compatibility of [step] with isomorphism of the source *)

(** [step] is compatible with isomorphism of the source: if [X] is isomorphic
    to [Y], [X] is well-formed, and [Y] steps to [Z], then [X] steps to [Z].
    This transfers a step across an iso by re-firing the image of the active
    pair in [X] (via [raw_splice_iso_compat]). It is the source-side dual of
    [step_iso_compat_r]. *)
Lemma step_iso_compat_l (A : Type) (S : System A) (X Y Z : Net A)
      (Hxy : net_iso A (sys_arity S) X Y)
      (HwfX : well_formed A (sys_arity S) X)
      (Hstep : step A S Y Z) :
  step A S X Z.
Proof.
  set (Ar := sys_arity S).
  destruct Hstep as [Y Z a b α β r HwfY Hap Hla Hlb Hr Hlhs HisoZ].
  (* Inverse iso: [Y -> X]. *)
  assert (Hyx : net_iso A Ar Y X).
  { exact (net_iso_symmetric A Ar X Y Hxy HwfX). }
  set (ma := @ni_map A Ar Y X Hyx a).
  set (mb := @ni_map A Ar Y X Hyx b).
  (* [a], [b] are agents of [Y]. *)
  assert (Ha : has_agent A Y a).
  { change (a <> b /\ has_agent A Y a /\ has_agent A Y b /\ has_link A Y (a, 0) (b, 0)) in Hap.
    exact (proj1 (proj2 Hap)). }
  assert (Hb : has_agent A Y b).
  { change (a <> b /\ has_agent A Y a /\ has_agent A Y b /\ has_link A Y (a, 0) (b, 0)) in Hap.
    exact (proj1 (proj2 (proj2 Hap))). }
  (* Splicing [Y] at [a, b] is iso to splicing [X] at [ma, mb]. *)
  assert (Hsp : net_iso A Ar (raw_splice A Ar Y a b r) (raw_splice A Ar X ma mb r)).
  { exact (raw_splice_iso_compat A Ar Y X Hyx a b r Ha Hb HwfY). }
  (* [raw_splice Y a b r] is well-formed. *)
  assert (Hrhs : well_formed A Ar (ru_rhs r)).
  { exact (sys_valid_wf A S α β r Hr). }
  assert (Hiface : ru_iface r = interface A Ar (ru_rhs r)).
  { exact (sys_valid_iface A S α β r Hr). }
  assert (Hlen := sys_valid_len A S α β r Hr).
  rewrite !Hlhs in Hlen. simpl in Hlen.
  assert (HspY : well_formed A Ar (raw_splice A Ar Y a b r)).
  { exact (raw_splice_wf A Ar Y a b r α β Hla Hlb Hlhs HwfY Hap Hrhs Hiface Hlen). }
  (* Flip [Hsp]: [raw_splice X ma mb r -> raw_splice Y a b r]. *)
  assert (Hsp' : net_iso A Ar (raw_splice A Ar X ma mb r) (raw_splice A Ar Y a b r)).
  { exact (net_iso_symmetric A Ar (raw_splice A Ar Y a b r) (raw_splice A Ar X ma mb r) Hsp HspY). }
  (* Compose with [HisoZ]: [raw_splice X ma mb r -> Z]. *)
  assert (HisoZ' : net_iso A Ar (raw_splice A Ar X ma mb r) Z).
  { exact (net_iso_transitive A Ar (raw_splice A Ar X ma mb r) (raw_splice A Ar Y a b r) Z Hsp' HisoZ). }
  (* [ma, mb] are an active pair in [X]. *)
  assert (HapX : is_active_pair A Ar X ma mb).
  { exact (net_iso_pres_active_pair A Ar Y X Hyx a b Hap). }
  (* Labels are preserved by the iso. *)
  assert (HlaX : agent_label A X ma = Some α).
  { unfold ma.
    assert (Heq : agent_label A X (@ni_map A Ar Y X Hyx a) = agent_label A Y a).
    { exact (net_iso_label A Ar Y X Hyx HwfY a Ha). }
    rewrite Heq. exact Hla. }
  assert (HlbX : agent_label A X mb = Some β).
  { unfold mb.
    assert (Heq : agent_label A X (@ni_map A Ar Y X Hyx b) = agent_label A Y b).
    { exact (net_iso_label A Ar Y X Hyx HwfY b Hb). }
    rewrite Heq. exact Hlb. }
  refine (step_intro A S X Z ma mb α β r HwfX HapX HlaX HlbX Hr Hlhs HisoZ').
Qed.

(**************************************************************************)
(** ** Label preservation under [raw_splice] (for the diamond) *)

(** A surviving agent of [raw_splice] (one whose id is neither of the two fired
    agents) keeps its label: the filter that removes the fired agents leaves its
    entry untouched, and its id is below the fresh-id threshold, so the freshened
    RHS block cannot shadow it. Both lookups (in the spliced net and in [N])
    return the same [Some la], since [c]'s entry is present in both and [c]
    appears at most once (by [wf_ids]). *)
Lemma raw_splice_pres_label (A : Type) (Ar : A -> nat) (N : Net A)
      (Hwf : well_formed A Ar N) (a b c : nat) (r : Rule A)
      (Hc : has_agent A N c) (Hca : c <> a) (Hcb : c <> b) :
  agent_label A (raw_splice A Ar N a b r) c = agent_label A N c.
Proof.
  set (Q := fun p : nat * A => negb (Nat.eqb (fst p) a) && negb (Nat.eqb (fst p) b)).
  set (fresh := fun p : nat * A => (fresh_id A N (fst p), snd p)).
  set (fb := map fresh (nt_agents (ru_rhs r))).
  unfold agent_label, raw_splice, splice_agents.
  simpl.
  (* Pin the goal to the [Q]/[fb] spelling so [rewrite] can match it. *)
  change (agent_label_lookup A c (filter Q (nt_agents N) ++ fb) = agent_label_lookup A c (nt_agents N)).
  assert (Hc_in : In c (map fst (nt_agents N))).
  { exact (proj1 (has_agent_In A N c) Hc). }
  destruct (agent_label A N c) as [la|] eqn:Hlook.
  - (* Hlook : agent_label N c = Some la. *)
    assert (Hcin : In (c, la) (nt_agents N)).
    { exact (agent_label_Some_In A N c la Hlook). }
    (* c survives the filter (c <> a and c <> b). *)
    assert (Hcsurv : In (c, la) (filter Q (nt_agents N))).
    { apply (proj2 (filter_In Q (c, la) (nt_agents N))).
      split.
      + exact Hcin.
      + unfold Q. simpl.
        destruct (Nat.eqb c a) eqn:Hb1; destruct (Nat.eqb c b) eqn:Hb2.
        - exfalso. apply (proj1 (Nat.eqb_eq c a)) in Hb1. apply Hca. exact Hb1.
        - exfalso. apply (proj1 (Nat.eqb_eq c a)) in Hb1. apply Hca. exact Hb1.
        - exfalso. apply (proj1 (Nat.eqb_eq c b)) in Hb2. apply Hcb. exact Hb2.
        - simpl. reflexivity. }
    (* c's entry is in the appended list (the filtered part). *)
    assert (Hcsurv_app : In (c, la) (filter Q (nt_agents N) ++ fb)).
    { apply (in_or_app (filter Q (nt_agents N)) fb (c, la)). left. exact Hcsurv. }
    (* c is not a fresh id (c <= max_agent_id N < fresh_id A N 0). *)
    assert (Hc_le : c <= max_agent_id A N).
    { exact (list_max_upper_bound (map fst (nt_agents N)) c Hc_in). }
    assert (Hc_not_fb : ~ In c (map fst fb)).
    { intro H.
      apply (proj1 (in_map_iff fst fb c)) in H.
      destruct H as [p Hpc].
      destruct Hpc as [Hcp Hin].
      unfold fb in Hin.
      apply (proj1 (in_map_iff fresh (nt_agents (ru_rhs r)) p)) in Hin.
      destruct Hin as [q Hq].
      destruct Hq as [Hqeq Hqin].
      unfold fresh in Hqeq.
      destruct p as [px py].
      simpl in Hcp.
      injection Hqeq as Hcid Hs.
      rewrite Hcp in Hcid.
      unfold fresh_id in Hcid.
      exfalso. lia. }
    (* Functionality: c appears at most once in the appended list. *)
    assert (Hfun : forall l1 l2, In (c, l1) (filter Q (nt_agents N) ++ fb) -> In (c, l2) (filter Q (nt_agents N) ++ fb) -> l1 = l2).
    { intros l1 l2 H1 H2.
      apply in_app_or in H1. apply in_app_or in H2.
      destruct H1 as [H1f|H1x]; destruct H2 as [H2f|H2x].
      - exact (wf_ids_functional Hwf c l1 l2
             (proj1 (proj1 (filter_In Q (c, l1) (nt_agents N)) H1f))
             (proj1 (proj1 (filter_In Q (c, l2) (nt_agents N)) H2f))).
      - exfalso. apply Hc_not_fb. apply (proj2 (in_map_iff fst fb c)).
        exists (c, l2). split; [reflexivity | exact H2x].
      - exfalso. apply Hc_not_fb. apply (proj2 (in_map_iff fst fb c)).
        exists (c, l1). split; [reflexivity | exact H1x].
      - exfalso. apply Hc_not_fb. apply (proj2 (in_map_iff fst fb c)).
        exists (c, l1). split; [reflexivity | exact H1x]. }
    (* The lookup in the spliced net is [Some la]. *)
    assert (Hlook_sp : agent_label_lookup A c (filter Q (nt_agents N) ++ fb) = Some la).
    { exact (agent_label_lookup_In A c (filter Q (nt_agents N) ++ fb) la Hcsurv_app Hfun). }
    (* The lookup in [N] is [Some la]. *)
    assert (Hlook_N : agent_label_lookup A c (nt_agents N) = Some la).
    { exact (agent_label_lookup_In A c (nt_agents N) la Hcin (wf_ids_functional Hwf c)). }
    rewrite Hlook_sp, Hlook_N.
    reflexivity.
  - (* agent_label N c = None. Contradiction: c is an agent, so its label is [Some]. *)
    exfalso.
    apply (proj1 (in_map_iff fst (nt_agents N) c)) in Hc_in.
    destruct Hc_in as [p Hpc].
    destruct Hpc as [Hcp Hp].
    destruct p as [x la]. simpl in Hcp. subst x.
    (* Hp : In (c, la) (nt_agents N). *)
    assert (Hsome : agent_label_lookup A c (nt_agents N) = Some la).
    { exact (agent_label_lookup_In A c (nt_agents N) la Hp (wf_ids_functional Hwf c)). }
    unfold agent_label in Hlook.
    rewrite Hsome in Hlook.
    discriminate Hlook.
Qed.

(** A surviving agent of [raw_splice] (one whose id is neither of the two
    fired agents) is still an agent of the spliced net: the filter that
    removes the fired agents keeps its entry. *)
Lemma raw_splice_pres_agent (A : Type) (Ar : A -> nat) (N : Net A)
      (a b c : nat) (r : Rule A)
      (Hc : has_agent A N c) (Hca : c <> a) (Hcb : c <> b) :
  has_agent A (raw_splice A Ar N a b r) c.
Proof.
  set (Q := fun p : nat * A => negb (Nat.eqb (fst p) a) && negb (Nat.eqb (fst p) b)).
  apply (proj2 (has_agent_In A (raw_splice A Ar N a b r) c)).
  unfold raw_splice.
  simpl.
  (* Goal: In c (map fst (splice_agents A N a b r)). *)
  unfold splice_agents.
  simpl.
  (* Goal: In c (map fst (filter Q (nt_agents N) ++ map (fun p => (fresh_id A N (fst p), snd p)) (nt_agents (ru_rhs r)))). *)
  apply (proj1 (has_agent_In A N c)) in Hc.
  apply (proj1 (in_map_iff fst (nt_agents N) c)) in Hc.
  destruct Hc as [p Hpc].
  destruct Hpc as [Hcp Hp].
  destruct p as [x la].
  simpl in Hcp. subst x.
  (* Hp : In (c, la) (nt_agents N). *)
  apply (proj2 (in_map_iff fst
         (filter Q (nt_agents N) ++ map (fun p : nat * A => (fresh_id A N (fst p), snd p)) (nt_agents (ru_rhs r))) c)).
  exists (c, la).
  split.
  - simpl. reflexivity.
  - apply (in_or_app (filter Q (nt_agents N))
         (map (fun p : nat * A => (fresh_id A N (fst p), snd p)) (nt_agents (ru_rhs r))) (c, la)).
    left.
    apply (proj2 (filter_In Q (c, la) (nt_agents N))).
    split.
    + exact Hp.
    + unfold Q. simpl.
      destruct (Nat.eqb c a) eqn:Hb1; destruct (Nat.eqb c b) eqn:Hb2.
      * exfalso. apply (proj1 (Nat.eqb_eq c a)) in Hb1. apply Hca. exact Hb1.
      * exfalso. apply (proj1 (Nat.eqb_eq c a)) in Hb1. apply Hca. exact Hb1.
      * exfalso. apply (proj1 (Nat.eqb_eq c b)) in Hb2. apply Hcb. exact Hb2.
      * simpl. reflexivity.
Qed.

(**************************************************************************)
(** ** The distinct-LHS-labels condition (for the diamond) *)

(** [distinct_lhs A S] holds when every rule of [S] has two DISTINCT LHS
    labels: no rule fires on a pair of agents carrying the same label. This
    rules out the swapped-orientation subcase of the diamond (firing [a, b]
    versus [b, a] with a rule whose LHS is [(α, α)]), which would require
    [raw_splice N a b r] to be isomorphic to [raw_splice N b a r] — false in
    general (the two splices can be non-isomorphic normal forms). Spec §4.4
    says rules are for *unordered* pairs, so such a rule must be symmetric
    under swapping the two interface halves; our encoding does not enforce
    that symmetry, so we exclude these rules instead. *)
Definition distinct_lhs (A : Type) (S : System A) : Prop :=
  forall α β (r : Rule A), sys_rules S α β = Some r ->
    fst (ru_lhs r) <> snd (ru_lhs r).

(**************************************************************************)
(** ** Trichotomy of two active pairs *)

(** Two active pairs of a well-formed net are either the same pair, the
    swapped pair, or disjoint: sharing one agent forces them to be the same
    (or swapped) pair, because a well-formed net has at most one main–main
    link incident to a given agent's main port ([link_unique]). Pure
    combinatorics — no rule-table premises are needed.

    Stated as a [Type]-sorted sum ([pair_trichotomy]) rather than a [Prop]
    disjunction, so that the diamond (whose goal is [Type]-sorted) can case-
    analyze on it: a [Prop] disjunction cannot be eliminated into [Type]. The
    proof therefore decides the endpoint equalities with the decidable
    [Nat.eqb] (a [Set]-valued predicate, eliminable into [Type]) rather than
    [classic]. *)
Inductive pair_trichotomy (a b c d : nat) : Type :=
| pt_same     : a = c -> b = d -> pair_trichotomy a b c d
| pt_swapped  : a = d -> b = c -> pair_trichotomy a b c d
| pt_disjoint : (a <> c /\ a <> d /\ b <> c /\ b <> d) -> pair_trichotomy a b c d.

(** [eqb_false_neq x y H] turns a decidable-inequality witness [H : x =? y =
    false] into the logical inequality [x <> y]. The converse of the
    [false]-side of [Nat.eqb_eq], which Stdlib does not provide directly. *)
Lemma eqb_false_neq (x y : nat) (H : Nat.eqb x y = false) : x <> y.
Proof.
  intro Hxy.
  rewrite <- Hxy in H.
  assert (Htt : Nat.eqb x x = true).
  { apply (proj2 (Nat.eqb_eq x x)). reflexivity. }
  rewrite Htt in H.
  discriminate H.
Qed.

Lemma active_pairs_trichotomy (A : Type) (Ar : A -> nat) (N : Net A)
      (Hwf : well_formed A Ar N) (a b c d : nat)
      (Hap_ab : is_active_pair A Ar N a b) (Hap_cd : is_active_pair A Ar N c d) :
  pair_trichotomy a b c d.
Proof.
  assert (Hlink_ab : has_link A N (a, 0) (b, 0)).
  { unfold is_active_pair in Hap_ab.
    exact (proj2 (proj2 (proj2 Hap_ab))). }
  assert (Hlink_cd : has_link A N (c, 0) (d, 0)).
  { unfold is_active_pair in Hap_cd.
    exact (proj2 (proj2 (proj2 Hap_cd))). }
  destruct (Nat.eqb a c) eqn:Hac_b.
  - (* a = c *)
    apply (proj1 (Nat.eqb_eq a c)) in Hac_b.
    destruct (Nat.eqb b d) eqn:Hbd_b.
    + (* b = d *)
      apply (proj1 (Nat.eqb_eq b d)) in Hbd_b.
      exact (pt_same a b c d Hac_b Hbd_b).
    + (* b <> d *)
      apply (eqb_false_neq b d) in Hbd_b.
      exfalso.
      rewrite <- Hac_b in Hlink_cd.
      assert (Hbd' : (b, 0) = (d, 0)).
      { exact (link_unique A Ar N Hwf (a, 0) (b, 0) (d, 0) Hlink_ab Hlink_cd). }
      injection Hbd' as Hbd2.
      apply Hbd_b. exact Hbd2.
  - (* a <> c *)
    apply (eqb_false_neq a c) in Hac_b.
    destruct (Nat.eqb a d) eqn:Had_b.
    + (* a = d *)
      apply (proj1 (Nat.eqb_eq a d)) in Had_b.
      destruct (Nat.eqb b c) eqn:Hbc_b.
      * (* b = c *)
        apply (proj1 (Nat.eqb_eq b c)) in Hbc_b.
        exact (pt_swapped a b c d Had_b Hbc_b).
      * (* b <> c *)
        apply (eqb_false_neq b c) in Hbc_b.
        exfalso.
        rewrite <- Had_b in Hlink_cd.
        assert (Hlink_ac : has_link A N (a, 0) (c, 0)).
        { exact (proj1 (has_link_sym A N (c, 0) (a, 0)) Hlink_cd). }
        assert (Hbc' : (b, 0) = (c, 0)).
        { exact (link_unique A Ar N Hwf (a, 0) (b, 0) (c, 0) Hlink_ab Hlink_ac). }
        injection Hbc' as Hbc2.
        apply Hbc_b. exact Hbc2.
    + (* a <> d *)
      apply (eqb_false_neq a d) in Had_b.
      destruct (Nat.eqb b c) eqn:Hbc_b.
      * (* b = c *)
        apply (proj1 (Nat.eqb_eq b c)) in Hbc_b.
        exfalso.
        rewrite <- Hbc_b in Hlink_cd.
        assert (Hlink_ba : has_link A N (b, 0) (a, 0)).
        { exact (proj1 (has_link_sym A N (a, 0) (b, 0)) Hlink_ab). }
        assert (Had' : (a, 0) = (d, 0)).
        { exact (link_unique A Ar N Hwf (b, 0) (a, 0) (d, 0) Hlink_ba Hlink_cd). }
        injection Had' as Had2.
        apply Had_b. exact Had2.
      * (* b <> c *)
        apply (eqb_false_neq b c) in Hbc_b.
        destruct (Nat.eqb b d) eqn:Hbd_b.
        -- (* b = d *)
           apply (proj1 (Nat.eqb_eq b d)) in Hbd_b.
           exfalso.
           rewrite <- Hbd_b in Hlink_cd.
           assert (Hlink_ba : has_link A N (b, 0) (a, 0)).
           { exact (proj1 (has_link_sym A N (a, 0) (b, 0)) Hlink_ab). }
           assert (Hlink_bc : has_link A N (b, 0) (c, 0)).
           { exact (proj1 (has_link_sym A N (c, 0) (b, 0)) Hlink_cd). }
           assert (Hac' : (a, 0) = (c, 0)).
           { exact (link_unique A Ar N Hwf (b, 0) (a, 0) (c, 0) Hlink_ba Hlink_bc). }
           injection Hac' as Hac2.
           apply Hac_b. exact Hac2.
        -- (* b <> d *)
           apply (eqb_false_neq b d) in Hbd_b.
           exact (pt_disjoint a b c d
                  (conj Hac_b (conj Had_b (conj Hbc_b Hbd_b)))).
Qed.

(**************************************************************************)
(** ** The diamond property (strong confluence, §4.7) *)

(** The one-step diamond, up to renaming (§4.7): if [N] reduces to [N1] and
    to [N2] (two steps of [S]), then there is a net [M] reachable from both
    [N1] and [N2] (each in finitely many steps, up to renaming). Stated with
    [step_star_iso] because the model is "nets up to renaming": the concrete
    [step_star] diamond is false when the two steps fire the same pair and
    yield distinct representatives of one isomorphism class (see
    [step_star_iso]). The conclusion is a [Type]-sorted sig (with [∗])
    because [step_star_iso] is [Type]-sorted.

    Requires [distinct_lhs S]: the swapped-orientation subcase (firing
    [a, b] versus [b, a] with a rule whose LHS is [(α, α)]) is excluded,
    since it would force [α = β], contradicting [distinct_lhs]. *)
Theorem diamond (A : Type) (S : System A) (Hdl : distinct_lhs A S) :
  forall N N1 N2, step A S N N1 -> step A S N N2 ->
    { M : Net A & step_star_iso A S N1 M * step_star_iso A S N2 M }.
Proof.
  intros N N1 N2 Hs1 Hs2.
  set (Ar := sys_arity S).
  destruct Hs1 as [N N1 a b α β r1 Hwf Hap_ab Hla Hlb Hr1 Hlhs1 Hiso1].
  destruct Hs2 as [N N2 c d γ δ r2 _ Hap_cd Hlc Hld Hr2 Hlhs2 Hiso2].
  (* The destructs consumed the original step hypotheses; rebuild them from
     the extracted data (both steps fire on the same [N], so [Hwf] serves
     both). Needed by [step_pres_wf] in the disjoint case. *)
  assert (Hs1 : step A S N N1).
  { exact (step_intro A S N N1 a b α β r1 Hwf Hap_ab Hla Hlb Hr1 Hlhs1 Hiso1). }
  assert (Hs2 : step A S N N2).
  { exact (step_intro A S N N2 c d γ δ r2 Hwf Hap_cd Hlc Hld Hr2 Hlhs2 Hiso2). }
  set (R1 := raw_splice A Ar N a b r1).
  destruct (active_pairs_trichotomy A Ar N Hwf a b c d Hap_ab Hap_cd)
    as [Hac Hbd|Had Hbc|Hdisj].
  (* ==================== Case 1: same pair (a = c, b = d) ==================== *)
  - { subst c. subst d.
    assert (Hαγ : α = γ).
    { rewrite Hla in Hlc. injection Hlc as Hαγ'. exact Hαγ'. }
    subst γ.
    assert (Hδβ : β = δ).
    { rewrite Hlb in Hld. injection Hld as Hδβ'. exact Hδβ'. }
    subst δ.
    rewrite Hr1 in Hr2.
    injection Hr2 as Hr12.
    subst r2.
    (* Now R1 = R2; both N1 and N2 are isomorphic to R1. *)
    assert (Hrhs1 : well_formed A Ar (ru_rhs r1)).
    { exact (sys_valid_wf A S α β r1 Hr1). }
    assert (Hiface1 : ru_iface r1 = interface A Ar (ru_rhs r1)).
    { exact (sys_valid_iface A S α β r1 Hr1). }
    assert (Hlen1 := sys_valid_len A S α β r1 Hr1).
    rewrite !Hlhs1 in Hlen1. simpl in Hlen1.
    assert (Hwf_R1 : well_formed A Ar R1).
    { exact (raw_splice_wf A Ar N a b r1 α β Hla Hlb Hlhs1 Hwf Hap_ab Hrhs1 Hiface1 Hlen1). }
    exists R1.
    split.
    - exists N1.
      split.
      + exact (step_star_refl A S N1).
      + exact (net_iso_symmetric A Ar R1 N1 Hiso1 Hwf_R1).
    - exists N2.
      split.
      + exact (step_star_refl A S N2).
      + exact (net_iso_symmetric A Ar R1 N2 Hiso2 Hwf_R1). }
  (* ==================== Case 2: swapped pair (a = d, b = c) ==================== *)
  - { subst d. subst c.
    assert (Hβγ : β = γ).
    { rewrite Hlb in Hlc. injection Hlc as Hβγ'. exact Hβγ'. }
    subst γ.
    assert (Hαδ : α = δ).
    { rewrite Hla in Hld. injection Hld as Hαδ'. exact Hαδ'. }
    subst δ.
    (* Hr2 : sys_rules S β α = Some r2; by symmetry of the rule table,
       sys_rules S β α = sys_rules S α β, so r2 = r1. *)
    rewrite (sys_sym S β α) in Hr2.
    rewrite Hr1 in Hr2.
    injection Hr2 as Hr12.
    subst r2.
    (* Hlhs2 : ru_lhs r1 = (β, α); with Hlhs1 : ru_lhs r1 = (α, β),
       this forces α = β, contradicting distinct_lhs. *)
    rewrite Hlhs1 in Hlhs2.
    injection Hlhs2 as Hαβ Hβα.
    exfalso.
    apply (Hdl α β r1 Hr1).
    rewrite Hlhs1. simpl.
    exact Hαβ. }
  (* ==================== Case 3: disjoint pairs ==================== *)
  - { (* Fire r1 then r2 (or r2 then r1); the two double splices are
         isomorphic by step_commuting. *)
    set (scN1 := sc_N1 A Ar N a b r1).
    set (scN2 := sc_N2 A Ar N c d r2).
    set (scN12 := sc_N12 A Ar N a b c d r1 r2).
    set (scN21 := sc_N21 A Ar N a b c d r1 r2).
    set (c' := @ni_map A Ar scN1 N1 Hiso1 c).
    set (d' := @ni_map A Ar scN1 N1 Hiso1 d).
    set (a' := @ni_map A Ar scN2 N2 Hiso2 a).
    set (b' := @ni_map A Ar scN2 N2 Hiso2 b).
    (* System validity of the two rules. *)
    assert (Hrhs1 : well_formed A Ar (ru_rhs r1)).
    { exact (sys_valid_wf A S α β r1 Hr1). }
    assert (Hiface1 : ru_iface r1 = interface A Ar (ru_rhs r1)).
    { exact (sys_valid_iface A S α β r1 Hr1). }
    assert (Hlen1_eq := sys_valid_len A S α β r1 Hr1).
    rewrite !Hlhs1 in Hlen1_eq. simpl in Hlen1_eq.
    (* Hlen1_eq : length (ru_iface r1) = Ar α + Ar β. *)
    assert (Hlen1_fst : length (ru_iface r1) = Ar (fst (ru_lhs r1)) + Ar (snd (ru_lhs r1))).
    { exact (sys_valid_len A S α β r1 Hr1). }
    assert (Hlen1_le : Ar (fst (ru_lhs r1)) + Ar (snd (ru_lhs r1)) <= length (ru_iface r1)).
    { rewrite Hlen1_fst. lia. }
    assert (Hrhs2 : well_formed A Ar (ru_rhs r2)).
    { exact (sys_valid_wf A S γ δ r2 Hr2). }
    assert (Hiface2 : ru_iface r2 = interface A Ar (ru_rhs r2)).
    { exact (sys_valid_iface A S γ δ r2 Hr2). }
    assert (Hlen2_fst : length (ru_iface r2) = Ar (fst (ru_lhs r2)) + Ar (snd (ru_lhs r2))).
    { exact (sys_valid_len A S γ δ r2 Hr2). }
    (* The LHS components of each rule. *)
    assert (Hf1 : fst (ru_lhs r1) = α). { rewrite Hlhs1. reflexivity. }
    assert (Hs1l : snd (ru_lhs r1) = β). { rewrite Hlhs1. reflexivity. }
    assert (Hf2 : fst (ru_lhs r2) = γ). { rewrite Hlhs2. reflexivity. }
    assert (Hs2l : snd (ru_lhs r2) = δ). { rewrite Hlhs2. reflexivity. }
    assert (Hlen2_γδ : length (ru_iface r2) = Ar γ + Ar δ).
    { rewrite Hf2, Hs2l in Hlen2_fst. exact Hlen2_fst. }
    (* Orientation premises for step_commuting. *)
    assert (Hol1 : agent_label A N a = Some (fst (ru_lhs r1))).
    { rewrite <- Hf1 in Hla. exact Hla. }
    assert (Hol2 : agent_label A N b = Some (snd (ru_lhs r1))).
    { rewrite <- Hs1l in Hlb. exact Hlb. }
    assert (Hol3 : agent_label A N c = Some (fst (ru_lhs r2))).
    { rewrite <- Hf2 in Hlc. exact Hlc. }
    assert (Hol4 : agent_label A N d = Some (snd (ru_lhs r2))).
    { rewrite <- Hs2l in Hld. exact Hld. }
    (* The single splices are well-formed. *)
    assert (Hwf_scN1 : well_formed A Ar scN1).
    { exact (raw_splice_wf A Ar N a b r1 α β Hla Hlb Hlhs1 Hwf Hap_ab Hrhs1 Hiface1 Hlen1_eq). }
    assert (Hwf_scN2 : well_formed A Ar scN2).
    { exact (raw_splice_wf A Ar N c d r2 γ δ Hlc Hld Hlhs2 Hwf Hap_cd Hrhs2 Hiface2 Hlen2_γδ). }
    (* The four agents of the two pairs, and the disjointness inequalities. *)
    assert (Ha : has_agent A N a).
    { change (a <> b /\ has_agent A N a /\ has_agent A N b /\ has_link A N (a, 0) (b, 0)) in Hap_ab.
      exact (proj1 (proj2 Hap_ab)). }
    assert (Hb : has_agent A N b).
    { change (a <> b /\ has_agent A N a /\ has_agent A N b /\ has_link A N (a, 0) (b, 0)) in Hap_ab.
      exact (proj1 (proj2 (proj2 Hap_ab))). }
    assert (Hc : has_agent A N c).
    { change (c <> d /\ has_agent A N c /\ has_agent A N d /\ has_link A N (c, 0) (d, 0)) in Hap_cd.
      exact (proj1 (proj2 Hap_cd)). }
    assert (Hd : has_agent A N d).
    { change (c <> d /\ has_agent A N c /\ has_agent A N d /\ has_link A N (c, 0) (d, 0)) in Hap_cd.
      exact (proj1 (proj2 (proj2 Hap_cd))). }
    assert (Hac : a <> c). { exact (proj1 Hdisj). }
    assert (Had : a <> d). { exact (proj1 (proj2 Hdisj)). }
    assert (Hbc : b <> c). { exact (proj1 (proj2 (proj2 Hdisj))). }
    assert (Hbd : b <> d). { exact (proj2 (proj2 (proj2 Hdisj))). }
    assert (Hca : c <> a). { intro H. apply Hac. symmetry. exact H. }
    assert (Hcb : c <> b). { intro H. apply Hbc. symmetry. exact H. }
    assert (Hda : d <> a). { intro H. apply Had. symmetry. exact H. }
    assert (Hdb : d <> b). { intro H. apply Hbd. symmetry. exact H. }
    (* The flipped disjointness, for firing (c, d) with survivors (a, b). *)
    assert (Hdisj2 : c <> a /\ c <> b /\ d <> a /\ d <> b).
    { split; [exact Hca | split; [exact Hcb | split; [exact Hda | exact Hdb]]]. }
    (* The surviving agents in the single splices. *)
    assert (Hc_scN1 : has_agent A scN1 c).
    { exact (raw_splice_pres_agent A Ar N a b c r1 Hc Hca Hcb). }
    assert (Hd_scN1 : has_agent A scN1 d).
    { exact (raw_splice_pres_agent A Ar N a b d r1 Hd Hda Hdb). }
    assert (Ha_scN2 : has_agent A scN2 a).
    { exact (raw_splice_pres_agent A Ar N c d a r2 Ha Hac Had). }
    assert (Hb_scN2 : has_agent A scN2 b).
    { exact (raw_splice_pres_agent A Ar N c d b r2 Hb Hbc Hbd). }
    (* The surviving labels in the single splices. *)
    assert (Hlc_scN1 : agent_label A scN1 c = Some (fst (ru_lhs r2))).
    { assert (Heq : agent_label A scN1 c = agent_label A N c).
      { exact (raw_splice_pres_label A Ar N Hwf a b c r1 Hc Hca Hcb). }
      rewrite Heq, Hlc.
      rewrite <- Hf2.
      reflexivity. }
    assert (Hld_scN1 : agent_label A scN1 d = Some (snd (ru_lhs r2))).
    { assert (Heq : agent_label A scN1 d = agent_label A N d).
      { exact (raw_splice_pres_label A Ar N Hwf a b d r1 Hd Hda Hdb). }
      rewrite Heq, Hld.
      rewrite <- Hs2l.
      reflexivity. }
    assert (Hla_scN2 : agent_label A scN2 a = Some (fst (ru_lhs r1))).
    { assert (Heq : agent_label A scN2 a = agent_label A N a).
      { exact (raw_splice_pres_label A Ar N Hwf c d a r2 Ha Hac Had). }
      rewrite Heq, Hla.
      rewrite <- Hf1.
      reflexivity. }
    assert (Hlb_scN2 : agent_label A scN2 b = Some (snd (ru_lhs r1))).
    { assert (Heq : agent_label A scN2 b = agent_label A N b).
      { exact (raw_splice_pres_label A Ar N Hwf c d b r2 Hb Hbc Hbd). }
      rewrite Heq, Hlb.
      rewrite <- Hs1l.
      reflexivity. }
    (* The other pair is still active in each single splice. *)
    assert (Hap_scN1 : is_active_pair A Ar scN1 c d).
    { exact (raw_splice_pres_pair A Ar N a b c d r1 Hwf Hap_ab Hap_cd Hdisj). }
    assert (Hap_scN2 : is_active_pair A Ar scN2 a b).
    { exact (raw_splice_pres_pair A Ar N c d a b r2 Hwf Hap_cd Hap_ab Hdisj2). }
    (* Reflexive LHS facts. *)
    assert (Hlhs1' : ru_lhs r1 = (fst (ru_lhs r1), snd (ru_lhs r1))).
    { rewrite Hf1, Hs1l, Hlhs1. reflexivity. }
    assert (Hlhs2' : ru_lhs r2 = (fst (ru_lhs r2), snd (ru_lhs r2))).
    { rewrite Hf2, Hs2l, Hlhs2. reflexivity. }
    (* The double splices are well-formed. *)
    assert (Hwf_scN12 : well_formed A Ar scN12).
    { exact (raw_splice_wf A Ar scN1 c d r2 (fst (ru_lhs r2)) (snd (ru_lhs r2))
             Hlc_scN1 Hld_scN1 Hlhs2' Hwf_scN1 Hap_scN1 Hrhs2 Hiface2 Hlen2_fst). }
    assert (Hwf_scN21 : well_formed A Ar scN21).
    { exact (raw_splice_wf A Ar scN2 a b r1 (fst (ru_lhs r1)) (snd (ru_lhs r1))
             Hla_scN2 Hlb_scN2 Hlhs1' Hwf_scN2 Hap_scN2 Hrhs1 Hiface1 Hlen1_fst). }
    (* ---- The step N1 -> scN12 (fire r2 on the image of c, d in N1) ---- *)
    assert (Hap_N1 : is_active_pair A Ar N1 c' d').
    { exact (step_preserves_pair A S N N1 a b c d r1 Hiso1 Hwf Hap_ab Hap_cd Hdisj). }
    assert (Hwf_N1 : well_formed A Ar N1).
    { exact (step_pres_wf A S N N1 Hs1). }
    assert (Hc_N1 : has_agent A N1 c').
    { unfold c'.
      exact (net_iso_agent_fwd A Ar scN1 N1 Hiso1 c Hc_scN1). }
    assert (Hd_N1 : has_agent A N1 d').
    { unfold d'.
      exact (net_iso_agent_fwd A Ar scN1 N1 Hiso1 d Hd_scN1). }
    assert (Hlc_N1 : agent_label A N1 c' = Some (fst (ru_lhs r2))).
    { unfold c'.
      assert (Heq : agent_label A N1 (@ni_map A Ar scN1 N1 Hiso1 c) = agent_label A scN1 c).
      { exact (net_iso_label A Ar scN1 N1 Hiso1 Hwf_scN1 c Hc_scN1). }
      rewrite Heq.
      exact Hlc_scN1. }
    assert (Hld_N1 : agent_label A N1 d' = Some (snd (ru_lhs r2))).
    { unfold d'.
      assert (Heq : agent_label A N1 (@ni_map A Ar scN1 N1 Hiso1 d) = agent_label A scN1 d).
      { exact (net_iso_label A Ar scN1 N1 Hiso1 Hwf_scN1 d Hd_scN1). }
      rewrite Heq.
      exact Hld_scN1. }
    assert (Hr2' : sys_rules S (fst (ru_lhs r2)) (snd (ru_lhs r2)) = Some r2).
    { rewrite <- Hf2, <- Hs2l in Hr2. exact Hr2. }
    assert (Hsp : net_iso A Ar scN12 (raw_splice A Ar N1 c' d' r2)).
    { exact (raw_splice_iso_compat A Ar scN1 N1 Hiso1 c d r2 Hc_scN1 Hd_scN1 Hwf_scN1). }
    assert (Hsp' : net_iso A Ar (raw_splice A Ar N1 c' d' r2) scN12).
    { exact (net_iso_symmetric A Ar scN12 (raw_splice A Ar N1 c' d' r2) Hsp Hwf_scN12). }
    assert (Hstep_N1 : step A S N1 scN12).
    { refine (step_intro A S N1 scN12 c' d' (fst (ru_lhs r2)) (snd (ru_lhs r2)) r2
             Hwf_N1 Hap_N1 Hlc_N1 Hld_N1 Hr2' Hlhs2' Hsp'). }
    (* ---- The step N2 -> scN21 (fire r1 on the image of a, b in N2) ---- *)
    assert (Hap_N2 : is_active_pair A Ar N2 a' b').
    { exact (step_preserves_pair A S N N2 c d a b r2 Hiso2 Hwf Hap_cd Hap_ab Hdisj2). }
    assert (Hwf_N2 : well_formed A Ar N2).
    { exact (step_pres_wf A S N N2 Hs2). }
    assert (Ha_N2 : has_agent A N2 a').
    { unfold a'.
      exact (net_iso_agent_fwd A Ar scN2 N2 Hiso2 a Ha_scN2). }
    assert (Hb_N2 : has_agent A N2 b').
    { unfold b'.
      exact (net_iso_agent_fwd A Ar scN2 N2 Hiso2 b Hb_scN2). }
    assert (Hla_N2 : agent_label A N2 a' = Some (fst (ru_lhs r1))).
    { unfold a'.
      assert (Heq : agent_label A N2 (@ni_map A Ar scN2 N2 Hiso2 a) = agent_label A scN2 a).
      { exact (net_iso_label A Ar scN2 N2 Hiso2 Hwf_scN2 a Ha_scN2). }
      rewrite Heq.
      exact Hla_scN2. }
    assert (Hlb_N2 : agent_label A N2 b' = Some (snd (ru_lhs r1))).
    { unfold b'.
      assert (Heq : agent_label A N2 (@ni_map A Ar scN2 N2 Hiso2 b) = agent_label A scN2 b).
      { exact (net_iso_label A Ar scN2 N2 Hiso2 Hwf_scN2 b Hb_scN2). }
      rewrite Heq.
      exact Hlb_scN2. }
    assert (Hr1' : sys_rules S (fst (ru_lhs r1)) (snd (ru_lhs r1)) = Some r1).
    { rewrite <- Hf1, <- Hs1l in Hr1. exact Hr1. }
    assert (Hsp2 : net_iso A Ar scN21 (raw_splice A Ar N2 a' b' r1)).
    { exact (raw_splice_iso_compat A Ar scN2 N2 Hiso2 a b r1 Ha_scN2 Hb_scN2 Hwf_scN2). }
    assert (Hsp2' : net_iso A Ar (raw_splice A Ar N2 a' b' r1) scN21).
    { exact (net_iso_symmetric A Ar scN21 (raw_splice A Ar N2 a' b' r1) Hsp2 Hwf_scN21). }
    assert (Hstep_N2 : step A S N2 scN21).
    { refine (step_intro A S N2 scN21 a' b' (fst (ru_lhs r1)) (snd (ru_lhs r1)) r1
             Hwf_N2 Hap_N2 Hla_N2 Hlb_N2 Hr1' Hlhs1' Hsp2'). }
    (* ---- The diamond: M = scN12; N2 reaches it via scN21 ≈ scN12 ---- *)
    exists scN12.
    split.
    - exists scN12.
      split.
      + exact (step_star_cons A S N1 scN12 scN12 Hstep_N1 (step_star_refl A S scN12)).
      + exact (net_iso_reflexive A Ar scN12).
    - exists scN21.
      split.
      + exact (step_star_cons A S N2 scN21 scN21 Hstep_N2 (step_star_refl A S scN21)).
      + exact (net_iso_symmetric A Ar scN12 scN21
               (step_commuting A Ar N a b c d r1 r2 Hwf Hap_ab Hap_cd Hdisj
                 Hrhs1 Hiface1 Hol1 Hol2 Hol3 Hol4 Hlen1_le)
               Hwf_scN12). }
Qed.

(**************************************************************************)
(** ** Confluence (section 4.7) *)

(** The [diamond] above concludes a [step_star_iso] join (a star sequence on
    each side). The spec's 4.7 diamond property is stronger: the join is
    reached in AT MOST ONE step on each side (zero steps when the two fired
    pairs coincide, one step when they are disjoint). That one-step strength
    is exactly what the Church-Rosser argument needs: in the inductive case
    of the step-vs-[step_star] peak lemma, the diamond must yield a single
    [step] (not a star) so that the induction hypothesis applies.

    [atmost1_step_iso A S N M] holds when [M] is reachable from [N] by at
    most one step of [S], up to renaming: either [N] is isomorphic to [M]
    (zero steps) or there is a net [M'] with [N -> M'] and [M'] isomorphic to
    [M] (one step). [Type]-sorted (a [sum] of the two cases) so it can be
    eliminated in a [Type] goal. Note [+] is [Nat.add] here ([nat_scope] is
    open), so the sum is written with [sum] explicitly. *)
Definition atmost1_step_iso (A : Type) (S : System A) (N M : Net A) : Type :=
  sum (net_iso A (sys_arity S) N M)
      { M' : Net A & step A S N M' * net_iso A (sys_arity S) M' M }.

(** A star sequence starting from a well-formed net ends in a well-formed net:
    each step preserves well-formedness ([step_pres_wf]), and the empty
    sequence ends where it started. *)
Lemma step_star_pres_wf (A : Type) (S : System A) (N M : Net A)
      (HwfN : well_formed A (sys_arity S) N)
      (Hstar : step_star A S N M) :
  well_formed A (sys_arity S) M.
Proof.
  induction Hstar as [N | N N' M Hstep Hstar' IH].
  - subst. exact HwfN.
  - exact (IH (step_pres_wf A S N N' Hstep)).
Qed.

(** A star sequence is compatible with isomorphism of its SOURCE, up to
    isomorphism of the target: if [M1] is isomorphic to [M] and [M] star-
    reaches [M2], then [M1] star-reaches some [M3] isomorphic to [M2]. The
    target is matched up to [net_iso] (not literally [M2]) because the concrete
    [step_star] is not closed under isomorphism in the zero-step case: the
    empty sequence from [M] to [M] transports to the empty sequence from [M1]
    to [M1], which is isomorphic to [M], not equal to it.

    The proof transports the star one step at a time across the source iso via
    [step_iso_compat_l], which re-fires the image of the active pair and lands
    on the SAME target, so only the base (empty) case needs the up-to-iso
    slack. *)
Lemma star_iso_source (A : Type) (S : System A) (M1 M M2 : Net A)
      (Hiso : net_iso A (sys_arity S) M1 M)
      (HwfM1 : well_formed A (sys_arity S) M1)
      (Hstar : step_star A S M M2) :
  { M3 : Net A & step_star A S M1 M3 * net_iso A (sys_arity S) M3 M2 }.
Proof.
  set (Ar := sys_arity S).
  induction Hstar as [M | M M' M2 Hstep Hstar'].
  - exists M1.
    exact (pair (step_star_refl A S M1) Hiso).
  - assert (Hstep' : step A S M1 M').
    { exact (step_iso_compat_l A S M1 M M' Hiso HwfM1 Hstep). }
    exists M2.
    exact (pair (step_star_cons A S M1 M' M2 Hstep' Hstar')
           (net_iso_reflexive A Ar M2)).
Qed.

(** [step_star_iso] is transitive: a star-up-to-iso from [X] to [M] followed
    by a star-up-to-iso from [M] to [K] is a star-up-to-iso from [X] to [K].
    The source [X] must be well-formed so the intermediate star can be
    transported across the source iso ([star_iso_source]). *)
Lemma step_star_iso_trans (A : Type) (S : System A) (X M K : Net A)
      (HwfX : well_formed A (sys_arity S) X)
      (H1 : step_star_iso A S X M)
      (H2 : step_star_iso A S M K) :
  step_star_iso A S X K.
Proof.
  set (Ar := sys_arity S).
  destruct H1 as [M1 [Hstar1 Hiso1]].
  destruct H2 as [M2 [Hstar2 Hiso2]].
  assert (HwfM1 : well_formed A Ar M1).
  { exact (step_star_pres_wf A S X M1 HwfX Hstar1). }
  destruct (star_iso_source A S M1 M M2 Hiso1 HwfM1 Hstar2) as [M3 [Hstar3 Hiso3]].
  exists M3.
  split.
  - exact (step_star_trans A S X M1 M3 Hstar1 Hstar3).
  - exact (net_iso_transitive A Ar M3 M2 K Hiso3 Hiso2).
Qed.

(** An at-most-one-step-up-to-iso reachability is in particular a star-up-to-
    iso reachability: the zero-step case is the empty star, the one-step case
    is a one-element star. *)
Lemma atmost1_to_star_iso (A : Type) (S : System A) (N M : Net A)
      (H : atmost1_step_iso A S N M) :
  step_star_iso A S N M.
Proof.
  set (Ar := sys_arity S).
  destruct H as [Hiso | Hsig].
  - exists N.
    exact (pair (step_star_refl A S N) Hiso).
  - destruct Hsig as [M' [Hstep Hiso]].
    exists M'.
    exact (pair (step_star_step A S N M' Hstep) Hiso).
Qed.

(** The [diamond] restated with the spec's 4.7 one-step strength: the join [M]
    is reached from [N1] and [N2] in AT MOST ONE step each (up to renaming),
    not by an arbitrary star sequence. This is the form the Church-Rosser
    argument needs (see [atmost1_step_iso]). The proof is the same case
    analysis as [diamond]; only the final packaging differs: the same-pair
    case is a zero-step iso, the disjoint case is a single step on each side
    (the two double splices being isomorphic by [step_commuting]). *)
Theorem diamond_atmost1 (A : Type) (S : System A) (Hdl : distinct_lhs A S) :
  forall N N1 N2, step A S N N1 -> step A S N N2 ->
    { M : Net A & atmost1_step_iso A S N1 M * atmost1_step_iso A S N2 M }.
Proof.
  intros N N1 N2 Hs1 Hs2.
  set (Ar := sys_arity S).
  destruct Hs1 as [N N1 a b α β r1 Hwf Hap_ab Hla Hlb Hr1 Hlhs1 Hiso1].
  destruct Hs2 as [N N2 c d γ δ r2 _ Hap_cd Hlc Hld Hr2 Hlhs2 Hiso2].
  (* The destructs consumed the original step hypotheses; rebuild them from
     the extracted data (both steps fire on the same [N], so [Hwf] serves
     both). Needed by [step_pres_wf] in the disjoint case. *)
  assert (Hs1 : step A S N N1).
  { exact (step_intro A S N N1 a b α β r1 Hwf Hap_ab Hla Hlb Hr1 Hlhs1 Hiso1). }
  assert (Hs2 : step A S N N2).
  { exact (step_intro A S N N2 c d γ δ r2 Hwf Hap_cd Hlc Hld Hr2 Hlhs2 Hiso2). }
  set (R1 := raw_splice A Ar N a b r1).
  destruct (active_pairs_trichotomy A Ar N Hwf a b c d Hap_ab Hap_cd)
    as [Hac Hbd|Had Hbc|Hdisj].
  (* ==================== Case 1: same pair (a = c, b = d) ==================== *)
  - { subst c. subst d.
    assert (Hαγ : α = γ).
    { rewrite Hla in Hlc. injection Hlc as Hαγ'. exact Hαγ'. }
    subst γ.
    assert (Hδβ : β = δ).
    { rewrite Hlb in Hld. injection Hld as Hδβ'. exact Hδβ'. }
    subst δ.
    rewrite Hr1 in Hr2.
    injection Hr2 as Hr12.
    subst r2.
    (* Now R1 = R2; both N1 and N2 are isomorphic to R1. *)
    assert (Hrhs1 : well_formed A Ar (ru_rhs r1)).
    { exact (sys_valid_wf A S α β r1 Hr1). }
    assert (Hiface1 : ru_iface r1 = interface A Ar (ru_rhs r1)).
    { exact (sys_valid_iface A S α β r1 Hr1). }
    assert (Hlen1 := sys_valid_len A S α β r1 Hr1).
    rewrite !Hlhs1 in Hlen1. simpl in Hlen1.
    assert (Hwf_R1 : well_formed A Ar R1).
    { exact (raw_splice_wf A Ar N a b r1 α β Hla Hlb Hlhs1 Hwf Hap_ab Hrhs1 Hiface1 Hlen1). }
    exists R1.
    split.
    - exact (inl (net_iso_symmetric A Ar R1 N1 Hiso1 Hwf_R1)).
    - exact (inl (net_iso_symmetric A Ar R1 N2 Hiso2 Hwf_R1)). }
  (* ==================== Case 2: swapped pair (a = d, b = c) ==================== *)
  - { subst d. subst c.
    assert (Hβγ : β = γ).
    { rewrite Hlb in Hlc. injection Hlc as Hβγ'. exact Hβγ'. }
    subst γ.
    assert (Hαδ : α = δ).
    { rewrite Hla in Hld. injection Hld as Hαδ'. exact Hαδ'. }
    subst δ.
    (* Hr2 : sys_rules S β α = Some r2; by symmetry of the rule table,
       sys_rules S β α = sys_rules S α β, so r2 = r1. *)
    rewrite (sys_sym S β α) in Hr2.
    rewrite Hr1 in Hr2.
    injection Hr2 as Hr12.
    subst r2.
    (* Hlhs2 : ru_lhs r1 = (β, α); with Hlhs1 : ru_lhs r1 = (α, β),
       this forces α = β, contradicting distinct_lhs. *)
    rewrite Hlhs1 in Hlhs2.
    injection Hlhs2 as Hαβ Hβα.
    exfalso.
    apply (Hdl α β r1 Hr1).
    rewrite Hlhs1. simpl.
    exact Hαβ. }
  (* ==================== Case 3: disjoint pairs ==================== *)
  - { (* Fire r1 then r2 (or r2 then r1); the two double splices are
         isomorphic by step_commuting. *)
    set (scN1 := sc_N1 A Ar N a b r1).
    set (scN2 := sc_N2 A Ar N c d r2).
    set (scN12 := sc_N12 A Ar N a b c d r1 r2).
    set (scN21 := sc_N21 A Ar N a b c d r1 r2).
    set (c' := @ni_map A Ar scN1 N1 Hiso1 c).
    set (d' := @ni_map A Ar scN1 N1 Hiso1 d).
    set (a' := @ni_map A Ar scN2 N2 Hiso2 a).
    set (b' := @ni_map A Ar scN2 N2 Hiso2 b).
    (* System validity of the two rules. *)
    assert (Hrhs1 : well_formed A Ar (ru_rhs r1)).
    { exact (sys_valid_wf A S α β r1 Hr1). }
    assert (Hiface1 : ru_iface r1 = interface A Ar (ru_rhs r1)).
    { exact (sys_valid_iface A S α β r1 Hr1). }
    assert (Hlen1_eq := sys_valid_len A S α β r1 Hr1).
    rewrite !Hlhs1 in Hlen1_eq. simpl in Hlen1_eq.
    (* Hlen1_eq : length (ru_iface r1) = Ar α + Ar β. *)
    assert (Hlen1_fst : length (ru_iface r1) = Ar (fst (ru_lhs r1)) + Ar (snd (ru_lhs r1))).
    { exact (sys_valid_len A S α β r1 Hr1). }
    assert (Hlen1_le : Ar (fst (ru_lhs r1)) + Ar (snd (ru_lhs r1)) <= length (ru_iface r1)).
    { rewrite Hlen1_fst. lia. }
    assert (Hrhs2 : well_formed A Ar (ru_rhs r2)).
    { exact (sys_valid_wf A S γ δ r2 Hr2). }
    assert (Hiface2 : ru_iface r2 = interface A Ar (ru_rhs r2)).
    { exact (sys_valid_iface A S γ δ r2 Hr2). }
    assert (Hlen2_fst : length (ru_iface r2) = Ar (fst (ru_lhs r2)) + Ar (snd (ru_lhs r2))).
    { exact (sys_valid_len A S γ δ r2 Hr2). }
    (* The LHS components of each rule. *)
    assert (Hf1 : fst (ru_lhs r1) = α). { rewrite Hlhs1. reflexivity. }
    assert (Hs1l : snd (ru_lhs r1) = β). { rewrite Hlhs1. reflexivity. }
    assert (Hf2 : fst (ru_lhs r2) = γ). { rewrite Hlhs2. reflexivity. }
    assert (Hs2l : snd (ru_lhs r2) = δ). { rewrite Hlhs2. reflexivity. }
    assert (Hlen2_γδ : length (ru_iface r2) = Ar γ + Ar δ).
    { rewrite Hf2, Hs2l in Hlen2_fst. exact Hlen2_fst. }
    (* Orientation premises for step_commuting. *)
    assert (Hol1 : agent_label A N a = Some (fst (ru_lhs r1))).
    { rewrite <- Hf1 in Hla. exact Hla. }
    assert (Hol2 : agent_label A N b = Some (snd (ru_lhs r1))).
    { rewrite <- Hs1l in Hlb. exact Hlb. }
    assert (Hol3 : agent_label A N c = Some (fst (ru_lhs r2))).
    { rewrite <- Hf2 in Hlc. exact Hlc. }
    assert (Hol4 : agent_label A N d = Some (snd (ru_lhs r2))).
    { rewrite <- Hs2l in Hld. exact Hld. }
    (* The single splices are well-formed. *)
    assert (Hwf_scN1 : well_formed A Ar scN1).
    { exact (raw_splice_wf A Ar N a b r1 α β Hla Hlb Hlhs1 Hwf Hap_ab Hrhs1 Hiface1 Hlen1_eq). }
    assert (Hwf_scN2 : well_formed A Ar scN2).
    { exact (raw_splice_wf A Ar N c d r2 γ δ Hlc Hld Hlhs2 Hwf Hap_cd Hrhs2 Hiface2 Hlen2_γδ). }
    (* The four agents of the two pairs, and the disjointness inequalities. *)
    assert (Ha : has_agent A N a).
    { change (a <> b /\ has_agent A N a /\ has_agent A N b /\ has_link A N (a, 0) (b, 0)) in Hap_ab.
      exact (proj1 (proj2 Hap_ab)). }
    assert (Hb : has_agent A N b).
    { change (a <> b /\ has_agent A N a /\ has_agent A N b /\ has_link A N (a, 0) (b, 0)) in Hap_ab.
      exact (proj1 (proj2 (proj2 Hap_ab))). }
    assert (Hc : has_agent A N c).
    { change (c <> d /\ has_agent A N c /\ has_agent A N d /\ has_link A N (c, 0) (d, 0)) in Hap_cd.
      exact (proj1 (proj2 Hap_cd)). }
    assert (Hd : has_agent A N d).
    { change (c <> d /\ has_agent A N c /\ has_agent A N d /\ has_link A N (c, 0) (d, 0)) in Hap_cd.
      exact (proj1 (proj2 (proj2 Hap_cd))). }
    assert (Hac : a <> c). { exact (proj1 Hdisj). }
    assert (Had : a <> d). { exact (proj1 (proj2 Hdisj)). }
    assert (Hbc : b <> c). { exact (proj1 (proj2 (proj2 Hdisj))). }
    assert (Hbd : b <> d). { exact (proj2 (proj2 (proj2 Hdisj))). }
    assert (Hca : c <> a). { intro H. apply Hac. symmetry. exact H. }
    assert (Hcb : c <> b). { intro H. apply Hbc. symmetry. exact H. }
    assert (Hda : d <> a). { intro H. apply Had. symmetry. exact H. }
    assert (Hdb : d <> b). { intro H. apply Hbd. symmetry. exact H. }
    (* The flipped disjointness, for firing (c, d) with survivors (a, b). *)
    assert (Hdisj2 : c <> a /\ c <> b /\ d <> a /\ d <> b).
    { split; [exact Hca | split; [exact Hcb | split; [exact Hda | exact Hdb]]]. }
    (* The surviving agents in the single splices. *)
    assert (Hc_scN1 : has_agent A scN1 c).
    { exact (raw_splice_pres_agent A Ar N a b c r1 Hc Hca Hcb). }
    assert (Hd_scN1 : has_agent A scN1 d).
    { exact (raw_splice_pres_agent A Ar N a b d r1 Hd Hda Hdb). }
    assert (Ha_scN2 : has_agent A scN2 a).
    { exact (raw_splice_pres_agent A Ar N c d a r2 Ha Hac Had). }
    assert (Hb_scN2 : has_agent A scN2 b).
    { exact (raw_splice_pres_agent A Ar N c d b r2 Hb Hbc Hbd). }
    (* The surviving labels in the single splices. *)
    assert (Hlc_scN1 : agent_label A scN1 c = Some (fst (ru_lhs r2))).
    { assert (Heq : agent_label A scN1 c = agent_label A N c).
      { exact (raw_splice_pres_label A Ar N Hwf a b c r1 Hc Hca Hcb). }
      rewrite Heq, Hlc.
      rewrite <- Hf2.
      reflexivity. }
    assert (Hld_scN1 : agent_label A scN1 d = Some (snd (ru_lhs r2))).
    { assert (Heq : agent_label A scN1 d = agent_label A N d).
      { exact (raw_splice_pres_label A Ar N Hwf a b d r1 Hd Hda Hdb). }
      rewrite Heq, Hld.
      rewrite <- Hs2l.
      reflexivity. }
    assert (Hla_scN2 : agent_label A scN2 a = Some (fst (ru_lhs r1))).
    { assert (Heq : agent_label A scN2 a = agent_label A N a).
      { exact (raw_splice_pres_label A Ar N Hwf c d a r2 Ha Hac Had). }
      rewrite Heq, Hla.
      rewrite <- Hf1.
      reflexivity. }
    assert (Hlb_scN2 : agent_label A scN2 b = Some (snd (ru_lhs r1))).
    { assert (Heq : agent_label A scN2 b = agent_label A N b).
      { exact (raw_splice_pres_label A Ar N Hwf c d b r2 Hb Hbc Hbd). }
      rewrite Heq, Hlb.
      rewrite <- Hs1l.
      reflexivity. }
    (* The other pair is still active in each single splice. *)
    assert (Hap_scN1 : is_active_pair A Ar scN1 c d).
    { exact (raw_splice_pres_pair A Ar N a b c d r1 Hwf Hap_ab Hap_cd Hdisj). }
    assert (Hap_scN2 : is_active_pair A Ar scN2 a b).
    { exact (raw_splice_pres_pair A Ar N c d a b r2 Hwf Hap_cd Hap_ab Hdisj2). }
    (* Reflexive LHS facts. *)
    assert (Hlhs1' : ru_lhs r1 = (fst (ru_lhs r1), snd (ru_lhs r1))).
    { rewrite Hf1, Hs1l, Hlhs1. reflexivity. }
    assert (Hlhs2' : ru_lhs r2 = (fst (ru_lhs r2), snd (ru_lhs r2))).
    { rewrite Hf2, Hs2l, Hlhs2. reflexivity. }
    (* The double splices are well-formed. *)
    assert (Hwf_scN12 : well_formed A Ar scN12).
    { exact (raw_splice_wf A Ar scN1 c d r2 (fst (ru_lhs r2)) (snd (ru_lhs r2))
             Hlc_scN1 Hld_scN1 Hlhs2' Hwf_scN1 Hap_scN1 Hrhs2 Hiface2 Hlen2_fst). }
    assert (Hwf_scN21 : well_formed A Ar scN21).
    { exact (raw_splice_wf A Ar scN2 a b r1 (fst (ru_lhs r1)) (snd (ru_lhs r1))
             Hla_scN2 Hlb_scN2 Hlhs1' Hwf_scN2 Hap_scN2 Hrhs1 Hiface1 Hlen1_fst). }
    (* ---- The step N1 -> scN12 (fire r2 on the image of c, d in N1) ---- *)
    assert (Hap_N1 : is_active_pair A Ar N1 c' d').
    { exact (step_preserves_pair A S N N1 a b c d r1 Hiso1 Hwf Hap_ab Hap_cd Hdisj). }
    assert (Hwf_N1 : well_formed A Ar N1).
    { exact (step_pres_wf A S N N1 Hs1). }
    assert (Hc_N1 : has_agent A N1 c').
    { unfold c'.
      exact (net_iso_agent_fwd A Ar scN1 N1 Hiso1 c Hc_scN1). }
    assert (Hd_N1 : has_agent A N1 d').
    { unfold d'.
      exact (net_iso_agent_fwd A Ar scN1 N1 Hiso1 d Hd_scN1). }
    assert (Hlc_N1 : agent_label A N1 c' = Some (fst (ru_lhs r2))).
    { unfold c'.
      assert (Heq : agent_label A N1 (@ni_map A Ar scN1 N1 Hiso1 c) = agent_label A scN1 c).
      { exact (net_iso_label A Ar scN1 N1 Hiso1 Hwf_scN1 c Hc_scN1). }
      rewrite Heq.
      exact Hlc_scN1. }
    assert (Hld_N1 : agent_label A N1 d' = Some (snd (ru_lhs r2))).
    { unfold d'.
      assert (Heq : agent_label A N1 (@ni_map A Ar scN1 N1 Hiso1 d) = agent_label A scN1 d).
      { exact (net_iso_label A Ar scN1 N1 Hiso1 Hwf_scN1 d Hd_scN1). }
      rewrite Heq.
      exact Hld_scN1. }
    assert (Hr2' : sys_rules S (fst (ru_lhs r2)) (snd (ru_lhs r2)) = Some r2).
    { rewrite <- Hf2, <- Hs2l in Hr2. exact Hr2. }
    assert (Hsp : net_iso A Ar scN12 (raw_splice A Ar N1 c' d' r2)).
    { exact (raw_splice_iso_compat A Ar scN1 N1 Hiso1 c d r2 Hc_scN1 Hd_scN1 Hwf_scN1). }
    assert (Hsp' : net_iso A Ar (raw_splice A Ar N1 c' d' r2) scN12).
    { exact (net_iso_symmetric A Ar scN12 (raw_splice A Ar N1 c' d' r2) Hsp Hwf_scN12). }
    assert (Hstep_N1 : step A S N1 scN12).
    { refine (step_intro A S N1 scN12 c' d' (fst (ru_lhs r2)) (snd (ru_lhs r2)) r2
             Hwf_N1 Hap_N1 Hlc_N1 Hld_N1 Hr2' Hlhs2' Hsp'). }
    (* ---- The step N2 -> scN21 (fire r1 on the image of a, b in N2) ---- *)
    assert (Hap_N2 : is_active_pair A Ar N2 a' b').
    { exact (step_preserves_pair A S N N2 c d a b r2 Hiso2 Hwf Hap_cd Hap_ab Hdisj2). }
    assert (Hwf_N2 : well_formed A Ar N2).
    { exact (step_pres_wf A S N N2 Hs2). }
    assert (Ha_N2 : has_agent A N2 a').
    { unfold a'.
      exact (net_iso_agent_fwd A Ar scN2 N2 Hiso2 a Ha_scN2). }
    assert (Hb_N2 : has_agent A N2 b').
    { unfold b'.
      exact (net_iso_agent_fwd A Ar scN2 N2 Hiso2 b Hb_scN2). }
    assert (Hla_N2 : agent_label A N2 a' = Some (fst (ru_lhs r1))).
    { unfold a'.
      assert (Heq : agent_label A N2 (@ni_map A Ar scN2 N2 Hiso2 a) = agent_label A scN2 a).
      { exact (net_iso_label A Ar scN2 N2 Hiso2 Hwf_scN2 a Ha_scN2). }
      rewrite Heq.
      exact Hla_scN2. }
    assert (Hlb_N2 : agent_label A N2 b' = Some (snd (ru_lhs r1))).
    { unfold b'.
      assert (Heq : agent_label A N2 (@ni_map A Ar scN2 N2 Hiso2 b) = agent_label A scN2 b).
      { exact (net_iso_label A Ar scN2 N2 Hiso2 Hwf_scN2 b Hb_scN2). }
      rewrite Heq.
      exact Hlb_scN2. }
    assert (Hr1' : sys_rules S (fst (ru_lhs r1)) (snd (ru_lhs r1)) = Some r1).
    { rewrite <- Hf1, <- Hs1l in Hr1. exact Hr1. }
    assert (Hsp2 : net_iso A Ar scN21 (raw_splice A Ar N2 a' b' r1)).
    { exact (raw_splice_iso_compat A Ar scN2 N2 Hiso2 a b r1 Ha_scN2 Hb_scN2 Hwf_scN2). }
    assert (Hsp2' : net_iso A Ar (raw_splice A Ar N2 a' b' r1) scN21).
    { exact (net_iso_symmetric A Ar scN21 (raw_splice A Ar N2 a' b' r1) Hsp2 Hwf_scN21). }
    assert (Hstep_N2 : step A S N2 scN21).
    { refine (step_intro A S N2 scN21 a' b' (fst (ru_lhs r1)) (snd (ru_lhs r1)) r1
             Hwf_N2 Hap_N2 Hla_N2 Hlb_N2 Hr1' Hlhs1' Hsp2'). }
    (* ---- The diamond: M = scN12; N2 reaches it via scN21 ≈ scN12 ---- *)
    exists scN12.
    split.
    - exact (inr (existT (fun M' : Net A => prod (step A S N1 M') (net_iso A Ar M' scN12))
             scN12 (pair Hstep_N1 (net_iso_reflexive A Ar scN12)))).
    - exact (inr (existT (fun M' : Net A => prod (step A S N2 M') (net_iso A Ar M' scN12))
             scN21 (pair Hstep_N2 (net_iso_symmetric A Ar scN12 scN21
               (step_commuting A Ar N a b c d r1 r2 Hwf Hap_ab Hap_cd Hdisj
                 Hrhs1 Hiface1 Hol1 Hol2 Hol3 Hol4 Hlen1_le)
               Hwf_scN12)))). }
Qed.

(** A concrete star sequence is in particular a star-up-to-iso sequence
    (matched by the identity renaming). *)
Lemma star_to_star_iso (A : Type) (S : System A) (N M : Net A)
      (Hstar : step_star A S N M) : step_star_iso A S N M.
Proof.
  exists M.
  exact (pair Hstar (net_iso_reflexive A (sys_arity S) M)).
Qed.

(** An isomorphism is in particular a star-up-to-iso sequence (the empty star,
    matched by the given renaming). *)
Lemma iso_to_star_iso (A : Type) (S : System A) (N M : Net A)
      (Hiso : net_iso A (sys_arity S) N M) : step_star_iso A S N M.
Proof.
  exists N.
  exact (pair (step_star_refl A S N) Hiso).
Qed.

(** A single step and a star sequence from the same net are joinable, up to
    renaming: if [N -> N1] and [N ->* N2], then some [M] is reachable (up to
    renaming) from both [N1] and [N2]. This is the peak lemma the confluence
    proof is built from. It is proved by induction on the star, using
    [diamond_atmost1] (the one-step diamond) so that the diamond yields a
    single [step] (or a mere iso) that the induction hypothesis can consume.

    The star is introduced before the step: the induction hypothesis must be
    polymorphic in the step's target, which requires the step to be a
    hypothesis at the point of the induction. *)
Lemma step_star_peak (A : Type) (S : System A) (Hdl : distinct_lhs A S) :
  forall N N2, step_star A S N N2 ->
    forall N1, step A S N N1 ->
      { M : Net A & step_star_iso A S N1 M * step_star_iso A S N2 M }.
Proof.
  set (Ar := sys_arity S).
  intros N N2 Hstar.
  induction Hstar as [N | N N' N2 Hstep Hstar IH].
  - (* Base: N2 = N. Take M = N1. *)
    intros N1 Hstep1.
    exists N1.
    split.
    + exists N1.
      exact (pair (step_star_refl A S N1) (net_iso_reflexive A Ar N1)).
    + exists N1.
      exact (pair (step_star_step A S N N1 Hstep1) (net_iso_reflexive A Ar N1)).
  - { (* Inductive: N -> N' ->* N2. *)
      intros N1 Hstep1.
      destruct (diamond_atmost1 A S Hdl N N1 N' Hstep1 Hstep) as [M [Ham1 Ham2]].
      destruct Ham2 as [Hiso | Hsig].
      - { (* N' ~= M (the diamond's zero-step case). *)
        assert (HwfN' : well_formed A Ar N').
        { exact (step_pres_wf A S N N' Hstep). }
        assert (HwfM : well_formed A Ar M).
        { exact (net_iso_pres_wf A Ar N' M Hiso HwfN'). }
        assert (HisoMN' : net_iso A Ar M N').
        { exact (net_iso_symmetric A Ar N' M Hiso HwfN'). }
        assert (HsMN2 : step_star_iso A S M N2).
        { exact (step_star_iso_trans A S M N' N2 HwfM
                 (iso_to_star_iso A S M N' HisoMN')
                 (star_to_star_iso A S N' N2 Hstar)). }
        assert (HsN1M : step_star_iso A S N1 M).
        { exact (atmost1_to_star_iso A S N1 M Ham1). }
        assert (HwfN1 : well_formed A Ar N1).
        { exact (step_pres_wf A S N N1 Hstep1). }
        assert (HsN1N2 : step_star_iso A S N1 N2).
        { exact (step_star_iso_trans A S N1 M N2 HwfN1 HsN1M HsMN2). }
        exists N2.
        split.
        + exact HsN1N2.
        + exists N2.
          exact (pair (step_star_refl A S N2) (net_iso_reflexive A Ar N2)). }
      - { (* N' -> M'' ~= M (the diamond's one-step case). *)
        destruct Hsig as [M'' [Hstep' Hiso]].
        destruct (IH M'' Hstep') as [K [HK1 HK2]].
        assert (HwfM'' : well_formed A Ar M'').
        { exact (step_pres_wf A S N' M'' Hstep'). }
        assert (HwfM : well_formed A Ar M).
        { exact (net_iso_pres_wf A Ar M'' M Hiso HwfM''). }
        assert (HisoMM'' : net_iso A Ar M M'').
        { exact (net_iso_symmetric A Ar M'' M Hiso HwfM''). }
        assert (HsMK : step_star_iso A S M K).
        { exact (step_star_iso_trans A S M M'' K HwfM
                 (iso_to_star_iso A S M M'' HisoMM'') HK1). }
        assert (HsN1M : step_star_iso A S N1 M).
        { exact (atmost1_to_star_iso A S N1 M Ham1). }
        assert (HwfN1 : well_formed A Ar N1).
        { exact (step_pres_wf A S N N1 Hstep1). }
        assert (HsN1K : step_star_iso A S N1 K).
        { exact (step_star_iso_trans A S N1 M K HwfN1 HsN1M HsMK). }
        exists K.
        split.
        + exact HsN1K.
        + exact HK2. } }
Qed.

(** Confluence (Church-Rosser), up to renaming: any two star sequences from
    the same net reach nets that have a common reduct (up to renaming). This
    is the 4.7 consequence of the diamond property.

    The binders are ordered so that the star the proof inducts on (the second
    one) is introduced first: the induction hypothesis must be polymorphic in
    the target of the OTHER star, which requires that star to be a hypothesis
    at the point of the induction (a binder in the goal cannot be). The
    inductive case moves the first star across the first step of the second
    via the step-vs-star peak lemma ([step_star_peak]) and then applies the
    induction hypothesis. *)
Theorem confluence (A : Type) (S : System A) (Hdl : distinct_lhs A S) :
  forall N N2, step_star A S N N2 ->
    forall N1, step_star A S N N1 ->
      { M : Net A & step_star_iso A S N1 M * step_star_iso A S N2 M }.
Proof.
  set (Ar := sys_arity S).
  intros N N2 Hstar2.
  induction Hstar2 as [N | N N' N2 Hstep Hstar2 IH].
  - (* Base: N2 = N. Take M = N1. *)
    intros N1 Hstar1.
    exists N1.
    split.
    + exists N1.
      exact (pair (step_star_refl A S N1) (net_iso_reflexive A Ar N1)).
    + exact (star_to_star_iso A S N N1 Hstar1).
  - (* Inductive: N -> N' ->* N2. *)
    intros N1 Hstar1.
    destruct (step_star_peak A S Hdl N N1 Hstar1 N' Hstep) as [M [HM' HM1]].
    destruct HM' as [M2 [HstarM2 Hiso2]].
    destruct (IH M2 HstarM2) as [K [HK1 HK2]].
    assert (HwfN : well_formed A Ar N).
    { exact (step_pres_wf_source A S N N' Hstep). }
    assert (HwfN1 : well_formed A Ar N1).
    { exact (step_star_pres_wf A S N N1 HwfN Hstar1). }
    assert (HwfM2 : well_formed A Ar M2).
    { exact (step_star_pres_wf A S N' M2 (step_pres_wf A S N N' Hstep) HstarM2). }
    assert (HisoMM2 : net_iso A Ar M M2).
    { exact (net_iso_symmetric A Ar M2 M Hiso2 HwfM2). }
    assert (HwfM : well_formed A Ar M).
    { exact (net_iso_pres_wf A Ar M2 M Hiso2 HwfM2). }
    assert (HsMK : step_star_iso A S M K).
    { exact (step_star_iso_trans A S M M2 K HwfM
               (iso_to_star_iso A S M M2 HisoMM2) HK1). }
    assert (HsN1K : step_star_iso A S N1 K).
    { exact (step_star_iso_trans A S N1 M K HwfN1 HM1 HsMK). }
    exists K.
    split.
    + exact HsN1K.
    + exact HK2.
Qed.

(** A star sequence out of a normal form is empty: a normal form has no
    outgoing step ([nf_no_step]), so the only way to star-reach [M] from [N]
    is the empty sequence, i.e. [M = N]. *)
Lemma star_from_nf_is_refl (A : Type) (S : System A) (N M : Net A)
      (Hnf : is_normal_form A (sys_arity S) N)
      (Hstar : step_star A S N M) : M = N.
Proof.
  induction Hstar as [N | N N' M Hstep Hstar IH].
  - subst. reflexivity.
  - exfalso.
    apply (nf_no_step A S N N' Hnf) in Hstep.
    exact Hstep.
Qed.

(** Unique normal forms (4.7(2)): if [N] normalizes to two normal forms [N1]
    and [N2], then [N1] and [N2] are isomorphic (equal up to renaming).
    Confluence gives a common reduct [M] (up to renaming); a normal form has
    no outgoing step, so the star from [N1] (resp. [N2]) to its witness is
    empty, forcing the witness to be [N1] (resp. [N2]) itself. Hence [N1] and
    [N2] are both isomorphic to [M], and therefore to each other.

    The starting net [N] is assumed well-formed: composing the two isomorphisms
    through [M] requires the symmetry of one of them, which in turn requires
    well-formedness. *)
Theorem nf_unique (A : Type) (S : System A) (Hdl : distinct_lhs A S)
      (N : Net A) (HwfN : well_formed A (sys_arity S) N) :
  forall N1 N2, step_star A S N N1 -> step_star A S N N2 ->
    is_normal_form A (sys_arity S) N1 -> is_normal_form A (sys_arity S) N2 ->
    net_iso A (sys_arity S) N1 N2.
Proof.
  set (Ar := sys_arity S).
  intros N1 N2 Hstar1 Hstar2 Hnf1 Hnf2.
  destruct (confluence A S Hdl N N2 Hstar2 N1 Hstar1) as [M [HM1 HM2]].
  destruct HM1 as [M1 [Hstar1' Hiso1]].
  destruct HM2 as [M2 [Hstar2' Hiso2]].
  assert (HM1eq : M1 = N1).
  { exact (star_from_nf_is_refl A S N1 M1 Hnf1 Hstar1'). }
  subst M1.
  assert (HM2eq : M2 = N2).
  { exact (star_from_nf_is_refl A S N2 M2 Hnf2 Hstar2'). }
  subst M2.
  (* Hiso1 : net_iso N1 M, Hiso2 : net_iso N2 M. Compose through M. *)
  assert (HwfN2 : well_formed A Ar N2).
  { exact (step_star_pres_wf A S N N2 HwfN Hstar2). }
  exact (net_iso_transitive A Ar N1 M N2 Hiso1
         (net_iso_symmetric A Ar N2 M Hiso2 HwfN2)).
Qed.

