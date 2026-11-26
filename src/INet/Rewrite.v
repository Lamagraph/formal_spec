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
    isomorphism class of the raw splice; [step_iso_compat_r] exploits this. *)
Inductive step (A : Type) (S : System A) : Net A -> Net A -> Prop :=
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
    rather than via [ReflTransCl], which is not available in this Stdlib. *)
Inductive step_star (A : Type) (S : System A) : Net A -> Net A -> Prop :=
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

(**************************************************************************)
(** ** Normal forms and normalizability *)

(** [is_normal_form A Ar N] holds when [N] contains no active (reducible)
    pair: no rule can fire on it (§4.6). *)
Definition is_normal_form (A : Type) (Ar : A -> nat) (N : Net A) : Prop :=
  forall a b, ~ is_active_pair A Ar N a b.

(** [normalizes_to A S N N'] holds when [N'] is a normal form reachable
    from [N] by a (possibly empty) sequence of steps of [S] (§4.6). *)
Definition normalizes_to (A : Type) (S : System A) (N N' : Net A) : Prop :=
  is_normal_form A (sys_arity S) N' /\ step_star A S N N'.

(** [is_normalizable A S N] holds when some normal form is reachable from
    [N] by a (possibly empty) sequence of steps of [S] (§4.6). *)
Definition is_normalizable (A : Type) (S : System A) (N : Net A) : Prop :=
  exists N', normalizes_to A S N N'.

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
  ~ step A S N N'.
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
  split.
  - exact Hnf.
  - exact (step_star_refl A S N).
Qed.

(** A normal form is normalizable (to itself). *)
Lemma is_normalizable_of_nf (A : Type) (S : System A) (N : Net A)
      (Hnf : is_normal_form A (sys_arity S) N) :
  is_normalizable A S N.
Proof.
  exists N.
  exact (normalizes_to_of_nf A S N Hnf).
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
