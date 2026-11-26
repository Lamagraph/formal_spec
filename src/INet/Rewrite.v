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
