Require Import PArith.
Require Import ZArith.
Require Import Lia.
Require Import FunctionalExtensionality.
Require Export Classical.
Require Import ClassicalFacts.
Require Import Relations.
Require Import RelationClasses.
Require Import EquivDec.
Require Import List.
Require Import SetoidList.
Require Import Permutation.
Require Import FMapPositive.
Require Import FSetPositive.
Require Import sflib.
Require Import paco.
Require Import HahnRelationsBasic.

Set Implicit Arguments.


Ltac refl := reflexivity.
Ltac congr := congruence.
Ltac etrans := etransitivity.
Ltac etrans' :=
  match goal with
  | [H: @PreOrder ?A ?R |- ?R (_:?A) (_:?A)] =>
    eapply (@PreOrder_Transitive _ _ H)
  end.
Ltac antisym :=
  match goal with
  | [H: @PartialOrder ?A ?EQ _ ?LE _ |- ?EQ (_:?A) (_:?A)] =>
    apply (partial_order_antisym H)
  end.
Ltac funext := apply functional_extensionality.
Axiom propext: prop_extensionality.
Ltac propext := apply propext.

Ltac condtac :=
  match goal with
  | [|- context[if ?c then _ else _]] =>
    let X := fresh "X" in
    destruct c eqn:X
  end.

Definition proj_sumbool (P Q: Prop) (a: {P} + {Q}) : bool :=
  if a then true else false.
Arguments proj_sumbool [P Q].
Coercion proj_sumbool: sumbool >-> bool.


Notation rtc := (clos_refl_trans_1n _). (* reflexive transitive closure *)
Notation rc := (clos_refl _). (* reflexive transitive closure *)
Notation tc := (clos_trans_1n _). (* transitive closure *)
Hint Immediate rt1n_refl rt1n_trans t1n_step.
Hint Resolve Relation_Operators.rt1n_trans.

Program Instance rtc_PreOrder A (R:A -> A -> Prop): PreOrder (rtc R).
Next Obligation.
  ii. revert H0. induction H; auto. i.
  exploit IHclos_refl_trans_1n; eauto.
Qed.

Lemma rtc_step_tc
      A a b c
      (rel:relation A)
      (AB: rtc rel a b)
      (BC: rel b c):
  tc rel a c.
Proof.
  revert c BC. induction AB.
  - i. econs. ss.
  - i. exploit IHAB; eauto. i.
    eapply Relation_Operators.t1n_trans; eauto.
Qed.

Lemma rtc_mon
      A (r1 r2:relation A)
      (LE: forall x y, r1 x y -> r2 x y):
  forall x y, rtc r1 x y -> rtc r2 x y.
Proof. i. induction H; eauto. Qed.


Inductive rtcn A (R: A -> A -> Prop): forall (n:nat) (a1 a2:A), Prop :=
| rtcn_nil
    a:
    rtcn R 0 a a
| rtcn_cons
    a1 a2 a3 n
    (A12: R a1 a2)
    (A23: rtcn R n a2 a3):
    rtcn R (S n) a1 a3
.
Hint Constructors rtcn.

Lemma rtcn_rtc A (R: A -> A -> Prop) n a1 a2
      (RTCN: rtcn R n a1 a2):
  rtc R a1 a2.
Proof.
  induction RTCN; auto. econs; eauto.
Qed.

Lemma rtc_rtcn A (R: A -> A -> Prop) a1 a2
      (RTC: rtc R a1 a2):
  exists n, rtcn R n a1 a2.
Proof.
  induction RTC; eauto. i. des.
  esplits; eauto.
Qed.

Lemma tc_rtcn A (R: A -> A -> Prop) a1 a2
      (TC: R⁺ a1 a2):
  exists n, rtcn R n a1 a2 /\ n > 0.
Proof.
  apply t_step_rt in TC. des. apply clos_rt_rt1n in TC0.
  apply rtc_rtcn in TC0. des. esplits; eauto. lia.
Qed.

Lemma rtcn_tc A (R: A -> A -> Prop) n a1 a2
      (RTCN: rtcn R n a1 a2)
      (N: n > 0):
  R⁺ a1 a2.
Proof.
  inv RTCN; [lia|]. apply t_step_rt. esplits; eauto.
  apply clos_rt1n_rt. eapply rtcn_rtc. eauto.
Qed.

Lemma rtcn_snoc A (R: A -> A -> Prop) n a1 a2 a3
      (RTCN: rtcn R n a1 a2)
      (REL: R a2 a3):
  rtcn R (S n) a1 a3.
Proof.
  revert a3 REL. induction RTCN; eauto.
Qed.

Lemma rtcn_app A (R: A -> A -> Prop) n1 n2 a1 a2 a3
      (RTCN1: rtcn R n1 a1 a2)
      (RTCN2: rtcn R n2 a2 a3):
  rtcn R (n1 + n2) a1 a3.
Proof.
  revert n1 a1 RTCN1. induction RTCN2.
  { i. rewrite Nat.add_0_r. ss. }
  i. exploit rtcn_snoc; try exact A12; eauto. i.
  exploit IHRTCN2; eauto. replace (n1 + S n) with (S n1 + n) by lia. ss.
Qed.

Lemma rtcn_inv A (R: A -> A -> Prop) n a1 a2
      (RTCN: rtcn R n a1 a2):
  rtcn (fun a b => R b a) n a2 a1.
Proof.
  induction RTCN; eauto. eapply rtcn_snoc; eauto.
Qed.

Lemma rtcn_imply
      A (R1 R2: A -> A -> Prop) n a1 a2
      (LE: R1 <2= R2)
      (RTCN: rtcn R1 n a1 a2):
  rtcn R2 n a1 a2.
Proof.
  induction RTCN; auto. econs; eauto.
Qed.


Inductive opt_pred A (pred: A -> Prop): forall (a:option A), Prop :=
| opt_pred_intro
    a
    (PRED: pred a):
    opt_pred pred (Some a)
.
Hint Constructors opt_pred.

Inductive opt_rel A B (rel: A -> B -> Prop): forall (a:option A) (b:option B), Prop :=
| opt_rel_None:
    opt_rel rel None None
| opt_rel_Some
    a b
    (REL: rel a b):
    opt_rel rel (Some a) (Some b)
.
Hint Constructors opt_rel.

Inductive opt_rel6 A B C D E F (rel6: A -> B -> C -> D -> E -> F -> Prop):
  forall (a: option A) (b: option B) (c: option C) (d: option D) (e: option E) (f: option F), Prop :=
| opt_rel6_None:
    opt_rel6 rel6 None None None None None None
| opt_rel6_Some
    a b c d e f
    (REL6: rel6 a b c d e f):
    opt_rel6 rel6 (Some a) (Some b) (Some c) (Some d) (Some e) (Some f)
.
Hint Constructors opt_rel6.


Fixpoint filter_map A B (f: A -> option B) (l: list A): list B :=
  match l with
  | [] => []
  | a::l =>
    match f a with
    | None => filter_map f l
    | Some b => b :: filter_map f l
    end
  end.

Lemma in_filter_map_iff A B (f: A -> option B) (l: list A) (b: B):
  List.In b (filter_map f l) <-> exists a, List.In a l /\ f a = Some b.
Proof.
  induction l; ss.
  { econs; i; des; ss. }
  destruct (f a) eqn:FA; ss.
  - rewrite IHl. intuition; des; subst; eauto.
    rewrite FA in H2. inv H2. auto.
  - rewrite IHl. intuition; des; subst; eauto. congr.
Qed.

Lemma filter_map_app A B (f: A -> option B) (l1 l2: list A):
  filter_map f (l1 ++ l2) = filter_map f l1 ++ filter_map f l2.
Proof.
  induction l1; ss. destruct (f a); ss. rewrite IHl1. ss.
Qed.

Lemma filter_map_in_length
      A B (f:A -> option B) (l:list A)
      a (IN: List.In a l) (FA: f a <> None):
  length (filter_map f l) <> 0.
Proof.
  revert IN. induction l; ss. i. des.
  - subst. destruct (f a); ss.
  - destruct (f a0); eauto. s. lia.
Qed.

Lemma nth_error_some A
      (l:list A) n a
      (SOME: nth_error l n = Some a):
  n < length l.
Proof.
  apply nth_error_Some. rewrite SOME. ss.
Qed.

Lemma nth_error_filter_map_inv A B
      f (l:list A) n (fa:B)
      (NTH: List.nth_error (filter_map f l) n = Some fa):
  exists m a,
    <<NTH: List.nth_error l m = Some a>> /\
    <<FA: f a = Some fa>> /\
    <<N: length (filter_map f (List.firstn (S m) l)) = S n>>.
Proof.
  revert n fa NTH. induction l; ss.
  { i. apply List.nth_error_In in NTH. inv NTH. }
  destruct (f a) eqn:FA.
  - destruct n; ss.
    + i. inv NTH. exists 0. esplits; ss.
    + i. exploit IHl; eauto. i. des.
      exists (S m). esplits; eauto.
  - i. exploit IHl; eauto. i. des.
    exists (S m). esplits; eauto.
Qed.

Lemma SetoidList_findA_rev
      (A B : Type) (eqA : A -> A -> Prop)
      (EQUIV: Equivalence eqA)
      (eqA_dec : forall x y : A, {eqA x y} + {~ eqA x y})
      (l : list (A * B))
      (a : A) (b : B)
      (NODUP: SetoidList.NoDupA (fun p p' : A * B => eqA (fst p) (fst p')) l):
  SetoidList.findA (fun a' : A => if eqA_dec a a' then true else false) l =
  SetoidList.findA (fun a' : A => if eqA_dec a a' then true else false) (List.rev l).
Proof.
  hexploit SetoidList.NoDupA_rev; try exact NODUP; [|i].
  { econs; ii.
    - refl.
    - symmetry. ss.
    - etrans; eauto.
  }

  match goal with
  | [|- ?f = _] => destruct f eqn:FIND
  end.
  { rewrite <- SetoidList.findA_NoDupA in FIND; ss.
    rewrite <- SetoidList.InA_rev in FIND.
    rewrite SetoidList.findA_NoDupA in FIND; ss.
    eauto.
  }

  match goal with
  | [|- _ = ?f] => destruct f eqn:FIND'
  end.
  { rewrite <- SetoidList.findA_NoDupA in FIND'; ss.
    rewrite SetoidList.InA_rev in FIND'.
    rewrite SetoidList.findA_NoDupA in FIND'; ss.
    rewrite FIND' in FIND. congr.
  }

  ss.
Qed.

Lemma List_nth_error_firstn
      A (l:list A) n m a
      (NTH: List.nth_error l n = Some a)
      (LE: n < m):
  List.nth_error (List.firstn m l) n = Some a.
Proof.
  revert n l a NTH LE. induction m; destruct n, l; ss.
  - i. lia.
  - i. lia.
  - i. exploit IHm; eauto. lia.
Qed.

Lemma List_firstn_S A
      (l:list A) n a
      (NTH: List.nth_error l n = Some a):
  List.firstn (S n) l = (List.firstn n l) ++ [a].
Proof.
  revert n a NTH. induction l; destruct n; ss.
  - i. inv NTH. ss.
  - i. erewrite IHl; ss.
Qed.

Lemma List_skipn_nil
      A n:
  @List.skipn A n [] = [].
Proof. induction n; ss. Qed.

Lemma List_firstn_le
      n m (LE: n <= m)
      A (l:list A):
  List.firstn m l = List.firstn n l ++ List.firstn (m - n) (List.skipn n l).
Proof.
  revert n m LE. induction l.
  { i. rewrite List_skipn_nil, ? List.firstn_nil. ss. }
  i. destruct m, n; ss.
  { lia. }
  erewrite IHl; ss. lia.
Qed.

Lemma List_nth_error_skipn
      A (l:list A) n m a
      (NTH: List.nth_error l n = Some a)
      (LE: m <= n):
  List.nth_error (List.skipn m l) (n - m) = Some a.
Proof.
  revert n l a NTH LE. induction m.
  { i. destruct n; ss. }
  i. destruct n, l; ss.
  - lia.
  - exploit IHm; eauto. lia.
Qed.

Lemma List_skipn_cons A
      (l:list A) n a
      (NTH: List.nth_error l n = Some a):
  List.skipn n l = a :: (List.skipn (S n) l).
Proof.
  revert n a NTH. induction l; destruct n; ss.
  - i. inv NTH. ss.
  - i. erewrite IHl; ss.
Qed.

Definition lastn A (n: nat) (l: list A) :=
  List.rev (List.firstn n (List.rev l)).

Lemma lastn_snoc A n (l:list A) x:
  lastn (S n) (l ++ [x]) = (lastn n l) ++ [x].
Proof.
  revert n. induction l using List.rev_ind; ss.
  unfold lastn. s. rewrite List.rev_app_distr. ss.
Qed.

Lemma lastn_cons A n a (l:list A)
      (N: n <= length l):
  lastn n (a::l) = lastn n l.
Proof.
  revert n N. induction l using List.rev_ind; ss.
  { i. destruct n; ss. unfold lastn. s. destruct n; lia. }
  i. destruct n; ss. rewrite List.app_comm_cons, ? lastn_snoc. f_equal.
  eapply IHl. rewrite List.app_length in N. ss. lia.
Qed.

Lemma lastn_one A
      (l: list A)
      (LENGTH: List.length l >= 1):
  exists a, lastn 1 l = [a].
Proof.
  destruct l using List.rev_ind; ss; [lia|]. rewrite lastn_snoc. s. eauto.
Qed.

Lemma lastn_all A n (l: list A)
      (N: n >= length l):
  lastn n l = l.
Proof.
  revert n N. induction l using List.rev_ind; ss.
  { destruct n; ss. }
  i. rewrite List.app_length in N. ss. destruct n; [lia|].
  rewrite lastn_snoc, IHl; ss. lia.
Qed.

Lemma lastn_length A n (l: list A):
  length (lastn n l) = min n (length l).
Proof.
  revert n. induction l using List.rev_ind; ss.
  { destruct n; ss. }
  i. destruct n; ss. rewrite lastn_snoc, ? List.app_length, IHl. s.
  rewrite (Nat.add_comm (length l)). s. lia.
Qed.

Lemma lastn_S A n (l: list A)
      (LENGTH: List.length l > 0):
  exists a l', lastn (S n) l = a :: l'.
Proof.
  generalize (lastn_length (S n) l). i.
  destruct (lastn (S n) l) eqn:LASTN; eauto.
  destruct l; ss. lia.
Qed.

Lemma lastn_S1 A
      (l: list A) n a l'
      (N: n < List.length l)
      (LASTN: lastn (S n) l = a :: l'):
  lastn n l = l'.
Proof.
  rewrite <- List.rev_length in N. apply List.nth_error_Some in N.
  destruct (List.nth_error (List.rev l) n) eqn:NTH; ss.
  revert LASTN. unfold lastn. erewrite List_firstn_S; eauto.
  rewrite List.rev_app_distr. s. i. inv LASTN. ss.
Qed.

Fixpoint List_find_pos A (pred:A -> bool) (l:list A): option nat :=
  match l with
  | [] => None
  | a::l =>
    if pred a
    then Some 0
    else option_map S (List_find_pos pred l)
  end.

Lemma List_find_pos_inv A pred (l:list A) n
      (POS: List_find_pos pred l = Some n):
  exists a,
    <<NTH: List.nth_error l n = Some a>> /\
    <<PRED: pred a>> /\
    <<NPRED: forall m b
               (M: m < n)
               (B: List.nth_error l m = Some b),
    ~ pred b>>.
Proof.
  revert n POS. induction l; ss.
  destruct (pred a) eqn:PA.
  - i. inv POS. esplits; ss. i. lia.
  - destruct ((List_find_pos pred l)) eqn:POS; ss. i. inv POS0.
    exploit IHl; eauto. i. des.
    esplits; eauto. i. destruct m; ss.
    + inv B. rewrite PA. ss.
    + eapply NPRED; eauto. lia.
Qed.

Lemma List_in_find_pos A `{_: EqDec A eq} a (l:list A)
      (IN: List.In a l):
  exists n, List_find_pos (fun a' => a' == a) l = Some n.
Proof.
  revert IN. induction l; ss. i. des.
  - subst. destruct (equiv_dec a a); [|congr]. s. eauto.
  - destruct (equiv_dec a0 a); s; eauto.
    specialize (IHl IN). des. rewrite IHl. s. eauto.
Qed.

Lemma List_nth_error_find_pos A `{_: EqDec A eq}
      (l:list A) n a
      (NTH: List.nth_error l n = Some a)
      (NODUP: List.NoDup l):
  List_find_pos (fun a' => a' == a) l = Some n.
Proof.
  revert n a NTH NODUP. induction l.
  { i. apply List.nth_error_In in NTH. inv NTH. }
  destruct n; s.
  - i. inv NTH. destruct (equiv_dec a0 a0); [|congr]. ss.
  - i. inv NODUP. exploit IHl; eauto. i. rewrite x.
    destruct (equiv_dec a a0); ss. inv e.
    contradict H2. eapply List.nth_error_In. eauto.
Qed.

Lemma nth_error_app_inv
      A
      (l1 l2:list A)
      n a
      (FIND: List.nth_error (l1 ++ l2) n = Some a):
  (n < length l1 /\ List.nth_error l1 n = Some a) \/
  (n >= length l1 /\ List.nth_error l2 (n - (length l1)) = Some a).
Proof.
  destruct (lt_dec n (length l1)).
  - left. splits; ss. rewrite List.nth_error_app1 in FIND; ss.
  - right. splits; [lia|]. rewrite List.nth_error_app2 in FIND; [|lia]. ss.
Qed.

Lemma nth_error_singleton_inv
      A
      n (a b:A)
      (FIND: List.nth_error [a] n = Some b):
  n = 0 /\ a = b.
Proof.
  destruct n; ss.
  - inv FIND. ss.
  - destruct n; ss.
Qed.

Lemma nth_error_snoc_inv
      A
      (l:list A) x
      n a
      (FIND: List.nth_error (l ++ [x]) n = Some a):
  (n < length l /\ List.nth_error l n = Some a) \/
  (n = length l /\ x = a).
Proof.
  exploit nth_error_app_inv; eauto. i. des; [left|right]; ss.
  exploit nth_error_singleton_inv; eauto. i. des. subst. splits; ss. lia.
Qed.

Lemma nth_error_snoc_inv_last
      A
      (l:list A) x
      a
      (FIND: List.nth_error (l ++ [x]) (length l) = Some a):
  x = a.
Proof.
  exploit nth_error_snoc_inv; eauto. i. des; ss. lia.
Qed.

Lemma nth_error_app_mon
      A
      (l1 l2:list A)
      n a
      (FIND: List.nth_error l1 n = Some a):
  List.nth_error (l1 ++ l2) n = Some a.
Proof.
  rewrite List.nth_error_app1; ss. apply List.nth_error_Some. congr.
Qed.


Lemma strong_nat_ind
      (P: nat -> Prop)
      (STEP: forall n, (forall m, m < n -> P m) -> P n):
  forall n, P n.
Proof.
  cut (forall n, forall m, m < n -> P m).
  { i. eapply H. eauto. }
  induction n; i; [lia|]. apply STEP. i. apply IHn. lia.
Qed.

Lemma partition A
      (l: list A)
      (pred: A -> Prop):
  exists l1 l2,
    Permutation (l1 ++ l2) l /\
    List.Forall pred l1 /\
    List.Forall (fun a => ~ (pred a)) l2.
Proof.
  induction l.
  { esplits; eauto. s. eauto. }
  des. destruct (classic (pred a)).
  - exists (a::l1), l2. esplits; eauto. s. econs. ss.
  - exists l1, (a::l2). esplits; eauto. rewrite <- Permutation_middle. econs. ss.
Qed.

Definition linearized A
           (rel:relation A)
           (l:list A): Prop :=
  forall i j x y
    (I: List.nth_error l i = Some x)
    (J: List.nth_error l j = Some y)
    (REL: rel x y),
    i < j.
Hint Unfold linearized.

Lemma linearize A
      (l: list A)
      (rel: relation A)
      (ACYCLIC: acyclic rel):
  exists l',
    <<PERM: Permutation l' l>> /\
    <<REL: linearized rel l'>>.
Proof.
  remember (length l) as n eqn:LEN. revert l LEN.
  induction n using strong_nat_ind. i. subst.
  destruct l.
  { esplits; eauto. ii. destruct i; ss. }
  generalize (partition l (fun b => rtc rel b a)). i. des.

  exploit (H (length l1)); ss.
  { erewrite <- (Permutation_length H0), List.app_length. lia. }
  i. des.

  exploit (H (length l2)); ss.
  { erewrite <- (Permutation_length H0), List.app_length. lia. }
  i. des.

  exists (l' ++ a :: l'0). esplits.
  { rewrite <- Permutation_middle. econs.
    rewrite Permutation_app; eauto.
  }
  rewrite List.Forall_forall in H1, H2. ii.
  destruct (Nat.compare_spec (length l') i), (Nat.compare_spec (length l') j);
    repeat (subst;
            match goal with
            | [X: List.nth_error (?l ++ _) (length ?l) = Some _ |- _] =>
              rewrite List.nth_error_app2 in X; ss
            | [X: List.nth_error (?l ++ _) ?i = Some _,
                  Y: ?i < length ?l |- _] =>
              rewrite List.nth_error_app1 in X; [|lia]
            | [X: List.nth_error (?l ++ _) ?i = Some _,
                  Y: length ?l < ?i |- _] =>
              rewrite List.nth_error_app2 in X; [|lia]
            | [X: List.nth_error (_ :: _) (?i - ?j) = Some _, Y: ?j < ?i |- _] =>
              let XX := fresh "XX" in
              hexploit Nat.sub_gt; try exact Y; eauto; i; destruct (i - j) eqn:XX
            | [X: context[?x - ?x] |- _] => rewrite Nat.sub_diag in X
            | [X: Some _ = Some _ |- _] => inv X
            end;
            ss).
  - exfalso. eapply ACYCLIC. econs. eauto.
  - hexploit H1.
    { eapply Permutation_in; eauto.
      eapply List.nth_error_In; eauto.
    }
    i. exfalso. eapply ACYCLIC. apply clos_t1n_trans.
    hexploit rtc_step_tc; eauto.
  - hexploit H2.
    { eapply Permutation_in; eauto.
      eapply List.nth_error_In; eauto.
    }
    i. contradict H5. econs; eauto.
  - exploit REL0; try exact REL1; eauto. lia.
  - hexploit H1.
    { eapply Permutation_in; eauto.
      eapply List.nth_error_In; eauto.
    }
    hexploit H2.
    { eapply Permutation_in; eauto.
      eapply List.nth_error_In; eauto.
    }
    i. contradict H6. etrans; eauto.
  - lia.
  - exploit REL; try exact REL1; eauto.
Qed.

Definition list_rev_list_rect
           (A:Type)
           (P:list A -> Type)
           (INIT: P [])
	         (STEP: forall (a:A) (l:list A), P (List.rev l) -> P (List.rev (a :: l))):
	forall l:list A, P (List.rev l).
Proof.
  induction l; auto.
Defined.

Definition list_rev_rect
           (A:Type)
           (P:list A -> Type)
           (INIT: P [])
           (STEP: forall x l, P l -> P (l ++ [x])):
  forall l, P l.
Proof.
  intros.
  generalize (List.rev_involutive l).
  intros E; rewrite <- E.
  apply (list_rev_list_rect P).
  auto.

  simpl.
  intros.
  apply (STEP a (List.rev l0)).
  auto.
Defined.

Instance Pos_eqdec: EqDec positive eq := Pos.eq_dec.
Instance Z_eqdec: EqDec Z eq := Z.eq_dec.

Module Id := Pos.

Module IdMap.
  Include PositiveMap.

  Lemma add_spec
        A id' id (a:A) am:
    find id' (add id a am) =
    if id' == id
    then Some a
    else find id' am.
  Proof.
    erewrite PositiveMapAdditionalFacts.gsspec; eauto.
    repeat condtac; ss.
  Qed.

  Lemma map_spec
        A B (f: A -> B) am id:
    find id (map f am) = option_map f (find id am).
  Proof.
    destruct (find id am) eqn:FIND; s.
    - eapply map_1 in FIND; eauto.
    - destruct (find id (map f am)) eqn:FIND'; ss.
      exploit map_2; [by econs; eauto|].
      intro X. inv X. congr.
  Qed.

  Lemma mapi_spec
        A B (f: key -> A -> B) am id:
    find id (mapi f am) = option_map (f id) (find id am).
  Proof.
    destruct (find id am) eqn:FIND; s.
    - eapply mapi_1 in FIND; eauto. des.
      inv FIND. inv FIND0. eauto.
    - destruct (find id (mapi f am)) eqn:FIND'; ss.
      exploit mapi_2; [by econs; eauto|].
      intro X. inv X. congr.
  Qed.

  Lemma elements_spec A id (am:t A):
    find id am = SetoidList.findA (fun id' => if id == id' then true else false) (elements am).
  Proof.
    generalize (elements_3w am).
    destruct (find id am) eqn:FIND.
    - apply elements_correct in FIND. revert FIND.
      induction (elements am); ss. i. des.
      + subst. destruct (equiv_dec id id); ss. congr.
      + destruct a0; ss. inv H. rewrite <- IHl; eauto.
        destruct (equiv_dec id k); ss. inv e.
        exfalso. apply H2. apply SetoidList.InA_alt. esplits; eauto. econs.
    - match goal with
      | [|- context[_ = ?f]] => destruct f eqn:FIND'
      end; ss.
      i. eapply SetoidList.findA_NoDupA in FIND'; eauto; cycle 1.
      { apply eq_equivalence. }
      apply elements_2 in FIND'. congr.
  Qed.

  Lemma mapi_mapi
        A B C
        (f: Id.t -> A -> B)
        (g: Id.t -> B -> C)
        m:
    mapi g (mapi f m) = mapi (fun tid a => g tid (f tid a)) m.
  Proof.
    unfold mapi. generalize 1%positive. induction m; ss.
    i. rewrite IHm1, IHm2. f_equal. destruct o; ss.
  Qed.

  Lemma add_add A i v1 v2 (m:t A):
    add i v1 (add i v2 m) = add i v1 m.
  Proof.
    revert m. induction i; destruct m; ss; try congruence.
  Qed.

  Lemma add_add_diff A i j v1 v2 (m:t A) (DIFF: i <> j):
    add i v1 (add j v2 m) = add j v2 (add i v1 m).
  Proof.
    revert j m DIFF. induction i; destruct j, m; ss; try congruence.
    - i. f_equal. apply IHi. contradict DIFF. congr.
    - i. f_equal. apply IHi. contradict DIFF. congr.
    - i. f_equal. apply IHi. contradict DIFF. congr.
    - i. f_equal. apply IHi. contradict DIFF. congr.
  Qed.

  Definition Forall2 A B
             (rel: Id.t -> A -> B -> Prop)
             (a: t A)
             (b: t B)
    : Prop :=
    forall id, opt_rel (rel id) (find id a) (find id b).

  Definition Forall6 A B C D E F
             (rel6: Id.t -> A -> B -> C -> D -> E -> F -> Prop)
             (a: t A)
             (b: t B)
             (c: t C)
             (d: t D)
             (e: t E)
             (f: t F)
    : Prop :=
    forall id, opt_rel6 (rel6 id) (find id a) (find id b) (find id c) (find id d) (find id e) (find id f).

  Definition Forall A
             (pred: Id.t -> A -> Prop)
             (m: t A)
    : Prop :=
    forall id a (FIND: find id m = Some a),
      pred id a.

  Inductive interleaving A (m:t (list A)): forall (l:list A), Prop :=
  | interleaving_nil
      (NIL: Forall (fun _ l => l = []) m):
      interleaving m []
  | interleaving_cons
      id a l res
      (FIND: find id m = Some (a::l))
      (INTERLEAVING: interleaving (add id l m) res):
      interleaving m (a::res)
  .
End IdMap.

Module IdSet.
  Include PositiveSet.

  Lemma add_o x' x s:
    mem x' (add x s) =
    if x' == x
    then true
    else mem x' s.
  Proof.
    destruct (equiv_dec x' x).
    - inv e. apply mem_1. apply add_spec. intuition.
    - destruct (mem x' s) eqn:MEM.
      + apply mem_1. apply add_spec. intuition.
      + destruct (mem x' (add x s)) eqn:MEM'; ss.
        apply mem_1 in MEM'. apply add_spec in MEM'. des; intuition.
        apply mem_1 in MEM'. eauto.
  Qed.

  Lemma remove_o x' x s:
    mem x' (remove x s) =
    if x' == x
    then false
    else mem x' s.
  Proof.
    destruct (equiv_dec x' x).
    - inv e. destruct (mem x (remove x s)) eqn:MEM; ss.
      apply remove_spec in MEM. des; ss.
    - destruct (mem x' s) eqn:MEM.
      + apply mem_1. apply remove_spec. intuition.
      + destruct (mem x' (remove x s)) eqn:MEM'; ss.
        apply mem_1 in MEM'. apply remove_spec in MEM'. des.
        apply mem_1 in MEM'0. eauto.
  Qed.
End IdSet.
