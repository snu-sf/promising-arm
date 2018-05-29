Require Import PArith.
Require Import ZArith.
Require Import Lia.
Require Import FunctionalExtensionality.
Require Import Classical.
Require Import ClassicalFacts.
Require Import Relations.
Require Import RelationClasses.
Require Import EquivDec.
Require Import List.
Require Import SetoidList.
Require Import Permutation.
Require Import sflib.
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
