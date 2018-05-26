Require Import PArith.
Require Import ZArith.
Require Import Lia.
Require Import FunctionalExtensionality.
Require Import ClassicalFacts.
Require Import Relations.
Require Import RelationClasses.
Require Import EquivDec.
Require Import List.
Require Import SetoidList.
Require Import sflib.

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

Lemma List_in_filter_length
      A (f:A -> bool) (l:list A)
      a (IN: List.In a l) (FA: f a):
  length (List.filter f l) <> 0.
Proof.
  revert IN. induction l; ss. i. des.
  - subst. rewrite FA. s. lia.
  - destruct (f a0); eauto. s. lia.
Qed.
