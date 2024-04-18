Require Import PArith.
Require Import ZArith.
Require Import FunctionalExtensionality.
Require Import ClassicalFacts.
Require Import Relations.
Require Import RelationClasses.
Require Import EquivDec.
Require Import List.
From sflib Require Import sflib.

Require Import PromisingArch.lib.Basic.

Set Implicit Arguments.


Class orderC (A:Type) (EQ LE: relation A) (join: forall (a b:A), A) (bot: A) `{_: PartialOrder A EQ LE} := mk {
  join_l: forall a b, LE a (join a b);
  join_r: forall a b, LE b (join a b);
  join_assoc: forall a b c, EQ (join (join a b) c) (join a (join b c));
  join_comm: forall a b, EQ (join a b) (join b a);
  join_spec:
    forall a b c
      (AC: LE a c)
      (BC: LE b c),
      LE (join a b) c;

  bot_spec: forall a, LE bot a;
}.

Definition ifc (A:Type) `{_: orderC A} (cond:bool) (a:A): A :=
  if cond then a else bot.

Definition joins (A:Type) `{_: orderC A} (l:list A): A :=
  List.fold_right join bot l.


Lemma join_le (A:Type) (eq le:relation A) `{_: orderC A eq le}
      a b c d
      (AC: le a c)
      (BD: le b d):
  le (join a b) (join c d).
Proof.
  apply join_spec.
  - etrans; eauto using join_l.
  - etrans; eauto using join_r.
Qed.

Lemma bot_join (A:Type) (eq le: relation A) `{_: orderC A eq le}
      a:
  eq (join a bot) a.
Proof.
  antisym.
  - eapply join_spec; eauto.
    + refl.
    + apply bot_spec.
  - eapply join_l.
Qed.

Lemma joins_le A (eq le: relation A) `{_: orderC A eq le}
      (a:A) (l:list A)
      (IN: In a l):
  le a (joins l).
Proof.
  revert IN. induction l; ss. i. des.
  - subst. apply join_l.
  - etrans; eauto. apply join_r.
Qed.

Lemma joins_spec A (eq le: relation A) `{_: orderC A eq le}
      (l:list A) (b:A)
      (LE: forall a (IN: In a l), le a b):
  le (joins l) b.
Proof.
  revert LE. induction l; ss.
  { i. apply bot_spec. }
  i. apply join_spec.
  - apply LE. left. ss.
  - apply IHl. auto.
Qed.


Definition equiv (A:Type) `{_: Equivalence A} := R.
Definition le (A:Type) `{_: orderC A} := LE.
Definition join (A:Type) `{_: orderC A} := join.
Definition bot (A:Type) `{_: orderC A} := bot.


Definition fun_add A B `{_: EqDec A} (a:A) (b:B) (f:A -> B): A -> B :=
  fun x => if x == a then b else f x.
#[export]
Hint Unfold fun_add: core.

Lemma fun_add_spec A B `{_: EqDec A} a (b:B) f x:
  (fun_add a b f) x = if x == a then b else f x.
Proof. refl. Qed.

Definition fun_eq A B `{_: Equivalence B} (f g: A -> B): Prop :=
  forall a, R (f a) (g a).
#[export]
Hint Unfold fun_eq: core.

Definition fun_le A B `{_: orderC B} (f g: A -> B): Prop :=
  forall a, LE (f a) (g a).
#[export]
Hint Unfold fun_le: core.

Definition fun_join A B `{_: orderC B} (f g: A -> B) :=
  fun a => join (f a) (g a).
#[export]
Hint Unfold fun_join: core.

Definition fun_bot A B `{_: orderC B} := fun (_:A) => bot.
#[export]
Hint Unfold fun_bot: core.

#[export]
Program Instance fun_equiv A B `{_: Equivalence B}: Equivalence (fun_eq (A:=A) (B:=B)).
Next Obligation. ii. refl. Qed.
Next Obligation. ii. symmetry. ss. Qed.
Next Obligation. ii. etrans; eauto. Qed.

#[export]
Program Instance fun_preorder A B `{_: orderC B}: PreOrder (fun_le (A:=A) (B:=B)).
Next Obligation. ii. refl. Qed.
Next Obligation. ii. etrans; eauto. Qed.

#[export]
Program Instance fun_partialorder A B `{_: orderC B}: @PartialOrder (A -> B) (fun_eq (A:=A) (B:=B)) _ (fun_le (A:=A) (B:=B)) _.
Next Obligation.
  econs.
  - econs; ii.
    + eapply (H (x a)) in H1. inv H1. ss.
    + eapply (H (x a)) in H1. inv H1. ss.
  - ii. antisym; apply H1.
Qed.

#[export]
Program Instance fun_order A B `{_: orderC B}:
  @orderC
    (A -> B)
    (fun_eq (A:=A) (B:=B))
    (fun_le (A:=A) (B:=B))
    (fun_join (A:=A) (B:=B))
    (fun_bot (A:=A) (B:=B))
    (fun_equiv A)
    (fun_preorder A)
    (fun_partialorder (A:=A) (B:=B)).
Next Obligation.
  unfold fun_le, fun_join, fun_bot.
  ii. apply join_l.
Qed.
Next Obligation.
  unfold fun_le, fun_join, fun_bot.
  ii. apply join_r.
Qed.
Next Obligation.
  unfold fun_eq, fun_le, fun_join, fun_bot.
  i. eauto using join_assoc.
Qed.
Next Obligation.
  unfold fun_eq, fun_le, fun_join, fun_bot.
  i. eauto using join_comm.
Qed.
Next Obligation.
  unfold fun_eq, fun_le, fun_join, fun_bot.
  eauto using join_spec.
Qed.
Next Obligation.
  unfold fun_eq, fun_le, fun_join, fun_bot.
  eauto using bot_spec.
Qed.

#[export]
Program Instance fun_eq_partialorder A B `{_: orderC B eq}: @PartialOrder (A -> B) eq _ (fun_le (A:=A) (B:=B)) _.
Next Obligation.
  econs.
  - i. subst. econs; refl.
  - i. funext. i. antisym; apply H1.
Qed.

#[export]
Program Instance fun_eq_order A B `{_: orderC B eq}:
  @orderC
    (A -> B)
    eq
    (fun_le (A:=A) (B:=B))
    (fun_join (A:=A) (B:=B))
    (fun_bot (A:=A) (B:=B))
    eq_equivalence
    (fun_preorder A)
    (fun_eq_partialorder (A:=A) (B:=B)).
Next Obligation.
  unfold fun_le, fun_join, fun_bot.
  ii. apply join_l.
Qed.
Next Obligation.
  unfold fun_le, fun_join, fun_bot.
  ii. apply join_r.
Qed.
Next Obligation.
  unfold fun_le, fun_join, fun_bot.
  funext. eauto using join_assoc.
Qed.
Next Obligation.
  unfold fun_le, fun_join, fun_bot.
  funext. eauto using join_comm.
Qed.
Next Obligation.
  unfold fun_le, fun_join.
  eauto using join_spec.
Qed.
Next Obligation.
  unfold fun_le, fun_join, fun_bot.
  eauto using bot_spec.
Qed.

Inductive opt_eq X `{_: Equivalence X}: forall (a b: option X), Prop :=
| opt_eq_None: opt_eq None None
| opt_eq_Some a b (EQX: equiv a b): opt_eq (Some a) (Some b)
.
#[export]
Hint Constructors opt_eq: core.

Inductive opt_le X `{_: orderC X}: forall (a b: option X), Prop :=
| opt_le_None b: opt_le None b
| opt_le_Some a b (LEX: le a b): opt_le (Some a) (Some b)
.
#[export]
Hint Constructors opt_le: core.

Definition opt_join X `{_: orderC X}(a b:option X) :=
  match a, b with
  | None, _ => b
  | _, None => a
  | Some a, Some b => Some (join a b)
  end.
#[export]
Hint Unfold opt_join: core.

Definition opt_bot X `{_: orderC X}: option X := None.
#[export]
Hint Unfold opt_bot: core.

#[export]
Program Instance opt_equiv X `{_: Equivalence X}: Equivalence (opt_eq (X:=X)).
Next Obligation. ii. destruct x; eauto. econs. refl. Qed.
Next Obligation. ii. inv H0; eauto. econs. symmetry. ss. Qed.
Next Obligation. ii. inv H0; inv H1; eauto. econs. etrans; eauto. Qed.

#[export]
Program Instance opt_eqdec X `{_: EqDec X eq}: EqDec (option X) eq.
Next Obligation.
  destruct x, y;
    (try by left);
    (try by right; i; ss).
  destruct (H x x0).
  - left. f_equal. ss.
  - right. intro Y. inv Y. intuition.
Defined.

#[export]
Program Instance opt_preorder X `{_: orderC X}: PreOrder (opt_le (X:=X)).
Next Obligation. ii. destruct x; eauto. econs. refl. Qed.
Next Obligation. ii. inv H1; inv H2; eauto. econs. etrans; eauto. Qed.

#[export]
Program Instance opt_partialorder X `{_: orderC X}: PartialOrder (opt_eq (X:=X)) (opt_le (X:=X)).
Next Obligation.
  econs.
  - i. inv H1.
    + econs; ss.
    + econs; econs; rewrite EQX; refl.
  - i. inv H1. inv H2; inv H3; econs. antisym; eauto.
Qed.

#[export]
Program Instance opt_order X `{_: orderC X}:
  @orderC
    (option X)
    (opt_eq (X:=X))
    (opt_le (X:=X))
    (opt_join (X:=X))
    (opt_bot (X:=X))
    (opt_equiv)
    (opt_preorder)
    (opt_partialorder (X:=X)).
Next Obligation.
  destruct a, b; ss; econs.
  - apply join_l.
  - refl.
Qed.
Next Obligation.
  destruct a, b; ss; econs.
  - apply join_r.
  - refl.
Qed.
Next Obligation.
  destruct  a, b, c; econs; try by refl.
  apply join_assoc.
Qed.
Next Obligation.
  destruct  a, b; econs; try by refl.
  apply join_comm.
Qed.
Next Obligation.
  inv AC; inv BC; econs; eauto. apply join_spec; ss.
Qed.


Definition prop_le (a b:Prop): Prop := a -> b.

Definition prop_join (a b:Prop): Prop := a \/ b.

Definition prop_bot: Prop := False.

#[export]
Program Instance prop_preorder: PreOrder prop_le.
Next Obligation. ii. ss. Qed.
Next Obligation. ii. auto. Qed.

#[export]
Program Instance prop_partialorder: PartialOrder eq prop_le.
Next Obligation.
  econs.
  - i. inv H. econs; ss.
  - i. inv H. propext. econs; eauto.
Qed.

#[export]
Program Instance prop_order:
  @orderC
    Prop
    eq
    prop_le
    prop_join
    prop_bot
    eq_equivalence
    prop_preorder
    prop_partialorder.
Next Obligation.
  unfold prop_le, prop_join, prop_bot in *.
  intuition.
Qed.
Next Obligation.
  unfold prop_le, prop_join, prop_bot in *.
  intuition.
Qed.
Next Obligation.
  unfold prop_le, prop_join, prop_bot in *.
  propext. intuition.
Qed.
Next Obligation.
  unfold prop_le, prop_join, prop_bot in *.
  propext. intuition.
Qed.
Next Obligation.
  unfold prop_le, prop_join, prop_bot in *.
  intuition.
Qed.
Next Obligation.
  unfold prop_le, prop_join, prop_bot in *.
  intuition.
Qed.


Definition bool_le (a b:bool): Prop := a -> b.

Definition bool_join (a b:bool): bool := a || b.

Definition bool_bot: bool := false.

#[export]
Program Instance bool_preorder: PreOrder bool_le.
Next Obligation. ii. ss. Qed.
Next Obligation. ii. auto. Qed.

#[export]
Program Instance bool_partialorder: PartialOrder eq bool_le.
Next Obligation.
  unfold bool_le in *.
  econs.
  - i. inv H. econs; ss.
  - i. inv H. destruct x, x0; intuition.
Qed.

#[export]
Program Instance bool_order:
  @orderC
    bool
    eq
    bool_le
    bool_join
    bool_bot
    eq_equivalence
    bool_preorder
    bool_partialorder.
Next Obligation.
  unfold bool_le, bool_join, bool_bot in *.
  destruct a, b; intuition.
Qed.
Next Obligation.
  unfold bool_le, bool_join, bool_bot in *.
  destruct a, b; intuition.
Qed.
Next Obligation.
  unfold bool_le, bool_join, bool_bot in *.
  destruct a, b, c; intuition.
Qed.
Next Obligation.
  unfold bool_le, bool_join, bool_bot in *.
  destruct a, b; intuition.
Qed.
Next Obligation.
  unfold bool_le, bool_join, bool_bot in *.
  destruct a, b, c; intuition.
Qed.


Definition unit_le (a b:unit): Prop := True.

Definition unit_join (a b:unit): unit := tt.

Definition unit_bot: unit := tt.

#[export]
Program Instance unit_preorder: PreOrder unit_le.
Next Obligation. ii. ss. Qed.

#[export]
Program Instance unit_partialorder: PartialOrder eq unit_le.
Next Obligation.
  ii. econs; ss. destruct x, x0; ss.
Qed.

#[export]
Program Instance unit_order:
  @orderC
    unit
    eq
    unit_le
    unit_join
    unit_bot
    eq_equivalence
    unit_preorder
    unit_partialorder.
Next Obligation.
  unfold unit_le, unit_join, unit_bot in *.
  destruct a, b; intuition.
Qed.
Next Obligation.
  unfold unit_le, unit_join, unit_bot in *.
  destruct a, b; intuition.
Qed.
Next Obligation.
  unfold unit_le, unit_join, unit_bot in *.
  ss.
Qed.
