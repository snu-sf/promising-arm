Require Import FunctionalExtensionality.
Require Import Relations.
Require Import RelationClasses.
Require Import EquivDec.
Require Import List.
Require Import sflib.

Set Implicit Arguments.


Ltac refl := reflexivity.
Ltac etrans := etransitivity.
Ltac antisym :=
  match goal with
  | [H: @PartialOrder ?A eq _ ?R _ |- (_:?A) = (_:?A)] =>
    apply (partial_order_antisym H)
  end.
Ltac funext := apply functional_extensionality.


Class orderC (A:Type) (R: relation A) (join: forall (a b:A), A) (bot: A) `{_: PartialOrder A eq R} := mk {
  join_l: forall a b, R a (join a b);
  join_r: forall a b, R b (join a b);
  join_assoc: forall a b c, join (join a b) c = join a (join b c);
  join_comm: forall a b, join a b = join b a;
  join_spec:
    forall a b c
      (AC: R a c)
      (BC: R b c),
      R (join a b) c;

  bot_spec: forall a, R bot a;
}.

Definition ifc (A:Type) `{_: orderC A} (cond:bool) (a:A): A :=
  if cond then a else bot.

Definition joins (A:Type) `{_: orderC A} (l:list A): A :=
  List.fold_right join bot l.


Lemma join_le (A:Type) (le:relation A) `{_: orderC A le}
      a b c d
      (AC: le a c)
      (BD: le b d):
  le (join a b) (join c d).
Proof.
  apply join_spec.
  - etrans; eauto using join_l.
  - etrans; eauto using join_r.
Qed.

Lemma bot_join (A:Type) (le: relation A) `{_: orderC A le}
      a:
  join a bot = a.
Proof.
  antisym.
  - eapply join_spec; eauto.
    + refl.
    + apply bot_spec.
  - eapply join_l.
Qed.

Lemma joins_le A (le: relation A) `{_: orderC A le}
      (a:A) (l:list A)
      (IN: In a l):
  le a (joins l).
Proof.
  revert IN. induction l; ss. i. des.
  - subst. apply join_l.
  - etrans; eauto. apply join_r.
Qed.

Lemma joins_spec A (le: relation A) `{_: orderC A le}
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


Definition le (A:Type) `{_: orderC A} := R.
Definition join (A:Type) `{_: orderC A} := join.
Definition bot (A:Type) `{_: orderC A} := bot.


Definition fun_add A B `{_: EqDec A} (a:A) (b:B) (f:A -> B): A -> B :=
  fun x => if a == x then b else f x.
Hint Unfold fun_add.

Lemma fun_add_spec A B `{_: EqDec A} a (b:B) f x:
  (fun_add a b f) x = if a == x then b else f x.
Proof. refl. Qed.

Definition fun_le A B `{_: orderC B} (f g: A -> B): Prop :=
  forall a, R (f a) (g a).
Hint Unfold fun_le.

Definition fun_join A B `{_: orderC B} (f g: A -> B) :=
  fun a => join (f a) (g a).
Hint Unfold fun_join.

Definition fun_bot A B `{_: orderC B} := fun (_:A) => bot.
Hint Unfold fun_bot.

Program Instance fun_preorder A B `{_: orderC B}: PreOrder (fun_le (A:=A) (B:=B)).
Next Obligation. ii. refl. Qed.
Next Obligation. ii. etrans; eauto. Qed.

Program Instance fun_partialorder A B `{_: orderC B}: PartialOrder eq (fun_le (A:=A) (B:=B)).
Next Obligation.
  econs.
  - i. subst. econs; ii; refl.
  - i. funext. i. inv H1. antisym; eauto.
Qed.

Program Instance fun_order A B `{_: orderC B}: @orderC (A -> B) (fun_le (A:=A) (B:=B)) (fun_join (A:=A) (B:=B)) (fun_bot (A:=A) (B:=B)) eq_equivalence (fun_preorder A B) (fun_partialorder A B).
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
  funext. i. eauto using join_assoc.
Qed.
Next Obligation.
  unfold fun_le, fun_join, fun_bot.
  funext. i. eauto using join_comm.
Qed.
Next Obligation.
  unfold fun_le, fun_join, fun_bot.
  eauto using join_spec.
Qed.
Next Obligation.
  unfold fun_le, fun_join, fun_bot.
  eauto using bot_spec.
Qed.


Inductive opt_le X `{_: orderC X}: forall (a b: option X), Prop :=
| opt_le_None b: opt_le None b
| opt_le_Some a b (LE: le a b): opt_le (Some a) (Some b)
.
Hint Constructors opt_le.

Definition opt_join X `{_: orderC X}(a b:option X) :=
  match a, b with
  | None, _ => b
  | _, None => a
  | Some a, Some b => Some (join a b)
  end.
Hint Unfold opt_join.

Definition opt_bot X `{_: orderC X}: option X := None.
Hint Unfold opt_bot.

Program Instance opt_eqdec X `{_: EqDec X eq}: EqDec (option X) eq.
Next Obligation.
  destruct x, y;
    (try by left);
    (try by right; i; ss).
  destruct (H x x0).
  - left. f_equal. ss.
  - right. intro Y. inv Y. intuition.
Defined.

Program Instance opt_preorder X `{_: orderC X}: PreOrder (opt_le (X:=X)).
Next Obligation. ii. destruct x; eauto. econs. refl. Qed.
Next Obligation. ii. inv H1; inv H2; eauto. econs. etrans; eauto. Qed.

Program Instance opt_partialorder X `{_: orderC X}: PartialOrder eq (opt_le (X:=X)).
Next Obligation.
  econs.
  - i. subst. econs; ii; refl.
  - i. inv H1. inv H2; inv H3; ss. f_equal. antisym; ss.
Qed.

Program Instance opt_order X `{_: orderC X}: @orderC (option X) (opt_le (X:=X)) (opt_join (X:=X)) (opt_bot (X:=X)) eq_equivalence (opt_preorder X) (opt_partialorder X).
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
  destruct  a, b, c; ss. f_equal. apply join_assoc.
Qed.
Next Obligation.
  destruct  a, b; ss. f_equal. apply join_comm.
Qed.
Next Obligation.
  inv AC; inv BC; econs; eauto. apply join_spec; ss.
Qed.
Next Obligation.
  econs.
Qed.


(* TODO: move *)

Definition proj_sumbool (P Q: Prop) (a: {P} + {Q}) : bool :=
  if a then true else false.

Arguments proj_sumbool [P Q].

Coercion proj_sumbool: sumbool >-> bool.
