Require Import Nat.
Require Import NArith.
Require Import PArith.
Require Import Lia.
Require Import FMapPositive.
Require Import FSetPositive.
Require Import Relations.
Require Import RelationClasses.
Require Import EquivDec.

Require Import sflib.

Set Implicit Arguments.


Require Import FunctionalExtensionality.

(* TODO: move *)
Ltac refl := reflexivity.
Ltac etrans := etransitivity.
Ltac antisym :=
  match goal with
  | [H: @PartialOrder ?A eq _ ?R _ |- (_:?A) = (_:?A)] =>
    apply (partial_order_antisym H)
  end.
Ltac funext := apply functional_extensionality.

Module Order.
  Class t (A:Type) (R: relation A) (join: forall (a b:A), A) (bot: A) `{_: PartialOrder A eq R} := mk {
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

  Lemma join_le (A:Type) (le:relation A) `{_: t A le}
       a b c d
       (AC: le a c)
       (BD: le b d):
    le (join a b) (join c d).
  Proof.
    apply join_spec.
    - etrans; eauto using join_l.
    - etrans; eauto using join_r.
  Qed.

  Lemma bot_join (A:Type) (le: relation A) `{_: t A le}
        a:
    join a bot = a.
  Proof.
    antisym.
    - eapply join_spec; eauto.
      + refl.
      + apply bot_spec.
    - eapply join_l.
  Qed.

  Definition le (A:Type) `{_: t A} := R.
  Definition join (A:Type) `{_: t A} := join.
  Definition bot (A:Type) `{_: t A} := bot.
  Definition bot_unless (A:Type) `{_: t A} (cond:bool) (a:A): A :=
    if cond then a else bot.
End Order.


Definition fun_add A B `{_: EqDec A} (a:A) (b:B) (f:A -> B): A -> B :=
  fun x => if a == x then b else f x.
Hint Unfold fun_add.

Lemma fun_add_spec A B `{_: EqDec A} a (b:B) f x:
  (fun_add a b f) x = if a == x then b else f x.
Proof. refl. Qed.

Definition fun_le A B `{BOrd: Order.t B} (f g: A -> B): Prop :=
  forall a, R (f a) (g a).
Hint Unfold fun_le.

Definition fun_join A B `{_: Order.t B} (f g: A -> B) :=
  fun a => join (f a) (g a).
Hint Unfold fun_join.

Definition fun_bot A B `{_: Order.t B} := fun (_:A) => bot.
Hint Unfold fun_bot.

Program Instance fun_preorder A B `{BOrd: Order.t B}: PreOrder (fun_le (A:=A) (B:=B)).
Next Obligation. ii. refl. Qed.
Next Obligation. ii. etrans; eauto. Qed.

Program Instance fun_partialorder A B `{BOrd: Order.t B}: PartialOrder eq (fun_le (A:=A) (B:=B)).
Next Obligation.
  econs.
  - i. subst. econs; ii; refl.
  - i. funext. i. inv H0. antisym; eauto.
Qed.

Program Instance fun_order A B `{BOrd: Order.t B}: @Order.t (A -> B) (fun_le (A:=A) (B:=B)) (fun_join (A:=A) (B:=B)) (fun_bot (A:=A) (B:=B)) eq_equivalence (fun_preorder A B) (fun_partialorder A B).
Next Obligation.
  unfold fun_le, fun_join, fun_bot.
  ii. apply Order.join_l.
Qed.
Next Obligation.
  unfold fun_le, fun_join, fun_bot.
  ii. apply Order.join_r.
Qed.
Next Obligation.
  unfold fun_le, fun_join, fun_bot.
  funext. i. eauto using Order.join_assoc.
Qed.
Next Obligation.
  unfold fun_le, fun_join, fun_bot.
  funext. i. eauto using Order.join_comm.
Qed.
Next Obligation.
  unfold fun_le, fun_join, fun_bot.
  eauto using Order.join_spec.
Qed.
Next Obligation.
  unfold fun_le, fun_join, fun_bot.
  eauto using Order.bot_spec.
Qed.

Module Time.
  Include Nat.

  Definition le (a b:t) := le a b.
  Definition join (a b:t) := max a b.
  Definition bot: t := 0.

  Program Instance order: Order.t join bot.
  Next Obligation. unfold join. lia. Qed.
  Next Obligation. unfold join. lia. Qed.
  Next Obligation. eauto using Max.max_assoc. Qed.
  Next Obligation. eauto using Max.max_comm. Qed.
  Next Obligation. unfold join. lia. Qed.
  Next Obligation. unfold bot. lia. Qed.
End Time.

Module Id := Pos.
Module IdMap := PositiveMap.
Module IdSet := PositiveSet.

Module View := Time.

Module Val := Nat.
Module Loc := Val.

Module Msg.
  Inductive t: Type := mk {
    loc: Loc.t;
    val: Val.t;
    tid: Id.t;
  }.
  Hint Constructors t.
End Msg.

Module Memory.
  Definition t := list Msg.t.

  Definition latest (mem:t) (loc:Loc.t) (view:View.t): Time.t := Order.bot. (* TODO *)
End Memory.

Module ValV.
  Inductive t: Type := mk {
    val: Val.t;
    view: View.t;
  }.
  Hint Constructors t.
End ValV.

Definition rmapT := IdMap.t ValV.t.

Module FwdItem.
  Inductive t: Type := mk {
    ts: Time.t;
    view: View.t;
    ex: bool;
  }.
  Hint Constructors t.
End FwdItem.

Definition fwdBankT := IdMap.t FwdItem.t.

Definition exBankT := option Time.t.

Definition cohT := Loc.t -> Time.t.

Definition promisesT := IdSet.t.

Module Local.
  Inductive t: Type := mk {
    rmap: rmapT;
    coh: cohT;
    vrp: View.t;
    vwp: View.t;
    vrm: View.t;
    vwm: View.t;
    vcap: View.t;
    vrel: View.t;
    fwd: fwdBankT;
    ex: exBankT;
    promises: promisesT;
  }.
  Hint Constructors t.

            (* Local.mk *)
            (*   lc1.(Local.rmap) *)
            (*   lc1.(Local.coh) *)
            (*   lc1.(Local.vrp) *)
            (*   lc1.(Local.vwp) *)
            (*   lc1.(Local.vrm) *)
            (*   lc1.(Local.vwm) *)
            (*   lc1.(Local.vcap) *)
            (*   lc1.(Local.vrel) *)
            (*   lc1.(Local.fwd) *)
            (*   lc1.(Local.ex) *)
            (*   lc1.(Local.promises)) *)
End Local.

Module Thread.
  Inductive t: Type := mk {
    lang: unit; (* TODO *)
    local: Local.t;
  }.
  Hint Constructors t.
End Thread.

Definition threadPoolT := IdMap.t Thread.t.

Module Configuration.
  Inductive t: Type := mk {
    tpool: threadPoolT;
    mem: Memory.t;
  }.
  Hint Constructors t.
End Configuration.
