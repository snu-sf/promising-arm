Require Import NArith.
Require Import PArith.
Require Import ZArith.
Require Import Lia.
Require Import EquivDec.
Require Import sflib.

Require Import Basic.
Require Import Order.

Set Implicit Arguments.


Module Time.
  Include Nat.

  Definition pred_opt (ts:t): option t :=
    match ts with
    | O => None
    | S n => Some n
    end.

  (* Definition le (a b:t) := a <= b. *)
  Definition join (a b:t) := max a b.
  Definition bot: t := 0.

  Global Program Instance order: orderC join bot.
  Next Obligation. unfold join. lia. Qed.
  Next Obligation. unfold join. lia. Qed.
  Next Obligation. eauto using Max.max_assoc. Qed.
  Next Obligation. eauto using Max.max_comm. Qed.
  Next Obligation. unfold join. lia. Qed.
  Next Obligation. unfold bot. lia. Qed.

  Global Instance eqdec: EqDec t eq := nat_eq_eqdec.
End Time.
