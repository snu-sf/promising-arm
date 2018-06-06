Require Import Relations.
Require Import EquivDec.
Require Import Equality.
Require Import List.
Require Import Bool.
Require Import Lia.
Require Import NArith.
Require Import PArith.
Require Import ZArith.
Require Import FMapPositive.
Require Import FSetPositive.
Require Import EquivDec.
Require Import sflib.

Require Import Basic.
Require Import Order.
Require Import Time.
Require Import Lang.
Require Import Promising.

Set Implicit Arguments.


Theorem promising_pf_to_promising
        p m
        (EXEC: Machine.pf_exec p m):
  Machine.exec p m.
Proof.
  inv EXEC. econs; eauto.
  etrans.
  - eapply Machine.rtc_step_mon; cycle 1; eauto. right. ss.
  - eapply Machine.rtc_step_mon; cycle 1; eauto. left. ss.
Qed.
