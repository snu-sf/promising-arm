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
Require Import Algorithmic.

Set Implicit Arguments.


Lemma rtc_astep_rtc_step
      eustep am1 am2
      (STEPS: rtc (AMachine.step eustep) am1 am2):
  rtc (Machine.step eustep) am1 am2.
Proof.
  induction STEPS.
  - refl.
  - econs; eauto. inv H. econs; eauto.
Qed.

Theorem algorithmic_to_promising
        p m
        (EXEC: AMachine.exec p m):
  Machine.exec p m.
Proof.
  inv EXEC. econs; eauto.
  apply rtc_astep_rtc_step in STEP. ss.
Qed.

Theorem algorithmic_deadlock_free
        m
        (CONSISTENT: AMachine.consistent m):
  exists m',
    <<STEPS: rtc (Machine.step ExecUnit.step) m.(AMachine.machine) m'>> /\
    <<NOPROMISE: Machine.no_promise m'>>.
Proof.
Admitted.
