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
Require Import Certify.
Require Import Algorithmic.
Require Import StateExecFacts.

Set Implicit Arguments.


Lemma lift_machine_state_step
      m1 m2 m3
      (STEP1: Machine.step ExecUnit.state_step m1 m2)
      (STEP2: rtc (Machine.step ExecUnit.state_step) m2 m3)
      (NOPROMISE: Machine.no_promise m3):
  AMachine.step ExecUnit.state_step
                (AMachine.mk m1 (IdMap.map (fun _ => Lock.init) m1.(Machine.tpool)))
                (AMachine.mk m2 (IdMap.map (fun _ => Lock.init) m2.(Machine.tpool))).
Proof.
  inv STEP1. econs; eauto; ss.
Admitted.

Lemma lift_rtc_machine_state_step
      m1 m2 m3
      (STEP1: rtc (Machine.step ExecUnit.state_step) m1 m2)
      (STEP2: rtc (Machine.step ExecUnit.state_step) m2 m3)
      (NOPROMISE: Machine.no_promise m3):
  rtc (AMachine.step ExecUnit.state_step)
      (AMachine.mk m1 (IdMap.map (fun _ => Lock.init) m1.(Machine.tpool)))
      (AMachine.mk m2 (IdMap.map (fun _ => Lock.init) m2.(Machine.tpool))).
Proof.
  revert STEP2 NOPROMISE. induction STEP1; eauto. i.
  exploit lift_machine_state_step; try exact NOPROMISE; eauto. etrans; eauto.
Qed.

Theorem algorithmic_pf_to_algorithmic
        p m
        (EXEC: AMachine.pf_exec p m):
  exists m',
    <<EXEC: AMachine.exec p m'>> /\
    <<EQUIV: Machine.equiv m m'>>.
Proof.
  inv EXEC. exploit state_exec_rtc_state_step; eauto. i. des.
  exploit Machine.equiv_no_promise; eauto. i.
  destruct am1.
  assert (tlocks = IdMap.map (fun _ => Lock.init) machine.(Machine.tpool)) by admit. subst. ss.
  exploit lift_rtc_machine_state_step; try exact x0; eauto. i.
  eexists (AMachine.mk m2' _). splits; eauto. econs.
  - etrans.
    + eapply rtc_mon; [|by eauto]. apply AMachine.step_mon. right. ss.
    + eapply rtc_mon; [|by eauto]. apply AMachine.step_mon. left. ss.
  - ss.
  - ss.
Admitted.
