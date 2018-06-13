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
Require Import Program.

Require Import Basic.
Require Import Order.
Require Import Time.
Require Import Lang.
Require Import Promising.
Require Import Algorithmic.
Require Import Certify.
Require Import CertifyFacts.
Require Import StateExecFacts.

Set Implicit Arguments.


Lemma lift_machine_state_step
      m1 m2 m3
      (STEP1: Machine.step ExecUnit.state_step m1 m2)
      (STEP2: rtc (Machine.step ExecUnit.state_step) m2 m3)
      (NOPROMISE: Machine.no_promise m3):
  AMachine.step ExecUnit.state_step
                (AMachine.mk m1 (fun tid => option_map (fun _ => Lock.init) (IdMap.find tid m1.(Machine.tpool))))
                (AMachine.mk m2 (fun tid => option_map (fun _ => Lock.init) (IdMap.find tid m2.(Machine.tpool)))).
Proof.
  inv STEP1. econs; eauto; ss.
  - funext. i. rewrite TPOOL, IdMap.add_spec, fun_add_spec. condtac; ss.
  - exploit Machine.unlift_step_state_step; eauto.
    { rewrite TPOOL, IdMap.add_spec. condtac; eauto. instantiate (1 := tid). congr. }
    i. des. eapply rtc_state_step_certify_bot; eauto. ss.
    eapply NOPROMISE. eauto.
  - econs 1. unfold compose. i. revert FIND0. rewrite TPOOL, IdMap.add_spec.
    condtac; ss.
    + i. inv FIND0. ss.
    + destruct (IdMap.find tid0 (Machine.tpool m1)); ss. i. inv FIND0. ss.
Qed.

Lemma lift_rtc_machine_state_step
      m1 m2 m3
      (STEP1: rtc (Machine.step ExecUnit.state_step) m1 m2)
      (STEP2: rtc (Machine.step ExecUnit.state_step) m2 m3)
      (NOPROMISE: Machine.no_promise m3):
  rtc (AMachine.step ExecUnit.state_step)
      (AMachine.mk m1 (fun tid => option_map (fun _ => Lock.init) (IdMap.find tid m1.(Machine.tpool))))
      (AMachine.mk m2 (fun tid => option_map (fun _ => Lock.init) (IdMap.find tid m2.(Machine.tpool)))).
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
  exploit AMachine.init_wf. i.
  exploit AMachine.rtc_step_promise_step_wf; eauto. i.
  destruct am1. ss.
  assert (tlocks = (fun tid => option_map (fun _ => Lock.init) (IdMap.find tid machine.(Machine.tpool)))).
  { funext. i.
    inv x2. ss. specialize (CERTIFY x). revert CERTIFY.
    destruct (IdMap.find x (Machine.tpool machine)) eqn:T.
    - i. inv CERTIFY. exploit FINAL; eauto. i. subst. ss.
    - i. inv CERTIFY. ss.
  }
  subst.
  exploit lift_rtc_machine_state_step; try exact x0; eauto. i.
  esplits; eauto. econs; ss.
  - etrans.
    + eapply rtc_mon; [|by eauto]. apply AMachine.step_mon. right. ss.
    + eapply rtc_mon; [|by eauto]. apply AMachine.step_mon. left. ss.
  - ss.
Qed.
