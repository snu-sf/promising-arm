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
Require Import Certify.
Require Import CertifyFacts.

Set Implicit Arguments.

Lemma amachine_step_backward
      m1 m2 tlocks2
      (STEP: Machine.step ExecUnit.promise_step m1 m2)
      (WF1: Machine.wf m1)
      (WF2: AMachine.wf (AMachine.mk m2 tlocks2)):
  exists tlocks1,
    <<STEP: AMachine.step ExecUnit.promise_step (AMachine.mk m1 tlocks1) (AMachine.mk m2 tlocks2)>> /\
    <<WF: AMachine.wf (AMachine.mk m1 tlocks1)>>.
Proof.
Admitted.

Lemma amachine_rtc_step_backward
      m1 m2 tlocks2
      (STEP: rtc (Machine.step ExecUnit.promise_step) m1 m2)
      (WF1: Machine.wf m1)
      (WF2: AMachine.wf (AMachine.mk m2 tlocks2)):
  exists tlocks1,
    <<STEP: rtc (AMachine.step ExecUnit.promise_step) (AMachine.mk m1 tlocks1) (AMachine.mk m2 tlocks2)>> /\
    <<WF: AMachine.wf (AMachine.mk m1 tlocks1)>>.
Proof.
  revert WF1. induction STEP; eauto. i. exploit IHSTEP; eauto.
  { eapply Machine.step_promise_step_wf; eauto. }
  i. des.
  exploit amachine_step_backward; eauto. i. des.
  esplits; eauto.
Qed.

Theorem promising_pf_to_algorithmic_pf
        p m
        (EXEC: Machine.pf_exec p m):
  AMachine.pf_exec p m.
Proof.
  inv EXEC. econs; ss.
  - instantiate (1 := AMachine.mk m1 (fun tid => option_map (fun _ => Lock.init) (IdMap.find tid m1.(Machine.tpool)))).
    exploit amachine_rtc_step_backward; eauto.
    { apply Machine.init_wf. }
    { instantiate (1 := (fun tid => option_map (fun _ => Lock.init) (IdMap.find tid m1.(Machine.tpool)))).
      econs; ss.
      - eapply Machine.rtc_step_promise_step_wf; eauto.
        apply Machine.init_wf.
      - i. inv STEP2. specialize (TPOOL tid). inv TPOOL; ss.
        exploit rtc_state_step_certify_bot; eauto. ss.
        destruct b. ss. eapply NOPROMISE. eauto.
      - apply AMachine.init_tlocks_consistent.
    }
    i. des.
    assert (tlocks1 = (fun tid => option_map (fun _ => Lock.init) (IdMap.find tid p))).
    { inv WF. ss. funext. i. specialize (CERTIFY x). revert CERTIFY.
      rewrite IdMap.map_spec. destruct (IdMap.find x p); ss.
      - i. inv CERTIFY. apply no_promise_certify_inv in REL; ss. congr.
      - i. inv CERTIFY. ss.
    }
    subst. apply STEP.
  - ss.
  - s. i. destruct (IdMap.find tid (Machine.tpool m1)); ss. inv FIND. ss.
Qed.
