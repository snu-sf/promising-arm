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


Lemma no_promise_step
      tid aeu1 aeu2
      (STEP: AExecUnit.step tid aeu1 aeu2)
      (WF: ExecUnit.wf tid aeu1)
      (NOPROMISE: aeu1.(ExecUnit.local).(Local.promises) = bot):
  <<NOPROMISE: aeu2.(ExecUnit.local).(Local.promises) = bot>> /\
  <<TAINT: aeu2.(AExecUnit.aux).(AExecUnit.taint) = aeu1.(AExecUnit.aux).(AExecUnit.taint)>>.
Proof.
  destruct aeu1 as [[st1 lc1 mem1] aux1].
  destruct aeu2 as [[st2 lc2 mem2] aux2].
  ss. inv STEP.
  - (* state_step *)
    inv STEP0. inv STEP. ss. subst. inv LOCAL.
    + inv LC. eauto.
    + inv STEP. ss. destruct ex; ss.
    + inv WF. ss. inv LOCAL. inv STEP. inv WRITABLE. ss.
      exploit PROMISES0; eauto. rewrite NOPROMISE, Promises.lookup_bot. ss.
    + inv STEP. ss. esplits; ss.
      funext. i. propext. econs; i.
      * inv H; ss.
      * left. ss.
    + inv STEP. ss.
    + inv STEP. ss.
    + inv STEP. ss.
    + inv STEP. ss.
  - (* write step *)
    inv STEP0. ss. subst.
    inv LOCAL. ss.
Qed.

Lemma no_promise_steps
      tid aeu1 aeu2
      (STEPS: rtc (AExecUnit.step tid) aeu1 aeu2)
      (WF: ExecUnit.wf tid aeu1)
      (NOPROMISE: aeu1.(ExecUnit.local).(Local.promises) = bot):
  <<NOPROMISE: aeu2.(ExecUnit.local).(Local.promises) = bot>> /\
  <<TAINT: aeu2.(AExecUnit.aux).(AExecUnit.taint) = aeu1.(AExecUnit.aux).(AExecUnit.taint)>>.
Proof.
  revert NOPROMISE. induction STEPS; ss. i.
  exploit no_promise_step; eauto. i. des.
  exploit IHSTEPS; eauto.
  { eapply AExecUnit.step_wf; eauto. }
  i. des.
  esplits; ss. etrans; eauto.
Qed.

Lemma rtc_state_step_certify_bot
      m1 m2 tid st lc
      (STEPS: rtc (Machine.step ExecUnit.state_step) m1 m2)
      (WF: Machine.wf m1)
      (NOPROMISE: Machine.no_promise m2)
      (FIND: IdMap.find tid m1.(Machine.tpool) = Some (st, lc)):
  certify tid (ExecUnit.mk st lc m1.(Machine.mem)) Lock.init.
Proof.
  revert tid st lc FIND NOPROMISE. induction STEPS.
  { econs; eauto; ss.
    - eapply NOPROMISE. eauto.
    - funext. unfold bot, fun_bot. i. propext. econs; ss. i. inv H; ss.
  }
  i. inv H. exploit IHSTEPS; ss.
  { eapply Machine.step_state_step_wf; eauto. }
  { rewrite TPOOL, IdMap.add_spec, FIND.
    instantiate (1 := if equiv_dec tid tid0 then lc2 else lc).
    instantiate (1 := if equiv_dec tid tid0 then st2 else st).
    condtac; ss.
  }
  condtac.
  - inversion e. subst. rewrite FIND in FIND0. inv FIND0.
    admit. (* certify is preserved if I executed a state_step. *)
  - admit. (* certify is preserved if another thread is executed. *)
Admitted.

Theorem promising_pf_to_algorithmic_pf
        p m
        (EXEC: Machine.pf_exec p m):
  AMachine.pf_exec p m.
Proof.
  inv EXEC. exploit rtc_state_step_certify_bot; eauto.
Admitted.
