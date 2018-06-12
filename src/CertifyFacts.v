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

Set Implicit Arguments.


Lemma no_promise_certify_init
      tid (eu:ExecUnit.t (A:=unit))
      (PROMISES: eu.(ExecUnit.local).(Local.promises) = bot):
  certify tid eu Lock.init.
Proof.
  econs; eauto. s. funext. i. propext. econs; ss.
  intro X. inv X. inv R.
Qed.

Lemma no_promise_certify_inv
      tid (eu:ExecUnit.t (A:=unit)) l
      (PROMISES: eu.(ExecUnit.local).(Local.promises) = bot)
      (CERTIFY: certify tid eu l):
  l = Lock.init.
Proof.
  destruct l. inv CERTIFY. ss. subst. inv STEPS.
  - ss. unfold Lock.init. f_equal. funext. i. propext. econs; i; ss.
    inv H. inv R.
  - inv H; inv STEP; ss.
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

Lemma rtc_state_step_certify_inv
      m1 m2 tid st lc lock
      (STEPS: rtc (Machine.step ExecUnit.state_step) m1 m2)
      (NOPROMISE: Machine.no_promise m2)
      (FIND: IdMap.find tid m1.(Machine.tpool) = Some (st, lc))
      (CERTIFY: certify tid (ExecUnit.mk st lc m1.(Machine.mem)) lock):
  lock = Lock.init.
Proof.
  destruct lock as [ex release].
  inv CERTIFY. ss. subst.
Admitted.
