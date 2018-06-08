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


Lemma rtc_state_step_certify_bot
      m1 m2 tid st lc
      (STEPS: rtc (Machine.step ExecUnit.state_step) m1 m2)
      (NOPROMISE: Machine.no_promise m2)
      (FIND: IdMap.find tid m1.(Machine.tpool) = Some (st, lc)):
  certify tid (ExecUnit.mk st lc m1.(Machine.mem)) bot.
Proof.
  revert tid st lc FIND NOPROMISE. induction STEPS.
  { econs; eauto; ss.
    - eapply NOPROMISE. eauto.
    - funext. unfold bot, fun_bot. i. propext. econs; ss. i. inv H; ss.
  }
  i. inv H. exploit IHSTEPS; ss.
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
