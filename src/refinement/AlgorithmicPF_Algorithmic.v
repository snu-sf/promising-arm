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
Require Import StateExecFacts.

Set Implicit Arguments.


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

Theorem algorithmic_pf_to_algorithmic
        p m
        (EXEC: AMachine.pf_exec p m):
  exists m',
    <<EXEC: AMachine.exec p m'>> /\
    <<EQUIV: Machine.equiv m m'>>.
Proof.
  inv EXEC. exploit state_exec_rtc_state_step; eauto. i. des.
  eexists (AMachine.mk m2' _). splits; eauto. econs.
  - etrans.
    + eapply rtc_mon; [|by eauto]. apply AMachine.step_mon. right. ss.
    + admit. (* machine step -> amachine step *)
  - eauto.
  - eapply Machine.equiv_no_promise; eauto.
Admitted.
