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


Lemma rtc_state_step_certify_inv
      m1 m2 tid st lc l
      (STEPS: rtc (Machine.step ExecUnit.state_step) m1 m2)
      (NOPROMISE: Machine.no_promise m2)
      (FIND: IdMap.find tid m1.(Machine.tpool) = Some (st, lc))
      (CERTIFY: certify tid (ExecUnit.mk st lc m1.(Machine.mem)) l):
  l = bot.
Proof.
Admitted.

Theorem algorithmic_pf_to_algorithmic
        p m
        (EXEC: AMachine.pf_exec p m):
  AMachine.exec p m.
Proof.
  inv EXEC. econs; cycle 1; ss.
  { instantiate (1 := AMachine.mk m (IdMap.map (fun _ => bot) p)). ss. }
  etrans.
  { eapply AMachine.rtc_step_mon; cycle 1; eauto. right. ss. }
  admit. (* use rtc_state_step_certify_inv *)
Admitted.
