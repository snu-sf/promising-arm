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
Require Import CertifyFacts.

Set Implicit Arguments.


Theorem promising_pf_to_algorithmic_pf
        p m
        (EXEC: Machine.pf_exec p m):
  AMachine.pf_exec p m.
Proof.
  inv EXEC. exploit rtc_state_step_certify_bot; eauto.
Admitted.
