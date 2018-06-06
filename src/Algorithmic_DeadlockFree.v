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

Theorem algorithmic_deadlock_free
        m
        (CONSISTENT: AMachine.consistent m):
  exists m',
    <<STEPS: rtc (Machine.step ExecUnit.step) m.(AMachine.machine) m'>> /\
    <<NOPROMISE: Machine.no_promise m'>>.
Proof.
Admitted.
