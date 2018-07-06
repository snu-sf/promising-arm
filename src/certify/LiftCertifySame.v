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
Require Import HahnSets.
Require Import sflib.

Require Import Basic.
Require Import Order.
Require Import Time.
Require Import Lang.
Require Import Promising.
Require Import Certify.
Require Import CertifyFacts.

Set Implicit Arguments.


Lemma lift_certify_same
      tid loc val lock2
      (eu1 eu2:ExecUnit.t (A:=unit))
      (CERTIFY: certify tid eu2 lock2)
      (STATE: eu1.(ExecUnit.state) = eu2.(ExecUnit.state))
      (LOCAL: Local.promise loc val tid eu1.(ExecUnit.local) eu1.(ExecUnit.mem) eu2.(ExecUnit.local) eu2.(ExecUnit.mem)):
  exists lock1,
    <<CERTIFY: certify tid eu1 lock1>> /\
    <<LOCK: Lock.proceed loc lock1 lock2>>.
Proof.
Admitted.
