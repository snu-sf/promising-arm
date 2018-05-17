Require Import Relations.
Require Import Permutation.
Require Import NArith.
Require Import PArith.
Require Import ZArith.
Require Import Lia.
Require Import FMapPositive.
Require Import FSetPositive.
Require Import EquivDec.
Require Import sflib.
Require Import paco.
Require Import HahnRelationsBasic.

Require Import Order.
Require Import Time.
Require Import Lang.
Require Import Axiomatic.
Require Import Promising.

Set Implicit Arguments.


Lemma linearize A
      (l: list A)
      (rel: relation A)
      (ACYCLIC: acyclic rel):
  exists l',
    <<PERM: Permutation l l'>> /\
    <<REL: forall i j x y
             (X: List.nth_error l' i = Some x)
             (X: List.nth_error l' j = Some y),
        ~ rel y x>>.
Proof.
  (* TODO
     - Pick an element x.
     - Split the list: BEFORE:={y | rtc rel y x} and the others AFTER
     - Linearize BEFORE, place x, and then linearize AFTER.
   *)
Admitted.

Lemma axiomatic_to_promising
      p ex
      (AXIOMATIC: is_valid p ex):
  False.
Proof.
  



  (* TODO

     - Give an order on all writes using `ob`.
   *)
Admitted.
