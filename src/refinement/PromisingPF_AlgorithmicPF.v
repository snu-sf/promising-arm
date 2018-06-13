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


Theorem promising_pf_to_algorithmic_pf
        p m
        (EXEC: Machine.pf_exec p m):
  AMachine.pf_exec p m.
Proof.
  inv EXEC. econs; ss.
  - instantiate (1 := AMachine.mk m1 (fun tid => option_map (fun _ => Lock.init) (IdMap.find tid m1.(Machine.tpool)))).
    (* TODO
     - rtc_state_step_certify_bot : lock.init at last
     - one step from the end..
     *)
    admit.
  - ss.
Admitted.
