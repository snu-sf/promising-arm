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
Require Import HahnSets.

Require Import PromisingArch.lib.Basic.
Require Import PromisingArch.lib.Order.
Require Import PromisingArch.lib.Time.
Require Import PromisingArch.lib.Lang.
Require Import PromisingArch.promising.Promising.
Require Import PromisingArch.lcertify.Certify.

Set Implicit Arguments.


Inductive certified_eu_step (tid:Id.t) (eu1 eu2:ExecUnit.t (A:=unit)): Prop :=
| certified_eu_step_intro
    (STEP: ExecUnit.step tid eu1 eu2)
    (CERTIFY: certify tid eu2)
.

Inductive certified_exec (p:program) (m:Machine.t): Prop :=
| exec_intro
    (STEP: rtc (Machine.step certified_eu_step) (Machine.init p) m)
    (NOPROMISE: Machine.no_promise m)
.
Hint Constructors certified_exec.

Theorem certified_exec_sound p m
        (EXEC: certified_exec p m):
  Machine.exec p m.
Proof.
  inv EXEC. econs; ss. eapply rtc_mon; try exact STEP; eauto.
  i. inv H. inv STEP0. econs; eauto.
Qed.

Theorem certified_exec_complete p m
        (EXEC: Machine.exec p m):
  certified_exec p m.
Proof.
  inv EXEC. econs; ss.
  apply clos_rt1n_rt, clos_rt_rtn1 in STEP.
  assert (CERTIFY: forall tid st lc (FIND: IdMap.find tid m.(Machine.tpool) = Some (st, lc)),
             certify tid (ExecUnit.mk st lc m.(Machine.mem))).
  { i. econs; eauto. s. inv NOPROMISE. eauto. }
  revert CERTIFY. clear NOPROMISE. induction STEP; [refl|].
  i. exploit IHSTEP; cycle 1.
  { i. etrans; eauto. econs 2; [|econs 1].
    inv H. econs; eauto. econs; ss. apply CERTIFY.
    rewrite TPOOL, IdMap.add_spec. condtac; ss. congr.
  }
  exploit Machine.rtc_step_step_wf.
  { apply clos_rt_rt1n, clos_rtn1_rt. eauto. }
  { apply Machine.init_wf. }
  i. inv H. rewrite TPOOL in *.
  generalize (CERTIFY tid). rewrite IdMap.add_spec. condtac.
  { inversion e. subst. rewrite FIND in FIND0. inv FIND0.
    intro Y. exploit Y; eauto. i. clear Y.
    eapply step_certify; eauto.
    eapply x0. ss.
  }
  inv STEP0.
  - (* state step *)
    inv STEP1. inv STEP0. ss. rewrite MEM in *.
    intro Y. eapply Y. ss.
  - (* promise step *)
    inv STEP1. ss. subst. inv LOCAL. inv MEM2. rewrite <- H1 in *.
    intro Y. eapply interference_certify; try by apply Y; eauto.
    + econs; ss. unfold nequiv_dec, swap_sumbool.
      match goal with
      | [|- context[match ?c with | left _ => _ | right _ => _ end]] => destruct c
      end; ss.
      congr.
    + eapply x0. ss.
Qed.
