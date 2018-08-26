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

Set Implicit Arguments.


Inductive write_step (tid:Id.t) (eu1 eu2:ExecUnit.t (A:=unit)): Prop :=
| write_step_intro
    ex ord vloc vval res ts e lc
    (EVENT: e = Event.write ex ord vloc vval res)
    (STATE: State.step e eu1.(ExecUnit.state) eu2.(ExecUnit.state))
    (PROMISE: Local.promise vloc.(ValA.val) vval.(ValA.val) ts tid eu1.(ExecUnit.local) eu1.(ExecUnit.mem) lc eu2.(ExecUnit.mem))
    (FULFILL: Local.fulfill ex ord vloc vval res ts tid lc eu2.(ExecUnit.mem) eu2.(ExecUnit.local))
.
Hint Constructors write_step.

Inductive certify_step (tid:Id.t) (eu1 eu2:ExecUnit.t (A:=unit)): Prop :=
| certify_step_state
    (STEP: ExecUnit.state_step tid eu1 eu2)
| certify_step_write
    (STEP: write_step tid eu1 eu2)
.
Hint Constructors certify_step.

Inductive certify (tid:Id.t) (eu1:ExecUnit.t (A:=unit)): Prop :=
| certify_intro
    eu2
    (STEPS: rtc (certify_step tid) eu1 eu2)
    (NOPROMISE: eu2.(ExecUnit.local).(Local.promises) = bot)
.
Hint Constructors certify.


Lemma write_step_wf
      tid eu1 eu2
      (STEP: write_step tid eu1 eu2)
      (WF: ExecUnit.wf tid eu1):
  ExecUnit.wf tid eu2.
Proof.
  inv STEP.
  exploit (ExecUnit.promise_step_wf (A:=unit)); [|by eauto|].
  { instantiate (1 := ExecUnit.mk (A:=unit) eu1.(ExecUnit.state) lc eu2.(ExecUnit.mem)).
    econs; ss. eauto.
  }
  i. exploit (ExecUnit.state_step_wf (A:=unit)); eauto. econs. econs; eauto. s.
  econs 3; eauto.
Qed.
Hint Resolve write_step_wf.

Lemma certify_step_wf
      tid eu1 eu2
      (STEP: certify_step tid eu1 eu2)
      (WF: ExecUnit.wf tid eu1):
  ExecUnit.wf tid eu2.
Proof.
  inv STEP.
  - eapply ExecUnit.state_step_wf; eauto.
  - eapply write_step_wf; eauto.
Qed.

Lemma rtc_certify_step_wf
      tid eu1 eu2
      (STEP: rtc (certify_step tid) eu1 eu2)
      (WF: ExecUnit.wf tid eu1):
  ExecUnit.wf tid eu2.
Proof.
  revert WF. induction STEP; ss.
  i. apply IHSTEP. eapply certify_step_wf; eauto.
Qed.

Lemma certify_step_vcap
      tid eu eu'
      (STEP: certify_step tid eu eu')
      (WF1: ExecUnit.wf tid eu):
  le eu.(ExecUnit.local).(Local.vcap) eu'.(ExecUnit.local).(Local.vcap).
Proof.
  destruct eu as [st lc mem].
  destruct eu' as [st' lc' mem'].
  ss. inv STEP.
  { inv STEP0. inv STEP. ss. subst. inv LOCAL; try inv STEP; ss; try refl.
    all: try by apply join_l.
    inv LC. s. apply join_l.
  }
  { inv STEP0. ss. inv PROMISE. inv FULFILL. ss. apply join_l. }
Qed.

Lemma certify_step_vcap_promise
      tid ts eu eu'
      (STEP: certify_step tid eu eu')
      (WF1: ExecUnit.wf tid eu)
      (VCAP: ts <= eu.(ExecUnit.local).(Local.vcap).(View.ts))
      (PROMISES: Promises.lookup ts eu.(ExecUnit.local).(Local.promises)):
  Promises.lookup ts eu'.(ExecUnit.local).(Local.promises).
Proof.
  destruct eu as [st lc mem].
  destruct eu' as [st' lc' mem'].
  ss. inv STEP.
  { inv STEP0. inv STEP. ss. subst. inv LOCAL; try inv STEP; ss.
    - rewrite Promises.unset_o. condtac; ss. inversion e. subst.
      inv WRITABLE. ss. clear -VCAP EXT. unfold join, Time.join in *. lia.
    - inv LC. ss.
  }
  { inv STEP0. ss. inv PROMISE. inv FULFILL. ss.
    rewrite Promises.unset_o, Promises.set_o. condtac; ss. inversion e. subst.
      inv WRITABLE. ss. clear -VCAP EXT. unfold join, Time.join in *. lia.
  }
Qed.

Lemma rtc_certify_step_vcap_promise
      tid ts eu eu'
      (STEP: rtc (certify_step tid) eu eu')
      (WF1: ExecUnit.wf tid eu)
      (VCAP: ts <= eu.(ExecUnit.local).(Local.vcap).(View.ts))
      (PROMISES: Promises.lookup ts eu.(ExecUnit.local).(Local.promises)):
  Promises.lookup ts eu'.(ExecUnit.local).(Local.promises).
Proof.
  revert WF1 VCAP PROMISES. induction STEP; ss. i.
  exploit certify_step_wf; eauto. i.
  exploit certify_step_vcap; eauto. i.
  exploit certify_step_vcap_promise; eauto. i.
  eapply IHSTEP; eauto.
  rewrite VCAP. apply x2.
Qed.

Lemma state_step_certify
      tid eu1 eu2
      (CERTIFY: certify tid eu2)
      (STEP: ExecUnit.state_step tid eu1 eu2):
  certify tid eu1.
Proof.
  inv CERTIFY. econs; [|by eauto]. econs; eauto.
Qed.


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
