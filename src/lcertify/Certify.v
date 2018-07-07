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
    ex ord vloc vval res e lc
    (EVENT: e = Event.write ex ord vloc vval res)
    (STATE: State.step e eu1.(ExecUnit.state) eu2.(ExecUnit.state))
    (PROMISE: Local.promise vloc.(ValA.val) vval.(ValA.val) tid eu1.(ExecUnit.local) eu1.(ExecUnit.mem) lc eu2.(ExecUnit.mem))
    (FULFILL: Local.fulfill ex ord vloc vval res tid lc eu2.(ExecUnit.mem) eu2.(ExecUnit.local))
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


Inductive sim_time (ts:Time.t) (v1 v2:Time.t): Prop :=
| sim_time_intro
    (TS: v2 <= ts -> v1 = v2)
.
Hint Constructors sim_time.

Inductive sim_view (ts:Time.t) (v1 v2:View.t (A:=unit)): Prop :=
| sim_view_intro
    (TS: v2.(View.ts) <= ts -> v1 = v2)
.
Hint Constructors sim_view.

Inductive sim_val (ts:Time.t) (v1 v2:ValA.t (A:=View.t (A:=unit))): Prop :=
| sim_val_intro
    (TS: v2.(ValA.annot).(View.ts) <= ts -> v1 = v2)
.
Hint Constructors sim_val.

Inductive sim_rmap (ts:Time.t) (rmap1 rmap2:RMap.t (A:=View.t (A:=unit))): Prop :=
| sim_rmap_intro
    (RMAP: IdMap.Forall2 (fun _ => sim_val ts) rmap1 rmap2)
.
Hint Constructors sim_rmap.

Inductive sim_state (ts:Time.t) (st1 st2:State.t (A:=View.t (A:=unit))): Prop :=
| sim_state_intro
    (STMTS: st1.(State.stmts) = st2.(State.stmts))
    (RMAP: sim_rmap ts st1.(State.rmap) st2.(State.rmap))
.
Hint Constructors sim_state.

Inductive sim_exbank (tid:Id.t) (ts:Time.t) (mem1 mem2:Memory.t) (eb1 eb2:Exbank.t (A:=unit)): Prop :=
| sim_exbank_intro
    (LOC: eb1.(Exbank.loc) = eb2.(Exbank.loc))
    (TS: sim_time ts eb1.(Exbank.ts) eb2.(Exbank.ts))
    (EBVIEW: sim_view ts eb1.(Exbank.view) eb2.(Exbank.view))
.

Inductive sim_lc (tid:Id.t) (ts:Time.t) (lc1 lc2:Local.t (A:=unit)) (mem1 mem2:Memory.t): Prop :=
| sim_lc_intro
    (COH: forall loc, sim_time ts (lc1.(Local.coh) loc) (lc2.(Local.coh) loc))
    (VRP: sim_view ts lc1.(Local.vrp) lc2.(Local.vrp))
    (VWP: sim_view ts lc1.(Local.vwp) lc2.(Local.vwp))
    (VRM: sim_view ts lc1.(Local.vrm) lc2.(Local.vrm))
    (VWM: sim_view ts lc1.(Local.vwm) lc2.(Local.vwm))
    (VCAP: sim_view ts lc1.(Local.vcap) lc2.(Local.vcap))
    (VREL: sim_view ts lc1.(Local.vrel) lc2.(Local.vrel))
    (FWDBANK: forall loc,
        opt_rel
          (fun fwd1 fwd2 =>
             fwd2.(FwdItem.ts) <= ts ->
             (fwd1.(FwdItem.ts) = fwd2.(FwdItem.ts) /\
              sim_view ts fwd1.(FwdItem.view) fwd2.(FwdItem.view) /\
              fwd1.(FwdItem.ex) = fwd2.(FwdItem.ex)))
          (lc1.(Local.fwdbank) loc) (lc2.(Local.fwdbank) loc))
    (EXBANK: opt_rel (sim_exbank tid ts mem1 mem2) lc1.(Local.exbank) lc2.(Local.exbank))
    (PROMISES: lc1.(Local.promises) = lc2.(Local.promises))
    (PROMISES_TS: forall mid (FIND: Promises.lookup mid lc1.(Local.promises)), mid <= ts)
.
Hint Constructors sim_lc.

Lemma sim_certify
      tid eu1 eu2
      (STATE: True)
      (CERTIFY: certify tid eu1):
  certify tid eu2.
Proof.
Admitted.
