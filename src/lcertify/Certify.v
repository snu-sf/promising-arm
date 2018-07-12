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


Inductive sim_time (ts:Time.t) (mem1 mem2:Memory.t) (v1 v2:Time.t): Prop :=
| sim_time_intro
    (TS: v2 <= ts -> v1 = v2)
    (WF1: v1 <= length mem1)
    (WF2: v2 <= length mem2)
    (ITF: forall loc (LAT: Memory.latest loc ts v2 mem2), Memory.latest loc ts v1 mem1)
.
Hint Constructors sim_time.

Inductive sim_view (ts:Time.t) (mem1 mem2:Memory.t) (v1 v2:View.t (A:=unit)): Prop :=
| sim_view_intro
    (TS: v2.(View.ts) <= ts -> v1 = v2)
    (WF1: v1.(View.ts) <= length mem1)
    (WF2: v2.(View.ts) <= length mem2)
    (ITF: forall loc (LAT: Memory.latest loc ts v2.(View.ts) mem2), Memory.latest loc ts v1.(View.ts) mem1)
.
Hint Constructors sim_view.

Inductive sim_val (ts:Time.t) (mem1 mem2:Memory.t) (v1 v2:ValA.t (A:=View.t (A:=unit))): Prop :=
| sim_val_intro
    (TS: v2.(ValA.annot).(View.ts) <= ts -> v1 = v2)
    (WF1: v1.(ValA.annot).(View.ts) <= length mem1)
    (WF2: v2.(ValA.annot).(View.ts) <= length mem2)
    (ITF: forall loc (LAT: Memory.latest loc ts v2.(ValA.annot).(View.ts) mem2), Memory.latest loc ts v1.(ValA.annot).(View.ts) mem1)
.
Hint Constructors sim_val.

Inductive sim_rmap (ts:Time.t) (mem1 mem2:Memory.t) (rmap1 rmap2:RMap.t (A:=View.t (A:=unit))): Prop :=
| sim_rmap_intro
    (RMAP: IdMap.Forall2 (fun _ => sim_val ts mem1 mem2) rmap1 rmap2)
.
Hint Constructors sim_rmap.

Inductive sim_state (ts:Time.t) (mem1 mem2:Memory.t) (st1 st2:State.t (A:=View.t (A:=unit))): Prop :=
| sim_state_intro
    (STMTS: st1.(State.stmts) = st2.(State.stmts))
    (RMAP: sim_rmap ts mem1 mem2 st1.(State.rmap) st2.(State.rmap))
.
Hint Constructors sim_state.

Inductive sim_fwdbank (ts:Time.t) (mem1 mem2:Memory.t) (loc:Loc.t) (fwd1 fwd2:FwdItem.t (A:=unit)): Prop :=
(* | sim_fwdbank_below *)
(*     (TS2: fwd2.(FwdItem.ts) <= ts) *)
(*     (VIEW2: fwd2.(FwdItem.view).(View.ts) <= fwd2.(FwdItem.ts)) *)
(*     (EQ: fwd1 = fwd2) *)
| sim_fwdbank_intro
    val
    (TS1: sim_time ts mem1 mem2 fwd1.(FwdItem.ts) fwd2.(FwdItem.ts))
    (TS2: fwd2.(FwdItem.ts) > ts -> fwd1.(FwdItem.ts) > ts)
    (VIEW: sim_view ts mem1 mem2 fwd1.(FwdItem.view) fwd2.(FwdItem.view))
    (EX: fwd1.(FwdItem.ex) = fwd2.(FwdItem.ex))
    (FWDTS1: fwd1.(FwdItem.view).(View.ts) <= fwd1.(FwdItem.ts))
    (FWDTS2: fwd2.(FwdItem.view).(View.ts) <= fwd2.(FwdItem.ts))
    (READ1: Memory.read loc fwd1.(FwdItem.ts) mem1 = Some val)
    (READ2: Memory.read loc fwd2.(FwdItem.ts) mem2 = Some val)
.

(* TODO: move many lemmas *)
(* TODO: move *)
Ltac des_eq :=
  repeat
    (try match goal with
         | [H: ?a === ?b |- _] => inv H
         | [H: _ === riscv |- _] => revert H
         | [H: proj_sumbool (equiv_dec ?a ?a) = true |- _] => clear H
         | [H: proj_sumbool (equiv_dec ?a ?b) = _ |- _] => destruct (equiv_dec a b)
         | [H: negb _ = true |- _] => apply Bool.negb_true_iff in H
         | [H: negb _ = false |- _] => apply Bool.negb_false_iff in H
         | [H: andb _ _ = false |- _] => apply Bool.andb_false_iff in H
         | [H: andb _ _ = true |- _] => apply Bool.andb_true_iff in H
         | [H: orb _ _ = false |- _] => apply Bool.orb_false_iff in H
         end;
     ss; des; subst; try congr).

Lemma sim_fwd_view1 ts mem1 mem2 loc fwd1 fwd2 t o
      (FWD: sim_fwdbank ts mem1 mem2 loc fwd1 fwd2)
      (MEM1: ts <= length mem1)
      (MEM2: ts <= length mem2)
      (T: t <= ts)
      (TS: fwd2.(FwdItem.ts) <= t):
  sim_view ts mem1 mem2 (FwdItem.read_view fwd1 t o) (FwdItem.read_view fwd2 t o).
Proof.
  destruct fwd1 as [ts1 view1 ex1].
  destruct fwd2 as [ts2 view2 ex2].
  unfold FwdItem.read_view. s. inv FWD; ss; repeat condtac; ss.
  all: repeat match goal with
              | [H: sim_time _ _ _ _ _ |- _] => inv H
              | [H: sim_view _ _ _ _ _ |- _] => inv H
              end.
  all: unfold Time.t in *.
  all: des_eq.
  all: try by econs; ss; ii; lia.
  - econs; ss; ii; try lia.
    rewrite TS0 in c; [|lia]. congr.
  - econs; ss; ii; try lia.
    rewrite TS0 in c; [|lia]. congr.
  - econs; ss; ii; try lia.
    rewrite TS0 in c; [|lia]. congr.
  - econs; ss; ii; try lia.
    rewrite TS0 in c; [|lia]. congr.
Qed.

(* TODO: move *)
    Lemma latest_uniq
          ts1 ts2 ts loc mem val1 val2
          (TS1: ts1 <= ts)
          (TS2: ts2 <= ts)
          (LATEST1: Memory.latest loc ts1 ts mem)
          (LATEST2: Memory.latest loc ts2 ts mem)
          (MSG1: Memory.read loc ts1 mem = Some val1)
          (MSG2: Memory.read loc ts2 mem = Some val2):
      ts1 = ts2.
    Proof.
      destruct (Nat.lt_trichotomy ts1 ts2); des; ss.
      - destruct ts2; [lia|]. exfalso.
        revert MSG2. unfold Memory.read. s. destruct (nth_error mem ts2) eqn:NTH; ss.
        condtac; ss. inversion e. subst. i. inv MSG2.
        eapply LATEST1; eauto.
      - destruct ts1; [lia|]. exfalso.
        revert MSG1. unfold Memory.read. s. destruct (nth_error mem ts1) eqn:NTH; ss.
        condtac; ss. inversion e. subst. i. inv MSG1.
        eapply LATEST2; eauto.
    Qed.

Lemma sim_fwd_view2 ts mem1 mem2 loc fwd1 fwd2 ts1 ts2 o
      (FWD: sim_fwdbank ts mem1 mem2 loc fwd1 fwd2)
      (MEM1: ts <= length mem1)
      (MEM2: ts <= length mem2)
      (TS1: ts1 <= length mem1)
      (TS2: ts2 <= length mem2)
      (T1: ts1 <= ts)
      (T2: ts2 > ts)
      (FWDTS1: fwd1.(FwdItem.ts) <= ts1)
      (FWDTS2: fwd2.(FwdItem.ts) <= ts2):
  sim_view ts mem1 mem2 (FwdItem.read_view fwd1 ts1 o) (FwdItem.read_view fwd2 ts2 o).
Proof.
  destruct fwd1 as [tsf1 view1 ex1].
  destruct fwd2 as [tsf2 view2 ex2].
  unfold FwdItem.read_view in *. s. inv FWD; ss; repeat condtac; ss; subst.
  all: repeat match goal with
              | [H: sim_time _ _ _ _ _ |- _] => inv H
              | [H: sim_view _ _ _ _ _ |- _] => inv H
              end.
  all: unfold Time.t in *.
  all: des_eq.
  all: try by econs; ss; ii; lia.
Qed.

      (* TODO: move *)
      Lemma latest_mon
            loc f t1 t2 mem
            (LATEST: Memory.latest loc f t2 mem)
            (T: t1 <= t2):
        Memory.latest loc f t1 mem.
      Proof.
        ii. eapply LATEST; eauto. lia.
      Qed.

Lemma sim_fwd_view3 ts mem1 mem2 loc fwd1 fwd2 ts2 o
      (FWD: sim_fwdbank ts mem1 mem2 loc fwd1 fwd2)
      (MEM1: ts <= length mem1)
      (MEM2: ts <= length mem2)
      (TS2: ts2 <= length mem2)
      (T2: ts2 > ts)
      (FWDVIEW1: fwd1.(FwdItem.view).(View.ts) <= fwd1.(FwdItem.ts))
      (FWDVIEW2: fwd2.(FwdItem.view).(View.ts) <= fwd2.(FwdItem.ts))
      (FWDTS1: fwd1.(FwdItem.ts) <= length mem1)
      (FWDTS2: fwd2.(FwdItem.ts) <= ts2):
  sim_view ts mem1 mem2 (FwdItem.read_view fwd1 fwd1.(FwdItem.ts) o) (FwdItem.read_view fwd2 ts2 o).
Proof.
  destruct fwd1 as [tsf1 view1 ex1].
  destruct fwd2 as [tsf2 view2 ex2].
  unfold FwdItem.read_view in *. s. inv FWD; ss; repeat condtac; ss; subst.
  all: repeat match goal with
              | [H: sim_time _ _ _ _ _ |- _] => inv H
              | [H: sim_view _ _ _ _ _ |- _] => inv H
              end.
  all: unfold Time.t in *.
  all: des_eq.
  all: try by econs; ss; ii; lia.
  - econs; ss; i; try lia.
    eapply ITF0. eapply latest_mon; eauto. lia.
  - econs; ss; i; try lia.
    eapply ITF0. eapply latest_mon; eauto. lia.
  - econs; ss; i; try lia.
    eapply ITF. eapply latest_mon; eauto.
  - econs; ss; i; try lia.
    eapply ITF. eapply latest_mon; eauto.
Qed.

Inductive sim_exbank (tid:Id.t) (ts:Time.t) (mem1 mem2:Memory.t) (eb1 eb2:Exbank.t (A:=unit)): Prop :=
| sim_exbank_intro
    (LOC: eb1.(Exbank.loc) = eb2.(Exbank.loc))
    (TS1: sim_time ts mem1 mem2 eb1.(Exbank.ts) eb2.(Exbank.ts))
    (TS2: ts < eb2.(Exbank.ts) -> Memory.latest eb1.(Exbank.loc) ts eb1.(Exbank.ts) mem1)
    (EBVIEW: sim_view ts mem1 mem2 eb1.(Exbank.view) eb2.(Exbank.view))
.
Hint Constructors sim_exbank.

Inductive sim_lc (tid:Id.t) (ts:Time.t) (mem1 mem2:Memory.t) (lc1 lc2:Local.t (A:=unit)): Prop :=
| sim_lc_intro
    (COH: forall loc, sim_time ts mem1 mem2 (lc1.(Local.coh) loc) (lc2.(Local.coh) loc))
    (VRP: sim_view ts mem1 mem2 lc1.(Local.vrp) lc2.(Local.vrp))
    (VWP: sim_view ts mem1 mem2 lc1.(Local.vwp) lc2.(Local.vwp))
    (VRM: sim_view ts mem1 mem2 lc1.(Local.vrm) lc2.(Local.vrm))
    (VWM: sim_view ts mem1 mem2 lc1.(Local.vwm) lc2.(Local.vwm))
    (VCAP: sim_view ts mem1 mem2 lc1.(Local.vcap) lc2.(Local.vcap))
    (VREL: sim_view ts mem1 mem2 lc1.(Local.vrel) lc2.(Local.vrel))
    (FWDBANK: forall loc, sim_fwdbank ts mem1 mem2 loc (lc1.(Local.fwdbank) loc) (lc2.(Local.fwdbank) loc))
    (EXBANK: opt_rel (sim_exbank tid ts mem1 mem2) lc1.(Local.exbank) lc2.(Local.exbank))
    (PROMISES1: forall tsp (TSP: tsp <= ts), Promises.lookup tsp lc1.(Local.promises) = Promises.lookup tsp lc2.(Local.promises))
    (PROMISES2: forall tsp (TSP: tsp > ts), Promises.lookup tsp lc1.(Local.promises) = false)
.
Hint Constructors sim_lc.

Inductive sim_mem (tid:Id.t) (ts:Time.t) (mem1 mem2:Memory.t): Prop :=
| sim_mem_intro
    mem mem1' mem2'
    (MEM: ts = length mem)
    (MEM1: mem1 = mem ++ mem1')
    (MEM2: mem2 = mem ++ mem2')
    (MEM1': List.Forall (fun msg => msg.(Msg.tid) = tid) mem1')
.
Hint Constructors sim_mem.

Inductive sim_eu (tid:Id.t) (ts:Time.t) (eu1 eu2:ExecUnit.t (A:=unit)): Prop :=
| sim_eu_intro
    (STATE: sim_state ts eu1.(ExecUnit.mem) eu2.(ExecUnit.mem) eu1.(ExecUnit.state) eu2.(ExecUnit.state))
    (LOCAL: sim_lc tid ts eu1.(ExecUnit.mem) eu2.(ExecUnit.mem) eu1.(ExecUnit.local) eu2.(ExecUnit.local))
    (MEM: sim_mem tid ts eu1.(ExecUnit.mem) eu2.(ExecUnit.mem))
.
Hint Constructors sim_eu.

Lemma sim_time_join
      ts mem1 mem2 l1 l2 r1 r2
      (VIEW1: sim_time ts mem1 mem2 l1 r1)
      (VIEW2: sim_time ts mem1 mem2 l2 r2):
  sim_time ts mem1 mem2 (join l1 l2) (join r1 r2).
Proof.
  inv VIEW1. inv VIEW2. econs.
  - i. rewrite TS, TS0; ss.
    + rewrite <- H, <- join_r. ss.
    + rewrite <- H, <- join_l. ss.
  - apply join_spec; ss.
  - apply join_spec; ss.
  - ii. apply Time.max_le in TS2. des.
    + eapply ITF; eauto.
      eapply latest_mon; eauto. apply join_l.
    + eapply ITF0; eauto.
      eapply latest_mon; eauto. apply join_r.
Qed.

Lemma sim_time_eq
      ts mem1 mem2 v1 v2
      (SIM: sim_time ts mem1 mem2 v1 v2)
      (V2: v2 <= ts):
  v1 = v2.
Proof.
  apply SIM. ss.
Qed.

Lemma sim_val_const
      ts mem1 mem2 c:
  sim_val ts mem1 mem2 (ValA.mk _ c bot) (ValA.mk _ c bot).
Proof.
  econs; splits; ss; try apply bot_spec.
  ii. inv TS2.
Qed.

Lemma sim_view_bot
      ts mem1 mem2:
  sim_view ts mem1 mem2 bot bot.
Proof.
  econs; splits; ss; try apply bot_spec.
  ii. inv TS2.
Qed.

Lemma sim_view_const
      ts mem1 mem2 c
      (C1: c <= ts)
      (C2: c <= length mem1)
      (C3: c <= length mem2):
  sim_view ts mem1 mem2 (View.mk c bot) (View.mk c bot).
Proof.
  econs; ss. ii. lia.
Qed.

Lemma sim_view_join
      ts mem1 mem2 l1 l2 r1 r2
      (VIEW1: sim_view ts mem1 mem2 l1 r1)
      (VIEW2: sim_view ts mem1 mem2 l2 r2):
  sim_view ts mem1 mem2 (join l1 l2) (join r1 r2).
Proof.
  destruct l1 as [lt1 lv1].
  destruct l2 as [lt2 lv2].
  destruct r1 as [rt1 rv1].
  destruct r2 as [rt2 rv2].
  inv VIEW1. inv VIEW2. econs; ss.
  - i. rewrite TS, TS0; ss.
    + rewrite <- H, <- join_r. ss.
    + rewrite <- H, <- join_l. ss.
  - apply join_spec; ss.
  - apply join_spec; ss.
  - ii. apply Time.max_le in TS2. des.
    + eapply ITF; eauto.
      eapply latest_mon; eauto. apply join_l.
    + eapply ITF0; eauto.
      eapply latest_mon; eauto. apply join_r.
Qed.

Lemma sim_view_ifc
      ts mem1 mem2 c l1 r1
      (VIEW1: sim_view ts mem1 mem2 l1 r1):
  sim_view ts mem1 mem2 (ifc c l1) (ifc c r1).
Proof.
  destruct c; ss. apply sim_view_bot.
Qed.

Lemma sim_view_eq
      ts mem1 mem2 v1 v2
      (SIM: sim_view ts mem1 mem2 v1 v2)
      (V2: v2.(View.ts) <= ts):
  v1 = v2.
Proof.
  apply SIM. ss.
Qed.

Lemma sim_val_view ts mem1 mem2 v1 v2
      (VAL: sim_val ts mem1 mem2 v1 v2):
  sim_view ts mem1 mem2 v1.(ValA.annot) v2.(ValA.annot).
Proof.
  inv VAL. econs; ss. i. rewrite TS; ss.
Qed.

Lemma sim_rmap_expr
      ts mem1 mem2 rmap1 rmap2 e
      (RMAP: sim_rmap ts mem1 mem2 rmap1 rmap2):
  sim_val ts mem1 mem2 (sem_expr rmap1 e) (sem_expr rmap2 e).
Proof.
  induction e; s.
  - apply sim_val_const.
  - unfold RMap.find. inv RMAP. specialize (RMAP0 reg). inv RMAP0; ss.
    apply sim_val_const.
  - inv IHe. econs; ss.
    i. rewrite TS; ss.
  - inv IHe1. inv IHe2. econs; ss.
    + i. rewrite TS, TS0; ss.
      * rewrite <- H, <- join_r. ss.
      * rewrite <- H, <- join_l. ss.
    + apply join_spec; ss.
    + apply join_spec; ss.
    + ii. apply Time.max_le in TS2. des.
      * eapply ITF; eauto.
        eapply latest_mon; eauto. apply join_l.
      * eapply ITF0; eauto.
        eapply latest_mon; eauto. apply join_r.
Qed.

Lemma sim_rmap_add
      ts mem1 mem2 rmap1 rmap2 v1 v2 r
      (RMAP: sim_rmap ts mem1 mem2 rmap1 rmap2)
      (VAL: sim_val ts mem1 mem2 v1 v2):
  sim_rmap ts mem1 mem2 (RMap.add r v1 rmap1) (RMap.add r v2 rmap2).
Proof.
  inv RMAP. econs. ii. unfold RMap.add. rewrite ? IdMap.add_spec.
  condtac; ss. inversion e. subst. econs. ss.
Qed.

Lemma sim_mem_read
      tid ts mem1 mem2 loc ts0
      (SIM: sim_mem tid ts mem1 mem2)
      (TS0: ts0 <= ts):
  Memory.read loc ts0 mem1 = Memory.read loc ts0 mem2.
Proof.
  inv SIM. unfold Memory.read. destruct ts0; ss. rewrite ? nth_error_app1; ss.
Qed.

Lemma sim_mem_get_msg
      tid ts mem1 mem2 ts0
      (SIM: sim_mem tid ts mem1 mem2)
      (TS0: ts0 <= ts):
  Memory.get_msg ts0 mem1 = Memory.get_msg ts0 mem2.
Proof.
  inv SIM. unfold Memory.get_msg. destruct ts0; ss. rewrite ? nth_error_app1; ss.
Qed.

Lemma sim_mem_length
      tid ts mem1 mem2
      (SIM: sim_mem tid ts mem1 mem2):
  ts <= length mem1 /\ ts <= length mem2.
Proof.
  inv SIM. rewrite ? List.app_length. splits; lia.
Qed.

Lemma sim_view_val
      ts mem1 mem2 c v1 v2
      (SIM: sim_view ts mem1 mem2 v1 v2):
  sim_val ts mem1 mem2 (ValA.mk _ c v1) (ValA.mk _ c v2).
Proof.
  inv SIM. econs; ss. i. rewrite TS; ss.
Qed.

Lemma sim_eu_step
      tid ts eu1 eu2 eu2'
      (SIM: sim_eu tid ts eu1 eu2)
      (STEP: certify_step tid eu2 eu2')
      (WF1: ExecUnit.wf tid eu1)
      (WF2: ExecUnit.wf tid eu2)
      (VCAP: eu2'.(ExecUnit.local).(Local.vcap).(View.ts) <= ts):
  exists eu1',
    <<STEP: certify_step tid eu1 eu1'>> /\
    <<SIM: sim_eu tid ts eu1' eu2'>>.
Proof.
  exploit certify_step_wf; eauto. i.
  destruct eu1 as [[stmts1 rmap1] lc1 mem1].
  destruct eu2 as [[stmts2 rmap2] lc2 mem2].
  destruct eu2' as [[stmts2' rmap2'] lc2' mem2'].
  inv SIM. inv STATE. ss. subst. inv STEP; cycle 1.
  { (* write step *)
    admit.
  }
  { (* state step *)
    inv STEP0. inv STEP. ss. subst. inv STATE; inv LOCAL0; inv EVENT.
    - (* skip *)
      eexists (ExecUnit.mk _ _ _). esplits.
      + econs 1. econs. econs; ss; cycle 1.
        * econs 1; eauto.
        * s. econs 1.
      + econs; ss.
    - (* assign *)
      eexists (ExecUnit.mk _ _ _). esplits.
      + econs 1. econs. econs; ss; cycle 1.
        * econs 1; eauto.
        * s. econs 2. ss.
      + econs; ss. econs; ss; try by apply LOCAL.
        apply sim_rmap_add; ss. apply sim_rmap_expr. ss.
    - (* read *)
      inv STEP.
      match goal with
      | [|- context[join (joins ?l) ?f]] =>
        remember (join (joins l) f) as post eqn:POST
      end.
      guardH POST.
      ss. exploit sim_rmap_expr; eauto. instantiate (1 := eloc). intro X. inv X.
      exploit TS.
      { rewrite <- VCAP, <- join_r. ss. }
      intro ELOC. rewrite ELOC in *. clear TS.
      inv LOCAL.
      destruct (le_lt_dec ts0 ts).
      { (* Case 1: tgt read <= ts. *)
        exploit sim_fwd_view1; eauto.
        { exploit sim_mem_length; eauto. i. des. ss. }
        { exploit sim_mem_length; eauto. i. des. ss. }
        { rewrite <- COH. apply WF2. }
        intro FWDVIEW.
        eexists (ExecUnit.mk _ _ _). esplits.
        - econs 1. econs. econs; ss.
          + econs; ss.
          + rewrite ELOC in *.
            econs 2; eauto. instantiate (2 := ts0). econs; ss.
            * exploit COH0; eauto. intro X. inv X. rewrite TS; ss.
              rewrite COH. ss.
            * admit. (* Memory.latest *)
            * admit. (* Memory.read *)
        - econs; ss.
          + econs; ss. apply sim_rmap_add; ss. apply sim_view_val.
            rewrite POST. eauto 10 using sim_view_join, sim_view_ifc, sim_view_bot.
          + econs; ss; try by rewrite ? POST; eauto 10 using sim_view_join, sim_view_ifc, sim_view_bot.
            * i. rewrite ? fun_add_spec. condtac; ss. admit. (* easy *)
            * destruct ex0; ss. econs. econs; ss.
              { admit. (* easy *) }
              { i. admit. (* WRONG : TODO *) }
              { rewrite POST. eauto 10 using sim_view_join, sim_view_ifc, sim_view_bot. }
      }
      (* Case 2: tgt read > ts. *)
      destruct (le_lt_dec post.(View.ts) ts).
      { (* if post-view <= ts, then read should be forwarded. *)
        admit.
        (* rename l0 into POST'. *)
        (* exploit sim_fwd_view2; eauto. *)
        (* { exploit sim_mem_length; eauto. i. des. ss. } *)
        (* { exploit sim_mem_length; eauto. i. des. ss. } *)
        (* { rewrite <- POST', POST. s. rewrite <- join_l, <- join_l. refl. } *)
        (* i. des. subst. *)
        (* eexists (ExecUnit.mk _ _ _). esplits. *)
        (* - econs 1. econs. econs; ss. *)
        (*   + econs; ss. *)
        (*   + rewrite ELOC in *. *)
        (*     econs 2; eauto. instantiate (2 := (FwdItem.ts (Local.fwdbank lc1 (ValA.val (sem_expr rmap2 eloc))))). econs; ss. *)
        (*     * rewrite COH1. ss. *)
        (*     * admit. (* Memory.latest *) *)
        (*     * rewrite READ, MSG. ss. *)
        (* - econs; ss. *)
        (*   + econs; ss. apply sim_rmap_add; ss. apply sim_view_val. *)
        (*     rewrite POST. eauto 10 using sim_view_join, sim_view_ifc. *)
        (*   + econs; ss; try by rewrite ? POST; eauto 10 using sim_view_join, sim_view_ifc. *)
        (*     * i. rewrite ? fun_add_spec. condtac; ss. econs. lia. *)
        (*     * i. rewrite ? fun_add_spec. condtac; ss. inversion e. subst. econs 3; ss. *)
        (*     * destruct ex0; ss. econs. econs; ss. *)
        (*       { econs. lia. } *)
        (*       { rewrite POST. eauto 10 using sim_view_join, sim_view_ifc. } *)
      }
      { (* if post-view > ts, then read the latest message. *)
        admit.
        (* exploit Memory.get_latest; eauto. i. des. *)
        (* eexists (ExecUnit.mk _ _ _). esplits. *)
        (* - econs 1. econs. econs; ss. *)
        (*   + econs; ss. *)
        (*   + rewrite ELOC in *. *)
        (*     econs 2; eauto. instantiate (2 := ts1). econs; ss. *)
        (*     * admit. (* coh <= ts1 *) *)
        (*     * admit. (* Memory.latest *) *)
        (*     * eauto. *)
        (* - econs; ss. *)
        (*   + econs; ss. apply sim_rmap_add; ss. econs. s. lia. *)
        (*   + econs; ss; try by rewrite ? POST; eauto 10 using sim_view_join, sim_view_ifc. *)
        (*     * i. rewrite ? fun_add_spec. condtac; ss. inversion e. subst. econs. lia. *)
        (*     * apply sim_view_join; ss. unfold ifc. condtac; ss. econs. lia. *)
        (*     * apply sim_view_join; ss. unfold ifc. condtac; ss. econs. lia. *)
        (*     * apply sim_view_join; ss. econs. lia. *)
        (*     * i. rewrite ? fun_add_spec. condtac; ss. inversion e. subst. *)
        (*       admit. (* sim fwdbank *) *)
        (*     * destruct ex0; ss. econs. econs; ss. *)
        (*       { econs. lia. } *)
        (*       { econs. lia. } *)
      }
    - (* fulfill *)
      inv STEP.
      destruct (le_lt_dec ts0 ts).
      { (* fulfilling a promise <= ts. *)
        rename l into TS0.
        exploit sim_rmap_expr; eauto. i. inv x1. exploit TS.
        { rewrite <- TS0. inv WRITABLE. etrans; [|by apply Time.lt_le_incl; eauto].
          s. rewrite <- join_l. eauto.
        }
        intro ELOC. clear TS.
        exploit sim_rmap_expr; eauto. i. inv x1. exploit TS.
        { rewrite <- TS0. inv WRITABLE. etrans; [|by apply Time.lt_le_incl; eauto].
          s. rewrite <- join_r, <- join_l. eauto.
        }
        intro EVAL. clear TS.
        eexists (ExecUnit.mk _ _ _). esplits.
        + econs 1. econs. econs; ss; cycle 1.
          * econs 3; eauto. econs; eauto; cycle 1.
            { rewrite <- MSG. eapply sim_mem_get_msg; eauto. }
            { inv LOCAL. rewrite PROMISES1; ss. }
            { instantiate (1 := view_ext).
              instantiate (1 := ord).
              instantiate (1 := ex0).
              inv WRITABLE. econs; eauto.
              - symmetry. eapply sim_view_eq; cycle 1.
                { etrans; [by apply Time.lt_le_incl; eauto|]. eauto. }
                s. repeat apply sim_view_join; ss.
                all: try apply sim_view_ifc.
                all: try apply sim_view_bot.
                all: try by apply LOCAL.
                all: admit.
              - exploit sim_time_eq.
                { inv LOCAL. eapply COH0. }
                { etrans; [by apply Time.lt_le_incl; eauto|]. eauto. }
                i. congr.
              - i. specialize (EX H). des. inv LOCAL. rewrite TSX in *. inv EXBANK.
                destruct a, eb. inv REL. ss. subst.
                esplits; eauto. s. ii. subst.
                inv WF2. ss. inv LOCAL. exploit EXBANK; eauto. s. i. des.
                admit.
                (* destruct (le_lt_dec ts2 ts). *)
                (* { inv TS. specialize (TS3 l). subst. *)
                (*   eapply EX0; eauto. rewrite <- MSG0. inv MEM. *)
                (*   exploit (EQUIV (S ts3)). *)
                (*   { lia. } *)
                (*   unfold Memory.get_msg, Memory.read. ss. *)
                (* } *)
                (* { lia. } *)
            }
          * econs 4; ss.
        + econs; ss.
          { econs; ss. apply sim_rmap_add; ss.
            admit.
          }
          inv LOCAL. econs; ss; i.
          all: repeat rewrite fun_add_spec.
          all: repeat apply sim_view_join; ss.
          all: try condtac; ss.
          * admit. (* easy *)
          * admit. (* easy *)
          * admit.
          * admit.
          * admit.
          * rewrite ? Promises.unset_o. condtac; ss. eauto.
          * rewrite Promises.unset_o. condtac; ss. eauto.
      }
      { (* fulfilling a new promise > ts (only in tgt) *)
        admit.
      }
    - (* write_failure *)
      inv STEP. eexists (ExecUnit.mk _ _ _). esplits.
      + econs 1. econs. econs; ss; cycle 1.
        * econs 4; eauto. econs; eauto.
        * econs 4; ss.
      + econs; ss. econs; ss; eauto using sim_rmap_add, sim_val_const.
        inv LOCAL. econs; ss.
    - (* isb *)
      inv STEP. eexists (ExecUnit.mk _ _ _). esplits.
      + econs 1. econs. econs; ss; cycle 1.
        * econs 5; eauto. econs; eauto.
        * econs 5.
      + econs; ss. inv LOCAL. econs; eauto using sim_view_join.
    - (* dmb *)
      inv STEP. eexists (ExecUnit.mk _ _ _). esplits.
      + econs 1. econs. econs; ss; cycle 1.
        * econs 6; eauto. econs; eauto.
        * econs 5.
      + econs; ss. inv LOCAL. econs; eauto 10 using sim_view_join, sim_view_ifc, sim_view_bot.
    - (* if *)
      inv LC. eexists (ExecUnit.mk _ _ _). esplits.
      + econs 1. econs. econs; ss; cycle 1.
        * econs 7; eauto. econs; eauto.
        * econs; ss.
      + exploit sim_rmap_expr; eauto. i. inv x1. exploit TS.
        { rewrite <- VCAP. s. rewrite <- join_r. refl. }
        intro ELOC. econs; ss.
        { econs; ss. rewrite ELOC. ss. }
        econs; ss; try by apply LOCAL.
        apply sim_view_join; try by apply LOCAL.
        rewrite ELOC. admit. (* sim_view refl *)
    - (* dowhile *)
      eexists (ExecUnit.mk _ _ _). esplits.
      + econs 1. econs. econs; ss; cycle 1.
        * econs 1; eauto.
        * econs 7. ss.
      + econs; ss.
  }
Admitted.

Lemma sim_eu_promises
      tid ts eu1 eu2
      (SIM: sim_eu tid ts eu1 eu2)
      (EU2: forall tsp (TSP: tsp <= ts), Promises.lookup tsp eu2.(ExecUnit.local).(Local.promises) = false):
  eu1.(ExecUnit.local).(Local.promises) = bot.
Proof.
  apply Promises.ext. i. rewrite Promises.lookup_bot.
  inv SIM. inv LOCAL. destruct (le_dec i ts).
  - rewrite PROMISES1, EU2; ss.
  - rewrite PROMISES2; ss. lia.
Qed.

Lemma sim_eu_rtc_step
      tid ts eu1 eu2 eu2'
      (SIM: sim_eu tid ts eu1 eu2)
      (STEP: rtc (certify_step tid) eu2 eu2')
      (WF1: ExecUnit.wf tid eu1)
      (WF2: ExecUnit.wf tid eu2)
      (PROMISES: eu2'.(ExecUnit.local).(Local.promises) = bot):
  exists eu1',
    <<STEP: rtc (certify_step tid) eu1 eu1'>> /\
    <<PROMISES: eu1'.(ExecUnit.local).(Local.promises) = bot>>.
Proof.
  revert eu1 SIM WF1 WF2. induction STEP; ss.
  { esplits; eauto.
    eapply sim_eu_promises; eauto. rewrite PROMISES.
    i. rewrite Promises.lookup_bot. ss.
  }
  i. destruct (le_lt_dec (View.ts (Local.vcap (ExecUnit.local y))) ts).
  - exploit sim_eu_step; eauto. i. des.
    exploit certify_step_wf; try exact H; eauto. i.
    exploit certify_step_wf; eauto. i.
    exploit IHSTEP; eauto. i. des.
    esplits; [|by eauto]. econs; eauto.
  - esplits; eauto. eapply sim_eu_promises; eauto. i.
    assert (PROMISES': forall tsp (TSP: tsp <= ts), Promises.lookup tsp y.(ExecUnit.local).(Local.promises) = false).
    { admit. }
    destruct x as [st1 lc1 mem1].
    destruct y as [st2 lc2 mem2].
    ss. inv H.
    + inv STEP0. inv STEP1. ss. subst.
      inv STATE; inv LOCAL; inv EVENT; ss.
      all: eauto.
      all: try inv STEP0; ss; eauto.
      all: try inv LC; ss; eauto.
      generalize (PROMISES' tsp TSP). rewrite Promises.unset_o. condtac; ss. inversion e. subst.
      inv WRITABLE. ss. admit. (* easy *)
    + inv STEP0. ss. admit. (* quite the same *)
Admitted.

Lemma state_step_certify
      tid eu1 eu2
      (CERTIFY: certify tid eu2)
      (STEP: ExecUnit.state_step tid eu1 eu2):
  certify tid eu1.
Proof.
  inv CERTIFY. econs; [|by eauto]. econs; eauto.
Qed.

Lemma promise_step_certify
      tid eu1 eu2
      (CERTIFY: certify tid eu2)
      (STEP: ExecUnit.promise_step tid eu1 eu2)
      (WF: ExecUnit.wf tid eu1):
  certify tid eu1.
Proof.
  destruct (classic (eu1.(ExecUnit.local).(Local.promises) = bot)).
  { econs; eauto. }
  rename H into PROMISES.

  assert (SIM: sim_eu tid (length eu1.(ExecUnit.mem)) eu1 eu2).
  { destruct eu1 as [st1 lc1 mem1].
    destruct eu2 as [st2 lc2 mem2].
    inv STEP. inv LOCAL. ss. subst. inv MEM2. subst. econs; ss.
    - econs; ss. econs. ii.
      destruct (IdMap.find id (State.rmap st2)) eqn:FIND; ss. econs.
      inv WF. ss. inv STATE. exploit RMAP; eauto. unfold RMap.find. rewrite FIND. i.
      econs; ss.
      + rewrite List.app_length. s. lia.
      + ii. eapply LAT; eauto. apply nth_error_app_mon. ss.
    - admit. (* sim_lc; easy *)
    - econs; ss. rewrite app_nil_r. ss.
  }

  inv CERTIFY. exploit sim_eu_rtc_step; eauto.
  { eapply ExecUnit.promise_step_wf; eauto. }
  i. des. econs; eauto.
Admitted.

Lemma interference_certify
      tid st lc mem mem_interference
      (CERTIFY: certify tid (ExecUnit.mk st lc (mem ++ mem_interference)))
      (WF: ExecUnit.wf tid (ExecUnit.mk st lc mem)):
  certify tid (ExecUnit.mk st lc mem).
Proof.
  destruct (classic (lc.(Local.promises) = bot)).
  { econs; eauto. }
  rename H into PROMISES.

  assert (SIM: sim_eu tid (length mem) (ExecUnit.mk st lc mem) (ExecUnit.mk st lc (mem ++ mem_interference))).
  { econs; ss.
    - econs; ss. econs. ii.
      destruct (IdMap.find id (State.rmap st)) eqn:FIND; ss. econs.
      inv WF. ss. inv STATE. exploit RMAP; eauto. unfold RMap.find. rewrite FIND. i.
      econs; ss.
      + rewrite List.app_length. s. lia.
      + ii. eapply LAT; eauto. apply nth_error_app_mon. ss.
    - admit. (* sim_lc; easy *)
    - econs; ss. rewrite app_nil_r. ss.
  }

  inv CERTIFY. exploit sim_eu_rtc_step; eauto.
  { admit. (* wf preserved *) }
  i. des. econs; eauto.
Admitted.
