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
Require Import Algorithmic.

Set Implicit Arguments.


Inductive sim_time (ts:Time.t) (v1 v2:Time.t): Prop :=
| sim_time_intro
    (TS: v2 <= ts -> v1 = v2)
.
Hint Constructors sim_time.

Inductive sim_view (ts:Time.t) (forbid:Taint.t) (v1 v2:View.t (A:=Taint.t)): Prop :=
| sim_view_intro
    (TS: v2.(View.ts) <= ts ->
         v1 = v2 /\
         v2.(View.annot) ∩₁ forbid ⊆₁ bot)
.
Hint Constructors sim_view.

Inductive sim_val (ts:Time.t) (forbid:Taint.t) (v1 v2:ValA.t (A:=View.t (A:=Taint.t))): Prop :=
| sim_val_intro
    (TS: v2.(ValA.annot).(View.ts) <= ts ->
         v1 = v2 /\
         v2.(ValA.annot).(View.annot) ∩₁ forbid ⊆₁ bot)
.
Hint Constructors sim_val.

Inductive sim_rmap (ts:Time.t) (forbid:Taint.t) (rmap1 rmap2:RMap.t (A:=View.t (A:=Taint.t))): Prop :=
| sim_rmap_intro
    (RMAP: IdMap.Forall2
             (fun _ => (sim_val ts forbid))
             rmap1 rmap2)
.
Hint Constructors sim_rmap.

Inductive sim_state (ts:Time.t) (forbid:Taint.t) (st1 st2:State.t (A:=View.t (A:=Taint.t))): Prop :=
| sim_state_intro
    (STMTS: st1.(State.stmts) = st2.(State.stmts))
    (RMAP: sim_rmap ts forbid st1.(State.rmap) st2.(State.rmap))
.
Hint Constructors sim_state.

Inductive sim_lc (ts:Time.t) (forbid:Taint.t) (lc1 lc2:Local.t (A:=Taint.t)): Prop :=
| sim_lc_intro
    (COH: forall loc, sim_time ts (lc1.(Local.coh) loc) (lc2.(Local.coh) loc))
    (VRP: sim_view ts forbid lc1.(Local.vrp) lc2.(Local.vrp))
    (VWP: sim_view ts forbid lc1.(Local.vwp) lc2.(Local.vwp))
    (VRM: sim_view ts forbid lc1.(Local.vrm) lc2.(Local.vrm))
    (VWM: sim_view ts forbid lc1.(Local.vwm) lc2.(Local.vwm))
    (VCAP: sim_view ts forbid lc1.(Local.vcap) lc2.(Local.vcap))
    (VREL: sim_view ts forbid lc1.(Local.vrel) lc2.(Local.vrel))
    (FWDBANK: forall loc,
        opt_rel
          (fun fwd1 fwd2 =>
             fwd2.(FwdItem.ts) <= ts ->
             (fwd1.(FwdItem.ts) = fwd2.(FwdItem.ts) /\
              sim_view ts forbid fwd1.(FwdItem.view) fwd2.(FwdItem.view) /\
              fwd1.(FwdItem.ex) = fwd2.(FwdItem.ex)))
          (lc1.(Local.fwdbank) loc) (lc2.(Local.fwdbank) loc))
    (EXBANK: opt_rel
               (fun exbank1 exbank2 => True)
               lc1.(Local.exbank) lc2.(Local.exbank))
    (PROMISES: lc1.(Local.promises) = lc2.(Local.promises))
    (PROMISES_TS: forall mid (FIND: Promises.lookup mid lc1.(Local.promises)), mid <= ts)
.
Hint Constructors sim_lc.

Inductive sim_mem (tid:Id.t) (ts:Time.t) (forbid:Taint.t) (mem1 mem2:Memory.t): Prop :=
| sim_mem_intro
    mem_prefix mem1' mem2' msg
    (LEN: ts = length mem_prefix)
    (MEM: mem1 = mem_prefix ++ mem1')
    (MEM: mem2 = mem_prefix ++ msg :: mem2')
    (TID: List.Forall (fun msg => msg.(Msg.tid) = tid) mem1')
    (TID: List.Forall (fun msg => msg.(Msg.tid) = tid) mem2')
    (MSG: msg.(Msg.tid) <> tid)
    (FORBID: forbid = (fun taint => exists id, taint = Taint.R id 0))
.
Hint Constructors sim_mem.

Inductive sim_eu (tid:Id.t) (ts:Time.t) (forbid:Taint.t) (eu1 eu2:ExecUnit.t (A:=Taint.t)): Prop :=
| sim_eu_intro
    (STATE: sim_state ts forbid eu1.(ExecUnit.state) eu2.(ExecUnit.state))
    (LOCAL: sim_lc ts forbid eu1.(ExecUnit.local) eu2.(ExecUnit.local))
    (MEM: sim_mem tid ts forbid eu1.(ExecUnit.mem) eu2.(ExecUnit.mem))
.
Hint Constructors sim_eu.

Inductive sim_aeu (tid:Id.t) (ts:Time.t) (forbid:Taint.t) (aeu1 aeu2:AExecUnit.t): Prop :=
| sim_aeu_intro
    (EU: sim_eu tid ts forbid aeu1.(AExecUnit.eu) aeu2.(AExecUnit.eu))
    (AUX: aeu1.(AExecUnit.aux) = aeu2.(AExecUnit.aux))
    (AUX_FORBID: aeu2.(AExecUnit.aux).(AExecUnit.taint) ∩₁ forbid ⊆₁ bot)
.
Hint Constructors sim_aeu.

Inductive sim_event ts forbid: forall (e1 e2:Event.t (A:=View.t (A:=Taint.t))), Prop :=
| sim_event_internal
    ctrl1 ctrl2
    (CTRL: sim_view ts forbid ctrl1 ctrl2):
    sim_event ts forbid (Event.internal ctrl1) (Event.internal ctrl2)
| sim_event_read
    ex ord vloc1 vloc2 res1 res2
    (VLOC: sim_val ts forbid vloc1 vloc2)
    (RES: sim_val ts forbid res1 res2):
    sim_event ts forbid (Event.read ex ord vloc1 res1) (Event.read ex ord vloc2 res2)
| sim_event_write
    ex ord vloc1 vloc2 vval1 vval2 res1 res2
    (VLOC: sim_val ts forbid vloc1 vloc2)
    (VVAL: sim_val ts forbid vval1 vval2)
    (RES: sim_val ts forbid res1 res2):
    sim_event ts forbid (Event.write ex ord vloc1 vval1 res1) (Event.write ex ord vloc2 vval2 res2)
| sim_event_barrier
    b:
    sim_event ts forbid (Event.barrier b) (Event.barrier b)
.

Lemma sim_time_join
      ts l1 l2 r1 r2
      (VIEW1: sim_time ts l1 r1)
      (VIEW2: sim_time ts l2 r2):
  sim_time ts (join l1 l2) (join r1 r2).
Proof.
  inv VIEW1. inv VIEW2.
  econs. intro X. unfold join, Time.join in X. apply Time.max_lub_iff in X. des.
  eauto.
Qed.

Lemma sim_val_const
      ts forbid c:
  sim_val ts forbid (ValA.mk _ c bot) (ValA.mk _ c bot).
Proof.
  econs. s. i. splits; ss. ii. inv H0. ss.
Qed.

Lemma sim_view_bot
      ts forbid:
  sim_view ts forbid bot bot.
Proof.
  econs. i. splits; ss. ii. inv H0. ss.
Qed.

Lemma sim_view_const
      ts forbid c:
  sim_view ts forbid (View.mk c bot) (View.mk c bot).
Proof.
  econs. i. splits; ss. ii. inv H0. ss.
Qed.

Lemma sim_view_join
      ts forbid l1 l2 r1 r2
      (VIEW1: sim_view ts forbid l1 r1)
      (VIEW2: sim_view ts forbid l2 r2):
  sim_view ts forbid (join l1 l2) (join r1 r2).
Proof.
  destruct l1 as [lt1 lv1].
  destruct l2 as [lt2 lv2].
  destruct r1 as [rt1 rv1].
  destruct r2 as [rt2 rv2].
  inv VIEW1. inv VIEW2. ss.
  econs. s. intro X. unfold join, Time.join in X. apply Time.max_lub_iff in X. des.
  specialize (TS X). specialize (TS0 X0). des. inv TS. inv TS0.
  splits; ss. ii. inv H. inv H0.
  - apply TS2. ss.
  - apply TS1. ss.
Qed.

Lemma sim_val_view ts forbid v1 v2
      (VAL: sim_val ts forbid v1 v2):
  sim_view ts forbid v1.(ValA.annot) v2.(ValA.annot).
Proof.
  inv VAL. econs. i. specialize (TS H). des. subst. ss.
Qed.

Lemma sim_rmap_expr
      ts forbid rmap1 rmap2 e
      (RMAP: sim_rmap ts forbid rmap1 rmap2):
  sim_val ts forbid (sem_expr rmap1 e) (sem_expr rmap2 e).
Proof.
  induction e; s.
  - apply sim_val_const.
  - unfold RMap.find. inv RMAP. specialize (RMAP0 reg). inv RMAP0; ss.
    apply sim_val_const.
  - econs. s. i. inv IHe. specialize (TS H). des. splits; ss. congr.
  - econs. s. i. unfold join, Time.join in H. apply Time.max_lub_iff in H. des.
    inv IHe1. inv IHe2.
    specialize (TS H). specialize (TS0 H0). des. splits; ss.
    + congr.
    + ii. inv H1. inv H2.
      * apply TS2. ss.
      * apply TS1. ss.
Qed.

Lemma sim_rmap_add
      ts forbid rmap1 rmap2 v1 v2 r
      (RMAP: sim_rmap ts forbid rmap1 rmap2)
      (VAL: sim_val ts forbid v1 v2):
  sim_rmap ts forbid (RMap.add r v1 rmap1) (RMap.add r v2 rmap2).
Proof.
  inv RMAP. econs. ii. unfold RMap.add. rewrite ? IdMap.add_spec.
  condtac; ss. inversion e. subst. econs. ss.
Qed.

Lemma sim_lc_step
      ts forbid tid
      e2 mem1 mem2
      (lc1 lc2 lc2':Local.t (A:=Taint.t))
      (STEP:  Local.step e2 tid mem2 lc2 lc2')
      (MEM: sim_mem tid ts forbid mem1 mem2)
      (LC: sim_lc ts forbid lc1 lc2)
      (EVENT: sim_event ts forbid e2 e2):
  exists e1 lc1',
    <<STEP: Local.step e1 tid mem1 lc1 lc1'>> /\
    <<LC: sim_lc ts forbid lc1' lc2'>> /\
    <<EVENT: sim_event ts forbid e1 e2>>.
Proof.
  inv LC. inv STEP.
  - (* internal *)
    inv LC. esplits.
    + econs 1; ss.
    + econs; ss. apply sim_view_join; ss.
      admit. (* sim_view ctrl *)
    + eauto.
  - (* read *)
    inv STEP0. destruct (le_dec ts0 ts).
    + (* read from old msg. *)
      esplits.
      * econs 2; eauto. econs; eauto.
        { etrans; [|exact COH0].
          specialize (COH (ValA.val vloc)). inv COH. rewrite TS; ss.
          etrans; eauto.
        }
        { admit. (* memory no_msgs *) }
        { admit. (* memory read *) }
      * econs; ss.
        { i. rewrite ? fun_add_spec. condtac; ss. }
        { apply sim_view_join; [by ss|].
          instantiate (1 := ord). destruct (OrdR.ge ord OrdR.acquire_pc); eauto using sim_view_bot.
          s. repeat apply sim_view_join.
          - inv EVENT. inv VLOC. econs. i. specialize (TS H). des.
            splits; ss.
          - ss.
          - destruct (OrdR.ge ord OrdR.acquire); ss. apply sim_view_bot.
          - apply sim_view_bot.
          - specialize (FWDBANK (ValA.val vloc)). inv FWDBANK.
            + apply sim_view_const.
            + admit. (* fwd *)
        }
        { admit. (* sim_view *) }
        { admit. (* sim_view *) }
        { admit. (* sim_view *) }
        { admit. (* exbank *) }
      * admit. (* event *)
    + (* read from new msg. *)
      admit.
  - (* write *)
    admit.
  - (* write_failure *)
    admit.
  - (* isb *)
    admit.
  - (* dmbst *)
    admit.
  - (* dmbld *)
    admit.
  - (* dmbsy *)
    admit.
Admitted.

Lemma sim_state_step
      ts forbid e1 e2 (st1 st2 st2':State.t (A:=View.t (A:=Taint.t)))
      (EVENT: sim_event ts forbid e1 e2)
      (STEP: State.step e2 st2 st2')
      (SIM: sim_state ts forbid st1 st2):
  exists st1',
    <<STEP: State.step e1 st1 st1'>> /\
    <<SIM: sim_state ts forbid st1' st2'>>.
Proof.
  destruct st1 as [stmts1 rmap1].
  destruct st2 as [stmts2 rmap2].
  inv SIM. ss. subst. inv STEP; inv EVENT.
  - inv CTRL. exploit TS; [by apply bot_spec|]. i. des. subst.
    esplits; ss.
    + econs 1; ss.
    + econs; ss.
  - inv CTRL. exploit TS; [by apply bot_spec|]. i. des. subst.
    esplits; ss.
    + econs 2; ss.
    + econs; ss. apply sim_rmap_add; ss. apply sim_rmap_expr. ss.
  - esplits; ss.
    + econs 3; ss.
      admit. (* sim_event dead end.. *)
    + econs; ss. apply sim_rmap_add; ss.
  - (* write *)
    admit.
  - (* barrier *)
    admit.
  - (* if *)
    admit.
  - (* dowhile *)
    admit.
Admitted.

Lemma sim_aeu_step
      tid ts forbid aeu1 aeu2 aeu2'
      (SIM: sim_aeu tid ts forbid aeu1 aeu2)
      (STEP: AExecUnit.step tid aeu2 aeu2'):
  exists aeu1',
    <<STEP: AExecUnit.step tid aeu1 aeu1'>> /\
    <<SIM: sim_aeu tid ts forbid aeu1' aeu2'>>.
Proof.
  destruct aeu1 as [[[stmts1 rmap1] lc1 mem1] aux1].
  destruct aeu2 as [[[stmts2 rmap2] lc2 mem2] aux2].
  destruct aeu2' as [[[stmts2' rmap2'] lc2' mem2'] aux2'].
  inv STEP.
  - (* state_step *)
    inv STEP0. ss. subst.
    inv SIM. ss. subst.
    inv EU. ss.
    inv STATE0. ss. subst.
    inv STATE; inv LOCAL; inv H0.
    + (* skip *)
      inv LC.
      eexists (AExecUnit.mk (ExecUnit.mk _ _ _) _). esplits.
      * left. econs; ss.
        { instantiate (2 := Event.internal bot). s. econs 1. }
        econs; eauto. econs; eauto.
      * econs; ss. econs; ss. inv LOCAL0. econs; ss.
        apply sim_view_join; ss. apply sim_view_bot.
    + (* assign *)
      inv LC.
      eexists (AExecUnit.mk (ExecUnit.mk _ _ _) _). esplits.
      * left. econs; ss.
        { instantiate (2 := Event.internal bot). s. econs 2. eauto. }
        econs; eauto. econs; eauto.
      * econs; ss. econs; ss.
        { econs; ss. apply sim_rmap_add; ss. apply sim_rmap_expr. ss. }
        { inv LOCAL0. econs; ss. eauto using sim_view_join, sim_view_bot. }
    + (* read *)
      admit.
    + (* fulfill *)
      admit.
    + (* write_failure *)
      inv STEP.
      eexists (AExecUnit.mk (ExecUnit.mk _ _ _) _). esplits.
      * left. econs; ss.
        { instantiate (2 := Event.write _ _ _ _ _). s. econs 4; eauto. }
        econs 4; eauto. econs; eauto.
      * econs; ss; cycle 1.
        { ii. apply AUX_FORBID. inv H. econs; ss. inv H0; ss. }
        econs; ss.
        { econs; ss. apply sim_rmap_add; ss. apply sim_val_const. }
        { econs; try by apply LOCAL0. ss. }
    + (* isb *)
      admit.
    + (* dmbst *)
      admit.
    + (* dmbld *)
      admit.
    + (* dmbsy *)
      admit.
    + (* if *)
      inv LC.
      eexists (AExecUnit.mk (ExecUnit.mk _ _ _) _). esplits.
      * left. econs; ss.
        { instantiate (2 := Event.internal _). s. econs 6; eauto. }
        econs; eauto. econs; eauto.
      * econs; ss. econs; ss.
        { econs; ss.
          exploit sim_rmap_expr; eauto. instantiate (1 := cond). i.
          inv x0. exploit TS; cycle 1.
          { i. des. rewrite x. ss. }
          admit. (* not depend on big ts *)
        }
        { inv LOCAL0. econs; ss. apply sim_view_join; ss.
          apply sim_val_view. apply sim_rmap_expr. ss.
        }
    + (* dowhile *)
      inv LC.
      eexists (AExecUnit.mk (ExecUnit.mk _ _ _) _). esplits.
      * left. econs; ss.
        { instantiate (2 := Event.internal bot). s. econs 7. ss. }
        econs; eauto. econs; eauto.
      * econs; ss. econs; ss. inv LOCAL0. econs; ss.
        eauto using sim_view_join, sim_view_bot.
  - (* write_step *)
    admit.
Admitted.

Lemma sim_aeu_rtc_step
      tid ts forbid aeu1 aeu2 aeu2'
      (SIM: sim_aeu tid ts forbid aeu1 aeu2)
      (STEP: rtc (AExecUnit.step tid) aeu2 aeu2'):
  exists aeu1',
    <<STEP: rtc (AExecUnit.step tid) aeu1 aeu1'>> /\
    <<SIM: sim_aeu tid ts forbid aeu1' aeu2'>>.
Proof.
  revert aeu1 SIM. induction STEP.
  { i. esplits; eauto. }
  i. exploit sim_aeu_step; eauto. i. des.
  exploit IHSTEP; eauto. i. des.
  esplits; [|by eauto]. econs; eauto.
Qed.

Lemma certify_lift_diff
      tid (eu1 eu2:ExecUnit.t (A:=unit)) locks msg
      (CERTIFY: certify tid eu2 locks)
      (WF: ExecUnit.wf eu1)
      (ST: eu2.(ExecUnit.state) = eu1.(ExecUnit.state))
      (LC: eu2.(ExecUnit.local) = eu1.(ExecUnit.local))
      (MEM: eu2.(ExecUnit.mem) = eu1.(ExecUnit.mem) ++ [msg])
      (MSG: msg.(Msg.tid) <> tid):
  <<CERTIFY: certify tid eu1 locks>> /\
  <<NOLOCK: forall lock (LOCK: locks lock), ~ (lock.(Lock.loc) = msg.(Msg.loc) /\ lock.(Lock.from) = 0)>>.
Proof.
  destruct eu1 as [st1 lc1 mem1].
  destruct eu2 as [st2 lc2 mem2].
  ss. subst. inv CERTIFY.
  exploit sim_aeu_rtc_step; eauto.
  { instantiate (1 := AExecUnit.init (ExecUnit.mk st1 lc1 mem1)). econs; ss.
    - econs; ss; cycle 2.
      + econs; ss. rewrite List.app_nil_r. ss.
      + econs; ss. econs. ii.
        unfold AExecUnit.init_rmap. rewrite IdMap.map_spec.
        destruct (IdMap.find id (State.rmap st1)); ss. econs. econs; ss.
        splits; ss. ii. inv H0. ss.
      + unfold AExecUnit.init_lc, AExecUnit.init_view.
        econs; ss; eauto using sim_view_const.
        * admit. (* TODO: bug on init vcap *)
        * i. destruct (Local.fwdbank lc1 loc); ss. econs; ss.
          splits; ss. apply sim_view_const.
        * admit. (* TODO: bug on exbank rel *)
        * inv WF. inv LOCAL. ss.
    - ii. inv H. inv H0.
  }
  i. des. esplits.
  - econs; eauto.
    + inv SIM. inv EU. inv LOCAL. etrans; eauto.
    + inv SIM. congr.
  - ii. des. destruct lock as [loc from to guarantee]. ss. subst.
    inv LOCK. ss. inv SIM. eapply AUX_FORBID. econs; cycle 1; eauto.
Admitted.
