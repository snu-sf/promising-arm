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


Inductive sim_time (ts:Time.t) (v1 v2:Time.t): Prop :=
| sim_time_intro
    (TS: v2 <= ts -> v1 = v2)
.
Hint Constructors sim_time.

Inductive sim_view (ts:Time.t) (v1 v2:View.t (A:=Taint.t)): Prop :=
| sim_view_intro
    (TS: v2.(View.ts) <= ts -> v1 = v2)
.
Hint Constructors sim_view.

Inductive sim_low_view (ts:Time.t) (v1 v2:View.t (A:=Taint.t)): Prop :=
| sim_low_view_intro
    (TS: v2.(View.ts) <= ts)
    (VAL: v1 = v2)
.
Hint Constructors sim_low_view.

Inductive sim_val (ts:Time.t) (v1 v2:ValA.t (A:=View.t (A:=Taint.t))): Prop :=
| sim_val_intro
    (TS: v2.(ValA.annot).(View.ts) <= ts -> v1 = v2)
.
Hint Constructors sim_val.

Inductive sim_rmap (ts:Time.t) (rmap1 rmap2:RMap.t (A:=View.t (A:=Taint.t))): Prop :=
| sim_rmap_intro
    (RMAP: IdMap.Forall2 (fun _ => sim_val ts) rmap1 rmap2)
.
Hint Constructors sim_rmap.

Inductive sim_state (ts:Time.t) (st1 st2:State.t (A:=View.t (A:=Taint.t))): Prop :=
| sim_state_intro
    (STMTS: st1.(State.stmts) = st2.(State.stmts))
    (RMAP: sim_rmap ts st1.(State.rmap) st2.(State.rmap))
.
Hint Constructors sim_state.

Inductive sim_exbank (tid:Id.t) (mem1 mem2:Memory.t) (lts1 lts2:Loc.t * Time.t): Prop :=
| sim_exbank_intro
    (LOC: lts1.(fst) = lts2.(fst))
    (EXBANK: Memory.exclusive tid lts2.(fst) lts2.(snd) (length mem2) mem2 ->
             Memory.exclusive tid lts1.(fst) lts1.(snd) (length mem1) mem1)
.

Inductive sim_lc (tid:Id.t) (ts:Time.t) (lc1 lc2:Local.t (A:=Taint.t)) (mem1 mem2:Memory.t): Prop :=
| sim_lc_intro
    (COH: forall loc, sim_time ts (lc1.(Local.coh) loc) (lc2.(Local.coh) loc))
    (VRP: sim_low_view ts lc1.(Local.vrp) lc2.(Local.vrp))
    (VWP: sim_low_view ts lc1.(Local.vwp) lc2.(Local.vwp))
    (VRM: sim_view ts lc1.(Local.vrm) lc2.(Local.vrm))
    (VWM: sim_view ts lc1.(Local.vwm) lc2.(Local.vwm))
    (VCAP: sim_low_view ts lc1.(Local.vcap) lc2.(Local.vcap))
    (VREL: sim_low_view ts lc1.(Local.vrel) lc2.(Local.vrel))
    (FWDBANK: forall loc,
        opt_rel
          (fun fwd1 fwd2 =>
             fwd2.(FwdItem.ts) <= ts ->
             (fwd1.(FwdItem.ts) = fwd2.(FwdItem.ts) /\
              sim_low_view ts fwd1.(FwdItem.view) fwd2.(FwdItem.view) /\
              fwd1.(FwdItem.ex) = fwd2.(FwdItem.ex)))
          (lc1.(Local.fwdbank) loc) (lc2.(Local.fwdbank) loc))
    (EXBANK: opt_rel (sim_exbank tid mem1 mem2) lc1.(Local.exbank) lc2.(Local.exbank))
    (PROMISES: lc1.(Local.promises) = lc2.(Local.promises))
    (PROMISES_TS: forall mid (FIND: Promises.lookup mid lc1.(Local.promises)), mid <= ts)
.
Hint Constructors sim_lc.

Inductive sim_mem (tid:Id.t) (ts:Time.t) (mem1 mem2:Memory.t): Prop :=
| sim_mem_intro
    mem_prefix mem1' mem2' msg
    (LEN: ts = length mem_prefix)
    (MEM: mem1 = mem_prefix ++ mem1')
    (MEM: mem2 = mem_prefix ++ msg :: mem2')
    (TID: List.Forall (fun msg => msg.(Msg.tid) = tid) mem1')
    (TID: List.Forall (fun msg => msg.(Msg.tid) = tid) mem2')
    (MSG: msg.(Msg.tid) <> tid)
.
Hint Constructors sim_mem.

Inductive sim_eu (tid:Id.t) (ts:Time.t) (eu1 eu2:ExecUnit.t (A:=Taint.t)): Prop :=
| sim_eu_intro
    (STATE: sim_state ts eu1.(ExecUnit.state) eu2.(ExecUnit.state))
    (LOCAL: sim_lc tid ts eu1.(ExecUnit.local) eu2.(ExecUnit.local) eu1.(ExecUnit.mem) eu2.(ExecUnit.mem))
    (MEM: sim_mem tid ts eu1.(ExecUnit.mem) eu2.(ExecUnit.mem))
.
Hint Constructors sim_eu.

Inductive sim_aeu (tid:Id.t) (ts:Time.t) (aeu1 aeu2:AExecUnit.t): Prop :=
| sim_aeu_intro
    (EU: sim_eu tid ts aeu1.(AExecUnit.eu) aeu2.(AExecUnit.eu))
    (AUX: aeu1.(AExecUnit.aux) = aeu2.(AExecUnit.aux))
| sim_aeu_exit
    (PROMISES1: aeu1.(ExecUnit.local).(Local.promises) = bot)
    (PROMISES2: aeu2.(ExecUnit.local).(Local.promises) = bot)
    (TAINT: aeu1.(AExecUnit.aux).(AExecUnit.taint) = aeu2.(AExecUnit.aux).(AExecUnit.taint))
    (RELEASE: aeu1.(AExecUnit.aux).(AExecUnit.release) = aeu2.(AExecUnit.aux).(AExecUnit.release))
.
Hint Constructors sim_aeu.

Inductive sim_event ts: forall (e1 e2:Event.t (A:=View.t (A:=Taint.t))), Prop :=
| sim_event_internal
    ctrl1 ctrl2
    (CTRL: sim_view ts ctrl1 ctrl2):
    sim_event ts (Event.internal ctrl1) (Event.internal ctrl2)
| sim_event_read
    ex ord vloc1 vloc2 res1 res2
    (VLOC: sim_val ts vloc1 vloc2)
    (RES: sim_val ts res1 res2):
    sim_event ts (Event.read ex ord vloc1 res1) (Event.read ex ord vloc2 res2)
| sim_event_write
    ex ord vloc1 vloc2 vval1 vval2 res1 res2
    (VLOC: sim_val ts vloc1 vloc2)
    (VVAL: sim_val ts vval1 vval2)
    (RES: sim_val ts res1 res2):
    sim_event ts (Event.write ex ord vloc1 vval1 res1) (Event.write ex ord vloc2 vval2 res2)
| sim_event_barrier
    b:
    sim_event ts (Event.barrier b) (Event.barrier b)
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
      ts c:
  sim_val ts (ValA.mk _ c bot) (ValA.mk _ c bot).
Proof.
  econs. ss.
Qed.

Lemma sim_view_bot
      ts:
  sim_view ts bot bot.
Proof.
  econs. ss.
Qed.

Lemma sim_view_const
      ts c:
  sim_view ts (View.mk c bot) (View.mk c bot).
Proof.
  econs. ss.
Qed.

Lemma sim_view_join
      ts l1 l2 r1 r2
      (VIEW1: sim_view ts l1 r1)
      (VIEW2: sim_view ts l2 r2):
  sim_view ts (join l1 l2) (join r1 r2).
Proof.
  destruct l1 as [lt1 lv1].
  destruct l2 as [lt2 lv2].
  destruct r1 as [rt1 rv1].
  destruct r2 as [rt2 rv2].
  inv VIEW1. inv VIEW2. ss.
  econs. s. intro X. unfold join, Time.join in X. apply Time.max_lub_iff in X. des.
  specialize (TS X). specialize (TS0 X0). des. inv TS. inv TS0. ss.
Qed.

Lemma sim_view_low_view
      ts l r
      (VIEW: sim_view ts l r)
      (TS: r.(View.ts) <= ts):
  sim_low_view ts l r.
Proof.
  inv VIEW. specialize (TS0 TS). des. econs; ss.
Qed.

Lemma sim_low_view_bot
      ts:
  sim_low_view ts bot bot.
Proof.
  econs; ss. apply bot_spec.
Qed.

Lemma sim_low_view_const
      ts c
      (TS: c <= ts):
  sim_low_view ts (View.mk c bot) (View.mk c bot).
Proof.
  econs; ss.
Qed.

Lemma sim_low_view_join
      ts l1 l2 r1 r2
      (VIEW1: sim_low_view ts l1 r1)
      (VIEW2: sim_low_view ts l2 r2):
  sim_low_view ts (join l1 l2) (join r1 r2).
Proof.
  destruct l1 as [lt1 lv1].
  destruct l2 as [lt2 lv2].
  destruct r1 as [rt1 rv1].
  destruct r2 as [rt2 rv2].
  inv VIEW1. inv VIEW2. ss. inv VAL. inv VAL0.
  econs; ss. apply join_spec; ss.
Qed.

Lemma sim_val_view ts v1 v2
      (VAL: sim_val ts v1 v2):
  sim_view ts v1.(ValA.annot) v2.(ValA.annot).
Proof.
  inv VAL. econs. i. specialize (TS H). des. subst. ss.
Qed.

Lemma sim_rmap_expr
      ts rmap1 rmap2 e
      (RMAP: sim_rmap ts rmap1 rmap2):
  sim_val ts (sem_expr rmap1 e) (sem_expr rmap2 e).
Proof.
  induction e; s.
  - apply sim_val_const.
  - unfold RMap.find. inv RMAP. specialize (RMAP0 reg). inv RMAP0; ss.
  - econs. s. i. inv IHe. specialize (TS H). des. congr.
  - econs. s. i. unfold join, Time.join in H. apply Time.max_lub_iff in H. des.
    inv IHe1. inv IHe2.
    specialize (TS H). specialize (TS0 H0). des. congr.
Qed.

Lemma sim_rmap_add
      ts rmap1 rmap2 v1 v2 r
      (RMAP: sim_rmap ts rmap1 rmap2)
      (VAL: sim_val ts v1 v2):
  sim_rmap ts (RMap.add r v1 rmap1) (RMap.add r v2 rmap2).
Proof.
  inv RMAP. econs. ii. unfold RMap.add. rewrite ? IdMap.add_spec.
  condtac; ss. inversion e. subst. econs. ss.
Qed.

Lemma sim_aeu_step
      tid ts aeu1 aeu2 aeu2'
      (SIM: sim_aeu tid ts aeu1 aeu2)
      (STEP: AExecUnit.step tid aeu2 aeu2')
      (WF1: ExecUnit.wf tid aeu1)
      (WF2: ExecUnit.wf tid aeu2)
      (VWP: aeu2'.(ExecUnit.local).(Local.vwp).(View.ts) <= ts)
      (VCAP: aeu2'.(ExecUnit.local).(Local.vcap).(View.ts) <= ts):
  exists aeu1',
    <<STEP: rtc (AExecUnit.step tid) aeu1 aeu1'>> /\
    <<SIM: sim_aeu tid ts aeu1' aeu2'>>.
Proof.
  exploit AExecUnit.step_wf; eauto. intro WF2'.
  destruct aeu1 as [[[stmts1 rmap1] lc1 mem1] aux1].
  destruct aeu2 as [[[stmts2 rmap2] lc2 mem2] aux2].
  destruct aeu2' as [[[stmts2' rmap2'] lc2' mem2'] aux2'].
  ss.

  inv SIM; ss; cycle 1.
  { inv STEP; inv STEP0; ss. }
  inv STEP.
  { (* state_step *)
    inv STEP0. inv STEP. ss. subst.
    inv EU. ss.
    assert (PROMISES1: lc1.(Local.promises) <> bot).
    { inv LOCAL0. ss. congr. }
    inv STATE0. ss. subst.
    inv LOCAL; ss; inv STATE.
    - (* skip *)
      inv LC.
      eexists (AExecUnit.mk (ExecUnit.mk _ _ _) _). esplits; [econs 2; [|econs 1]|].
      + left. econs; ss. econs; ss; cycle 1.
        * econs 1; eauto. econs; eauto.
        * s. econs 1.
      + econs; ss. econs; ss.
        inv LOCAL0. econs; ss.
        apply sim_low_view_join; ss. apply sim_low_view_bot.
    - (* assign *)
      inv LC.
      eexists (AExecUnit.mk (ExecUnit.mk _ _ _) _). esplits; [econs 2; [|econs 1]|].
      + left. econs; ss. econs; ss; cycle 1.
        * econs 1; eauto. econs; eauto.
        * s. econs 2. ss.
      + econs; ss. econs; ss.
        * econs; ss. apply sim_rmap_add; ss. apply sim_rmap_expr. ss.
        * inv LOCAL0. econs; ss. eauto using sim_low_view_join, sim_low_view_bot.
    - (* if *)
      inv LC.
      eexists (AExecUnit.mk (ExecUnit.mk _ _ _) _). esplits; [econs 2; [|econs 1]|].
      + left. econs; ss. econs; ss; cycle 1.
        * econs 1; eauto. econs; eauto.
        * s. econs 6; ss.
      + econs; ss.
        assert (LOC_VIEW: View.ts (ValA.annot (sem_expr rmap2' cond)) <= ts).
        { rewrite <- VCAP, <- join_r. refl. }
        econs; ss.
        * econs; ss.
          exploit sim_rmap_expr; eauto. i.
          inv x0. exploit TS; eauto. i. des. rewrite x. ss.
        * inv LOCAL0. econs; ss. apply sim_low_view_join; ss.
          apply sim_view_low_view; ss. apply sim_val_view. apply sim_rmap_expr. ss.
    - (* dowhile *)
      inv LC.
      eexists (AExecUnit.mk (ExecUnit.mk _ _ _) _). esplits; [econs 2; [|econs 1]|].
      + left. econs; ss. econs; ss; cycle 1.
        * econs 1; eauto. econs; eauto.
        * s. econs 7. ss.
      + econs; ss. econs; ss. inv LOCAL0. econs; ss.
        eauto using sim_low_view_join, sim_low_view_bot.
    - (* read *)
      inv STEP. destruct (le_dec ts0 ts).
      { (* read from old msg. *)
        eexists (AExecUnit.mk (ExecUnit.mk _ _ _) _). esplits; [econs 2; [|econs 1]|].
        - left. econs; ss.
          assert (ELOC: sem_expr rmap1 eloc = sem_expr rmap2 eloc).
          { eapply sim_rmap_expr; eauto. rewrite <- VCAP, <- join_r. refl. }
          econs; ss; cycle 1.
          + econs 2; eauto. econs.
            4: instantiate (1 := ts0).
            1: instantiate (1 := (sem_expr rmap1 eloc)).
            all: ss.
            all: rewrite ELOC.
            * inv LOCAL0. specialize (COH0 (ValA.val (sem_expr rmap2 eloc))). inv COH0.
              rewrite TS; ss. etrans; eauto.
            * admit. (* hard: coh <= ts0, so no additional messages *)
            * rewrite <- MSG. inv MEM. unfold Memory.read. destruct ts0; ss.
              rewrite ? nth_error_app1; ss.
          + econs 3; ss.
        - econs; ss. econs; ss.
          + admit. (* sim_state *)
          + admit. (* sim_lc *)
      }
      { (* read from new msg. *)
        admit.
      }
    - (* fulfill *)
      admit.
    - (* write_failure *)
      inv STEP.
      eexists (AExecUnit.mk (ExecUnit.mk _ _ _) _). esplits; [econs 2; [|econs 1]|].
      + left. econs; ss. econs; ss; cycle 1.
        * econs 4; eauto. econs; eauto.
        * s. econs 4; ss.
      + econs; ss. econs; ss; eauto using sim_rmap_add, sim_val_const.
        inv LOCAL0. econs; ss.
    - (* isb *)
      inv STEP.
      eexists (AExecUnit.mk (ExecUnit.mk _ _ _) _). esplits; [econs 2; [|econs 1]|].
      + left. econs; ss. econs; ss; cycle 1.
        * econs 5; eauto. econs; eauto.
        * s. econs 5.
      + econs; ss. econs; ss.
        inv LOCAL0. econs; ss; eauto using sim_low_view_join, sim_low_view_bot.
    - (* dmbst *)
      inv STEP.
      eexists (AExecUnit.mk (ExecUnit.mk _ _ _) _). esplits; [econs 2; [|econs 1]|].
      + left. econs; ss. econs; ss; cycle 1.
        * econs 6; eauto. econs; eauto.
        * s. econs 5.
      + econs; ss. econs; ss.
        inv LOCAL0. econs; ss. apply sim_low_view_join; ss. apply sim_view_low_view; ss.
        rewrite <- VWP, <- join_r. refl.
    - (* dmbld *)
      inv STEP.
      eexists (AExecUnit.mk (ExecUnit.mk _ _ _) _). esplits; [econs 2; [|econs 1]|].
      + left. econs; ss. econs; ss; cycle 1.
        * econs 7; eauto. econs; eauto.
        * s. econs 5.
      + econs; ss. econs; ss.
        inv LOCAL0. econs; ss.
        * apply sim_low_view_join; ss. apply sim_view_low_view; ss.
          rewrite <- VWP, <- join_r. refl.
        * apply sim_low_view_join; ss. apply sim_view_low_view; ss.
          rewrite <- VWP, <- join_r. refl.
    - (* dmbsy *)
      inv STEP.
      eexists (AExecUnit.mk (ExecUnit.mk _ _ _) _). esplits; [econs 2; [|econs 1]|].
      + left. econs; ss. econs; ss; cycle 1.
        * econs 8; eauto. econs; eauto.
        * s. econs 5.
      + econs; ss. econs; ss.
        inv LOCAL0. econs; ss.
        * repeat apply sim_low_view_join; eauto using sim_low_view_bot.
          { apply sim_view_low_view; ss. rewrite <- VWP, <- join_r, <- join_l. refl. }
          { apply sim_view_low_view; ss. rewrite <- VWP, <- join_r, <- join_r, <- join_l. refl. }
        * repeat apply sim_low_view_join; eauto using sim_low_view_bot.
          { apply sim_view_low_view; ss. rewrite <- VWP, <- join_r, <- join_l. refl. }
          { apply sim_view_low_view; ss. rewrite <- VWP, <- join_r, <- join_r, <- join_l. refl. }
  }
  { (* write_step *)
    admit.
  }
Admitted.

Lemma sim_aeu_rtc_step
      tid ts aeu1 aeu2 aeu2'
      (SIM: sim_aeu tid ts aeu1 aeu2)
      (STEP: rtc (AExecUnit.step tid) aeu2 aeu2')
      (WF1: ExecUnit.wf tid aeu1)
      (WF2: ExecUnit.wf tid aeu2):
  exists aeu1',
    <<STEP: rtc (AExecUnit.step tid) aeu1 aeu1'>> /\
    <<SIM: sim_aeu tid ts aeu1' aeu2'>>.
Proof.
  revert aeu1 SIM WF1 WF2. induction STEP.
  { i. esplits; eauto. }
  i. exploit sim_aeu_step; eauto.
  { admit. (* vwp *) }
  { admit. (* vcap *) }
  i. des.
  exploit AExecUnit.step_wf; eauto. i.
  exploit AExecUnit.rtc_step_wf; eauto. i.
  exploit IHSTEP; eauto. i. des.
  esplits; [|by eauto]. etrans; eauto.
Admitted.

Inductive sound_taint (loc:Loc.t) (v:Taint.t): Prop :=
| sound_taint_intro
    (TAINT: forall to, ~ v (Taint.W 0 to loc))
.

Definition sound_view (loc:Loc.t) (v:View.t (A:=Taint.t)): Prop :=
  sound_taint loc v.(View.annot).

Definition sound_val (loc:Loc.t) (v:ValA.t (A:=View.t (A:=Taint.t))): Prop :=
  sound_view loc v.(ValA.annot).

Inductive sound_rmap (loc:Loc.t) (rmap:RMap.t (A:=View.t (A:=Taint.t))): Prop :=
| sound_rmap_intro
    (RMAP: IdMap.Forall (fun _ => sound_val loc) rmap)
.

Inductive sound_lc (tid:Id.t) (is_first_ex:Prop) (loc:Loc.t) (lc:Local.t (A:=Taint.t)) (mem:Memory.t): Prop :=
| sound_lc_intro
    (VRP: sound_view loc lc.(Local.vrp))
    (VWP: sound_view loc lc.(Local.vwp))
    (VRM: sound_view loc lc.(Local.vrm))
    (VWM: sound_view loc lc.(Local.vwm))
    (VCAP: sound_view loc lc.(Local.vcap))
    (VREL: sound_view loc lc.(Local.vrel))
    (FWDBANK: forall l fwd (FWD: lc.(Local.fwdbank) l = Some fwd), sound_view loc fwd.(FwdItem.view))
    (EXBANK: forall ts
               (FIRST: is_first_ex)
               (EXBANK: lc.(Local.exbank) = Some (loc, ts)),
        ~ Memory.exclusive tid loc ts (length mem) mem)
.

Inductive sound_aeu (tid:Id.t) (loc:Loc.t) (aeu:AExecUnit.t): Prop :=
| sound_aeu_intro
    (ST: sound_rmap loc aeu.(ExecUnit.state).(State.rmap))
    (LC: sound_lc tid (aeu.(AExecUnit.aux).(AExecUnit.ex_counter) = 0) loc aeu.(ExecUnit.local) aeu.(ExecUnit.mem))
    (AUX: sound_taint loc aeu.(AExecUnit.aux).(AExecUnit.taint))
.

Lemma sound_taint_join
      loc l r
      (L: sound_taint loc l)
      (R: sound_taint loc r):
  sound_taint loc (join l r).
Proof.
  inv L. inv R. econs. ii. inv H.
  - eapply TAINT. eauto.
  - eapply TAINT0. eauto.
Qed.

Lemma sound_taint_bot
      loc:
  sound_taint loc bot.
Proof.
  econs. ss.
Qed.

Lemma sound_view_join
      loc v1 v2
      (V1: sound_view loc v1)
      (V2: sound_view loc v2):
  sound_view loc (join v1 v2).
Proof.
  eapply sound_taint_join; eauto.
Qed.

Lemma sound_view_bot
      loc:
  sound_view loc bot.
Proof.
  econs. apply sound_taint_bot.
Qed.

Lemma sound_view_ifc
      loc cond v
      (V1: sound_view loc v):
  sound_view loc (ifc cond v).
Proof.
  destruct cond; ss. eauto using sound_view_bot.
Qed.

Lemma sound_rmap_expr
      loc rmap e
      (RMAP: sound_rmap loc rmap):
  sound_view loc (sem_expr rmap e).(ValA.annot).
Proof.
  induction e; ss.
  - apply sound_view_bot.
  - unfold RMap.find. destruct (IdMap.find reg rmap) eqn:V.
    + eapply RMAP. eauto.
    + apply sound_view_bot.
  - apply sound_view_join; ss.
Qed.

Lemma sound_rmap_add
      loc l v rmap
      (RMAP: sound_rmap loc rmap)
      (V: sound_val loc v):
  sound_rmap loc (RMap.add l v rmap).
Proof.
  inv RMAP. econs. ii. revert FIND.
  unfold RMap.add. rewrite IdMap.add_spec. condtac.
  - inversion e. i. inv FIND. ss.
  - apply RMAP0.
Qed.

Lemma sound_aeu_step
      loc tid aeu1 aeu2
      (STEP: AExecUnit.step tid aeu1 aeu2)
      (SOUND: sound_aeu tid loc aeu1):
  sound_aeu tid loc aeu2.
Proof.
  destruct aeu1 as [[st1 lc1 mem1] aux1].
  destruct aeu2 as [[st2 lc2 mem2] aux2].
  inv SOUND. ss. inv STEP.
  { inv STEP0. inv STEP. ss. subst.
    inv LC. inv LOCAL; inv STATE; ss.
    - inv LC. econs; ss. econs; ss.
      eauto using sound_view_join, sound_view_bot.
    - inv LC. econs; ss.
      + apply sound_rmap_add; ss.
        econs. apply sound_rmap_expr. ss.
      + econs; ss.
        eauto using sound_view_join, sound_view_bot.
    - inv LC. econs; ss.
      econs; ss.
      apply sound_view_join. ss.
      apply sound_rmap_expr. ss.
    - inv LC. econs; ss.
      econs; ss.
      eauto using sound_view_join, sound_view_bot.
    - inv STEP.
      assert (FWD: sound_view loc
                              match Local.fwdbank lc1 (ValA.val (sem_expr rmap eloc)) with
                              | Some fwd => FwdItem.read_view fwd ts ord
                              | None => {| View.ts := ts; View.annot := bot |}
                              end).
      { destruct (Local.fwdbank lc1 (ValA.val (sem_expr rmap eloc))) eqn:FWD.
        - unfold FwdItem.read_view. condtac; eauto.
          apply sound_taint_bot.
        - apply sound_taint_bot.
      }
      econs; ss.
      + apply sound_rmap_add; ss. s.
        repeat apply sound_taint_join; eauto using sound_taint_bot.
        * apply sound_rmap_expr. ss.
        * destruct (OrdR.ge ord OrdR.acquire); eauto using sound_taint_bot.
        * destruct ex; ss. eauto using sound_taint_bot.
      + econs; ss.
        all: repeat (try apply sound_view_join;
                     try apply sound_view_ifc;
                     eauto using sound_view_bot, sound_rmap_expr).
        i. destruct ex; ss. apply EXBANK; ss.
      + destruct ex; ss.
    - inv STEP.
      assert (VIEW_EXT: sound_taint loc (View.annot view_ext)).
      { inv WRITABLE. repeat apply sound_taint_join; eauto using sound_taint_bot.
        all: try apply sound_rmap_expr; ss.
        all: destruct (OrdW.ge ord OrdW.release); eauto using sound_taint_bot.
      }
      econs; ss.
      + eauto using sound_rmap_add.
      + econs; ss.
        all: repeat apply sound_taint_join; eauto using sound_taint_bot.
        * apply sound_rmap_expr. ss.
        * i. revert FWD. rewrite fun_add_spec. condtac; eauto.
          inversion e. i. inv FWD. s.
          apply sound_taint_join; apply sound_rmap_expr; ss.
        * destruct ex; ss.
      + eauto using sound_taint_join.
    - inv STEP. econs; ss.
      + apply sound_rmap_add; ss. econs. apply sound_view_bot.
      + eauto using sound_taint_join, sound_taint_bot.
    - inv STEP. econs; ss.
      econs; ss. eauto using sound_view_join.
    - inv STEP. econs; ss.
      econs; ss. eauto using sound_view_join.
    - inv STEP. econs; ss.
      econs; ss; eauto using sound_view_join.
    - inv STEP. econs; ss.
      econs; ss; eauto using sound_view_join, sound_view_bot.
  }
  { inv STEP0. ss. subst.
    inv ST. inv LC.
    inv LOCAL. inv STATE.
    assert (VIEW_EXT: sound_taint loc (View.annot view_ext)).
    { inv WRITABLE. repeat apply sound_taint_join; eauto using sound_taint_bot.
      all: try apply sound_rmap_expr; ss.
      all: destruct (OrdW.ge ord OrdW.release); eauto using sound_taint_bot.
    }
    assert (TAINT: sound_taint loc
                               ((fun _ : Taint.elt =>
                                   ex /\
                                   (exists tsx : Time.t, Local.exbank lc1 = Some (ValA.val (sem_expr rmap eloc), tsx)))
                                  ∩ eq (AExecUnit.taint_write ord (ValA.val (sem_expr rmap eloc)) aux1))).
    { econs. ii. inv H. inv H1. des. destruct ex; ss.
      inv WRITABLE. exploit EX; eauto. i. des.
      rewrite TSX in H1. inv H1. specialize (EX0 eq_refl).
      eapply EXBANK; eauto. ii. eapply EX0; eauto.
    }
    econs; ss.
    - apply sound_rmap_add; ss. apply sound_taint_join; ss.
    - econs; ss.
      all: repeat (try apply sound_view_join;
                   try apply sound_view_ifc;
                   eauto using sound_view_bot, sound_rmap_expr).
      + apply sound_rmap_expr. ss.
      + i. revert FWD. rewrite fun_add_spec. condtac; eauto.
        inversion e. i. inv FWD. s.
        repeat apply sound_taint_join; eauto using sound_taint_bot.
        all: try apply sound_rmap_expr; ss.
      + destruct ex; ss. ii. rename H into EX. eapply EXBANK; eauto.
        rewrite app_length in EX. ss.
        ii. eapply EX; eauto.
        * clear -TS2. lia.
        * rewrite nth_error_app1; ss.
  }
Qed.

Lemma sound_rtc_aeu_step
      tid loc aeu1 aeu2
      (STEP: rtc (AExecUnit.step tid) aeu1 aeu2)
      (SOUND: sound_aeu tid loc aeu1):
  sound_aeu tid loc aeu2.
Proof.
  revert SOUND. induction STEP; ss. i. exploit sound_aeu_step; eauto.
Qed.

Lemma lift_wf
      tid (eu1 eu2:ExecUnit.t (A:=unit)) msg
      (WF: ExecUnit.wf tid eu1)
      (ST: eu2.(ExecUnit.state) = eu1.(ExecUnit.state))
      (LC: eu2.(ExecUnit.local) = eu1.(ExecUnit.local))
      (MEM: eu2.(ExecUnit.mem) = eu1.(ExecUnit.mem) ++ [msg])
      (MSG: msg.(Msg.tid) <> tid):
  ExecUnit.wf tid eu2.
Proof.
  destruct eu1 as [st1 lc1 mem1].
  destruct eu2 as [st2 lc2 mem2].
  ss. subst. inv WF. ss. econs; ss.
  - apply ExecUnit.rmap_append_wf. ss.
  - inv LOCAL. econs; try rewrite app_length; intuition.
    + exploit FWDBANK; eauto. i. des. intuition.
    + exploit FWDBANK; eauto. i. des. intuition.
    + exploit EXBANK; eauto. i. des.
      eexists. apply Memory.read_mon. eauto.
    + apply Memory.get_msg_snoc_inv in MSG0. des; eauto.
      subst. ss.
Qed.

Lemma certify_diff_not_locked
      tid (eu1 eu2:ExecUnit.t (A:=unit)) lock msg
      (CERTIFY: certify tid eu2 lock)
      (WF: ExecUnit.wf tid eu1)
      (ST: eu2.(ExecUnit.state) = eu1.(ExecUnit.state))
      (LC: eu2.(ExecUnit.local) = eu1.(ExecUnit.local))
      (MEM: eu2.(ExecUnit.mem) = eu1.(ExecUnit.mem) ++ [msg])
      (MSG: msg.(Msg.tid) <> tid):
  ~ Lock.is_locked lock msg.(Msg.loc).
Proof.
  exploit lift_wf; eauto. i.
  destruct eu1 as [st1 lc1 mem1].
  destruct eu2 as [st2 lc2 mem2].
  ss. subst. inv CERTIFY.
  exploit sound_rtc_aeu_step; eauto.
  { instantiate (1 := msg.(Msg.loc)).
    ss. subst. econs.
    - econs. s. ii. revert FIND.
      unfold AExecUnit.init_rmap. rewrite IdMap.map_spec.
      destruct (IdMap.find id (State.rmap st1)); ss. i. inv FIND.
      econs. econs. econs. ss.
    - s. unfold AExecUnit.init_lc, AExecUnit.init_view. econs; ss.
      all: try by econs; econs; ss.
      + i. destruct (Local.fwdbank lc1 l) eqn:FWDL; ss. inv FWD. ss.
        econs. econs. ss.
      + ii. inv WF. inv LOCAL. ss. exploit EXBANK0; eauto. i. des.
        eapply H; cycle 2.
        { rewrite nth_error_app2; [|refl]. rewrite Nat.sub_diag. ss. }
        { ss. }
        { exploit ExecUnit.read_wf; eauto. i. lia. }
        { rewrite app_length. s. intuition. }
        all: eauto.
    - econs. ss.
  }
  ii. destruct lock as [ex release]. ss. subst.
  inv H. destruct exlock as [from to loc]. ss. subst.
  inv LOCK. ss. eapply x1. eauto.
Qed.

Lemma lift_certify_diff
      tid (eu1 eu2:ExecUnit.t (A:=unit)) lock msg
      (CERTIFY: certify tid eu2 lock)
      (WF: ExecUnit.wf tid eu1)
      (ST: eu2.(ExecUnit.state) = eu1.(ExecUnit.state))
      (LC: eu2.(ExecUnit.local) = eu1.(ExecUnit.local))
      (MEM: eu2.(ExecUnit.mem) = eu1.(ExecUnit.mem) ++ [msg])
      (MSG: msg.(Msg.tid) <> tid):
  certify tid eu1 lock.
Proof.
  exploit lift_wf; eauto. i.
  destruct eu1 as [st1 lc1 mem1].
  destruct eu2 as [st2 lc2 mem2].
  ss. subst. inv CERTIFY.
  exploit sim_aeu_rtc_step; try exact STEPS; eauto.
  { instantiate (1 := AExecUnit.init tid (ExecUnit.mk st1 lc1 mem1)). econs; ss.
    econs; ss; cycle 2.
    - econs; ss. rewrite List.app_nil_r. ss.
    - econs; ss. econs. ii.
      unfold AExecUnit.init_rmap. rewrite IdMap.map_spec.
      destruct (IdMap.find id (State.rmap st1)); ss. econs. econs; ss.
    - unfold AExecUnit.init_lc, AExecUnit.init_view.
      inv WF. ss. inv LOCAL.
      econs; ss; eauto using sim_view_const, sim_low_view_const.
      + i. destruct (Local.fwdbank lc1 loc) eqn:FWD; ss. econs; ss.
        splits; ss. apply sim_low_view_const. eapply FWDBANK. eauto.
      + destruct lc1. s. destruct exbank; ss. econs.
        econs; eauto. ii. eapply H; eauto.
        * rewrite app_length. lia.
        * exploit nth_error_Some. rewrite MSG0. intros [X _]. exploit X; ss. i.
          rewrite nth_error_app1; ss.
  }
  { apply AExecUnit.init_wf. ss. }
  { apply AExecUnit.init_wf. ss. }
  i. des.
  econs; eauto.
  - inv SIM; ss. inv EU. inv LOCAL. etrans; eauto.
  - inv SIM; congr.
  - rewrite RELEASE. inv SIM; ss.
    inv EU. congr.
Qed.
