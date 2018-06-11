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

Inductive sim_exbank (tid:Id.t) (mem1 mem2:Memory.t) (ts1 ts2:Time.t): Prop :=
| sim_exbank_intro
    (EXBANK: forall loc,
        Memory.exclusive tid loc ts2 (length mem2) mem2 ->
        Memory.exclusive tid loc ts1 (length mem1) mem1)
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
      (STEP: AExecUnit.step tid aeu2 aeu2'):
  exists aeu1',
    <<STEP: AExecUnit.step tid aeu1 aeu1'>> /\
    <<SIM: sim_aeu tid ts aeu1' aeu2'>>.
Proof.
  destruct aeu1 as [[[stmts1 rmap1] lc1 mem1] aux1].
  destruct aeu2 as [[[stmts2 rmap2] lc2 mem2] aux2].
  destruct aeu2' as [[[stmts2' rmap2'] lc2' mem2'] aux2'].
  inv STEP.
  { (* state_step *)
    inv STEP0. inv STEP. ss. subst.
    inv SIM. ss. subst.
    inv EU. ss.
    inv STATE0. ss. subst.
    inv LOCAL; ss; inv STATE.
    - (* skip *)
      inv LC.
      eexists (AExecUnit.mk (ExecUnit.mk _ _ _) _). esplits.
      + left. econs; ss. econs; ss; cycle 1.
        * econs 1; eauto. econs; eauto.
        * s. econs 1.
      + econs; ss. econs; ss.
        inv LOCAL0. econs; ss.
        apply sim_low_view_join; ss. apply sim_low_view_bot.
    - (* assign *)
      inv LC.
      eexists (AExecUnit.mk (ExecUnit.mk _ _ _) _). esplits.
      + left. econs; ss. econs; ss; cycle 1.
        * econs 1; eauto. econs; eauto.
        * s. econs 2. ss.
      + econs; ss. econs; ss.
        * econs; ss. apply sim_rmap_add; ss. apply sim_rmap_expr. ss.
        * inv LOCAL0. econs; ss. eauto using sim_low_view_join, sim_low_view_bot.
    - (* if *)
      inv LC.
      eexists (AExecUnit.mk (ExecUnit.mk _ _ _) _). esplits.
      + left. econs; ss. econs; ss; cycle 1.
        * econs 1; eauto. econs; eauto.
        * s. econs 6; ss.
      + econs; ss.
        assert (LOC_VIEW: View.ts (ValA.annot (sem_expr rmap2' cond)) <= ts).
        { admit. (* MOVE: not depend on big ts of cond *) }
        econs; ss.
        * econs; ss.
          exploit sim_rmap_expr; eauto. i.
          inv x0. exploit TS; eauto. i. des. rewrite x. ss.
        * inv LOCAL0. econs; ss. apply sim_low_view_join; ss.
          apply sim_view_low_view; ss. apply sim_val_view. apply sim_rmap_expr. ss.
    - (* dowhile *)
      inv LC.
      eexists (AExecUnit.mk (ExecUnit.mk _ _ _) _). esplits.
      + left. econs; ss. econs; ss; cycle 1.
        * econs 1; eauto. econs; eauto.
        * s. econs 7. ss.
      + econs; ss. econs; ss. inv LOCAL0. econs; ss.
        eauto using sim_low_view_join, sim_low_view_bot.
    - (* read *)
      inv STEP. destruct (le_dec ts0 ts).
      { (* read from old msg. *)
        eexists (AExecUnit.mk (ExecUnit.mk _ _ _) _). esplits.
        - left. econs; ss. econs; ss; cycle 1.
          + econs 2; eauto. econs.
            4: instantiate (1 := ts0).
            1: instantiate (1 := (sem_expr rmap1 eloc)).
            all: ss.
            * rewrite <- COH.
              admit. (* not depend on big ts of loc *)
            * hexploit sim_rmap_expr; eauto. intro X. inv X.
              exploit TS.
              { admit. (* not depend on big ts of loc *) }
              i. des. rewrite x.
              admit. (* memory no_msgs *)
            * admit. (* memory read *)
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
      eexists (AExecUnit.mk (ExecUnit.mk _ _ _) _). esplits.
      + left. econs; ss. econs; ss; cycle 1.
        * econs 4; eauto. econs; eauto.
        * s. econs 4; ss.
      + econs; ss. econs; ss; eauto using sim_rmap_add, sim_val_const.
        inv LOCAL0. econs; ss.
    - (* isb *)
      inv STEP.
      eexists (AExecUnit.mk (ExecUnit.mk _ _ _) _). esplits.
      + left. econs; ss. econs; ss; cycle 1.
        * econs 5; eauto. econs; eauto.
        * s. econs 5.
      + econs; ss. econs; ss.
        inv LOCAL0. econs; ss; eauto using sim_low_view_join, sim_low_view_bot.
    - (* dmbst *)
      inv STEP.
      eexists (AExecUnit.mk (ExecUnit.mk _ _ _) _). esplits.
      + left. econs; ss. econs; ss; cycle 1.
        * econs 6; eauto. econs; eauto.
        * s. econs 5.
      + econs; ss. econs; ss.
        inv LOCAL0. econs; ss.
        admit. (* big vwp *)
        (* eauto using sim_low_view_join, sim_low_view_bot. *)
    - (* dmbld *)
      inv STEP.
      eexists (AExecUnit.mk (ExecUnit.mk _ _ _) _). esplits.
      + left. econs; ss. econs; ss; cycle 1.
        * econs 7; eauto. econs; eauto.
        * s. econs 5.
      + econs; ss. econs; ss.
        inv LOCAL0. econs; ss.
        all: admit. (* big vwp *)
        (* eauto using sim_low_view_join, sim_low_view_bot. *)
    - (* dmbsy *)
      inv STEP.
      eexists (AExecUnit.mk (ExecUnit.mk _ _ _) _). esplits.
      + left. econs; ss. econs; ss; cycle 1.
        * econs 8; eauto. econs; eauto.
        * s. econs 5.
      + econs; ss. econs; ss.
        inv LOCAL0. econs; ss.
        all: admit. (* big vwp *)
        (* eauto using sim_low_view_join, sim_low_view_bot. *)
  }
  { (* write_step *)
    admit.
  }
Admitted.

Lemma sim_aeu_rtc_step
      tid ts aeu1 aeu2 aeu2'
      (SIM: sim_aeu tid ts aeu1 aeu2)
      (STEP: rtc (AExecUnit.step tid) aeu2 aeu2'):
  exists aeu1',
    <<STEP: rtc (AExecUnit.step tid) aeu1 aeu1'>> /\
    <<SIM: sim_aeu tid ts aeu1' aeu2'>>.
Proof.
  revert aeu1 SIM. induction STEP.
  { i. esplits; eauto. }
  i. exploit sim_aeu_step; eauto. i. des.
  exploit IHSTEP; eauto. i. des.
  esplits; [|by eauto]. econs; eauto.
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
    + apply Memory.get_msg_snoc_inv in MSG0. des; eauto.
      subst. ss.
Qed.

Inductive sound_taint (loc:Loc.t) (v:Taint.t): Prop :=
| sound_taint_intro
    (TAINT: forall from to, ~ v (Taint.W from to loc))
.

Inductive sound_view (loc:Loc.t) (v:View.t (A:=Taint.t)): Prop :=
| sound_view_intro
    (VIEW: sound_taint loc v.(View.annot))
.

Inductive sound_val (loc:Loc.t) (v:ValA.t (A:=View.t (A:=Taint.t))): Prop :=
| sound_val_intro
    (VAL: sound_view loc v.(ValA.annot))
.

Inductive sound_st (loc:Loc.t) (st:State.t (A:=View.t (A:=Taint.t))): Prop :=
| sound_st_intro
    (RMAP: IdMap.Forall (fun _ => sound_val loc) st.(State.rmap))
.

Inductive sound_lc (is_first_ex:bool) (ts:Time.t) (loc:Loc.t) (lc:Local.t (A:=Taint.t)): Prop :=
| sound_lc_intro
    (VRP: sound_view loc lc.(Local.vrp))
    (VWP: sound_view loc lc.(Local.vwp))
    (VRM: sound_view loc lc.(Local.vrm))
    (VWM: sound_view loc lc.(Local.vwm))
    (VCAP: sound_view loc lc.(Local.vcap))
    (VREL: sound_view loc lc.(Local.vrel))
    (FWDBANK: forall l fwd (FWD: lc.(Local.fwdbank) l = Some fwd), sound_view loc fwd.(FwdItem.view))
    (EXBANK: is_first_ex -> forall exbank (EXBANK: lc.(Local.exbank) = Some exbank), exbank <= ts)
.

Inductive sound_aeu (loc:Loc.t) (ts:Time.t) (aeu:AExecUnit.t): Prop :=
| sound_aeu_intro
    (ST: sound_st loc aeu.(ExecUnit.state))
    (LC: sound_lc (aeu.(AExecUnit.aux).(AExecUnit.ex_counter) == 0) ts loc aeu.(ExecUnit.local))
    (AUX: sound_taint loc aeu.(AExecUnit.aux).(AExecUnit.taint))
.

Lemma sound_aeu_step
      loc ts tid aeu1 aeu2
      (STEP: AExecUnit.step tid aeu1 aeu2)
      (SOUND: sound_aeu loc ts aeu1):
  sound_aeu loc ts aeu2.
Proof.
  destruct aeu1 as [[st1 lc1 mem1] aux1].
  destruct aeu2 as [[st2 lc2 mem2] aux2].
  inv SOUND. ss. inv STEP.
  { inv STEP0. inv STEP. ss. subst.
    inv ST. inv LC.
    inv LOCAL; inv STATE; ss. 
    - inv LC. econs; ss. econs; ss.
      admit. (* soudn view bot join *)
    - inv LC. econs; ss.
      + admit. (* sound rmap addd expr *)
      + econs; ss. admit. (* soudn view bot join *)
    - inv LC. econs; ss.
      econs; ss. admit. (* sound join expr *)
    - inv LC. econs; ss.
      econs; ss. admit. (* sound join bot *)
    - inv STEP. econs; ss.
      + econs; ss. admit.
      + admit.
      + destruct ex; ss.
    - inv STEP. econs; ss.
      + econs; ss. admit.
      + admit.
      + admit.
    - inv STEP. econs; ss.
      + econs; ss. admit.
      + admit.
    - inv STEP. econs; ss.
      econs; ss. admit.
    - inv STEP. econs; ss.
      econs; ss. admit.
    - inv STEP. econs; ss.
      econs; ss.
      admit.
      admit.
    - inv STEP. econs; ss.
      econs; ss.
      admit.
      admit.
  }
  { inv STEP0. ss. subst.
    inv ST. inv LC.
    inv LOCAL. inv STATE. econs; ss.
    - econs; ss. admit.
    - econs; ss.
      all: admit.
  }
Admitted.

Lemma sound_rtc_aeu_step
      loc ts tid aeu1 aeu2
      (STEP: rtc (AExecUnit.step tid) aeu1 aeu2)
      (SOUND: sound_aeu loc ts aeu1):
  sound_aeu loc ts aeu2.
Proof.
  revert SOUND. induction STEP; ss. i. exploit sound_aeu_step; eauto.
Qed.

Lemma certify_diff_not_locked
      tid (eu:ExecUnit.t (A:=unit)) lock mem msg
      (CERTIFY: certify tid eu lock)
      (WF: ExecUnit.wf tid eu)
      (MEM: eu.(ExecUnit.mem) = mem ++ [msg])
      (MSG: msg.(Msg.tid) <> tid):
  ~ Lock.is_locked lock bot msg.(Msg.loc).
Proof.
  inv CERTIFY.
  exploit sound_rtc_aeu_step; eauto.
  { instantiate (1 := (length mem)).
    instantiate (1 := msg.(Msg.loc)).
    destruct eu as [st1 lc1 mem1]. ss. subst.
    econs.
    - econs. s. ii. revert FIND.
      unfold AExecUnit.init_rmap. rewrite IdMap.map_spec.
      destruct (IdMap.find id (State.rmap st1)); ss. i. inv FIND.
      econs. econs. econs. ss.
    - s. admit.
    - econs. ss.
  }
  ii. destruct lock as [ex release]. ss. subst.
  inv H. destruct exlock as [from to loc]. ss. subst.
  inv RANGE. inv H. inv LOCK. ss.
  eapply x0. eauto.
Admitted.

Lemma lift_certify_diff
      tid (eu1 eu2:ExecUnit.t (A:=unit)) lock msg
      (CERTIFY: certify tid eu2 lock)
      (WF: ExecUnit.wf tid eu1)
      (ST: eu2.(ExecUnit.state) = eu1.(ExecUnit.state))
      (LC: eu2.(ExecUnit.local) = eu1.(ExecUnit.local))
      (MEM: eu2.(ExecUnit.mem) = eu1.(ExecUnit.mem) ++ [msg])
      (MSG: msg.(Msg.tid) <> tid):
  <<CERTIFY: certify tid eu1 lock>> /\
  <<NOLOCK: ~ Lock.is_locked lock bot msg.(Msg.loc)>>.
Proof.
  exploit lift_wf; eauto. i.
  splits; cycle 1.
  { eapply certify_diff_not_locked; eauto. }
  destruct eu1 as [st1 lc1 mem1].
  destruct eu2 as [st2 lc2 mem2].
  ss. subst. inv CERTIFY.
  exploit sim_aeu_rtc_step; eauto.
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
        * apply Memory.read_mon. eauto.
        * rewrite app_length. lia.
        * exploit nth_error_Some. rewrite MSG0. intros [X _]. exploit X; ss. i.
          rewrite nth_error_app1; ss.
  }
  i. des.
  econs; eauto.
  - inv SIM. inv EU. inv LOCAL. etrans; eauto.
  - inv SIM. congr.
  - inv SIM. congr.
Qed.
