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

Inductive sim_view (ts:Time.t) (ex:Taint.t) (v1 v2:View.t (A:=Taint.t)): Prop :=
| sim_view_intro
    (TS: v2.(View.ts) <= ts ->
         v1 = v2 /\
         v2.(View.annot) ∩₁ ex = bot)
.
Hint Constructors sim_view.

Inductive sim_val (ts:Time.t) (ex:Taint.t) (v1 v2:ValA.t (A:=View.t (A:=Taint.t))): Prop :=
| sim_val_intro
    (TS: v2.(ValA.annot).(View.ts) <= ts ->
         v1 = v2 /\
         v2.(ValA.annot).(View.annot) ∩₁ ex = bot)
.
Hint Constructors sim_val.

Inductive sim_rmap (ts:Time.t) (ex:Taint.t) (rmap1 rmap2:RMap.t (A:=View.t (A:=Taint.t))): Prop :=
| sim_rmap_intro
    (RMAP: IdMap.Forall2
             (fun _ => (sim_val ts ex))
             rmap1 rmap2)
.
Hint Constructors sim_rmap.

Inductive sim_state (ts:Time.t) (ex:Taint.t) (st1 st2:State.t (A:=View.t (A:=Taint.t))): Prop :=
| sim_state_intro
    (STMTS: st1.(State.stmts) = st2.(State.stmts))
    (RMAP: sim_rmap ts ex st1.(State.rmap) st2.(State.rmap))
.
Hint Constructors sim_state.

Inductive sim_lc (ts:Time.t) (ex:Taint.t) (lc1 lc2:Local.t (A:=Taint.t)): Prop :=
| sim_lc_intro
    (COH: forall loc, sim_time ts (lc1.(Local.coh) loc) (lc2.(Local.coh) loc))
    (VRP: sim_view ts ex lc1.(Local.vrp) lc2.(Local.vrp))
    (VWP: sim_view ts ex lc1.(Local.vwp) lc2.(Local.vwp))
    (VRM: sim_view ts ex lc1.(Local.vrm) lc2.(Local.vrm))
    (VWM: sim_view ts ex lc1.(Local.vwm) lc2.(Local.vwm))
    (VCAP: sim_view ts ex lc1.(Local.vcap) lc2.(Local.vcap))
    (VREL: sim_view ts ex lc1.(Local.vrel) lc2.(Local.vrel))
    (FWDBANK: forall loc,
        opt_rel
          (fun fwd1 fwd2 =>
             fwd2.(FwdItem.ts) <= ts ->
             (fwd1.(FwdItem.ts) = fwd2.(FwdItem.ts) /\
              sim_view ts ex fwd1.(FwdItem.view) fwd2.(FwdItem.view) /\
              fwd1.(FwdItem.ex) = fwd2.(FwdItem.ex)))
          (lc1.(Local.fwdbank) loc) (lc2.(Local.fwdbank) loc))
    (EXBANK: opt_rel
               (fun exbank1 exbank2 => True)
               lc1.(Local.exbank) lc2.(Local.exbank))
    (PROMISES: lc1.(Local.promises) = lc2.(Local.promises))
    (PROMISES_TS: forall mid (FIND: Promises.lookup mid lc1.(Local.promises)), mid <= ts)
.
Hint Constructors sim_lc.

Inductive sim_mem (tid:Id.t) (ts:Time.t) (ex:Taint.t) (mem1 mem2:Memory.t): Prop :=
| sim_mem_intro
    mem_prefix mem1' mem2' msg
    (LEN: ts = length mem_prefix)
    (MEM: mem1 = mem_prefix ++ mem1')
    (MEM: mem2 = mem_prefix ++ msg :: mem2')
    (MSG: msg.(Msg.tid) <> tid)
    (EX: ex = (fun taint => exists id, taint = Taint.R id 0))
.
Hint Constructors sim_mem.

Inductive sim_eu (tid:Id.t) (ts:Time.t) (ex:Taint.t) (eu1 eu2:ExecUnit.t (A:=Taint.t)): Prop :=
| sim_eu_intro
    (STATE: sim_state ts ex eu1.(ExecUnit.state) eu2.(ExecUnit.state))
    (LOCAL: sim_lc ts ex eu1.(ExecUnit.local) eu2.(ExecUnit.local))
    (MEM: sim_mem tid ts ex eu1.(ExecUnit.mem) eu2.(ExecUnit.mem))
.
Hint Constructors sim_eu.

Inductive sim_aeu (tid:Id.t) (ts:Time.t) (ex:Taint.t) (aeu1 aeu2:AExecUnit.t): Prop :=
| sim_aeu_intro
    (EU: sim_eu tid ts ex aeu1.(AExecUnit.eu) aeu2.(AExecUnit.eu))
    (AUX: aeu1.(AExecUnit.aux) = aeu2.(AExecUnit.aux))
    (AUX_EX: aeu2.(AExecUnit.aux).(AExecUnit.taint) ∩₁ ex ⊆₁ bot)
.
Hint Constructors sim_aeu.

Lemma sim_aeu_step
      tid ts ex aeu1 aeu2 aeu2'
      (SIM: sim_aeu tid ts ex aeu1 aeu2)
      (STEP: AExecUnit.step tid aeu2 aeu2'):
  exists aeu1',
    <<STEP: AExecUnit.step tid aeu1 aeu1'>> /\
    <<SIM: sim_aeu tid ts ex aeu1' aeu2'>>.
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
      * econs; ss. econs; ss. econs; try by apply LOCAL0.
        s. rewrite ? bot_join; try by apply View.order. apply LOCAL0.
    + (* assign *)
      inv LC.
      eexists (AExecUnit.mk (ExecUnit.mk _ _ _) _). esplits.
      * left. econs; ss.
        { instantiate (2 := Event.internal bot). s. econs 2. eauto. }
        econs; eauto. econs; eauto.
      * econs; ss. econs; ss.
        { econs; ss. admit. (* sim_rmap add *) }
        { econs; try by apply LOCAL0.
          s. rewrite ? bot_join; try by apply View.order. apply LOCAL0.
        }
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
        { admit. (* join bot *) }
        econs; ss.
        { econs; ss. admit. (* sim_rmap add *) }
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
        { econs; ss. admit. (* sim_rmap add *) }
        { econs; try by apply LOCAL0. s.
          admit. (* sim_view join *)
        }
    + (* dowhile *)
      inv LC.
      eexists (AExecUnit.mk (ExecUnit.mk _ _ _) _). esplits.
      * left. econs; ss.
        { instantiate (2 := Event.internal bot). s. econs 7. ss. }
        econs; eauto. econs; eauto.
      * econs; ss. econs; ss. econs; try by apply LOCAL0.
        s. rewrite ? bot_join; try by apply View.order. apply LOCAL0.
  - (* write_step *)
    admit.
Admitted.

Lemma sim_aeu_rtc_step
      tid ts ex aeu1 aeu2 aeu2'
      (SIM: sim_aeu tid ts ex aeu1 aeu2)
      (STEP: rtc (AExecUnit.step tid) aeu2 aeu2'):
  exists aeu1',
    <<STEP: rtc (AExecUnit.step tid) aeu1 aeu1'>> /\
    <<SIM: sim_aeu tid ts ex aeu1' aeu2'>>.
Proof.
  revert aeu1 SIM. induction STEP.
  { i. esplits; eauto. }
  i. exploit sim_aeu_step; eauto. i. des.
  exploit IHSTEP; eauto. i. des.
  esplits; [|by eauto]. econs; eauto.
Qed.

Lemma certify_lift_diff
      tid eu1 eu2 locks msg
      (CERTIFY: certify tid eu2 locks)
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
        splits; ss.
        admit. (* bot cap X = bot *)
      + admit. (* sim_lc *)
    - admit. (* bot cap X = bot *)
  }
  i. des. esplits.
  - econs; eauto.
    + inv SIM. inv EU. inv LOCAL. etrans; eauto.
    + inv SIM. congr.
  - ii. des. destruct lock as [loc from to guarantee]. ss. subst.
    inv LOCK. ss. inv SIM. eapply AUX_EX. econs; cycle 1; eauto.
Admitted.
