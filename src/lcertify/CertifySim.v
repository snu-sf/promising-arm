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

Inductive sim_mem (tid:Id.t) (ts ts_private:Time.t) (src_promises:Promises.t) (coh1 coh2: Loc.t -> View.t (A:=unit)) (mem1 mem2:Memory.t): Prop :=
| sim_mem_intro
    mem mem1' mem2'
    (MEM: ts = length mem)
    (MEM1: mem1 = mem ++ mem1')
    (MEM2: mem2 = mem ++ mem2')
    (SRC_PROMISES_WF: forall tsp (TSP: Promises.lookup (S tsp) src_promises),
        length mem < S tsp /\
        exists msg, nth_error mem1 tsp = Some msg /\
               Memory.exclusive tid msg.(Msg.loc) ts (S tsp) mem1 /\
               Memory.latest msg.(Msg.loc) (S tsp) (length mem1) mem1)
    (SRC_PROMISES: forall tsp msg
                     (TSP: Promises.lookup (S tsp) src_promises)
                     (MSG: nth_error mem1 tsp = Some msg),
        <<MSG: msg.(Msg.tid) = tid>> /\
        <<MSGCOH: (coh1 msg.(Msg.loc)).(View.ts) < S tsp>>)
    (TS_PRIVATE: forall tsp msg
                   (TSP: ts_private < tsp)
                   (READ: Memory.get_msg tsp mem1 = Some msg),
        msg.(Msg.tid) = tid)
    (MEM1': forall n1 msg1
              (NTH: nth_error mem1' n1 = Some msg1)
              (PROMISES: Promises.lookup (S (length mem) + n1) src_promises = false),
        <<TID: msg1.(Msg.tid) = tid>> /\
        <<MSGCOH: S (length mem) + n1 <= (coh1 msg1.(Msg.loc)).(View.ts)>> /\
        exists n2 msg2,
          <<MSG: nth_error mem2' n2 = Some msg2>> /\
          <<LOC: msg1.(Msg.loc) = msg2.(Msg.loc)>> /\
          <<MSGCOH: S (length mem) + n2 <= (coh2 msg2.(Msg.loc)).(View.ts)>>)
.
Hint Constructors sim_mem.

Inductive sim_fwdbank (tid:Id.t) (ts:Time.t) (mem1 mem2:Memory.t) (loc:Loc.t) (fwd1 fwd2:FwdItem.t (A:=unit)): Prop :=
| sim_fwdbank_below
    val
    (BELOW: fwd2.(FwdItem.view).(View.ts) <= ts)
    (TS: sim_time ts fwd1.(FwdItem.ts) fwd2.(FwdItem.ts))
    (TSABOVE: ts < fwd2.(FwdItem.ts) -> ts < fwd1.(FwdItem.ts) /\ Memory.latest loc fwd1.(FwdItem.ts) (length mem1) mem1)
    (VIEW: fwd1.(FwdItem.view) = fwd2.(FwdItem.view))
    (EX: fwd1.(FwdItem.ex) = fwd2.(FwdItem.ex))
    (READ1: Memory.read loc fwd1.(FwdItem.ts) mem1 = Some val)
    (READ2: Memory.read loc fwd2.(FwdItem.ts) mem2 = Some val)
| sim_fwdbank_above
    (ABOVE: ts < fwd2.(FwdItem.view).(View.ts))
    (LATEST: Memory.latest loc fwd1.(FwdItem.ts) (length mem1) mem1)
.

Inductive sim_exbank (tid:Id.t) (ts:Time.t) (mem1 mem2:Memory.t) (eb1 eb2:Exbank.t (A:=unit)): Prop :=
| sim_exbank_below
    (BELOW: eb2.(Exbank.view).(View.ts) <= ts)
    (LOC: eb1.(Exbank.loc) = eb2.(Exbank.loc))
    (TS: sim_time ts eb1.(Exbank.ts) eb2.(Exbank.ts))
    (EXCLUSIVE: ts < eb2.(Exbank.ts) -> Memory.exclusive tid eb1.(Exbank.loc) eb1.(Exbank.ts) ts mem1)
    (VIEW: eb1.(Exbank.view) = eb2.(Exbank.view))
| sim_exbank_above
    (ABOVE: ts < eb2.(Exbank.view).(View.ts))
    (EXCLUSIVE: Memory.exclusive tid eb1.(Exbank.loc) eb1.(Exbank.ts) ts mem1)
.
Hint Constructors sim_exbank.

Inductive sim_lc (tid:Id.t) (ts:Time.t) (mem1 mem2:Memory.t) (src_promises:Promises.t) (lc1 lc2:Local.t (A:=unit)): Prop :=
| sim_lc_intro
    (COH: forall loc, sim_view ts (lc1.(Local.coh) loc) (lc2.(Local.coh) loc))
    (VRN: sim_view ts lc1.(Local.vrn) lc2.(Local.vrn))
    (VWN: sim_view ts lc1.(Local.vwn) lc2.(Local.vwn))
    (VRO: sim_view ts lc1.(Local.vro) lc2.(Local.vro))
    (VWO: sim_view ts lc1.(Local.vwo) lc2.(Local.vwo))
    (VCAP: sim_view ts lc1.(Local.vcap) lc2.(Local.vcap))
    (VREL: sim_view ts lc1.(Local.vrel) lc2.(Local.vrel))
    (FWDBANK: forall loc, sim_fwdbank tid ts mem1 mem2 loc (lc1.(Local.fwdbank) loc) (lc2.(Local.fwdbank) loc))
    (EXBANK: opt_rel (sim_exbank tid ts mem1 mem2) lc1.(Local.exbank) lc2.(Local.exbank))
    (PROMISES1: forall tsp (TSP: tsp <= ts), Promises.lookup tsp lc1.(Local.promises) = Promises.lookup tsp lc2.(Local.promises))
    (PROMISES2: forall tsp (TSP: tsp > ts), Promises.lookup tsp lc1.(Local.promises) = Promises.lookup tsp src_promises)
.
Hint Constructors sim_lc.

Inductive sim_eu (tid:Id.t) (ts ts_private:Time.t) (src_promises:Promises.t) (eu1 eu2:ExecUnit.t (A:=unit)): Prop :=
| sim_eu_intro
    (STATE: sim_state ts eu1.(ExecUnit.state) eu2.(ExecUnit.state))
    (LOCAL: sim_lc tid ts eu1.(ExecUnit.mem) eu2.(ExecUnit.mem) src_promises eu1.(ExecUnit.local) eu2.(ExecUnit.local))
    (MEM: sim_mem tid ts ts_private src_promises eu1.(ExecUnit.local).(Local.coh) eu2.(ExecUnit.local).(Local.coh) eu1.(ExecUnit.mem) eu2.(ExecUnit.mem))
.
Hint Constructors sim_eu.

Lemma sim_time_join
      ts l1 l2 r1 r2
      (VIEW1: sim_time ts l1 r1)
      (VIEW2: sim_time ts l2 r2):
  sim_time ts (join l1 l2) (join r1 r2).
Proof.
  inv VIEW1. inv VIEW2. econs.
  i. rewrite TS, TS0; ss.
  - rewrite <- H, <- join_r. ss.
  - rewrite <- H, <- join_l. ss.
Qed.

Lemma sim_time_eq
      ts v1 v2
      (SIM: sim_time ts v1 v2)
      (V2: v2 <= ts):
  v1 = v2.
Proof.
  apply SIM. ss.
Qed.

Lemma sim_time_above
      ts v1 v2
      (ABOVE: ts < v2):
  sim_time ts v1 v2.
Proof.
  econs. lia.
Qed.

Lemma sim_val_const
      ts c:
  sim_val ts (ValA.mk _ c bot) (ValA.mk _ c bot).
Proof.
  econs; splits; ss; try apply bot_spec.
Qed.

Lemma sim_view_bot
      ts:
  sim_view ts bot bot.
Proof.
  econs; splits; ss; try apply bot_spec.
Qed.

Lemma sim_view_const
      ts c
      (C1: c <= ts):
  sim_view ts (View.mk c bot) (View.mk c bot).
Proof.
  econs; ss.
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
  inv VIEW1. inv VIEW2. econs; ss.
  i. rewrite TS, TS0; ss.
  - rewrite <- H, <- join_r. ss.
  - rewrite <- H, <- join_l. ss.
Qed.

Lemma sim_view_ifc
      ts c l1 r1
      (VIEW1: sim_view ts l1 r1):
  sim_view ts (ifc c l1) (ifc c r1).
Proof.
  destruct c; ss.
Qed.

Lemma sim_view_eq
      ts v1 v2
      (SIM: sim_view ts v1 v2)
      (V2: v2.(View.ts) <= ts):
  v1 = v2.
Proof.
  apply SIM. ss.
Qed.

Lemma sim_view_above
      ts v1 v2
      (ABOVE: ts < v2.(View.ts)):
  sim_view ts v1 v2.
Proof.
  econs. lia.
Qed.

Lemma sim_val_view ts v1 v2
      (VAL: sim_val ts v1 v2):
  sim_view ts v1.(ValA.annot) v2.(ValA.annot).
Proof.
  inv VAL. econs; ss. i. rewrite TS; ss.
Qed.

Lemma sim_view_val
      ts c v1 v2
      (SIM: sim_view ts v1 v2):
  sim_val ts (ValA.mk _ c v1) (ValA.mk _ c v2).
Proof.
  inv SIM. econs; ss. i. rewrite TS; ss.
Qed.

Lemma sim_val_above
      ts (v1 v2:ValA.t (A:=View.t (A:=unit)))
      (ABOVE: ts < v2.(ValA.annot).(View.ts)):
  sim_val ts v1 v2.
Proof.
  econs. lia.
Qed.

Lemma sim_val_below
      ts v1 v2
      (SIM: sim_val ts v1 v2)
      (BELOW: v2.(ValA.annot).(View.ts) <= ts):
  v1 = v2.
Proof.
  apply SIM. ss.
Qed.

Lemma sim_view_refl
      ts v:
  sim_view ts v v.
Proof.
  econs; ss.
Qed.

Lemma sim_time_refl
      ts t:
  sim_time ts t t.
Proof.
  econs; ss.
Qed.

Lemma sim_time_below
      ts v1 v2
      (SIM: sim_time ts v1 v2)
      (BELOW: v2 <= ts):
  v1 = v2.
Proof.
  apply SIM. ss.
Qed.

Lemma sim_time_ifc
      ts c l1 r1
      (VIEW1: sim_time ts l1 r1):
  sim_time ts (ifc c l1) (ifc c r1).
Proof.
  destruct c; ss.
Qed.
Lemma sim_time_bot
      ts:
  sim_time ts bot bot.
Proof.
  econs; splits; ss; try apply bot_spec.
Qed.

Lemma sim_view_time ts v1 v2
      (VIEW: sim_view ts v1 v2):
  sim_time ts v1.(View.ts) v2.(View.ts).
Proof.
  inv VIEW. econs; ss. i. rewrite TS; ss.
Qed.

Lemma sim_view_below
      ts v1 v2
      (SIM: sim_view ts v1 v2)
      (BELOW: v2.(View.ts) <= ts):
  v1 = v2.
Proof.
  apply SIM. ss.
Qed.

Lemma sim_view_below_weak
      ts v1 v2
      (SIM: sim_view ts v1 v2)
      (BELOW: v2.(View.ts) <= ts):
  v1.(View.ts) <= ts.
Proof.
  exploit sim_view_below; eauto. i. subst. ss.
Qed.

Lemma sim_rmap_expr
      ts rmap1 rmap2 e
      (RMAP: sim_rmap ts rmap1 rmap2):
  sim_val ts (sem_expr rmap1 e) (sem_expr rmap2 e).
Proof.
  induction e; s.
  - apply sim_val_const.
  - unfold RMap.find. inv RMAP. specialize (RMAP0 reg). inv RMAP0; ss.
  - inv IHe. econs; ss.
    i. rewrite TS; ss.
  - inv IHe1. inv IHe2. econs; ss.
    + i. rewrite TS, TS0; ss.
      * rewrite <- H, <- join_r. ss.
      * rewrite <- H, <- join_l. ss.
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

Lemma sim_mem_read
      tid ts ts_private src_promises coh1 coh2 mem1 mem2 loc ts0
      (SIM: sim_mem tid ts ts_private src_promises coh1 coh2 mem1 mem2)
      (TS0: ts0 <= ts):
  Memory.read loc ts0 mem1 = Memory.read loc ts0 mem2.
Proof.
  inv SIM. unfold Memory.read. destruct ts0; ss. rewrite ? nth_error_app1; ss.
Qed.

Lemma sim_mem_get_msg
      tid ts ts_private src_promises coh1 coh2 mem1 mem2 ts0
      (SIM: sim_mem tid ts ts_private src_promises coh1 coh2 mem1 mem2)
      (TS0: ts0 <= ts):
  Memory.get_msg ts0 mem1 = Memory.get_msg ts0 mem2.
Proof.
  inv SIM. unfold Memory.get_msg. destruct ts0; ss. rewrite ? nth_error_app1; ss.
Qed.

Lemma sim_mem_length
      tid ts ts_private src_promises coh1 coh2 mem1 mem2
      (SIM: sim_mem tid ts ts_private src_promises coh1 coh2 mem1 mem2):
  ts <= length mem1 /\ ts <= length mem2.
Proof.
  inv SIM. rewrite ? app_length. lia.
Qed.

Lemma sim_mem1_exclusive
      tid ts ts_private src_promises loc from to coh1 coh2 mem1 mem2
      (MEM: sim_mem tid ts ts_private src_promises coh1 coh2 mem1 mem2)
      (EXCLUSIVE: Memory.exclusive tid loc from ts mem1):
  Memory.exclusive tid loc from to mem1.
Proof.
  ii. des. destruct (le_lt_dec (S ts0) ts).
  - eapply EXCLUSIVE; eauto.
  - inv MEM.
    destruct (Promises.lookup (S ts0) src_promises) eqn:TSP.
    { exploit SRC_PROMISES; eauto. i. des. subst. eauto. }
    rewrite nth_error_app2 in MSG; [|lia].
    exploit MEM1'; eauto.
    + replace (S (length mem) + (ts0 - length mem)) with (S ts0) by lia. ss.
    + i. des. subst. ss.
Qed.

Lemma sim_mem_no_msgs
      tid ts ts_private src_promises from to pred coh1 coh2 mem1 mem2
      (MEM: sim_mem tid ts ts_private src_promises coh1 coh2 mem1 mem2)
      (TS: to <= ts)
      (NOMSGS: Memory.no_msgs from to pred mem2):
  Memory.no_msgs from to pred mem1.
Proof.
  ii. eapply NOMSGS; eauto. inv MEM. rewrite nth_error_app1 in *; try lia. ss.
Qed.

Ltac des_eq :=
  repeat
    (try match goal with
         | [H: _ === riscv |- _] => revert H
         | [H: ?a === ?b |- _] => inv H
         | [H: proj_sumbool (equiv_dec ?a ?a) = true |- _] => clear H
         | [H: proj_sumbool (equiv_dec ?a ?b) = _ |- _] => destruct (equiv_dec a b)
         | [H: negb _ = true |- _] => apply Bool.negb_true_iff in H
         | [H: negb _ = false |- _] => apply Bool.negb_false_iff in H
         | [H: andb _ _ = false |- _] => apply Bool.andb_false_iff in H
         | [H: andb _ _ = true |- _] => apply Bool.andb_true_iff in H
         | [H: orb _ _ = false |- _] => apply Bool.orb_false_iff in H
         end;
     ss; des; subst; try congr).

Lemma sim_fwd_view1 tid ts ts_private src_promises mem1 mem2 loc coh1 coh2 fwd1 fwd2 o
      (FWD: sim_fwdbank tid ts mem1 mem2 loc fwd1 fwd2)
      (WF1: Local.wf_fwdbank loc mem1 (coh1 loc).(View.ts) fwd1)
      (WF2: Local.wf_fwdbank loc mem2 (coh2 loc).(View.ts) fwd2)
      (MEM: sim_mem tid ts ts_private src_promises coh1 coh2 mem1 mem2)
      (COND: andb fwd2.(FwdItem.ex) (equiv_dec arch riscv || OrdR.ge o OrdR.acquire_pc) = false):
  sim_view ts (FwdItem.read_view fwd1 fwd1.(FwdItem.ts) o) (FwdItem.read_view fwd2 fwd2.(FwdItem.ts) o).
Proof.
  destruct fwd1 as [ts1 view1 ex1].
  destruct fwd2 as [ts2 view2 ex2].
  unfold FwdItem.read_view. s. inv WF1. inv WF2. inv MEM.
  inv FWD; ss; repeat condtac; ss.
  all: repeat match goal with
              | [H: sim_time _ _ _ |- _] => inv H
              | [H: sim_view _ _ _ |- _] => inv H
              | [H: FwdItem.mk _ _ _ = FwdItem.mk _ _ _ |- _] => inv H
              end.
  all: unfold Time.t in *.
  all: des_eq.
  all: try by econs; ss; ii; lia.
Qed.

Lemma sim_fwd_view2 tid ts ts_private src_promises mem1 mem2 loc coh1 coh2 fwd1 fwd2 t o
      (FWD: sim_fwdbank tid ts mem1 mem2 loc fwd1 fwd2)
      (WF1: Local.wf_fwdbank loc mem1 (coh1 loc).(View.ts) fwd1)
      (WF2: Local.wf_fwdbank loc mem2 (coh2 loc).(View.ts) fwd2)
      (MEM: sim_mem tid ts ts_private src_promises coh1 coh2 mem1 mem2)
      (TS: t <= ts)
      (FWDTS: fwd2.(FwdItem.ts) <= t)
      (COND: fwd2.(FwdItem.ts) <> t \/ andb fwd2.(FwdItem.ex) (equiv_dec arch riscv || OrdR.ge o OrdR.acquire_pc) = true):
  sim_view ts (FwdItem.read_view fwd1 t o) (FwdItem.read_view fwd2 t o).
Proof.
  destruct fwd1 as [ts1 view1 ex1].
  destruct fwd2 as [ts2 view2 ex2].
  unfold FwdItem.read_view. s. inv WF1. inv WF2. inv MEM.
  inv FWD; ss; repeat condtac; ss.
  all: repeat match goal with
              | [H: sim_time _ _ _ |- _] => inv H
              | [H: sim_view _ _ _ |- _] => inv H
              | [H: FwdItem.mk _ _ _ = FwdItem.mk _ _ _ |- _] => inv H
              end.
  all: unfold Time.t in *.
  all: des_eq.
  all: try by econs; ss; ii; lia.
Qed.

Lemma sim_fwdbank_mon
      tid ts ts_private src_promises coh1 coh2 mem1 mem2 loc fwd1 fwd2 mem1' mem2'
      (MEM: sim_mem tid ts ts_private src_promises coh1 coh2 mem1 mem2)
      (SIM: sim_fwdbank tid ts mem1 mem2 loc fwd1 fwd2)
      (FWD1: fwd1.(FwdItem.ts) <= length mem1)
      (MEM1': Forall (fun msg => msg.(Msg.loc) <> loc) mem1'):
  sim_fwdbank tid ts (mem1 ++ mem1') (mem2 ++ mem2') loc fwd1 fwd2.
Proof.
  inv SIM.
  - econs 1; ss.
    + intro X. specialize (TSABOVE X). des. splits; ss.
      ii. subst. apply nth_error_app_inv in MSG. des; cycle 1.
      { apply nth_error_In in MSG0. eapply Forall_forall in MEM1'; eauto.
        destruct (nequiv_dec (Msg.loc msg) (Msg.loc msg)); ss. congr.
      }
      eapply TSABOVE0; eauto.
    + apply Memory.read_mon. eauto.
    + apply Memory.read_mon. eauto.
  - econs 2; ss. eapply Memory.no_msgs_split; eauto.
    { rewrite app_length. clear. lia. }
    splits.
    + apply Memory.no_msgs_full; ss.
    + ii. subst. rewrite nth_error_app2 in MSG; [|lia].
      apply nth_error_In in MSG. eapply Forall_forall in MEM1'; eauto.
      destruct (nequiv_dec (Msg.loc msg) (Msg.loc msg)); ss. congr.
Qed.

Lemma sim_exbank_mon
      tid ts ts_private src_promises coh1 coh2 mem1 mem2 eb1 eb2 mem1' mem2'
      (MEM: sim_mem tid ts ts_private src_promises coh1 coh2 mem1 mem2)
      (SIM: sim_exbank tid ts mem1 mem2 eb1 eb2):
  sim_exbank tid ts (mem1 ++ mem1') (mem2 ++ mem2') eb1 eb2.
Proof.
  exploit sim_mem_length; eauto. i. des.
  inv SIM.
  - econs 1; ss. ii. eapply EXCLUSIVE; eauto.
    rewrite nth_error_app1 in MSG; ss. lia.
  - econs 2; ss. ii. eapply EXCLUSIVE; eauto.
    rewrite nth_error_app1 in MSG; ss. lia.
Qed.

Lemma sim_eu_step
      tid ts ts_private src_promises eu1 eu2 eu2'
      (SIM: sim_eu tid ts ts_private src_promises eu1 eu2)
      (STEP: certify_step tid eu2 eu2')
      (SRC_PROMISES_BELOW: forall tsp msg
                             (TSP: Promises.lookup (S tsp) src_promises)
                             (MEM: nth_error eu1.(ExecUnit.mem) tsp = Some msg),
          (eu2'.(ExecUnit.local).(Local.coh) msg.(Msg.loc)).(View.ts) <= ts)
      (WF1: ExecUnit.wf tid eu1)
      (WF2: ExecUnit.wf tid eu2)
      (VCAP: eu2'.(ExecUnit.local).(Local.vcap).(View.ts) <= ts):
  exists eu1',
    <<STEP: certify_step tid eu1 eu1'>> /\
    <<SIM: sim_eu tid ts ts_private src_promises eu1' eu2'>>.
Proof.
  exploit certify_step_wf; eauto. i.
  destruct eu1 as [[stmts1 rmap1] lc1 mem1].
  destruct eu2 as [[stmts2 rmap2] lc2 mem2].
  destruct eu2' as [[stmts2' rmap2'] lc2' mem2'].
  inv SIM. inv STATE. ss. subst.
  exploit sim_mem_length; eauto. intro LEN. des.
  inv STEP; cycle 1.
  { (* write step *)
    inv STEP0. ss. inv STATE. inv PROMISE. inv FULFILL. inv MEM2. ss.
    exploit sim_rmap_expr; eauto. instantiate (1 := eloc).
    intro X. inv X. exploit TS.
    { rewrite <- VCAP, <- join_r. ss. }
    clear TS. intro TS. rewrite <- TS in *.
    eexists (ExecUnit.mk _ _ _). esplits.
    - econs 2. econs; ss.
      + econs; ss.
      + econs; ss.
        * inv WF1. ss. inv LOCAL0. inv WRITABLE. ss. econs; ss.
          { eapply le_lt_trans; [|ss]. apply COH. }
          { eapply le_lt_trans; [|ss]. s. repeat apply join_spec; ss.
            all: unfold ifc.
            all: try condtac; ss.
            all: try apply bot_spec.
            - apply ExecUnit.expr_wf. ss.
            - apply ExecUnit.expr_wf. ss.
            - destruct lc1; ss. destruct exbank; [|by apply bot_spec].
              exploit EXBANK; eauto. intro Y. inv Y. rewrite VIEW. ss.
          }
          { intro X. specialize (EX X). des. inv LOCAL. inv EXBANK0; [congr|].
            rewrite TSX in H. inv H. esplits; eauto.
            destruct a, eb. ss. i. subst.
            eapply Memory.no_msgs_split; swap 1 2.
            { apply Nat.le_succ_diag_r. }
            { exploit EXBANK; eauto. s. intro Y. inv Y. ss.
              rewrite TS0, <- COH. apply Memory.latest_ts_spec.
            }
            split.
            - apply Memory.no_msgs_full; ss. eapply sim_mem1_exclusive; eauto.
              inv REL; ss. subst. destruct (le_lt_dec ts1 ts); eauto.
              inv TS0. rewrite TS1 in *; ss.
              eapply sim_mem_no_msgs; eauto.
              eapply Memory.no_msgs_weaken; [|by apply EX0; ss].
              clear -LEN0. lia.
            - ii. replace ts2 with (length mem1) in * by (clear -TS1 TS2; lia).
              rewrite nth_error_app2, Nat.sub_diag in MSG0; ss. inv MSG0. des. ss.
          }
        * unfold Memory.get_msg. s. rewrite nth_error_app2, Nat.sub_diag; ss.
        * rewrite Promises.set_o. condtac; ss. congr.
    - inv WRITABLE. ss.
      econs; ss.
      + econs; ss. apply sim_rmap_add; ss. econs; ss.
        unfold ifc. condtac; ss. intro Y. clear -Y LEN0. exfalso. lia.
      + inv LOCAL. econs; ss.
        * i. rewrite ? fun_add_spec. condtac; ss.
          apply sim_view_above. s. clear -LEN0. lia.
        * apply sim_view_join; ss.
          apply sim_view_above. s. clear -LEN0. lia.
        * apply sim_view_join; ss.
        * apply sim_view_join; ss. unfold ifc. condtac; ss.
          apply sim_view_above. s. clear -LEN0. lia.
        * i. rewrite ? fun_add_spec. condtac; ss.
          { inversion e. subst.
            destruct (le_lt_dec (View.ts (ValA.annot (sem_expr rmap2 eval))) ts).
            - exploit sim_rmap_expr; eauto. instantiate (1 := eval).
              intro Y. inv Y. exploit TS0; ss. clear TS0. intro EVAL. rewrite <- EVAL in *.
              econs 1; ss.
              + apply join_spec; ss. rewrite <- VCAP, <- join_r. ss.
              + apply sim_time_above. clear -LEN0. lia.
              + splits.
                * clear -LEN. lia.
                * apply Memory.ge_no_msgs. clear. rewrite app_length. s. lia.
              + unfold Memory.read. s. rewrite ? nth_error_app2, ? Nat.sub_diag; ss.
                condtac; ss.
              + eapply Memory.get_msg_read; eauto.
            - econs 2; ss.
              + eapply lt_le_trans; eauto. apply join_r.
              + rewrite app_length. s. ii. lia.
          }
          { eapply sim_fwdbank_mon; eauto.
            - inv WF1. ss. inv LOCAL. destruct (FWDBANK0 loc). des.
              rewrite TS0, <- COH1. apply Memory.latest_ts_spec.
            - econs; ss. destruct (nequiv_dec (ValA.val (sem_expr rmap1 eloc)) loc); ss. congr.
          }
        * destruct ex; ss. inv EXBANK; econs; ss.
          eapply sim_exbank_mon; eauto.
        * i. rewrite ? Promises.unset_o, ? Promises.set_o. condtac.
          { inversion e. subst. clear -LEN TSP. lia. }
          condtac.
          { inversion e. subst. clear -LEN0 TSP. lia. }
          apply PROMISES1. ss.
        * i. rewrite Promises.unset_o, Promises.set_o. condtac; ss.
          { clear X. inv e. rewrite <- PROMISES2; ss.
            erewrite Local.wf_promises_above; eauto. apply WF1.
          }
          { eauto. }
      + inv MEM. ss. econs.
        * ss.
        * rewrite <- app_assoc. ss.
        * rewrite <- app_assoc. ss.
        * i. exploit SRC_PROMISES_WF; eauto. i. des. esplits; ss.
          { apply nth_error_app_mon; eauto. }
          { ii. eapply x2; eauto. apply nth_error_snoc_inv in MSG0. des; subst; ss. }
          { rewrite app_length. s. ii. apply nth_error_snoc_inv in MSG0. des; subst; ss.
            - eapply x3; eauto.
            - exploit SRC_PROMISES_BELOW; eauto. rewrite fun_add_spec. condtac; ss; [|congr].
              clear. rewrite app_length. lia.
          }
        * i. apply nth_error_snoc_inv in MSG0. des.
          { exploit SRC_PROMISES; eauto. i. des. subst. splits; ss.
            exploit SRC_PROMISES_BELOW; eauto. rewrite ? fun_add_spec.
            condtac; ss. clear X. inv e. clear. rewrite app_length. lia.
          }
          { subst. splits; ss.
            rewrite fun_add_spec. condtac; ss; cycle 1.
            { exfalso. apply c. clear. refl. }
            apply SRC_PROMISES_WF in TSP. des.
            apply nth_error_some in TSP0. clear -TSP0. lia.
          }
        * i. apply Memory.get_msg_snoc_inv in READ. des; eauto. subst. ss.
        * i. apply nth_error_snoc_inv in NTH. des.
          { exploit MEM1'; eauto. i. des. subst. esplits; swap 1 3.
            { apply nth_error_app_mon. eauto. }
            all: ss.
            - rewrite fun_add_spec. condtac; ss.
              rewrite app_length. clear -NTH. lia.
            - s. rewrite MSGCOH0, fun_add_spec. condtac; ss.
              inv WF2. ss. inv LOCAL0. rewrite COH0. clear. lia.
          }
          { subst. ss. esplits; swap 1 3.
            { rewrite nth_error_app2, Nat.sub_diag; ss. }
            all: ss.
            - rewrite fun_add_spec. condtac; [|congr]. s.
              rewrite app_length. ss.
            - s. rewrite fun_add_spec. condtac; [|congr]. s.
              rewrite app_length. clear. lia.
          }
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

      (* Case analysis on [tgt's post-view <= ts]. *)
      destruct (le_lt_dec post.(View.ts) ts); cycle 1.
      { (* Case 1: Tgt's post-view > ts. Src reads the latest msg. *)
        rename l into POST_ABOVE. inv LOCAL.
        exploit Memory.latest_ts_spec; eauto. i. des.
        eexists (ExecUnit.mk _ _ _). esplits.
        - econs 1. econs. econs; ss.
          + econs; ss.
          + rewrite ELOC in *.
            econs 2; eauto. econs; ss; cycle 2.
            * apply READ.
            * instantiate (1 := length mem1).
              eapply Memory.latest_mon2.
              { apply Memory.latest_ts_latest; eauto. }
              { inv WF1. ss. inv LOCAL. apply COH1. }
            * eapply Memory.latest_mon2.
              { apply Memory.latest_ts_latest; eauto. }
              { inv WF1. ss. inv LOCAL. repeat apply join_spec; ss.
                - rewrite <- ELOC. eapply ExecUnit.expr_wf. ss.
                - unfold ifc. condtac; ss. apply bot_spec.
                - apply bot_spec.
              }
        - econs; ss.
          + econs; ss. apply sim_rmap_add; ss. apply sim_val_above. ss.
          + econs; ss.
            * i. rewrite ? fun_add_spec. condtac; ss.
              apply sim_view_join; ss. apply sim_view_above. ss.
            * apply sim_view_join; ss. apply sim_view_ifc; ss. apply sim_view_above. ss.
            * apply sim_view_join; ss. apply sim_view_ifc; ss. apply sim_view_above. ss.
            * apply sim_view_join; ss. apply sim_view_above. ss.
            * apply sim_view_join; ss.
            * destruct ex0; ss. econs. econs 2; ss.
              ii. des. eapply Memory.latest_ts_latest; eauto.
              rewrite TS2. clear -MEM. inv MEM. rewrite app_length. lia.
          + inv MEM. econs; ss.
            * i. exploit SRC_PROMISES; eauto. i. des. subst. splits; ss.
              exploit SRC_PROMISES_BELOW; eauto. rewrite ? fun_add_spec.
              condtac; ss. clear X. inv e. clear -POST_ABOVE. unfold join, Time.join. lia.
            * i. exploit MEM1'; eauto. i. des. subst.
              esplits; try exact MSG0; ss.
              { rewrite fun_add_spec. condtac; ss. inversion e. subst.
                rewrite MSGCOH, <- join_l. ss.
              }
              { rewrite MSGCOH0, fun_add_spec. condtac; ss. inversion e. subst.
                rewrite <- join_l. ss.
              }
      }

      (* Tgt's post-view <= ts. *)
      rename l into POST_BELOW.
      assert (VRNEQ: lc1.(Local.vrn) = lc2.(Local.vrn)).
      { inv LOCAL. eapply sim_view_below; eauto. rewrite <- POST_BELOW, POST. s.
        rewrite <- join_l, <- join_r, <- join_l. ss.
      }
      assert (VRELEQ: (ifc (OrdR.ge ord OrdR.acquire) lc1.(Local.vrel)) =
                      (ifc (OrdR.ge ord OrdR.acquire) lc2.(Local.vrel))).
      { inv LOCAL. eapply sim_view_below.
        - apply sim_view_ifc. eauto.
        - rewrite <- POST_BELOW, POST. s.
          rewrite <- join_l, <- join_r, <- join_r, <- join_l. ss.
      }
      (* Now case analysis on whether tgt read from fwdbank. *)
      destruct (((lc2.(Local.fwdbank) (ValA.val (sem_expr rmap2 eloc))).(FwdItem.ts) == ts0) &&
                (negb (__guard__ (andb (lc2.(Local.fwdbank) (ValA.val (sem_expr rmap2 eloc))).(FwdItem.ex)
                                       ((proj_sumbool (equiv_dec arch riscv)) || OrdR.ge ord OrdR.acquire_pc))))) eqn:E.
      { (* Case 2: Tgt read from fwdbank. Src reads from fwdbank, too. *)
        des_eq. unguardH E0. inv LOCAL. exploit sim_fwd_view1; eauto.
        { apply WF1. }
        { apply WF2. }
        intro FWDVIEW.
        eexists (ExecUnit.mk _ _ _). esplits.
        - econs 1. econs. econs; ss.
          + econs; ss.
          + rewrite ELOC in *.
            econs 2; eauto. econs; ss; cycle 2.
            * destruct (FWDBANK (ValA.val (sem_expr rmap2 eloc))).
              { rewrite READ1, <- READ2. eauto. }
              { exploit (Local.fwd_view_le (A:=unit)); try by apply WF2.
                all: s; eauto.
                instantiate (1 := ord). rewrite POST in POST_BELOW. clear -POST_BELOW ABOVE.
                ss. unfold join, Time.join in *. lia.
              }
            * destruct (FWDBANK (ValA.val (sem_expr rmap2 eloc))).
              { destruct (le_lt_dec (View.ts (Local.coh lc2 (ValA.val (sem_expr rmap2 eloc)))) ts).
                - exploit sim_view_below; try exact l; eauto. i.
                  rewrite x1 in *. eapply sim_mem_no_msgs; eauto.
                  destruct (le_lt_dec (FwdItem.ts (Local.fwdbank lc2 (ValA.val (sem_expr rmap2 eloc)))) ts).
                  + apply sim_time_below in TS; ss. rewrite TS in *. ss.
                  + specialize (TSABOVE l0). apply Memory.ge_no_msgs. clear -l TSABOVE. lia.
                - destruct (le_lt_dec (FwdItem.ts (Local.fwdbank lc2 (ValA.val (sem_expr rmap2 eloc)))) ts).
                  + apply sim_time_below in TS; ss. rewrite TS in *. ss.
                    ii. destruct (le_lt_dec (S ts0) ts).
                    * eapply COH; eauto.
                      { clear -l1 l. lia. }
                      { inv MEM. rewrite nth_error_app1 in *; ss. }
                    * inv MEM.
                      destruct (Promises.lookup (S ts0) src_promises) eqn:TSP.
                      { exploit SRC_PROMISES; eauto. i. des. subst.
                        rewrite H in MSGCOH. clear -MSGCOH TS2. lia.
                      }
                      rewrite nth_error_app2 in MSG0; ss; [|clear -l1; lia].
                      exploit MEM1'; eauto.
                      { replace (S (length mem + (ts0 - length mem))) with (S ts0) by lia. ss. }
                      i. des. destruct msg, msg2. ss. subst.
                      eapply COH; try exact MSGCOH0; eauto.
                      { clear -l0. lia. }
                      { rewrite <- MSG1. clear. rewrite nth_error_app2; [|lia]. f_equal. lia. }
                      { ss. }
                  + specialize (TSABOVE l0). des. eapply Memory.latest_mon2; eauto.
                    inv WF1. ss. inv LOCAL. apply COH1.
              }
              { eapply Memory.latest_mon2; eauto. inv WF1. ss. inv LOCAL. apply COH1. }
            * rewrite VRNEQ, VRELEQ.
              destruct (FWDBANK (ValA.val (sem_expr rmap2 eloc))).
              { destruct (le_lt_dec (FwdItem.ts (Local.fwdbank lc2 (ValA.val (sem_expr rmap2 eloc)))) ts).
                - apply sim_time_below in TS; ss. rewrite TS.
                  eapply sim_mem_no_msgs; eauto. rewrite <- POST_BELOW, POST. s. apply join_l.
                - specialize (TSABOVE l). apply Memory.ge_no_msgs.
                  rewrite POST in POST_BELOW. clear -POST_BELOW TSABOVE. ss.
                  unfold join, Time.join in *. lia.
              }
              { eapply Memory.latest_mon2; eauto. rewrite <- LEN, <- POST_BELOW, POST. s. apply join_l. }
        - assert (SIM_POST: sim_view ts (join
    (View._join (ValA.annot (sem_expr rmap2 eloc))
       (View._join (Local.vrn lc1)
          (View._join (ifc (OrdR.ge ord OrdR.acquire) (Local.vrel lc1)) View._bot)))
    (FwdItem.read_view (Local.fwdbank lc1 (ValA.val (sem_expr rmap2 eloc)))
                       (FwdItem.ts (Local.fwdbank lc1 (ValA.val (sem_expr rmap2 eloc)))) ord)) post).
          { rewrite POST. eauto 10 using sim_view_join, sim_view_ifc, sim_view_bot. }
          econs; ss.
          + econs; ss. apply sim_rmap_add; ss. apply sim_view_val. ss.
          + econs; ss; try by rewrite ? POST; eauto 10 using sim_view_join, sim_view_ifc, sim_view_bot.
            * i. rewrite ? fun_add_spec. condtac; ss. apply sim_view_join; ss.
            * destruct ex0; ss. econs. econs 1; ss.
              { destruct (FWDBANK (ValA.val (sem_expr rmap2 eloc))); ss.
                apply sim_time_above. inv WF2. ss. inv LOCAL.
                destruct (FWDBANK0 (ValA.val (sem_expr rmap2 eloc))). des.
                clear -ABOVE VIEW. lia.
              }
              { destruct (FWDBANK (ValA.val (sem_expr rmap2 eloc))); eauto.
                - intro Y. specialize (TSABOVE Y).
                  apply Memory.ge_no_msgs. clear -TSABOVE. lia.
                - ii. des. eapply LATEST0; eauto. rewrite TS2.
                  inv MEM. rewrite app_length. clear. lia.
              }
              { eapply sim_view_below; eauto. }
          + inv MEM. econs; ss.
            * i. exploit SRC_PROMISES; eauto. i. des. subst. splits; ss.
              exploit SRC_PROMISES_BELOW; eauto. rewrite ? fun_add_spec.
              condtac; ss. clear X. inv e. i.
              exploit sim_view_below.
              { apply sim_view_join; [apply COH0|apply SIM_POST]. }
              { s. eauto. }
              i. apply View.eq_time_eq in x2. ss. rewrite H0 in *. rewrite x2.
              eapply le_lt_trans; eauto. apply SRC_PROMISES_WF. ss.
            * i. exploit MEM1'; eauto. i. des. subst.
              esplits; try exact MSG0; ss.
              { rewrite fun_add_spec. condtac; ss. inversion e. subst.
                rewrite MSGCOH, <- join_l. ss.
              }
              { rewrite MSGCOH0, fun_add_spec. condtac; ss. inversion e. subst.
                rewrite <- join_l. ss.
              }
      }
      { (* Case 3: Tgt didn't read from fwdbank. Src reads the same msg. *)
        generalize POST. intro POST'.
        unfold FwdItem.read_view in POST'.
        generalize E. intro E'. unfold __guard__ in E'. rewrite E' in POST'. clear E'. ss.
        assert (BELOW: ts0 <= ts).
        { rewrite <- POST_BELOW, POST'. s. apply join_r. }
        inv LOCAL. exploit sim_fwd_view2; eauto.
        { apply WF1. }
        { apply WF2. }
        { inv WF2. ss. inv LOCAL. destruct (FWDBANK0 (sem_expr rmap2 eloc).(ValA.val)). des.
          rewrite TS. apply Memory.latest_latest_ts. ss.
        }
        { des_eq.
          - left. ii. apply c. ss.
          - right. apply E.
        }
        intro FWDVIEW.
        eexists (ExecUnit.mk _ _ _). esplits.
        - econs 1. econs. econs; ss.
          + econs; ss.
          + rewrite ELOC in *.
            econs 2; eauto. econs; ss; cycle 2.
            * erewrite sim_mem_read; eauto.
            * destruct (le_lt_dec (View.ts (Local.coh lc2 (ValA.val (sem_expr rmap2 eloc)))) ts).
              { exploit sim_view_below; try exact l; eauto. intro Y. rewrite Y in *.
                eapply sim_mem_no_msgs; eauto.
              }
              ii. destruct (le_lt_dec (S ts1) ts).
              { eapply COH; eauto.
                - clear -l0 l. lia.
                - inv MEM. rewrite nth_error_app1 in *; ss.
              }
              { inv MEM.
                destruct (Promises.lookup (S ts1) src_promises) eqn:TSP.
                { exploit SRC_PROMISES; eauto. i. des. subst.
                  rewrite H in MSGCOH. clear -MSGCOH TS2. lia.
                }
                rewrite nth_error_app2 in MSG0; ss; [|clear -l0; lia].
                exploit MEM1'; eauto.
                { replace (S (length mem + (ts1 - length mem))) with (S ts1) by lia. ss. }
                i. des. destruct msg, msg2. ss. subst.
                eapply COH; try exact MSGCOH0; eauto.
                - clear -BELOW. lia.
                - rewrite <- MSG1. clear. rewrite nth_error_app2; [|lia]. f_equal. lia.
                - ss.
              }
            * rewrite VRNEQ, VRELEQ. eapply sim_mem_no_msgs; eauto.
              rewrite <- POST_BELOW, POST'. s. apply join_l.
        - assert (SIM_POST: sim_view ts
    (join
       (View._join (ValA.annot (sem_expr rmap2 eloc))
          (View._join (Local.vrn lc1)
             (View._join (ifc (OrdR.ge ord OrdR.acquire) (Local.vrel lc1)) View._bot)))
       (FwdItem.read_view (Local.fwdbank lc1 (ValA.val (sem_expr rmap2 eloc))) ts0 ord)) post).
          { rewrite POST. eauto 10 using sim_view_join, sim_view_ifc, sim_view_bot. }
          econs; ss.
          + econs; ss. apply sim_rmap_add; ss. apply sim_view_val. ss.
          + econs; ss; try by rewrite ? POST; eauto 10 using sim_view_join, sim_view_ifc, sim_view_bot.
            * i. rewrite ? fun_add_spec. condtac; ss. apply sim_view_join; ss.
            * destruct ex0; ss. econs. econs; ss.
              { clear. ii. lia. }
              { eapply sim_view_below; eauto. }
          + inv MEM. econs; ss.
            * i. exploit SRC_PROMISES; eauto. i. des. subst. splits; ss.
              exploit SRC_PROMISES_BELOW; eauto. rewrite ? fun_add_spec.
              condtac; ss. clear X. inv e. i.
              exploit sim_view_below.
              { apply sim_view_join; [apply COH0|apply SIM_POST]. }
              { s. eauto. }
              i. apply View.eq_time_eq in x2. ss. rewrite H0 in *. rewrite x2.
              eapply le_lt_trans; eauto. apply SRC_PROMISES_WF. ss.
            * i. exploit MEM1'; eauto. i. des. subst.
              esplits; try exact MSG0; ss.
              { rewrite fun_add_spec. condtac; ss. inversion e. subst.
                rewrite MSGCOH, <- join_l. ss.
              }
              { rewrite MSGCOH0, fun_add_spec. condtac; ss. inversion e. subst.
                rewrite <- join_l. ss.
              }
      }
    - (* fulfill *)
      inv STEP. ss.
      exploit sim_rmap_expr; eauto. instantiate (1 := eloc).
      intro X. inv X. exploit TS.
      { rewrite <- VCAP, <- join_r. ss. }
      clear TS. intro ELOC.
      destruct (le_lt_dec ts0 ts).
      { (* fulfilling a promise <= ts. *)
        rename l into TS0.
        exploit sim_rmap_expr; eauto. instantiate (1 := eval).
        intro X. inv X. exploit TS.
        { rewrite <- TS0. inv WRITABLE. etrans; [|by apply Time.lt_le_incl; eauto].
          s. rewrite <- join_r, <- join_l. eauto.
        }
        clear TS. intro EVAL.
        eexists (ExecUnit.mk _ _ _). esplits.
        + econs 1. econs. econs; ss; cycle 1.
          * econs 3; eauto. econs; eauto; cycle 1.
            { rewrite <- MSG. eapply sim_mem_get_msg; eauto. }
            { inv LOCAL. rewrite PROMISES1; ss. }
            { instantiate (1 := view_pre).
              instantiate (1 := ord).
              instantiate (1 := ex0).
              inv WRITABLE. econs; eauto.
              - symmetry. eapply sim_view_eq; cycle 1.
                { etrans; [by apply Time.lt_le_incl; eauto|]. eauto. }
                s. repeat apply sim_view_join; ss.
                all: try apply sim_view_ifc.
                all: try apply sim_view_bot.
                all: try by apply LOCAL.
                inv LOCAL. inv EXBANK; ss. inv REL; ss. clear -ABOVE. econs. lia.
              - inv LOCAL. destruct (COH0 (ValA.val (sem_expr rmap2 eloc))).
                rewrite TS; ss. rewrite <- TS0. apply Nat.le_lteq. left. ss.
              - i. specialize (EX H). des. inv LOCAL. rewrite TSX in *. inv EXBANK.
                destruct a, eb. ss. esplits; eauto. ss. i. subst. inv REL; ss; subst.
                + move EX0 at bottom. specialize (EX0 eq_refl).
                  destruct (le_lt_dec ts2 ts).
                  * inv TS. specialize (TS1 l). subst. eapply sim_mem_no_msgs; eauto.
                  * eapply Memory.no_msgs_weaken; eauto. rewrite app_nil_r. apply EXCLUSIVE; ss.
                + eapply Memory.no_msgs_weaken; eauto. rewrite app_nil_r. apply EXCLUSIVE; ss.
            }
          * econs 4; ss.
        + econs; ss.
          { econs; ss. apply sim_rmap_add; ss. }
          inv LOCAL. econs; ss; i.
          all: repeat rewrite fun_add_spec.
          all: repeat apply sim_view_join; ss.
          all: try condtac; ss.
          * inversion e. subst. econs; ss.
            { rewrite <- TS0. inv WRITABLE. ss. clear -EXT. unfold join, Time.join in *. lia. }
            { clear -TS0. lia. }
            { erewrite sim_mem_read; eauto. eapply Memory.get_msg_read; eauto. }
            { eapply Memory.get_msg_read; eauto. }
          * rewrite ? Promises.unset_o. condtac; ss. eauto.
          * rewrite Promises.unset_o. condtac; ss.
            { clear X. inv e. clear -TS0 TSP. lia. }
            { eauto. }
          * inv MEM. econs; ss.
            { i. exploit SRC_PROMISES; eauto. i. des. subst. splits; ss.
              exploit SRC_PROMISES_BELOW; eauto. rewrite ? fun_add_spec.
              condtac; ss. clear X. inv e. i.
              eapply le_lt_trans; eauto. apply SRC_PROMISES_WF. ss.
            }
            { i. exploit MEM1'; eauto. i. des. subst.
              esplits; try exact MSG0; ss.
              { rewrite fun_add_spec. condtac; ss. inversion e. destruct msg1, msg2. ss. subst.
                inv WRITABLE. ss. exploit sim_view_below.
                { inv LOCAL. apply COH0. }
                { rewrite <- TS0. apply Nat.le_lteq. left. eauto. }
                i. rewrite <- x1 in *. clear -TS0 COH MSGCOH. lia.
              }
              { rewrite fun_add_spec. condtac; ss. inversion e. destruct msg1, msg2. ss. subst.
                inv WRITABLE. ss. exploit sim_view_below.
                { inv LOCAL. apply COH0. }
                { rewrite <- TS0. apply Nat.le_lteq. left. eauto. }
                i. rewrite <- x1 in *. clear -TS0 COH MSGCOH. lia.
              }
            }
      }
      { (* fulfilling a new promise > ts (only in tgt) *)
        rename l into TS0.
        eexists (ExecUnit.mk _ _ _). esplits.
        - econs 2. econs; ss.
          + econs; ss.
          + econs; ss.
            * inv WF1. ss. inv LOCAL0. inv WRITABLE. ss. econs; ss.
              { eapply le_lt_trans; [|ss]. apply COH. }
              { eapply le_lt_trans; [|ss]. s. repeat apply join_spec; ss.
                all: unfold ifc.
                all: try condtac; ss.
                all: try apply bot_spec.
                - apply ExecUnit.expr_wf. ss.
                - apply ExecUnit.expr_wf. ss.
                - destruct lc1; ss. destruct exbank; [|by apply bot_spec].
                  exploit EXBANK; eauto. intro Y. inv Y. rewrite VIEW. ss.
              }
              { intro X. specialize (EX X). des. inv LOCAL. inv EXBANK0; [congr|].
                rewrite TSX in H. inv H. esplits; eauto.
                destruct a, eb. ss. i. subst.
                eapply Memory.no_msgs_split; swap 1 2.
                { apply Nat.le_succ_diag_r. }
                { exploit EXBANK; eauto. s. intro Y. inv Y. ss.
                  rewrite TS, <- COH. apply Memory.latest_ts_spec.
                }
                split.
                - apply Memory.no_msgs_full; ss. eapply sim_mem1_exclusive; eauto.
                  inv REL; ss. subst. destruct (le_lt_dec ts2 ts); eauto.
                  inv TS. rewrite TS1 in *; ss.
                  eapply sim_mem_no_msgs; eauto.
                  eapply Memory.no_msgs_weaken; cycle 1.
                  { rewrite app_nil_r, ELOC. apply EX0; ss. rewrite ELOC. ss. }
                  { clear -TS0. lia. }
                - ii. replace ts3 with (length mem1) in * by (clear -TS1 TS2; lia).
                  rewrite nth_error_app2, Nat.sub_diag in MSG0; ss. inv MSG0. des. ss.
              }
            * unfold Memory.get_msg. s. rewrite nth_error_app2, Nat.sub_diag; ss.
            * rewrite Promises.set_o. condtac; ss. congr.
        - rewrite <- ELOC in *. inv WRITABLE. ss. econs; ss.
          + econs; ss. apply sim_rmap_add; ss. econs; ss.
            unfold ifc. condtac; ss. intro Y. clear -Y TS0. lia.
          + inv LOCAL. econs; ss.
            * i. rewrite ? fun_add_spec. condtac; ss. apply sim_view_above. ss.
            * apply sim_view_join; ss. apply sim_view_above. ss.
            * apply sim_view_join; ss.
            * apply sim_view_join; ss. unfold ifc. condtac; ss. apply sim_view_above. ss.
            * i. rewrite ? fun_add_spec. condtac; ss.
              { inversion e. subst.
                destruct (le_lt_dec (View.ts (ValA.annot (sem_expr rmap2 eval))) ts).
                - exploit sim_rmap_expr; eauto. instantiate (1 := eval).
                  intro Y. inv Y. exploit TS; ss. clear TS. intro EVAL. rewrite <- EVAL in *.
                  econs 1; ss.
                  + apply join_spec; ss. rewrite <- VCAP, <- join_r. ss.
                  + apply sim_time_above. ss.
                  + splits.
                    * clear -LEN. lia.
                    * apply Memory.ge_no_msgs. clear. rewrite app_length. s. lia.
                  + unfold Memory.read. s. rewrite ? nth_error_app2, ? Nat.sub_diag; ss. condtac; ss.
                  + eapply Memory.get_msg_read; eauto.
                - econs 2; ss.
                  + eapply lt_le_trans; eauto. apply join_r.
                  + rewrite app_length. s. ii. lia.
              }
              { exploit sim_fwdbank_mon; try exact MEM; cycle 3.
                - rewrite (@app_nil_r _ mem2). eauto.
                - ss.
                - inv WF1. ss. inv LOCAL. destruct (FWDBANK0 loc). des.
                  rewrite TS, <- COH1. apply Memory.latest_ts_spec.
                - econs; ss. destruct (nequiv_dec (ValA.val (sem_expr rmap1 eloc)) loc); ss. congr.
              }
            * destruct ex0; ss. inv EXBANK; econs; ss.
              exploit sim_exbank_mon; eauto. rewrite (@app_nil_r _ mem2). eauto.
            * i. rewrite ? Promises.unset_o, ? Promises.set_o. condtac.
              { inversion e. subst. clear -TSP MEM. inv MEM. rewrite app_length in TSP. lia. }
              condtac.
              { inversion e. subst. clear -TS0 TSP. lia. }
              apply PROMISES1. ss.
            * i. rewrite Promises.unset_o, Promises.set_o. condtac; ss.
              { clear X. inv e. rewrite <- PROMISES2; ss.
                erewrite Local.wf_promises_above; eauto. apply WF1.
              }
              { eauto. }
          + inv MEM. ss. econs.
            * ss.
            * rewrite <- app_assoc. ss.
            * ss.
            * i. exploit SRC_PROMISES_WF; eauto. i. des. esplits; ss.
              { apply nth_error_app_mon; eauto. }
              { ii. eapply x2; eauto. apply nth_error_snoc_inv in MSG0. des; subst; ss. }
              { rewrite app_length. s. ii. apply nth_error_snoc_inv in MSG0. des; subst; ss.
                - eapply x3; eauto.
                - exploit SRC_PROMISES_BELOW; eauto. rewrite fun_add_spec. condtac; ss; [|congr].
                  clear -TS0. lia.
              }
            * i. apply nth_error_snoc_inv in MSG0. des.
              { exploit SRC_PROMISES; eauto. i. des. subst. splits; ss.
                exploit SRC_PROMISES_BELOW; eauto. rewrite ? fun_add_spec.
                condtac; ss. clear X. inv e. i. clear -TS0 x. lia.
              }
              { subst. splits; ss.
                rewrite fun_add_spec. condtac; ss; cycle 1.
                { exfalso. apply c. clear. refl. }
                apply SRC_PROMISES_WF in TSP. des.
                apply nth_error_some in TSP0. clear -TSP0. lia.
              }
            * i. apply Memory.get_msg_snoc_inv in READ. des; eauto. subst. ss.
            * i. apply nth_error_snoc_inv in NTH. des.
              { exploit MEM1'; eauto. i. des. subst. esplits; try exact MSG0; ss.
                - rewrite fun_add_spec. condtac; ss. rewrite app_length.
                  exploit nth_error_Some. rewrite NTH0. intros [Y _]. clear -Y.
                  exploit Y; [congr|]. lia.
                - rewrite fun_add_spec. condtac; ss. inversion e. destruct msg1, msg2. ss. subst.
                  rewrite MSGCOH0. clear -COH. ss. lia.
              }
              { subst. ss. apply Memory.get_msg_app_inv in MSG. des.
                { clear -MSG TS0. lia. }
                esplits; try exact MSG0; eauto.
                - rewrite fun_add_spec. condtac; [|congr]. s. rewrite app_length. ss.
                - s. rewrite fun_add_spec. condtac; [|congr]. s. clear -TS0. lia.
              }
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
        rewrite ELOC. econs; ss.
    - (* dowhile *)
      eexists (ExecUnit.mk _ _ _). esplits.
      + econs 1. econs. econs; ss; cycle 1.
        * econs 1; eauto.
        * econs 7. ss.
      + econs; ss.
  }
Qed.

Lemma sim_eu_rtc_step
      tid ts ts_private src_promises eu1 eu2 eu2'
      (SIM: sim_eu tid ts ts_private src_promises eu1 eu2)
      (STEP: rtc (certify_step tid) eu2 eu2')
      (SRC_PROMISES_BELOW: forall tsp msg
                             (TSP: Promises.lookup (S tsp) src_promises)
                             (MEM: nth_error eu1.(ExecUnit.mem) tsp = Some msg),
          (eu2'.(ExecUnit.local).(Local.coh) msg.(Msg.loc)).(View.ts) <= ts)
      (WF1: ExecUnit.wf tid eu1)
      (WF2: ExecUnit.wf tid eu2)
      (VCAP: eu2'.(ExecUnit.local).(Local.vcap).(View.ts) <= ts):
  exists eu1',
    <<STEP: rtc (certify_step tid) eu1 eu1'>> /\
    <<SIM: sim_eu tid ts ts_private src_promises eu1' eu2'>>.
Proof.
  revert eu1 SIM SRC_PROMISES_BELOW WF1 WF2. induction STEP; eauto.
  i. destruct (le_lt_dec (View.ts (Local.vcap (ExecUnit.local y))) ts).
  - exploit sim_eu_step; eauto.
    { i. exploit SRC_PROMISES_BELOW; eauto. i. rewrite <- x0.
      admit. (* coh monotone *)
    }
    i. des.
    exploit certify_step_wf; try exact H; eauto. i.
    exploit certify_step_wf; eauto. i.
    exploit IHSTEP; eauto.
    { i. exploit SRC_PROMISES_BELOW; eauto.
      admit. (* mem monotone *)
    }
    i. des.
    esplits; [|by eauto]. econs; eauto.
  - admit. (* vcap monotone *)
Admitted.

Lemma sim_eu_promises
      tid ts ts_private src_promises eu1 eu2
      (SIM: sim_eu tid ts ts_private src_promises eu1 eu2)
      (EU2: forall tsp (TSP: tsp <= ts), Promises.lookup tsp eu2.(ExecUnit.local).(Local.promises) = false):
  eu1.(ExecUnit.local).(Local.promises) = src_promises.
Proof.
  apply Promises.ext. i. inv SIM. inv LOCAL. destruct (le_lt_dec i ts).
  - rewrite PROMISES1, EU2; ss. destruct (Promises.lookup i src_promises) eqn:TSP; ss.
    destruct i; ss.
    inv MEM. exploit SRC_PROMISES_WF; eauto. i. des. clear -l x. lia.
  - rewrite PROMISES2; ss.
Qed.

Lemma sim_eu_rtc_step_bot
      tid ts ts_private src_promises eu1 eu2 eu2'
      (SIM: sim_eu tid ts ts_private src_promises eu1 eu2)
      (STEP: rtc (certify_step tid) eu2 eu2')
      (SRC_PROMISES_BELOW: forall tsp msg
                             (TSP: Promises.lookup (S tsp) src_promises)
                             (MEM: nth_error eu1.(ExecUnit.mem) tsp = Some msg),
          (eu2'.(ExecUnit.local).(Local.coh) msg.(Msg.loc)).(View.ts) <= ts)
      (WF1: ExecUnit.wf tid eu1)
      (WF2: ExecUnit.wf tid eu2)
      (PROMISES: eu2'.(ExecUnit.local).(Local.promises) = bot):
  exists eu1',
    <<STEP: rtc (certify_step tid) eu1 eu1'>> /\
    <<PROMISES: eu1'.(ExecUnit.local).(Local.promises) = src_promises>>.
Proof.
  revert eu1 SIM SRC_PROMISES_BELOW WF1 WF2. induction STEP; ss.
  { esplits; eauto.
    eapply sim_eu_promises; eauto. rewrite PROMISES.
    i. rewrite Promises.lookup_bot. ss.
  }
  i. destruct (le_lt_dec (View.ts (Local.vcap (ExecUnit.local y))) ts).
  - exploit sim_eu_step; eauto.
    { i. exploit SRC_PROMISES_BELOW; eauto. i. rewrite <- x0.
      admit. (* coh monotone *)
    }
    i. des.
    exploit certify_step_wf; try exact H; eauto. i.
    exploit certify_step_wf; eauto. i.
    exploit IHSTEP; eauto.
    { i. exploit SRC_PROMISES_BELOW; eauto.
      admit. (* mem monotone *)
    }
    i. des.
    esplits; [|by eauto]. econs; eauto.
  - esplits; eauto. eapply sim_eu_promises; eauto. i.
    exploit certify_step_wf; eauto. i.
    assert (PROMISES': forall tsp (TSP: tsp <= ts), Promises.lookup tsp y.(ExecUnit.local).(Local.promises) = false).
    { i. destruct (Promises.lookup tsp0 (Local.promises (ExecUnit.local y))) eqn:X; ss.
      destruct tsp0; ss.
      exploit rtc_certify_step_vcap_promise; try exact X; eauto.
      - lia.
      - rewrite PROMISES. ss.
    }
    destruct x as [st1 lc1 mem1].
    destruct y as [st2 lc2 mem2].
    ss. inv H.
    + inv STEP0. inv STEP1. ss. subst.
      inv STATE; inv LOCAL; inv EVENT; ss.
      all: eauto.
      all: try inv STEP0; ss; eauto.
      all: try inv LC; ss; eauto.
      generalize (PROMISES' tsp TSP). rewrite Promises.unset_o. condtac; ss. inversion e. subst.
      inv WRITABLE. ss. clear -l TSP EXT. unfold join, Time.join in *. lia.
    + inv STEP0. ss. inv STATE. inv PROMISE. inv FULFILL. ss.
      generalize (PROMISES' tsp TSP). rewrite Promises.unset_o, Promises.set_o. condtac; ss. inversion e. subst.
      inv WRITABLE. ss. clear -l TSP EXT. unfold join, Time.join in *. lia.
Admitted.
