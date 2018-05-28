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

Set Implicit Arguments.


Module Msg.
  Inductive t := mk {
    loc: Loc.t;
    val: Val.t;
    tid: Id.t;
  }.
  Hint Constructors t.

  Global Program Instance eqdec: EqDec t eq.
  Next Obligation.
    destruct x, y.

    destruct (loc0 == loc1); cycle 1.
    { right. intro X. inv X. intuition. }

    destruct (val0 == val1); cycle 1.
    { right. intro X. inv X. intuition. }

    destruct (tid0 == tid1); cycle 1.
    { right. intro X. inv X. intuition. }

    left. f_equal; intuition.
  Defined.
End Msg.

Module Memory.
  Definition t := list Msg.t.

  Definition empty: t := [].

  Definition read (ts:Time.t) (loc:Loc.t) (mem:t): option Val.t :=
    match Time.pred_opt ts with
    | None => Some Val.default
    | Some ts =>
      match List.nth_error mem ts with
      | None => None
      | Some msg =>
        if msg.(Msg.loc) == loc
        then Some msg.(Msg.val)
        else None
      end
    end.

  Definition get_msg (ts:Time.t) (mem:t): option Msg.t :=
    match Time.pred_opt ts with
    | None => None
    | Some ts => List.nth_error mem ts
    end.

  Definition append (msg:Msg.t) (mem:t): Time.t * t :=
    (S (length mem), mem ++ [msg]).

  Definition no_msgs (from to:nat) (pred:Msg.t -> Prop) (mem:t): Prop :=
    forall ts msg
      (TS1: from < S ts)
      (TS2: S ts <= to)
      (MSG: List.nth_error mem ts = Some msg),
      ~ pred msg.
End Memory.

Module FwdItem.
  Inductive t := mk {
    ts: Time.t;
    view: View.t;
    ex: bool;
  }.
  Hint Constructors t.

  Definition read_view (fwd:t) (tsx:Time.t) (ord:OrdR.t): View.t :=
    if andb (fwd.(ts) == tsx) (orb (negb fwd.(ex)) (negb (OrdR.ge ord OrdR.acquire_pc)))
    then fwd.(view)
    else tsx.
End FwdItem.

Definition fwdBankT := Loc.t -> option FwdItem.t.

Definition exBankT := option Time.t.

Definition cohT := Loc.t -> Time.t.

Module Promises.
  Include IdSet.

  Definition id_of_time (ts:Time.t): option positive :=
    option_map Pos.of_succ_nat (Time.pred_opt ts).

  Lemma id_of_time_inj ts ts'
        (EQ: id_of_time ts = id_of_time ts'):
    ts = ts'.
  Proof.
    revert EQ. unfold id_of_time, Time.pred_opt.
    destruct ts, ts'; ss. i. inv EQ.
    f_equal. apply SuccNat2Pos.inj. ss.
  Qed.

  Definition lookup (ts:Time.t) (promises:t): bool :=
    match id_of_time ts with
    | None => false
    | Some ts => mem ts promises
    end.

  Definition set (ts:Time.t) (promises:t): t :=
    match id_of_time ts with
    | None => promises
    | Some ts => add ts promises
    end.

  Lemma set_o ts' ts promises:
    lookup ts' (set ts promises) =
    if ts' == ts
    then ts' <> 0
    else lookup ts' promises.
  Proof.
    unfold lookup, set.
    destruct (id_of_time ts') eqn:X', (id_of_time ts) eqn:X, (equiv_dec ts' ts); ss;
      destruct ts, ts'; ss;
      try rewrite add_o in *.
    - inv e. rewrite X in X'. inv X'. condtac; intuition.
    - condtac; ss. inversion e. subst.
      rewrite <- X' in X. apply id_of_time_inj in X. inv X. intuition.
  Qed.

  Definition unset (ts:Time.t) (promises:t): t :=
    match id_of_time ts with
    | None => promises
    | Some ts => IdSet.remove ts promises
    end.

  Lemma unset_o ts' ts promises:
    lookup ts' (unset ts promises) =
    if ts' == ts
    then false
    else lookup ts' promises.
  Proof.
    unfold lookup, unset.
    destruct (id_of_time ts') eqn:X', (id_of_time ts) eqn:X, (equiv_dec ts' ts); ss;
      destruct ts, ts'; ss;
      try rewrite remove_o in *.
    - inv e. rewrite X in X'. inv X'. condtac; intuition.
    - condtac; ss. inversion e. subst.
      rewrite <- X' in X. apply id_of_time_inj in X. inv X. intuition.
  Qed.

  Definition IsEmpty (promises:t) :=
    forall ts, lookup ts promises = false.

  Lemma lookup_empty view:
    lookup view empty = false.
  Proof.
    unfold lookup. destruct (id_of_time view); ss.
  Qed.
End Promises.

Module Local.
  Inductive t := mk {
    coh: cohT;
    vrp: View.t;
    vwp: View.t;
    vrm: View.t;
    vwm: View.t;
    vcap: View.t;
    vrel: View.t;
    fwdbank: fwdBankT;
    exbank: exBankT;
    promises: Promises.t;
  }.
  Hint Constructors t.

  Definition init: t := mk bot bot bot bot bot bot bot (fun _ => None) bot IdSet.empty.

  Definition init_with_promises (promises: Promises.t): Local.t :=
    mk bot bot bot bot bot bot bot (fun _ => None) bot promises.

  Inductive promise (loc:Loc.t) (val:Val.t) (tid:Id.t) (lc1:t) (mem1:Memory.t) (lc2:t) (mem2:Memory.t): Prop :=
  | promise_intro
      ts
      (LC2: lc2 =
            mk
              lc1.(coh)
              lc1.(vrp)
              lc1.(vwp)
              lc1.(vrm)
              lc1.(vwm)
              lc1.(vcap)
              lc1.(vrel)
              lc1.(fwdbank)
              lc1.(exbank)
              (Promises.set ts lc1.(promises)))
      (MEM2: Memory.append (Msg.mk loc val tid) mem1 = (ts, mem2))
  .
  Hint Constructors promise.

  Inductive internal (ctrl:View.t) (lc1 lc2:t): Prop :=
  | internal_intro
      (LC2: lc2 = 
            mk
              lc1.(coh)
              lc1.(vrp)
              lc1.(vwp)
              lc1.(vrm)
              lc1.(vwm)
              (join lc1.(vcap) ctrl)
              lc1.(vrel)
              lc1.(fwdbank)
              lc1.(exbank)
              lc1.(promises))
  .
  Hint Constructors internal.

  Inductive read (ex:bool) (ord:OrdR.t) (vloc:ValA.t (A:=View.t)) (res: ValA.t (A:=View.t)) (lc1:t) (mem1: Memory.t) (lc2:t): Prop :=
  | read_intro
      ts loc val view
      view_ext1 view_ext2
      (LOC: loc = vloc.(ValA.val))
      (VIEW: view = vloc.(ValA.annot))
      (VIEW_EXT1: view_ext1 = joins [view; lc1.(vrp); (ifc (OrdR.ge ord OrdR.acquire) lc1.(vrel))])
      (COH: le (lc1.(coh) loc) ts)
      (LATEST: Memory.no_msgs ts view_ext1 (fun msg => msg.(Msg.loc) = loc) mem1)
      (MSG: Memory.read ts loc mem1 = Some val)
      (VIEW_EXT2: view_ext2 = join view_ext1 (match lc1.(fwdbank) loc with
                                              | None => ts
                                              | Some fwd => fwd.(FwdItem.read_view) ts ord
                                              end))
      (RES: res = ValA.mk _ val view_ext2)
      (LC2: lc2 =
            mk
              (fun_add loc ts lc1.(coh))
              (join lc1.(vrp) (ifc (OrdR.ge ord OrdR.acquire_pc) view_ext2))
              (join lc1.(vwp) (ifc (OrdR.ge ord OrdR.acquire_pc) view_ext2))
              (join lc1.(vrm) view_ext2)
              lc1.(vwm)
              (join lc1.(vcap) view)
              lc1.(vrel)
              lc1.(fwdbank)
              (if ex then Some ts else lc1.(exbank))
              lc1.(promises))
  .
  Hint Constructors read.

  Inductive fulfill (ex:bool) (ord:OrdW.t) (vloc:ValA.t (A:=View.t)) (vval:ValA.t (A:=View.t)) (res: ValA.t (A:=View.t)) (tid:Id.t) (lc1:t) (mem1: Memory.t) (lc2:t): Prop :=
  | fulfill_intro
      ts loc val
      view_loc view_val view_ext
      (LOC: loc = vloc.(ValA.val))
      (VIEW_LOC: view_loc = vloc.(ValA.annot))
      (VAL: val = vval.(ValA.val))
      (VIEW_VAL: view_val = vval.(ValA.annot))
      (VIEW_EXT: view_ext = joins [
                                view_loc; view_val; lc1.(vcap); lc1.(vwp);
                                ifc (OrdW.ge ord OrdW.release) lc1.(vrm);
                                ifc (OrdW.ge ord OrdW.release) lc1.(vwm)
                             ])
      (COH: lt (lc1.(coh) loc) ts)
      (EXT: lt view_ext ts)
      (EX: ex -> exists tsx,
           <<TSX: lc1.(exbank) = Some tsx>> /\
           <<LATEST: forall valx (READ: Memory.read tsx loc mem1 = Some valx),
               Memory.no_msgs tsx ts (fun msg => msg.(Msg.loc) = loc /\ msg.(Msg.tid) <> tid) mem1>>)
      (MSG: Memory.get_msg ts mem1 = Some (Msg.mk loc val tid))
      (RES: res = ValA.mk _ 0 bot)
      (LC2: lc2 =
            mk
              (fun_add loc ts lc1.(coh))
              lc1.(vrp)
              lc1.(vwp)
              lc1.(vrm)
              (join lc1.(vwm) ts)
              (join lc1.(vcap) view_loc)
              (join lc1.(vrel) (ifc (OrdW.ge ord OrdW.release) ts))
              (fun_add loc (Some (FwdItem.mk ts (join view_loc view_val) ex)) lc1.(fwdbank))
              (if ex then None else lc1.(exbank))
              (Promises.unset ts lc1.(promises)))
  .
  Hint Constructors fulfill.

  Inductive write_failure (ex:bool) (res: ValA.t (A:=View.t)) (lc1:t) (lc2:t): Prop :=
  | write_failure_intro
      (EX: ex)
      (RES: res = ValA.mk _ 1 bot)
      (LC2: lc2 =
            mk
              lc1.(coh)
              lc1.(vrp)
              lc1.(vwp)
              lc1.(vrm)
              lc1.(vwm)
              lc1.(vcap)
              lc1.(vrel)
              lc1.(fwdbank)
              None
              lc1.(promises))
  .
  Hint Constructors write_failure.

  Inductive isb (lc1 lc2:t): Prop :=
  | isb_intro
      (LC2: lc2 = 
            mk
              lc1.(coh)
              (join lc1.(vrp) lc1.(vcap))
              lc1.(vwp)
              lc1.(vrm)
              lc1.(vwm)
              lc1.(vcap)
              lc1.(vrel)
              lc1.(fwdbank)
              lc1.(exbank)
              lc1.(promises))
  .
  Hint Constructors isb.

  Inductive dmbst (lc1 lc2:t): Prop :=
  | dmbst_intro
      (LC2: lc2 = 
            mk
              lc1.(coh)
              lc1.(vrp)
              (join lc1.(vwp) lc1.(vwm))
              lc1.(vrm)
              lc1.(vwm)
              lc1.(vcap)
              lc1.(vrel)
              lc1.(fwdbank)
              lc1.(exbank)
              lc1.(promises))
  .
  Hint Constructors dmbst.

  Inductive dmbld (lc1 lc2:t): Prop :=
  | dmbld_intro
      (LC2: lc2 = 
            mk
              lc1.(coh)
              (join lc1.(vrp) lc1.(vrm))
              (join lc1.(vwp) lc1.(vrm))
              lc1.(vrm)
              lc1.(vwm)
              lc1.(vcap)
              lc1.(vrel)
              lc1.(fwdbank)
              lc1.(exbank)
              lc1.(promises))
  .
  Hint Constructors dmbld.

  Inductive dmbsy (lc1 lc2:t): Prop :=
  | dmbsy_intro
      (LC2: lc2 = 
            mk
              lc1.(coh)
              (joins [lc1.(vrp); lc1.(vrm); lc1.(vwm)])
              (joins [lc1.(vwp); lc1.(vrm); lc1.(vwm)])
              lc1.(vrm)
              lc1.(vwm)
              lc1.(vcap)
              lc1.(vrel)
              lc1.(fwdbank)
              lc1.(exbank)
              lc1.(promises))
  .
  Hint Constructors dmbsy.

  Inductive step (event:Event.t (A:=View.t)) (tid:Id.t) (lc1:t) (mem1:Memory.t) (lc2:t): Prop :=
  | step_internal
      ctrl
      (EVENT: event = (Event.internal ctrl))
      (LC: internal ctrl lc1 lc2)
  | step_read
      ex ord vloc res
      (EVENT: event = Event.read ex ord vloc res)
      (STEP: read ex ord vloc res lc1 mem1 lc2)
  | step_fulfill
      ex ord vloc vval res
      (EVENT: event = Event.write ex ord vloc vval res)
      (STEP: fulfill ex ord vloc vval res tid lc1 mem1 lc2)
  | step_write_failure
      ex ord vloc vval res
      (EVENT: event = Event.write ex ord vloc vval res)
      (STEP: write_failure ex res lc1 lc2)
  | step_isb
      (EVENT: event = Event.barrier Barrier.isb)
      (STEP: isb lc1 lc2)
  | step_dmbst
      (EVENT: event = Event.barrier Barrier.dmbst)
      (STEP: dmbst lc1 lc2)
  | step_dmbld
      (EVENT: event = Event.barrier Barrier.dmbld)
      (STEP: dmbld lc1 lc2)
  | step_dmbsy
      (EVENT: event = Event.barrier Barrier.dmbsy)
      (STEP: dmbsy lc1 lc2)
  .
  Hint Constructors step.
End Local.

Module ExecUnit.
  Inductive t := mk {
    state: State.t (A:=View.t);
    local: Local.t;
    mem: Memory.t;
  }.
  Hint Constructors t.

  Inductive state_step (tid:Id.t) (eu1 eu2:t): Prop :=
  | state_step_intro
      e
      (STATE: State.step e eu1.(state) eu2.(state))
      (LOCAL: Local.step e tid eu1.(local) eu1.(mem) eu2.(local))
      (MEM: eu2.(mem) = eu1.(mem))
  .

  Inductive promise_step (tid:Id.t) (eu1 eu2:t): Prop :=
  | promise_step_intro
      loc val
      (STATE: eu1.(state) = eu2.(state))
      (LOCAL: Local.promise loc val tid eu1.(local) eu1.(mem) eu2.(local) eu2.(mem))
  .

  Inductive step (tid:Id.t) (eu1 eu2:t): Prop :=
  | step_state (STEP: state_step tid eu1 eu2)
  | step_promise (STEP: promise_step tid eu1 eu2)
  .
End ExecUnit.

Module Machine.
  Inductive t := mk {
    tpool: IdMap.t (State.t (A:=View.t) * Local.t);
    mem: Memory.t;
  }.
  Hint Constructors t.

  Definition init (p:program): t :=
    mk
      (IdMap.map (fun stmts => (State.init stmts, Local.init)) p)
      Memory.empty.

  Inductive is_terminal (m:t): Prop :=
  | is_terminal_intro
      (TERMINAL:
         forall tid st lc
           (FIND: IdMap.find tid m.(tpool) = Some (st, lc)),
           State.is_terminal st /\ Promises.IsEmpty lc.(Local.promises))
  .
  Hint Constructors is_terminal.

  Inductive no_promise (m:t): Prop :=
  | no_promise_intro
      (PROMISES:
         forall tid st lc
           (FIND: IdMap.find tid m.(tpool) = Some (st, lc)),
           Promises.IsEmpty lc.(Local.promises))
  .
  Hint Constructors no_promise.

  Inductive step0 (eustep: forall (tid:Id.t) (eu1 eu2:ExecUnit.t), Prop) (m1 m2:t): Prop :=
  | step0_intro
      tid st1 lc1 st2 lc2
      (FIND: IdMap.find tid m1.(tpool) = Some (st1, lc1))
      (STEP: eustep tid (ExecUnit.mk st1 lc1 m1.(mem)) (ExecUnit.mk st2 lc2 m2.(mem)))
      (ADD: m2.(tpool) = IdMap.add tid (st2, lc2) m1.(tpool))
  .
  Hint Constructors step0.

  (* The "global" consistency condition: in certification, machine may take any thread's steps. *)
  Inductive consistent (eustep: forall (tid:Id.t) (eu1 eu2:ExecUnit.t), Prop) (m:t): Prop :=
  | consistent_intro
      m'
      (STEP: rtc (step0 eustep) m m')
      (NOPROMISE: no_promise m')
  .
  Hint Constructors consistent.

  Inductive step (eustep: forall (tid:Id.t) (eu1 eu2:ExecUnit.t), Prop) (m1 m2:t): Prop :=
  | step_intro
      (STEP: step0 eustep m1 m2)
      (CONSISTENT: consistent eustep m2)
  .
  Hint Constructors step.

  Inductive pf_init (p:program) (m:t): Prop :=
  | init_pf_intro
      (STEP: rtc (step0 ExecUnit.promise_step) (init p) m)
      (CONSISTENT: consistent ExecUnit.state_step m)
  .

  Lemma no_promise_consistent
        eustep m
        (NOPROMISE: no_promise m):
    consistent eustep m.
  Proof. econs; eauto. Qed.
        
  Lemma rtc_step0_step eustep m1 m2
        (STEP: rtc (step0 eustep) m1 m2)
        (CONSISTENT: consistent eustep m2):
    rtc (step eustep) m1 m2.
  Proof.
    revert CONSISTENT. induction STEP; [refl|]. i. econs.
    - econs; eauto. inv CONSISTENT. econs; [|by eauto]. etrans; eauto.
    - eauto.
  Qed.

  Lemma rtc_eu_step_step0
        eustep tid m st1 lc1 mem1 st2 lc2 mem2
        (FIND: IdMap.find tid m.(tpool) = Some (st1, lc1))
        (MEM: m.(mem) = mem1)
        (EX: rtc (eustep tid)
                 (ExecUnit.mk st1 lc1 mem1)
                 (ExecUnit.mk st2 lc2 mem2)):
    rtc (step0 eustep)
        m
        (mk
           (IdMap.add tid (st2, lc2) m.(tpool))
           mem2).
  Proof.
    revert m FIND MEM.
    depind EX.
    { i. subst. destruct m. s. rewrite PositiveMapAdditionalFacts.gsident; ss. refl. }
    destruct y. i. subst. econs.
    - instantiate (1 := mk _ _). econs; ss; eauto.
    - exploit IHEX; eauto.
      + instantiate (1 := mk _ _). s.
        rewrite IdMap.add_spec. condtac; eauto. exfalso. apply c. ss.
      + ss.
      + s. rewrite (IdMap.add_add tid (st2, lc2)). eauto.
  Qed.
End Machine.

Lemma reorder_state_step_promise_step
      m1 m2 m3
      (STEP1: Machine.step0 ExecUnit.state_step m1 m2)
      (STEP2: Machine.step0 ExecUnit.promise_step m2 m3):
  exists m2',
    <<STEP: Machine.step0 ExecUnit.promise_step m1 m2'>> /\
    <<STEP: Machine.step0 ExecUnit.state_step m2' m3>>.
Proof.
  destruct m1 as [tpool1 mem1].
  destruct m2 as [tpool2 mem2].
  destruct m3 as [tpool3 mem3].
  inv STEP1. inv STEP2. ss. subst.
  revert FIND0. rewrite IdMap.add_spec. condtac.
  - (* same thread *)
    inversion e. i. inv FIND0.
    inv STEP. inv STEP0. inv LOCAL0. inv MEM2. ss. subst.
    eexists (Machine.mk _ _). esplits.
    + econs; eauto; ss. econs; ss. econs; ss.
    + econs; ss.
      * rewrite IdMap.add_spec. instantiate (3 := tid). condtac; [|congr]. eauto.
      * econs; eauto; ss.
        admit.
      * rewrite ? IdMap.add_add. eauto.
  - (* diff thread *)
    inv STEP. inv STEP0. inv LOCAL0. inv MEM2. ss. subst.
    eexists (Machine.mk _ _). esplits.
    + econs; eauto; ss. econs; ss. econs; ss.
    + econs; ss.
      * rewrite IdMap.add_spec. instantiate (3 := tid). condtac; [|by eauto].
        inversion e0. subst. congr.
      * econs; eauto; ss.
        inv LOCAL.
        { econs 1; eauto. }
        { admit. }
        { admit. }
        { econs 4; eauto. }
        { econs 5; eauto. }
        { econs 6; eauto. }
        { econs 7; eauto. }
        { econs 8; eauto. }
      * apply IdMap.add_add_diff. ss.
Admitted.

Lemma reorder_state_step_rtc_promise_step
      m1 m2 m3
      (STEP1: Machine.step0 ExecUnit.state_step m1 m2)
      (STEP2: rtc (Machine.step0 ExecUnit.promise_step) m2 m3):
  exists m2',
    <<STEP: rtc (Machine.step0 ExecUnit.promise_step) m1 m2'>> /\
    <<STEP: Machine.step0 ExecUnit.state_step m2' m3>>.
Proof.
  revert m1 STEP1. induction STEP2; eauto.
  i. exploit reorder_state_step_promise_step; eauto. i. des.
  exploit IHSTEP2; eauto. i. des.
  esplits; cycle 1; eauto.
Qed.

Lemma split_rtc_step
      m1 m3
      (STEP: rtc (Machine.step0 ExecUnit.step) m1 m3):
  exists m2,
    <<STEP: rtc (Machine.step0 ExecUnit.promise_step) m1 m2>> /\
    <<STEP: rtc (Machine.step0 ExecUnit.state_step) m2 m3>>.
Proof.
  induction STEP; eauto.
  des. inv H. inv STEP2.
  - exploit reorder_state_step_rtc_promise_step; eauto. i. des.
    esplits; eauto.
  - esplits; cycle 1; eauto.
Qed.

Theorem init_step_pf_init_step
        p m
        (STEP: rtc (Machine.step ExecUnit.step) (Machine.init p) m):
  exists m',
    <<INIT: Machine.pf_init p m'>> /\
    <<STEP: rtc (Machine.step ExecUnit.state_step) m' m>>.
Proof.
Admitted.

Theorem pf_init_step_init_step
        p m1 m2
        (INIT: Machine.pf_init p m1)
        (STEP: rtc (Machine.step ExecUnit.state_step) m1 m2):
  rtc (Machine.step ExecUnit.step) (Machine.init p) m2.
Proof.
Admitted.
