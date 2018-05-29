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

  Lemma read_mon ts loc val mem1 mem2
        (READ: Memory.read ts loc mem1 = Some val):
    Memory.read ts loc (mem1 ++ mem2) = Some val.
  Proof.
    revert READ. unfold Memory.read. destruct (Time.pred_opt ts); ss.
    destruct (nth_error mem1 t0) eqn:NTH; ss.
    rewrite List.nth_error_app1, NTH; ss.
    apply List.nth_error_Some. congr.
  Qed.

  Lemma get_msg_mon ts msg mem1 mem2
        (READ: Memory.get_msg ts mem1 = Some msg):
    Memory.get_msg ts (mem1 ++ mem2) = Some msg.
  Proof.
    revert READ. unfold Memory.get_msg. destruct (Time.pred_opt ts); ss.
    destruct (nth_error mem1 t0) eqn:NTH; ss.
    rewrite List.nth_error_app1, NTH; ss.
    apply List.nth_error_Some. congr.
  Qed.
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

  Inductive step (event:Event.t (A:=View.t)) (tid:Id.t) (mem:Memory.t) (lc1 lc2:t): Prop :=
  | step_internal
      ctrl
      (EVENT: event = (Event.internal ctrl))
      (LC: internal ctrl lc1 lc2)
  | step_read
      ex ord vloc res
      (EVENT: event = Event.read ex ord vloc res)
      (STEP: read ex ord vloc res lc1 mem lc2)
  | step_fulfill
      ex ord vloc vval res
      (EVENT: event = Event.write ex ord vloc vval res)
      (STEP: fulfill ex ord vloc vval res tid lc1 mem lc2)
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

  Inductive wf (mem:Memory.t) (lc:t): Prop :=
  | wf_intro
      (COH: forall loc, lc.(coh) loc <= List.length mem)
      (VRP: lc.(vrp) <= List.length mem)
      (VWP: lc.(vwp) <= List.length mem)
      (VRM: lc.(vrm) <= List.length mem)
      (VWM: lc.(vwm) <= List.length mem)
      (VCAP: lc.(vcap) <= List.length mem)
      (VREL: lc.(vrel) <= List.length mem)
      (FWDBANK: forall loc fwd,
          lc.(fwdbank) loc = Some fwd ->
          fwd.(FwdItem.ts) <= List.length mem /\
          fwd.(FwdItem.view) <= List.length mem)
      (EXBANK: forall ts, lc.(exbank) = Some ts -> ts <= List.length mem)
      (PROMISES: forall ts (IN: Promises.lookup ts lc.(promises)), ts <= List.length mem)
  .

  Lemma init_wf mem: wf mem init.
  Proof.
    econs; ss; i; try by apply bot_spec.
    rewrite Promises.lookup_empty in IN. ss.
  Qed.
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
      (LOCAL: Local.step e tid eu1.(mem) eu1.(local) eu2.(local))
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

  Inductive rmap_wf (mem:Memory.t) (rmap:RMap.t (A:=View.t)): Prop :=
  | rmap_wf_intro
      (RMAP: forall r, (RMap.find r rmap).(ValA.annot) <= List.length mem)
  .

  Inductive wf (eu:t): Prop :=
  | wf_intro
      (STATE: rmap_wf eu.(mem) eu.(state).(State.rmap))
      (LOCAL: Local.wf eu.(mem) eu.(local))
  .

  Ltac tac :=
    repeat
      (try match goal with
           | [|- join _ _ <= _] => apply join_spec
           | [|- bot <= _] => apply bot_spec
           | [|- View.join _ _ <= _] => apply join_spec
           | [|- View.bot <= _] => apply bot_spec
           | [|- ifc ?c _ <= _] => destruct c; s
           end;
       ss; eauto).

  Lemma rmap_add_wf
        mem rmap loc val
        (WF: rmap_wf mem rmap)
        (VAL: val.(ValA.annot) <= List.length mem):
    rmap_wf mem (RMap.add loc val rmap).
  Proof.
    inv WF. econs. i. unfold RMap.find, RMap.add. rewrite IdMap.add_spec.
    condtac; tac.
  Qed.

  Lemma expr_wf
        mem rmap e
        (RMAP: rmap_wf mem rmap):
    (sem_expr rmap e).(ValA.annot) <= List.length mem.
  Proof.
    induction e; tac. apply RMAP.
  Qed.

  Lemma read_wf
        ts loc val mem
        (READ: Memory.read ts loc mem = Some val):
    ts <= List.length mem.
  Proof.
    revert READ. unfold Memory.read. destruct ts; [lia|]. s.
    destruct (nth_error mem ts) eqn:NTH; ss. condtac; ss.
    i. eapply List.nth_error_Some. congr.
  Qed.

  Lemma get_msg_wf
        ts msg mem
        (READ: Memory.get_msg ts mem = Some msg):
    ts <= List.length mem.
  Proof.
    revert READ. unfold Memory.get_msg. destruct ts; [lia|]. s.
    destruct (nth_error mem ts) eqn:NTH; ss. i. inv READ.
    eapply List.nth_error_Some. congr.
  Qed.

  Lemma state_step_wf tid eu1 eu2
        (STEP: state_step tid eu1 eu2)
        (WF: wf eu1):
    wf eu2.
  Proof.
    destruct eu1 as [state1 local1 mem1].
    destruct eu2 as [state2 local2 mem2].
    inv WF. inv STEP. ss. subst.

    assert (FWD:
              forall loc ord ts,
                ts <= List.length mem1 ->
                match Local.fwdbank local1 loc with
                | Some fwd => FwdItem.read_view fwd ts ord
                | None => ts
                end <= length mem1).
    { inv LOCAL. i. destruct (Local.fwdbank local1 loc) eqn:FWD; ss.
      exploit FWDBANK; eauto. i. des.
      unfold FwdItem.read_view. condtac; ss.
    }

    inv STATE0; inv LOCAL0; inv EVENT; inv LOCAL; ss.
    - inv LC. econs; ss. econs; tac.
    - inv LC. econs; ss.
      + eauto using rmap_add_wf, expr_wf.
      + econs; tac.
    - inv STEP. econs; ss.
      + apply rmap_add_wf; tac.
        * eauto using expr_wf.
        * apply FWD. eauto using read_wf.
      + econs; tac; eauto using expr_wf.
        * i. rewrite fun_add_spec. condtac; tac.
          eapply read_wf. eauto.
        * apply FWD. eauto using read_wf.
        * apply FWD. eauto using read_wf.
        * apply FWD. eauto using read_wf.
        * destruct ex0; ss. i. inv H. eapply read_wf. eauto.
    - inv STEP. econs; ss.
      + apply rmap_add_wf; tac.
      + econs; tac; eauto using get_msg_wf, expr_wf.
        * i. rewrite fun_add_spec. condtac; tac.
          eapply get_msg_wf. eauto.
        * i. revert H. rewrite fun_add_spec. condtac; tac.
          i. inv H. s. splits; tac; eauto using get_msg_wf, expr_wf.
        * destruct ex0; ss.
        * i. revert IN. rewrite Promises.unset_o. condtac; ss. eauto.
    - inv STEP. econs; ss. apply rmap_add_wf; tac.
    - inv STEP. econs; ss. econs; tac.
    - inv STEP. econs; ss. econs; tac.
    - inv STEP. econs; ss. econs; tac.
    - inv STEP. econs; ss. econs; tac.
    - inv LC. econs; ss. econs; tac. eauto using expr_wf.
    - inv LC. econs; ss. econs; tac.
  Qed.

  Lemma rmap_append_wf
        mem msg rmap
        (WF: rmap_wf mem rmap):
    rmap_wf (mem ++ [msg]) rmap.
  Proof.
    inv WF. econs. i. rewrite RMAP. rewrite List.app_length. lia.
  Qed.

  Lemma promise_step_wf tid eu1 eu2
        (STEP: promise_step tid eu1 eu2)
        (WF: wf eu1):
    wf eu2.
  Proof.
    destruct eu1 as [state1 local1 mem1].
    destruct eu2 as [state2 local2 mem2].
    inv WF. inv STEP. ss. subst.
    inv LOCAL. inv LOCAL0. inv MEM2. econs; ss.
    - apply rmap_append_wf. ss.
    - econs.
      all: rewrite List.app_length; s; try lia.
      + i. rewrite COH. lia.
      + i. exploit FWDBANK; eauto. i. des. lia.
      + i. rewrite EXBANK; ss. lia.
      + i. revert IN. rewrite Promises.set_o. condtac.
        * inversion e. i. inv IN. lia.
        * i. exploit PROMISES; eauto. lia.
  Qed.

  Lemma step_wf tid eu1 eu2
        (STEP: step tid eu1 eu2)
        (WF: wf eu1):
    wf eu2.
  Proof.
    inv STEP; eauto using state_step_wf, promise_step_wf.
  Qed.
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

  Lemma step0_consistent
        eustep m1 m2
        (STEP: rtc (step0 eustep) m1 m2)
        (CONSISTENT: consistent eustep m2):
    consistent eustep m1.
  Proof. inv CONSISTENT. econs; [|by eauto]. etrans; eauto. Qed.

  Lemma rtc_step0_step eustep m1 m2
        (STEP: rtc (step0 eustep) m1 m2)
        (CONSISTENT: consistent eustep m2):
    rtc (step eustep) m1 m2.
  Proof.
    revert CONSISTENT. induction STEP; [refl|]. i. econs.
    - econs; eauto. eapply step0_consistent; eauto.
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

  Inductive wf (m:t): Prop :=
  | wf_intro
      (WF: forall tid st lc
             (FIND: IdMap.find tid m.(tpool) = Some (st, lc)),
          ExecUnit.wf (ExecUnit.mk st lc m.(mem)))
  .

  Lemma init_wf p:
    wf (init p).
  Proof.
    econs. i. ss.
    rewrite IdMap.map_spec in FIND. destruct (IdMap.find tid p); inv FIND.
    econs; ss.
    - econs. i. unfold RMap.find, RMap.init. rewrite IdMap.gempty. ss.
    - apply Local.init_wf.
  Qed.

  Lemma init_consistent eustep p:
    consistent eustep (init p).
  Proof.
    econs; eauto. econs. s. i.
    revert FIND. rewrite IdMap.map_spec. destruct (IdMap.find tid p); ss. i. inv FIND.
    s. ii. apply Promises.lookup_empty.
  Qed.

  Lemma step0_state_step_wf
        m1 m2
        (STEP: step0 ExecUnit.state_step m1 m2)
        (WF: wf m1):
    wf m2.
  Proof.
    destruct m1 as [tpool1 mem1].
    destruct m2 as [tpool2 mem2].
    inv STEP. inv STEP0. inv WF. econs. ss. subst.
    i. revert FIND0. rewrite IdMap.add_spec. condtac.
    - inversion e0. i. inv FIND0.
      eapply ExecUnit.state_step_wf; eauto. econs; eauto.
    - i. exploit WF0; eauto.
  Qed.

  Lemma step0_promise_step_wf
        m1 m2
        (STEP: step0 ExecUnit.promise_step m1 m2)
        (WF: wf m1):
    wf m2.
  Proof.
    destruct m1 as [tpool1 mem1].
    destruct m2 as [tpool2 mem2].
    inv STEP. inv STEP0. inv LOCAL. inv MEM2. inv WF. econs. ss. subst.
    i. revert FIND0. rewrite IdMap.add_spec. condtac.
    - inversion e. i. inv FIND0.
      eapply ExecUnit.promise_step_wf; eauto. econs; eauto. econs; eauto.
      + econs; eauto.
      + refl.
    - i. exploit WF0; eauto. i. inv x. ss. econs; ss.
      + apply ExecUnit.rmap_append_wf. ss.
      + inv LOCAL. econs.
        all: rewrite List.app_length; s; try lia.
        * i. rewrite COH. lia.
        * i. exploit FWDBANK; eauto. i. des. lia.
        * i. rewrite EXBANK; ss. lia.
        * i. exploit PROMISES; eauto. lia.
  Qed.

  Lemma step0_step_wf
        m1 m2
        (STEP: step0 ExecUnit.step m1 m2)
        (WF: wf m1):
    wf m2.
  Proof.
    inv STEP. inv STEP0.
    - eapply step0_state_step_wf; eauto.
    - eapply step0_promise_step_wf; eauto.
  Qed.

  Lemma pf_init_wf p m
        (INIT: pf_init p m):
    wf m.
  Proof.
    inv INIT. clear CONSISTENT.
    generalize (init_wf p). induction STEP; ss.
    i. apply IHSTEP. eapply step0_promise_step_wf; eauto.
  Qed.

  Lemma step0_mon
        (eustep1 eustep2: _ -> _ -> _ -> Prop)
        (EUSTEP: forall tid m1 m2, eustep1 tid m1 m2 -> eustep2 tid m1 m2):
    forall m1 m2, step0 eustep1 m1 m2 -> step0 eustep2 m1 m2.
  Proof.
    i. inv H. econs; eauto.
  Qed.

  Lemma rtc_step0_mon
        (eustep1 eustep2: _ -> _ -> _ -> Prop)
        (EUSTEP: forall tid m1 m2, eustep1 tid m1 m2 -> eustep2 tid m1 m2):
    forall m1 m2, rtc (step0 eustep1) m1 m2 -> rtc (step0 eustep2) m1 m2.
  Proof.
    i. induction H; eauto. econs; eauto. eapply step0_mon; eauto.
  Qed.

  Lemma rtc_step_consistent
        eustep m1 m2
        (STEP: rtc (Machine.step eustep) m1 m2)
        (CONSISTENT: Machine.consistent eustep m1):
    Machine.consistent eustep m2.
  Proof.
    revert CONSISTENT. induction STEP; ss.
    i. apply IHSTEP. apply H.
  Qed.
End Machine.

Lemma reorder_state_step_promise_step
      m1 m2 m3
      (WF: Machine.wf m1)
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
        { econs 2; eauto. inv STEP. econs; eauto.
          - ii. eapply LATEST; eauto.
            destruct (lt_dec ts0 (length mem1)).
            { rewrite List.nth_error_app1 in MSG0; ss. }
            contradict n.
            eapply View.lt_le_trans; [apply TS2|].
            inv WF. exploit WF0; try exact FIND; eauto. i. inv x. inv LOCAL. ss.
            repeat apply join_spec; ExecUnit.tac.
            inv STATE. apply ExecUnit.expr_wf. ss.
          - apply Memory.read_mon. ss.
        }
        { econs 3; eauto. inv STEP. econs; eauto.
          - i. exploit EX; eauto. i. des. esplits; eauto.
            exploit ExecUnit.get_msg_wf; eauto. i.
            ii. des. rewrite List.nth_error_app1 in MSG0; [|lia].
            eapply LATEST; eauto.
            rewrite <- READ. unfold Memory.read. destruct tsx; ss.
            rewrite nth_error_app1; ss. lia.
          - apply Memory.get_msg_mon. ss.
        }
        { econs 4; eauto. }
        { econs 5; eauto. }
        { econs 6; eauto. }
        { econs 7; eauto. }
        { econs 8; eauto. }
      * apply IdMap.add_add_diff. ss.
Admitted.

Lemma reorder_state_step_rtc_promise_step
      m1 m2 m3
      (WF: Machine.wf m1)
      (STEP1: Machine.step0 ExecUnit.state_step m1 m2)
      (STEP2: rtc (Machine.step0 ExecUnit.promise_step) m2 m3):
  exists m2',
    <<STEP: rtc (Machine.step0 ExecUnit.promise_step) m1 m2'>> /\
    <<STEP: Machine.step0 ExecUnit.state_step m2' m3>>.
Proof.
  revert m1 WF STEP1. induction STEP2; eauto.
  i. exploit reorder_state_step_promise_step; eauto. i. des.
  exploit Machine.step0_promise_step_wf; eauto. i.
  exploit IHSTEP2; eauto. i. des.
  esplits; cycle 1; eauto.
Qed.

Lemma split_rtc_step0
      m1 m3
      (WF: Machine.wf m1)
      (STEP: rtc (Machine.step0 ExecUnit.step) m1 m3):
  exists m2,
    <<STEP: rtc (Machine.step0 ExecUnit.promise_step) m1 m2>> /\
    <<STEP: rtc (Machine.step0 ExecUnit.state_step) m2 m3>>.
Proof.
  revert WF. induction STEP; eauto. i.
  exploit Machine.step0_step_wf; eauto. i.
  exploit IHSTEP; eauto. i. des.
  inv H. inv STEP2.
  - exploit reorder_state_step_rtc_promise_step; try exact WF; eauto. i. des.
    esplits; eauto.
  - esplits; cycle 1; eauto.
Qed.

Theorem init_step_pf_init_step
        p m
        (STEP: rtc (Machine.step ExecUnit.step) (Machine.init p) m)
        (NOPROMISE: Machine.no_promise m):
  exists m',
    <<INIT: Machine.pf_init p m'>> /\
    <<STEP: rtc (Machine.step ExecUnit.state_step) m' m>>.
Proof.
  generalize (Machine.init_wf p). intro WF.
  generalize (Machine.init_consistent ExecUnit.step p). intro CONSISTENT.
  exploit Machine.rtc_step_consistent; eauto. i.
  exploit rtc_mon.
  { instantiate (1 := Machine.step0 ExecUnit.step).
    instantiate (1 := Machine.step ExecUnit.step).
    i. inv H. ss.
  }
  { eauto. }
  i. exploit split_rtc_step0; eauto. i. des.
  esplits.
  - econs; eauto.
  - apply Machine.rtc_step0_step; ss. econs; eauto.
Qed.

Theorem pf_init_step_init_step
        p m1 m2
        (INIT: Machine.pf_init p m1)
        (STEP: rtc (Machine.step ExecUnit.state_step) m1 m2)
        (NOPROMISE: Machine.no_promise m2):
  rtc (Machine.step ExecUnit.step) (Machine.init p) m2.
Proof.
  inv INIT.
  exploit Machine.rtc_step_consistent; try exact STEP; eauto. i.
  apply Machine.rtc_step0_step; cycle 1.
  { econs; eauto. }
  etrans.
  - eapply rtc_mon; cycle 1; eauto.
    i. eapply Machine.step0_mon; cycle 1; eauto.
    econs 2; eauto.
  - eapply rtc_mon; cycle 1; eauto.
    i. inv H. exploit Machine.step0_mon; cycle 1; eauto.
    econs 1; eauto.
Qed.
