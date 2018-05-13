Require Import List.
Require Import Bool.
Require Import NArith.
Require Import PArith.
Require Import FMapPositive.
Require Import FSetPositive.
Require Import EquivDec.
Require Import sflib.

Require Import Order.
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

  Definition read (ts:Time.t) (mem:t): option Msg.t :=
    List.nth_error mem ts.

  Definition write (ts:Time.t) (msg:Msg.t) (mem:t): option t :=
    if read ts mem == Some msg
    then Some mem
    else
      if length mem == ts
      then Some (mem ++ [msg])
      else None.

  Definition latest (mem:t) (loc:Loc.t) (view:View.t): Time.t := Order.bot. (* TODO *)
End Memory.

Module FwdItem.
  Inductive t := mk {
    ts: Time.t;
    view: View.t;
    ex: bool;
  }.
  Hint Constructors t.

  Definition read_view (fwd:t) (tsx:Time.t) (ord:ordT): View.t :=
    if andb (fwd.(ts) == tsx) (orb (negb fwd.(ex)) (ord_le ord pln))
    then fwd.(view)
    else tsx.
End FwdItem.

Definition fwdBankT := Loc.t -> option FwdItem.t.

Definition exBankT := option Time.t.

Definition cohT := Loc.t -> Time.t.

Definition promisesT := IdSet.t.

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
    promises: promisesT;
  }.
  Hint Constructors t.

            (* mk *)
            (*   lc1.(coh) *)
            (*   lc1.(vrp) *)
            (*   lc1.(vwp) *)
            (*   lc1.(vrm) *)
            (*   lc1.(vwm) *)
            (*   lc1.(vcap) *)
            (*   lc1.(vrel) *)
            (*   lc1.(fwd) *)
            (*   lc1.(ex) *)
            (*   lc1.(promises)) *)

  Inductive read (ex:bool) (ord:ordT) (vloc:ValV.t) (res: ValV.t) (lc1:t) (mem1: Memory.t) (lc2:t): Prop :=
  | read_intro
      ts loc val tid view
      view_ext1 view_ext2
      (LOC: loc = vloc.(ValV.val))
      (VIEW: view = vloc.(ValV.view))
      (VIEW_EXT1: view_ext1 = joins [view; lc1.(vrp); (ifc (ord_le ra ord) lc1.(vrel))])
      (COH: le (lc1.(coh) loc) ts)
      (LATEST: le (Memory.latest mem1 loc view_ext1) ts)
      (VIEW_EXT2: view_ext2 = join view_ext1 (match lc1.(fwdbank) loc with
                                              | None => ts
                                              | Some fwd => fwd.(FwdItem.read_view) ts ord
                                              end))
      (MSG: Memory.read ts mem1 = Some (Msg.mk loc val tid))
      (RES: res = ValV.mk val view_ext2)
      (LC2: lc2 =
            mk
              (fun_add loc ts lc1.(coh))
              (join lc1.(vrp) (ifc (ord_le ra ord) view_ext2))
              (join lc1.(vwp) (ifc (ord_le ra ord) view_ext2))
              (join lc1.(vrm) view_ext2)
              lc1.(vwm)
              (join lc1.(vcap) view)
              lc1.(vrel)
              lc1.(fwdbank)
              (if ex then Some ts else lc1.(exbank))
              lc1.(promises))
  .
  Hint Constructors read.

  Inductive write (ex:bool) (ord:ordT) (vloc:ValV.t) (vval:ValV.t) (res: ValV.t) (tid:Id.t) (lc1:t) (mem1: Memory.t) (lc2:t) (mem2: Memory.t): Prop :=
  | write_intro
      ts loc val
      view_loc view_val view_ext
      (LOC: loc = vloc.(ValV.val))
      (VIEW_LOC: view_loc = vloc.(ValV.view))
      (VAL: val = vloc.(ValV.val))
      (VIEW_VAL: view_val = vloc.(ValV.view))
      (VIEW_EXT: view_ext = joins [
                                view_loc; view_val; lc1.(vcap); lc1.(vwp);
                                ifc (ord_le ra ord) lc1.(vrm);
                                ifc (ord_le ra ord) lc1.(vwm)
                             ])
      (COH: le (lc1.(coh) loc) ts)
      (EXT: le (lc1.(coh) loc) ts)
      (EX: ex -> exists tsx, lc1.(exbank) = Some tsx /\ True) (* TODO: non-blocked(M, l tsx, ts) *)
      (RES: res = ValV.mk 0 bot)
      (LC2: lc2 =
            mk
              (fun_add loc ts lc1.(coh))
              lc1.(vrp)
              lc1.(vwp)
              lc1.(vrm)
              (join lc1.(vwm) ts)
              (join lc1.(vcap) view_loc)
              (join lc1.(vrel) (ifc (ord_le ra ord) ts))
              (fun_add loc (Some (FwdItem.mk ts (join view_loc view_val) ex)) lc1.(fwdbank))
              (if ex then None else lc1.(exbank))
              lc1.(promises))
      (MEM2: Memory.write ts (Msg.mk loc val tid) mem1 = Some mem2)
  .
  Hint Constructors write.

  Inductive write_failure (ex:bool) (res: ValV.t) (lc1:t) (lc2:t): Prop :=
  | write_failure_intro
      (EX: ex)
      (RES: res = ValV.mk 1 bot)
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
              lc1.(vrp)
              (join lc1.(vwp) lc1.(vcap))
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

  Inductive ctrl (view:View.t) (lc1 lc2:t): Prop :=
  | ctrl_intro
      (LC2: lc2 = 
            mk
              lc1.(coh)
              lc1.(vrp)
              lc1.(vwp)
              lc1.(vrm)
              lc1.(vwm)
              (join lc1.(vcap) view)
              lc1.(vrel)
              lc1.(fwdbank)
              lc1.(exbank)
              lc1.(promises))
  .
  Hint Constructors ctrl.

  Inductive step (event:Event.t) (tid:Id.t) (lc1:t) (mem1:Memory.t) (lc2:t) (mem2:Memory.t): Prop :=
  | step_internal
      (EVENT: event = Event.internal)
      (LC: lc2 = lc1)
      (MEM: mem2 = mem1)
  | step_read
      ex ord vloc res
      (EVENT: event = Event.read ex ord vloc res)
      (STEP: read ex ord vloc res lc1 mem1 lc2)
      (MEM: mem2 = mem1)
  | step_write
      ex ord vloc vval res
      (EVENT: event = Event.write ex ord vloc vval res)
      (STEP: write ex ord vloc vval res tid lc1 mem1 lc2 mem2)
  | step_write_failure
      ex ord vloc vval res
      (EVENT: event = Event.write ex ord vloc vval res)
      (STEP: write_failure ex res lc1 lc2)
      (MEM: mem2 = mem1)
  | step_isb
      (EVENT: event = Event.barrier Barrier.isb)
      (STEP: isb lc1 lc2)
      (MEM: mem2 = mem1)
  | step_dmbst
      (EVENT: event = Event.barrier Barrier.dmbst)
      (STEP: dmbst lc1 lc2)
      (MEM: mem2 = mem1)
  | step_dmbld
      (EVENT: event = Event.barrier Barrier.dmbld)
      (STEP: dmbld lc1 lc2)
      (MEM: mem2 = mem1)
  | step_dmbsy
      (EVENT: event = Event.barrier Barrier.dmbsy)
      (STEP: dmbsy lc1 lc2)
      (MEM: mem2 = mem1)
  | step_ctrl
      view
      (EVENT: event = Event.ctrl view)
      (STEP: ctrl view lc1 lc2)
      (MEM: mem2 = mem1)
  .
  Hint Constructors step.
End Local.
