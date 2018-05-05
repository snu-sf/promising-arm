Require Import List.
Require Import NArith.
Require Import PArith.
Require Import FMapPositive.
Require Import FSetPositive.

Require Import sflib.

Require Import Order.
Require Import Lang.
Require Import Machine.

Set Implicit Arguments.

Module Step.
            (* Local.mk *)
            (*   lc1.(Local.coh) *)
            (*   lc1.(Local.vrp) *)
            (*   lc1.(Local.vwp) *)
            (*   lc1.(Local.vrm) *)
            (*   lc1.(Local.vwm) *)
            (*   lc1.(Local.vcap) *)
            (*   lc1.(Local.vrel) *)
            (*   lc1.(Local.fwd) *)
            (*   lc1.(Local.ex) *)
            (*   lc1.(Local.promises)) *)

  Inductive read (ex:bool) (o:ord) (vloc:ValV.t) (lc1:Local.t) (mem1: Memory.t) (result: ValV.t) (lc2:Local.t): Prop :=
  | read_intro
      ts loc val tid view
      view_ext1 view_ext2
      (LOC: loc = vloc.(ValV.val))
      (VIEW: view = vloc.(ValV.view))
      (VIEW_EXT1: view_ext1 = joins [view; lc1.(Local.vrp); (ifc (ord_le ra o) lc1.(Local.vrel))])
      (COH: le (lc1.(Local.coh) loc) ts)
      (LATEST: le (Memory.latest mem1 loc view_ext1) ts)
      (VIEW_EXT2: view_ext2 = join view_ext1 (match lc1.(Local.fwd) loc with
                                              | None => ts
                                              | Some fwd => fwd.(FwdItem.read_view) ts o
                                              end))
      (MSG: Memory.get ts mem1 = Some (Msg.mk loc val tid))
      (RESULT: result = ValV.mk val view_ext2)
      (LC2: lc2 =
            Local.mk
              (fun_add loc ts lc1.(Local.coh))
              (join lc1.(Local.vrp) (ifc (ord_le ra o) view_ext2))
              (join lc1.(Local.vwp) (ifc (ord_le ra o) view_ext2))
              (join lc1.(Local.vrm) view_ext2)
              lc1.(Local.vwm)
              (join lc1.(Local.vcap) view)
              lc1.(Local.vrel)
              lc1.(Local.fwd)
              (if ex then Some ts else lc1.(Local.ex))
              lc1.(Local.promises))
  .
  Hint Constructors read.

  Inductive write (ex:bool) (o:ord) (vloc:ValV.t) (vval:ValV.t) (lc1:Local.t) (tid:Id.t) (mem1: Memory.t) (result: ValV.t) (lc2:Local.t) (mem2: Memory.t): Prop :=
  | write_intro
      ts loc val
      view_loc view_val view_ext
      (LOC: loc = vloc.(ValV.val))
      (VIEW_LOC: view_loc = vloc.(ValV.view))
      (VAL: val = vloc.(ValV.val))
      (VIEW_VAL: view_val = vloc.(ValV.view))
      (VIEW_EXT: view_ext = joins [view_loc; view_val; lc1.(Local.vcap); lc1.(Local.vwp);
                              ifc (ord_le ra o) lc1.(Local.vrm);
                              ifc (ord_le ra o) lc1.(Local.vwm)
                             ])
      (COH: le (lc1.(Local.coh) loc) ts)
      (EXT: le (lc1.(Local.coh) loc) ts)
      (EX: ex -> exists tsx, lc1.(Local.ex) = Some tsx /\ True) (* TODO: non-blocked(M, l tsx, ts) *)
      (RESULT: result = ValV.mk 0 bot)
      (LC2: lc2 =
            Local.mk
              (fun_add loc ts lc1.(Local.coh))
              lc1.(Local.vrp)
              lc1.(Local.vwp)
              lc1.(Local.vrm)
              (join lc1.(Local.vwm) ts)
              (join lc1.(Local.vcap) view_loc)
              (join lc1.(Local.vrel) (ifc (ord_le ra o) ts))
              (fun_add loc (Some (FwdItem.mk ts (join view_loc view_val) ex)) lc1.(Local.fwd))
              (if ex then None else lc1.(Local.ex))
              lc1.(Local.promises))
      (MEM2: True) (* TODO: use (Msg.mk loc val tid) *)
  .

  Inductive write_failure (ex:bool) (lc1:Local.t) (result: ValV.t) (lc2:Local.t): Prop :=
  | write_failure_intro
      (EX: ex)
      (RESULT: result = ValV.mk 1 bot)
      (LC2: lc2 =
            Local.mk
              lc1.(Local.coh)
              lc1.(Local.vrp)
              lc1.(Local.vwp)
              lc1.(Local.vrm)
              lc1.(Local.vwm)
              lc1.(Local.vcap)
              lc1.(Local.vrel)
              lc1.(Local.fwd)
              None
              lc1.(Local.promises))
  .

  Inductive isb (lc1 lc2:Local.t): Prop :=
  | isb_intro
      (LC2: lc2 = 
            Local.mk
              lc1.(Local.coh)
              lc1.(Local.vrp)
              (join lc1.(Local.vwp) lc1.(Local.vcap))
              lc1.(Local.vrm)
              lc1.(Local.vwm)
              lc1.(Local.vcap)
              lc1.(Local.vrel)
              lc1.(Local.fwd)
              lc1.(Local.ex)
              lc1.(Local.promises))
  .

  Inductive dmbst (lc1 lc2:Local.t): Prop :=
  | dmbst_intro
      (LC2: lc2 = 
            Local.mk
              lc1.(Local.coh)
              lc1.(Local.vrp)
              (join lc1.(Local.vwp) lc1.(Local.vwm))
              lc1.(Local.vrm)
              lc1.(Local.vwm)
              lc1.(Local.vcap)
              lc1.(Local.vrel)
              lc1.(Local.fwd)
              lc1.(Local.ex)
              lc1.(Local.promises))
  .

  Inductive dmbld (lc1 lc2:Local.t): Prop :=
  | dmbld_intro
      (LC2: lc2 = 
            Local.mk
              lc1.(Local.coh)
              (join lc1.(Local.vrp) lc1.(Local.vrm))
              (join lc1.(Local.vwp) lc1.(Local.vrm))
              lc1.(Local.vrm)
              lc1.(Local.vwm)
              lc1.(Local.vcap)
              lc1.(Local.vrel)
              lc1.(Local.fwd)
              lc1.(Local.ex)
              lc1.(Local.promises))
  .

  Inductive dmbsy (lc1 lc2:Local.t): Prop :=
  | dmbsy_intro
      (LC2: lc2 = 
            Local.mk
              lc1.(Local.coh)
              (joins [lc1.(Local.vrp); lc1.(Local.vrm); lc1.(Local.vwm)])
              (joins [lc1.(Local.vwp); lc1.(Local.vrm); lc1.(Local.vwm)])
              lc1.(Local.vrm)
              lc1.(Local.vwm)
              lc1.(Local.vcap)
              lc1.(Local.vrel)
              lc1.(Local.fwd)
              lc1.(Local.ex)
              lc1.(Local.promises))
  .
End Step.
