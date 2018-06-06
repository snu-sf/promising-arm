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
Require Import Promising.

Set Implicit Arguments.


Module Taint.
  Inductive elt :=
  | R (id:nat) (tr:Time.t)
  | W (id:nat) (tw:Time.t) (guarantee: Loc.t -> Prop)
  .

  Definition t := elt -> Prop.

  Inductive is_lock (ts:Time.t) (taint:t) (tr tw:Time.t) (guarantee:Loc.t -> Prop): Prop :=
  | is_lock_base
      id
      (R: taint (R id tr))
      (W: taint (W id tw guarantee))
      (TR: tr <= ts)
  | is_lock_step
      id tr' guarantee'
      (R: taint (R id tr))
      (W: taint (W id tw guarantee))
      (TR: is_lock ts taint tr' tr guarantee')
  .
End Taint.

Module AExecUnit.
  Inductive t := mk {
    eu: ExecUnit.t (A:=Taint.t);
    counter: nat;
    guarantee: Loc.t -> Prop;
  }.
  Hint Constructors t.
  Coercion eu: t >-> ExecUnit.t.

  Definition taint_load (lc:Local.t (A:=Taint.t)) (c:nat) (e:Event.t (A:=View.t (A:=Taint.t))): nat * Event.t (A:=View.t (A:=Taint.t)) :=
    match e, lc.(Local.exbank) with
    | Event.read true ord vloc res, Some tsr =>
      (S c, Event.read true ord vloc
                       (ValA.mk _ res.(ValA.val) (View.mk res.(ValA.annot).(View.ts) (join (eq (Taint.R (S c) tsr)) res.(ValA.annot).(View.annot)))))
    | _, _ =>
      (c, e)
    end.

  Inductive state_step (tid:Id.t) (aeu1 aeu2:t): Prop :=
  | state_step_intro
      e e' st
      (STATE: State.step e' aeu1.(ExecUnit.state) st)
      (LOCAL: Local.step e tid aeu1.(ExecUnit.mem) aeu1.(ExecUnit.local) aeu2.(eu).(ExecUnit.local))
      (TAINT: taint_load aeu2.(eu).(ExecUnit.local) aeu1.(counter) e = (aeu2.(counter), e'))
      (GUARANTEE: aeu2.(guarantee) = aeu1.(guarantee))
  .

  Inductive taint_store (c:nat) (guarantee:Loc.t -> Prop) (ex:bool) (ord:OrdW.t) (vloc vval res1 res2:ValA.t (A:=View.t (A:=Taint.t))) (lc1 lc2:Local.t (A:=Taint.t)): Prop :=
  | taint_store_nex
      (EX: ~ ex)
      (RES: res2 = res1)
      (LC: lc2 = lc1)
  | taint_store_ex
      loc tsw taint fwd
      (EX: ex)
      (LOC: loc = vloc.(ValA.val))
      (TSW: tsw = lc1.(Local.coh) loc)
      (TAINT: taint = eq (Taint.W c tsw guarantee))
      (FWD: Some fwd = lc1.(Local.fwdbank) loc)
      (RES: res2 = ValA.mk _ res1.(ValA.val) (View.mk res1.(ValA.annot).(View.ts) (join taint res1.(ValA.annot).(View.annot))))
      (LC: lc2 = Local.mk 
                   lc1.(Local.coh)
                   lc1.(Local.vrp)
                   lc1.(Local.vwp)
                   lc1.(Local.vrm)
                   lc1.(Local.vwm)
                   lc1.(Local.vcap)
                   lc1.(Local.vrel)
                   (fun_add
                      loc
                      (Some (FwdItem.mk fwd.(FwdItem.ts)
                                        (View.mk fwd.(FwdItem.view).(View.ts)
                                                 (join taint fwd.(FwdItem.view).(View.annot)))
                                        fwd.(FwdItem.ex)))
                      lc1.(Local.fwdbank))
                   lc1.(Local.exbank)
                   lc1.(Local.promises))
  .

  Inductive write_step (tid:Id.t) (aeu1 aeu2:t): Prop :=
  | write_step_intro
      ex ord vloc vval res1 res2 lc1 lc2
      (STATE: State.step (Event.write ex ord vloc vval res2) aeu1.(ExecUnit.state) aeu2.(ExecUnit.state))
      (LOCAL1: Local.promise vloc.(ValA.val) vval.(ValA.val) tid aeu1.(ExecUnit.local) aeu1.(ExecUnit.mem) lc1 aeu2.(ExecUnit.mem))
      (LOCAL2: Local.fulfill ex ord vloc vval res1 tid lc1 aeu2.(ExecUnit.mem) lc2)
      (TAINT: taint_store aeu1.(counter) aeu1.(guarantee) ex ord vloc vval res1 res2 lc2 aeu2.(ExecUnit.local))
      (COUNTER: aeu2.(counter) = aeu1.(counter))
      (GUARANTEE: aeu2.(guarantee) = join aeu1.(guarantee) (eq vloc.(ValA.val)))
  .

  (* TODO
   * - initialize: [R 0 tr] in vcap if exbank exists?
   * - calculate locks in fulfill step.  `res` contains the necessary taint.  Use `Taint.is_lock`.
   *)
End AExecUnit.
Coercion AExecUnit.eu: AExecUnit.t >-> ExecUnit.t.
