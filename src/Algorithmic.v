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


Module Lock.
  Inductive t := mk {
    loc: Loc.t;
    counter: nat;
    guarantee: Loc.t -> Prop;
  }.
  Hint Constructors t.
End Lock.

Module Taint.
  Inductive elt :=
  | R (id:nat) (tr:Time.t)
  | W (id:nat) (tr:Time.t) (lock:Lock.t)
  .
  Hint Constructors elt.

  Definition t := elt -> Prop.

  Inductive is_locked (taint:t) (lock:Lock.t): Prop :=
  | is_locked_intro
      id tr
      (R: taint (R id tr))
      (W: taint (W id tr lock))
  .
End Taint.

Module AExecUnit.
  Inductive aux_t := mk_aux {
    ex_counter: nat;
    st_counter: Loc.t -> nat;
    guarantee: Loc.t -> Prop;
    locks: Lock.t -> Prop;
  }.
  Hint Constructors aux_t.

  Inductive t := mk {
    eu: ExecUnit.t (A:=Taint.t);
    aux: aux_t;
  }.
  Hint Constructors t.
  Coercion eu: t >-> ExecUnit.t.

  Definition taint_read_event (c:nat) (lc:Local.t (A:=Taint.t)) (e:Event.t (A:=View.t (A:=Taint.t))): Event.t (A:=View.t (A:=Taint.t)) :=
    match e, lc.(Local.exbank) with
    | Event.read true ord vloc res, Some tsr =>
      Event.read true ord vloc
                 (ValA.mk _ res.(ValA.val) (View.mk res.(ValA.annot).(View.ts) (join (eq (Taint.R c tsr)) res.(ValA.annot).(View.annot))))
    | _, _ => e
    end.

  Definition state_step_aux (e:Event.t (A:=View.t (A:=Taint.t))) (aux:aux_t): aux_t :=
    match e with
    | Event.read true _ _ _ =>
      mk_aux
        (S aux.(ex_counter))
        aux.(st_counter)
        aux.(guarantee)
        aux.(locks)
    | Event.write _ _ vloc _ res =>
      mk_aux
        aux.(ex_counter)
        (fun_add vloc.(ValA.val) (S (aux.(st_counter) vloc.(ValA.val))) aux.(st_counter))
        (join aux.(guarantee) (eq vloc.(ValA.val)))
        (join aux.(locks) (Taint.is_locked res.(ValA.annot).(View.annot)))
    | _ =>
      aux
    end.

  Inductive state_step (tid:Id.t) (aeu1 aeu2:t): Prop :=
  | state_step_intro
      e1 e2
      (EVENT: e2 = taint_read_event aeu2.(aux).(ex_counter) aeu2.(eu).(ExecUnit.local) e1)
      (STATE: State.step e2 aeu1.(ExecUnit.state) aeu2.(ExecUnit.state))
      (LOCAL: Local.step e1 tid aeu1.(ExecUnit.mem) aeu1.(ExecUnit.local) aeu2.(eu).(ExecUnit.local))
      (MEM: aeu2.(ExecUnit.mem) = aeu1.(ExecUnit.mem))
      (AUX: aeu2.(aux) = state_step_aux e1 aeu1.(aux))
  .
  Hint Constructors state_step.

  Definition taint_write (ex:bool) (loc:Loc.t) (tsr:Time.t) (aux:aux_t): Taint.elt :=
    Taint.W aux.(ex_counter) tsr (Lock.mk loc (aux.(st_counter) loc) (ifc ex aux.(guarantee))).

  Definition taint_write_res (lc: Local.t (A:=Taint.t)) (aux:aux_t) (ex:bool) (ord:OrdW.t) (loc:Loc.t) (res:ValA.t (A:=View.t (A:=Taint.t))): ValA.t (A:=View.t (A:=Taint.t)) :=
    match ex, lc.(Local.exbank) with
    | true, Some tsr =>
      ValA.mk _ res.(ValA.val) (View.mk res.(ValA.annot).(View.ts) (join (eq (taint_write ex loc tsr aux)) res.(ValA.annot).(View.annot)))
    | _, _ => res
    end.

  Definition taint_write_lc (tsr:option Time.t) (lc: Local.t (A:=Taint.t)) (aux:aux_t) (ex:bool) (ord:OrdW.t) (loc:Loc.t): Local.t (A:=Taint.t) :=
    match ex, tsr, lc.(Local.fwdbank) loc with
    | true, Some tsr, Some fwd =>
      Local.mk
        lc.(Local.coh)
        lc.(Local.vrp)
        lc.(Local.vwp)
        lc.(Local.vrm)
        lc.(Local.vwm)
        lc.(Local.vcap)
        lc.(Local.vrel)
        (fun_add
           loc
           (Some (FwdItem.mk fwd.(FwdItem.ts)
                             (View.mk fwd.(FwdItem.view).(View.ts)
                                      (join (eq (taint_write ex loc tsr aux)) fwd.(FwdItem.view).(View.annot)))
                             fwd.(FwdItem.ex)))
           lc.(Local.fwdbank))
        lc.(Local.exbank)
        lc.(Local.promises)
    | _, _, _ => lc
    end.

  Definition write_step_aux (loc:Loc.t) (aux:aux_t): aux_t :=
    mk_aux
      aux.(ex_counter)
      (fun_add loc (S (aux.(st_counter) loc)) aux.(st_counter))
      (join aux.(guarantee) (eq loc))
      aux.(locks).

  Inductive write_step (tid:Id.t) (aeu1 aeu2:t): Prop :=
  | write_step_intro
      ex ord vloc vval res1 res2 lc1 lc2
      (RES: res2 = taint_write_res lc1 aeu1.(aux) ex ord vloc.(ValA.val) res1)
      (STATE: State.step (Event.write ex ord vloc vval res2) aeu1.(ExecUnit.state) aeu2.(ExecUnit.state))
      (LOCAL1: Local.promise vloc.(ValA.val) vval.(ValA.val) tid aeu1.(ExecUnit.local) aeu1.(ExecUnit.mem) lc1 aeu2.(ExecUnit.mem))
      (LOCAL2: Local.fulfill ex ord vloc vval res1 tid lc1 aeu2.(ExecUnit.mem) lc2)
      (LOCAL3: aeu2.(ExecUnit.local) = taint_write_lc lc1.(Local.exbank) lc2 aeu2.(aux) ex ord vloc.(ValA.val))
      (AUX: aeu2.(aux) = write_step_aux vloc.(ValA.val) aeu1.(aux))
  .
  Hint Constructors write_step.

  Inductive step (tid:Id.t) (aeu1 aeu2:t): Prop :=
  | step_state (STEP: state_step tid aeu1 aeu2)
  | step_write (STEP: write_step tid aeu1 aeu2)
  .
  Hint Constructors step.

  Definition init_view (v:View.t (A:=unit)): View.t (A:=Taint.t) :=
    View.mk v.(View.ts) bot.

  Definition init_lc (lc:Local.t (A:=unit)): Local.t (A:=Taint.t) :=
    Local.mk
      lc.(Local.coh)
      (init_view lc.(Local.vrp))
      (init_view lc.(Local.vwp))
      (init_view lc.(Local.vrm))
      (init_view lc.(Local.vwm))
      (View.mk lc.(Local.vcap).(View.ts) match lc.(Local.exbank) with Some tsr => eq (Taint.R 0 tsr) | None => bot end)
      (init_view lc.(Local.vrel))
      (fun loc =>
         option_map
           (fun fwd => FwdItem.mk fwd.(FwdItem.ts) (init_view fwd.(FwdItem.view)) fwd.(FwdItem.ex))
           (lc.(Local.fwdbank) loc))
      lc.(Local.exbank)
      lc.(Local.promises).

  Definition init_aux: aux_t := mk_aux 0 (fun _ => 0) bot bot.

  Definition init_rmap (rmap:RMap.t (A:=View.t (A:=unit))): RMap.t (A:=View.t (A:=Taint.t)) :=
    IdMap.map (fun vala => ValA.mk _ vala.(ValA.val) (init_view vala.(ValA.annot))) rmap.

  Definition init_st (st:State.t (A:=View.t (A:=unit))): State.t (A:=View.t (A:=Taint.t)) :=
    State.mk st.(State.stmts) (init_rmap st.(State.rmap)).

  Definition init (eu:ExecUnit.t (A:=unit)): t :=
    mk
      (ExecUnit.mk (init_st eu.(ExecUnit.state)) (init_lc eu.(ExecUnit.local)) eu.(ExecUnit.mem))
      init_aux.
End AExecUnit.
Coercion AExecUnit.eu: AExecUnit.t >-> ExecUnit.t.

Inductive certify (tid:Id.t) (eu:ExecUnit.t (A:=unit)): forall (locks:Lock.t -> Prop), Prop :=
| certify_intro
    aeu
    (STEPS: rtc (AExecUnit.step tid) (AExecUnit.init eu) aeu)
    (NOPROMISE: aeu.(ExecUnit.local).(Local.promises) = bot):
    certify tid eu aeu.(AExecUnit.aux).(AExecUnit.locks)
.
