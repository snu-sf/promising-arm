Require Import Relations.
Require Import NArith.
Require Import PArith.
Require Import ZArith.
Require Import Lia.
Require Import FMapPositive.
Require Import FSetPositive.
Require Import EquivDec.
Require Import sflib.
Require Import paco.
Require Import HahnRelationsBasic.

Require Import Order.
Require Import Time.
Require Import Lang.

Set Implicit Arguments.


Inductive labelT :=
| read (ex:bool) (ord:ordT) (loc:Loc.t) (val:Val.t)
| write (ex:bool) (ord:ordT) (loc:Loc.t) (val:Val.t) (res:Val.t)
.

Module ALocal.
  Inductive t := mk {
    labels: list labelT;
    addr: relation nat;
    data: relation nat;
    ctrl: relation nat;
    ctrl_src: nat -> Prop;
  }.
  Hint Constructors t.

  Definition init: t := mk [] bot bot bot bot.

  Definition next_eid (eu:t): nat :=
    List.length eu.(labels).

  Inductive step (event:Event.t (A:=nat -> Prop)) (ctor1:t) (ctor2:t): Prop :=
  | step_internal
      (EVENT: event = Event.internal)
      (CTOR: ctor2 = ctor1)
  | step_read
      ex ord vloc res
      (EVENT: event = Event.read ex ord vloc (ValA.mk _ res (eq (next_eid ctor1))))
      (CTOR: ctor2 =
             mk
               (ctor1.(labels) ++ [read ex ord vloc.(ValA.val) res])
               (ctor1.(addr) ∪ (vloc.(ValA.annot) × (eq (next_eid ctor1))))
               ctor1.(data)
               (ctor1.(ctrl) ∪ (ctor1.(ctrl_src) × (eq (next_eid ctor1))))
               ctor1.(ctrl_src))
  | step_write
      ex ord vloc vval res
      (EVENT: event = Event.write ex ord vloc vval (ValA.mk _ res (eq (next_eid ctor1))))
      (CTOR: ctor2 =
             mk
               (ctor1.(labels) ++ [write ex ord vloc.(ValA.val) vval.(ValA.val) res])
               (ctor1.(addr) ∪ (vloc.(ValA.annot) × (eq (next_eid ctor1))))
               (ctor1.(data) ∪ (vval.(ValA.annot) × (eq (next_eid ctor1))))
               (ctor1.(ctrl) ∪ (ctor1.(ctrl_src) × (eq (next_eid ctor1))))
               ctor1.(ctrl_src))
  | step_barrier
      b
      (EVENT: event = Event.barrier b)
      (CTOR: ctor2 = ctor1)
  | step_ctrl
      src
      (EVENT: event = Event.ctrl src)
      (CTOR: ctor2 =
             mk
               ctor1.(labels)
               ctor1.(addr)
               ctor1.(data)
               ctor1.(ctrl)
               ((ctor1.(ctrl_src)) \1/ (src)))
  .
  Hint Constructors step.

  Inductive exec_unitT := mk_exec_unit {
    state: State.t (A:=nat -> Prop);
    local: ALocal.t;
  }.
  Hint Constructors exec_unitT.

  Inductive exec_unit_step (eu1 eu2:exec_unitT): Prop :=
  | step_exec_unit
      e
      (STATE: State.step e eu1.(state) eu2.(state))
      (LOCAL: ALocal.step e eu1.(local) eu2.(local))
  .
End ALocal.

Definition eid := (Id.t * nat)%type.

Inductive executionT := mk {
  labels: IdMap.t (list labelT);
  po: relation eid;
  addr: relation eid;
  data: relation eid;
  ctrl: relation eid;
  co: relation eid;
  rf: relation eid;
}.

Inductive is_pre_execution (p:program) (ex:executionT): Prop :=
| is_pre_execution_intro
    locals
    (LOCALS: IdMap.for_all
               (fun stmts local =>
                  exists state,
                    <<STEP: rtc ALocal.exec_unit_step
                                (ALocal.mk_exec_unit (State.init stmts) ALocal.init)
                                (ALocal.mk_exec_unit state local)>> /\
                    <<TERMINAL: State.is_terminal state>>)
               p locals)
    (LABELS: ex.(labels) = IdMap.map (fun local => local.(ALocal.labels)) locals)
    (* TODO: po, addr, data, ctrl *)
.

Inductive is_execution (p:program) (ex:executionT): Prop :=
| is_execution_intro
    (PRE: is_pre_execution p ex)
    (* TODO: axioms *)
.
