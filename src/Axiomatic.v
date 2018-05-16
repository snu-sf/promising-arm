Require Import NArith.
Require Import PArith.
Require Import ZArith.
Require Import Lia.
Require Import FMapPositive.
Require Import FSetPositive.
Require Import sflib.
Require Import EquivDec.

Require Import Order.
Require Import Time.
Require Import Lang.

Set Implicit Arguments.


Module Event.
  Inductive t :=
  | read (ex:bool) (ord:ordT) (loc:Loc.t) (val:Val.t)
  | write (ex:bool) (ord:ordT) (loc:Loc.t) (val:Val.t) (res:Val.t)
  .

  Definition from_lang A `{_: orderC A} (e:Lang.Event.t (A:=A)): option t :=
    match e with
    | Lang.Event.read ex ord vloc res => Some (read ex ord vloc.(ValA.val) res.(ValA.val))
    | Lang.Event.write ex ord vloc vval res => Some (write ex ord vloc.(ValA.val) vval.(ValA.val) res.(ValA.val))
    | _ => None
    end.
End Event.

Definition depT := nat -> Prop.

Inductive exec_state: forall (st:State.t (A:=depT)) (events:list Event.t), Prop :=
| exec_state_terminal
    st
    (TERMINAL: State.is_terminal st):
    exec_state st nil
| exec_state_step
    st1 st2 e events
    (STEP: State.step e st1 st2)
    (EXEC: exec_state st2 events):
    exec_state st1 (match Event.from_lang e with
                    | None => []
                    | Some e => [e]
                    end ++ events)
.
Hint Constructors exec_state.
