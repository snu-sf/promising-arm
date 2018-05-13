Require Import sflib.
Require Import Relations.
Require Import EquivDec.

Require Import Order.
Require Import Lang.
Require Import Memory.

Set Implicit Arguments.


Module ExecUnit.
  Inductive t := mk {
    lang: State.t;
    local: Local.t;
    mem: Memory.t;
  }.
  Hint Constructors t.

  Inductive step (tid:Id.t) (eu1 eu2:t): Prop :=
  | step_intro
      e
      (STATE: State.step e eu1.(lang) eu2.(lang))
      (LOCAL: Local.step e tid eu1.(local) eu1.(mem) eu2.(local) eu2.(mem))
  .
End ExecUnit.

Module Machine.
  Inductive t := mk {
    tpool: IdMap.t (State.t * Local.t);
    mem: Memory.t;
  }.
  Hint Constructors t.

  Inductive step (th1 th2:t): Prop :=
  | step_intro
      tid st1 lc1 st2 lc2
      (FIND: IdMap.find tid th1.(tpool) = Some (st1, lc1))
      (STEP: ExecUnit.step tid (ExecUnit.mk st1 lc1 th1.(mem)) (ExecUnit.mk st2 lc2 th2.(mem)))
      (ADD: th2.(tpool) = IdMap.add tid (st2, lc2) th1.(tpool))
  .

  (* The consistency condition for the "lazy" semantics. *)
  Definition consistent (th:t): Prop :=
    exists th',
      <<STEP: rtc step th th'>> /\
      <<PROMISES:
        forall tid st lc
          (FIND: IdMap.find tid th'.(tpool) = Some (st, lc)),
          IdSet.is_empty lc.(Local.promises)>>.
End Machine.
