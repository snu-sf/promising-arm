Require Import sflib.

Require Import EquivDec.
Require Import Order.
Require Import Lang.
Require Import Memory.

Set Implicit Arguments.


Module Thread.
  Inductive t := mk {
    lang: State.t;
    local: Local.t;
  }.
  Hint Constructors t.

  Inductive step (tid:Id.t) (th1:t) (mem1:Memory.t) (th2:t) (mem2:Memory.t): Prop :=
  | step_intro
      e
      (STATE: State.step e th1.(lang) th2.(lang))
      (LOCAL: Local.step e tid th1.(local) mem1 th2.(local) mem2)
  .
End Thread.

Definition threadPoolT := IdMap.t Thread.t.

Module Machine.
  Inductive t := mk {
    tpool: threadPoolT;
    mem: Memory.t;
  }.
  Hint Constructors t.
End Machine.
