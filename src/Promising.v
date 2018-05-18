Require Import sflib.
Require Import Relations.
Require Import EquivDec.

Require Import Order.
Require Import Time.
Require Import Lang.
Require Import Memory.

Set Implicit Arguments.


Module ExecUnit.
  Inductive t := mk {
    state: State.t (A:=View.t);
    local: Local.t;
    mem: Memory.t;
  }.
  Hint Constructors t.

  Inductive step (tid:Id.t) (eu1 eu2:t): Prop :=
  | step_state
      e
      (STATE: State.step e eu1.(state) eu2.(state))
      (LOCAL: Local.step e tid eu1.(local) eu1.(mem) eu2.(local) eu2.(mem))
  | step_promise
      loc val
      (STATE: eu1.(state) = eu2.(state))
      (LOCAL: Local.promise loc val tid eu1.(local) eu1.(mem) eu2.(local) eu2.(mem))
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
           State.is_terminal st /\ Promises.is_empty lc.(Local.promises))
  .
  Hint Constructors is_terminal.

  Inductive step0 (m1 m2:t): Prop :=
  | step0_intro
      tid st1 lc1 st2 lc2
      (FIND: IdMap.find tid m1.(tpool) = Some (st1, lc1))
      (STEP: ExecUnit.step tid (ExecUnit.mk st1 lc1 m1.(mem)) (ExecUnit.mk st2 lc2 m2.(mem)))
      (ADD: m2.(tpool) = IdMap.add tid (st2, lc2) m1.(tpool))
  .
  Hint Constructors step0.

  Inductive no_promise (m:t): Prop :=
  | no_promise_intro
      (PROMISES:
         forall tid st lc
           (FIND: IdMap.find tid m.(tpool) = Some (st, lc)),
           Promises.is_empty lc.(Local.promises))
  .
  Hint Constructors no_promise.

  (* The "global" consistency condition: in certification, machine may take any thread's steps. *)
  Inductive consistent (m:t): Prop :=
  | consistent_intro
      m'
      (STEP: rtc step0 m m')
      (NOPROMISE: no_promise m')
  .
  Hint Constructors consistent.

  Inductive step (m1 m2:t): Prop :=
  | step_intro
      (STEP: step0 m1 m2)
      (CONSISTENT: consistent m2)
  .
  Hint Constructors step.

  Lemma rtc_step0_step m1 m2
        (STEP: rtc step0 m1 m2)
        (NOPROMISE: no_promise m2):
    rtc step m1 m2.
  Proof.
    induction STEP; [refl|]. econs; eauto.
  Qed.
End Machine.
