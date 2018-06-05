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
Require Import Sorted.
Require Import sflib.

Require Import Basic.
Require Import Order.
Require Import Time.
Require Import Lang.
Require Import Promising.

Set Implicit Arguments.


Inductive rgT := {
  rely_loc: Loc.t;
  rely_val: Val.t;
  guarantee: Loc.t -> Prop;
}.

Module RGs.
  Definition t := list rgT.

  Definition consistentT := forall (tid:Id.t) (eu:ExecUnit.t) (rgs:t), Prop.

  Inductive consistent0 (c:consistentT) (tid:Id.t) (eu:ExecUnit.t): forall (rgs:t), Prop :=
  | consistent_nil
      eu'
      (STEP: rtc (ExecUnit.state_step tid) eu eu')
      (PROMISES: eu'.(ExecUnit.local).(Local.promises) = bot):
      consistent0 c tid eu nil
  | consistent_promise
      eu' rg rgs
      (STEP: ExecUnit.promise_step tid eu eu')
      (GUARANTEE: rg.(guarantee) 0) (* TODO *)
      (CONSISTENT: c tid eu' (rg::rgs)):
      consistent0 c tid eu (rg::rgs)
  | consistent_unlock
      eu' rg rgs
      (STEP: ExecUnit.promise_step tid eu eu') (* TODO: rg.(rely) *)
      (CONSISTENT: c tid eu' rgs):
      consistent0 c tid eu (rg::rgs)
  .
  Hint Constructors consistent0.

  Inductive future (rgs:t) (eu1 eu2:ExecUnit.t): Prop :=
  | future_intro
      mem
      (GUARANTEE: forall msg (MSG: In msg mem), Forall (fun rg => rg.(rely_loc) <> msg.(Msg.loc)) rgs)
      (STATE: eu2.(ExecUnit.state) = eu1.(ExecUnit.state))
      (LOCAL: eu2.(ExecUnit.local) = eu1.(ExecUnit.local))
      (MEM: eu2.(ExecUnit.mem) = eu1.(ExecUnit.mem) ++ mem)
  .
  Hint Constructors future.

  Inductive consistent (tid:Id.t) (eu:ExecUnit.t) (rgs:t): Prop :=
  | consistent_intro
      (CONSISTENT:
         forall eu'
           (GUARANTEE: future rgs eu eu'),
           consistent0 consistent tid eu' rgs)
  .
  Hint Constructors consistent.

  Inductive consistent_imm (tid:Id.t) (eu:ExecUnit.t) (rgs:t): Prop :=
  | consistent_imm_intro
      (CONSISTENT: consistent0 consistent_imm tid eu rgs)
  .
  Hint Constructors consistent_imm.

  Inductive consistent_ex (tid:Id.t) (eu:ExecUnit.t) (rgs:t): Prop :=
  | consistent_ex_intro
      eu'
      (GUARANTEE: future rgs eu eu')
      (CONSISTENT: consistent0 consistent_ex tid eu' rgs)
  .
  Hint Constructors consistent_ex.
End RGs.

Module LMachine.
  Inductive t := mk {
    machine: Machine.t;
    rgss: IdMap.t RGs.t;
  }.

  Definition init (p:program): t :=
    mk
      (Machine.init p)
      (IdMap.map (fun _ => []) p).

  Inductive consistent (m:t): Prop :=
  | consistent_intro
      rgs
      (RGSS: IdMap.Forall2
               (fun tid th rgs =>
                  RGs.consistent
                    tid
                    (ExecUnit.mk th.(fst) th.(snd) m.(machine).(Machine.mem))
                    rgs)
               m.(machine).(Machine.tpool) m.(rgss))
      (INTERLEAVING: IdMap.interleaving m.(rgss) rgs)
      (GUARANTEE: StronglySorted (fun rg1 rg2 => ~ rg1.(guarantee) rg2.(rely_loc)) rgs)
  .

  Lemma init_consistent p:
    consistent (init p).
  Proof.
    econs; ss.
    - ii. rewrite ? IdMap.map_spec. destruct (IdMap.find id p); ss.
      econs. s. econs. econs; eauto.
      inv GUARANTEE. rewrite LOCAL. ss.
    - econs 1. ii. revert FIND. rewrite IdMap.map_spec. destruct (IdMap.find id p); ss. congr.
    - econs.
  Qed.
End LMachine.

Lemma local_consistent_global_consistent_nil (* TODO: naming? *)
        m
        (RGSS: IdMap.Forall (fun _ l => l = []) m.(LMachine.rgss))
        (CONSISTENT: LMachine.consistent m):
  Machine.consistent ExecUnit.state_step m.(LMachine.machine).
Proof.
Admitted.

Theorem local_consistent_global_consistent
        m
        (CONSISTENT: LMachine.consistent m):
  Machine.consistent ExecUnit.step m.(LMachine.machine).
Proof.
Admitted.
