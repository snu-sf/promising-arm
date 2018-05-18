Require Import Relations.
Require Import Permutation.
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
Require Import Memory.
Require Import Promising.
Require Import Axiomatic.

Set Implicit Arguments.


Lemma linearize A
      (l: list A)
      (rel: relation A)
      (ACYCLIC: acyclic rel):
  exists l',
    <<PERM: Permutation l l'>> /\
    <<REL: forall i j x y
             (X: List.nth_error l' i = Some x)
             (X: List.nth_error l' j = Some y)
             (REL: rel x y),
        i < j>>.
Proof.
Admitted.

Inductive sim_label (tid:Id.t): forall (label:Label.t) (msg:Msg.t), Prop :=
| sim_label_intro
    ex ord loc val:
    sim_label tid (Label.write ex ord loc val) (Msg.mk loc val tid)
.
Hint Constructors sim_label.

(* TODO: move *)
Fixpoint filter_map A B (f: A -> option B) (l: list A): list B :=
  match l with
  | [] => []
  | a::l =>
    match f a with
    | None => filter_map f l
    | Some b => b :: filter_map f l
    end
  end.

Definition construct_mem
           (ex:Execution.t)
           (eids:list eidT):
  Memory.t :=
  filter_map
    (fun eid =>
       match Execution.label eid ex with
       | Some (Label.write ex ord loc val) => Some (Msg.mk loc val eid.(fst))
       | _ => None
       end)
    eids.

Inductive sim (ex:Execution.t) (m: Machine.t): Prop :=
| sim_intro
    eids
    (EIDS: Permutation eids (Execution.eids ex))
    (OB: forall i j x y
           (X: List.nth_error eids i = Some x)
           (X: List.nth_error eids j = Some y)
           (OB: ex.(Execution.ob) x y),
        i < j)
    (MEM: m.(Machine.mem) = construct_mem ex eids)
.
Hint Constructors sim.

Lemma promise_mem
      p mem
      (MEM: forall msg (MSG: List.In msg mem), IdMap.find msg.(Msg.tid) p <> None):
  exists m,
    <<STEP: rtc Machine.step0 (Machine.init p) m>> /\
    <<TPOOL: m.(Machine.tpool) = (Machine.init p).(Machine.tpool)>> /\ (* TODO: Local.promises.. *)
    <<MEM: m.(Machine.mem) = mem>>.
Proof.
  revert MEM. induction mem using List.rev_ind; i.
  { esplits; eauto. }
  exploit IHmem; eauto.
  { i. apply MEM. apply List.in_app_iff. intuition. }
  i. des. subst. destruct x.
  hexploit MEM.
  { apply List.in_app_iff. right. left. eauto. }
  match goal with
  | [|- context[?f]] => destruct f eqn:FIND
  end; ss.
  intro X. clear X.
  eexists (Machine.mk _ _). esplits.
  - etrans; [eauto|]. econs 2; [|refl].
    econs.
    + rewrite TPOOL, IdMap.map_spec, FIND. ss.
    + econs 2; ss. econs; eauto. ss.
    + ss.
  - admit. (* Local.promises is updated *)
  - ss.
Admitted.

Lemma axiomatic_to_promising
      p ex
      (AXIOMATIC: is_valid p ex):
  exists m,
    <<STEP: rtc Machine.step (Machine.init p) m>> /\
    <<SIM: sim ex m>>.
Proof.
  (* Linearize events and construct memory. *)
  exploit (linearize (Execution.eids ex)).
  { inv AXIOMATIC. apply EXTERNAL. }
  i. des. rename l' into eids.
  remember (construct_mem ex eids) as mem eqn:MEM.

  (* Construct promise steps. *)
  exploit (promise_mem p mem); eauto.
  { i. subst. admit. }
  i. des.

  (* TODO: execute each thread. *)
  admit.
Admitted.
