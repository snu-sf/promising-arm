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

Require Import PromisingArch.lib.Basic.
Require Import PromisingArch.lib.Order.
Require Import PromisingArch.lib.Time.
Require Import PromisingArch.lib.Lang.
Require Import PromisingArch.promising.Promising.

Set Implicit Arguments.


Lemma rtc_state_step_state_exec
      m1 m2
      (WF: Machine.wf m1)
      (STEP: rtc (Machine.step ExecUnit.state_step) m1 m2):
  Machine.state_exec m1 m2.
Proof.
  revert WF. induction STEP.
  { econs; ss. ii. destruct (IdMap.find id (Machine.tpool x)); ss. econs. refl. }
  i. exploit Machine.step_state_step_wf; eauto. i.
  exploit IHSTEP; eauto. i. inv x0.
  destruct x as [tpool1 mem1].
  destruct y as [tpool2 mem2].
  inv H. inversion STEP0. inv STEP1. ss. subst. econs; ss.
  ii. specialize (TPOOL id). revert TPOOL.
  rewrite IdMap.add_spec. condtac; ss. i.
  inversion e0. inv TPOOL. rewrite FIND, <- H2. econs.
  econs; eauto.
Qed.

Lemma state_exec_rtc_state_step
      m1 m2
      (STEP: Machine.state_exec m1 m2):
  exists m2',
    <<EXEC: rtc (Machine.step ExecUnit.state_step) m1 m2'>> /\
    <<EQUIV: Machine.equiv m2 m2'>>.
Proof.
  inv STEP.
  assert (IN: forall tid sl1
                (FIND1: IdMap.find tid m1.(Machine.tpool) = Some sl1),
             exists sl2,
               IdMap.find tid m2.(Machine.tpool) = Some sl2 /\
               rtc (ExecUnit.state_step tid)
                   (ExecUnit.mk (fst sl1) (snd sl1) m1.(Machine.mem))
                   (ExecUnit.mk (fst sl2) (snd sl2) m1.(Machine.mem))).
  { i. specialize (TPOOL tid). rewrite FIND1 in TPOOL. inv TPOOL. esplits; ss. }
  assert (OUT: forall tid
                 (FIND1: IdMap.find tid m1.(Machine.tpool) = None),
             IdMap.find tid m1.(Machine.tpool) = IdMap.find tid m2.(Machine.tpool)).
  { i. specialize (TPOOL tid). rewrite FIND1 in TPOOL. inv TPOOL. ss. }
  assert (P: forall tid sl1
               (FIND1: IdMap.find tid m1.(Machine.tpool) = Some sl1),
             IdMap.find tid m1.(Machine.tpool) = Some sl1).
  { ss. }
  clear TPOOL.
  setoid_rewrite IdMap.elements_spec in IN at 1.
  setoid_rewrite IdMap.elements_spec in OUT at 1.
  setoid_rewrite IdMap.elements_spec in P at 1.
  generalize (IdMap.elements_3w m1.(Machine.tpool)). intro NODUP. revert NODUP.
  revert IN OUT P. generalize (IdMap.elements (m1.(Machine.tpool))). intro ps.
  revert m1 MEM. induction ps; ss.
  { i. esplits; eauto. econs; ss. ii. rewrite OUT; ss. }

  i. destruct a. inv NODUP.
  exploit (IN k).
  { destruct (equiv_dec k k); ss. congr. }
  exploit (P k).
  { destruct (equiv_dec k k); ss. congr. }
  i. des. destruct p. ss.

  cut (exists m2', rtc (Machine.step ExecUnit.state_step)
                 (Machine.mk (IdMap.add k (fst sl2, snd sl2) m1.(Machine.tpool)) m1.(Machine.mem))
                 m2' /\
             Machine.equiv m2 m2').
  { i. des. esplits; [|by eauto]. etrans; [|by eauto].
    eapply Machine.rtc_eu_step_step; [eauto|refl|eauto].
  }
  assert (TID: forall tid sl (FIND: SetoidList.findA (fun id' : IdMap.key => if equiv_dec tid id' then true else false) ps = Some sl), tid <> k).
  { ii. subst. apply H1. revert FIND. clear. induction ps; ss.
    destruct a. destruct (equiv_dec k k0); ss.
    - inv e. i. inv FIND. left. ss.
    - i. right. apply IHps. ss.
  }
  eapply IHps; ss.
  - i. eapply IN. destruct (equiv_dec tid k); ss.
    inv e. exfalso. eapply TID; eauto.
  - i. rewrite IdMap.add_spec. condtac.
    + inversion e. subst. rewrite x1. destruct sl2. ss.
    + eapply OUT. destruct (equiv_dec tid k); ss.
  - i. rewrite IdMap.add_spec. condtac.
    + inversion e. subst. exfalso. eapply TID; eauto.
    + eapply P. destruct (equiv_dec tid k); ss.
Qed.
