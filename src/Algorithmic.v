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
Require Import HahnSets.

Require Import Basic.
Require Import Order.
Require Import Time.
Require Import Lang.
Require Import Promising.
Require Import Certify.
Require Import CertifyFacts.

Set Implicit Arguments.


Module AMachine.
  Inductive t := mk {
    machine: Machine.t;
    tlocks: IdMap.t Lock.t;
  }.
  Hint Constructors t.
  Coercion machine: t >-> Machine.t.

  Definition init (p:program): t :=
    mk
      (Machine.init p)
      (IdMap.map (fun _ => Lock.init) p).

  Inductive consistent (am: IdMap.t (Lock.t * (Loc.t -> nat))): Prop :=
  | consistent_final
      (FINAL: IdMap.Forall (fun _ th => Lock.is_final th.(fst) th.(snd)) am)
  | consistent_step
      (TODO: False)
  .
  Hint Constructors consistent.

  Inductive wf (m:t): Prop :=
  | wf_intro
      (MACHINE: Machine.wf m.(machine))
      (CERTIFY: IdMap.Forall2
                  (fun tid th tlock => certify tid (ExecUnit.mk th.(fst) th.(snd) m.(Machine.mem)) tlock)
                  m.(Machine.tpool) m.(tlocks))
      (CONSISTENT: consistent (IdMap.map (fun tlock => (tlock, bot)) m.(tlocks)))
  .
  Hint Constructors wf.

  Lemma init_wf p:
    wf (init p).
  Proof.
    econs.
    - apply Machine.init_wf.
    - s. ii. rewrite ? IdMap.map_spec. destruct (IdMap.find id p); ss.
      econs. s. apply no_promise_certify_init. ss.
    - econs. s. intros ? ?. rewrite ? IdMap.map_spec.
      destruct (IdMap.find id p); ss. i. inv FIND. ss.
  Qed.

  Inductive step (eustep: forall (tid:Id.t) (eu1 eu2:ExecUnit.t (A:=unit)), Prop) (m1 m2:t): Prop :=
  | step_intro
      tid st1 lc1 st2 lc2 tlock
      (FIND: IdMap.find tid m1.(Machine.tpool) = Some (st1, lc1))
      (STEP: eustep tid (ExecUnit.mk st1 lc1 m1.(Machine.mem)) (ExecUnit.mk st2 lc2 m2.(Machine.mem)))
      (TPOOL: m2.(Machine.tpool) = IdMap.add tid (st2, lc2) m1.(Machine.tpool))
      (TLOCKS: m2.(tlocks) = IdMap.add tid tlock m1.(tlocks))
      (CERTIFY: certify tid (ExecUnit.mk st2 lc2 m2.(Machine.mem)) tlock)
      (INTERFERE: True) (* TODO: doesn't bother other's lock *)
      (CONSISTENT: consistent (IdMap.map (fun tlock => (tlock, bot)) m2.(tlocks)))
  .
  Hint Constructors step.

  Lemma step_state_step_wf
        m1 m2
        (STEP: step ExecUnit.state_step m1 m2)
        (WF: wf m1):
    wf m2.
  Proof.
    inv WF. inv STEP. econs; eauto.
    - eapply Machine.step_state_step_wf; eauto.
    - rewrite TPOOL, TLOCKS. ii. rewrite ? IdMap.add_spec. condtac.
      + inversion e. eauto.
      + inv STEP0. inv STEP. ss. rewrite MEM. eauto.
  Qed.

  Lemma step_promise_step_wf
        m1 m2
        (STEP: step ExecUnit.promise_step m1 m2)
        (WF: wf m1):
    wf m2.
  Proof.
    inv WF. inv STEP. econs; eauto.
    - eapply Machine.step_promise_step_wf; eauto.
    - rewrite TPOOL, TLOCKS. ii. rewrite ? IdMap.add_spec. condtac.
      + inversion e. eauto.
      + admit. (* certify after changing mem; "INTERFERE" is important here. *)
  Admitted.

  Lemma step_step_wf
        m1 m2
        (STEP: step ExecUnit.step m1 m2)
        (WF: wf m1):
    wf m2.
  Proof.
    inv STEP. inv STEP0.
    - eapply step_state_step_wf; eauto.
    - eapply step_promise_step_wf; eauto.
  Qed.

  Lemma step_mon
        (eustep1 eustep2: _ -> _ -> _ -> Prop)
        (EUSTEP: forall tid m1 m2, eustep1 tid m1 m2 -> eustep2 tid m1 m2):
    forall m1 m2, step eustep1 m1 m2 -> step eustep2 m1 m2.
  Proof.
    i. inv H. econs; eauto.
  Qed.

  Lemma rtc_step_mon
        (eustep1 eustep2: _ -> _ -> _ -> Prop)
        (EUSTEP: forall tid m1 m2, eustep1 tid m1 m2 -> eustep2 tid m1 m2):
    forall m1 m2, rtc (step eustep1) m1 m2 -> rtc (step eustep2) m1 m2.
  Proof.
    i. induction H; eauto. econs; eauto. eapply step_mon; eauto.
  Qed.

  Inductive exec (p:program) (m:Machine.t): Prop :=
  | exec_intro
      am
      (STEP: rtc (step ExecUnit.step) (init p) am)
      (MACHINE: m = am.(machine))
      (NOPROMISE: Machine.no_promise m)
  .
  Hint Constructors exec.

  Inductive pf_exec (p:program) (m:Machine.t): Prop :=
  | pf_exec_intro
      am1
      (STEP1: rtc (step ExecUnit.promise_step) (init p) am1)
      (STEP2: Machine.state_exec am1 m)
      (NOPROMISE: Machine.no_promise m)
  .
  Hint Constructors pf_exec.
End AMachine.
Coercion AMachine.machine: AMachine.t >-> Machine.t.
