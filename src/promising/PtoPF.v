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
From sflib Require Import sflib.

Require Import PromisingArch.lib.Basic.
Require Import PromisingArch.lib.Order.
Require Import PromisingArch.lib.Time.
Require Import PromisingArch.lib.Lang.
Require Import PromisingArch.promising.Promising.
Require Import PromisingArch.promising.StateExecFacts.

Set Implicit Arguments.


Lemma reorder_state_step_promise_step
      m1 m2 m3
      (WF: Machine.wf m1)
      (STEP1: Machine.step ExecUnit.state_step m1 m2)
      (STEP2: Machine.step ExecUnit.promise_step m2 m3):
  exists m2',
    <<STEP: Machine.step ExecUnit.promise_step m1 m2'>> /\
    <<STEP: Machine.step ExecUnit.state_step m2' m3>>.
Proof.
  destruct m1 as [tpool1 mem1].
  destruct m2 as [tpool2 mem2].
  destruct m3 as [tpool3 mem3].
  inv STEP1. inv STEP2. ss. subst.
  revert FIND0. rewrite IdMap.add_spec. condtac.
  - (* same thread *)
    inversion e. i. inv FIND0.
    inv STEP. inv STEP0. inv STEP1. inv LOCAL. inv MEM2. ss. subst.
    eexists (Machine.mk _ _). esplits.
    + econs; eauto; ss. econs; ss.
    + econs; ss.
      * rewrite IdMap.add_spec. instantiate (3 := tid). condtac; [|congr]. eauto.
      * econs. econs; eauto; ss.
        instantiate (1 :=
                       Local.mk
                         lc0.(Local.coh)
                         lc0.(Local.vrn)
                         lc0.(Local.vwn)
                         lc0.(Local.vro)
                         lc0.(Local.vwo)
                         lc0.(Local.vcap)
                         lc0.(Local.vrel)
                         lc0.(Local.fwdbank)
                         lc0.(Local.exbank)
                         (Promises.set (S (length mem1)) lc0.(Local.promises))).
        inv LOCAL0.
        { econs 1; eauto. }
        { econs 2; eauto. instantiate (1 := ts). inv STEP. ss.
          exploit ExecUnit.read_wf; try exact MSG. i.
          econs; eauto; ss.
          - ii. eapply COH; eauto.
            rewrite nth_error_app1 in MSG0; ss.
            eapply lt_le_trans; eauto.
            inv WF. exploit WF0; eauto. intro x. inv x. ss. inv LOCAL. ss.
          - ii. eapply LATEST; eauto.
            rewrite nth_error_app1 in MSG0; ss.
            eapply lt_le_trans; eauto.
            inv WF. exploit WF0; eauto. intro x. inv x. ss. inv LOCAL.
            repeat apply join_spec; viewtac.
            inv STATE0. apply ExecUnit.expr_wf. ss.
          - apply Memory.read_mon. ss.
        }
        { econs 3; eauto. instantiate (1 := view_pre). instantiate (1 := ts).
          inv STEP. inv WRITABLE. ss.
          exploit ExecUnit.get_msg_wf; try exact MSG. i.
          econs; eauto; ss.
          - econs; eauto.
            i. exploit EX; eauto. i. des.
            esplits; eauto. ii.
            rewrite nth_error_app1 in MSG0; [|lia].
            eapply EX0; eauto.
          - rewrite <- MSG. unfold Memory.get_msg. destruct ts; ss.
            rewrite nth_error_app1; [|lia]. ss.
          - rewrite Promises.set_o. condtac; ss. inversion e0. subst. ss.
          - f_equal. apply Promises.set_unset.
            ii. subst. lia.
        }
        { econs 4; eauto. inv STEP. econs; eauto. }
        { econs 5; eauto. inv STEP. econs; eauto. }
        { econs 6; eauto. inv STEP. econs; eauto. }
        { econs 7; eauto. inv LC. econs; eauto. }
      * rewrite ? IdMap.add_add. eauto.
  - (* diff thread *)
    inv STEP. inv STEP1. inv STEP0. inv LOCAL0. inv MEM2. ss. subst.
    eexists (Machine.mk _ _). esplits.
    + econs; eauto; ss. econs; ss.
    + econs; ss.
      * rewrite IdMap.add_spec. instantiate (3 := tid). condtac; [|by eauto].
        inversion e0. subst. congr.
      * econs. econs; eauto; ss.
        instantiate (1 := lc2). inv LOCAL.
        { econs 1; eauto. }
        { econs 2; eauto. inv STEP. econs; eauto.
          - ii. eapply COH; eauto.
            destruct (lt_dec ts0 (length mem1)).
            { rewrite nth_error_app1 in MSG0; ss. }
            contradict n.
            eapply lt_le_trans; [apply TS2|].
            inv WF. exploit WF0; try exact FIND; eauto. intro x. inv x. inv LOCAL. ss.
          - ii. eapply LATEST; eauto.
            destruct (lt_dec ts0 (length mem1)).
            { rewrite nth_error_app1 in MSG0; ss. }
            contradict n.
            eapply Time.lt_le_trans; [apply TS2|].
            inv WF. exploit WF0; try exact FIND; eauto. intro x. inv x. inv LOCAL. ss.
            repeat apply join_spec; viewtac.
            inv STATE. apply ExecUnit.expr_wf. ss.
          - apply Memory.read_mon. ss.
        }
        { econs 3; eauto. inv STEP. inv WRITABLE. econs; eauto.
          - econs; ss.
            i. exploit EX; eauto. i. des. esplits; eauto.
            exploit ExecUnit.get_msg_wf; eauto. i.
            ii. des. rewrite nth_error_app1 in MSG0; [|lia].
            eapply EX0; eauto.
          - apply Memory.get_msg_mon. ss.
        }
        { econs 4; eauto. }
        { econs 5; eauto. }
        { econs 6; eauto. }
        { econs 7; eauto. }
      * apply IdMap.add_add_diff. ss.
Qed.

Lemma reorder_state_step_rtc_promise_step
      m1 m2 m3
      (WF: Machine.wf m1)
      (STEP1: Machine.step ExecUnit.state_step m1 m2)
      (STEP2: rtc (Machine.step ExecUnit.promise_step) m2 m3):
  exists m2',
    <<STEP: rtc (Machine.step ExecUnit.promise_step) m1 m2'>> /\
    <<STEP: Machine.step ExecUnit.state_step m2' m3>>.
Proof.
  revert m1 WF STEP1. induction STEP2; eauto.
  i. exploit reorder_state_step_promise_step; eauto. i. des.
  exploit Machine.step_promise_step_wf; eauto. i.
  exploit IHSTEP2; eauto. i. des.
  esplits; cycle 1; eauto.
Qed.

Lemma split_rtc_step
      m1 m3
      (WF: Machine.wf m1)
      (STEP: rtc (Machine.step ExecUnit.step) m1 m3):
  exists m2,
    <<STEP: rtc (Machine.step ExecUnit.promise_step) m1 m2>> /\
    <<STEP: rtc (Machine.step ExecUnit.state_step) m2 m3>>.
Proof.
  revert WF. induction STEP; eauto. i.
  exploit Machine.step_step_wf; eauto. i.
  exploit IHSTEP; eauto. i. des.
  inv H. inv STEP2.
  - exploit reorder_state_step_rtc_promise_step; try exact WF; eauto. i. des.
    esplits; eauto.
  - esplits; cycle 1; eauto.
Qed.

Theorem promising_to_promising_pf
        p m
        (EXEC: Machine.exec p m):
  Machine.pf_exec p m.
Proof.
  inv EXEC. generalize (Machine.init_wf p). intro WF.
  exploit split_rtc_step; eauto. i. des.
  exploit Machine.rtc_step_promise_step_wf; eauto. i.
  exploit rtc_state_step_state_exec; eauto.
Qed.
