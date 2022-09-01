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
Require Import HahnSets.

Require Import PromisingArch.lib.Basic.
Require Import PromisingArch.lib.Order.
Require Import PromisingArch.lib.Time.
Require Import PromisingArch.lib.Lang.
Require Import PromisingArch.promising.Promising.
Require Import PromisingArch.lcertify.Certify.
Require Import PromisingArch.lcertify.CertifySim.

Set Implicit Arguments.


Lemma promise_step_certify
      tid eu1 eu2
      (CERTIFY: certify tid eu2)
      (STEP: ExecUnit.promise_step tid eu1 eu2)
      (WF: ExecUnit.wf tid eu1):
  certify tid eu1.
Proof.
  destruct (classic (eu1.(ExecUnit.local).(Local.promises) = bot)).
  { econs; eauto. }
  rename H into PROMISES.

  assert (SIM: sim_eu tid (length eu1.(ExecUnit.mem)) (length eu1.(ExecUnit.mem)) bot eu1 eu2).
  { destruct eu1 as [st1 lc1 mem1].
    destruct eu2 as [st2 lc2 mem2].
    inv STEP. inv LOCAL. ss. subst. inv MEM2. subst. econs; ss.
    - econs; ss. econs. ii.
      destruct (IdMap.find id (State.rmap st2)) eqn:FIND; ss. econs.
      inv WF. ss.
    - (* sim_lc *)
      { inv WF. inv LOCAL. ss. econs; ss.
        - i. destruct (FWDBANK loc0). des. econs; eauto.
          + rewrite VIEW, TS, <- COH. apply Memory.latest_ts_spec.
          + destruct (FWDBANK loc0). des.
            exploit Memory.latest_ts_spec; eauto. i. des.
            rewrite LE, COH in TS0. clear -TS0 H. i. lia.
          + erewrite Memory.read_mon; eauto.
        - destruct (Local.exbank lc1) eqn:X; ss. exploit EXBANK; eauto. intro Y. inv Y. des.
          econs. econs 1; ss.
          + rewrite VIEW, COH. ss.
          + i. exploit lt_le_trans; eauto.
            i. exploit lt_le_trans; [|apply Memory.latest_ts_spec|]; eauto.
            i. exploit lt_le_trans; [|apply COH|]; eauto.
            clear. lia.
        - i. rewrite Promises.set_o. condtac; ss.
          inversion e. subst. lia.
        - i. destruct (Promises.lookup tsp (Local.promises lc1)) eqn:X; ss.
          + exploit PROMISES0; eauto. lia.
          + rewrite Promises.lookup_bot. ss.
      }
    - econs; ss.
      + rewrite app_nil_r. ss.
      + i. exploit ExecUnit.get_msg_wf; eauto. lia.
      + i. destruct n1; ss.
  }

  inv CERTIFY. exploit sim_eu_rtc_step_bot; eauto.
  { i. rewrite Promises.lookup_bot in TSP. ss. }
  { eapply ExecUnit.promise_step_wf; eauto. }
  i. des. econs; eauto.
Qed.

Lemma step_certify
      tid eu1 eu2
      (CERTIFY: certify tid eu2)
      (STEP: ExecUnit.step tid eu1 eu2)
      (WF: ExecUnit.wf tid eu1):
  certify tid eu1.
Proof.
  inv STEP.
  - eapply state_step_certify; eauto.
  - eapply promise_step_certify; eauto.
Qed.

Lemma eu_wf_interference
      tid st (lc:Local.t (A:=unit)) mem mem_interference
      (INTERFERENCE: Forall (fun msg => msg.(Msg.tid) <> tid) mem_interference)
      (WF: ExecUnit.wf tid (ExecUnit.mk st lc mem)):
  ExecUnit.wf tid (ExecUnit.mk st lc (mem ++ mem_interference)).
Proof.
  inv WF. ss. econs; ss.
  - apply ExecUnit.rmap_interference_wf. ss.
  - apply Local.interference_wf; ss.
Qed.

Lemma interference_certify
      tid st lc mem mem_interference
      (INTERFERENCE: Forall (fun msg => msg.(Msg.tid) <> tid) mem_interference)
      (CERTIFY: certify tid (ExecUnit.mk st lc (mem ++ mem_interference)))
      (WF: ExecUnit.wf tid (ExecUnit.mk st lc mem)):
  certify tid (ExecUnit.mk st lc mem).
Proof.
  destruct (classic (lc.(Local.promises) = bot)).
  { econs; eauto. }
  rename H into PROMISES.

  assert (SIM: sim_eu tid (length mem) (length mem) bot (ExecUnit.mk st lc mem) (ExecUnit.mk st lc (mem ++ mem_interference))).
  { econs; ss.
    - econs; ss. econs. ii.
      destruct (IdMap.find id (State.rmap st)) eqn:FIND; ss. econs.
      inv WF. ss.
    - (* sim_lc *)
      { inv WF. inv LOCAL. ss. econs; ss.
        - i. destruct (FWDBANK loc). des. econs; eauto.
          + rewrite VIEW, TS, <- COH. apply Memory.latest_ts_spec.
          + destruct (FWDBANK loc). des.
            exploit Memory.latest_ts_spec; eauto. i. des.
            rewrite LE, COH in TS0. clear -TS0 H. i. lia.
          + erewrite Memory.read_mon; eauto.
        - destruct (Local.exbank lc) eqn:X; ss. exploit EXBANK; eauto. intro Y. inv Y. des.
          econs. econs 1; ss.
          + rewrite VIEW, COH. ss.
          + i. exploit lt_le_trans; eauto.
            i. exploit lt_le_trans; [|apply Memory.latest_ts_spec|]; eauto.
            i. exploit lt_le_trans; [|apply COH|]; eauto.
            clear. lia.
        - i. destruct (Promises.lookup tsp (Local.promises lc)) eqn:X; ss.
          + exploit PROMISES0; eauto. lia.
          + rewrite Promises.lookup_bot. ss.
      }
    - econs; ss.
      + rewrite app_nil_r. ss.
      + i. exploit ExecUnit.get_msg_wf; eauto. lia.
      + i. destruct n1; ss.
  }

  inv CERTIFY. exploit sim_eu_rtc_step_bot; eauto.
  { i. rewrite Promises.lookup_bot in TSP. ss. }
  { apply eu_wf_interference; ss. }
  i. des. econs; eauto.
Qed.

Theorem certified_exec_complete p m
        (EXEC: Machine.exec p m):
  certified_exec p m.
Proof.
  inv EXEC. econs; ss.
  apply clos_rt1n_rt, clos_rt_rtn1 in STEP.
  assert (CERTIFY: forall tid st lc (FIND: IdMap.find tid m.(Machine.tpool) = Some (st, lc)),
             certify tid (ExecUnit.mk st lc m.(Machine.mem))).
  { i. econs; eauto. s. inv NOPROMISE. eauto. }
  revert CERTIFY. clear NOPROMISE. induction STEP; [refl|].
  i. exploit IHSTEP; cycle 1.
  { i. etrans; eauto. econs 2; [|econs 1].
    inv H. econs; eauto. econs; ss. apply CERTIFY.
    rewrite TPOOL, IdMap.add_spec. condtac; ss. congr.
  }
  exploit Machine.rtc_step_step_wf.
  { apply clos_rt_rt1n, clos_rtn1_rt. eauto. }
  { apply Machine.init_wf. }
  i. inv H. rewrite TPOOL in *.
  generalize (CERTIFY tid). rewrite IdMap.add_spec. condtac.
  { inversion e. subst. rewrite FIND in FIND0. inv FIND0.
    intro Y. exploit Y; eauto. i. clear Y.
    eapply step_certify; eauto.
    eapply x0. ss.
  }
  inv STEP0.
  - (* state step *)
    inv STEP1. inv STEP0. ss. rewrite MEM in *.
    intro Y. eapply Y. ss.
  - (* promise step *)
    inv STEP1. ss. subst. inv LOCAL. inv MEM2. rewrite <- H1 in *.
    intro Y. eapply interference_certify; try by apply Y; eauto.
    + econs; ss. unfold nequiv_dec, swap_sumbool.
      match goal with
      | [|- context[match ?c with | left _ => _ | right _ => _ end]] => destruct c
      end; ss.
      congr.
    + eapply x0. ss.
Qed.

Theorem certified_exec_equivalent p m:
  Machine.exec p m <-> certified_exec p m.
Proof.
  split.
  - apply certified_exec_complete.
  - apply certified_exec_sound.
Qed.
