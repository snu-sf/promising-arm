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

Require Import PromisingArch.lib.Basic.
Require Import PromisingArch.lib.Order.
Require Import PromisingArch.lib.Time.
Require Import PromisingArch.lib.Lang.
Require Import PromisingArch.promising.Promising.
Require Import PromisingArch.lcertify.Certify.
Require Import PromisingArch.lcertify.CertifySim.

Set Implicit Arguments.


Inductive certified_promise (tid:Id.t) (eu1:ExecUnit.t (A:=unit)) (loc:Loc.t) (val:Val.t): Prop :=
| certified_promise_intro
    eu2 eu3 eu4 mem2' view_pre
    (STEP2: rtc (certify_step tid) eu1 eu2)
    (STEP3: write_step tid loc val view_pre eu2 eu3)
    (STEP4: rtc (certify_step tid) eu3 eu4)
    (PROMISES: Local.promises (ExecUnit.local eu4) = bot)
    (MEM: eu2.(ExecUnit.mem) = eu1.(ExecUnit.mem) ++ mem2')
    (MEM2': Forall (fun msg => msg.(Msg.loc) <> loc) mem2')
    (COH_PRE: (eu2.(ExecUnit.local).(Local.coh) loc).(View.ts) <= length eu1.(ExecUnit.mem))
    (VIEW_PRE: view_pre.(View.ts) <= length eu1.(ExecUnit.mem))
.

Lemma promise_src_sim_eu
      tid (eu1:ExecUnit.t (A:=unit)) loc val
      (WF: ExecUnit.wf tid eu1):
  exists eu2,
    <<STATE: eu2.(ExecUnit.state) = eu1.(ExecUnit.state)>> /\
    <<STEP: Local.promise loc val (S (length eu1.(ExecUnit.mem))) tid
                          eu1.(ExecUnit.local) eu1.(ExecUnit.mem)
                          eu2.(ExecUnit.local) eu2.(ExecUnit.mem)>> /\
    <<MSG: nth_error eu2.(ExecUnit.mem) (length eu1.(ExecUnit.mem)) = Some (Msg.mk loc val tid)>> /\
    <<SIM: sim_eu tid (length eu1.(ExecUnit.mem)) (Promises.set (S (length eu1.(ExecUnit.mem))) bot) eu2 eu1>>.
Proof.
  destruct eu1 as [st1 lc1 mem1]. eexists (ExecUnit.mk _ _ _). splits; ss.
  { rewrite nth_error_app2, Nat.sub_diag; ss. }
  econs; ss.
  - econs; ss. econs. ii. destruct (IdMap.find id (State.rmap st1)); ss. econs. econs. ss.
  - econs; ss.
    + inv WF. inv LOCAL. ss. i. specialize (FWDBANK loc0). inv FWDBANK. des.
      assert (FWD_TS: FwdItem.ts (Local.fwdbank lc1 loc0) <= length mem1).
      { rewrite TS. apply Memory.latest_latest_ts. apply Memory.ge_latest. ss. }
      econs 1; eauto.
      * rewrite VIEW. ss.
      * lia.
      * apply Memory.read_mon. ss.
    + inv WF. inv LOCAL. ss.
      destruct (Local.exbank lc1); ss. specialize (EXBANK _ eq_refl). inv EXBANK. des. econs.
      assert (EXBANK_TS: Exbank.ts t <= length mem1).
      { rewrite TS. apply Memory.latest_latest_ts. apply Memory.ge_latest. ss. }
      econs; ss.
      * rewrite VIEW. ss.
      * lia.
    + i. rewrite Promises.set_o. condtac; ss. clear X. inv e. lia.
    + i. rewrite ? Promises.set_o, Promises.lookup_bot. condtac; ss.
      eapply Local_wf_promises_above; eauto. apply WF.
  - econs; ss.
    + rewrite app_nil_r. ss.
    + i. revert TSP. rewrite Promises.set_o, Promises.lookup_bot. condtac; ss. clear X. inv e.
      rewrite app_length. s. clear. lia.
    + i. revert TSP. rewrite Promises.set_o, Promises.lookup_bot. condtac; ss. clear X. inv e.
      apply nth_error_snoc_inv in MSG. des; subst; ss.
      * lia.
      * splits; ss. inv WF. inv LOCAL. ss. eapply le_lt_trans; [apply COH|]. ss.
    + i. apply nth_error_singleton_inv in NTH. des. subst.
      revert PROMISES. rewrite Promises.set_o. condtac; ss.
      exfalso. apply c. rewrite Time.add_0_r. refl.
Qed.

Lemma sim_eu_write_step
      tid ts loc val view_pre tsp src_promises eu1 eu2 eu2'
      (SIM: sim_eu tid ts src_promises eu1 eu2)
      (STEP: write_step tid loc val view_pre eu2 eu2')
      (SRC_PROMISES_BELOW: forall tsp' msg
                             (TSP': Promises.lookup (S tsp') (Promises.unset (S tsp) src_promises))
                             (MEM: nth_error eu1.(ExecUnit.mem) tsp' = Some msg),
          (eu2'.(ExecUnit.local).(Local.coh) msg.(Msg.loc)).(View.ts) <= ts)
      (TSP: nth_error eu1.(ExecUnit.mem) tsp = Some (Msg.mk loc val tid))
      (WF1: ExecUnit.wf tid eu1)
      (WF2: ExecUnit.wf tid eu2)
      (VCAP: eu2'.(ExecUnit.local).(Local.vcap).(View.ts) <= ts)
      (COH_PRE: (eu2.(ExecUnit.local).(Local.coh) loc).(View.ts) <= ts)
      (VIEW_PRE: view_pre.(View.ts) <= ts):
  exists eu1',
    <<STEP: certify_step tid eu1 eu1'>> /\
    <<SIM: sim_eu tid ts (Promises.unset (S tsp) src_promises) eu1' eu2'>>.
Proof.
Admitted.

Theorem certified_promise_sound
        tid (eu1:ExecUnit.t (A:=unit)) loc val
        (WF1: ExecUnit.wf tid eu1)
        (CERTIFY: certified_promise tid eu1 loc val):
  exists eu2 ts,
    <<STATE: eu1.(ExecUnit.state) = eu2.(ExecUnit.state)>> /\
    <<LOCAL: Local.promise loc val ts tid
                           eu1.(ExecUnit.local) eu1.(ExecUnit.mem)
                           eu2.(ExecUnit.local) eu2.(ExecUnit.mem)>> /\
    <<CERTIFY: certify tid eu2>>.
Proof.
  inv CERTIFY.
  exploit rtc_certify_step_wf; try exact STEP2; eauto. intro WF2.
  exploit write_step_wf; eauto. intro WF3.
  exploit rtc_certify_step_wf; try exact STEP4; eauto. intro WF4.

  (* promise the message. *)
  exploit promise_src_sim_eu; try exact WF1; eauto. i. des. rename eu0 into eu1', STEP into STEP1', SIM into SIM1.
  exploit (ExecUnit.promise_step_wf (A:=unit)); try exact WF1; eauto.
  { econs; try exact STEP1'; ss. }
  intro WF1'.

  (* simulate the certified steps before writing the message. *)
  exploit sim_eu_rtc_step; try exact SIM1; eauto.
  { i. revert TSP. rewrite Promises.set_o. condtac; ss. clear X. inv e.
    rewrite MSG in MEM0. inv MEM0. s. i. apply COH_PRE.
  }
  { rewrite <- VIEW_PRE.
    destruct eu2 as [st2 lc2 mem2].
    destruct eu3 as [st3 lc3 mem3].
    inv STEP3. inv PROMISE. inv FULFILL. inv WRITABLE. ss. subst.
    rewrite <- join_r, <- join_r, <- join_l. ss.
  }
  i. des. rename eu1'0 into eu2', STEP into STEP2', SIM into SIM2.
  exploit rtc_certify_step_wf; try exact STEP2'; eauto. intro WF2'.

  (* simulate the write step. *)
  exploit sim_eu_write_step; try exact SIM2; eauto.
  { i. revert TSP'. rewrite Promises.unset_o, Promises.set_o. condtac; ss. rewrite X. clear X.
    rewrite Promises.lookup_bot. ss.
  }
  { admit. (* mem monotone *) }
  { rewrite <- VIEW_PRE.
    destruct eu2 as [st2 lc2 mem2].
    destruct eu3 as [st3 lc3 mem3].
    inv STEP3. inv PROMISE; inv FULFILL; ss. subst. ss.
    inv WRITABLE. ss. apply join_spec.
    - rewrite <- join_r, <- join_r, <- join_l. ss.
    - rewrite <- join_l. ss.
  }
  replace (Promises.unset (S (length (ExecUnit.mem eu1))) (Promises.set (S (length (ExecUnit.mem eu1))) bot)) with (bot:Promises.t); cycle 1.
  { apply Promises.ext. i. rewrite Promises.unset_o, Promises.set_o. condtac; ss. clear X. inv e.
    apply Promises.lookup_bot.
  }
  i. des. rename eu1'0 into eu3', STEP into STEP3', SIM into SIM3.
  exploit certify_step_wf; try exact STEP3'; eauto. intro WF3'.

  (* simulate the certified steps after writing the message. *)
  exploit sim_eu_rtc_step_bot; try exact SIM3; eauto.
  { i. revert TSP. rewrite Promises.lookup_bot. ss. }
  i. des. rename eu1'0 into eu4', STEP into STEP4'.

  esplits; try exact STEP1'; ss. econs; [|exact PROMISES0].
  etrans; eauto.
Admitted.


Lemma promise_tgt_sim_eu
      tid (eu1 eu2:ExecUnit.t (A:=unit))
      (WF: ExecUnit.wf tid eu1)
      (STEP: ExecUnit.promise_step tid eu1 eu2):
  sim_eu tid (length eu1.(ExecUnit.mem)) bot eu1 eu2.
Proof.
  destruct eu1 as [st1 lc1 mem1].
  destruct eu2 as [st2 lc2 mem2].
  inv STEP. inv LOCAL. inv MEM2. ss. subst. econs; ss.
  econs; ss.
  - econs. ii. destruct (IdMap.find id (State.rmap st2)); ss. econs. econs. ss.
  - econs; ss.
    + inv WF. inv LOCAL. ss. i. specialize (FWDBANK loc0). inv FWDBANK. des.
      assert (FWD_TS: FwdItem.ts (Local.fwdbank lc1 loc0) <= length mem1).
      { rewrite TS. apply Memory.latest_latest_ts. apply Memory.ge_latest. ss. }
      econs 1; eauto.
      * rewrite VIEW. ss.
      * lia.
      * apply Memory.read_mon. ss.
    + inv WF. inv LOCAL. ss.
      destruct (Local.exbank lc1); ss. specialize (EXBANK _ eq_refl). inv EXBANK. des. econs.
      assert (EXBANK_TS: Exbank.ts t <= length mem1).
      { rewrite TS. apply Memory.latest_latest_ts. apply Memory.ge_latest. ss. }
      econs; ss.
      * rewrite VIEW. ss.
      * lia.
    + i. rewrite Promises.set_o. condtac; ss. clear X. inv e. lia.
    + i. rewrite ? Promises.set_o, Promises.lookup_bot.
      eapply Local_wf_promises_above; eauto. apply WF.
  - econs; ss.
    + rewrite app_nil_r. ss.
    + i. revert TSP. rewrite Promises.lookup_bot. ss.
    + i. destruct n1; ss.
Qed.

Theorem certified_promise_complete
        tid (eu1 eu2:ExecUnit.t (A:=unit)) loc val ts
        (WF1: ExecUnit.wf tid eu1)
        (STATE: eu1.(ExecUnit.state) = eu2.(ExecUnit.state))
        (LOCAL: Local.promise loc val ts tid
                              eu1.(ExecUnit.local) eu1.(ExecUnit.mem)
                              eu2.(ExecUnit.local) eu2.(ExecUnit.mem))
        (CERTIFY: certify tid eu2):
  certified_promise tid eu1 loc val.
Proof.
  (* promise the message. *)
  exploit promise_tgt_sim_eu; eauto.
  { econs; eauto. }
  intro SIM1.
  exploit (ExecUnit.promise_step_wf (A:=unit)); eauto.
  { econs; eauto. }
  intro WF2.

  (* TODO: simulate the certified steps before fulfilling the message. *)

  (* TODO: simulate the fulfill step. *)

  (* TODO: simulate the certified steps after fulfilling the message. *)
Admitted.
