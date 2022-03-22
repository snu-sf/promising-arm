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
    eu2 eu3 eu4 view_pre
    (STEP2: rtc (certify_step tid) eu1 eu2)
    (STEP3: write_step tid loc val view_pre eu2 eu3)
    (STEP4: rtc (certify_step tid) eu3 eu4)
    (PROMISES: Local.promises (ExecUnit.local eu4) = bot)
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
    <<SIM: sim_eu tid (length eu1.(ExecUnit.mem)) (length eu1.(ExecUnit.mem)) (Promises.set (S (length eu1.(ExecUnit.mem))) bot) eu2 eu1>>.
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
      eapply Local.wf_promises_above; eauto. apply WF.
  - econs; ss.
    + rewrite app_nil_r. ss.
    + i. revert TSP. rewrite Promises.set_o, Promises.lookup_bot. condtac; ss. clear X. inv e.
      rewrite app_length. esplits; ss.
      * rewrite nth_error_app2, Nat.sub_diag; ss.
      * ii. assert (ts = length mem1) by (clear -TS1 TS2; lia). subst.
        ss. des. subst. apply nth_error_snoc_inv in MSG. des; [lia|]. destruct msg. inv MSG0. ss.
      * apply Memory.ge_latest. clear. lia.
    + i. revert TSP. rewrite Promises.set_o, Promises.lookup_bot. condtac; ss. clear X. inv e.
      apply nth_error_snoc_inv in MSG. des; subst; ss.
      * lia.
      * splits; ss. inv WF. inv LOCAL. ss. eapply le_lt_trans; [apply COH|]. ss.
    + i. apply Memory.get_msg_snoc_inv in READ. des; subst; ss. lia.
    + i. apply nth_error_singleton_inv in NTH. des. subst.
      revert PROMISES. rewrite Promises.set_o. condtac; ss.
      exfalso. apply c. rewrite Time.add_0_r. refl.
Qed.

Lemma sim_eu_write_step
      tid ts loc val view_pre tsp src_promises eu1 eu2 eu2'
      (SIM: sim_eu tid ts ts src_promises eu1 eu2)
      (STEP: write_step tid loc val view_pre eu2 eu2')
      (SRC_PROMISES_BELOW: forall tsp' msg
                             (TSP': Promises.lookup (S tsp') (Promises.unset (S tsp) src_promises))
                             (MEM: nth_error eu1.(ExecUnit.mem) tsp' = Some msg),
          (eu2'.(ExecUnit.local).(Local.coh) msg.(Msg.loc)).(View.ts) <= ts)
      (TSPMSG: nth_error eu1.(ExecUnit.mem) tsp = Some (Msg.mk loc val tid))
      (TSP: Promises.lookup (S tsp) src_promises)
      (WF1: ExecUnit.wf tid eu1)
      (WF2: ExecUnit.wf tid eu2)
      (VCAP: eu2'.(ExecUnit.local).(Local.vcap).(View.ts) <= ts)
      (COH_PRE: (eu2.(ExecUnit.local).(Local.coh) loc).(View.ts) <= ts)
      (VIEW_PRE: view_pre.(View.ts) <= ts):
  exists eu1',
    <<STEP: certify_step tid eu1 eu1'>> /\
    <<SIM: sim_eu tid ts ts (Promises.unset (S tsp) src_promises) eu1' eu2'>>.
Proof.
  exploit write_step_wf; eauto. intro WF2'.
  destruct eu1 as [[stmts1 rmap1] lc1 mem1].
  destruct eu2 as [[stmts2 rmap2] lc2 mem2].
  destruct eu2' as [[stmts2' rmap2'] lc2' mem2'].
  inv SIM. inv STATE. ss. subst.
  exploit sim_mem_length; eauto. intro LEN. des.
  inv STEP. ss. inv STATE. inv PROMISE. inv FULFILL. inv MEM2. ss.
  exploit sim_rmap_expr; eauto. instantiate (1 := eloc).
  intro X. inv X. exploit TS.
  { rewrite <- VCAP, <- join_r. ss. }
  clear TS. intro TS. rewrite <- TS in *.
  exploit sim_rmap_expr; eauto. instantiate (1 := eval).
  intro X. inv X. exploit TS0.
  { rewrite <- VIEW_PRE. inv WRITABLE. ss. rewrite <- join_r, <- join_l. ss. }
  clear TS0. intro EVAL. rewrite <- EVAL in *.
  remember view_pre as view_pre' eqn:VIEW_PRE'. guardH VIEW_PRE'. rewrite VIEW_PRE' in VIEW_PRE.
  inversion MEM. subst. inv LOCAL.
  exploit SRC_PROMISES_WF; eauto. intro x. des.
  rename x into ABOVE, x0 into XMSG, x1 into XCLUSIVE, x2 into XLATEST.
  rewrite XMSG in TSPMSG. inv TSPMSG. ss.
  eexists (ExecUnit.mk _ _ _). esplits.
  - econs 1. econs. econs; ss.
    + econs; ss.
    + econs 3; ss. instantiate (3 := S tsp).
      econs; ss.
      * inv WF1. ss. inv WRITABLE. ss. econs; ss.
        { eapply le_lt_trans; [|exact ABOVE].
          eapply sim_view_below_weak; [|exact COH_PRE]. ss.
        }
        { eapply le_lt_trans; [|exact ABOVE].
          eapply sim_view_below_weak; [|exact VIEW_PRE]. rewrite <- VIEW_PRE'.
          repeat apply sim_view_join; ss; eauto using sim_view_ifc.
          apply sim_view_ifc. inv EXBANK; ss. inv REL; ss. apply sim_view_above. ss.
        }
        { intro X. specialize (EX X). des. inv LOCAL. inv EXBANK; [congr|].
          rewrite TSX in H. inv H. esplits; eauto.
          destruct a, eb. ss. i. subst.
          eapply Memory.no_msgs_split'. instantiate (1 := length mem). split; ss.
          destruct (le_lt_dec (S (length mem)) ts).
          { ii. clear -TS1 TS2 l. lia. }
          inv REL; ss. inv TS0. destruct (le_lt_dec ts0 (length mem)).
          - specialize (TS1 l0). subst. ii. eapply EX0; eauto.
            + rewrite TS2, app_length. clear. lia.
            + apply nth_error_app_inv in MSG0. des; ss.
              * apply nth_error_app_mon. apply nth_error_app_mon. ss.
              * clear -TS1 TS2 MSG0. lia.
          - apply EXCLUSIVE; ss.
        }
      * rewrite PROMISES2; ss.
  - inv WRITABLE. ss.
    econs; ss.
    + econs; ss. apply sim_rmap_add; ss. econs; ss.
      unfold ifc. condtac; ss. intro Y. clear -Y LEN0. exfalso. lia.
    + econs; ss.
      * i. rewrite ? fun_add_spec. condtac; ss.
        apply sim_view_above. s. clear -LEN0. lia.
      * apply sim_view_join; ss.
        apply sim_view_above. s. clear -LEN0. lia.
      * apply sim_view_join; ss.
      * apply sim_view_join; ss. unfold ifc. condtac; ss.
        apply sim_view_above. s. clear -LEN0. lia.
      * i. rewrite ? fun_add_spec. condtac; ss.
        { clear X. inv e.
          destruct (le_lt_dec (View.ts (ValA.annot (sem_expr rmap2 eval))) (length mem)).
          - rewrite <- EVAL in *.
            econs 1; ss.
            + apply join_spec; ss. rewrite <- VCAP, <- join_r. ss.
            + apply sim_time_above. clear -LEN0. lia.
            + unfold Memory.read. s. rewrite XMSG. s. condtac; [|congr]. ss.
            + eapply Memory.get_msg_read; eauto.
          - econs 2; ss.
            eapply lt_le_trans; eauto. rewrite <- EVAL, <- join_r. ss.
        }
        { replace (mem ++ mem1') with ((mem ++ mem1') ++ []) by apply app_nil_r.
          eapply sim_fwdbank_mon; eauto.
          inv WF1. ss. inv LOCAL. destruct (FWDBANK0 loc). des.
          rewrite TS0, <- COH1. apply Memory.latest_ts_spec.
        }
      * destruct ex; ss. inv EXBANK; econs; ss.
        replace (mem ++ mem1') with ((mem ++ mem1') ++ []) by apply app_nil_r.
        eapply sim_exbank_mon; eauto.
      * i. rewrite ? Promises.unset_o, ? Promises.set_o.
        condtac; clear X.
        { inv e. clear -ABOVE TSP0. lia. }
        condtac; clear X.
        { inv e. clear -TSP0. rewrite app_length in TSP0. lia. }
        apply PROMISES1. ss.
      * i. rewrite ? Promises.unset_o. condtac; ss.
        rewrite PROMISES2; ss.
    + econs.
      * ss.
      * ss.
      * rewrite <- app_assoc. ss.
      * i. revert TSP0. rewrite Promises.unset_o. condtac; ss. i. exploit SRC_PROMISES_WF; eauto.
      * i. revert TSP0. rewrite Promises.unset_o. condtac; ss. i. exploit SRC_PROMISES; eauto. i. des. subst.
        exploit SRC_PROMISES_BELOW; eauto.
        { rewrite Promises.unset_o. condtac; ss. }
        rewrite ? fun_add_spec. condtac; ss. clear X0. inv e.
        exploit SRC_PROMISES_WF; eauto. intro x0. des. rewrite MSG0 in x1. inv x1. splits; ss.
        destruct (Time.compare_spec (S tsp) (S tsp0)).
        { subst. congr. }
        { clear -H. lia. }
        exfalso. eapply x3; eauto. apply nth_error_some in XMSG. ss.
      * ss.
      * i. revert PROMISES. rewrite Promises.unset_o. condtac; clear X; ss.
        { inv e. i.
          move XMSG at bottom. apply nth_error_app_inv in XMSG. des.
          { clear -XMSG. lia. }
          replace (length mem + n1 - length mem) with n1 in XMSG0 by lia. rewrite XMSG0 in NTH. inv NTH.
          s. esplits; ss.
          - rewrite fun_add_spec. condtac; [|congr]. refl.
          - rewrite nth_error_app2, Nat.sub_diag; ss.
          - ss.
          - s. rewrite fun_add_spec. condtac; [|congr]. s. rewrite app_length. ss.
        }
        { i. exploit MEM1'; eauto. i. des. subst. esplits; swap 1 3.
          { apply nth_error_app_mon. eauto. }
          all: ss.
          - rewrite fun_add_spec. condtac; ss. clear X. inv e.
            destruct (le_lt_dec (S (length mem + n1)) (S tsp)); ss.
            exfalso. eapply XLATEST; eauto.
            + s. apply nth_error_some in NTH. clear -NTH. rewrite app_length. lia.
            + rewrite nth_error_app2; [|clear; lia].
              replace (length mem + n1 - length mem) with n1; ss. clear. lia.
          - s. rewrite MSGCOH0, fun_add_spec. condtac; ss.
            inv WF2. ss. inv LOCAL. rewrite COH1. clear. lia.
        }
Qed.

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
    rewrite MSG in MEM. inv MEM. s. i. apply COH_PRE.
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
  { exploit rtc_certify_step_incr; eauto. intro LE. inv LE.
    rewrite MEM. rewrite nth_error_app1; eauto.
    inv STEP1'. inv MEM2. rewrite app_length. clear. s. lia.
  }
  { rewrite Promises.set_o, Promises.lookup_bot. condtac; ss. congr. }
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
Qed.


Lemma promise_tgt_sim_eu
      tid (eu1 eu2:ExecUnit.t (A:=unit))
      (WF: ExecUnit.wf tid eu1)
      (STEP: ExecUnit.promise_step tid eu1 eu2):
  sim_eu tid (length eu1.(ExecUnit.mem)) (length eu1.(ExecUnit.mem)) bot eu1 eu2.
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
      eapply Local.wf_promises_above; eauto. apply WF.
  - econs; ss.
    + rewrite app_nil_r. ss.
    + i. exploit ExecUnit.get_msg_wf; eauto. lia.
    + i. destruct n1; ss.
Qed.

Lemma identify_fulfill
      tid (eu1:ExecUnit.t (A:=unit)) tsp loc val
      (WF1: ExecUnit.wf tid eu1)
      (PROMISE: Promises.lookup tsp eu1.(ExecUnit.local).(Local.promises))
      (MEM: Memory.read loc tsp eu1.(ExecUnit.mem) = Some val)
      (CERTIFY: certify tid eu1):
  exists eu2 eu3 eu4 ex ord vloc vval res view_pre,
    <<STEP2: rtc (certify_step tid) eu1 eu2>> /\
    <<ST3: State.step (Event.write ex ord vloc vval res) eu2.(ExecUnit.state) eu3.(ExecUnit.state)>> /\
    <<LC3: Local.fulfill ex ord vloc vval res tsp tid view_pre eu2.(ExecUnit.local) eu2.(ExecUnit.mem) eu3.(ExecUnit.local)>> /\
    <<MEM3: eu2.(ExecUnit.mem) = eu3.(ExecUnit.mem)>> /\
    <<VLOC3: vloc.(ValA.val) = loc>> /\
    <<VVAL3: vval.(ValA.val) = val>> /\
    <<STEP4: rtc (certify_step tid) eu3 eu4>> /\
    <<PROMISES: eu4.(ExecUnit.local).(Local.promises) = bot>>.
Proof.
  inv CERTIFY. revert WF1 NOPROMISE MEM PROMISE. induction STEPS.
  { i. rewrite NOPROMISE, Promises.lookup_bot in PROMISE. ss. }
  i. exploit certify_step_wf; try exact H; eauto. intro WF2.
  destruct (Promises.lookup tsp (Local.promises (ExecUnit.local y))) eqn:PROMISE2.
  { exploit IHSTEPS; eauto.
    { exploit certify_step_incr; eauto. intro LE. inv LE. rewrite MEM0 in *.
      eapply Memory.read_mon. ss.
    }
    i. des. subst. esplits; try exact LC3; try exact PROMISES; eauto.
  }
  destruct x as [st1 lc1 mem1].
  destruct y as [st2 lc2 mem2].
  ss. inv H; cycle 1.
  { inv STEP. inv PROMISE0. inv FULFILL. ss. inv MEM2. ss.
    revert PROMISE2. rewrite Promises.unset_o, Promises.set_o. condtac; ss.
    - clear X. inv e. revert PROMISE. erewrite Local.wf_promises_above; ss. apply WF1.
    - rewrite PROMISE. ss.
  }
  inv STEP. inv STEP0. ss. subst. revert PROMISE PROMISE2. inv LOCAL; (try inv STEP); (try inv LC); ss.
  all: try congr.
  rewrite Promises.unset_o. condtac; [|congr]. clear X. inv e.
  i. exploit Memory.read_get_msg; eauto. i. des; subst; ss.
  rewrite MSG in x0. inv x0. eexists (ExecUnit.mk st1 _ _), (ExecUnit.mk st2 _ _). s. esplits; eauto.
  econs; eauto.
Qed.

Lemma sim_eu_fulfill_step
      tid ts loc val ex ord vloc vval res view_pre (eu1 eu2 eu2':ExecUnit.t (A:=unit))
      (SIM: sim_eu tid ts ts bot eu1 eu2)
      (ST: State.step (Event.write ex ord vloc vval res) eu2.(ExecUnit.state) eu2'.(ExecUnit.state))
      (LC: Local.fulfill ex ord vloc vval res (S ts) tid view_pre eu2.(ExecUnit.local) eu2.(ExecUnit.mem) eu2'.(ExecUnit.local))
      (MEM: eu2'.(ExecUnit.mem) = eu2.(ExecUnit.mem))
      (VLOC: vloc.(ValA.val) = loc)
      (VVAL: vval.(ValA.val) = val)
      (WF1: ExecUnit.wf tid eu1)
      (WF2: ExecUnit.wf tid eu2)
      (VIEW_PRE: view_pre.(View.ts) <= ts):
  exists eu1',
    <<STEP: write_step tid loc val view_pre eu1 eu1'>> /\
    <<SIM: sim_eu tid ts ts bot eu1' eu2'>> /\
    <<COH_PRE: (eu1.(ExecUnit.local).(Local.coh) loc).(View.ts) <= ts>>.
Proof.
  destruct eu1 as [[stmt1 rmap1] lc1 mem1].
  destruct eu2 as [[stmt2 rmap2] lc2 mem2].
  destruct eu2' as [[stmt2' rmap2'] lc2' mem2'].
  ss. subst.

  assert (VCAP_BELOW: lc2.(Local.vcap).(View.ts) <= ts).
  { inv LC. inv WRITABLE. ss. subst. ss.
    clear -EXT. unfold join, Time.join in *. lia.
  }
  assert (LOC_BELOW: vloc.(ValA.annot).(View.ts) <= ts).
  { inv LC. inv WRITABLE. ss. subst. ss.
    clear -EXT. unfold join, Time.join in *. lia.
  }
  assert (VAL_BELOW: vval.(ValA.annot).(View.ts) <= ts).
  { inv LC. inv WRITABLE. ss. subst. ss.
    clear -EXT. unfold join, Time.join in *. lia.
  }

  inv SIM. inv STATE. inv ST. inv LC. ss. subst.
  exploit sim_rmap_expr; eauto. instantiate (1 := eloc). intro ELOC. apply sim_val_below in ELOC; ss.
  exploit sim_rmap_expr; eauto. instantiate (1 := eval). intro EVAL. apply sim_val_below in EVAL; ss.
  exploit sim_mem_length; eauto. intro LEN. des.

  eexists (ExecUnit.mk _ _ _). esplits.
  - econs; ss.
    + econs; ss.
    + econs; ss.
      * inv WRITABLE. econs; ss.
        { symmetry. eapply sim_view_eq; cycle 1.
          { instantiate (1 := ts). clear -EXT. ss. lia. }
          repeat apply sim_view_join; ss.
          all: try apply sim_view_ifc.
          all: try apply sim_view_bot.
          all: try by apply LOCAL.
          inv LOCAL. inv EXBANK; ss. inv REL; ss. clear -ABOVE. econs. lia.
        }
        { inv LOCAL. destruct (COH0 (ValA.val (sem_expr rmap2 eloc))).
          rewrite TS; ss.
          - eapply lt_le_trans; [exact COH|]. exploit sim_mem_length; eauto. clear. lia.
          - clear -COH. lia.
        }
        { eapply lt_le_trans; [exact EXT|]. exploit sim_mem_length; eauto. clear. lia. }
        { i. specialize (EX H). des. inv LOCAL. rewrite TSX in *. inv EXBANK.
          destruct a, eb. ss. esplits; eauto. ss. i. subst.
          eapply Memory.no_msgs_split'. instantiate (1 := ts). split; cycle 1.
          { ii. apply nth_error_snoc_inv in MSG0. des; subst; ss.
            apply H2. inv MEM. eapply TS_PRIVATE; eauto.
          }
          inv REL; ss; subst.
          + destruct (le_lt_dec ts1 ts); cycle 1.
            { apply Memory.no_msgs_full; ss. apply EXCLUSIVE. ss. }
            apply sim_time_below in TS. subst.
            apply Memory.no_msgs_full. all: ss.
            specialize (EX0 eq_refl). ii. eapply EX0; eauto.
            inv MEM. apply nth_error_app_inv in MSG0. des; subst; [|lia].
            rewrite nth_error_app1; ss.
          + apply Memory.no_msgs_full; ss.
        }
      * unfold Memory.get_msg. s. rewrite nth_error_app2, Nat.sub_diag; ss.
      * rewrite Promises.set_o. condtac; ss. congr.
  - econs; ss.
    + econs; ss. apply sim_rmap_add; ss.
      destruct (ex && equiv_dec arch riscv); ss. apply sim_val_above. ss.
    + inv LOCAL. econs; ss.
      * i. rewrite ? fun_add_spec. condtac; ss. apply sim_view_above. ss.
      * apply sim_view_join; ss. apply sim_view_above. ss.
      * apply sim_view_join; ss.
      * apply sim_view_join; ss. unfold ifc. condtac; ss. apply sim_view_above. ss.
      * i. rewrite ? fun_add_spec. condtac; ss.
        { inversion e. subst.
          destruct (le_lt_dec (View.ts (ValA.annot (sem_expr rmap2 eval))) ts).
          - rewrite <- EVAL in *.
            econs 1; ss.
            + apply join_spec; ss.
            + apply sim_time_above. ss.
            + splits.
              * clear -LEN. lia.
              * apply Memory.ge_no_msgs. clear. rewrite app_length. s. lia.
            + unfold Memory.read. s. rewrite ? nth_error_app2, ? Nat.sub_diag; ss. condtac; ss.
            + eapply Memory.get_msg_read; eauto.
          - econs 2; ss.
            + eapply lt_le_trans; eauto. apply join_r.
            + rewrite app_length. s. ii. lia.
        }
        { exploit sim_fwdbank_mon; try exact MEM; cycle 3.
          - rewrite (@app_nil_r _ mem2). eauto.
          - ss.
          - inv WF1. ss. inv LOCAL. destruct (FWDBANK0 loc). des.
            rewrite TS, <- COH0. apply Memory.latest_ts_spec.
          - econs; ss. destruct (nequiv_dec (ValA.val (sem_expr rmap2 eloc)) loc); ss. congr.
        }
      * destruct ex; ss. inv EXBANK; econs; ss.
        exploit sim_exbank_mon; eauto. rewrite (@app_nil_r _ mem2). eauto.
      * i. rewrite ? Promises.unset_o, ? Promises.set_o. condtac.
        { inversion e. subst. clear -TSP MEM. inv MEM. rewrite app_length in TSP. lia. }
        condtac.
        { inversion e. subst. clear -TSP. lia. }
        apply PROMISES1. ss.
      * i. rewrite Promises.unset_o, Promises.set_o. condtac; ss.
        { clear X. inv e. rewrite <- PROMISES2; ss.
          erewrite Local.wf_promises_above; eauto. apply WF1.
        }
        { eauto. }
    + inv MEM. ss. econs.
      * ss.
      * rewrite <- app_assoc. ss.
      * ss.
      * i. revert TSP. rewrite Promises.lookup_bot. ss.
      * i. apply nth_error_snoc_inv in MSG0. des.
        { exploit SRC_PROMISES; eauto. i. des. subst. splits; ss. }
        { subst. splits; ss. }
      * i. apply Memory.get_msg_snoc_inv in READ. des; eauto. subst. ss.
      * i. apply nth_error_snoc_inv in NTH. des.
        { exploit MEM1'; eauto. i. des. subst. esplits; try exact MSG0; ss.
          - rewrite fun_add_spec. condtac; ss. rewrite app_length.
            exploit nth_error_Some. rewrite NTH0. intros [Y _]. clear -Y.
            exploit Y; [congr|]. lia.
          - rewrite fun_add_spec. condtac; ss. inversion e. destruct msg1, msg2. ss. subst.
            rewrite MSGCOH0. inv WRITABLE. clear -COH. lia.
        }
        { subst. ss. apply Memory.get_msg_app_inv in MSG. des.
          { clear -MSG. lia. }
          esplits; try exact MSG0; eauto.
          - rewrite fun_add_spec. condtac; [|congr]. s. rewrite app_length. ss.
          - s. rewrite fun_add_spec. condtac; [|congr]. s. clear. lia.
        }
  - inv LOCAL. inv WRITABLE.
    rewrite (sim_view_below (COH (ValA.val (sem_expr rmap2 eloc)))); clear -COH0; lia.
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
  replace ts with (S (length eu1.(ExecUnit.mem))) in *; cycle 1.
  { destruct eu1 as [st1 lc1 mem1].
    destruct eu2 as [st2 lc2 mem2].
    inv LOCAL. inv MEM2. ss.
  }

  (* promise the message. *)
  exploit promise_tgt_sim_eu; eauto.
  { econs; eauto. }
  intro SIM1.
  exploit (ExecUnit.promise_step_wf (A:=unit)); eauto.
  { econs; eauto. }
  intro WF2.

  (* identify the fulfill step. *)
  exploit identify_fulfill; try exact CERTIFY; eauto.
  { instantiate (1 := (S (length eu1.(ExecUnit.mem)))). inv LOCAL. inv MEM2.
    rewrite LC2. s. rewrite Promises.set_o. condtac; ss. congr.
  }
  { instantiate (1 := val). instantiate (1 := loc). inv LOCAL. inv MEM2.
    unfold Memory.read. s. rewrite nth_error_app2, Nat.sub_diag; ss. condtac; ss. congr.
  }
  i. des. subst. rename eu0 into eu3, eu3 into eu4, eu4 into eu5.
  rename STEP2 into STEP3, ST3 into ST4, LC3 into LC4, MEM3 into MEM4, STEP4 into STEP5, PROMISES into PROMISES5.
  exploit rtc_certify_step_wf; try exact STEP3; eauto. intro WF3.
  exploit (ExecUnit.state_step0_wf (A:=unit)); eauto.
  { econs; eauto. econs 3; eauto. }
  { econs; ss. }
  intro WF4.
  exploit rtc_certify_step_wf; try exact STEP4; eauto. intro WF5.

  (* simulate the certified steps before fulfill step. *)
  exploit sim_eu_rtc_step; try exact STEP3; eauto.
  { i. revert TSP. rewrite Promises.lookup_bot. ss. }
  { destruct eu1 as [st1 lc1 mem1].
    destruct eu2 as [st2 lc2 mem2].
    inv LOCAL. inv MEM2. ss. subst.
    destruct eu3 as [st3 lc3 mem3].
    destruct eu4 as [st4 lc4 mem4].
    inv LC4. inv WRITABLE. ss. subst.
    clear -EXT. unfold join, Time.join in *. lia.
  }
  i. des. rename eu1' into eu3', STEP into STEP3', SIM into SIM3.
  exploit rtc_certify_step_wf; try exact STEP3'; eauto. intro WF3'.
  assert (VIEW_PRE: View.ts view_pre <= length (ExecUnit.mem eu1)).
  { destruct eu3 as [st3 lc3 mem3].
    destruct eu4 as [st4 lc4 mem4].
    inv LC4. inv WRITABLE. ss. clear -EXT. lia.
  }

  (* simulate the fulfill step. *)
  exploit sim_eu_fulfill_step; try exact LC4; eauto.
  i. des. rename eu1' into eu4', STEP into STEP4', SIM into SIM4.
  exploit write_step_wf; try exact STEP4'; eauto. intro WF4'.

  (* simulate the certified steps after the fulfill step. *)
  exploit sim_eu_rtc_step_bot; try exact STEP5; eauto.
  { i. revert TSP. rewrite Promises.lookup_bot. ss. }
  i. des. rename eu1' into eu5', STEP into STEP5', PROMISES into PROMISES5'.
  exploit rtc_certify_step_wf; try exact STEP5'; eauto. intro WF5'.

  econs; try exact STEP4; eauto.
Qed.

Theorem certified_promise_correct
        tid (eu1:ExecUnit.t (A:=unit)) loc val
        (WF1: ExecUnit.wf tid eu1):
  certified_promise tid eu1 loc val <->
  exists eu2 ts,
    <<STATE: eu1.(ExecUnit.state) = eu2.(ExecUnit.state)>> /\
    <<LOCAL: Local.promise loc val ts tid
                           eu1.(ExecUnit.local) eu1.(ExecUnit.mem)
                           eu2.(ExecUnit.local) eu2.(ExecUnit.mem)>> /\
    <<CERTIFY: certify tid eu2>>.
Proof.
  split; i; des.
  - eapply certified_promise_sound; eauto.
  - eapply certified_promise_complete; eauto.
Qed.
