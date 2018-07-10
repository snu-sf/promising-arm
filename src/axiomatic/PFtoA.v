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
Require Import HahnSets.

Require Import PromisingArch.lib.Basic.
Require Import PromisingArch.lib.HahnRelationsMore.
Require Import PromisingArch.lib.Order.
Require Import PromisingArch.lib.Time.
Require Import PromisingArch.lib.Lang.
Require Import PromisingArch.promising.Promising.
Require Import PromisingArch.promising.StateExecFacts.
Require Import PromisingArch.axiomatic.Axiomatic.
Require Import PromisingArch.axiomatic.CommonAxiomatic.
Require Import PromisingArch.axiomatic.PFtoA1.
Require Import PromisingArch.axiomatic.PFtoA2.
Require Import PromisingArch.axiomatic.PFtoA3.
Require Import PromisingArch.axiomatic.PFtoA4OBW.
Require Import PromisingArch.axiomatic.PFtoA4OBR.
Require Import PromisingArch.axiomatic.PFtoA4FR.
Require Import PromisingArch.axiomatic.PFtoA4Atomic.
Require Import PromisingArch.axiomatic.PFtoA4SL.

Set Implicit Arguments.

          
Lemma sim_traces_sim_th'_step
      p trs atrs ws rs covs vexts
      m ex
      (STEP: Machine.pf_exec p m)
      (SIM: sim_traces p m.(Machine.mem) trs atrs ws rs covs vexts)
      (PRE: Valid.pre_ex p ex)
      (CO: ex.(Execution.co) = co_gen ws)
      (RF: ex.(Execution.rf) = rf_gen ws rs)
      (CO1: Valid.co1 ex)
      (CO2: Valid.co2 ex)
      (RF1: Valid.rf1 ex)
      (RF2: Valid.rf2 ex)
      (RF_WF: Valid.rf_wf ex)
      (TR: IdMap.Forall2
             (fun _ tr sl => exists l, tr = (ExecUnit.mk sl.(fst) sl.(snd) m.(Machine.mem)) :: l)
             trs m.(Machine.tpool))
      (ATR: IdMap.Forall2
              (fun _ atr aeu => exists l, atr = aeu :: l)
              atrs (Valid.aeus PRE)):
  forall tid tr atr covl vextl
    n eu1 eu2 tr' aeu1 aeu2 atr' cov1 cov2 covl' vext1 vext2 vextl'
    (FIND_TR: IdMap.find tid trs = Some tr)
    (FIND_ATR: IdMap.find tid atrs = Some atr)
    (FIND_COVL: IdMap.find tid covs = Some covl)
    (FIND_VEXTL: IdMap.find tid vexts = Some vextl)
    (EU: lastn (S n) tr = eu2 :: eu1 :: tr')
    (AEU: lastn (S n) atr = aeu2 :: aeu1 :: atr')
    (COV: lastn (S n) covl = cov2 :: cov1 :: covl')
    (VEXT: lastn (S n) vextl = vext2 :: vext1 :: vextl')
    (SIM_TH': sim_th' tid ex (v_gen vexts) eu1 aeu1),
    sim_th' tid ex (v_gen vexts) eu2 aeu2.
Proof.
  i. econs.
  - eapply sim_traces_sim_th'_sl; eauto.
  - eapply sim_traces_sim_th'_sl; eauto.
  - eapply sim_traces_sim_th'_ob_write; eauto.
  - eapply sim_traces_sim_th'_ob_read; eauto.
  - eapply sim_traces_sim_th'_fr; eauto.
  - eapply sim_traces_sim_th'_atomic; eauto.
Qed.

Lemma sim_traces_sim_th'
      p trs atrs ws rs covs vexts
      m ex
      (STEP: Machine.pf_exec p m)
      (SIM: sim_traces p m.(Machine.mem) trs atrs ws rs covs vexts)
      (PRE: Valid.pre_ex p ex)
      (CO: ex.(Execution.co) = co_gen ws)
      (RF: ex.(Execution.rf) = rf_gen ws rs)
      (CO1: Valid.co1 ex)
      (CO2: Valid.co2 ex)
      (RF1: Valid.rf1 ex)
      (RF2: Valid.rf2 ex)
      (RF_WF: Valid.rf_wf ex)
      (TR: IdMap.Forall2
             (fun _ tr sl => exists l, tr = (ExecUnit.mk sl.(fst) sl.(snd) m.(Machine.mem)) :: l)
             trs m.(Machine.tpool))
      (ATR: IdMap.Forall2
              (fun _ atr aeu => exists l, atr = aeu :: l)
              atrs (Valid.aeus PRE)):
  forall tid n tr atr covl vextl
    eu tr' aeu atr' cov covl' vext vextl'
    (N: n < length tr)
    (FIND_TR: IdMap.find tid trs = Some tr)
    (FIND_ATR: IdMap.find tid atrs = Some atr)
    (FIND_COVL: IdMap.find tid covs = Some covl)
    (FIND_VEXTL: IdMap.find tid vexts = Some vextl)
    (EU: lastn (S n) tr = eu :: tr')
    (AEU: lastn (S n) atr = aeu :: atr')
    (COV: lastn (S n) covl = cov :: covl')
    (VEXT: lastn (S n) vextl = vext :: vextl'),
    sim_th' tid ex (v_gen vexts) eu aeu.
Proof.
  intro tid. generalize (SIM tid). intro X. inv X; [by i|]. induction n.
  { (* init *)
    i. simplify. rename c into wl, d into rl.
    exploit (lastn_one tr).
    { exploit sim_trace_last; eauto. }
    i. des.
    exploit (lastn_one atr).
    { exploit sim_trace_last; eauto. i. des. subst. ss. lia. }
    i. des.
    (* exploit (lastn_one covl). *)
    (* { exploit sim_trace_last; eauto. i. des. subst. ss. lia. } *)
    (* i. des. *)
    (* exploit (lastn_one vextl). *)
    (* { exploit sim_trace_last; eauto. i. des. subst. ss. lia. } *)
    (* i. des. *)
    rewrite EU in x0. symmetry in x0. inv x0.
    rewrite AEU in x1. symmetry in x1. inv x1.
    (* rewrite COV in x2. symmetry in x2. inv x2. *)
    (* rewrite VEXT in x3. symmetry in x3. inv x3. *)
    exploit sim_trace_lastn; eauto. rewrite AEU. i.
    inv x0. ss. splits; i; try lia.
    admit.
  }
  i. simplify. rename c into wl, d into rl.
  exploit sim_trace_length; eauto. intro LEN. guardH LEN.
  exploit lastn_S1; try exact EU; [unguardH LEN; des; lia|i]. 
  exploit lastn_S1; try exact AEU; [unguardH LEN; des; lia|i]. 
  exploit lastn_S1; try exact COV; [unguardH LEN; des; lia|i]. 
  exploit lastn_S1; try exact VEXT; [unguardH LEN; des; lia|i].
  subst. exploit sim_trace_lastn; eauto. instantiate (1 := n). i.
  exploit sim_trace_last; eauto. i. des.
  exploit IHn; try exact HDTR; eauto; [lia|]. i.
  eapply sim_traces_sim_th'_step; eauto.
  - rewrite EU, HDTR. ss.
  - rewrite AEU, HDATR. ss.
  - rewrite COV, HDCOVL. ss.
  - rewrite VEXT, HDVEXTL. ss.
Admitted.

Lemma sim_traces_vext_valid
      p mem trs atrs ws rs covs vexts
      m ex
      (SIM: sim_traces p mem trs atrs ws rs covs vexts)
      (NOPROMISE: Machine.no_promise m)
      (PRE: Valid.pre_ex p ex)
      (CO: ex.(Execution.co) = co_gen ws)
      (RF: ex.(Execution.rf) = rf_gen ws rs)
      (CO1: Valid.co1 ex)
      (CO2: Valid.co2 ex)
      (RF1: Valid.rf1 ex)
      (RF2: Valid.rf2 ex)
      (RF_WF: Valid.rf_wf ex)
      (TR: IdMap.Forall2
             (fun _ tr sl => exists l, tr = (ExecUnit.mk sl.(fst) sl.(snd) mem) :: l)
             trs m.(Machine.tpool))
      (ATR: IdMap.Forall2
              (fun _ atr aeu => exists l, atr = aeu :: l)
              atrs (Valid.aeus PRE)):
  <<FR:
    forall eid1 eid2
      (FR: ex.(Execution.fr) eid1 eid2),
      Time.lt ((v_gen vexts) eid1) ((v_gen vexts) eid2)>> /\
  <<OB_WRITE:
    forall eid1 eid2
      (OB: ex.(ob') eid1 eid2)
      (EID2: ex.(Execution.label_is) Label.is_write eid2),
      Time.lt ((v_gen vexts) eid1) ((v_gen vexts) eid2)>> /\
  <<OB_READ:
    forall eid1 eid2
      (OB: ex.(ob') eid1 eid2)
      (EID2: ex.(Execution.label_is) Label.is_read eid2),
      Time.le ((v_gen vexts) eid1) ((v_gen vexts) eid2)>> /\
  <<ATOMIC:
    forall eid1 eid2 eid
      (ATOMIC: ex.(Execution.rmw) eid1 eid2)
      (FRE: ex.(Execution.fre) eid1 eid)
      (COE: ex.(Execution.coe) eid eid2),
      False>>.
Proof.
Admitted.

Lemma sim_traces_valid
      p trs atrs ws rs covs vexts
      m ex
      (STEP: Machine.pf_exec p m)
      (SIM: sim_traces p m.(Machine.mem) trs atrs ws rs covs vexts)
      (PRE: Valid.pre_ex p ex)
      (CO: ex.(Execution.co) = co_gen ws)
      (RF: ex.(Execution.rf) = rf_gen ws rs)
      (CO1: Valid.co1 ex)
      (CO2: Valid.co2 ex)
      (RF1: Valid.rf1 ex)
      (RF2: Valid.rf2 ex)
      (RF_WF: Valid.rf_wf ex)
      (TR: IdMap.Forall2
             (fun _ tr sl => exists l, tr = (ExecUnit.mk sl.(fst) sl.(snd) m.(Machine.mem)) :: l)
             trs m.(Machine.tpool))
      (ATR: IdMap.Forall2
              (fun _ atr aeu => exists l, atr = aeu :: l)
              atrs (Valid.aeus PRE)):
  <<INTERNAL:
    forall eid1 eid2
      (INTERNAL: ex.(Execution.internal) eid1 eid2),
      (Time.lt ((v_gen covs) eid1) ((v_gen covs) eid2) /\ ex.(Execution.label_is) Label.is_write eid2) \/
      (Time.le ((v_gen covs) eid1) ((v_gen covs) eid2) /\ ex.(Execution.label_is) Label.is_read eid2)>> /\
  <<EXTERNAL:
    forall eid1 eid2
      (OB: ex.(Execution.ob) eid1 eid2)
      (LABEL1: Execution.label_is ex Label.is_access eid1)
      (LABEL2: Execution.label_is ex Label.is_access eid2),
      (Time.lt ((v_gen vexts) eid1) ((v_gen vexts) eid2) /\ ex.(Execution.label_is) Label.is_write eid2) \/
      (Time.le ((v_gen vexts) eid1) ((v_gen vexts) eid2) /\ ex.(Execution.label_is) Label.is_read eid2)>> /\
  <<ATOMIC: le (ex.(Execution.rmw) ∩ (ex.(Execution.fre) ⨾ ex.(Execution.coe))) bot>>.
Proof.
  generalize STEP. intro X. inv X. splits.
  - ii. exploit Valid.internal_rw; eauto. i. des.
    inv EID2. destruct l; ss.
    + right. des_union.
      * exploit sim_traces_cov_po_loc; eauto. i. des.
        exploit PO_LOC_READ; eauto.
      * exploit sim_traces_cov_fr; eauto. i.
        split; eauto using Nat.lt_le_incl.
      * exploit sim_traces_cov_co; eauto. i.
        split; eauto using Nat.lt_le_incl.
      * exploit sim_traces_cov_rf; eauto. i.
        split; eauto. rewrite x0. auto.
    + left. des_union.
      * exploit sim_traces_cov_po_loc; eauto. i. des.
        exploit PO_LOC_WRITE; eauto.
      * exploit sim_traces_cov_fr; eauto.
      * exploit sim_traces_cov_co; eauto.
      * exploit RF2; eauto. i. des. congr.
  - exploit sim_traces_vext_valid; eauto. i. des.
    inv LABEL2. destruct l; ss.
    + right. rewrite ob_ob' in OB. des_union.
      * exploit FR; eauto. i.
        split; eauto using Nat.lt_le_incl.
      * exploit sim_traces_vext_co; eauto. i.
        split; eauto using Nat.lt_le_incl.
      * exploit OB_READ; eauto.
    + left. rewrite ob_ob' in OB. des_union.
      * exploit FR; eauto.
      * exploit sim_traces_vext_co; eauto.
      * exploit OB_WRITE; eauto.
  - exploit sim_traces_vext_valid; eauto. i. des.
    ii. inv H. inv H1. des. exfalso. eauto.
Qed.

Lemma internal_acyclic
      ex cov
      (INTERNAL: forall eid1 eid2 (INTERNAL: ex.(Execution.internal)⁺ eid1 eid2),
          Time.lt (cov eid1) (cov eid2) \/
          (Time.le (cov eid1) (cov eid2) /\
           Execution.po eid1 eid2 /\
           ex.(Execution.label_is) Label.is_read eid1 /\
           ex.(Execution.label_is) Label.is_read eid2) \/
          (Time.le (cov eid1) (cov eid2) /\
           ex.(Execution.label_is) Label.is_write eid1 /\
           ex.(Execution.label_is) Label.is_read eid2)):
  acyclic ex.(Execution.internal).
Proof.
  ii. exploit INTERNAL; eauto. i. des.
  - inv x0; lia.
  - inv x1. lia.
  - inv x1. inv x2. rewrite EID in EID0. inv EID0. destruct l0; ss; congr.
Qed.

Lemma promising_pf_valid
      p m
      (STEP: Machine.pf_exec p m):
  exists ex (PRE: Valid.pre_ex p ex) (cov: forall (eid: eidT), Time.t) (vext: forall (eid: eidT), Time.t),
    <<CO1: Valid.co1 ex>> /\
    <<CO2: Valid.co2 ex>> /\
    <<RF1: Valid.rf1 ex>> /\
    <<RF2: Valid.rf2 ex>> /\
    <<RF_WF: Valid.rf_wf ex>> /\
    <<INTERNAL:
      forall eid1 eid2
        (INTERNAL: ex.(Execution.internal)⁺ eid1 eid2),
        Time.lt (cov eid1) (cov eid2) \/
        (Time.le (cov eid1) (cov eid2) /\
         Execution.po eid1 eid2 /\
         ex.(Execution.label_is) Label.is_read eid1 /\
         ex.(Execution.label_is) Label.is_read eid2) \/
        (Time.le (cov eid1) (cov eid2) /\
         ex.(Execution.label_is) Label.is_write eid1 /\
         ex.(Execution.label_is) Label.is_read eid2)>> /\
    <<EXTERNAL:
      forall eid1 eid2
        (OB: (ex.(Execution.ob) ∩ (ex.(Execution.label_is_rel) Label.is_access))⁺ eid1 eid2),
        Time.lt (vext eid1) (vext eid2) \/
        (Time.le (vext eid1) (vext eid2) /\
         Execution.po eid1 eid2 /\
         ex.(Execution.label_is) Label.is_read eid1 /\
         ex.(Execution.label_is) Label.is_read eid2) \/
        (Time.le (vext eid1) (vext eid2) /\
         ex.(Execution.label_is) Label.is_write eid1 /\
         ex.(Execution.label_is) Label.is_read eid2)>> /\
    <<ATOMIC: le (ex.(Execution.rmw) ∩ (ex.(Execution.fre) ⨾ ex.(Execution.coe))) bot>> /\
    <<STATE: IdMap.Forall2
               (fun tid sl aeu => sim_state_weak sl.(fst) aeu.(AExecUnit.state))
               m.(Machine.tpool) PRE.(Valid.aeus)>>.
Proof.
  exploit promising_pf_sim_traces; eauto. i. des.
  destruct PRE, ex. ss.
  remember (Execution.mk labels addr data ctrl rmw (co_gen ws) (rf_gen ws rs)) as ex'.
  replace labels with ex'.(Execution.labels) in LABELS; [|subst; ss].
  replace addr with ex'.(Execution.addr) in ADDR; [|subst; ss].
  replace data with ex'.(Execution.data) in DATA; [|subst; ss].
  replace ctrl with ex'.(Execution.ctrl) in CTRL; [|subst; ss].
  replace rmw with ex'.(Execution.rmw) in RMW; [|subst; ss].
  remember (@Valid.mk_pre_ex p ex' aeus AEUS LABELS ADDR DATA CTRL RMW) as PRE'.
  replace aeus with PRE'.(Valid.aeus) in ATR; [|subst; ss].
  exists ex'. exists PRE'. exists (v_gen covs). exists (v_gen vexts).
  generalize STEP. intro X. inversion X.
  generalize (sim_traces_co1 PRE' SIM ATR). intro CO1.
  generalize (sim_traces_co2 PRE' SIM ATR). intro CO2.
  generalize (sim_traces_rf1 STEP PRE' NOPROMISE SIM TR ATR). intro RF1.
  generalize (sim_traces_rf2 PRE' SIM ATR). intro RF2.
  generalize (sim_traces_rf_wf SIM). intro RF_WF.
  replace (co_gen ws) with (ex'.(Execution.co)) in CO1, CO2;[|subst; ss].
  replace (rf_gen ws rs) with (ex'.(Execution.rf)) in RF1, RF2, RF_WF; [|subst; ss].
  exploit sim_traces_valid; eauto; try by (subst; ss). i. des.
  assert (INTERNAL': forall eid1 eid2 (INTERNAL: ex'.(Execution.internal)⁺ eid1 eid2),
             Time.lt (v_gen covs eid1) (v_gen covs eid2) \/
             (Time.le (v_gen covs eid1) (v_gen covs eid2) /\
              Execution.po eid1 eid2 /\
              ex'.(Execution.label_is) Label.is_read eid1 /\
              ex'.(Execution.label_is) Label.is_read eid2) \/
             (Time.le (v_gen covs eid1) (v_gen covs eid2) /\
              ex'.(Execution.label_is) Label.is_write eid1 /\
              ex'.(Execution.label_is) Label.is_read eid2)).
  { i. induction INTERNAL0.
    + exploit INTERNAL; eauto. i. des; eauto.
      { exploit Valid.internal_rw; eauto. i. des.
        inversion EID1. inversion EID2.
        destruct l0; ss.
        - destruct l; ss.
          + exploit Valid.internal_read_read_po; eauto. i.
            right. left. splits; eauto.
          + right. right. split; eauto.
        - inversion x1. rewrite EID0 in EID3. inversion EID3.
          rewrite H1 in *. destruct l0; ss; congr. }
    + des.
      * left. etrans; eauto.
      * left. eapply le_lt_trans; eauto.
      * left. eapply le_lt_trans; eauto.
      * left. eapply lt_le_trans; eauto.
      * right. left. splits; try etrans; eauto.
      * right. right. splits; try etrans; eauto.
      * left. eapply lt_le_trans; eauto.
      * inversion IHINTERNAL0_6. inversion IHINTERNAL0_0.
        rewrite EID in EID0. inversion EID0. rewrite H0 in *.
        destruct l0; ss; congr.
      * inversion IHINTERNAL0_5. inversion IHINTERNAL0_0.
        rewrite EID in EID0. inversion EID0. rewrite H0 in *.
        destruct l0; ss; congr. }
  esplits; eauto.
  - generalize (internal_acyclic _ INTERNAL'). intro ACYCLIC.
    clear INTERNAL'. i. induction OB.
    + inversion H. inversion H1.
      exploit EXTERNAL; eauto. i. des; eauto.
      { destruct l1.
        - exploit Valid.ob_read_read_po; eauto. i.
          right. left. splits; eauto.
        - right. right. splits; eauto.
        - inv LABEL1.
        - inv LABEL1.
}
    + des.
      * left. etrans; eauto.
      * left. eapply le_lt_trans; eauto.
      * left. eapply le_lt_trans; eauto.
      * left. eapply lt_le_trans; eauto.
      * right. left. splits; try etrans; eauto.
      * right. right. splits; try etrans; eauto.
      * left. eapply lt_le_trans; eauto.
      * inversion IHOB6. inversion IHOB0. rewrite EID in EID0.
        inversion EID0. rewrite H0 in *. ss. destruct l0; ss; congr.
      * inversion IHOB5. inversion IHOB0. rewrite EID in EID0.
        inversion EID0. rewrite H0 in *. ss. destruct l0; ss; congr.
  - clear - SIM TR ATR.
    ii. generalize (SIM id). i. inv H; ss.
    + generalize (TR id). i. inv H; try congr.
      generalize (ATR id). i. inv H; try congr.
      econs.
    + generalize (TR id). i. inv H; try congr.
      generalize (ATR id). i. inv H; try congr.
      des. simplify. inv REL6; auto.
      { econs. unfold Machine.init_with_promises in *. ss.
        rewrite IdMap.mapi_spec in *. rewrite STMT in FIND. ss.
        symmetry in FIND. inv FIND. rewrite H0.
        apply sim_state_weak_init. }
Qed.

Theorem promising_pf_to_axiomatic
        p m
        (STEP: Machine.pf_exec p m):
  exists ex (EX: Valid.ex p ex),
    <<TERMINAL: Machine.is_terminal m -> EX.(Valid.is_terminal)>> /\
    <<STATE: IdMap.Forall2
               (fun tid sl aeu => sim_state_weak sl.(fst) aeu.(AExecUnit.state))
               m.(Machine.tpool) EX.(Valid.aeus)>>.
Proof.
  exploit promising_pf_valid; eauto. i. des.
  exists ex. eexists (Valid.mk_ex PRE CO1 CO2 RF1 RF2 RF_WF _ _ ATOMIC).
  s. esplits; eauto.
  ii. inv H. specialize (STATE tid). inv STATE; try congr.
  rewrite FIND in H. inv H. destruct a. destruct aeu. ss.
  exploit TERMINAL; eauto. i. des. inv REL. inv x. congr.
Grab Existential Variables.
{ (* external *)
  ii. exploit Valid.ob_cycle; eauto. i. des. rename x1 into NONBARRIER.
  clear - EXTERNAL NONBARRIER.
  exploit EXTERNAL; eauto. i. des.
  - inv x; lia.
  - inv x0. lia.
  - inv x0. inv x1. rewrite EID in EID0. inv EID0. destruct l0; ss; congr.
}
{ (* internal *)
  clear - INTERNAL.
  eapply internal_acyclic. auto.
}
Qed.
