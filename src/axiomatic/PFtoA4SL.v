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

Set Implicit Arguments.


Lemma sim_traces_sim_th'_sl
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
  forall tid tr atr wl rl covl vextl
    n eu1 eu2 tr' aeu1 aeu2 atr' w1 w2 wl' r1 r2 rl' cov1 cov2 covl' vext1 vext2 vextl'
    (FIND_TR: IdMap.find tid trs = Some tr)
    (FIND_ATR: IdMap.find tid atrs = Some atr)
    (FIND_WL: IdMap.find tid ws = Some wl)
    (FIND_RL: IdMap.find tid rs = Some rl)
    (FIND_COVL: IdMap.find tid covs = Some covl)
    (FIND_VEXTL: IdMap.find tid vexts = Some vextl)
    (EU: lastn (S n) tr = eu2 :: eu1 :: tr')
    (AEU: lastn (S n) atr = aeu2 :: aeu1 :: atr')
    (WL: lastn (S n) wl = w2 :: w1 :: wl')
    (RL: lastn (S n) rl = r2 :: r1 :: rl')
    (COV: lastn (S n) covl = cov2 :: cov1 :: covl')
    (VEXT: lastn (S n) vextl = vext2 :: vext1 :: vextl')
    (SIM_TH': sim_th' tid ex (v_gen vexts) eu1 aeu1),
    sim_state tid (v_gen vexts) eu2.(ExecUnit.state) aeu2.(AExecUnit.state) /\
    sim_local tid ex (v_gen vexts) eu2.(ExecUnit.local) aeu2.(AExecUnit.local).
Proof.
  i. rename SIM_TH' into L.
  generalize (SIM tid). intro X. inv X; simplify.
  destruct n.
  { generalize (lastn_length 1 tr). rewrite EU. destruct tr; ss. }
  exploit sim_trace_lastn; eauto. instantiate (1 := S n). intro SIMTR.
  hexploit sim_traces_ex; eauto. intro EX2.
  inversion SIMTR; subst; simplify; [congr|].
  repeat match goal with
         | [H1: lastn ?a ?b = ?c, H2: ?d = lastn ?a ?b |- _] =>
           rewrite H1 in H2; inv H2
         end.
  exploit sim_trace_sim_state_weak; eauto. intro STATE1.

  destruct eu1 as [[stmts1 rmap1] lc1 mem1].
  destruct eu2 as [[stmts2 rmap2] lc2 mem2].
  destruct aeu1 as [[astmts1 armap1] alc1].
  destruct aeu2 as [[astmts2 armap2] alc2].
  ss. inv STEP0. ss. subst.
  inv STATE. inv STATE1. ss. subst.
  inv STATE0; inv LOCAL0; ss; inv EVENT0; inv EVENT; ss.
  - (* skip *)
    inv ASTATE_STEP; inv ALOCAL_STEP; ss; inv EVENT; ss. splits.
    + econs; ss. apply L.
    + econs; ss; try by apply L.
  - (* assign *)
    inv ASTATE_STEP; inv ALOCAL_STEP; ss; inv EVENT; ss. splits.
    + econs; ss. apply sim_rmap_add; try by apply L.
      apply sim_rmap_expr. apply L.
    + econs; ss; try by apply L.
  - (* read *)
    inv STEP0. inv ASTATE_STEP; inv ALOCAL_STEP; ss; inv EVENT; ss. splits.
    { econs; ss. apply sim_rmap_add; try apply L.
      inv VAL. ss. subst. econs; ss.
      ii. des. destruct eid. ss. subst.
      rewrite EX2.(XVEXT); cycle 1.
      { ss. rewrite List.app_length. ss. unfold ALocal.next_eid. clear. lia. }
      destruct (ALocal.next_eid alc1 =? ALocal.next_eid alc1) eqn:Heq; ss.
      rewrite Nat.eqb_neq in Heq. ss. }
    destruct L.(LC). ss. econs; ss.
    all: try rewrite List.app_length, Nat.add_1_r.
    + i. rewrite sim_local_coh_step. rewrite inverse_step.
      rewrite inverse_union. rewrite fun_add_spec. condtac.
      { ii. des.
        - inv EID. etrans; eauto. rewrite <- e. apply COH0; eauto.
        - inv EID. inv REL. des. inv H. inv H2.
          apply Label.is_writing_inv in LABEL. des. subst. inv H0; cycle 1.
          + inv H. exploit RF2; eauto. i. des.
            destruct x as [tid1 eid1]. ss.
            unfold Execution.label in WRITE. ss.
            rewrite PRE.(Valid.LABELS) in WRITE.
            rewrite IdMap.map_spec in WRITE.
            destruct (IdMap.find tid1 (Valid.aeus PRE)) eqn:FIND1; ss.
            generalize (ATR tid1). intro ATR1. inv ATR1; try congr. des. simplify.
            generalize (SIM tid1). intro SIM1. inv SIM1; simplify.
            exploit sim_trace_last; try exact REL0. i. des. simplify.
            exploit sim_trace_sim_th; try exact REL0; eauto. intro L1.
            rewrite RF in H0. inv H0. ss. simplify.
            exploit WPROP3; eauto. i. des. simplify.
            unfold v_gen. ss. rewrite <- H8. rewrite x2.
            assert (ts = ts2).
            { exploit EX2.(XR); eauto.
              - instantiate (1 := ALocal.next_eid alc1).
                ss. rewrite List.app_length. ss. unfold ALocal.next_eid. clear. lia.
              - destruct (ALocal.next_eid alc1 =? ALocal.next_eid alc1) eqn:Heq; cycle 1.
                { rewrite Nat.eqb_neq in Heq. ss. }
                rewrite fun_add_spec.
                destruct (equiv_dec (ValA.val (sem_expr rmap1 eloc)) (ValA.val (sem_expr rmap1 eloc))) eqn:Heq1; cycle 1.
                { exfalso. apply c. ss. }
                i. unfold ALocal.next_eid in *.
                rewrite R in x6. inv x6. ss. }
            subst. ss.
          + exploit EX2.(LABELS); eauto; ss.
            { rewrite List.app_length. s. lia. }
            rewrite List.nth_error_app2, Nat.sub_diag; ss.
      }
      ii. des; [apply COH0|]; eauto.
      inv EID. inv REL. inv H. inv H0. inv H2.
      apply Label.is_writing_inv in LABEL. des. subst. inv H1.
      * exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
      * inv H. exploit RF2; eauto. i. des.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x1.
        rewrite EID in WRITE. inv WRITE. inv VLOC. congr.
    + i. rewrite sim_local_vrn_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VRN; eauto. i. rewrite <- join_l. ss.
      * inv EID. inv REL. inv H. inv H1. inv H. inv H2. inv H3.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x1. inv LABEL. }
      * inv EID. inv REL. inv H. inv H1. inv H. inv H2. inv H3.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x1. inv LABEL. }
      * inv EID. inv REL. inv H. inv H1. inv H2.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. }
      * inv EID. inv REL. inv H0. destruct l; ss.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0.
        rewrite LABEL. s. rewrite <- join_r.
        rewrite EX2.(XVEXT); cycle 1.
        { ss. rewrite List.app_length. ss. unfold ALocal.next_eid. clear. lia. }
        destruct (length (ALocal.labels alc1) =? ALocal.next_eid alc1) eqn:Heq; ss.
        rewrite Nat.eqb_neq in Heq. ss.
    + i. rewrite sim_local_vwn_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VWN; eauto. i. rewrite <- join_l. ss.
      * inv EID. inv REL. inv H. inv H1. inv H. inv H2. inv H3.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x1. inv LABEL. }
      * inv EID. inv REL. inv H. inv H1. inv H. inv H2. inv H3.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x1. inv LABEL. }
      * inv EID. inv REL. inv H0. destruct l; ss.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0.
        rewrite LABEL. s. rewrite <- join_r.
        rewrite EX2.(XVEXT); cycle 1.
        { ss. rewrite List.app_length. ss. unfold ALocal.next_eid. clear. lia. }
        destruct (length (ALocal.labels alc1) =? ALocal.next_eid alc1) eqn:Heq; ss.
        rewrite Nat.eqb_neq in Heq. ss.
    + i. rewrite sim_local_vro_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VRO; eauto. i. rewrite <- join_l. ss.
      * inv EID. inv REL. inv H0. destruct l; ss.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0.
        rewrite <- join_r.
        rewrite EX2.(XVEXT); cycle 1.
        { ss. rewrite List.app_length. ss. unfold ALocal.next_eid. clear. lia. }
        destruct (length (ALocal.labels alc1) =? ALocal.next_eid alc1) eqn:Heq; ss.
        rewrite Nat.eqb_neq in Heq. ss.
    + i. rewrite sim_local_vwo_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VWO; eauto.
      * inv EID. inv REL. inv H0. destruct l; ss.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
    + i. rewrite sim_local_vcap_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VCAP; eauto. i. rewrite <- join_l. ss.
      * inv EID.
        exploit EX2.(LABELS_REV); ss.
        { apply nth_error_last. apply Nat.eqb_eq. ss. }
        intro X. exploit Valid.ctrl_label; eauto. i. des.
        inv EID2. rewrite X in EID. inv EID. ss.
      * (* sim addr *)
        inv EID. rewrite <- join_r.
        destruct eid as [tid1 eid1]. exploit Valid.addr_is_po; eauto. intro X. inv X. ss. subst.
        exploit EX2.(ADDR); eauto; ss.
        { rewrite List.app_length. s. clear. lia. }
        intro X. inv X.
        { exploit sim_trace_sim_th; try exact TRACE; eauto. intro M.
          destruct M.(AEU_WF). ss. exploit ADDR_LIMIT; eauto. clear. lia.
        }
        inv H. eapply sim_rmap_expr; eauto. apply L.
    + i. rewrite sim_local_vrel_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VREL; eauto.
      * inv EID. inv REL. inv H0. destruct l; ss.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. }
    + i. specialize (FWDBANK loc). des.
      * left. esplits; eauto.
        rewrite sim_local_fwd_step. econs.
        econs; cycle 1.
        { instantiate (1 := (_, _)). econs; ss. }
        left. econs. split; eauto. econs; ss.
        exploit EX2.(LABELS_REV); ss.
        { apply nth_error_last. apply Nat.eqb_eq. ss. }
        i. econs; eauto.
      * right. esplits; eauto.
        i. specialize (FWDBANK0 eid).
        rewrite sim_local_fwd_none_step. rewrite inverse_step.
        ii. inv H. inv REL.
        { apply FWDBANK0. econs; eauto. }
        { inv H. inv H1. exploit EX2.(LABELS); eauto; ss.
          { rewrite List.app_length. s. lia. }
          rewrite List.nth_error_app2, Nat.sub_diag; ss.
          destruct l; ss. }
    + destruct ex0; ss. econs. s. splits.
      * exploit EX2.(LABELS_REV); ss.
        { apply nth_error_last. apply Nat.eqb_eq. ss. }
        i. econs; eauto. inv VLOC. rewrite VAL0. apply Label.read_is_reading.
      * econs.
        { ii. inv EID. destruct eid as (tid1, eid1).
          rewrite RF in REL. inv REL. ss.
          generalize (SIM tid1). intro SIM1. inv SIM1; simplify.
          exploit sim_trace_last; try exact REL0. i. des. simplify.
          exploit sim_trace_sim_th; try exact REL0; eauto. intro L1.
          exploit L1.(WPROP3); eauto. i. des.
          unfold v_gen. ss. rewrite <- H5. rewrite x2.
          assert (ts = ts2).
          { exploit EX2.(XR); eauto.
            - instantiate (1 := ALocal.next_eid alc1).
              ss. rewrite List.app_length. ss. unfold ALocal.next_eid. clear. lia.
            - destruct (ALocal.next_eid alc1 =? ALocal.next_eid alc1) eqn:Heq; cycle 1.
              { rewrite Nat.eqb_neq in Heq. ss. }
              rewrite fun_add_spec.
              destruct (equiv_dec (ValA.val (sem_expr rmap1 eloc)) (ValA.val (sem_expr rmap1 eloc))) eqn:Heq1; cycle 1.
              { exfalso. apply c. ss. }
              i. unfold ALocal.next_eid in *.
              rewrite R in x6. inv x6. ss. }
          subst. ss. }
        { exploit sim_trace_sim_th; try exact SIMTR; eauto. intro L2. ss.
          exploit (L2.(RPROP2) (ALocal.next_eid alc1)); ss.
          { destruct (ALocal.next_eid alc1 =? ALocal.next_eid alc1) eqn:Heq; ss.
            rewrite Nat.eqb_neq in Heq. ss. }
          destruct (ALocal.next_eid alc1 =? ALocal.next_eid alc1) eqn:Heq; cycle 1.
          { rewrite Nat.eqb_neq in Heq. ss. }
          rewrite fun_add_spec.
          destruct (equiv_dec (ValA.val (sem_expr rmap1 eloc)) (ValA.val (sem_expr rmap1 eloc))) eqn:Heq1; cycle 1.
          { exfalso. apply c. ss. }
          i. des. unguardH x3.  des.
          - rewrite x3. econs 1. ss.
          - exploit sim_traces_memory; eauto. i. des.
            generalize (SIM tid'). intro SIM'. inv SIM'; simplify.
            exploit sim_trace_last; try exact REL0. i. des. simplify.
            exploit sim_trace_sim_th; try exact REL0; eauto. intro L'.
            exploit L'.(WPROP1); eauto. i. des.
            { generalize (TR tid'). intro TR'. inv TR'; try congr. des. simplify.
              inv STEP. inv NOPROMISE. destruct b0.
              exploit (PROMISES0 tid').
              { rewrite <- H6. refl. }
              i. ss. rewrite x7 in x5.
              rewrite Promises.lookup_bot in x5. inv x5. }
            econs 2.
            { instantiate (1 := (tid', eid)). subst.
              econs; eauto. rewrite RF.
              exploit sim_trace_last; try exact REL6. i. des. subst.
              econs; cycle 1; eauto; ss.
              exploit EX2.(XR); eauto.
              - instantiate (1 := ALocal.next_eid alc1).
                ss. rewrite List.app_length. ss. unfold ALocal.next_eid. clear. lia.
              - destruct (ALocal.next_eid alc1 =? ALocal.next_eid alc1) eqn:Heq2; cycle 1.
                { rewrite Nat.eqb_neq in Heq2. ss. }
                rewrite fun_add_spec.
                destruct (equiv_dec (ValA.val (sem_expr rmap1 eloc)) (ValA.val (sem_expr rmap1 eloc))) eqn:Heq3; cycle 1.
                { exfalso. apply c. ss. }
                i. ss. }
            exploit L'.(WPROP3); eauto. i. des.
            subst. unfold v_gen. ss. rewrite <- H5. rewrite x10. ss.
        }
      * ii. subst. erewrite EX2.(XVEXT); eauto; cycle 1.
        { s. rewrite List.app_length. s. unfold ALocal.next_eid. clear. lia. }
        des_ifs. apply Nat.eqb_neq in Heq. clear -Heq. lia.
    + i. exploit PROMISES; eauto. i. des. esplits; cycle 1; eauto.
      inv N.
      * inv WRITE. exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
        destruct l; ss.
      * clear -H. lia.
  - (* write *)
    inv STEP0. inv ASTATE_STEP; inv ALOCAL_STEP; ss; inv EVENT; inv RES; ss. splits.
    { econs; ss. apply sim_rmap_add; try apply L.
      econs; ss. unfold ifc. condtac; cycle 1.
      { ii. des. inv EID0. }
      ii. des. destruct eid as [tid1 eid1]. ss. subst.
      rewrite EX2.(XVEXT); cycle 1.
      { ss. rewrite List.app_length. ss. unfold ALocal.next_eid. clear. lia. }
      destruct (ALocal.next_eid alc1 =? ALocal.next_eid alc1) eqn:Heq; ss.
      - rewrite fun_add_spec.
        destruct (equiv_dec (ValA.val (sem_expr rmap1 eloc)) (ValA.val (sem_expr rmap1 eloc))) eqn:Heq1; ss.
        exfalso. apply c. ss.
      - rewrite Nat.eqb_neq in Heq. ss. }
    destruct L.(LC). ss. econs; ss.
    all: try rewrite List.app_length, Nat.add_1_r.
    + i. rewrite sim_local_coh_step. rewrite inverse_step.
      rewrite inverse_union. rewrite fun_add_spec. condtac.
      { ii. des.
        - inv EID. inv WRITABLE. ss. apply Nat.lt_le_incl.
          eapply Nat.le_lt_trans; try eapply COH0. rewrite <- e.
          apply COH; eauto.
        - inv EID. inv REL. des. inv H. inv H2.
          apply Label.is_writing_inv in LABEL. des. subst. inv H0; cycle 1.
          + inv H. exploit RF2; eauto. i. des.
            exploit EX2.(LABELS); eauto; ss.
            { rewrite List.app_length. s. lia. }
            rewrite List.nth_error_app2, Nat.sub_diag; ss.
          + exploit EX2.(LABELS); eauto; ss.
            { rewrite List.app_length. s. lia. }
            rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0.
            rewrite EX2.(XVEXT); cycle 1.
            { ss. rewrite List.app_length. ss. clear. lia. }
            destruct (length (ALocal.labels alc1) =? ALocal.next_eid alc1) eqn:Heq; cycle 1.
            { rewrite Nat.eqb_neq in Heq. unfold ALocal.next_eid in Heq. ss. }
            rewrite fun_add_spec.
            destruct (equiv_dec (ValA.val (sem_expr rmap1 eloc)) (ValA.val (sem_expr rmap1 eloc))) eqn:Heq1; ss.
            exfalso. apply c. ss.
      }
      ii. des; [apply COH|]; eauto.
      inv EID. inv REL. inv H. inv H0. inv H2.
      apply Label.is_writing_inv in LABEL. des. subst. inv H1.
      * exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0.
        inv VLOC. congr.
      * inv H. exploit RF2; eauto. i. des.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
    + i. rewrite sim_local_vrn_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VRN; eauto.
      * inv EID. inv REL. inv H. inv H1. inv H. inv H2. inv H3.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x1. inv LABEL. }
      * inv EID. inv REL. inv H. inv H1. inv H. inv H2. inv H3.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x1. inv LABEL. }
      * inv EID. inv REL. inv H. inv H1. inv H2.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. }
      * inv EID. inv REL. inv H0. destruct l; ss.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
    + i. rewrite sim_local_vwn_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VWN; eauto.
      * inv EID. inv REL. inv H. inv H1. inv H. inv H2. inv H3.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x1. inv LABEL. }
      * inv EID. inv REL. inv H. inv H1. inv H. inv H2. inv H3.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x1. inv LABEL. }
      * inv EID. inv REL. inv H0. destruct l; ss.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
    + i. rewrite sim_local_vro_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VRO; eauto.
      * inv EID. inv REL. inv H0. destruct l; ss.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
    + i. rewrite sim_local_vwo_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VWO; eauto. i. rewrite <- join_l. ss.
      * inv EID. inv REL. inv H0. destruct l; ss.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0.
        rewrite <- join_r.
        rewrite EX2.(XVEXT); cycle 1.
        { ss. rewrite List.app_length. ss. clear. lia. }
        destruct (length (ALocal.labels alc1) =? ALocal.next_eid alc1) eqn:Heq; cycle 1.
        { rewrite Nat.eqb_neq in Heq. unfold ALocal.next_eid in Heq. ss. }
        rewrite fun_add_spec.
        destruct (equiv_dec (ValA.val (sem_expr rmap1 eloc)) (ValA.val (sem_expr rmap1 eloc))) eqn:Heq1; ss.
        exfalso. apply c. ss.
    + i. rewrite sim_local_vcap_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VCAP; eauto. i. rewrite <- join_l. ss.
      * inv EID.
        exploit EX2.(LABELS_REV); ss.
        { apply nth_error_last. apply Nat.eqb_eq. ss. }
        intro X. exploit Valid.ctrl_label; eauto. i. des.
        inv EID2. rewrite X in EID. inv EID. ss.
      * (* sim addr *)
        inv EID. rewrite <- join_r.
        destruct eid as [tid1 eid1]. exploit Valid.addr_is_po; eauto. intro X. inv X. ss. subst.
        exploit EX2.(ADDR); eauto; ss.
        { rewrite List.app_length. s. clear. lia. }
        intro X. inv X.
        { exploit sim_trace_sim_th; try exact TRACE; eauto. intro M.
          destruct M.(AEU_WF). ss. exploit ADDR_LIMIT; eauto. clear. lia.
        }
        inv H. eapply sim_rmap_expr; eauto. apply L.
    + i. rewrite sim_local_vrel_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VREL; eauto. i. rewrite <- join_l. ss.
      * inv EID. inv REL. inv H0. destruct l; ss.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0.
        rewrite LABEL. s. rewrite <- join_r.
        rewrite EX2.(XVEXT); cycle 1.
        { ss. rewrite List.app_length. ss. clear. lia. }
        destruct (length (ALocal.labels alc1) =? ALocal.next_eid alc1) eqn:Heq; cycle 1.
        { rewrite Nat.eqb_neq in Heq. unfold ALocal.next_eid in Heq. ss. }
        rewrite fun_add_spec.
        destruct (equiv_dec (ValA.val (sem_expr rmap1 eloc)) (ValA.val (sem_expr rmap1 eloc))) eqn:Heq1; ss.
        exfalso. apply c. ss.
    + i. rewrite fun_add_spec. condtac; s.
      { inversion e. subst. left. esplits; eauto.
        - destruct ts; ss. clear. lia.
        - instantiate (1 := (tid, length (ALocal.labels alc1))). econs.
          + econs; ss.
          + exploit EX2.(LABELS_REV); ss.
            { apply nth_error_last. apply Nat.eqb_eq. ss. }
            i. econs; eauto. inv VLOC. rewrite VAL0. apply Label.write_is_writing.
          + i. inv PO. inv PO0. ss. subst. clear -N N0. lia.
        - rewrite EX2.(XVEXT); cycle 1.
          { ss. rewrite List.app_length. ss. clear. lia. }
          destruct (length (ALocal.labels alc1) =? ALocal.next_eid alc1) eqn:Heq; cycle 1.
          { rewrite Nat.eqb_neq in Heq. unfold ALocal.next_eid in Heq. ss. }
          rewrite fun_add_spec.
          destruct (equiv_dec (ValA.val (sem_expr rmap1 eloc)) (ValA.val (sem_expr rmap1 eloc))) eqn:Heq1; ss.
        - ii. inv EID. inv REL.
          + (* sim addr *)
            rewrite <- join_l.
            destruct eid as [tid1 eid1]. exploit Valid.addr_is_po; eauto. intro Y. inv Y. ss. subst.
            exploit EX2.(ADDR); eauto; ss.
            { rewrite List.app_length. s. clear. lia. }
            intro Y. inv Y.
            { exploit sim_trace_sim_th; try exact TRACE; eauto. intro M.
              destruct M.(AEU_WF). ss. exploit ADDR_LIMIT; eauto. clear. lia.
            }
            inv H0. eapply sim_rmap_expr; eauto. apply L.
          + (* sim data *)
            rewrite <- join_r.
            destruct eid as [tid1 eid1]. exploit Valid.data_is_po; eauto. intro Y. inv Y. ss. subst.
            exploit EX2.(DATA); eauto; ss.
            { rewrite List.app_length. s. clear. lia. }
            intro Y. inv Y.
            { exploit sim_trace_sim_th; try exact TRACE; eauto. intro M.
              destruct M.(AEU_WF). ss. exploit DATA_LIMIT; eauto. clear. lia.
            }
            inv H0. eapply sim_rmap_expr; eauto. apply L.
        - destruct ex0; econs; i; ss.
          + exploit EX2.(LABELS_REV); ss.
            { apply nth_error_last. apply Nat.eqb_eq. ss. }
            i. eapply PRE.(Valid.write_ex_codom_rmw). econs; eauto.
          + inv H.
            exploit PRE.(Valid.rmw_is_po); eauto. i. inv x1. destruct x. ss. subst.
            exploit EX2.(RMW); ss; eauto.
            { rewrite List.app_length. s. clear. lia. }
            i. inv x0; ss. 
            exploit sim_trace_sim_th; try exact TRACE; eauto. intro M.
            destruct M.(AEU_WF). ss. exploit RMW_LIMIT; eauto. clear. lia.
      }
      specialize (FWDBANK loc). des.
      * left. esplits; eauto.
        rewrite sim_local_fwd_step. econs.
        econs; cycle 1.
        { instantiate (1 := (_, _)). econs; ss. }
        left. econs. split; eauto. econs; ss.
        exploit EX2.(LABELS_REV); ss.
        { apply nth_error_last. apply Nat.eqb_eq. ss. }
        i. econs; eauto. ii. apply Label.is_writing_inv in H. des. inv H.
        inv VLOC. congr.
      * right. esplits; eauto.
        i. specialize (FWDBANK0 eid).
        rewrite sim_local_fwd_none_step. rewrite inverse_step.
        ii. inv H. inv REL.
        { apply FWDBANK0. econs; eauto. }
        { inv H. inv H1. exploit EX2.(LABELS); eauto; ss.
          { rewrite List.app_length. s. lia. }
          rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0.
          apply Label.is_writing_inv in LABEL. i. des. inv LABEL.
          inv VLOC. congr. }
    + destruct ex0; ss.
    + intro. rewrite Promises.unset_o. condtac; ss. i.
      exploit PROMISES; eauto. i. des. esplits; cycle 1; eauto.
      inv N.
      * exfalso. apply c.
        rewrite EX2.(XVEXT); cycle 1.
        { ss. rewrite List.app_length. ss. clear. lia. }
        destruct (length (ALocal.labels alc1) =? ALocal.next_eid alc1) eqn:Heq; cycle 1.
        { rewrite Nat.eqb_neq in Heq. unfold ALocal.next_eid in Heq. ss. }
        rewrite fun_add_spec.
        destruct (equiv_dec (ValA.val (sem_expr rmap1 eloc)) (ValA.val (sem_expr rmap1 eloc))) eqn:Heq1; ss.
        exfalso. apply c0. ss.
      * clear -H. lia.
  - (* write failure *)
    inv STEP0. inv RES. inv ASTATE_STEP; inv ALOCAL_STEP; ss; inv EVENT; ss. splits.
    + econs; ss. apply sim_rmap_add; try by apply L. econs; ss. ii. des. ss.
    + econs; ss; try by apply L.
  - (* isb *)
    inv STEP0. inv ASTATE_STEP; inv ALOCAL_STEP; ss; inv EVENT; ss. splits.
    econs; ss.
    { econs; ss. apply L. }
    destruct L.(LC). ss. econs; ss.
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_coh_step. rewrite inverse_step.
      rewrite inverse_union. ii. des; [apply COH|]; eauto.
      inv EID. inv REL. inv H. inv H0. inv H2.
      apply Label.is_writing_inv in LABEL. des. subst. inv H1.
      * exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
      * inv H. exploit RF2; eauto. i. des.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vrn_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VRN; eauto. i. rewrite <- join_l. ss.
      * inv EID. inv REL. inv H. inv H1. inv H. inv H2. inv H3.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x1. inv LABEL.
      * inv EID. inv REL. inv H. inv H1. inv H. inv H2. inv H3.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x1. inv LABEL.
      * inv EID. inv REL. inv H. inv H1.
        rewrite <- join_r. apply L. econs; eauto.
      * inv EID. inv REL. inv H0. destruct l; ss.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vwn_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VWN; eauto.
      * inv EID. inv REL. inv H. inv H1. inv H. inv H2. inv H3.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x1. inv LABEL.
      * inv EID. inv REL. inv H. inv H1. inv H. inv H2. inv H3.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x1. inv LABEL.
      * inv EID. inv REL. inv H0. destruct l; ss.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vro_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VRO; eauto.
      * inv EID. inv REL. inv H0. destruct l; ss.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vwo_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VWO; eauto.
      * inv EID. inv REL. inv H0. destruct l; ss.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vcap_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VCAP; eauto.
      * inv EID.
        exploit Valid.ctrl_is_po; eauto. i. inv x0. destruct eid. ss. subst.
        exploit EX2.(CTRL); eauto; ss.
        { rewrite List.app_length. ss. clear. lia. }
        i. exploit EX2.(CTRL); eauto; ss.
        { rewrite List.app_length. ss. clear. lia. }
        i.
        exploit EX2.(LABELS_REV); ss.
        { apply nth_error_last. apply Nat.eqb_eq. ss. }
        intro X. exploit Valid.ctrl_label; eauto. i. des.
        inv EID2. rewrite X in EID. inv EID. ss.
      * inv EID.
        exploit Valid.addr_is_po; eauto. i. inv x0. destruct eid. ss. subst.
        exploit EX2.(ADDR); eauto; ss.
        { rewrite List.app_length. ss. clear. lia. }
        i. exploit EX2.(ADDR); eauto; ss.
        { rewrite List.app_length. ss. clear. lia. }
        i.
        exploit EX2.(LABELS_REV); ss.
        { apply nth_error_last. apply Nat.eqb_eq. ss. }
        intro X. exploit Valid.addr_label; eauto. i. des.
        inv EID2. rewrite X in EID. inv EID. ss.
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vrel_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VREL; eauto.
      * inv EID. inv REL. inv H0. destruct l; ss.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
    + i. specialize (FWDBANK loc). des.
      * left. esplits; eauto.
        rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_fwd_step. econs.
        econs; cycle 1.
        { instantiate (1 := (_, _)). econs; ss. }
        left. econs. split; eauto. econs; ss.
        exploit EX2.(LABELS_REV); ss.
        { apply nth_error_last. apply Nat.eqb_eq. ss. }
        intro X. econs; eauto.
      * right. esplits; eauto.
        i. specialize (FWDBANK0 eid).
        rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_fwd_none_step. rewrite inverse_step.
        ii. inv H. inv REL.
        { apply FWDBANK0. econs; eauto. }
        { inv H. inv H1. exploit EX2.(LABELS); eauto; ss.
          { rewrite List.app_length. s. lia. }
          rewrite List.nth_error_app2, Nat.sub_diag; ss.
          destruct l; ss. }
    + i. exploit PROMISES; eauto. i. des. esplits; cycle 1; eauto.
      rewrite List.app_length, Nat.add_1_r. inv N.
      * inv WRITE. exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
        destruct l; ss.
      * clear -H. lia.
  - (* dmb *)
    inv STEP0. inv ASTATE_STEP; inv ALOCAL_STEP; ss; inv EVENT; ss. splits.
    econs; ss.
    { econs; ss. apply L. }
    destruct L.(LC). ss. econs; ss.
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_coh_step. rewrite inverse_step.
      rewrite inverse_union. ii. des; [apply COH|]; eauto.
      inv EID. inv REL. inv H. inv H0. inv H2.
      apply Label.is_writing_inv in LABEL. des. subst. inv H1.
      * exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
      * inv H. exploit RF2; eauto. i. des.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vrn_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VRN; eauto. i. rewrite <- join_l. ss.
      * inv EID. inv REL. inv H. inv H1. inv H. inv H2. inv H3.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. simplify.
        destruct rr; ss.
        rewrite <- join_r, <- join_l. apply L. econs; eauto. econs; eauto.
      * inv EID. inv REL. inv H. inv H1. inv H. inv H2. inv H3.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. simplify.
        destruct wr; ss.
        rewrite <- join_r, <- join_r, <- join_l. apply L. econs; eauto. econs; eauto.
      * inv EID. inv REL. inv H. inv H1. inv H2.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
      * inv EID. inv REL. inv H0. destruct l; ss.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vwn_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VWN; eauto. i. rewrite <- join_l. ss.
      * inv EID. inv REL. inv H. inv H1. inv H. inv H2. inv H3.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. simplify.
        destruct rw; ss.
        rewrite <- join_r, <- join_l. apply L. econs; eauto. econs; eauto.
      * inv EID. inv REL. inv H. inv H1. inv H. inv H2. inv H3.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. simplify.
        destruct ww; ss.
        rewrite <- join_r, <- join_r, <- join_l. apply L. econs; eauto. econs; eauto.
      * inv EID. inv REL. inv H0. destruct l; ss.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vro_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VRO; eauto.
      * inv EID. inv REL. inv H0. destruct l; ss.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vwo_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VWO; eauto.
      * inv EID. inv REL. inv H0. destruct l; ss.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vcap_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VCAP; eauto.
      * inv EID.
        exploit Valid.ctrl_is_po; eauto. i. inv x0. destruct eid. ss. subst.
        exploit EX2.(CTRL); eauto; ss.
        { rewrite List.app_length. ss. clear. lia. }
        i. exploit EX2.(CTRL); eauto; ss.
        { rewrite List.app_length. ss. clear. lia. }
        i.
        exploit EX2.(LABELS_REV); ss.
        { apply nth_error_last. apply Nat.eqb_eq. ss. }
        intro X. exploit Valid.ctrl_label; eauto. i. des.
        inv EID2. rewrite X in EID. inv EID. ss.
      * inv EID.
        exploit Valid.addr_is_po; eauto. i. inv x0. destruct eid. ss. subst.
        exploit EX2.(ADDR); eauto; ss.
        { rewrite List.app_length. ss. clear. lia. }
        i. exploit EX2.(ADDR); eauto; ss.
        { rewrite List.app_length. ss. clear. lia. }
        i.
        exploit EX2.(LABELS_REV); ss.
        { apply nth_error_last. apply Nat.eqb_eq. ss. }
        intro X. exploit Valid.addr_label; eauto. i. des.
        inv EID2. rewrite X in EID. inv EID. ss.
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vrel_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VREL; eauto.
      * inv EID. inv REL. inv H0. destruct l; ss.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
    + i. specialize (FWDBANK loc). des.
      * left. esplits; eauto.
        rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_fwd_step. econs.
        econs; cycle 1.
        { instantiate (1 := (_, _)). econs; ss. }
        left. econs. split; eauto. econs; ss.
        exploit EX2.(LABELS_REV); ss.
        { apply nth_error_last. apply Nat.eqb_eq. ss. }
        intro X. econs; eauto.
      * right. esplits; eauto.
        i. specialize (FWDBANK0 eid).
        rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_fwd_none_step. rewrite inverse_step.
        ii. inv H. inv REL.
        { apply FWDBANK0. econs; eauto. }
        { inv H. inv H1. exploit EX2.(LABELS); eauto; ss.
          { rewrite List.app_length. s. lia. }
          rewrite List.nth_error_app2, Nat.sub_diag; ss.
          destruct l; ss. }
    + i. exploit PROMISES; eauto. i. des. esplits; cycle 1; eauto.
      rewrite List.app_length, Nat.add_1_r. inv N.
      * inv WRITE. exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
        destruct l; ss.
      * clear -H. lia.
  - (* if *)
    inv LC. inv ASTATE_STEP; inv ALOCAL_STEP; ss; inv EVENT; ss. splits.
    econs; ss.
    { econs; ss. apply L. }
    destruct L.(LC). ss. econs; ss.
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_coh_step. rewrite inverse_step.
      rewrite inverse_union. ii. des; [apply COH|]; eauto.
      inv EID. inv REL. inv H. inv H0. inv H2.
      apply Label.is_writing_inv in LABEL. des. subst. inv H1.
      * exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
      * inv H. exploit RF2; eauto. i. des.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vrn_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VRN; eauto.
      * inv EID. inv REL. inv H. inv H1. inv H. inv H2. inv H3.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. simplify. ss.
      * inv EID. inv REL. inv H. inv H1. inv H. inv H2. inv H3.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. simplify. ss.
      * inv EID. inv REL. inv H. inv H1. inv H2.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
      * inv EID. inv REL. inv H0. destruct l; ss.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vwn_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VWN; eauto.
      * inv EID. inv REL. inv H. inv H1. inv H. inv H2. inv H3.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. simplify. ss.
      * inv EID. inv REL. inv H. inv H1. inv H. inv H2. inv H3.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. simplify. ss.
      * inv EID. inv REL. inv H0. destruct l; ss.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vro_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VRO; eauto.
      * inv EID. inv REL. inv H0. destruct l; ss.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vwo_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VWO; eauto.
      * inv EID. inv REL. inv H0. destruct l; ss.
        exploit EX2.(LABELS); eauto; ss.
        rewrite List.app_length. s. lia.
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vcap_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * rewrite <- join_l. inv EID. exploit VCAP; eauto.
      * inv EID.
        exploit Valid.ctrl_is_po; eauto. i. inv x0. destruct eid. ss. subst.
        exploit EX2.(CTRL); eauto; ss.
        { rewrite List.app_length. ss. clear. lia. }
        i. inv x0.
        { exploit sim_trace_sim_th; try exact TRACE; eauto. intro M.
          destruct M.(AEU_WF). ss. exploit CTRL_LIMIT; eauto. clear. lia.
        }
        inv H. destruct L.(ST). ss.
        exploit sim_rmap_expr; eauto. i. inv x0.
        rewrite <- join_r. apply VIEW; eauto.
      * inv EID.
        exploit Valid.addr_is_po; eauto. i. inv x0. destruct eid. ss. subst.
        exploit EX2.(ADDR); eauto; ss.
        { rewrite List.app_length. ss. clear. lia. }
        i. exploit EX2.(ADDR); eauto; ss.
        { rewrite List.app_length. ss. clear. lia. }
        i.
        exploit EX2.(LABELS_REV); ss.
        { apply nth_error_last. apply Nat.eqb_eq. ss. }
        intro X. exploit Valid.addr_label; eauto. i. des.
        inv EID2. rewrite X in EID. inv EID. ss.
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vrel_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VREL; eauto.
      * inv EID. inv REL. inv H0. destruct l; ss.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
    + i. specialize (FWDBANK loc). des.
      * left. esplits; eauto.
        rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_fwd_step. econs.
        econs; cycle 1.
        { instantiate (1 := (_, _)). econs; ss. }
        left. econs. split; eauto. econs; ss.
        exploit EX2.(LABELS_REV); ss.
        { apply nth_error_last. apply Nat.eqb_eq. ss. }
        intro X. econs; eauto.
      * right. esplits; eauto.
        i. specialize (FWDBANK0 eid).
        rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_fwd_none_step. rewrite inverse_step.
        ii. inv H. inv REL.
        { apply FWDBANK0. econs; eauto. }
        { inv H. inv H1. exploit EX2.(LABELS); eauto; ss.
          { rewrite List.app_length. s. lia. }
          rewrite List.nth_error_app2, Nat.sub_diag; ss.
          destruct l; ss. }
    + i. exploit PROMISES; eauto. i. des. esplits; cycle 1; eauto.
      rewrite List.app_length, Nat.add_1_r. inv N.
      * inv WRITE. exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
        destruct l; ss.
      * clear -H. lia.
  - (* dowhile *)
    inv ASTATE_STEP; inv ALOCAL_STEP; ss; inv EVENT; ss. splits.
    + econs; ss; try by apply L.
    + econs; ss; try by apply L.
Qed.
