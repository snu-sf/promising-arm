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
    sim_state tid (v_gen vexts) eu2.(ExecUnit.state) aeu2.(AExecUnit.state) /\
    sim_local tid ex (v_gen vexts) eu2.(ExecUnit.local) aeu2.(AExecUnit.local).
Proof.
  i. rename SIM_TH' into L.
  generalize (SIM tid). intro X. inv X; simplify. rename c into wl, d into rl.
  destruct n.
  { generalize (lastn_length 1 tr). rewrite EU. destruct tr; ss. }
  exploit sim_trace_lastn; eauto. instantiate (1 := S n). intro SIMTR.
  exploit sim_traces_ex; eauto. intro EX2.
  inversion SIMTR; subst; simplify; [congr|].
  repeat match goal with
         | [H1: lastn ?a ?b = ?c, H2: ?d = lastn ?a ?b |- _] =>
           rewrite H1 in H2; inv H2
         end.
  exploit sim_trace_sim_state_weak; eauto. intro STATE1.
  rename H2 into WS, H3 into RS, H4 into WL, H5 into RL.

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
    admit.
  - (* write *)
    admit.
  (* econs; ss. *)
  (* { econs; ss. apply sim_rmap_add; ss. inv STEP. econs; ss. *)
  (*   ii. des. subst. destruct (equiv_dec arch riscv); ss. destruct eid. ss. subst. *)
  (*   unfold ALocal.next_eid in *. *)
  (*   rewrite VEXT1; cycle 1. *)
  (*   { rewrite List.app_length. s. clear. lia. } *)
  (*   condtac; cycle 1. *)
  (*   { apply Nat.eqb_neq in X. ss. } *)
  (*   rewrite fun_add_spec. condtac; ss. *)
  (*   inv WRITABLE. apply Nat.lt_le_incl. ss. *)
  (* } *)
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
      * exploit EX2.(LABELS); eauto; ss; cycle 1.
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. }
        { rewrite List.app_length. s. lia. }
      * inv H. exploit RF2; eauto. i. des.
        exploit EX2.(LABELS); eauto; ss; cycle 1.
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. }
        { rewrite List.app_length. s. lia. }
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vrp_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VRP; eauto. i. rewrite <- join_l. ss.
      * inv EID. inv REL. inv H. inv H1. inv H. inv H2. inv H3.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x1. inv LABEL. }
      * inv EID. inv REL. inv H. inv H1. inv H. inv H2. inv H3.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x1. inv LABEL. }
      * inv EID. inv REL. inv H. inv H1.
        rewrite <- join_r. apply L. econs; eauto.
      * inv EID. inv REL. inv H0. destruct l; ss.
        exploit EX2.(LABELS); eauto; ss; cycle 1.
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. }
        { rewrite List.app_length. s. lia. }
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vwp_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VWP; eauto.
      * inv EID. inv REL. inv H. inv H1. inv H. inv H2. inv H3.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x1. inv LABEL. }
      * inv EID. inv REL. inv H. inv H1. inv H. inv H2. inv H3.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x1. inv LABEL. }
      * inv EID. inv REL. inv H0. destruct l; ss.
        exploit EX2.(LABELS); eauto; ss; cycle 1.
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. }
        { rewrite List.app_length. s. lia. }
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vrm_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VRM; eauto.
      * inv EID. inv REL. inv H0. destruct l; ss.
        exploit EX2.(LABELS); eauto; ss; cycle 1.
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. }
        { rewrite List.app_length. s. lia. }
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vwm_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VWM; eauto.
      * inv EID. inv REL. inv H0. destruct l; ss.
        exploit EX2.(LABELS); eauto; ss; cycle 1.
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. }
        { rewrite List.app_length. s. lia. }
    + (* vcap *)
      rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vcap_step. rewrite inverse_step.
      rewrite inverse_union. ii. des.
      * exploit VCAP; eauto.
      * admit. (* ctrl/addr doesn't flow into barrier *)

    (* * (* TODO: move *) *)
    (*   Lemma addr_po_step ex: *)
    (*     (ex.(Execution.addr) ⨾ Execution.po) = *)
    (*     ((ex.(Execution.addr) ⨾ Execution.po) ∪ ex.(Execution.addr)) ⨾ *)
    (*                                                                  Execution.po_adj. *)
    (*   Proof. *)
    (*     rewrite ? (union_seq' Execution.po_adj), ? seq_assoc, ? union_assoc. *)
    (*     rewrite Execution.po_po_adj at 1. *)
    (*     rewrite (clos_refl_union Execution.po), union_seq, eq_seq. *)
    (*     rewrite ? (seq_union' (Execution.po ⨾ Execution.po_adj) Execution.po_adj), ? seq_assoc, ? union_assoc. *)
    (*     refl. *)
    (*   Qed. *)
        
    (*   rewrite addr_po_step in H. *)
        
    (*   (*TODO: move *) *)
    (*   Lemma step r eid tid n: *)
    (*     (r ⨾ Execution.po_adj) eid (tid, S n) = r eid (tid, n). *)
    (*   Proof. *)
    (*     propext. econs; i. *)
    (*     - inv H. des. inv H1. destruct x. ss. inv N. auto. *)
    (*     - econs. split; eauto. *)
    (*   Qed. *)

    (*   rewrite step in H. *)
    (*   inv H. *)
    (*   { eapply VCAP; eauto. econs; eauto. econs 2; eauto. } *)
    (*   { (* TODO: move *) *)
    (*     Lemma addr_eid *)
    (*           p ex (PRE: Valid.pre_ex p ex) *)
    (*           eid tid eid2 *)
    (*           (ADDR: ex.(Execution.addr) eid (tid, eid2)): *)
    (*       exists eid1, eid = (tid, eid1). *)
    (*     Proof. *)
    (*     Admitted. *)

    (*     exploit addr_eid; eauto. i. des. subst. *)
    (*     exploit ADDR; eauto; ss. *)
    (*     { rewrite List.app_length. ss. clear. lia. } *)
    (*     i. *)

    (*     (* TODO: move *) *)
    (*     Lemma addr_inv *)
    (*           p mem tid tr aeu atr wl rl covl vextl *)
    (*           eid1 eid2 *)
    (*           (SIM: sim_trace p mem tid tr (aeu::atr) wl rl covl vextl) *)
    (*           (EID2: eid2 >= List.length aeu.(AExecUnit.local).(ALocal.labels)) *)
    (*           (ADDR: aeu.(AExecUnit.local).(ALocal.addr) eid1 eid2): *)
    (*       False. *)
    (*     Proof. *)
    (*     Admitted. *)

    (*     exploit addr_inv; eauto. ss. *)
    (*   } *)
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vrel_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VREL; eauto.
      * inv EID. inv REL. inv H0. destruct l; ss.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. }
    + admit. (* fwdbank *)
    + admit. (* promise *)
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
      * exploit EX2.(LABELS); eauto; ss; cycle 1.
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. }
        { rewrite List.app_length. s. lia. }
      * inv H. exploit RF2; eauto. i. des.
        exploit EX2.(LABELS); eauto; ss; cycle 1.
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. }
        { rewrite List.app_length. s. lia. }
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vrp_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VRP; eauto. i. rewrite <- join_l. ss.
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
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. }
      * inv EID. inv REL. inv H0. destruct l; ss.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. }
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vwp_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VWP; eauto. i. rewrite <- join_l. ss.
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
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. }
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vrm_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VRM; eauto.
      * inv EID. inv REL. inv H0. destruct l; ss.
        exploit EX2.(LABELS); eauto; ss; cycle 1.
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. }
        { rewrite List.app_length. s. lia. }
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vwm_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VWM; eauto.
      * inv EID. inv REL. inv H0. destruct l; ss.
        exploit EX2.(LABELS); eauto; ss; cycle 1.
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. }
        { rewrite List.app_length. s. lia. }
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vcap_step. rewrite inverse_step.
      rewrite inverse_union. ii. des.
      * exploit VCAP; eauto.
      * admit. (* ctrl/addr doesn't flow into barrier *)
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vrel_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VREL; eauto.
      * inv EID. inv REL. inv H0. destruct l; ss.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. }
    + admit. (* fwdbank *)
    + admit. (* promise *)
  - (* if *)
    inv LC0. inv ASTATE_STEP; inv ALOCAL_STEP; ss; inv EVENT; ss. splits.
    econs; ss.
    { econs; ss. apply L. }
    destruct L.(LC). ss. econs; ss.
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_coh_step. rewrite inverse_step.
      rewrite inverse_union. ii. des; [apply COH|]; eauto.
      inv EID. inv REL. inv H. inv H0. inv H2.
      apply Label.is_writing_inv in LABEL. des. subst. inv H1.
      * exploit EX2.(LABELS); eauto; ss; cycle 1.
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. }
        { rewrite List.app_length. s. lia. }
      * inv H. exploit RF2; eauto. i. des.
        exploit EX2.(LABELS); eauto; ss; cycle 1.
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. }
        { rewrite List.app_length. s. lia. }
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vrp_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VRP; eauto.
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
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. }
      * inv EID. inv REL. inv H0. destruct l; ss.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. }
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vwp_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VWP; eauto.
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
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. }
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vrm_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VRM; eauto.
      * inv EID. inv REL. inv H0. destruct l; ss.
        exploit EX2.(LABELS); eauto; ss; cycle 1.
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. }
        { rewrite List.app_length. s. lia. }
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vwm_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VWM; eauto.
      * inv EID. inv REL. inv H0. destruct l; ss.
        exploit EX2.(LABELS); eauto; ss; cycle 1.
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. }
        { rewrite List.app_length. s. lia. }
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vcap_step. rewrite inverse_step.
      rewrite inverse_union. ii. des.
      * rewrite <- join_l. exploit VCAP; eauto.
      * rewrite <- join_r.
        admit. (* use EX2.(CTRL) .. *)
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vrel_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VREL; eauto.
      * inv EID. inv REL. inv H0. destruct l; ss.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. }
    + admit. (* fwdbank *)
    + admit. (* promise *)
  - (* dowhile *)
    inv ASTATE_STEP; inv ALOCAL_STEP; ss; inv EVENT; ss. splits.
    + econs; ss; try by apply L.
    + econs; ss; try by apply L.
Admitted.
