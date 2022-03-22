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
Require Import PacoNotation.
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


Lemma sim_traces_sim_th'_ob_write
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
             (fun _ tr sl => exists l, tr = (ExecUnit.mk (fst sl) (snd sl) m.(Machine.mem)) :: l)
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
    (SIM_TH': sim_th' tid m.(Machine.mem) ex (v_gen vexts) eu1 aeu1),
    sim_ob_write tid ex (v_gen vexts) eu2 aeu2.
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

  ii.
  destruct (le_lt_dec (length (ALocal.labels (AExecUnit.local aeu1))) eid2); cycle 1.
  { eapply L; eauto. }
  inv EID2. destruct l0; ss.
  destruct eu1 as [st1 lc1 mem1].
  destruct eu2 as [st2 lc2 mem2].
  destruct aeu1 as [ast1 alc1].
  destruct aeu2 as [ast2 alc2].
  inv ASTATE_STEP; inv EVENT; inv ALOCAL_STEP; inv EVENT; repeat (ss; subst).
  all: try (clear - LABEL l; lia).
  all: rewrite List.app_length in LABEL; ss.
  all: assert (EID2: eid2 = length (ALocal.labels alc1)) by (clear - LABEL l; lia); subst.
  all: exploit LABELS; eauto; ss.
  all: try by clear; rewrite List.app_length; s; lia.
  all: intro NTH; apply nth_error_snoc_inv_last in NTH; inv NTH.
  rewrite EU, AEU, WL, RL, COV, VEXT in SIMTR.
  exploit sim_trace_sim_th; try exact SIMTR; eauto. intro L'.
  inv RES. destruct res1. ss. subst.
  exploit L'.(WPROP2); ss.
  { apply nth_error_last. apply Nat.eqb_eq. ss. }
  unfold ALocal.next_eid in *. condtac; cycle 1.
  { apply Nat.eqb_neq in X. congr. }
  i. des. inv x0.
  exploit L'.(WPROP3); eauto.
  { rewrite X. eauto. }
  s. rewrite X. i. des.
  apply nth_error_snoc_inv_last in x5. inv x5.
  rewrite x1 in x6. inv x6. clear x3 x4 H1.
  rewrite EX2.(XVEXT); s; cycle 1.
  { rewrite List.app_length. s. clear. lia. }
  rewrite X.
  inv STEP0. ss. subst. inv LOCAL0; inv EVENT; inv STEP0; ss.
  move OB at bottom. unfold ob' in OB. des_union.
  - (* rfe *)
    inv H. exploit RF2; eauto. i. des. congr.
  - (* dob *)
    unfold Execution.dob in H. rewrite ? seq_assoc in *. des_union.
    + inv H1. des. inv H1; cycle 1.
      { inv H2. exploit RF2; eauto. i. des.  congr. }
      rewrite fun_add_spec. condtac; [|congr]. inv WRITABLE.
      eapply Nat.le_lt_trans; [|apply EXT]. s.
      inv H.
      * rewrite <- join_l.
        destruct eid1 as [tid1 eid1]. exploit Valid.addr_is_po; eauto. intro Y. inv Y. ss. subst.
        rewrite EX2.(XVEXT); s; cycle 1.
        { s. rewrite List.app_length. s. clear -N. lia. }
        condtac.
        { apply Nat.eqb_eq in X1. subst. clear -N. lia. }
        exploit EX2.(ADDR); eauto; ss.
        { rewrite List.app_length. s. clear. lia. }
        intro Y. inv Y.
        { exploit sim_trace_sim_th; try exact TRACE; eauto. intro M.
          destruct M.(AEU_WF). ss. exploit ADDR_LIMIT; eauto. clear. lia.
        }
        inv H.
        move STATE0 at bottom. inv STATE0.
        inv STATE1. ss. inv STMTS. destruct L.(ST). ss.
        exploit sim_rmap_expr; eauto. instantiate (1 := eloc). i.
        inv x3. specialize (VIEW (tid, eid1)). ss.
        exploit VIEW; ss. i.
        hexploit sim_traces_sim_ex_step; eauto. i.
        rewrite <- H.(XVEXT); auto.
      * rewrite <- join_r. rewrite <- join_l.
        destruct eid1 as [tid1 eid1]. exploit Valid.data_is_po; eauto. intro Y. inv Y. ss. subst.
        rewrite EX2.(XVEXT); s; cycle 1.
        { s. rewrite List.app_length. s. clear -N. lia. }
        condtac.
        { apply Nat.eqb_eq in X1. subst. clear -N. lia. }
        exploit EX2.(DATA); eauto; ss.
        { rewrite List.app_length. s. clear. lia. }
        intro Y. inv Y.
        { exploit sim_trace_sim_th; try exact TRACE; eauto. intro L1.
          destruct L1.(AEU_WF). ss. exploit DATA_LIMIT; eauto. clear. lia. }
        inv H.
        move STATE0 at bottom. inv STATE0.
        inv STATE1. ss. inv STMTS. destruct L.(ST). ss.
        exploit sim_rmap_expr; eauto. instantiate (1 := eval). i.
        inv x3. specialize (VIEW (tid, eid1)). ss.
        exploit VIEW; ss. i.
        hexploit sim_traces_sim_ex_step; eauto. i.
        rewrite <- H.(XVEXT); auto.
    + inv H1. des. inv H1; cycle 1.
      { inv H2. des. inv H2. inv H5. destruct l0; ss. congr. }
      inv H2. eapply Nat.le_lt_trans.
      { apply L.(LC).(VCAP); ss. econs; ss. ss. }
      s. rewrite fun_add_spec. condtac; [|congr].
      inv WRITABLE. ss. eapply Nat.le_lt_trans; [|exact EXT].
      s. rewrite <- join_r, <- join_r, <- join_l. ss.
  - (* aob *)
    unfold Execution.aob in H1. rewrite ? seq_assoc in *.
    inv H1. des. inv H. des. inv H2. inv H1. guardH H2.
    inv H4. exploit RF2; eauto. i. des. congr.
  - (* bob *)
    unfold Execution.bob in H. rewrite ? seq_assoc in *. des_union.
    + inv H1. des. inv H1. inv H4. destruct l0; ss. congr.
    + eapply Nat.le_lt_trans; [apply L.(LC).(VWN)|]; ss; cycle 1.
      * rewrite fun_add_spec. condtac; [|congr].
        inv WRITABLE. ss. eapply Nat.le_lt_trans; [|exact EXT].
        rewrite <- join_r, <- join_r, <- join_r, <- join_l. ss.
      * econs; eauto. unfold sim_local_vwn. left. left.
        rewrite ? seq_assoc. inv H1. des. inv H1. ss.
    + inv H. des. inv H2. inv H4. destruct l0; ss. congr.
    + eapply Nat.le_lt_trans; [apply L.(LC).(VWN)|]; ss; cycle 1.
      * rewrite fun_add_spec. condtac; [|congr].
        inv WRITABLE. ss. eapply Nat.le_lt_trans; [|exact EXT].
        rewrite <- join_r, <- join_r, <- join_r, <- join_l. ss.
      * econs; eauto. unfold sim_local_vwn. left. right.
        rewrite ? seq_assoc. inv H1. des. inv H1. ss.
    + inv H. des. inv H2. inv H4. destruct l0; ss. congr.
    + eapply Nat.le_lt_trans; [apply L.(LC).(VWN)|]; ss; cycle 1.
      * rewrite fun_add_spec. condtac; [|congr].
        inv WRITABLE. ss. eapply Nat.le_lt_trans; [|exact EXT].
        rewrite <- join_r, <- join_r, <- join_r, <- join_l. ss.
      * econs; eauto. unfold sim_local_vwn. right.
        rewrite ? seq_assoc. ss.
    + inv H. des. inv H2. inv H4. destruct l0; ss. rewrite EID in EID0. inv EID0.
      exploit Valid.po_label_pre; eauto. i. des.
      destruct eid1 as [tid1 eid1]. inv H1. ss. subst.
      destruct label1; ss.
      * eapply Nat.le_lt_trans; [apply L.(LC).(VRO)|]; ss; cycle 1.
        { rewrite fun_add_spec. condtac; [|congr].
          inv WRITABLE. ss. eapply Nat.le_lt_trans; [|exact EXT].
          rewrite <- join_r, <- join_r, <- join_r, <- join_r, <- join_l.
          rewrite LABEL1. refl.
        }
        {  econs; eauto. unfold sim_local_vro. econs. splits; eauto.
           econs; ss. econs; eauto. econs; ss.
        }
      * eapply Nat.le_lt_trans; [apply L.(LC).(VWO)|]; ss; cycle 1.
        { rewrite fun_add_spec. condtac; [|congr].
          inv WRITABLE. ss. eapply Nat.le_lt_trans; [|exact EXT].
          rewrite <- join_r, <- join_r, <- join_r, <- join_r, <- join_r, <- join_l.
          rewrite LABEL1. refl.
        }
        {  econs; eauto. unfold sim_local_vwo. econs. splits; eauto.
           econs; ss. econs; eauto. econs; ss.
        }
      * eapply Nat.le_lt_trans; cycle 1.
        { eapply Nat.lt_le_trans; try eapply x0. apply Memory.latest_ts_spec. }
        rewrite EX2.(XVEXT); ss; cycle 1.
        { rewrite List.app_length. s. clear -N. lia. }
        condtac.
        { apply Nat.eqb_eq in X0. clear -N X0. lia. }
        destruct (le_lt_dec (vext1 eid1) 0); ss.
        exploit sim_trace_sim_th; try exact TRACE; eauto. intro L1.
        exploit L1.(VEXTPROP); eauto. s. i. inv x3.
        exploit LABELS_REV; eauto; ss.
        { apply nth_error_app_mon. eauto. }
        rewrite LABEL2. intro Y. inv Y. ss.
      * eapply Nat.le_lt_trans; cycle 1.
        { eapply Nat.lt_le_trans; try eapply x0. apply Memory.latest_ts_spec. }
        rewrite EX2.(XVEXT); ss; cycle 1.
        { rewrite List.app_length. s. clear -N. lia. }
        condtac.
        { apply Nat.eqb_eq in X0. clear -N X0. lia. }
        destruct (le_lt_dec (vext1 eid1) 0); ss.
        exploit sim_trace_sim_th; try exact TRACE; eauto. intro L1.
        exploit L1.(VEXTPROP); eauto. s. i. inv x3.
        exploit LABELS_REV; eauto; ss.
        { apply nth_error_app_mon. eauto. }
        rewrite LABEL2. intro Y. inv Y. ss.
    + destruct (equiv_dec arch riscv) eqn:Z; ss.
      rewrite fun_add_spec. condtac; [|congr].
      exploit Valid.rmw_is_po; eauto. destruct eid1. intro Y. inv Y. ss. subst.
      exploit EX2.(RMW); eauto; ss.
      { s. rewrite List.app_length. s. clear. lia. }
      intro Y. inv Y.
      { exploit sim_trace_sim_th; try exact TRACE; eauto. intro L1.
        destruct L1.(AEU_WF). ss. exploit RMW_LIMIT; eauto. clear. lia. }
      destruct ex0; ss. inv H. exploit EX; eauto. intro x. des. rewrite H2 in x. inv x.
      inv x3. des. destruct a; ss. 
      generalize L.(LC).(EXBANK). s. rewrite H2. intro Y. inv Y. des.
      inv REL. apply Label.is_reading_inv in LABEL1. des. subst.
      exploit EX2.(LABELS); eauto; ss.
      { rewrite List.app_length. s. clear -N. lia. }
      i. apply nth_error_snoc_inv in x3. des; ss. rewrite x4 in H5. inv H5.
      inv WRITABLE. eapply Nat.le_lt_trans; [|apply EXT]. s.
      rewrite <- join_r, <- join_r, <- join_r, <- join_r, <- join_r, <- join_r, <- join_l.
      rewrite Z, <- H. s. apply REL1. ss.
Qed.
