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


Lemma sim_traces_sim_th'_ob_read
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
    sim_ob_read tid ex (v_gen vexts) eu2 aeu2.
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
  exploit L'.(RPROP1); ss.
  { apply nth_error_last. apply Nat.eqb_eq. ss. }
  unfold ALocal.next_eid in *. condtac; cycle 1.
  { apply Nat.eqb_neq in X. congr. }
  i. des. inv x0.
  exploit L'.(RPROP2); eauto.
  { rewrite X. eauto. }
  s. rewrite X. i. des.
  apply nth_error_snoc_inv_last in x3. inv x3.
  clear x4 H3 tid'0 x2 x0.
  rewrite EX2.(XVEXT); s; cycle 1.
  { rewrite List.app_length. s. clear. lia. }
  rewrite X.
  inv STEP0. ss. subst. inv LOCAL0; inv EVENT. inv STEP0. ss.
  exploit EX2.(LABELS); eauto; ss.
  { rewrite List.app_length. s. clear. lia. }
  i.
  move AOB at bottom. unfold ob' in AOB. des_union.
  - (* rfe *)
    assert (v_gen vexts eid1 = ts).
    { inv H. destruct eid1 as [tid1 eid1]. inv H2. ss.
      generalize H1. intro Y. rewrite RF in Y. inv Y. ss.
      assert (r (length (ALocal.labels alc1)) =
              (fun eid : nat =>
                 if eid =? length (ALocal.labels alc1)
                 then Some (ValA.val vloc, fun_add (ValA.val vloc) ts (Local.coh lc1) (ValA.val vloc))
                 else r1 eid) (length (ALocal.labels alc1))).
      { eapply EX2.(XR); eauto. s. rewrite List.app_length. s. clear. lia. }
      rewrite H in R. clear H.
      destruct (length (ALocal.labels alc1) =? length (ALocal.labels alc1)); ss.
      rewrite fun_add_spec in R.
      destruct (equiv_dec (ValA.val vloc) (ValA.val vloc)); cycle 1.
      { exfalso. apply c. ss. }
      inv R.
      generalize (SIM tid1). intro SIM1. inv SIM1; simplify.
      exploit sim_trace_last; try exact REL0. i. des. simplify.
      exploit sim_trace_sim_th; try exact REL0; eauto. intro L1.
      exploit L1.(WPROP3); eauto. i. des.
      unfold v_gen. ss. rewrite <- H7. ss. }
    subst.
    rewrite <- join_r. unfold FwdItem.read_view. condtac; ss.
    destruct (equiv_dec (FwdItem.ts (Local.fwdbank lc1 (ValA.val vloc))) (v_gen vexts eid1)); ss. inv e.
    generalize (L.(LC).(FWDBANK) (ValA.val vloc)). s. i. des.
    + rewrite <- TS in H2.
      destruct eid as [tid2 eid2], eid1 as [tid1 eid1].
      assert (tid1 = tid2).
      { inv H. exploit RF2; eauto. i. des.
        unfold Execution.label in WRITE0. ss.
        rewrite PRE.(Valid.LABELS) in WRITE0.
        rewrite IdMap.map_spec in WRITE0.
        destruct (IdMap.find tid1 (Valid.aeus PRE)) eqn:FIND1; ss.
        generalize (ATR tid1). intro ATR1. inv ATR1; try congr. des. simplify.
        generalize (SIM tid1). intro SIM1. inv SIM1; simplify.
        exploit sim_trace_last; try exact REL0. i. des. simplify.
        exploit sim_trace_sim_th; try exact REL0; eauto. intro L1.
        inv WRITE. inv WRITE1. destruct l0; ss.
        unfold Execution.label in EID0. ss.
        rewrite PRE.(Valid.LABELS) in EID0.
        rewrite IdMap.map_spec in EID0.
        destruct (IdMap.find tid2 (Valid.aeus PRE)) eqn:FIND2; ss.
        generalize (ATR tid2). intro ATR2. inv ATR2; try congr. des. simplify.
        generalize (SIM tid2). intro SIM2. inv SIM2; simplify.
        exploit sim_trace_last; try exact REL1. i. des. simplify.
        exploit sim_trace_sim_th; try exact REL1; eauto. intro L2.
        move H2 at bottom.
        unfold v_gen in H2. ss.
        rewrite <- H10, <- H16 in H2.
        exploit L1.(WPROP2); eauto. i. des.
        exploit L2.(WPROP2); eauto. i. des.
        exploit L1.(WPROP3); eauto. i. des.
        exploit L2.(WPROP3); eauto. i. des.
        rewrite x8, x14 in H2. inv H2.
        rewrite H in x17. rewrite x11 in x17. inv x17. ss. }
      subst.
      inv WRITE. inv PO. ss. subst. inv H. inv H3. ss.
    + rewrite H1. refl.
  - (* dob *)
    unfold Execution.dob in H. rewrite ? seq_assoc in *. des_union.
    + inv H1. des. inv H1; cycle 1.
      { generalize L.(LC).(FWDBANK). intro SIM_FWD. ss.
        specialize (SIM_FWD (sem_expr rmap eloc).(ValA.val)). des; cycle 1.
        - destruct x. inv H2. exploit RF2; eauto. i. des.
          exfalso. apply (SIM_FWD0 (t, n0)).
          econs; try refl. econs. split.
          + rewrite READ in EID. inv EID. econs; eauto.
            econs; eauto. ss. unfold equiv_dec.
            unfold Z_eqdec. unfold proj_sumbool. des_ifs.
          + inv H3. admit. (* rfi is po: requires internal *)
        - inv WRITE.
          assert (x = eid).
          { admit. (* use internal *) }
          subst. rewrite <- join_r. exploit VIEW; eauto. i.
          rewrite H0. unfold FwdItem.read_view. rewrite <- TS.
          destruct L'.(EU_WF). destruct LOCAL0. ss.
          specialize (FWDBANK (ValA.val (sem_expr rmap eloc))). des.
          rewrite H0 in FWDBANK. rewrite fun_add_spec in FWDBANK.
          des_ifs; etrans; eauto; ss; try by (etrans; eauto).
          + exfalso. apply c. ss.
          + exfalso. apply c. ss.
      }
      inv H; cycle 1.
      { exploit Valid.data_label; eauto. i. des. inv EID2. destruct l0; ss. congr. }
      inv EID. rewrite <- join_l, <- join_l.
      destruct eid1 as [tid1 eid1]. exploit Valid.addr_is_po; eauto. intro Y. inv Y. ss. subst.
      exploit EX2.(ADDR); eauto; ss.
      { rewrite List.app_length. s. clear. lia. }
      intro Y. inv Y.
      { exploit sim_trace_sim_th; try exact TRACE; eauto. intro M.
        destruct M.(AEU_WF). ss. exploit ADDR_LIMIT; eauto. clear. lia.
      }
      inv H.
      (* destruct L'.(EU_WF). destruct LOCAL0. ss. *)
      (* specialize (FWDBANK (ValA.val (sem_expr rmap eloc))). des. *)
      (* rewrite H0 in FWDBANK. rewrite fun_add_spec in FWDBANK. *)
      move STATE0 at bottom. inv STATE0.
      inv STATE1. ss. inv STMTS. destruct L.(ST). ss.
      exploit sim_rmap_expr; eauto. instantiate (1 := eloc). i.
      inv x2. specialize (VIEW (tid, eid1)). ss.
      exploit VIEW; ss.
    + inv H1. des. inv H1.
      { inv H2. inv H3. destruct l0; ss. congr. }
      inv H2. des. inv H2.
      rewrite L.(LC).(VRP); ss.
      * rewrite <- join_l, <- join_r, <- join_l. ss.
      * econs; eauto. unfold sim_local_vrp. left. right.
        rewrite ? seq_assoc in H1. econs; eauto.
  - (* aob *)
    unfold Execution.aob in H1. rewrite ? seq_assoc in *.
    inv H1. des. inv H.  des. inv H2. inv H1. guardH H2.
    assert (v_gen vexts x2 = ts).
    { inv H3. destruct x2 as [tid1 eid1]. inv H1. ss.
      generalize H. intro Y. rewrite RF in Y. inv Y. ss.
      assert (r (length (ALocal.labels alc1)) =
              (fun eid : nat =>
                 if eid =? length (ALocal.labels alc1)
                 then Some (ValA.val vloc, fun_add (ValA.val vloc) ts (Local.coh lc1) (ValA.val vloc))
                 else r1 eid) (length (ALocal.labels alc1))).
      { eapply EX2.(XR); eauto. s. rewrite List.app_length. s. clear. lia. }
      rewrite H1 in R. clear H1.
      destruct (length (ALocal.labels alc1) =? length (ALocal.labels alc1)); ss.
      rewrite fun_add_spec in R.
      destruct (equiv_dec (ValA.val vloc) (ValA.val vloc)); cycle 1.
      { exfalso. apply c. ss. }
      inv R.
      generalize (SIM tid). intro SIM1. inv SIM1; simplify.
      exploit sim_trace_last; try exact REL0. i. des. simplify.
      exploit sim_trace_sim_th; try exact REL0; eauto. intro L1.
      exploit L1.(WPROP3); eauto. i. des.
      unfold v_gen. ss. rewrite -> FIND_VEXTL. ss. }
    subst.
    rewrite <- join_r. unfold FwdItem.read_view. condtac; ss.
    destruct (equiv_dec (FwdItem.ts (Local.fwdbank lc1 (ValA.val vloc))) (v_gen vexts x2)); ss. inv e.
    generalize (L.(LC).(FWDBANK) (ValA.val vloc)). s. i. des.
    + apply Bool.negb_true_iff, Bool.andb_false_iff in X0. des.
      * admit. (* fwdbank similarity *)
        (* H3 : Execution.rfi ex x2 (tid, length (ALocal.labels alc1)) *)
        (* H4 : codom_rel (Execution.rmw ex) x2 *)
        (* X0 : FwdItem.ex (Local.fwdbank lc1 (ValA.val vloc)) = false *)
      * unguardH H2. des.
        { destruct (equiv_dec arch riscv); ss. }
        { inv H2. destruct l0; ss. rewrite EID in EID0. inv EID0.
          rewrite LABEL1 in X0. rewrite Bool.orb_comm in X0. ss.
        }
    + rewrite H. refl.
  - (* bob *)
    unfold Execution.bob in H. rewrite ? seq_assoc in *. des_union.
    + rewrite L.(LC).(VRP); ss.
      * rewrite <- join_l, <- join_r, <- join_l. ss.
      * econs; eauto. unfold sim_local_vrp. left. left. left.
        rewrite ? seq_assoc. inv H1. des. inv H1. ss.
    + inv H1. des. inv H1. inv H3. destruct l0; ss. congr.
    + rewrite L.(LC).(VRP); ss.
      * rewrite <- join_l, <- join_r, <- join_l. ss.
      * econs; eauto. unfold sim_local_vrp. left. left. right.
        rewrite ? seq_assoc. inv H. des. inv H2. ss.
    + inv H1. des. inv H1. inv H3. destruct l0; ss. congr.
    + inv H. des. inv H2. inv H3. destruct l0; ss. rewrite EID in EID0. inv EID0. rewrite LABEL1.
      rewrite L.(LC).(VREL); ss.
      * rewrite <- join_l, <- join_r, <- join_r, <- join_l. ss.
      * econs; ss. unfold sim_local_vrel. ss.
    + rewrite L.(LC).(VRP); ss.
      * rewrite <- join_l, <- join_r, <- join_l. ss.
      * econs; eauto. unfold sim_local_vrp. right.
        rewrite ? seq_assoc. ss.
    + inv H. des. inv H2. inv H3. destruct l0; ss. congr.
    + destruct (equiv_dec arch riscv); ss. exploit Valid.rmw_spec; eauto. i. des.
      exploit EX2.(LABELS_REV); eauto. i.
      inv LABEL2. des. destruct l0; ss. rewrite x2 in EID0. inv EID0.
Admitted.
