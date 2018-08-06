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
Require Import PromisingArch.axiomatic.PFtoA4FR.

Set Implicit Arguments.


Lemma sim_traces_sim_th'_atomic
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
    (SIM_TH': sim_th' tid m.(Machine.mem) ex (v_gen vexts) eu1 aeu1),
    sim_atomic tid ex (v_gen vexts) eu2 aeu2.
Proof.
  i. rename SIM_TH' into L.
  hexploit sim_traces_sim_th'_fr; eauto. intro SIM_FR.
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
  exploit Valid.rmw_spec; eauto. i. des.
  inv LABEL2. des. destruct l0; ss. destruct ex0; ss.
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
  destruct eid1 as [tid1 eid1]. inv PO. ss. subst.
  inv FRE. exploit SIM_FR; try exact H; [|intro X]; ss.
  { rewrite List.app_length; ss. etrans; eauto. }
  destruct eid as [tid' eid'].
  inv COE. exploit sim_traces_vext_co; eauto. intro Y.
  rewrite CO in H1. inv H1. ss.
  generalize (SIM tid'). intro SIM'. inv SIM'; simplify.
  exploit sim_trace_last; try exact REL0. i. des. simplify.
  exploit sim_trace_sim_th; try exact REL0; eauto. intro L'.
  exploit L'.(WPROP3); eauto. i. des.
  exploit sim_trace_memory; try exact SIMTR; eauto. intro MEM. ss.
  inv STEP0. ss. subst.
  inv LOCAL0; inv EVENT; cycle 1.
  { inv STEP0. inv RES. inv VAL. }
  inv STEP0. inv WRITABLE. exploit EX0; ss. i. des.
  destruct L.(LC). ss.
  rewrite TSX in EXBANK. inv EXBANK. des.
  exploit EX2.(RMW); eauto; ss.
  { rewrite List.app_length. ss. }
  i. inv x1.
  { exploit sim_trace_sim_th; try exact TRACE; eauto. intro L1.
    destruct L1.(AEU_WF). ss. exploit RMW2; eauto. i. des.
    assert (List.nth_error (ALocal.labels alc1) (length (ALocal.labels alc1)) <> None).
    { ii. congr. }
    rewrite List.nth_error_Some in H9. clear - H9. lia. }
  inv H1. rewrite <- H5 in H9. inv H9.
  assert (LOC: Exbank.loc eb = ValA.val vloc).
  { assert (SLW: sim_local_weak lc1 alc1).
    { clear - TRACE. inv TRACE; ss.
      unfold Machine.init_with_promises in FIND. ss.
      rewrite IdMap.mapi_spec in FIND.
      destruct (IdMap.find tid p); ss. inv FIND.
      econs; ss. }
    inv SLW; ss.
    { rewrite TSX in LOCAL_EX. inv LOCAL_EX. }
    rewrite TSX in LOCAL_EX. inv LOCAL_EX.
    assert (EQ1: ValA.val vloc = loc2).
    { exploit EX2.(XW); eauto.
      { instantiate (1 := length alc1.(ALocal.labels)). ss.
        rewrite List.app_length. ss. }
      i. destruct (length (ALocal.labels alc1) =? ALocal.next_eid alc1) eqn:Heq; cycle 1.
      { rewrite Nat.eqb_neq in Heq. unfold ALocal.next_eid in Heq. ss. }
      rewrite W2 in x1. inv x1. ss. }
    exploit sim_trace_sim_th; try exact TRACE; eauto. intro L1.
    rewrite ALOCAL_EX in H5. symmetry in H5. inv H5.
    inv H.
    - inv H1. des. rewrite RF in H. rewrite CO in H1.
      destruct x as [tid'' eid'']. inv H. inv H1. ss.
      simplify. rewrite W in W0. inv W0.
      exploit L1.(RPROP1); eauto. i. des.
      exploit EX2.(XR); eauto.
      { instantiate (1 := eid1). ss.
        rewrite List.app_length. ss.
        exploit List.nth_error_Some. i. des.
        exploit x7.
        { ii. rewrite LABEL_EX in H. inv H. }
        i. clear - x. lia. }
      i. rewrite R in x7. rewrite x1 in x7. inv x7.
      rewrite W1 in W3. inv W3. ss.
    - inv H1. inv H. inv H5. inv H. inv H1. inv H5.
      rewrite EID1 in EID3. inv EID3.
      rewrite EID2 in EID0. inv EID0.
      destruct l3; destruct l0; ss.
      inv LABEL3. inv X0. inv Y0.
      assert (loc = loc0).
      { destruct (equiv_dec loc loc1); ss.
        destruct (equiv_dec loc0 loc1); ss.
        rewrite e, e0. ss. }
      subst.
      exploit List.nth_error_Some. i. des. exploit x1.
      { ii. rewrite LABEL_EX in H. inv H. }
      i. clear x1. clear x6.
      exploit EX2.(LABELS); try eapply EID1; ss.
      { rewrite List.app_length. ss. clear - x. lia. }
      i. rewrite List.nth_error_app1 in x6; ss.
      rewrite LABEL_EX in x6. inv x6.
      unfold Execution.label in EID2. ss.
      rewrite PRE.(Valid.LABELS) in EID2.
      rewrite IdMap.map_spec in EID2.
      generalize (ATR tid'). intro ATR'. inv ATR'; try congr. des. simplify.
      rewrite <- H in EID2. ss. rewrite x4 in EID2. inv EID2. ss. }
  specialize (EX1 LOC). unfold Memory.exclusive in EX1.
  unfold Memory.no_msgs in EX1.
  destruct (cov eid') eqn:Hcov; ss.
  move x5 at bottom.
  unfold Memory.get_msg in x5. ss.
  exploit EX1; try exact x5; eauto.
  { inv H.
    - inv H1. des. inv REL1. inv H11.
      { rewrite VIEW. ss. }
      inv EID0. exploit RF_WF; [exact H|exact REL1|]. i. subst.
      exploit sim_traces_vext_co; try exact H1; eauto. i.
      unfold v_gen in x1. ss.
      rewrite <- H8 in x1. rewrite x2 in x1.
      eapply le_lt_trans; eauto.
    - inv H1. inv H9. inv H1. inv REL1. inv H13.
      { rewrite VIEW. ss. }
      exfalso. apply H12. unfold codom_rel.
      inv EID0. esplits; eauto. }
  { move Y at bottom. rewrite EX2.(XVEXT) in Y; cycle 1.
    { ss. rewrite List.app_length. ss. }
    destruct (length (ALocal.labels alc1) =? ALocal.next_eid alc1) eqn:Heq; cycle 1.
    { rewrite Nat.eqb_neq in Heq. ss. }
    rewrite fun_add_spec in Y.
    destruct (equiv_dec (ValA.val vloc) (ValA.val vloc)) eqn:Heq1; cycle 1.
    { exfalso. apply c. ss. }
    unfold v_gen in Y. ss. rewrite <- H8 in Y. rewrite <- x2.
    apply Nat.lt_le_incl. auto. }
  { ss. split.
    - exploit EX2.(XW); eauto.
      { instantiate (1 := length alc1.(ALocal.labels)). ss.
        rewrite List.app_length. ss. }
      i. destruct (length (ALocal.labels alc1) =? ALocal.next_eid alc1) eqn:Heq; cycle 1.
      { rewrite Nat.eqb_neq in Heq. unfold ALocal.next_eid in Heq. ss. }
      rewrite W2 in x1. inv x1. ss.
    - inv H0. auto. }
Qed.
