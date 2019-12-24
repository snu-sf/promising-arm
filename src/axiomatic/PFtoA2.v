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

Set Implicit Arguments.


Inductive co_gen (ws: IdMap.t (list (nat -> option (Loc.t * Time.t)))) (eid1 eid2: eidT): Prop :=
| co_gen_intro
    w1 wl1 ts1 loc1 w2 wl2 ts2 loc2
    (WS1: IdMap.find (fst eid1) ws = Some (w1::wl1))
    (W1: w1 (snd eid1) = Some (loc1, ts1))
    (WS2: IdMap.find (fst eid2) ws = Some (w2::wl2))
    (W2: w2 (snd eid2) = Some (loc2, ts2))
    (LOC: loc1 = loc2)
    (TS: Time.lt ts1 ts2)
.

Inductive rf_gen (ws: IdMap.t (list (nat -> option (Loc.t * Time.t)))) (rs: IdMap.t (list (nat -> option (Loc.t *Time.t)))) (eid1 eid2: eidT): Prop :=
| rf_gen_intro
    w wl ts1 loc1 r rl loc2 ts2
    (WS: IdMap.find (fst eid1) ws = Some (w::wl))
    (W: w (snd eid1) = Some (loc1, ts1))
    (RS: IdMap.find (fst eid2) rs = Some (r::rl))
    (R: r (snd eid2) = Some (loc2, ts2))
    (LOC: loc1 = loc2)
    (TS: ts1 = ts2)
.

Definition v_gen (vs: IdMap.t (list (nat -> Time.t))) (eid: eidT): Time.t :=
  match IdMap.find (fst eid) vs with
  | Some (v::vl) => v (snd eid)
  | _ => Time.bot
  end
.

Lemma sim_traces_co1
      p mem trs atrs rs ws covs vexts ex
      (PRE: Valid.pre_ex p ex)
      (SIM: sim_traces p mem trs atrs ws rs covs vexts)
      (ATR: IdMap.Forall2
              (fun tid atr aeu => exists l, atr = aeu :: l)
              atrs PRE.(Valid.aeus)):
  forall eid1 eid2,
    (exists loc
        ex1 ord1 val1
        ex2 ord2 val2,
        <<LABEL: Execution.label eid1 ex = Some (Label.write ex1 ord1 loc val1)>> /\
        <<LABEL: Execution.label eid2 ex = Some (Label.write ex2 ord2 loc val2)>>) ->
    (eid1 = eid2 \/ (co_gen ws) eid1 eid2 \/ (co_gen ws) eid2 eid1).
Proof.
  i. des. destruct PRE, ex. unfold Execution.label in *. ss.
  destruct eid1 as [tid1 eid1], eid2 as [tid2 eid2]. ss.
  destruct (IdMap.find tid1 labels) eqn:FIND1, (IdMap.find tid2 labels) eqn:FIND2; ss.
  subst. rewrite IdMap.map_spec in *.
  generalize (ATR tid1). intro ATR1.
  generalize (ATR tid2). intro ATR2.
  generalize (SIM tid1). intro SIM1. inv SIM1.
  { inv ATR1; try congr. rewrite <- H7 in FIND1. ss. }
  generalize (SIM tid2). intro SIM2. inv SIM2.
  { inv ATR2; try congr. rewrite <- H13 in FIND2. ss. }
  inv ATR1; inv ATR2; try congr. des.
  rewrite <- H13 in *. rewrite <- H15 in *. ss.
  inv FIND1. inv FIND2.
  exploit sim_trace_last; try exact REL6; eauto. i. des. simplify.
  exploit sim_trace_last; try exact REL0; eauto. i. des. simplify.
  exploit sim_trace_sim_th; try exact REL6; eauto. intro TH1.
  exploit sim_trace_sim_th; try exact REL0; eauto. intro TH2.
  exploit TH1.(WPROP2); try exact LABEL; eauto. intro W1. des.
  exploit TH2.(WPROP2); try exact LABEL0; eauto. intro W2. des.
  destruct (Id.eq_dec tid1 tid2); subst; simplify.
  - specialize (Nat.lt_trichotomy ts ts0). i. des; subst.
    + right. left. econs; eauto.
    + exploit TH1.(WPROP4); [exact W1|exact W2|..]. auto.
    + right. right. econs; eauto.
  - specialize (Nat.lt_trichotomy ts ts0). i. des; subst.
    + right. left. econs; eauto.
    + congr.
    + right. right. econs; eauto.
Qed.

Lemma sim_traces_co2
      p mem trs atrs rs ws covs vexts ex
      (PRE: Valid.pre_ex p ex)
      (SIM: sim_traces p mem trs atrs ws rs covs vexts)
      (ATR: IdMap.Forall2
              (fun tid atr aeu => exists l, atr = aeu :: l)
              atrs PRE.(Valid.aeus)):
  forall eid1 eid2,
    (co_gen ws) eid1 eid2 ->
    exists loc
       ex1 ord1 val1
       ex2 ord2 val2,
      <<LABEL: Execution.label eid1 ex = Some (Label.write ex1 ord1 loc val1)>> /\
      <<LABEL: Execution.label eid2 ex = Some (Label.write ex2 ord2 loc val2)>>.
Proof.
  i. destruct PRE, ex. unfold Execution.label in *. ss.
  destruct eid1 as [tid1 eid1], eid2 as [tid2 eid2]. inv H. ss.
  generalize (SIM tid1). intro SIM1. inv SIM1; try congr.
  generalize (SIM tid2). intro SIM2. inv SIM2; try congr.
  generalize (ATR tid1). intro ATR1. inv ATR1; try congr.
  generalize (ATR tid2). intro ATR2. inv ATR2; try congr.
  des. simplify.
  repeat rewrite IdMap.map_spec.
  rewrite <- H13. rewrite <- H15. ss.
  exploit sim_trace_last; try exact REL6; eauto. i. des. simplify.
  exploit sim_trace_last; try exact REL0; eauto. i. des. simplify.
  exploit sim_trace_sim_th; try exact REL6; eauto. intro TH1.
  exploit sim_trace_sim_th; try exact REL0; eauto. intro TH2.
  exploit TH1.(WPROP3); eauto. i. des.
  exploit TH2.(WPROP3); eauto. i. des.
  esplits; eauto.
Qed.

Lemma sim_traces_rf1_aux
      p trs atrs rs ws covs vexts ex m
      (STEP: Machine.pf_exec p m)
      (PRE: Valid.pre_ex p ex)
      (NOPROMISE: Machine.no_promise m)
      (SIM: sim_traces p m.(Machine.mem) trs atrs ws rs covs vexts)
      (TR: IdMap.Forall2
             (fun tid tr sl => exists l, tr = (ExecUnit.mk (fst sl) (snd sl) m.(Machine.mem)) :: l)
             trs m.(Machine.tpool))
      (ATR: IdMap.Forall2
              (fun tid atr aeu => exists l, atr = aeu :: l)
              atrs PRE.(Valid.aeus)):
  forall eid1 ex1 ord1 loc val
     (LABEL: Execution.label eid1 ex = Some (Label.read ex1 ord1 loc val)),
    (<<NORF: ~ codom_rel (rf_gen ws rs) eid1>> /\ <<VAL: val = Val.default >> /\
     <<R: exists r rl loc, IdMap.find (fst eid1) rs = Some (r::rl) /\ r (snd eid1) = Some (loc, Time.bot)>>) \/
    (exists eid2 ex2 ord2,
        <<LABEL: Execution.label eid2 ex = Some (Label.write ex2 ord2 loc val)>> /\
        <<RF: (rf_gen ws rs) eid2 eid1>>).
Proof.
  i. destruct eid1 as [tid1 eid1].
  destruct PRE, ex. unfold Execution.label in *. ss.
  rewrite LABELS in *. rewrite IdMap.map_spec in *.
  destruct (IdMap.find tid1 aeus) eqn:FIND1; ss.
  generalize (ATR tid1). intro ATR1. inv ATR1; try congr.
  generalize (SIM tid1). intro SIM1. inv SIM1; try congr.
  des. simplify.
  exploit sim_trace_last; eauto. i. des. simplify.
  exploit sim_trace_sim_th; eauto. intro TH.
  (* exploit r_property; eauto. i. des. simplify. *)
  exploit TH.(RPROP1); eauto. i. des. unguardH x1. des.
  - left. esplits; subst; eauto.
    ii. inv H. inv H1.
    destruct x as [tid2 eid2]. ss. simplify.
    rewrite R in x0. inv x0.
    generalize (SIM tid2). intro SIM1. inv SIM1; try congr.
    simplify.
    exploit sim_trace_last; try exact REL0; eauto. i. des. simplify.
    exploit sim_trace_sim_th; try exact REL0; eauto. intro TH'.
    exploit TH'.(WPROP3); eauto. i. des.
    unfold Memory.get_msg in x0. ss.
  - right. exploit sim_traces_memory; eauto. i. des.
    generalize (TR tid'). intro TR2. inv TR2; try congr.
    generalize (SIM tid'). intro SIM2. inv SIM2; try congr.
    des. simplify.
    exploit sim_trace_last; try exact REL0; eauto. i. des. simplify.
    exploit sim_trace_sim_th; try exact REL0; eauto. intro TH'.
    exploit TH'.(WPROP1); eauto. i. des; ss.
    + destruct b. ss. inv NOPROMISE.
      exploit PROMISES; eauto. i. rewrite x in x3.
      rewrite Promises.lookup_bot in x3. ss.
    + generalize (ATR tid'). intro ATR2. inv ATR2; try congr.
      des. simplify. eexists (tid', eid). esplits; ss.
      * rewrite IdMap.map_spec. rewrite <- H8. ss. eauto.
      * econs; eauto.
Qed.

Lemma sim_traces_rf1
      p trs atrs rs ws covs vexts ex m
      (ETEP: Machine.pf_exec p m)
      (PRE: Valid.pre_ex p ex)
      (NOPROMISE: Machine.no_promise m)
      (SIM: sim_traces p m.(Machine.mem) trs atrs ws rs covs vexts)
      (TR: IdMap.Forall2
             (fun tid tr sl => exists l, tr = (ExecUnit.mk (fst sl) (snd sl) m.(Machine.mem)) :: l)
             trs m.(Machine.tpool))
      (ATR: IdMap.Forall2
              (fun tid atr aeu => exists l, atr = aeu :: l)
              atrs PRE.(Valid.aeus)):
  forall eid1 ex1 ord1 loc val
     (LABEL: Execution.label eid1 ex = Some (Label.read ex1 ord1 loc val)),
    (<<NORF: ~ codom_rel (rf_gen ws rs) eid1>> /\ <<VAL: val = Val.default >>) \/
    (exists eid2 ex2 ord2,
        <<LABEL: Execution.label eid2 ex = Some (Label.write ex2 ord2 loc val)>> /\
        <<RF: (rf_gen ws rs) eid2 eid1>>).
Proof.
  ii. exploit sim_traces_rf1_aux; eauto. i. des.
  - left. esplits; eauto.
  - right. esplits; eauto.
Qed.

Lemma sim_traces_rf2
      p mem trs atrs rs ws covs vexts ex
      (PRE: Valid.pre_ex p ex)
      (SIM: sim_traces p mem trs atrs ws rs covs vexts)
      (ATR: IdMap.Forall2
              (fun tid atr aeu => exists l, atr = aeu :: l)
              atrs PRE.(Valid.aeus)):
  forall eid1 eid2 (RF: (rf_gen ws rs) eid2 eid1),
  exists ex1 ex2 ord1 ord2 loc val,
    <<READ: Execution.label eid1 ex = Some (Label.read ex1 ord1 loc val)>> /\
    <<WRITE: Execution.label eid2 ex = Some (Label.write ex2 ord2 loc val)>>.
Proof.
  i. inv RF. destruct eid1 as [tid1 eid1], eid2 as [tid2 eid2]. ss.
  generalize (SIM tid1). intro SIM1. inv SIM1; try congr.
  generalize (SIM tid2). intro SIM2. inv SIM2; try congr.
  simplify.
  exploit sim_trace_last; try exact REL0; eauto. i. des. simplify.
  exploit sim_trace_sim_th; try exact REL0; eauto. intro TH1.
  exploit sim_trace_last; try exact REL6; eauto. i. des. simplify.
  exploit sim_trace_sim_th; try exact REL6; eauto. intro TH2.
  exploit TH1.(WPROP3); eauto. i. des.
  exploit TH2.(RPROP2); eauto. i. des. unguardH x9. des; subst; ss.
  { rewrite x9 in *. unfold Time.lt in x0. lia. }
  rewrite x9 in x5. inv x5.
  generalize (ATR tid1). intro ATR1. inv ATR1; try congr.
  generalize (ATR tid2). intro ATR2. inv ATR2; try congr.
  des. simplify. destruct PRE, ex. unfold Execution.label. ss.
  rewrite LABELS. repeat rewrite IdMap.map_spec.
  rewrite <- H8. rewrite <- H13. ss. esplits; eauto.
Qed.

Lemma sim_traces_rf_wf
      p mem trs atrs rs ws covs vexts
      (SIM: sim_traces p mem trs atrs ws rs covs vexts):
  functional (rf_gen ws rs)⁻¹.
Proof.
  ii. inv H. inv H0.
  destruct y as [tid1 eid1], z as [tid2 eid2]. ss.
  simplify. rewrite R in R0. inv R0.
  destruct (Id.eq_dec tid1 tid2); subst; simplify.
  - specialize (SIM tid2). inv SIM; try congr.
    exploit sim_trace_last; eauto. i. des. simplify.
    exploit sim_trace_sim_th; eauto. intro TH.
    exploit TH.(WPROP4); [exact W|exact W0|..]. i. subst. refl.
  - generalize (SIM tid1). intro SIM1. inv SIM1; try congr.
    generalize (SIM tid2). intro SIM2. inv SIM2; try congr.
    exploit sim_trace_last; try exact REL6; eauto. i. des. simplify.
    exploit sim_trace_sim_th; try exact REL6; eauto. intro TH1.
    exploit sim_trace_last; try exact REL0; eauto. i. des. simplify.
    exploit sim_trace_sim_th; try exact REL0; eauto. intro TH2.
    simplify.
    exploit TH1.(WPROP3); eauto. i. des.
    exploit TH2.(WPROP3); eauto. i. des.
    congr.
Qed.

Lemma sim_traces_cov_co
      p mem trs atrs ws rs covs vexts
      ex
      (SIM: sim_traces p mem trs atrs ws rs covs vexts)
      (CO: ex.(Execution.co) = co_gen ws):
  <<CO:
    forall eid1 eid2
      (CO: ex.(Execution.co) eid1 eid2),
      Time.lt ((v_gen covs) eid1) ((v_gen covs) eid2)>>.
Proof.
  ii. rewrite CO in *. inv CO0.
  destruct eid1 as [tid1 eid1], eid2 as [tid2 eid2]. ss.
  generalize (SIM tid1). intro SIM1. inv SIM1; try congr.
  generalize (SIM tid2). intro SIM2. inv SIM2; try congr. simplify.
  exploit sim_trace_last; try exact REL6; eauto. i. des. simplify.
  exploit sim_trace_sim_th; try exact REL6; eauto. intro TH1.
  exploit sim_trace_last; try exact REL0; eauto. i. des. simplify.
  exploit sim_trace_sim_th; try exact REL0; eauto. intro TH2.
  exploit TH1.(WPROP3); eauto. i. des.
  exploit TH2.(WPROP3); eauto. i. des.
  unfold v_gen. ss. subst. rewrite <- H4, <- H10. ss.
Qed.

Lemma sim_traces_cov_rf
      p mem trs atrs ws rs covs vexts
      ex
      (SIM: sim_traces p mem trs atrs ws rs covs vexts)
      (RF: ex.(Execution.rf) = rf_gen ws rs):
  <<RF:
    forall eid1 eid2
      (RF: ex.(Execution.rf) eid1 eid2),
      Time.eq ((v_gen covs) eid1) ((v_gen covs) eid2)>>.
Proof.
  ii. rewrite RF in *. inv RF0.
  destruct eid1 as [tid1 eid1], eid2 as [tid2 eid2]. ss.
  generalize (SIM tid1). intro SIM1. inv SIM1; try congr.
  generalize (SIM tid2). intro SIM2. inv SIM2; try congr. simplify.
  exploit sim_trace_last; try exact REL6; eauto. i. des. simplify.
  exploit sim_trace_sim_th; try exact REL6; eauto. intro TH1.
  exploit sim_trace_last; try exact REL0; eauto. i. des. simplify.
  exploit sim_trace_sim_th; try exact REL0; eauto. intro TH2.
  exploit TH1.(WPROP3); eauto. i. des.
  exploit TH2.(RPROP2); eauto. i. des.
  unfold v_gen. ss. subst. rewrite <- H4, <- H10. ss.
Qed.

Lemma sim_traces_cov_fr
      p trs atrs ws rs covs vexts
      ex m
      (STEP: Machine.pf_exec p m)
      (SIM: sim_traces p m.(Machine.mem) trs atrs ws rs covs vexts)
      (CO: ex.(Execution.co) = co_gen ws)
      (RF: ex.(Execution.rf) = rf_gen ws rs)
      (PRE: Valid.pre_ex p ex)
      (NOPROMISE: Machine.no_promise m)
      (TR: IdMap.Forall2
             (fun tid tr sl => exists l, tr = (ExecUnit.mk (fst sl) (snd sl) m.(Machine.mem)) :: l)
             trs m.(Machine.tpool))
      (ATR: IdMap.Forall2
              (fun tid atr aeu => exists l, atr = aeu :: l)
              atrs PRE.(Valid.aeus)):
  <<FR:
    forall eid1 eid2
      (FR: Execution.fr ex eid1 eid2),
      Time.lt ((v_gen covs) eid1) ((v_gen covs) eid2)>>.
Proof.
  ii. inv FR.
  - inv H. des.
    exploit sim_traces_cov_co; eauto. i.
    exploit sim_traces_cov_rf; eauto. i.
    rewrite <- x2. auto.
  - inv H. inv H1. inv H. inv H1. destruct l; ss.
    exploit sim_traces_rf1_aux; eauto. i. des.
    + inv H2. destruct l; ss. destruct PRE.
      unfold Execution.label in EID0.
      rewrite LABELS in EID0. rewrite IdMap.map_spec in EID0.
      destruct eid1 as [tid1 eid1], eid2 as [tid2 eid2]. ss.
      destruct (IdMap.find tid2 aeus) eqn:FIND2; ss.
      generalize (ATR tid2). intro ATR2. inv ATR2; try congr. des. simplify.
      generalize (SIM tid2). intro SIM2. inv SIM2; try congr. simplify.
      exploit sim_trace_last; try exact REL6; eauto. i. des. simplify.
      exploit sim_trace_sim_th; try exact REL6; eauto. intro TH1.
      exploit TH1.(WPROP2); eauto. i. des.
      exploit TH1.(WPROP3); eauto. i. des.
      generalize (SIM tid1). intro SIM1. inv SIM1; try congr. simplify.
      exploit sim_trace_last; try exact REL0; eauto. i. des. simplify.
      exploit sim_trace_sim_th; try exact REL0; eauto. intro TH2.
      exploit TH1.(WPROP3); eauto. i. des.
      exploit TH2.(RPROP2); eauto. i. des.
      unfold v_gen. ss. subst. rewrite <- H12, <- H7, x13. ss.
    + exfalso.
      rewrite RF in *. eapply H3. unfold codom_rel.
      eexists. eauto.
Qed.

Lemma sim_traces_cov_po_loc
      p mem trs atrs ws rs covs vexts
      ex
      (SIM: sim_traces p mem trs atrs ws rs covs vexts)
      (PRE: Valid.pre_ex p ex)
      (ATR: IdMap.Forall2
              (fun tid atr aeu => exists l, atr = aeu :: l)
              atrs PRE.(Valid.aeus)):
  forall eid1 eid2 (PO_LOC: Execution.po_loc ex eid1 eid2),
     <<PO_LOC_WRITE:
       ex.(Execution.label_is) Label.is_write eid2 ->
       Time.lt ((v_gen covs) eid1) ((v_gen covs) eid2)>> /\
     <<PO_LOC_READ:
       ex.(Execution.label_is) Label.is_read eid2 ->
       Time.le ((v_gen covs) eid1) ((v_gen covs) eid2)>>.
Proof.
  i. destruct eid1 as [tid1 iid1], eid2 as [tid2 iid2]. inv PO_LOC. inv H. ss. subst.
  inv H0. unfold Execution.label in *. ss. rewrite PRE.(Valid.LABELS), IdMap.map_spec in *.
  generalize (ATR tid2). intro X. inv X; ss; rewrite <- H in *; ss.
  des. subst. generalize (SIM tid2). i. inv H1; simplify.
  exploit sim_trace_last; eauto. i. des. subst. simplify.
  exploit sim_trace_sim_th; eauto. intro TH.
  exploit TH.(PO); eauto. i. des.
  unfold v_gen. s. rewrite <- H7. splits; i.
  - inv H1. unfold Execution.label in *. ss.
    rewrite PRE.(Valid.LABELS), IdMap.map_spec, <- H in *. inv EID.
    rewrite EID2 in H2. inv H2. eauto.
  - inv H1. unfold Execution.label in *. ss.
    rewrite PRE.(Valid.LABELS), IdMap.map_spec, <- H in *. inv EID.
    rewrite EID2 in H2. inv H2. eauto.
Qed.

Lemma sim_traces_vext_co
      p mem trs atrs ws rs covs vexts
      ex
      (SIM: sim_traces p mem trs atrs ws rs covs vexts)
      (CO: ex.(Execution.co) = co_gen ws):
  <<CO:
    forall eid1 eid2
      (CO: ex.(Execution.co) eid1 eid2),
      Time.lt ((v_gen vexts) eid1) ((v_gen vexts) eid2)>>.
Proof.
  ii. rewrite CO in *. inv CO0.
  destruct eid1 as [tid1 eid1], eid2 as [tid2 eid2]. ss.
  generalize (SIM tid1). intro SIM1. inv SIM1; try congr.
  generalize (SIM tid2). intro SIM2. inv SIM2; try congr. simplify.
  exploit sim_trace_last; try exact REL6; eauto. i. des. simplify.
  exploit sim_trace_sim_th; try exact REL6; eauto. intro TH1.
  exploit sim_trace_last; try exact REL0; eauto. i. des. simplify.
  exploit sim_trace_sim_th; try exact REL0; eauto. intro TH2.
  exploit TH1.(WPROP3); eauto. i. des.
  exploit TH2.(WPROP3); eauto. i. des.
  unfold v_gen. ss. subst. rewrite <- H5, <- H11, x2, x8. ss.
Qed.

Lemma sim_trace_lastn
      p mem tid tr atr wl rl covl vextl
      n
      (SIM: sim_trace p mem tid tr atr wl rl covl vextl):
  sim_trace p mem tid
            (lastn (S n) tr) (lastn (S n) atr) (lastn (S n) wl)
            (lastn (S n) rl) (lastn (S n) covl) (lastn (S n) vextl).
Proof.
  revert n atr wl rl covl vextl SIM. induction tr; i; [by inv SIM|].
  exploit sim_trace_length; eauto. s. i. des.
  destruct (le_lt_dec (length tr) n).
  { rewrite ? lastn_all in *; ss; try lia. }
  exploit sim_trace_last; eauto. i. des. simplify. ss.
  rewrite ? lastn_cons; try lia. eapply IHtr.
  inv SIM; ss. lia.
Qed.

Inductive sim_ex tid ex (ws rs:IdMap.t (list (nat -> option (Loc.t * Time.t)))) covs vexts aeu w r cov vext: Prop := {
  LABELS:
    forall eid label
      (EID: eid < List.length aeu.(AExecUnit.local).(ALocal.labels))
      (LABEL: Execution.label (tid, eid) ex = Some label),
      List.nth_error aeu.(AExecUnit.local).(ALocal.labels) eid = Some label;
  ADDR:
    forall eid1 eid2
      (EID2: eid2 < List.length aeu.(AExecUnit.local).(ALocal.labels))
      (ADDR: ex.(Execution.addr) (tid, eid1) (tid, eid2)),
      aeu.(AExecUnit.local).(ALocal.addr) eid1 eid2;
  DATA:
    forall eid1 eid2
      (EID2: eid2 < List.length aeu.(AExecUnit.local).(ALocal.labels))
      (DATA: ex.(Execution.data) (tid, eid1) (tid, eid2)),
      aeu.(AExecUnit.local).(ALocal.data) eid1 eid2;
  CTRL:
    forall eid1 eid2
      (EID2: eid2 < List.length aeu.(AExecUnit.local).(ALocal.labels))
      (CTRL: ex.(Execution.ctrl0) (tid, eid1) (tid, eid2)),
      aeu.(AExecUnit.local).(ALocal.ctrl) eid1 eid2;
  RMW:
    forall eid1 eid2
      (EID2: eid2 < List.length aeu.(AExecUnit.local).(ALocal.labels))
      (ADDR: ex.(Execution.rmw) (tid, eid1) (tid, eid2)),
      aeu.(AExecUnit.local).(ALocal.rmw) eid1 eid2;
  XCOV:
    forall eid
      (EID: eid < List.length aeu.(AExecUnit.local).(ALocal.labels)),
      (v_gen covs) (tid, eid) = cov eid;
  XVEXT:
    forall eid
      (EID: eid < List.length aeu.(AExecUnit.local).(ALocal.labels)),
      (v_gen vexts) (tid, eid) = vext eid;
  XW:
    forall eid w0 wl
      (EID: eid < List.length aeu.(AExecUnit.local).(ALocal.labels))
      (W: IdMap.find tid ws = Some (w0::wl)),
      w0 eid = w eid;
  XR:
    forall eid r0 rl
      (EID: eid < List.length aeu.(AExecUnit.local).(ALocal.labels))
      (R: IdMap.find tid rs = Some (r0::rl)),
      r0 eid = r eid;

  LABELS_REV:
    forall eid label
      (LABEL: List.nth_error aeu.(AExecUnit.local).(ALocal.labels) eid = Some label),
      Execution.label (tid, eid) ex = Some label;
  ADDR_REV:
    forall eid1 eid2
      (ADDR: aeu.(AExecUnit.local).(ALocal.addr) eid1 eid2),
      ex.(Execution.addr) (tid, eid1) (tid, eid2);
  DATA_REV:
    forall eid1 eid2
      (DATA: aeu.(AExecUnit.local).(ALocal.data) eid1 eid2),
      ex.(Execution.data) (tid, eid1) (tid, eid2);
  CTRL_REV:
    forall eid1 eid2
      (CTRL: aeu.(AExecUnit.local).(ALocal.ctrl) eid1 eid2),
      ex.(Execution.ctrl0) (tid, eid1) (tid, eid2);
  RMW_REV:
    forall eid1 eid2
      (RMW: aeu.(AExecUnit.local).(ALocal.rmw) eid1 eid2),
      ex.(Execution.rmw) (tid, eid1) (tid, eid2);
}.

Lemma sim_traces_sim_ex_step
      p trs atrs ws rs covs vexts
      mem ex
      (SIM: sim_traces p mem trs atrs ws rs covs vexts)
      (PRE: Valid.pre_ex p ex)
      (ATR: IdMap.Forall2
              (fun _ atr aeu => exists l, atr = aeu :: l)
              atrs (Valid.aeus PRE)):
  forall tid atr wl rl covl vextl
    n aeu1 aeu2 atr' w2 w1 wl' r2 r1 rl' cov1 cov2 covl' vext1 vext2 vextl'
    (FIND_ATR: IdMap.find tid atrs = Some atr)
    (FIND_WL: IdMap.find tid ws = Some wl)
    (FIND_RL: IdMap.find tid rs = Some rl)
    (FIND_COVL: IdMap.find tid covs = Some covl)
    (FIND_VEXTL: IdMap.find tid vexts = Some vextl)
    (AEU: lastn (S n) atr = aeu2 :: aeu1 :: atr')
    (W: lastn (S n) wl = w2 :: w1 :: wl')
    (R: lastn (S n) rl = r2 :: r1 :: rl')
    (COV: lastn (S n) covl = cov2 :: cov1 :: covl')
    (VEXT: lastn (S n) vextl = vext2 :: vext1 :: vextl')
    (SIM_EX: sim_ex tid ex ws rs covs vexts aeu2 w2 r2 cov2 vext2),
    sim_ex tid ex ws rs covs vexts aeu1 w1 r1 cov1 vext1.
Proof.
  i. rename SIM_EX into L.
  generalize (SIM tid). intro X. inv X; simplify.
  destruct n.
  { generalize (lastn_length 1 atr). rewrite AEU. destruct atr; ss. }
  exploit sim_trace_lastn; eauto. instantiate (1 := S n). intro SIMTR.
  inv SIMTR.
  { rewrite AEU in H. inv H. }
  repeat match goal with
         | [H1: lastn ?a ?b = ?c, H2: ?d = lastn ?a ?b |- _] =>
           rewrite H1 in H2; inv H2
         end.
  destruct aeu1 as [ast1 alc1].
  destruct aeu2 as [ast2 alc2].
  inv ASTATE_STEP; ss; inv ALOCAL_STEP; inv EVENT0; ss; inv EVENT.
  Ltac tac :=
    repeat
      (try match goal with
           | [|- context[length (_ ++ _)]] => rewrite List.app_length
           | [H: List.nth_error (_ ++ [_]) _ = Some _ |- _] =>
             apply nth_error_snoc_inv in H; des
           end;
       ss; subst; unfold ALocal.next_eid in *; eauto; i).
  all: destruct L; econs; tac.
  all: try match goal with
             [|- List.nth_error _ _ = Some _] => try by exploit LABELS0; eauto; tac; lia
           end.
  all: try match goal with
           | [|- ALocal.addr _ _ _] => try by exploit ADDR0; eauto; tac; lia
           | [|- ALocal.data _ _ _] => try by exploit DATA0; eauto; tac; lia
           | [|- ALocal.ctrl _ _ _] => try by exploit CTRL0; eauto; tac; lia
           | [|- ALocal.rmw _ _ _] => try by exploit RMW0; eauto; tac; lia
           | [|- v_gen _ _ = _] => try by erewrite XCOV0; eauto; tac; lia
           | [|- _ _ = _ _] => try by erewrite XW0; eauto; tac; lia
           end.
  - exploit ADDR0; eauto; tac; try lia.
    inv x; ss. inv H. lia.
  - rewrite XCOV0; eauto; tac; try lia.
    condtac; ss. apply Nat.eqb_eq in X. lia.
  - rewrite XVEXT0; eauto; tac; try lia.
    condtac; ss. apply Nat.eqb_eq in X. lia.
  - erewrite XR0; eauto; tac; try lia.
    condtac; ss. apply Nat.eqb_eq in X. lia.
  - eapply LABELS_REV0; eauto. apply nth_error_app_mon. ss.
  - eapply ADDR_REV0; eauto. left. ss.
  - exploit ADDR0; eauto; tac; try lia.
    inv x; ss. inv H. lia.
  - exploit DATA0; eauto; tac; try lia.
    inv x; ss. inv H. lia.
  - exploit RMW0; eauto; tac; try lia.
    inv x; ss. destruct ex1; ss. inv H. lia.
  - rewrite XCOV0; eauto; tac; try lia.
    inv RES. destruct res1. ss. subst.
    condtac; ss. apply Nat.eqb_eq in X. lia.
  - rewrite XVEXT0; eauto; tac; try lia.
    inv RES. destruct res1. ss. subst.
    condtac; ss. apply Nat.eqb_eq in X. lia.
  - erewrite XW0; eauto; tac; try lia.
    inv RES. destruct res1. ss. subst.
    condtac; ss. apply Nat.eqb_eq in X. lia.
  - erewrite XR0; eauto; tac; try lia.
  - eapply LABELS_REV0; eauto. apply nth_error_app_mon. ss.
  - eapply ADDR_REV0; eauto. left. ss.
  - eapply DATA_REV0; eauto. left. ss.
  - eapply RMW_REV0; eauto. left. ss.
  - rewrite XCOV0; eauto; tac; try lia.
    inv RES. destruct res1. ss. subst. ss.
  - rewrite XVEXT0; eauto; tac; try lia.
    inv RES. destruct res1. ss. subst. ss.
  - erewrite XW0; eauto; tac; try lia.
    inv RES. destruct res1. ss. subst. ss.
  - rewrite XVEXT0; eauto; tac; try lia.
  - erewrite XR0; eauto; tac; try lia.
  - eapply LABELS_REV0; eauto. apply nth_error_app_mon. ss.
  - exploit CTRL0; eauto; tac; try lia.
    inv x; ss. inv H. lia.
  - rewrite XVEXT0; eauto; tac; try lia.
  - erewrite XR0; eauto; tac; try lia.
  - eapply LABELS_REV0; eauto. apply nth_error_app_mon. ss.
  - eapply CTRL_REV0; eauto. left. ss.
Qed.

Lemma sim_traces_sim_ex_aux
      p mem trs atrs ws rs covs vexts
      ex
      (SIM: sim_traces p mem trs atrs ws rs covs vexts)
      (PRE: Valid.pre_ex p ex)
      (ATR: IdMap.Forall2
              (fun _ atr aeu => exists l, atr = aeu :: l)
              atrs (Valid.aeus PRE)):
  forall tid atr wl rl covl vextl
    n aeu atr' w wl' r rl' cov covl' vext vextl'
    (N: n < length atr)
    (FIND_ATR: IdMap.find tid atrs = Some atr)
    (FIND_WL: IdMap.find tid ws = Some wl)
    (FIND_RL: IdMap.find tid rs = Some rl)
    (FIND_COVL: IdMap.find tid covs = Some covl)
    (FIND_VEXTL: IdMap.find tid vexts = Some vextl)
    (AEU: lastn (S n) atr = aeu :: atr')
    (W: lastn (S n) wl = w :: wl')
    (R: lastn (S n) rl = r :: rl')
    (COV: lastn (S n) covl = cov :: covl')
    (VEXT: lastn (S n) vextl = vext :: vextl'),
    sim_ex tid ex ws rs covs vexts aeu w r cov vext.
Proof.
  intros tid. generalize (SIM tid). intro X. inv X; [by i|].
  intros. remember (length atr - 1 - n) as n'.
  replace n with (length atr - 1 - n') in * by lia.
  assert (n' < length atr) by lia. clear Heqn' N n.
  move n' at top. revert_until H5. induction n'.
  { (* init *)
    i. simplify.
    exploit sim_trace_length; eauto. i. des.
    rewrite lastn_all in *; try lia. subst.
    econs.
    - i. revert LABEL.
      unfold Execution.label. s. rewrite PRE.(Valid.LABELS), IdMap.map_spec.
      destruct (IdMap.find tid (Valid.aeus PRE)) eqn:X; ss.
      generalize (ATR tid). rewrite X. intro Y. inv Y. des. subst.
      rewrite <- H7 in H. inv H. ss.
    - i. rewrite PRE.(Valid.ADDR) in ADDR0. inv ADDR0.
      rewrite IdMap.map_spec in RELS.
      destruct ((IdMap.find tid0 (Valid.aeus PRE))) eqn:X; ss.
      inv REL. inv RELS. ss.
      generalize (ATR tid). rewrite X. intro Y. inv Y. des. subst.
      rewrite <- H7 in H. inv H. ss.
    - i. rewrite PRE.(Valid.DATA) in DATA0. inv DATA0.
      rewrite IdMap.map_spec in RELS.
      destruct ((IdMap.find tid0 (Valid.aeus PRE))) eqn:X; ss.
      inv REL. inv RELS. ss.
      generalize (ATR tid). rewrite X. intro Y. inv Y. des. subst.
      rewrite <- H7 in H. inv H. ss.
    - i. rewrite PRE.(Valid.CTRL) in CTRL0. inv CTRL0.
      rewrite IdMap.map_spec in RELS.
      destruct ((IdMap.find tid0 (Valid.aeus PRE))) eqn:X; ss.
      inv REL. inv RELS. ss.
      generalize (ATR tid). rewrite X. intro Y. inv Y. des. subst.
      rewrite <- H7 in H. inv H. ss.
    - i. rewrite PRE.(Valid.RMW) in ADDR0. inv ADDR0.
      rewrite IdMap.map_spec in RELS.
      destruct ((IdMap.find tid0 (Valid.aeus PRE))) eqn:X; ss.
      inv REL. inv RELS. ss.
      generalize (ATR tid). rewrite X. intro Y. inv Y. des. subst.
      rewrite <- H7 in H. inv H. ss.
    - unfold v_gen. s. rewrite <- H4. ss.
    - unfold v_gen. s. rewrite <- H5. ss.
    - i. simplify. ss.
    - i. simplify. ss.
    - i. generalize (ATR tid). rewrite <- H. intro X. inv X. des. simplify.
      unfold Execution.label. s. rewrite PRE.(Valid.LABELS), IdMap.map_spec, <- H8. ss.
    - i. generalize (ATR tid). rewrite <- H. intro X. inv X. des. simplify.
      rewrite PRE.(Valid.ADDR). econs; eauto.  rewrite IdMap.map_spec. s. rewrite <- H8. ss.
    - i. generalize (ATR tid). rewrite <- H. intro X. inv X. des. simplify.
      rewrite PRE.(Valid.DATA). econs; eauto.  rewrite IdMap.map_spec. s. rewrite <- H8. ss.
    - i. generalize (ATR tid). rewrite <- H. intro X. inv X. des. simplify.
      rewrite PRE.(Valid.CTRL). econs; eauto.  rewrite IdMap.map_spec. s. rewrite <- H8. ss.
    - i. generalize (ATR tid). rewrite <- H. intro X. inv X. des. simplify.
      rewrite PRE.(Valid.RMW). econs; eauto.  rewrite IdMap.map_spec. s. rewrite <- H8. ss.
  }
  i. simplify.
  exploit sim_trace_length; eauto. intro LEN. guardH LEN.
  replace (S (length atr - 1 - S n')) with (S (length atr - S (S n'))) in * by lia.
  exploit sim_trace_lastn; eauto. instantiate (1 := (length atr - 1 - n')). i.
  exploit sim_trace_last; eauto. i. des.
  exploit IHn'; try exact HDTR; eauto; [lia|]. i.
  replace (S (length atr - 1 - n')) with (S (S (length atr - S (S n')))) in * by lia.
  exploit lastn_S1; try exact HDTR; [unguardH LEN; des; lia|i]. 
  exploit lastn_S1; try exact HDATR; [unguardH LEN; des; lia|i]. 
  exploit lastn_S1; try exact HDWL; [unguardH LEN; des; lia|i]. 
  exploit lastn_S1; try exact HDRL; [unguardH LEN; des; lia|i]. 
  exploit lastn_S1; try exact HDCOVL; [unguardH LEN; des; lia|i].
  exploit lastn_S1; try exact HDVEXTL; [unguardH LEN; des; lia|i].
  repeat match goal with
         | [H1: lastn ?a ?b = ?c, H2: lastn ?a ?b = ?d |- _] =>
           rewrite H1 in H2
         end.
  subst. eapply sim_traces_sim_ex_step; eauto.
Qed.

Lemma sim_traces_ex
      p mem trs atrs ws rs covs vexts
      ex
      tid n atr aeu atr' wl w wl' rl r rl' covl cov covl' vextl vext vextl'
      (SIM: sim_traces p mem trs atrs ws rs covs vexts)
      (PRE: Valid.pre_ex p ex)
      (ATR: IdMap.Forall2
              (fun _ atr aeu => exists l, atr = aeu :: l)
              atrs (Valid.aeus PRE))
      (FIND_ATR: IdMap.find tid atrs = Some atr)
      (FIND_WL: IdMap.find tid ws = Some wl)
      (FIND_RL: IdMap.find tid rs = Some rl)
      (FIND_COVL: IdMap.find tid covs = Some covl)
      (FIND_VEXTL: IdMap.find tid vexts = Some vextl)
      (AEU: lastn (S n) atr = aeu :: atr')
      (W: lastn (S n) wl = w :: wl')
      (R: lastn (S n) rl = r :: rl')
      (COV: lastn (S n) covl = cov :: covl')
      (VEXT: lastn (S n) vextl = vext :: vextl'):
  sim_ex tid ex ws rs covs vexts aeu w r cov vext.
Proof.
  generalize (SIM tid). intro X. inv X; simplify.
  exploit sim_trace_length; eauto. intro LEN. guardH LEN.
  exploit sim_trace_last; eauto. i. des. subst.
  destruct (le_lt_dec (length (aeu0::atr'0)) n).
  - rewrite lastn_all in *; ss; try by unguardH LEN; des; lia.
    simplify. eapply sim_traces_sim_ex_aux; eauto.
    1: instantiate (1 := length tr').
    all: ss.
    all: try apply lastn_all; ss; try by unguardH LEN; des; lia.
  - eapply sim_traces_sim_ex_aux; eauto.
Qed.
