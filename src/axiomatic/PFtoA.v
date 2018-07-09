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

Require Import PromisingArch.lib.Basic.
Require Import PromisingArch.lib.HahnRelationsMore.
Require Import PromisingArch.lib.Order.
Require Import PromisingArch.lib.Time.
Require Import PromisingArch.lib.Lang.
Require Import PromisingArch.promising.Promising.
Require Import PromisingArch.promising.StateExecFacts.
Require Import PromisingArch.axiomatic.Axiomatic.
Require Import PromisingArch.axiomatic.CommonAxiomatic.
Require Import PromisingArch.axiomatic.PFtoALocal.

Set Implicit Arguments.


Inductive co_gen (ws: IdMap.t (list (nat -> option (Loc.t * Time.t)))) (eid1 eid2: eidT): Prop :=
| co_gen_intro
    w1 wl1 ts1 loc1 w2 wl2 ts2 loc2
    (WS1: IdMap.find eid1.(fst) ws = Some (w1::wl1))
    (W1: w1 eid1.(snd) = Some (loc1, ts1))
    (WS2: IdMap.find eid2.(fst) ws = Some (w2::wl2))
    (W2: w2 eid2.(snd) = Some (loc2, ts2))
    (LOC: loc1 = loc2)
    (TS: Time.lt ts1 ts2)
.

Inductive rf_gen (ws: IdMap.t (list (nat -> option (Loc.t * Time.t)))) (rs: IdMap.t (list (nat -> option (Loc.t *Time.t)))) (eid1 eid2: eidT): Prop :=
| rf_gen_intro
    w wl ts1 loc1 r rl loc2 ts2
    (WS: IdMap.find eid1.(fst) ws = Some (w::wl))
    (W: w eid1.(snd) = Some (loc1, ts1))
    (RS: IdMap.find eid2.(fst) rs = Some (r::rl))
    (R: r eid2.(snd) = Some (loc2, ts2))
    (LOC: loc1 = loc2)
    (TS: ts1 = ts2)
.

Definition v_gen (vs: IdMap.t (list (nat -> Time.t))) (eid: eidT): Time.t :=
  match IdMap.find eid.(fst) vs with
  | Some (v::vl) => v eid.(snd)
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
             (fun tid tr sl => exists l, tr = (ExecUnit.mk sl.(fst) sl.(snd) m.(Machine.mem)) :: l)
             trs m.(Machine.tpool))
      (ATR: IdMap.Forall2
              (fun tid atr aeu => exists l, atr = aeu :: l)
              atrs PRE.(Valid.aeus)):
  forall eid1 ex1 ord1 loc val
     (LABEL: Execution.label eid1 ex = Some (Label.read ex1 ord1 loc val)),
    (<<NORF: ~ codom_rel (rf_gen ws rs) eid1>> /\ <<VAL: val = Val.default >> /\
     <<R: exists r rl loc, IdMap.find eid1.(fst) rs = Some (r::rl) /\ r eid1.(snd) = Some (loc, Time.bot)>>) \/
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
             (fun tid tr sl => exists l, tr = (ExecUnit.mk sl.(fst) sl.(snd) m.(Machine.mem)) :: l)
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
             (fun tid tr sl => exists l, tr = (ExecUnit.mk sl.(fst) sl.(snd) m.(Machine.mem)) :: l)
             trs m.(Machine.tpool))
      (ATR: IdMap.Forall2
              (fun tid atr aeu => exists l, atr = aeu :: l)
              atrs PRE.(Valid.aeus)):
  <<FR:
    forall eid1 eid2
      (FR: ex.(Execution.fr) eid1 eid2),
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
  forall eid1 eid2 (PO_LOC: ex.(Execution.po_loc) eid1 eid2),
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

Lemma sim_traces_ex
      p mem trs atrs ws rs covs vexts
      ex
      tid n atr aeu atr' covl cov covl' vextl vext vextl'
      (SIM: sim_traces p mem trs atrs ws rs covs vexts)
      (PRE: Valid.pre_ex p ex)
      (ATR: IdMap.Forall2
              (fun _ atr aeu => exists l, atr = aeu :: l)
              atrs (Valid.aeus PRE))
      (FIND_ATR: IdMap.find tid atrs = Some atr)
      (FIND_COVL: IdMap.find tid covs = Some covl)
      (FIND_VEXTL: IdMap.find tid vexts = Some vextl)
      (AEU: lastn (S n) atr = aeu :: atr')
      (COV: lastn (S n) covl = cov :: covl')
      (VEXT: lastn (S n) vextl = vext :: vextl'):
  <<LABELS:
    forall eid label
      (EID: eid < List.length aeu.(AExecUnit.local).(ALocal.labels))
      (LABEL: Execution.label (tid, eid) ex = Some label),
      List.nth_error aeu.(AExecUnit.local).(ALocal.labels) eid = Some label>> /\
  <<ADDR:
    forall eid1 eid2
      (EID2: eid2 < List.length aeu.(AExecUnit.local).(ALocal.labels))
      (ADDR: ex.(Execution.addr) (tid, eid1) (tid, eid2)),
      aeu.(AExecUnit.local).(ALocal.addr) eid1 eid2>> /\
  <<DATA:
    forall eid1 eid2
      (EID2: eid2 < List.length aeu.(AExecUnit.local).(ALocal.labels))
      (DATA: ex.(Execution.data) (tid, eid1) (tid, eid2)),
      aeu.(AExecUnit.local).(ALocal.data) eid1 eid2>> /\
  <<CTRL:
    forall eid1 eid2
      (EID2: eid2 < List.length aeu.(AExecUnit.local).(ALocal.labels))
      (CTRL: ex.(Execution.ctrl) (tid, eid1) (tid, eid2)),
      aeu.(AExecUnit.local).(ALocal.ctrl) eid1 eid2>> /\
  <<RMW:
    forall eid1 eid2
      (EID2: eid2 < List.length aeu.(AExecUnit.local).(ALocal.labels))
      (ADDR: ex.(Execution.rmw) (tid, eid1) (tid, eid2)),
      aeu.(AExecUnit.local).(ALocal.rmw) eid1 eid2>> /\
  <<COV:
    forall eid
      (EID: eid < List.length aeu.(AExecUnit.local).(ALocal.labels)),
      (v_gen covs) (tid, eid) = cov eid>> /\
  <<VEXT:
    forall eid
      (EID: eid < List.length aeu.(AExecUnit.local).(ALocal.labels)),
      (v_gen vexts) (tid, eid) = vext eid>>.
Proof.
Admitted.

Definition ob' (ex: Execution.t): relation eidT :=
  ex.(Execution.rfe) ∪ ex.(Execution.dob) ∪ ex.(Execution.aob) ∪ ex.(Execution.bob).

Ltac des_union :=
  repeat
    (try match goal with
         | [H: Execution.internal _ _ _ |- _] => inv H
         | [H: Execution.ob _ _ _ |- _] => inv H
         | [H: Execution.obs _ _ _ |- _] => inv H
         | [H: (_ ∪ _) _ _ |- _] => inv H
         end).

Lemma ob_ob'
      ex eid1 eid2:
  ex.(Execution.ob) eid1 eid2 <->
  (ex.(Execution.fr) ∪ ex.(Execution.co) ∪ ex.(ob')) eid1 eid2.
Proof.
  split; i.
  - des_union.
    + right. left. left. left. auto.
    + left. left. auto.
    + left. right. auto.
    + right. left. left. right. auto.
    + right. left. right. auto.
    + right. right. auto.
  - unfold ob' in *. des_union.
    + left. left. left. left. right. auto.
    + left. left. left. right. auto.
    + left. left. left. left. left. auto.
    + left. left. right. auto.
    + left. right. auto.
    + right. auto.
Qed.

Lemma nth_error_last A (l: list A) a n
      (N: Nat.eqb n (List.length l) = true):
  List.nth_error (l ++ [a]) n = Some a.
Proof.
Admitted.

Lemma nth_error_not_last A (l: list A) a b n
      (NTH: List.nth_error (l ++ [a]) n = Some b)
      (N: Nat.eqb n (List.length l) = false):
  n < List.length l.
Proof.
Admitted.

Lemma sim_traces_sim_eu
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
    n eu tr' aeu atr' cov covl' vext vextl'
    (FIND_TR: IdMap.find tid trs = Some tr)
    (FIND_ATR: IdMap.find tid atrs = Some atr)
    (FIND_COVL: IdMap.find tid covs = Some covl)
    (FIND_VEXTL: IdMap.find tid vexts = Some vextl)
    (EU: lastn (S n) tr = eu :: tr')
    (AEU: lastn (S n) atr = aeu :: atr')
    (COV: lastn (S n) covl = cov :: covl')
    (VEXT: lastn (S n) vextl = vext :: vextl'),
    <<SIM_EU: sim_eu tid ex (v_gen vexts) eu aeu>> /\
    <<OB_WRITE:
      forall eid1 eid2
        (LABEL: eid2 < List.length aeu.(AExecUnit.local).(ALocal.labels))
        (OB: ex.(ob') eid1 (tid, eid2))
        (EID2: ex.(Execution.label_is) Label.is_write (tid, eid2)),
        Time.lt ((v_gen vexts) eid1) (vext eid2)>> /\
    <<OB_READ:
      forall eid1 eid2
        (LABEL: eid2 < List.length aeu.(AExecUnit.local).(ALocal.labels))
        (AOB: ex.(ob') eid1 (tid, eid2))
        (EID2: ex.(Execution.label_is) Label.is_read (tid, eid2)),
        Time.le ((v_gen vexts) eid1) (vext eid2)>> /\
    <<FR:
      forall eid1 eid2
        (LABEL: eid1 < List.length aeu.(AExecUnit.local).(ALocal.labels))
        (FR: ex.(Execution.fr) (tid, eid1) eid2),
        Time.lt (vext eid1) ((v_gen vexts) eid2)>>.
Proof.
  rename STEP into MACHINE_STEP.
  i. generalize (SIM tid). intro X. inv X; simplify.
  revert eu aeu tr' atr' cov covl' vext vextl' EU AEU COV VEXT. induction n.
  { i.
    exploit (lastn_one tr).
    { exploit sim_trace_last; eauto. i. des. subst. ss. lia. }
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
  i. rename c into wl, d into rl.
  destruct (Nat.le_gt_cases (List.length tr) (S n)).
  { exploit sim_trace_length; eauto. i. des.
    rewrite lastn_all in EU; [|lia]. subst.
    rewrite lastn_all in AEU; [|lia]. subst.
    rewrite lastn_all in COV; [|lia]. subst.
    rewrite lastn_all in VEXT; [|lia]. subst.
    eapply IHn; apply lastn_all; lia. }
  exploit sim_trace_length; eauto. i. des.
  exploit (lastn_S (S n) wl); try rewrite LENGTH_WL; try lia. intro W. des.
  exploit (lastn_S (S n) rl); try rewrite LENGTH_RL; try lia. intro R. des.
  exploit lastn_S1; try exact EU; eauto. intro EU'.
  exploit lastn_S1; try exact AEU; try rewrite LENGTH_ATR; eauto. intro AEU'.
  exploit lastn_S1; try exact WL; try rewrite LENGTH_WL; eauto. intro W'.
  exploit lastn_S1; try exact RL; try rewrite LENGTH_RL; eauto. intro R'.
  exploit lastn_S1; try exact COV; try rewrite LENGTH_COVL; eauto. intro COV'.
  exploit lastn_S1; try exact VEXT; try rewrite LENGTH_VEXTL; eauto. intro VEXT'.
  exploit (lastn_S n tr); try lia. i. des.
  exploit (lastn_S n atr); try lia. i. des.
  exploit (lastn_S n wl); try lia. i. des.
  exploit (lastn_S n rl); try lia. i. des.
  exploit (lastn_S n covl); try lia. i. des.
  exploit (lastn_S n vextl); try lia. i. des.
  rewrite EU' in x0. rewrite x0 in *. clear x0 tr'.
  rewrite AEU' in x1. rewrite x1 in *. clear x1 atr'.
  rewrite W' in x2. rewrite x2 in *. clear x2 l'.
  rewrite R' in x3. rewrite x3 in *. clear x3 l'0.
  rewrite COV' in x4. rewrite x4 in *. clear x4 covl'.
  rewrite VEXT' in x5. rewrite x5 in *. clear x5 vextl'.
  rename a1 into eu1, l'1 into tr'.
  rename a2 into aeu1, l'2 into atr'.
  rename a into w, a3 into w1, l'3 into wl'.
  rename a0 into r, a4 into r1, l'4 into rl'.
  rename a5 into cov1, l'5 into covl'.
  rename a6 into vext1, l'6 into vextl'.
  exploit IHn; eauto. i. des.
  exploit sim_trace_lastn; try exact REL6; eauto.
  rewrite EU', AEU', W', R', COV', VEXT'. intro SIM1.
  exploit sim_trace_lastn; try exact REL6; eauto.
  rewrite EU, AEU, W, R, COV, VEXT. intro SIM2.
  exploit sim_traces_ex; try exact AEU'; eauto. i. des.
  exploit sim_traces_ex; try exact AEU; eauto. i. des.
  clear IHn. (* clear as much as possible *)
  match goal with
  | [|- _ /\ ?a /\ ?b /\ ?c] =>
    assert (OB_WRITE': a);
      [|assert (OB_READ': b);
        [|assert (FR': c)]]
  end.
  { (* OB WRITE *)
    
  (* OB_WRITE : forall (eid1 : eidT) (eid2 : nat), *)
  (*            eid2 < length (ALocal.labels (AExecUnit.local aeu1)) -> *)
  (*            ob' ex eid1 (tid, eid2) -> *)
  (*            Execution.label_is ex (fun label : Label.t => Label.is_write label) (tid, eid2) -> *)
  (*            Time.lt (v_gen vexts eid1) (vext1 eid2) *)


    admit.
  }
  { (* OB READ *)
    admit.
  }
  { (* FR *)
    ii. generalize FR0. intro X. inv X.
    - admit.
    - inv H0. inv H4. inv H0. inv H4.
      exploit LABELS0; eauto. intro LABEL1. destruct l; ss.
      exploit sim_trace_sim_th; try exact SIM2; eauto. i. destruct x0.
      exploit RPROP1; eauto. i. des. unguardH x0. des.
      + inv SIM2.
        rename LOCAL into SIM_LOCAL_WEAK.
        destruct eu1 as [st1 lc1 mem1], eu as [st2 lc2 mem2].
        destruct aeu1 as [ast1 alc1], aeu as [ast2 alc2].
        inv EVENT; ss.
        * eapply FR; eauto. inv ALOCAL_STEP; ss.
        * des_ifs; cycle 1.
          { eapply FR; eauto. inv ALOCAL_STEP; ss.
            eapply nth_error_not_last; eauto. }
          { inv STEP. ss. inv LOCAL; ss. inv STEP. inv EVENT. ss.
            rewrite fun_add_spec in H4.
            destruct (equiv_dec (ValA.val vloc) (ValA.val vloc)); try congr.
            admit.
          }
        * inv STEP. ss. inv LOCAL; ss; inv EVENT.
          { inv STEP. ss. inv ALOCAL_STEP; ss.
            - destruct (Nat.eqb eid1 (ALocal.next_eid alc1)) eqn:HEID1.
              + rewrite nth_error_last in LABEL1; auto. inv LABEL1.
              + eapply FR; eauto. eapply nth_error_not_last; eauto.
            - inv EVENT. inv RES. ss. }
          { inv STEP. ss. eapply FR; eauto. inv ALOCAL_STEP; ss.
            destruct (Nat.eqb eid1 (List.length (ALocal.labels alc1))) eqn:HEID1.
            - rewrite nth_error_last in LABEL1; eauto. inv LABEL1.
            - eapply nth_error_not_last; eauto. }
        * inv STEP. ss. inv LOCAL; ss; inv EVENT.
          { inv STEP. ss. eapply FR; eauto. inv ALOCAL_STEP; ss.
            destruct (Nat.eqb eid1 (List.length (ALocal.labels alc1))) eqn:HEID1.
            - rewrite nth_error_last in LABEL1; eauto. inv LABEL1.
            - eapply nth_error_not_last; eauto. }
          { inv STEP. ss. eapply FR; eauto. inv ALOCAL_STEP; ss.
            destruct (Nat.eqb eid1 (List.length (ALocal.labels alc1))) eqn:HEID1.
            - rewrite nth_error_last in LABEL1; eauto. inv LABEL1.
            - eapply nth_error_not_last; eauto. }
      + exploit sim_traces_memory; eauto. i. des.
        generalize (SIM tid'). intro SIM'. inv SIM'; try congr. simplify.
        exploit sim_trace_last; try exact REL0. i. des. subst.
        exploit sim_trace_sim_th; try exact REL0; eauto. i. destruct x3.
        exploit WPROP0; eauto. i. des.
        * inv MACHINE_STEP. inv NOPROMISE.
          generalize (TR tid'). intro TR'. inv TR'; try congr. des. simplify.
          destruct b. exploit PROMISES; eauto. i.
          ss. rewrite x4 in *. rewrite Promises.lookup_bot in x1. ss.
        * exfalso. apply H6. econs. rewrite RF.
          instantiate (1 := (tid', eid)).
          exploit sim_trace_last; try exact REL6. i. des. subst.
          econs; try refl; ss; eauto.
          admit. (* should prove that r includes r2 *)
  }
  splits; eauto.
  (* SIM_EU *)
  destruct eu1 as [[stmts1 rmap1] lc1 mem1].
  destruct aeu1 as [[astmts1 armap1] alc1].
  destruct eu as [[stmts2 rmap2] lc2 mem2].
  destruct aeu as [[astmts2 armap2] alc2].
  inv SIM2. rename LOCAL into SIM_LOCAL_WEAK.
  inv SIM_EU. inv STATE0. inv STATE. ss. subst.
  rename LOCAL into SIM_LOCAL. inv STEP. ss.
  inv EVENT; inv STATE; inv LOCAL; inv EVENT; inv ASTATE_STEP; inv ALOCAL_STEP; inv EVENT; ss.
  - (* skip *)
    econs; ss. inv LC. inv SIM_LOCAL. econs; ss.
    ii. etrans; [|eapply join_l]. eauto.
  - (* assign *)
    econs; ss.
    + econs; ss. apply sim_rmap_add; ss. apply sim_rmap_expr; ss.
    + inv LC. inv SIM_LOCAL. econs; ss.
      ii. etrans; [|eapply join_l]. eauto.
  - (* if *)
    econs; ss.
    inv LC. inv SIM_LOCAL. econs; ss.
    ii. etrans; [|eapply join_l]. eauto.
  - (* do while *)
    econs; ss.
    inv LC. inv SIM_LOCAL. econs; ss.
    ii. etrans; [|eapply join_l]. eauto.
  - (* read *)
    admit.
  - (* write success *)
    econs; ss.
    { econs; ss. apply sim_rmap_add; ss. inv STEP. econs; ss.
      ii. des. subst. destruct (equiv_dec arch riscv); ss. destruct eid. ss. subst.
      unfold ALocal.next_eid in *.
      rewrite VEXT1; cycle 1.
      { rewrite List.app_length. s. clear. lia. }
      condtac; cycle 1.
      { apply Nat.eqb_neq in X. ss. }
      rewrite fun_add_spec. condtac; ss.
      inv WRITABLE. apply Nat.lt_le_incl. ss.
    }
    admit.
  - (* write fail *)
    inv RES. inv STEP. ss.
  - (* write success *)
    inv RES. inv STEP. ss.
  - (* write fail *)
    inv STEP. econs; ss.
    + econs; ss. apply sim_rmap_add; ss. econs; ss. ii. des. ss.
    + inv SIM_LOCAL. econs; ss.
  - (* isb *)
    econs; ss.
    inv STEP. inv SIM_LOCAL. econs; ss.
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_coh_step. rewrite inverse_step.
      rewrite inverse_union. ii. des; [apply COH|]; eauto.
      inv EID. inv REL. inv H0. inv H1. inv H5.
      apply Label.is_writing_inv in LABEL. des. subst. inv H4.
      * exploit LABELS0; eauto; cycle 1.
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. }
        { rewrite List.app_length. s. lia. }
      * inv H0. exploit RF2; eauto. i. des.
        exploit LABELS0; eauto; cycle 1.
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. }
        { rewrite List.app_length. s. lia. }
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vrp_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VRP; eauto. i. rewrite <- join_l. ss.
      * inv EID. inv REL. inv H0. inv H4. inv H0. inv H5. inv H6.
        exploit LABELS0; eauto.
        { rewrite List.app_length. s. lia. }
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0. inv LABEL. }
      * inv EID. inv REL. inv H0. inv H4. inv H0. inv H5. inv H6.
        exploit LABELS0; eauto.
        { rewrite List.app_length. s. lia. }
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0. inv LABEL. }
      * inv EID. inv REL. inv H0. inv H4.
        rewrite <- join_r. apply VCAP. econs; eauto.
      * inv EID. inv REL. inv H1. destruct l; ss.
        exploit LABELS0; eauto; cycle 1.
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. }
        { rewrite List.app_length. s. lia. }
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vwp_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VWP; eauto.
      * inv EID. inv REL. inv H0. inv H4. inv H0. inv H5. inv H6.
        exploit LABELS0; eauto.
        { rewrite List.app_length. s. lia. }
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0. inv LABEL. }
      * inv EID. inv REL. inv H0. inv H4. inv H0. inv H5. inv H6.
        exploit LABELS0; eauto.
        { rewrite List.app_length. s. lia. }
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0. inv LABEL. }
      * inv EID. inv REL. inv H1. destruct l; ss.
        exploit LABELS0; eauto; cycle 1.
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. }
        { rewrite List.app_length. s. lia. }
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vrm_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VRM; eauto.
      * inv EID. inv REL. inv H1. destruct l; ss.
        exploit LABELS0; eauto.
        { rewrite List.app_length. s. lia. }
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. }
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vwm_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VWM; eauto.
      * inv EID. inv REL. inv H1. destruct l; ss.
        exploit LABELS0; eauto.
        { rewrite List.app_length. s. lia. }
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. }
    + rewrite List.app_length, Nat.add_1_r.
      ii. inv EID. inv REL.
      * admit. (* ctrl should be local *)
      * (* TODO: move *)
        Lemma addr_po_step ex:
          (ex.(Execution.addr) ⨾ Execution.po) =
          ((ex.(Execution.addr) ⨾ Execution.po) ∪ ex.(Execution.addr)) ⨾
          Execution.po_adj.
        Proof.
          rewrite ? (union_seq' Execution.po_adj), ? seq_assoc, ? union_assoc.
          rewrite Execution.po_po_adj at 1.
          rewrite (clos_refl_union Execution.po), union_seq, eq_seq.
          rewrite ? (seq_union' (Execution.po ⨾ Execution.po_adj) Execution.po_adj), ? seq_assoc, ? union_assoc.
          refl.
        Qed.
        
        rewrite addr_po_step in H0.
        
        (*TODO: move *)
        Lemma step r eid tid n:
          (r ⨾ Execution.po_adj) eid (tid, S n) = r eid (tid, n).
        Proof.
          propext. econs; i.
          - inv H. des. inv H1. destruct x. ss. inv N. auto.
          - econs. split; eauto.
        Qed.

        rewrite step in H0.
        inv H0.
        { eapply VCAP; eauto. econs; eauto. econs 2; eauto. }
        { (* TODO: move *)
          Lemma addr_eid
                p ex (PRE: Valid.pre_ex p ex)
                eid tid eid2
                (ADDR: ex.(Execution.addr) eid (tid, eid2)):
            exists eid1, eid = (tid, eid1).
          Proof.
          Admitted.

          exploit addr_eid; eauto. i. des. subst.
          exploit ADDR0; eauto.
          { rewrite List.app_length. ss. clear. lia. }
          i.

          (* TODO: move *)
          Lemma addr_inv
                p mem tid tr aeu atr wl rl covl vextl
                eid1 eid2
                (SIM: sim_trace p mem tid tr (aeu::atr) wl rl covl vextl)
                (EID2: eid2 >= List.length aeu.(AExecUnit.local).(ALocal.labels))
                (ADDR: aeu.(AExecUnit.local).(ALocal.addr) eid1 eid2):
            False.
          Proof.
          Admitted.

          exploit addr_inv; eauto. ss.
        }
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vrel_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VREL; eauto.
      * inv EID. inv REL. inv H1. destruct l; ss.
        exploit LABELS0; eauto.
        { rewrite List.app_length. s. lia. }
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. }
    + admit. (* fwdbank *)
    + admit. (* promise *)
  - (* dmb *)
    econs; ss.
    inv STEP. inv SIM_LOCAL. econs; ss.
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_coh_step. rewrite inverse_step.
      rewrite inverse_union. ii. des; [apply COH|]; eauto.
      inv EID. inv REL. inv H0. inv H1. inv H5.
      apply Label.is_writing_inv in LABEL. des. subst. inv H4.
      * exploit LABELS0; eauto; cycle 1.
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. }
        { rewrite List.app_length. s. lia. }
      * inv H0. exploit RF2; eauto. i. des.
        exploit LABELS0; eauto; cycle 1.
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. }
        { rewrite List.app_length. s. lia. }
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vrp_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VRP; eauto. i. rewrite <- join_l. ss.
      * inv EID. inv REL. inv H0. inv H4. inv H0. inv H5. inv H6.
        exploit LABELS0; eauto.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. simplify.
        destruct rr; ss.
        rewrite <- join_r, <- join_l. apply VRM. econs; eauto. econs; eauto.
      * inv EID. inv REL. inv H0. inv H4. inv H0. inv H5. inv H6.
        exploit LABELS0; eauto.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. simplify.
        destruct wr; ss.
        rewrite <- join_r, <- join_r, <- join_l. apply VWM. econs; eauto. econs; eauto.
      * inv EID. inv REL. inv H0. inv H4. inv H5.
        exploit LABELS0; eauto.
        { rewrite List.app_length. s. lia. }
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. }
      * inv EID. inv REL. inv H1. destruct l; ss.
        exploit LABELS0; eauto.
        { rewrite List.app_length. s. lia. }
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. }
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vwp_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VWP; eauto. i. rewrite <- join_l. ss.
      * inv EID. inv REL. inv H0. inv H4. inv H0. inv H5. inv H6.
        exploit LABELS0; eauto.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. simplify.
        destruct rw; ss.
        rewrite <- join_r, <- join_l. apply VRM. econs; eauto. econs; eauto.
      * inv EID. inv REL. inv H0. inv H4. inv H0. inv H5. inv H6.
        exploit LABELS0; eauto.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. simplify.
        destruct ww; ss.
        rewrite <- join_r, <- join_r, <- join_l. apply VWM. econs; eauto. econs; eauto.
      * inv EID. inv REL. inv H1. destruct l; ss.
        exploit LABELS0; eauto.
        { rewrite List.app_length. s. lia. }
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. }
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vrm_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VRM; eauto.
      * inv EID. inv REL. inv H1. destruct l; ss.
        exploit LABELS0; eauto.
        { rewrite List.app_length. s. lia. }
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. }
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vwm_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VWM; eauto.
      * inv EID. inv REL. inv H1. destruct l; ss.
        exploit LABELS0; eauto.
        { rewrite List.app_length. s. lia. }
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. }
    + admit. (* vcap *)
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vrel_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VREL; eauto.
      * inv EID. inv REL. inv H1. destruct l; ss.
        exploit LABELS0; eauto.
        { rewrite List.app_length. s. lia. }
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. }
    + admit. (* fwdbank *)
    + admit. (* promise *)
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
      Time.le ((v_gen vexts) eid1) ((v_gen vexts) eid2)>>.
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
  - admit.
Admitted.

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
        - inv LABEL1. }
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
      { econs. unfold init_with_promises in *. ss.
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
  ii. exploit Valid.ob_cycle; eauto. i. des.
  - clear - EXTERNAL NONBARRIER.
    exploit EXTERNAL; eauto. i. des.
    + inv x; lia.
    + inv x0. lia.
    + inv x0. inv x1. rewrite EID in EID0. inv EID0. destruct l0; ss; congr.
  - exploit Valid.barrier_ob_po; eauto. i. inv x1. lia.
}
{ (* internal *)
  clear - INTERNAL.
  eapply internal_acyclic. auto.
}
Qed.
