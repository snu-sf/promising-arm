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
Require Import PromisingArch.axiomatic.PFtoAGlobal.

Set Implicit Arguments.


Inductive sim_ex tid ex covs vexts aeu cov vext: Prop := {
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
      (CTRL: ex.(Execution.ctrl) (tid, eid1) (tid, eid2)),
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
}.

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
  sim_ex tid ex covs vexts aeu cov vext.
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
  apply Nat.eqb_eq in N. subst.
  rewrite List.nth_error_app2, Nat.sub_diag; ss. 
Qed.

Lemma nth_error_not_last A (l: list A) a b n
      (NTH: List.nth_error (l ++ [a]) n = Some b)
      (N: Nat.eqb n (List.length l) = false):
  n < List.length l.
Proof.
  apply nth_error_snoc_inv in NTH. des; ss. subst.
  apply Nat.eqb_neq in N. lia.
Qed.

Definition sim_view (vext: eidT -> Time.t) (view: Time.t) (eids: eidT -> Prop): Prop :=
  forall eid (EID: eids eid), le (vext eid) view.

Inductive sim_view_rev (vext: eidT -> Time.t) (view: Time.t) (eids: eidT -> Prop): Prop :=
| sim_view_rev_bot
    (VIEW: view = bot)
| sim_view_rev_event
    eid
    (EID: eids eid)
    (VIEW: le view (vext eid))
.
Hint Constructors sim_view_rev.

Definition sim_view_eq (vext: eidT -> Time.t) (view: Time.t) (eids: eidT -> Prop): Prop :=
  sim_view vext view eids /\ sim_view_rev vext view eids.

Inductive sim_val (tid:Id.t) (vext:eidT -> Time.t) (vala:ValA.t (A:=View.t (A:=unit))) (avala:ValA.t (A:=nat -> Prop)): Prop :=
| sim_val_intro
    (VAL: vala.(ValA.val) = avala.(ValA.val))
    (VIEW: sim_view vext vala.(ValA.annot).(View.ts) (fun eid => eid.(fst) = tid /\ avala.(ValA.annot) eid.(snd)))
.
Hint Constructors sim_val.

Inductive sim_rmap (tid:Id.t) (vext:eidT -> Time.t) (rmap:RMap.t (A:=View.t (A:=unit))) (armap:RMap.t (A:=nat -> Prop)): Prop :=
| sim_rmap_intro
    (RMAP: IdMap.Forall2 (fun reg => sim_val tid vext) rmap armap)
.
Hint Constructors sim_rmap.

Inductive sim_state (tid:Id.t) (vext:eidT -> Time.t) (state:State.t (A:=View.t (A:=unit))) (astate:State.t (A:=nat -> Prop)): Prop :=
| sim_state_intro
    (STMTS: state.(State.stmts) = astate.(State.stmts))
    (RMAP: sim_rmap tid vext state.(State.rmap) astate.(State.rmap))
.
Hint Constructors sim_state.

Lemma sim_rmap_add
      tid vext rmap armap reg vala avala
      (SIM: sim_rmap tid vext rmap armap)
      (VAL: sim_val tid vext vala avala):
  sim_rmap tid vext (RMap.add reg vala rmap) (RMap.add reg avala armap).
Proof.
  econs. ii. unfold RMap.add. rewrite ? IdMap.add_spec.
  inv SIM. condtac; eauto.
Qed.

Lemma sim_rmap_expr
      tid vext rmap armap e
      (SIM: sim_rmap tid vext rmap armap):
  sim_val tid vext (sem_expr rmap e) (sem_expr armap e).
Proof.
  inv SIM. induction e; s.
  - (* const *)
    econs; ss. ii. inv EID. inv H0.
  - (* reg *)
    specialize (RMAP reg). unfold RMap.find. inv RMAP; ss.
    econs; ss. ii. inv EID. inv H2.
  - (* op1 *)
    inv IHe. econs; ss. congr.
  - (* op2 *)
    inv IHe1. inv IHe2. econs; ss.
    + congr.
    + ii. des. inv EID0.
      * etrans; [|eapply join_l]; eauto.
      * etrans; [|eapply join_r]; eauto.
Qed.

Inductive sim_local (tid:Id.t) (ex: Execution.t) (vext: eidT -> Time.t) (local:Local.t (A:=unit)) (alocal:ALocal.t): Prop := mk_sim_local {
  COH: forall loc,
        sim_view
          vext
          (local.(Local.coh) loc)
          (inverse (sim_local_coh ex loc) (eq (tid, List.length (alocal.(ALocal.labels)))));
  VRP: sim_view
         vext
         local.(Local.vrp).(View.ts)
         (inverse (sim_local_vrp ex) (eq (tid, List.length (alocal.(ALocal.labels)))));
  VWP: sim_view
         vext
         local.(Local.vwp).(View.ts)
         (inverse (sim_local_vwp ex) (eq (tid, List.length (alocal.(ALocal.labels)))));
  VRM: sim_view
         vext
         local.(Local.vrm).(View.ts)
         (inverse (sim_local_vrm ex) (eq (tid, List.length (alocal.(ALocal.labels)))));
  VWM: sim_view
         vext
         local.(Local.vwm).(View.ts)
         (inverse (sim_local_vwm ex) (eq (tid, List.length (alocal.(ALocal.labels)))));
  VCAP: sim_view
          vext
          local.(Local.vcap).(View.ts)
          (inverse (sim_local_vcap ex) (eq (tid, List.length (alocal.(ALocal.labels)))));
  VREL: sim_view
          vext
          local.(Local.vrel).(View.ts)
          (inverse (sim_local_vrel ex) (eq (tid, List.length (alocal.(ALocal.labels)))));
  FWDBANK: forall loc,
      (exists eid,
          <<TS_NONZERO: (local.(Local.fwdbank) loc).(FwdItem.ts) > 0>> /\
          <<WRITE: sim_local_fwd ex loc eid (tid, List.length (alocal.(ALocal.labels)))>> /\
          <<TS: vext eid = (local.(Local.fwdbank) loc).(FwdItem.ts)>> /\
          <<VIEW: sim_view
                    vext
                    (local.(Local.fwdbank) loc).(FwdItem.view).(View.ts)
                    (inverse (ex.(Execution.addr) ∪ ex.(Execution.data)) (eq eid))>> /\
          <<EX: (local.(Local.fwdbank) loc).(FwdItem.ex) <-> ex.(Execution.label_is) (Label.is_ex) eid>>) \/
      ((local.(Local.fwdbank) loc) = FwdItem.init /\
       forall eid, ~ (inverse (sim_local_fwd_none ex loc) (eq (tid, List.length (alocal.(ALocal.labels)))) eid));
  EXBANK: opt_rel
            (fun aeb eb =>
               ex.(Execution.label_is) (Label.is_reading eb.(Exbank.loc)) (tid, aeb) /\
               sim_view_eq
                 vext
                 eb.(Exbank.ts)
                 (inverse ex.(Execution.rf) (eq (tid, aeb))) /\
               sim_view
                 vext
                 eb.(Exbank.view).(View.ts)
                 (eq (tid, aeb)))
            alocal.(ALocal.exbank) local.(Local.exbank);
  PROMISES: forall view (VIEW: Promises.lookup view local.(Local.promises)),
      exists n,
        <<N: (length alocal.(ALocal.labels)) <= n>> /\
        <<WRITE: ex.(Execution.label_is) Label.is_write (tid, n)>> /\
        <<VIEW: vext (tid, n) = view>>;
}.
Hint Constructors sim_local.

Definition sim_ob_write
           (tid:Id.t) (ex:Execution.t) (vext: eidT -> Time.t)
           (eu:ExecUnit.t (A:=unit)) (aeu:AExecUnit.t): Prop :=
  forall eid1 eid2
    (LABEL: eid2 < List.length aeu.(AExecUnit.local).(ALocal.labels))
    (OB: ex.(ob') eid1 (tid, eid2))
    (EID2: ex.(Execution.label_is) Label.is_write (tid, eid2)),
    Time.lt (vext eid1) (vext (tid, eid2)).

Definition sim_ob_read
           (tid:Id.t) (ex:Execution.t) (vext: eidT -> Time.t)
           (eu:ExecUnit.t (A:=unit)) (aeu:AExecUnit.t): Prop :=
  forall eid1 eid2
    (LABEL: eid2 < List.length aeu.(AExecUnit.local).(ALocal.labels))
    (AOB: ex.(ob') eid1 (tid, eid2))
    (EID2: ex.(Execution.label_is) Label.is_read (tid, eid2)),
    Time.le (vext eid1) (vext (tid, eid2)).

Definition sim_fr
           (tid:Id.t) (ex:Execution.t) (vext: eidT -> Time.t)
           (eu:ExecUnit.t (A:=unit)) (aeu:AExecUnit.t): Prop :=
  forall eid1 eid2
    (LABEL: eid1 < List.length aeu.(AExecUnit.local).(ALocal.labels))
    (FR: ex.(Execution.fr) (tid, eid1) eid2),
    Time.lt (vext (tid, eid1)) (vext eid2).

Inductive sim_th'
          (tid:Id.t) (ex:Execution.t) (vext: eidT -> Time.t)
          (eu:ExecUnit.t (A:=unit)) (aeu:AExecUnit.t): Prop := {
  ST: sim_state tid vext eu.(ExecUnit.state) aeu.(AExecUnit.state);
  LC: sim_local tid ex vext eu.(ExecUnit.local) aeu.(AExecUnit.local);
  OBW: sim_ob_write tid ex vext eu aeu;
  OBR: sim_ob_read tid ex vext eu aeu;
  FR: sim_fr tid ex vext eu aeu;
}.
Hint Constructors sim_th'.

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
  assert (OBW: sim_ob_write tid ex (v_gen vexts) eu2 aeu2).
  { admit. }
  assert (OBR: sim_ob_read tid ex (v_gen vexts) eu2 aeu2).
  { admit. }
  assert (FR: sim_fr tid ex (v_gen vexts) eu2 aeu2).
  { exploit sim_traces_ex; try exact EU; eauto. intro X. destruct X.
    ii. generalize FR0. intro X. inv X.
    - admit.
    - inv H. inv H1. inv H. inv H1.
      exploit LABELS0; eauto. intro LABEL1. destruct l; ss.
      rewrite EU, AEU, COV, VEXT in SIMTR.
      rewrite <- WL in SIMTR. rewrite <- RL in SIMTR.
      exploit sim_trace_sim_th; try exact SIMTR; eauto. i. destruct x0.
      exploit RPROP1; eauto. i. des. unguardH x0. des.
      + destruct eu1 as [st1 lc1 mem1], eu2 as [st2 lc2 mem2].
        destruct aeu1 as [ast1 alc1], aeu2 as [ast2 alc2].
        inv EVENT; ss.
        * eapply FR; eauto. inv ALOCAL_STEP; ss.
        * des_ifs; cycle 1.
          { eapply FR; eauto. inv ALOCAL_STEP; ss.
            eapply nth_error_not_last; eauto. }
          { inv STEP0. ss. inv LOCAL0; ss. inv STEP0. inv EVENT. ss.
            rewrite fun_add_spec in H1.
            destruct (equiv_dec (ValA.val vloc) (ValA.val vloc)); try congr.
            admit.
          }
        * inv STEP0. ss. inv LOCAL0; ss; inv EVENT.
          { inv STEP0. ss. inv ALOCAL_STEP; ss.
            - destruct (Nat.eqb eid1 (ALocal.next_eid alc1)) eqn:HEID1.
              + rewrite nth_error_last in LABEL1; auto. inv LABEL1.
              + eapply FR; eauto. eapply nth_error_not_last; eauto.
            - inv EVENT. inv RES. ss. }
          { inv STEP0. ss. eapply FR; eauto. inv ALOCAL_STEP; ss.
            destruct (Nat.eqb eid1 (List.length (ALocal.labels alc1))) eqn:HEID1.
            - rewrite nth_error_last in LABEL1; eauto. inv LABEL1.
            - eapply nth_error_not_last; eauto. }
        * inv STEP0. ss. inv LOCAL0; ss; inv EVENT.
          { inv STEP0. ss. eapply FR; eauto. inv ALOCAL_STEP; ss.
            destruct (Nat.eqb eid1 (List.length (ALocal.labels alc1))) eqn:HEID1.
            - rewrite nth_error_last in LABEL1; eauto. inv LABEL1.
            - eapply nth_error_not_last; eauto. }
          { inv STEP0. ss. eapply FR; eauto. inv ALOCAL_STEP; ss.
            destruct (Nat.eqb eid1 (List.length (ALocal.labels alc1))) eqn:HEID1.
            - rewrite nth_error_last in LABEL1; eauto. inv LABEL1.
            - eapply nth_error_not_last; eauto. }
        * inv STEP0. ss. inv LOCAL0; ss; inv EVENT.
          inv LC0. ss. eapply FR; eauto. inv ALOCAL_STEP; ss.
          destruct (Nat.eqb eid1 (List.length (ALocal.labels alc1))) eqn:HEID1.
          { rewrite nth_error_last in LABEL1; eauto. inv LABEL1. }
          { eapply nth_error_not_last; eauto. }
      + exploit sim_traces_memory; eauto. i. des.
        generalize (SIM tid'). intro SIM'. inv SIM'; try congr. simplify.
        exploit sim_trace_last; try exact REL0. i. des. subst.
        exploit sim_trace_sim_th; try exact REL0; eauto. i. destruct x3.
        exploit WPROP0; eauto. i. des.
        * inv STEP. inv NOPROMISE.
          generalize (TR tid'). intro TR'. inv TR'; try congr. des. simplify.
          destruct b. exploit PROMISES0; eauto. i.
          ss. rewrite x4 in *. rewrite Promises.lookup_bot in x1. ss.
        * exfalso. apply H3. econs. rewrite RF.
          instantiate (1 := (tid', eid)).
          exploit sim_trace_last; try exact REL6. i. des. subst.
          econs; try refl; ss; eauto.
          admit. (* should prove that r includes r2 *)
  }
  assert (SL: sim_state tid (v_gen vexts) eu2.(ExecUnit.state) aeu2.(AExecUnit.state) /\
              sim_local tid ex (v_gen vexts) eu2.(ExecUnit.local) aeu2.(AExecUnit.local)).
  { destruct eu1 as [[stmts1 rmap1] lc1 mem1].
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
        rewrite inverse_union. ii. des; [apply COH0|]; eauto.
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
        ii. inv EID. inv REL.
        * admit. (* ctrl should be local *)
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
        rewrite inverse_union. ii. des; [apply COH0|]; eauto.
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
      + admit. (* vcap *)
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
        rewrite inverse_union. ii. des; [apply COH0|]; eauto.
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
      + admit. (* vcap *)
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
  }
  des. econs; ss.
Admitted.  

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
      * exploit FR0; eauto. i.
        split; eauto using Nat.lt_le_incl.
      * exploit sim_traces_vext_co; eauto. i.
        split; eauto using Nat.lt_le_incl.
      * exploit OB_READ; eauto.
    + left. rewrite ob_ob' in OB. des_union.
      * exploit FR0; eauto.
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
  replace labels with ex'.(Execution.labels) in LABELS0; [|subst; ss].
  replace addr with ex'.(Execution.addr) in ADDR0; [|subst; ss].
  replace data with ex'.(Execution.data) in DATA0; [|subst; ss].
  replace ctrl with ex'.(Execution.ctrl) in CTRL0; [|subst; ss].
  replace rmw with ex'.(Execution.rmw) in RMW0; [|subst; ss].
  remember (@Valid.mk_pre_ex p ex' aeus AEUS LABELS0 ADDR0 DATA0 CTRL0 RMW0) as PRE'.
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
