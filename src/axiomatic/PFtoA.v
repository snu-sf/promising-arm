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
Require Import PromisingArch.axiomatic.Axiomatic.

Set Implicit Arguments.


Inductive inverse A (rel:relation A) (codom:A -> Prop) (a:A): Prop :=
| inverse_intro
    a'
    (REL: rel a a')
    (CODOM: codom a')
.
Hint Constructors inverse.

Lemma inverse_mon A (r1 r2:relation A)
      (REL: r1 ⊆ r2):
  inverse r1 <2= inverse r2.
Proof.
  i. inv PR. econs; eauto.
Qed.

Lemma inverse_union A (r1 r2:relation A) s:
  inverse (r1 ∪ r2) s = inverse r1 s \1/ inverse r2 s.
Proof.
  funext. i. propext. econs; i.
  - inv H. inv REL; eauto.
  - des; inv H; econs; eauto.
    + left. ss.
    + right. ss.
Qed.

Lemma inverse_step
      r tid n:
  inverse (r ⨾ Execution.po_adj) (eq (tid, S n)) = inverse r (eq (tid, n)).
Proof.
  funext. i. propext. econs; i.
  - inv H. inv REL. des. inv H0. destruct x, x0. ss. inv N. econs; eauto.
  - inv H. econs; eauto. econs; eauto.
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

Definition sim_local_coh ex loc :=
  ⦗ex.(Execution.label_is) (Label.is_writing loc)⦘ ⨾
  ex.(Execution.rfe)^? ⨾
  Execution.po.

Lemma sim_local_coh_step ex loc:
  sim_local_coh ex loc =
  (sim_local_coh ex loc ∪
   ⦗ex.(Execution.label_is) (Label.is_writing loc)⦘ ⨾ ex.(Execution.rfe)^?) ⨾
  Execution.po_adj.
Proof.
  unfold sim_local_coh. rewrite Execution.po_po_adj at 1.
  rewrite (clos_refl_union Execution.po), union_seq, eq_seq.
  rewrite ? seq_union, ? union_seq, ? seq_assoc.
  refl.
Qed.

Lemma sim_local_coh_spec
      p ex loc eid1 eid2
      (EX: Valid.ex p ex)
      (EID2: Execution.label_is ex (Label.is_accessing loc) eid2)
      (COH: sim_local_coh ex loc eid1 eid2):
  <<INTERNAL: ex.(Execution.internal)⁺ eid1 eid2>> /\
  <<LABEL: Execution.label_is ex (Label.is_writing loc) eid1>>.
Proof.
  inv COH. des. inv H. inv H0. des. inv EID2. inv H2. destruct l0; ss. inv H.
  - esplits.
    + econs. left. left. left. econs; eauto.
    + destruct (equiv_dec loc0 loc); ss. inv e. econs; eauto. apply Label.write_is_writing.
  - inv H1. splits.
    + econs 2; [econs|].
      { right. eauto. }
      exploit EX.(Valid.RF2); eauto. i. des.
      rewrite EID0 in WRITE. inv WRITE.
      econs. left. left. left. econs; eauto.
    + destruct (equiv_dec loc0 loc); ss. inv e. econs; eauto. apply Label.write_is_writing.
Qed.

Definition sim_local_vrp ex :=
  (⦗ex.(Execution.label_is) Label.is_read⦘ ⨾
   Execution.po ⨾
   ⦗ex.(Execution.label_is) (Label.is_barrier_c Barrier.is_dmb_rr)⦘ ⨾
   Execution.po) ∪

  (⦗ex.(Execution.label_is) Label.is_write⦘ ⨾
   Execution.po ⨾
   ⦗ex.(Execution.label_is) (Label.is_barrier_c Barrier.is_dmb_wr)⦘ ⨾
   Execution.po) ∪

  ((ex.(Execution.ctrl) ∪ (ex.(Execution.addr) ⨾ Execution.po)) ⨾
   ⦗ex.(Execution.label_is) (eq (Label.barrier Barrier.isb))⦘ ⨾
   Execution.po) ∪

  (⦗ex.(Execution.label_is) (Label.is_acquire_pc)⦘ ⨾
   Execution.po).

Lemma sim_local_vrp_step ex:
  sim_local_vrp ex =
  (sim_local_vrp ex ∪
   ((⦗ex.(Execution.label_is) Label.is_read⦘ ⨾
     Execution.po ⨾
     ⦗ex.(Execution.label_is) (Label.is_barrier_c Barrier.is_dmb_rr)⦘) ∪

   (⦗ex.(Execution.label_is) Label.is_write⦘ ⨾
     Execution.po ⨾
     ⦗ex.(Execution.label_is) (Label.is_barrier_c Barrier.is_dmb_wr)⦘) ∪

    ((ex.(Execution.ctrl) ∪ (ex.(Execution.addr) ⨾ Execution.po)) ⨾
     ⦗ex.(Execution.label_is) (eq (Label.barrier Barrier.isb))⦘) ∪

    (⦗ex.(Execution.label_is) (Label.is_acquire_pc)⦘))) ⨾
  Execution.po_adj.
Proof.
  unfold sim_local_vrp. rewrite ? (union_seq' Execution.po_adj), ? seq_assoc, ? union_assoc.
  rewrite Execution.po_po_adj at 2 4 6 7.
  rewrite (clos_refl_union Execution.po), union_seq, eq_seq.
  rewrite ? (seq_union' (Execution.po ⨾ Execution.po_adj) Execution.po_adj), ? seq_assoc, ? union_assoc.
  funext. i. funext. i. propext. econs; i.
  - repeat match goal with
           | [H: (_ ∪ _) _ _ |- _] => inv H
           end;
      eauto 10 using union_l, union_r.
  - repeat match goal with
           | [H: (_ ∪ _) _ _ |- _] => inv H
           end;
      eauto 10 using union_l, union_r.
Qed.

Lemma sim_local_vrp_spec
      p ex eid1 eid2
      (EX: Valid.ex p ex)
      (EID2: Execution.label_is ex Label.is_read eid2)
      (VRP: sim_local_vrp ex eid1 eid2):
  <<OB: ex.(Execution.ob) eid1 eid2>>.
Proof.
  inv EID2. destruct l; inv LABEL. unfold sim_local_vrp in VRP.
  repeat match goal with
         | [H: (_ ∪ _) _ _ |- _] => inv H
         end.
  - right. left. left. left. left. left. left. left.
    inv H. des. econs. splits; eauto.
    rewrite ? seq_assoc. econs. splits; [|by econs; eauto].
    rewrite <- ? seq_assoc. ss.
  - right. left. left. left. left. left. right.
    inv H. des. econs. splits; eauto.
    rewrite ? seq_assoc. econs. splits; [|by econs; eauto].
    rewrite <- ? seq_assoc. ss.
  - left. left. right. right.
    inv H0. des. econs. splits; eauto.
    right. rewrite seq_assoc. econs. splits; eauto. econs; ss. econs; eauto.
  - right. left. left. right.
    inv H. des. econs. splits; eauto.
Qed.

Definition sim_local_vwp ex :=
  (⦗ex.(Execution.label_is) Label.is_read⦘ ⨾
   Execution.po ⨾
   ⦗ex.(Execution.label_is) (Label.is_barrier_c Barrier.is_dmb_rw)⦘ ⨾
   Execution.po) ∪

  (⦗ex.(Execution.label_is) Label.is_write⦘ ⨾
   Execution.po ⨾
   ⦗ex.(Execution.label_is) (Label.is_barrier_c Barrier.is_dmb_ww)⦘ ⨾
   Execution.po) ∪

  (⦗ex.(Execution.label_is) (Label.is_acquire_pc)⦘ ⨾
   Execution.po).

Lemma sim_local_vwp_step ex:
  sim_local_vwp ex =
  (sim_local_vwp ex ∪
   ((⦗ex.(Execution.label_is) Label.is_read⦘ ⨾
     Execution.po ⨾
     ⦗ex.(Execution.label_is) (Label.is_barrier_c Barrier.is_dmb_rw)⦘) ∪

   (⦗ex.(Execution.label_is) Label.is_write⦘ ⨾
     Execution.po ⨾
     ⦗ex.(Execution.label_is) (Label.is_barrier_c Barrier.is_dmb_ww)⦘) ∪

    (⦗ex.(Execution.label_is) (Label.is_acquire_pc)⦘))) ⨾
  Execution.po_adj.
Proof.
  unfold sim_local_vwp. rewrite ? (union_seq' Execution.po_adj), ? seq_assoc, ? union_assoc.
  rewrite Execution.po_po_adj at 2 4 5.
  rewrite (clos_refl_union Execution.po), union_seq, eq_seq.
  rewrite ? (seq_union' (Execution.po ⨾ Execution.po_adj) Execution.po_adj), ? seq_assoc, ? union_assoc.
  funext. i. funext. i. propext. econs; i.
  - repeat match goal with
           | [H: (_ ∪ _) _ _ |- _] => inv H
           end;
      eauto 10 using union_l, union_r.
  - repeat match goal with
           | [H: (_ ∪ _) _ _ |- _] => inv H
           end;
      eauto 10 using union_l, union_r.
Qed.

Lemma sim_local_vwp_spec
      p ex eid1 eid2
      (EX: Valid.ex p ex)
      (EID2: Execution.label_is ex Label.is_write eid2)
      (VWP: sim_local_vwp ex eid1 eid2):
  <<OB: ex.(Execution.ob) eid1 eid2>>.
Proof.
  inv EID2. destruct l; inv LABEL. unfold sim_local_vwp in VWP.
  repeat match goal with
         | [H: (_ ∪ _) _ _ |- _] => inv H
         end.
  - right. left. left. left. left. left. left. right.
    inv H0. des. econs. splits; eauto.
    rewrite ? seq_assoc. econs. splits; [|by econs; eauto].
    rewrite <- ? seq_assoc. ss.
  - right. left. left. left. left. right.
    inv H0. des. econs. splits; eauto.
    rewrite ? seq_assoc. econs. splits; [|by econs; eauto].
    rewrite <- ? seq_assoc. ss.
  - right. left. left. right.
    inv H. des. econs. splits; eauto.
Qed.

Definition sim_local_vrm ex :=
  ⦗ex.(Execution.label_is) (Label.is_read)⦘ ⨾ Execution.po.

Lemma sim_local_vrm_step ex:
  sim_local_vrm ex =
  (sim_local_vrm ex ∪ ⦗ex.(Execution.label_is) (Label.is_read)⦘) ⨾
  Execution.po_adj.
Proof.
  unfold sim_local_vrm. rewrite ? (union_seq' Execution.po_adj), ? seq_assoc, ? union_assoc.
  rewrite Execution.po_po_adj at 1.
  rewrite (clos_refl_union Execution.po), union_seq, eq_seq.
  rewrite ? (seq_union' (Execution.po ⨾ Execution.po_adj) Execution.po_adj), ? seq_assoc, ? union_assoc.
  refl.
Qed.

Definition sim_local_vwm ex :=
  ⦗ex.(Execution.label_is) (Label.is_write)⦘ ⨾ Execution.po.

Lemma sim_local_vwm_step ex:
  sim_local_vwm ex =
  (sim_local_vwm ex ∪ ⦗ex.(Execution.label_is) (Label.is_write)⦘) ⨾
  Execution.po_adj.
Proof.
  unfold sim_local_vwm. rewrite ? (union_seq' Execution.po_adj), ? seq_assoc, ? union_assoc.
  rewrite Execution.po_po_adj at 1.
  rewrite (clos_refl_union Execution.po), union_seq, eq_seq.
  rewrite ? (seq_union' (Execution.po ⨾ Execution.po_adj) Execution.po_adj), ? seq_assoc, ? union_assoc.
  refl.
Qed.

Definition sim_local_vcap ex :=
  ex.(Execution.ctrl) ∪ (ex.(Execution.addr) ⨾ Execution.po).

Lemma sim_local_vcap_po
      p ex
      (EX: Valid.ex p ex):
  (sim_local_vcap ex ⨾ Execution.po) ⊆ sim_local_vcap ex.
Proof.
  unfold sim_local_vcap. ii. inv H. des. inv H0.
  - left. eapply Valid.ctrl_po; eauto. econs. splits; eauto.
  - right. inv H. des. econs. splits; eauto. etrans; eauto.
Qed.

Lemma sim_local_vcap_po_adj
      p ex
      (EX: Valid.ex p ex):
  (sim_local_vcap ex ⨾ Execution.po_adj) ⊆ sim_local_vcap ex.
Proof.
  ii. eapply sim_local_vcap_po; eauto.
  inv H. des. econs. splits; eauto. apply Execution.po_adj_po. ss.
Qed.

Definition sim_local_vrel ex :=
  ⦗ex.(Execution.label_is) (Label.is_release)⦘ ⨾ Execution.po.

Lemma sim_local_vrel_step ex:
  sim_local_vrel ex =
  (sim_local_vrel ex ∪ ⦗ex.(Execution.label_is) (Label.is_release)⦘) ⨾
  Execution.po_adj.
Proof.
  unfold sim_local_vrel. rewrite ? (union_seq' Execution.po_adj), ? seq_assoc, ? union_assoc.
  rewrite Execution.po_po_adj at 1.
  rewrite (clos_refl_union Execution.po), union_seq, eq_seq.
  rewrite ? (seq_union' (Execution.po ⨾ Execution.po_adj) Execution.po_adj), ? seq_assoc, ? union_assoc.
  refl.
Qed.

Lemma sim_local_vrel_spec
      p ex eid1 eid2
      (EX: Valid.ex p ex)
      (EID2: Execution.label_is ex Label.is_acquire eid2)
      (VREL: sim_local_vrel ex eid1 eid2):
  <<OB: ex.(Execution.ob) eid1 eid2>>.
Proof.
  inv EID2. destruct l; inv LABEL. unfold sim_local_vrel in VREL.
  right. left. left. left. right.
  rewrite seq_assoc. econs. splits; eauto. econs; eauto.
Qed.

Inductive sim_local_fwd ex (loc:Loc.t) (eid1 eid2:eidT): Prop :=
| sim_local_fwd_intro
    (PO: Execution.po eid1 eid2)
    (WRITE: ex.(Execution.label_is) (Label.is_writing loc) eid1)
    (NWRITE: forall eid
               (PO: Execution.po eid1 eid)
               (PO: Execution.po eid eid2),
        ex.(Execution.label_is) (fun l => ~ Label.is_writing loc l) eid)
.

Lemma sim_local_fwd_step ex loc:
  sim_local_fwd ex loc =
  (sim_local_fwd ex loc ⨾ ⦗ex.(Execution.label_is) (fun l => ~ (Label.is_writing loc l))⦘ ∪
   ⦗ex.(Execution.label_is) (Label.is_writing loc)⦘) ⨾
  Execution.po_adj.
Proof.
  funext. i. funext. i. propext. econs.
  - i. inv H. rewrite Execution.po_po_adj in PO. inv PO. des.
    inv H0. destruct x0, x1. ss. subst.
    econs. splits; cycle 1.
    { instantiate (1 := (_, _)). econs; ss. }
    inv H.
    + right. econs; ss.
    + hexploit NWRITE; eauto. i.
      left. econs. splits; cycle 1.
      { econs; eauto. }
      econs; eauto. i. apply NWRITE; eauto. etrans; eauto.
  - i. inv H. des. inv H1. destruct x0, x1. ss. subst. inv H0.
    + inv H. des. inv H1. inv H2. inv H0.
      econs; eauto.
      * etrans; eauto.
      * i. rewrite Execution.po_po_adj in PO1. inv PO1. des. inv H0. destruct x0. ss. inv N.
        inv H; eauto.
    + inv H. inv H1. apply Label.is_writing_inv in LABEL. des. subst.
      econs; eauto.
      * econs; eauto. apply Label.write_is_writing.
      * i. inv PO. inv PO0. ss. subst. lia.
Qed.

Lemma sim_local_fwd_functional ex loc eid1 eid2 eid3
      (EID1: sim_local_fwd ex loc eid1 eid3)
      (EID2: sim_local_fwd ex loc eid2 eid3):
  eid1 = eid2.
Proof.
  inv EID1. inv EID2.
  destruct eid1, eid2, eid3. inv PO. inv PO0. ss. subst. f_equal.
  destruct (Nat.compare_spec n n0); ss.
  - exploit (NWRITE (t1, n0)); eauto. i.
    inv WRITE0. apply Label.is_writing_inv in LABEL. des. subst.
    inv x0. rewrite EID in EID0. inv EID0. ss. destruct (equiv_dec loc loc); ss. congr.
  - exploit (NWRITE0 (t1, n)); eauto. i.
    inv WRITE. apply Label.is_writing_inv in LABEL. des. subst.
    inv x0. rewrite EID in EID0. inv EID0. ss. destruct (equiv_dec loc loc); ss. congr.
Qed.

Lemma rfi_sim_local_fwd
      p ex (EX: Valid.ex p ex)
      loc eid1 eid2
      (EID1: ex.(Execution.label_is) (Label.is_writing loc) eid1)
      (EID2: ex.(Execution.label_is) (Label.is_reading loc) eid2)
      (RFI: ex.(Execution.rfi) eid1 eid2):
  sim_local_fwd ex loc eid1 eid2.
Proof.
  destruct eid1 as [tid1 n1].
  destruct eid2 as [tid2 n2].
  inv RFI. inv H0. ss. subst.
  destruct (Nat.compare_spec n1 n2).
  - subst. exfalso. eapply EX.(Valid.INTERNAL).
    econs. right. eauto.
  - econs; ss. i. destruct eid. inv PO. inv PO0. ss. subst.
    inv EID1. apply Label.is_writing_inv in LABEL. des. subst.
    inv EID2. apply Label.is_reading_inv in LABEL. des. subst.
    exploit Valid.po_label; eauto.
    { instantiate (1 := (t, n)). econs; ss. }
    i. des. econs; eauto. intro X. apply Label.is_writing_inv in X. des. subst.
    exploit Valid.coherence_ww.
    { eauto. }
    { econs; try exact EID; eauto. apply Label.write_is_writing. }
    { econs; try exact LABEL; eauto. apply Label.write_is_writing. }
    { econs; ss. }
    i.
    exploit Valid.coherence_wr; try exact H; eauto.
    { econs; try exact LABEL; eauto. apply Label.write_is_writing. }
    { econs; try exact EID0; eauto. apply Label.read_is_reading. }
    { econs; ss. }
    i. des.
    exploit EX.(Valid.RF_WF); [exact H|exact RF|]. i. subst.
    inv CO.
    + inv H1. lia.
    + exfalso. eapply EX.(Valid.INTERNAL). econs 2; econs; left; right; eauto.
  - exfalso. eapply EX.(Valid.INTERNAL). econs 2; [econs|econs].
    + right. eauto.
    + left. left. left. econs; eauto.
      inv EID1. apply Label.is_writing_inv in LABEL. des. subst.
      inv EID2. apply Label.is_reading_inv in LABEL. des. subst.
      econs; eauto. econs; eauto using Label.read_is_accessing, Label.write_is_accessing.
Qed.

Definition sim_local_fwd_none ex loc :=
  ⦗ex.(Execution.label_is) (Label.is_writing loc)⦘ ⨾ Execution.po.

Lemma sim_local_fwd_none_step ex loc:
  sim_local_fwd_none ex loc =
  (sim_local_fwd_none ex loc ∪ ⦗ex.(Execution.label_is) (Label.is_writing loc)⦘) ⨾
  Execution.po_adj.
Proof.
  unfold sim_local_fwd_none. rewrite ? (union_seq' Execution.po_adj), ? seq_assoc, ? union_assoc.
  rewrite Execution.po_po_adj at 1.
  rewrite (clos_refl_union Execution.po), union_seq, eq_seq.
  rewrite ? (seq_union' (Execution.po ⨾ Execution.po_adj) Execution.po_adj), ? seq_assoc, ? union_assoc.
  refl.
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

Inductive sim_eu (tid:Id.t) (ex:Execution.t) (vext: eidT -> Time.t) (eu:ExecUnit.t (A:=unit)) (aeu:AExecUnit.t): Prop :=
| sim_eu_intro
    (STATE: sim_state tid vext eu.(ExecUnit.state) aeu.(AExecUnit.state))
    (LOCAL: sim_local tid ex vext eu.(ExecUnit.local) aeu.(AExecUnit.local))
.
Hint Constructors sim_eu.

(* Lemma label_read_mem_of_ex *)
(*       eid ex ob exm ord loc val *)
(*       (OB: Permutation ob (Execution.eids ex)) *)
(*       (LABEL: Execution.label eid ex = Some (Label.read exm ord loc val)): *)
(*   exists view, *)
(*     <<VIEW: view_of_eid ex ob eid = Some view>>. *)
(* Proof. *)
(*   generalize (Execution.eids_spec ex). i. des. rename NODUP into NODUP0. *)
(*   specialize (LABEL0 eid). rewrite LABEL in LABEL0. *)
(*   inv LABEL0. clear H0. exploit H; [congr|]. clear H. intro IN0. *)
(*   symmetry in OB. exploit Permutation_in; eauto. intro IN. *)
(*   exploit HahnList.Permutation_nodup; eauto. intro NODUP. *)
(*   generalize (List_in_find_pos _ ob IN). i. des. *)
(*   unfold view_of_eid. rewrite H. s. eauto. *)
(* Qed. *)

(* Lemma label_write_mem_of_ex_msg *)
(*       eid ex ob exm ord loc val *)
(*       (OB: Permutation ob (Execution.eids ex)) *)
(*       (LABEL: Execution.label eid ex = Some (Label.write exm ord loc val)): *)
(*   exists n, *)
(*     <<VIEW: view_of_eid ex ob eid = Some (S n)>> /\ *)
(*     <<MSG: List.nth_error (mem_of_ex ex ob) n = Some (Msg.mk loc val eid.(fst))>>. *)
(* Proof. *)
(*   generalize (Execution.eids_spec ex). i. des. rename NODUP into NODUP0. *)
(*   specialize (LABEL0 eid). rewrite LABEL in LABEL0. *)
(*   inv LABEL0. clear H0. exploit H; [congr|]. clear H. intro IN0. *)
(*   symmetry in OB. exploit Permutation_in; eauto. intro IN. *)
(*   exploit HahnList.Permutation_nodup; eauto. intro NODUP. *)
(*   generalize (List_in_find_pos _ ob IN). i. des. *)
(*   unfold view_of_eid. rewrite H. *)
(*   exploit List_find_pos_inv; eauto. i. des. *)
(*   destruct (equiv_dec a eid); [|done]. inversion e. subst. *)
(*   esplits. *)
(*   - unfold option_map. erewrite List_firstn_S; eauto. *)
(*     rewrite mem_of_ex_app, List.app_length. *)
(*     unfold mem_of_ex at 2. s. rewrite LABEL. s. rewrite Nat.add_1_r. ss. *)
(*   - rewrite <- (List.firstn_skipn n ob) at 1. *)
(*     rewrite mem_of_ex_app, List.nth_error_app2; [|lia]. *)
(*     erewrite Nat.sub_diag, List_skipn_cons; eauto. s. *)
(*     unfold mem_of_ex. s. rewrite LABEL. ss. *)
(* Qed. *)

(* Lemma label_write_mem_of_ex *)
(*       eid ex ob exm ord loc val *)
(*       (OB: Permutation ob (Execution.eids ex)) *)
(*       (LABEL: Execution.label eid ex = Some (Label.write exm ord loc val)): *)
(*   exists n, *)
(*     <<VIEW: view_of_eid ex ob eid = Some (S n)>> /\ *)
(*     <<READ: Memory.read loc (S n) (mem_of_ex ex ob) = Some val>> /\ *)
(*     <<MSG: Memory.get_msg (S n) (mem_of_ex ex ob) = Some (Msg.mk loc val eid.(fst))>>. *)
(* Proof. *)
(*   exploit label_write_mem_of_ex_msg; eauto. i. des. *)
(*   esplits; eauto. *)
(*   unfold Memory.read. s. rewrite MSG. s. condtac; [|congr]. ss. *)
(* Qed. *)

(* Lemma in_mem_of_ex *)
(*       ex ob view msg *)
(*       (NODUP: List.NoDup ob) *)
(*       (IN: List.nth_error (mem_of_ex ex ob) view = Some msg): *)
(*   exists n ex1 ord1, *)
(*     <<LABEL: Execution.label (msg.(Msg.tid), n) ex = Some (Label.write ex1 ord1 msg.(Msg.loc) msg.(Msg.val))>> /\ *)
(*     <<VIEW: view_of_eid ex ob (msg.(Msg.tid), n) = Some (S view)>>. *)
(* Proof. *)
(*   unfold mem_of_ex in IN. exploit nth_error_filter_map_inv; eauto. i. des. *)
(*   destruct (Execution.label a ex) eqn:LABEL; ss. destruct t; inv FA. destruct a. ss. *)
(*   esplits. *)
(*   - eauto. *)
(*   - unfold view_of_eid. *)
(*     erewrite List_nth_error_find_pos; eauto. s. f_equal. ss. *)
(* Qed. *)

Definition promises_from_mem
           (tid:Id.t) (mem: Memory.t): Promises.t.
Proof.
  induction mem using list_rev_rect.
  - exact bot.
  - destruct x.
    apply (if tid0 == tid
           then Promises.set (S (List.length (List.rev mem))) IHmem
           else IHmem).
Defined.

Lemma promises_from_mem_nil tid:
  promises_from_mem tid Memory.empty = bot.
Proof.
  unfold promises_from_mem, list_rev_rect, eq_rect. ss.
  match goal with
  | [|- context[match ?c with | eq_refl => _ end]] => destruct c
  end; ss.
Qed.

Lemma promises_from_mem_snoc tid mem msg:
  promises_from_mem tid (mem ++ [msg]) =
  if msg.(Msg.tid) == tid
  then Promises.set (S (List.length mem)) (promises_from_mem tid mem)
  else promises_from_mem tid mem.
Proof.
  unfold promises_from_mem at 1, list_rev_rect, eq_rect.
  match goal with
  | [|- context[match ?c with | eq_refl => _ end]] => destruct c
  end; ss.
  rewrite List.rev_involutive, List.rev_app_distr. ss.
  destruct msg. s. condtac.
  - inversion e. subst. rewrite ? List.rev_length.
    f_equal.
    unfold promises_from_mem, list_rev_rect, eq_rect.
    match goal with
    | [|- context[match ?c with | eq_refl => _ end]] => destruct c
    end; ss.
  - unfold promises_from_mem, list_rev_rect, eq_rect.
    match goal with
    | [|- context[match ?c with | eq_refl => _ end]] => destruct c
    end; ss.
Qed.

Lemma promises_from_mem_inv
      ts tid mem
      (LOOKUP: Promises.lookup (S ts) (promises_from_mem tid mem)):
  exists loc val, List.nth_error mem ts = Some (Msg.mk loc val tid).
Proof.
  revert LOOKUP. induction mem using List.rev_ind.
  { rewrite promises_from_mem_nil, Promises.lookup_bot. ss. }
  rewrite promises_from_mem_snoc. condtac.
  { rewrite Promises.set_o. condtac.
    - inversion e. inversion e0. subst.
      rewrite List.nth_error_app2; [|lia].
      rewrite Nat.sub_diag. ss.
      destruct x. esplits; eauto.
    - i. exploit IHmem; eauto.  i. des.
      rewrite List.nth_error_app1; eauto.
      apply List.nth_error_Some. congr.
  }
  i. exploit IHmem; eauto.  i. des.
  rewrite List.nth_error_app1; eauto.
  apply List.nth_error_Some. congr.
Qed.

Definition init_with_promises (p:program) (mem:Memory.t): Machine.t :=
  Machine.mk
    (IdMap.mapi (fun tid stmts =>
                   (State.init stmts,
                    Local.init_with_promises (promises_from_mem tid mem)))
                p)
    mem.

Lemma pf_init_with_promises
      p promises
      (MEM: forall msg (MSG: List.In msg promises), IdMap.find msg.(Msg.tid) p <> None):
  exists m,
    <<STEP: rtc (Machine.step ExecUnit.promise_step) (Machine.init p) m>> /\
    <<TPOOL: IdMap.Equal m.(Machine.tpool) (init_with_promises p promises).(Machine.tpool)>> /\
    <<MEM: m.(Machine.mem) = promises>>.
Proof.
  revert MEM. induction promises using List.rev_ind; i.
  { esplits; eauto. ii. s. rewrite IdMap.map_spec, IdMap.mapi_spec.
    destruct (IdMap.find y p); ss.
    unfold Local.init, Local.init_with_promises. repeat f_equal.
    rewrite promises_from_mem_nil. ss.
  }
  exploit IHpromises; eauto.
  { i. apply MEM. apply List.in_app_iff. intuition. }
  i. des. subst. destruct x.
  hexploit MEM.
  { apply List.in_app_iff. right. left. eauto. }
  match goal with
  | [|- context[(?f <> None) -> _]] => destruct f eqn:FIND
  end; ss.
  intro X. clear X.
  eexists (Machine.mk _ _). esplits.
  - etrans; [eauto|]. econs 2; [|refl].
    econs.
    + rewrite TPOOL, IdMap.mapi_spec, FIND. ss.
    + econs; ss. econs; eauto. ss.
    + ss.
  - s. ii. rewrite IdMap.add_spec. condtac; ss.
    + inversion e. subst. rewrite IdMap.mapi_spec, FIND. s.
      unfold Local.init_with_promises. repeat f_equal.
      rewrite promises_from_mem_snoc. condtac; ss.
    + rewrite TPOOL, ? IdMap.mapi_spec. destruct (IdMap.find y p); ss.
      unfold Local.init_with_promises. rewrite promises_from_mem_snoc. s.
      condtac; ss. congr.
  - ss.
Qed.

Inductive sim_val_weak (vala:ValA.t (A:=View.t (A:=unit))) (avala:ValA.t (A:=nat -> Prop)): Prop :=
| sim_val_weak_intro
    (VAL: vala.(ValA.val) = avala.(ValA.val))
.
Hint Constructors sim_val_weak.

Inductive sim_rmap_weak (rmap:RMap.t (A:=View.t (A:=unit))) (armap:RMap.t (A:=nat -> Prop)): Prop :=
| sim_rmap_weak_intro
    (RMAP: IdMap.Forall2 (fun reg => sim_val_weak) rmap armap)
.
Hint Constructors sim_rmap_weak.

Inductive sim_state_weak (state:State.t (A:=View.t (A:=unit))) (astate:State.t (A:=nat -> Prop)): Prop :=
| sim_state_weak_intro
    (STMTS: state.(State.stmts) = astate.(State.stmts))
    (RMAP: sim_rmap_weak state.(State.rmap) astate.(State.rmap))
.
Hint Constructors sim_state_weak.

Lemma sim_state_weak_init stmts:
  sim_state_weak (State.init stmts) (State.init stmts).
Proof.
  econs; ss. econs. ii. unfold RMap.init. rewrite ? IdMap.gempty. econs.
Qed.

Lemma sim_rmap_weak_add
      rmap armap reg vala avala
      (SIM: sim_rmap_weak rmap armap)
      (VAL: sim_val_weak vala avala):
  sim_rmap_weak (RMap.add reg vala rmap) (RMap.add reg avala armap).
Proof.
  econs. ii. unfold RMap.add. rewrite ? IdMap.add_spec.
  inv SIM. condtac; eauto.
Qed.

Lemma sim_rmap_weak_expr
      rmap armap e
      (SIM: sim_rmap_weak rmap armap):
  sim_val_weak (sem_expr rmap e) (sem_expr armap e).
Proof.
  inv SIM. induction e; s.
  - (* const *)
    econs; ss.
  - (* reg *)
    specialize (RMAP reg). unfold RMap.find. inv RMAP; ss.
  - (* op1 *)
    inv IHe. econs; ss. congr.
  - (* op2 *)
    inv IHe1. inv IHe2. econs; ss; try congr.
Qed.

Inductive sim_event: forall (e1: Event.t (A:=View.t (A:=unit))) (e2: Event.t (A:=nat -> Prop)), Prop :=
| sim_event_internal
    ctrl1 ctrl2:
    sim_event (Event.internal ctrl1) (Event.internal ctrl2)
| sim_event_read
    ex1 ord1 vloc1 val1
    ex2 ord2 vloc2 val2:
    sim_event (Event.read ex1 ord1 vloc1 val1) (Event.read ex2 ord2 vloc2 val2)
| sim_event_write
    ex1 ord1 vloc1 vval1 res1
    ex2 ord2 vloc2 vval2 res2
    (FAILURE: res1.(ValA.val) = res2.(ValA.val)):
    sim_event (Event.write ex1 ord1 vloc1 vval1 res1) (Event.write ex2 ord2 vloc2 vval2 res2)
| sim_event_barrier
    b1 b2:
    sim_event (Event.barrier b1) (Event.barrier b2)
.

Inductive sim_trace (p: program) (mem: Memory.t) (tid: Id.t):
  forall (tr: list (ExecUnit.t (A:=unit))) (atr: list AExecUnit.t)
     (wl: list (nat -> option (Loc.t * Time.t))) (rl: list (nat -> option Time.t))
     (cov: nat -> Time.t) (vext: nat -> Time.t), Prop :=
| sim_trace_init
    st lc stmts
    (FIND: IdMap.find tid (init_with_promises p mem).(Machine.tpool) = Some (st, lc))
    (STMT: IdMap.find tid p = Some stmts):
    sim_trace p mem tid [ExecUnit.mk st lc mem] [AExecUnit.mk (State.init stmts) ALocal.init]
              [fun _ => None] [fun _ => None] (fun _ => Time.bot) (fun _ => Time.bot)
| sim_trace_step
    e ae tr eu1 eu2 atr aeu1 aeu2 rl r1 r2 wl w1 w2 cov cov' vext vext'
    (STEP: ExecUnit.state_step0 tid e e eu1 eu2)
    (ASTATE_STEP: State.step ae aeu1.(AExecUnit.state) aeu2.(AExecUnit.state))
    (ALOCAL_STEP: ALocal.step ae aeu1.(AExecUnit.local) aeu2.(AExecUnit.local))
    (EVENT: sim_event e ae)
    (STATE: sim_state_weak eu2.(ExecUnit.state) aeu2.(AExecUnit.state))
    (W: w2 = match e with
             | Event.write _ _ vloc _ (ValA.mk _ 0 _) =>
               (fun eid => if Nat.eqb eid (ALocal.next_eid aeu1.(AExecUnit.local))
                         then Some (vloc.(ValA.val), (eu2.(ExecUnit.local).(Local.coh) vloc.(ValA.val)))
                         else w1 eid)
             | _ => w1
             end)
    (R: r2 = match e with
               | Event.read _ _ vloc _ =>
                 (fun eid => if Nat.eqb eid (ALocal.next_eid aeu1.(AExecUnit.local))
                            then Some (eu2.(ExecUnit.local).(Local.coh) vloc.(ValA.val))
                            else r1 eid)
               | _ => r1
               end)
    (COV: cov' = match e with
                 | Event.read _ _ vloc _
                 | Event.write _ _ vloc _ (ValA.mk _ 0 _) =>
                   (fun eid => if Nat.eqb eid (ALocal.next_eid aeu1.(AExecUnit.local))
                              then eu2.(ExecUnit.local).(Local.coh) vloc.(ValA.val)
                              else cov eid)
                 | _ => cov
                 end)
    (VEXT: vext' = match e with
                   | Event.read _ _ _ res =>
                     (fun eid => if Nat.eqb eid (ALocal.next_eid aeu1.(AExecUnit.local))
                                then res.(ValA.annot).(View.ts)
                                else vext eid)
                   | Event.write _ _ vloc _ (ValA.mk _ 0 _) =>
                     (fun eid => if Nat.eqb eid (ALocal.next_eid aeu1.(AExecUnit.local))
                                then eu2.(ExecUnit.local).(Local.coh) vloc.(ValA.val)
                                else vext eid)
                   | _ => vext
                   end)
    (TRACE: sim_trace p mem tid (eu1::tr) (aeu1::atr) (w1::wl) (r1::rl) cov vext):
    sim_trace p mem tid (eu2::eu1::tr) (aeu2::aeu1::atr) (w2::w1::wl) (r2::r1::rl) cov' vext'
.

Definition sim_traces
           (p: program) (mem: Memory.t)
           (trs: IdMap.t (list (ExecUnit.t (A:=unit))))
           (atrs: IdMap.t (list AExecUnit.t))
           (ws: IdMap.t (list (nat -> option (Loc.t * Time.t))))
           (rs: IdMap.t (list (nat -> option Time.t)))
           (covs: IdMap.t (nat -> Time.t))
           (vexts: IdMap.t (nat -> Time.t))
  : Prop :=
  IdMap.Forall6 (sim_trace p mem) trs atrs ws rs covs vexts.

Lemma sim_trace_last
      p mem tid tr atr wl rl cov vext
      (SIM: sim_trace p mem tid tr atr wl rl cov vext):
  exists eu tr' aeu atr' w wl' r rl',
    <<HDTR: tr = eu :: tr'>> /\
    <<HDATR: atr = aeu :: atr'>> /\
    <<HDWL: wl = w :: wl'>> /\
    <<HDRL: rl = r :: rl'>>.
Proof.
  inv SIM; esplits; eauto.
Qed.

Lemma sim_traces_memory
      p mem trs atrs rs ws covs vexts
      m
      ts loc val tid
      (STEP: Machine.pf_exec p m)
      (SIM: sim_traces p mem trs atrs ws rs covs vexts)
      (TR: IdMap.Forall2
             (fun tid tr sl => exists l, tr = (ExecUnit.mk sl.(fst) sl.(snd) mem) :: l)
             trs m.(Machine.tpool))
      (GET: Memory.get_msg ts mem = Some (Msg.mk loc val tid)):
  exists eu, IdMap.find tid trs = Some eu.
Proof.
Admitted.

Lemma promising_pf_sim_traces
      p m
      (STEP: Machine.pf_exec p m):
  exists trs atrs ws rs covs vexts ex (PRE: Valid.pre_ex p ex),
    <<SIM: sim_traces p m.(Machine.mem) trs atrs ws rs covs vexts>> /\
    <<TR: IdMap.Forall2
            (fun tid tr sl => exists l, tr = (ExecUnit.mk sl.(fst) sl.(snd) m.(Machine.mem)) :: l)
            trs m.(Machine.tpool)>> /\
    <<ATR: IdMap.Forall2
             (fun tid atr aeu => exists l, atr = aeu :: l)
             atrs PRE.(Valid.aeus)>>.
Proof.
Admitted.

Ltac simplify :=
  repeat
    (try match goal with
         | [H1: _ = IdMap.find ?id ?m, H2: _ = IdMap.find ?id ?m |- _] =>
           rewrite <- H1 in H2; inv H2
         | [H1: IdMap.find ?id ?m = _, H2: IdMap.find ?id ?m = _ |- _] =>
           rewrite H1 in H2; inv H2
         | [H1: IdMap.find ?id ?m = _, H2: _ = IdMap.find ?id ?m |- _] =>
           rewrite H1 in H2; inv H2
         | [H: Some _ = Some _ |- _] => inv H
         | [H: _::_ = _::_ |- _] => inv H
         end).

Lemma w_property
      p mem tid tr atr wl rl cov vext
      (SIM: sim_trace p mem tid tr atr wl rl cov vext):
  exists eu tr' aeu atr' w wl',
    tr = eu :: tr' /\
    atr = aeu :: atr' /\
    wl = w :: wl' /\
    <<WPROP1:
      forall ts loc val
         (GET: Memory.get_msg ts mem = Some (Msg.mk loc val tid)),
        ((Promises.lookup ts eu.(ExecUnit.local).(Local.promises) = true /\
          forall eid, w eid <> Some (loc, ts)) \/
         (Promises.lookup ts eu.(ExecUnit.local).(Local.promises) = false /\
          exists eid ex ord,
            w eid = Some (loc, ts) /\
            List.nth_error aeu.(AExecUnit.local).(ALocal.labels) eid = Some (Label.write ex ord loc val)))>> /\
    <<WPROP2:
      forall eid ex ord loc val
        (GET: List.nth_error aeu.(AExecUnit.local).(ALocal.labels) eid = Some (Label.write ex ord loc val)),
      exists ts,
        w eid = Some (loc, ts) /\
        Memory.get_msg ts mem = Some (Msg.mk loc val tid)>> /\
    <<WPROP3:
      forall eid loc ts (GET: w eid = Some (loc, ts)),
        Time.lt Time.bot ts /\
      exists ex ord val,
        List.nth_error aeu.(AExecUnit.local).(ALocal.labels) eid = Some (Label.write ex ord loc val) /\
        Memory.get_msg ts mem = Some (Msg.mk loc val tid)>> /\
    <<WPROP4:
      forall eid1 loc1 eid2 loc2 ts (W1: w eid1 = Some (loc1, ts)) (W2: w eid2 = Some (loc2, ts)),
        eid1 = eid2>>.
Proof.
  induction SIM.
  { esplits; ss.
    - rewrite IdMap.mapi_spec, STMT in FIND. inv FIND. s. i.
      left. splits; ss. admit.
    - rewrite IdMap.mapi_spec, STMT in FIND. inv FIND. s. i.
      destruct eid; ss.
  }
  des. simplify. esplits; eauto.
  - inv STEP. inv EVENT; inv LOCAL; ss.
    + inv LC. rewrite LC2 in *. s. 
      inv ALOCAL_STEP; ss. rewrite ALOCAL in *. s.
      eauto.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
  - admit.
  - admit.
  - admit.
Admitted.

Lemma r_property
      p mem tid tr atr wl rl cov vext
      (SIM: sim_trace p mem tid tr atr wl rl cov vext):
  exists eu tr' aeu atr' r rl',
    tr = eu :: tr' /\
    atr = aeu :: atr' /\
    rl = r :: rl' /\
    <<RPROP1:
      forall eid ex ord loc val
         (GET: List.nth_error aeu.(AExecUnit.local).(ALocal.labels) eid = Some (Label.read ex ord loc val)),
      exists ts tid',
        r eid = Some ts /\
        ((ts = Time.bot /\ val = Val.default) \/
         Memory.get_msg ts mem = Some (Msg.mk loc val tid'))>> /\
    <<RPROP2:
      forall eid ts (GET: r eid = Some ts),
      exists ex ord loc val tid',
        List.nth_error aeu.(AExecUnit.local).(ALocal.labels) eid = Some (Label.read ex ord loc val) /\
        ((ts = Time.bot /\ val = Val.default) \/
         Memory.get_msg ts mem = Some (Msg.mk loc val tid'))>>.
Proof.
Admitted.

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

Inductive rf_gen (ws: IdMap.t (list (nat -> option (Loc.t * Time.t)))) (rs: IdMap.t (list (nat -> option Time.t))) (eid1 eid2: eidT): Prop :=
| rf_gen_intro
    w wl ts1 loc1 r rl ts2
    (WS: IdMap.find eid1.(fst) ws = Some (w::wl))
    (W: w eid1.(snd) = Some (loc1, ts1))
    (RS: IdMap.find eid2.(fst) rs = Some (r::rl))
    (R: r eid2.(snd) = Some ts2)
    (TS: ts1 = ts2)
.

Definition v_gen (vs: IdMap.t (nat -> Time.t)) (eid: eidT): Time.t :=
  match IdMap.find eid.(fst) vs with
  | Some v => v eid.(snd)
  | None => Time.bot
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
  exploit w_property; try exact REL6. i. des.
  exploit w_property; try exact REL0. i. des.
  subst. simplify.
  exploit WPROP2; try exact LABEL; eauto. intro W1. des.
  exploit WPROP5; try exact LABEL0; eauto. intro W2. des.
  destruct (Id.eq_dec tid1 tid2); subst; simplify.
  - specialize (Nat.lt_trichotomy ts ts0). i. des; subst.
    + right. left. econs; eauto.
    + exploit WPROP4; [exact W1|exact W2|..]. auto.
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
  exploit w_property; try exact REL6. i. des. simplify.
  exploit w_property; try exact REL0. i. des. simplify.
  exploit WPROP3; eauto. i. des.
  exploit WPROP6; eauto. i. des.
  esplits; eauto.
Qed.

Lemma sim_traces_rf1_aux
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
    (<<NORF: ~ codom_rel (rf_gen ws rs) eid1>> /\ <<VAL: val = Val.default >> /\
     <<R: exists r rl, IdMap.find eid1.(fst) rs = Some (r::rl) /\ r eid1.(snd) = Some Time.bot>>) \/
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
  exploit r_property; eauto. i. des. simplify.
  exploit RPROP1; eauto. i. des.
  - left. esplits; subst; eauto.
    ii. inv H. inv H1.
    destruct x0 as [tid2 eid2]. ss. simplify.
    rewrite R in x. inv x.
    generalize (SIM tid2). intro SIM1. inv SIM1; try congr.
    simplify.
    exploit w_property; try exact REL0; eauto. i. des. simplify.
    exploit WPROP3; eauto. i. des.
    unfold Memory.get_msg in x0. ss.
  - right. exploit sim_traces_memory; eauto. i. des.
    generalize (TR tid'). intro TR2. inv TR2; try congr.
    generalize (SIM tid'). intro SIM2. inv SIM2; try congr.
    des. simplify.
    exploit w_property; try exact REL0; eauto. i. des. simplify.
    exploit WPROP1; eauto. i. des; ss.
    + destruct b. ss. inv NOPROMISE.
      exploit PROMISES0; eauto. i. rewrite x4 in x1.
      rewrite Promises.lookup_bot in x1. ss.
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
  exploit w_property; try exact REL0; eauto. i. des. inv x2.
  exploit r_property; try exact REL6; eauto. i. des. inv x2.
  exploit WPROP3; eauto. i. des.
  exploit RPROP2; eauto. i. des.
  - rewrite x3 in x1. inv x1.
  - rewrite x3 in x1. inv x1.
    generalize (ATR tid1). intro ATR1. inv ATR1; try congr.
    generalize (ATR tid2). intro ATR2. inv ATR2; try congr.
    des. simplify. destruct PRE, ex. unfold Execution.label. ss.
    clear WPROP1 WPROP2 WPROP3 WPROP4 RPROP1 RPROP2.
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
    exploit w_property; eauto. i. des. simplify.
    exploit WPROP4; [exact W|exact W0|..]. i. subst. refl.
  - generalize (SIM tid1). intro SIM1. inv SIM1; try congr.
    generalize (SIM tid2). intro SIM2. inv SIM2; try congr.
    exploit w_property; try exact REL6; eauto. i. des.
    exploit w_property; try exact REL0; eauto. i. des.
    simplify.
    exploit WPROP3; eauto. i. des.
    exploit WPROP6; eauto. i. des.
    congr.
Qed.

Definition lastn A (n: nat) (l: list A) :=
  List.rev (List.firstn n (List.rev l)).

Lemma lastn_all A (l: list A):
  lastn (S (List.length l)) l = l.
Proof.
  unfold lastn.
  rewrite <- List.rev_length.
  rewrite List.firstn_all2.
  - rewrite List.rev_involutive. refl.
  - omega.
Qed.

Lemma sim_trace_vext_cov
      p mem tid tr atr wl rl cov vext
      (SIM: sim_trace p mem tid tr atr wl rl cov vext):
  exists aeu atr' w wl' r rl',
    atr = aeu :: atr' /\
    wl = w :: wl' /\
    rl = r :: rl' /\
    (forall eid ts (W: w eid = Some ts),
        (exists ex ord loc val,
            List.nth_error aeu.(AExecUnit.local).(ALocal.labels) eid = Some (Label.write ex ord loc val)) /\
        cov eid = ts.(snd) /\
        vext eid = ts.(snd)) /\
    (forall eid ts (R: r eid = Some ts),
        (exists ex ord loc val,
            List.nth_error aeu.(AExecUnit.local).(ALocal.labels) eid = Some (Label.read ex ord loc val)) /\
        cov eid = ts).
Proof.
  induction SIM; esplits; eauto; i; ss.
  - des. inv IHSIM. inv IHSIM0. inv EVENT.
    + exploit IHSIM2; eauto. i. des.
      destruct aeu2. destruct local.
      inv ALOCAL_STEP; ss; inv ALOCAL; esplits; eauto.
    + des_ifs; eauto.
      * exfalso.
        rewrite Nat.eqb_eq in Heq. subst.
        exploit IHSIM2; eauto. i. des.
        unfold ALocal.next_eid in *.
        assert (H: List.nth_error (ALocal.labels (AExecUnit.local aeu)) (length (ALocal.labels (AExecUnit.local aeu))) <> None)
          by (ii; congr).
        rewrite List.nth_error_Some in H. lia.
      * exploit IHSIM2; eauto. i. des.
        destruct aeu2. destruct local.
        inv ALOCAL_STEP; ss; inv ALOCAL; esplits; eauto.
        { rewrite List.nth_error_app1; eauto.
          eapply List.nth_error_Some. ii. congr. }
    + des_ifs; eauto.
      * destruct eu1. destruct eu2.
        destruct aeu. destruct aeu2. ss.
        inv STATE. inv STEP. inv STATE; ss.
        rewrite Nat.eqb_eq in Heq. subst.
        inv LOCAL; ss.
        { inv STEP. ss. splits; eauto.
          inv EVENT. inv ALOCAL_STEP; ss.
          - esplits. unfold ALocal.next_eid.
            rewrite List.nth_error_app2.
            rewrite <- Minus.minus_n_n. ss. lia.
          - inv EVENT. inv FAILURE. }
        { inv STEP. ss. }
      * exploit IHSIM2; eauto. i. des.
        destruct aeu2. destruct local.
        inv ALOCAL_STEP; ss; inv ALOCAL; esplits; eauto.
        { rewrite List.nth_error_app1; eauto.
          eapply List.nth_error_Some. ii. congr. }
      * exploit IHSIM2; eauto. i. des.
        destruct aeu2. destruct local.
        inv ALOCAL_STEP; ss; inv ALOCAL; esplits; eauto.
        { rewrite List.nth_error_app1; eauto.
          eapply List.nth_error_Some. ii. congr. }
      * exploit IHSIM2; eauto. i. des.
        destruct aeu2. destruct local.
        inv ALOCAL_STEP; ss; inv ALOCAL; esplits; eauto.
        { rewrite List.nth_error_app1; eauto.
          eapply List.nth_error_Some. ii. congr. }
    + exploit IHSIM2; eauto. i. des.
      destruct aeu2. destruct local.
      inv ALOCAL_STEP; ss; inv ALOCAL; esplits; eauto.
      { rewrite List.nth_error_app1; eauto.
        eapply List.nth_error_Some. ii. congr. }
  - des. inv IHSIM. inv IHSIM1. inv EVENT.
    + exploit IHSIM3; eauto. i. des.
      destruct aeu2. destruct local.
      inv ALOCAL_STEP; ss; inv ALOCAL; esplits; eauto.
    + des_ifs; eauto.
      * destruct eu1. destruct eu2.
        destruct aeu. destruct aeu2. ss.
        inv STATE. inv STEP. inv STATE; ss.
        rewrite Nat.eqb_eq in Heq. subst.
        inv LOCAL; ss.
        inv STEP. ss. splits; eauto.
        inv EVENT. inv ALOCAL_STEP; ss.
        esplits. unfold ALocal.next_eid.
        rewrite List.nth_error_app2.
        rewrite <- Minus.minus_n_n. ss. lia.
      * exploit IHSIM3; eauto. i. des.
        destruct aeu2. destruct local.
        inv ALOCAL_STEP; ss; inv ALOCAL; esplits; eauto.
        { rewrite List.nth_error_app1; eauto.
          eapply List.nth_error_Some. ii. congr. }
    + des_ifs; eauto.
      * exfalso.
        rewrite Nat.eqb_eq in Heq. subst.
        exploit IHSIM3; eauto. i. des.
        unfold ALocal.next_eid in *.
        assert (H: List.nth_error (ALocal.labels (AExecUnit.local aeu)) (length (ALocal.labels (AExecUnit.local aeu))) <> None)
          by (ii; congr).
        rewrite List.nth_error_Some in H. lia.
      * exploit IHSIM3; eauto. i. des.
        destruct aeu2. destruct local.
        inv ALOCAL_STEP; ss; inv ALOCAL; esplits; eauto.
        { rewrite List.nth_error_app1; eauto.
          eapply List.nth_error_Some. ii. congr. }
      * exploit IHSIM3; eauto. i. des.
        destruct aeu2. destruct local.
        inv ALOCAL_STEP; ss; inv ALOCAL; esplits; eauto.
        { rewrite List.nth_error_app1; eauto.
          eapply List.nth_error_Some. ii. congr. }
      * exploit IHSIM3; eauto. i. des.
        destruct aeu2. destruct local.
        inv ALOCAL_STEP; ss; inv ALOCAL; esplits; eauto.
        { rewrite List.nth_error_app1; eauto.
          eapply List.nth_error_Some. ii. congr. }
    + exploit IHSIM3; eauto. i. des.
      destruct aeu2. destruct local.
      inv ALOCAL_STEP; ss; inv ALOCAL; esplits; eauto.
      { rewrite List.nth_error_app1; eauto.
        eapply List.nth_error_Some. ii. congr. }
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
  exploit sim_trace_vext_cov; try exact REL6. i. des.
  exploit sim_trace_vext_cov; try exact REL0. i. des. simplify.
  exploit x3; eauto. i. des.
  exploit x8; eauto. i. des.
  unfold v_gen. ss. rewrite <- H4. rewrite <- H10.
  rewrite x0. rewrite x5. auto.
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
  exploit sim_trace_vext_cov; try exact REL6. i. des.
  exploit sim_trace_vext_cov; try exact REL0. i. des. simplify.
  exploit x3; eauto. i. des.
  exploit x9; eauto. i. des.
  unfold v_gen. ss. rewrite <- H4. rewrite <- H10.
  rewrite x0. rewrite x5. refl.
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
      exploit w_property; try exact REL6. i. des. simplify.
      exploit WPROP2; eauto. i. des.
      exploit WPROP3; eauto. i. des.
      clear ex2 ord1 val0 x2 x3.
      generalize (SIM tid1). intro SIM1. inv SIM1; try congr. simplify.
      exploit sim_trace_vext_cov; try exact REL6. i. des.
      exploit sim_trace_vext_cov; try exact REL0. i. des. simplify.
      exploit x5; eauto. i. des.
      exploit x11; eauto. i. des.
      unfold v_gen. ss. rewrite <- H12. rewrite <- H7.
      rewrite x8. rewrite x3. auto.
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
Admitted.

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
  exploit sim_trace_vext_cov; try exact REL6. i. des.
  exploit sim_trace_vext_cov; try exact REL0. i. des. simplify.
  exploit x3; eauto. i. des.
  exploit x8; eauto. i. des.
  unfold v_gen. ss. rewrite <- H5. rewrite <- H11.
  rewrite x1. rewrite x6. auto.
Qed.

Lemma asdf
      p mem trs atrs ws rs covs vexts
      ex
      tid n atr aeu atr'
      (SIM: sim_traces p mem trs atrs ws rs covs vexts)
      (PRE: Valid.pre_ex p ex)
      (ATR: IdMap.Forall2
              (fun _ atr aeu => exists l, atr = aeu :: l)
              atrs (Valid.aeus PRE))
      (FIND_ATR: IdMap.find tid atrs = Some atr)
      (AEU: lastn (S n) atr = aeu :: atr'):
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
      aeu.(AExecUnit.local).(ALocal.rmw) eid1 eid2>>.
Proof.
Admitted.

Lemma sim_traces_sim_eu
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
  forall tid tr atr n eu tr' aeu atr'
    (FIND_TR: IdMap.find tid trs = Some tr)
    (FIND_ATR: IdMap.find tid atrs = Some atr)
    (EU: lastn (S n) tr = eu :: tr')
    (AEU: lastn (S n) atr = aeu :: atr'),
    sim_eu tid ex (v_gen vexts) eu aeu.
Proof.
  i. generalize (SIM tid). intro X. inv X; simplify.
  revert eu aeu tr' atr' EU AEU. induction n.
  { i. admit. (* lastn *) }
  (* Lemma lastn_S A *)
  (* n (l:list A): *)
  (*   lastn (S n) l =  :: lastn n l. *)
  admit.
Admitted.

Lemma sim_traces_vext_valid_aux
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
  forall tid atr
    (FINDA: IdMap.find tid atrs = Some atr)
    n aeu atr'
    (LASTN: lastn (S n) atr = aeu :: atr'),
    <<RFE:
      forall eid1 eid2
        (LABEL: eid2 < List.length aeu.(AExecUnit.local).(ALocal.labels))
        (RFE: ex.(Execution.rfe) eid1 (tid, eid2)),
        Time.le ((v_gen vexts) eid1) ((v_gen vexts) (tid, eid2))>> /\
    <<FR:
      forall eid1 eid2
        (LABEL: eid1 < List.length aeu.(AExecUnit.local).(ALocal.labels))
        (FR: ex.(Execution.fr) (tid, eid1) eid2),
        Time.lt ((v_gen vexts) (tid, eid1)) ((v_gen vexts) eid2)>> /\
    <<AOB_WRITE:
      forall eid1 eid2
        (LABEL: eid2 < List.length aeu.(AExecUnit.local).(ALocal.labels))
        (AOB: ex.(Execution.aob) eid1 (tid, eid2))
        (EID1: ex.(Execution.label_is) Label.is_access eid1)
        (EID2: ex.(Execution.label_is) Label.is_write (tid, eid2)),
        Time.lt ((v_gen vexts) eid1) ((v_gen vexts) (tid, eid2))>> /\
    <<AOB_READ:
      forall eid1 eid2
        (LABEL: eid2 < List.length aeu.(AExecUnit.local).(ALocal.labels))
        (AOB: ex.(Execution.aob) eid1 (tid, eid2))
        (EID1: ex.(Execution.label_is) Label.is_access eid1)
        (EID2: ex.(Execution.label_is) Label.is_read (tid, eid2)),
        Time.le ((v_gen vexts) eid1) ((v_gen vexts) (tid, eid2))>> /\
    <<BOB_WRITE:
      forall eid1 eid2
        (LABEL: eid2 < List.length aeu.(AExecUnit.local).(ALocal.labels))
        (BOB: ex.(Execution.bob) eid1 (tid, eid2))
        (EID1: ex.(Execution.label_is) Label.is_access eid1)
        (EID2: ex.(Execution.label_is) Label.is_write (tid, eid2)),
        Time.lt ((v_gen vexts) eid1) ((v_gen vexts) (tid, eid2))>> /\
    <<BOB_READ:
      forall eid1 eid2
        (LABEL: eid2 < List.length aeu.(AExecUnit.local).(ALocal.labels))
        (BOB: ex.(Execution.bob) eid1 (tid, eid2))
        (EID2: ex.(Execution.label_is) Label.is_read (tid, eid2)),
        Time.le ((v_gen vexts) eid1) ((v_gen vexts) (tid, eid2))>> /\
    <<DOB_WRITE:
      forall eid1 eid2
        (LABEL: eid2 < List.length aeu.(AExecUnit.local).(ALocal.labels))
        (DOB: ex.(Execution.dob) eid1 (tid, eid2))
        (EID1: ex.(Execution.label_is) Label.is_access eid1)
        (EID2: ex.(Execution.label_is) Label.is_write (tid, eid2)),
        Time.lt ((v_gen vexts) eid1) ((v_gen vexts) (tid, eid2))>> /\
    <<DOB_READ:
      forall eid1 eid2
        (LABEL: eid2 < List.length aeu.(AExecUnit.local).(ALocal.labels))
        (DOB: ex.(Execution.dob) eid1 (tid, eid2))
        (EID1: ex.(Execution.label_is) Label.is_access eid1)
        (EID2: ex.(Execution.label_is) Label.is_read (tid, eid2)),
        Time.le ((v_gen vexts) eid1) ((v_gen vexts) (tid, eid2))>>.
Proof.
  i. induction n.
  - admit.
  - admit.
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
  <<RFE:
    forall eid1 eid2
      (RFE: ex.(Execution.rfe) eid1 eid2),
      Time.le ((v_gen vexts) eid1) ((v_gen vexts) eid2)>> /\
  <<FR:
    forall eid1 eid2
      (FR: ex.(Execution.fr) eid1 eid2),
      Time.lt ((v_gen vexts) eid1) ((v_gen vexts) eid2)>> /\
  <<AOB_WRITE:
    forall eid1 eid2
      (AOB: ex.(Execution.aob) eid1 eid2)
      (EID1: ex.(Execution.label_is) Label.is_access eid1)
      (EID2: ex.(Execution.label_is) Label.is_write eid2),
      Time.lt ((v_gen vexts) eid1) ((v_gen vexts) eid2)>> /\
  <<AOB_READ:
    forall eid1 eid2
      (AOB: ex.(Execution.aob) eid1 eid2)
      (EID1: ex.(Execution.label_is) Label.is_access eid1)
      (EID2: ex.(Execution.label_is) Label.is_read eid2),
      Time.le ((v_gen vexts) eid1) ((v_gen vexts) eid2)>> /\
  <<BOB_WRITE:
    forall eid1 eid2
      (BOB: ex.(Execution.bob) eid1 eid2)
      (EID1: ex.(Execution.label_is) Label.is_access eid1)
      (EID2: ex.(Execution.label_is) Label.is_write eid2),
      Time.lt ((v_gen vexts) eid1) ((v_gen vexts) eid2)>> /\
  <<BOB_READ:
    forall eid1 eid2
      (BOB: ex.(Execution.bob) eid1 eid2)
      (EID2: ex.(Execution.label_is) Label.is_read eid2),
      Time.le ((v_gen vexts) eid1) ((v_gen vexts) eid2)>> /\
  <<DOB_WRITE:
    forall eid1 eid2
      (DOB: ex.(Execution.dob) eid1 eid2)
      (EID1: ex.(Execution.label_is) Label.is_access eid1)
      (EID2: ex.(Execution.label_is) Label.is_write eid2),
      Time.lt ((v_gen vexts) eid1) ((v_gen vexts) eid2)>> /\
  <<DOB_READ:
    forall eid1 eid2
      (DOB: ex.(Execution.dob) eid1 eid2)
      (EID1: ex.(Execution.label_is) Label.is_access eid1)
      (EID2: ex.(Execution.label_is) Label.is_read eid2),
      Time.le ((v_gen vexts) eid1) ((v_gen vexts) eid2)>>.
Proof.
  splits.
  - i. destruct eid2 as [tid2 eid2].
    generalize RFE. intro X. inv X.
    rewrite RF in H. inv H. ss.
    generalize (SIM tid2). intro SIM2. inv SIM2; try congr.
    exploit sim_trace_last; eauto. i. des. simplify.
    exploit sim_traces_vext_valid_aux; eauto.
    { rewrite lastn_all. refl. }
    i. des.
    exploit RFE0; eauto.
    exploit r_property; try exact REL6. i. des.
    simplify. exploit RPROP2; eauto. i. des.
    + eapply List.nth_error_Some; eauto. ii. congr.
    + eapply List.nth_error_Some; eauto. ii. congr.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

Ltac des_union :=
  repeat
    (try match goal with
         | [H: Execution.internal _ _ _ |- _] => inv H
         | [H: Execution.ob _ _ _ |- _] => inv H
         | [H: Execution.obs _ _ _ |- _] => inv H
         | [H: (_ ∪ _) _ _ |- _] => inv H
         end).

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
    + right. des_union.
      * exploit RFE; eauto.
      * exploit FR; eauto. i.
        split; eauto using Nat.lt_le_incl.
      * exploit sim_traces_vext_co; eauto. i.
        split; eauto using Nat.lt_le_incl.
      * exploit DOB_READ; eauto.
      * exploit AOB_READ; eauto.
      * exploit BOB_READ; eauto.
    + left. des_union.
      * inv H. rewrite RF in *. inv H0.
        destruct eid2 as [tid2 eid2]. ss.
        generalize (SIM tid2). intro SIM2. inv SIM2; try congr.
        exploit r_property; eauto. i. des. simplify.
        generalize (ATR tid2). intro ATR2. inv ATR2; try congr. des.
        simplify. unfold Execution.label in *. destruct PRE.
        rewrite LABELS in *. rewrite IdMap.map_spec in *. ss.
        rewrite <- H7 in *. ss.
        exploit RPROP2; eauto. i. des; try congr.
      * exploit FR; eauto.
      * exploit sim_traces_vext_co; eauto.
      * exploit DOB_WRITE; eauto.
      * exploit AOB_WRITE; eauto.
      * exploit BOB_WRITE; eauto.
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
