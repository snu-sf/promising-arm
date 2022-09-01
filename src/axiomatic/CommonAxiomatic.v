Require Import Relations.
Require Import Permutation.
Require Import NArith.
Require Import PArith.
Require Import ZArith.
Require Import Lia.
Require Import FMapPositive.
Require Import FSetPositive.
Require Import EquivDec.
From sflib Require Import sflib.
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

Set Implicit Arguments.


Inductive inverse A (rel:relation A) (codom:A -> Prop) (a:A): Prop :=
| inverse_intro
    a'
    (REL: rel a a')
    (CODOM: codom a')
.
#[export]
Hint Constructors inverse: core.

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

Inductive sim_val_weak (vala:ValA.t (A:=View.t (A:=unit))) (avala:ValA.t (A:=nat -> Prop)): Prop :=
| sim_val_weak_intro
    (VAL: vala.(ValA.val) = avala.(ValA.val))
.
#[export]
Hint Constructors sim_val_weak: core.

Inductive sim_rmap_weak (rmap:RMap.t (A:=View.t (A:=unit))) (armap:RMap.t (A:=nat -> Prop)): Prop :=
| sim_rmap_weak_intro
    (RMAP: IdMap.Forall2 (fun reg => sim_val_weak) rmap armap)
.
#[export]
Hint Constructors sim_rmap_weak: core.

Inductive sim_state_weak (state:State.t (A:=View.t (A:=unit))) (astate:State.t (A:=nat -> Prop)): Prop :=
| sim_state_weak_intro
    (STMTS: state.(State.stmts) = astate.(State.stmts))
    (RMAP: sim_rmap_weak state.(State.rmap) astate.(State.rmap))
.
#[export]
Hint Constructors sim_state_weak: core.

Inductive sim_local_weak (local: Local.t (A:=unit)) (alocal: ALocal.t): Prop :=
| sim_local_weak_none
    (LOCAL_EX: local.(Local.exbank) = None)
    (ALOCAL_EX: alocal.(ALocal.exbank) = None)
| sim_local_weak_some
    eb aeb ex ord loc val
    (LOCAL_EX: local.(Local.exbank) = Some eb)
    (ALOCAL_EX: alocal.(ALocal.exbank) = Some aeb)
    (LABEL_EX: List.nth_error alocal.(ALocal.labels) aeb = Some (Label.read ex ord loc val))
    (EX_EX: ex = true)
    (EX_LOC: loc = eb.(Exbank.loc))
.
#[export]
Hint Constructors sim_local_weak: core.

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
| sim_event_internal:
    sim_event Event.internal Event.internal
| sim_event_read
    ex1 ord1 vloc1 val1
    ex2 ord2 vloc2 val2
    (EX: ex1 = ex2)
    (ORD: ord1 = ord2)
    (VLOC: sim_val_weak vloc1 vloc2)
    (VAL: sim_val_weak val1 val2):
    sim_event (Event.read ex1 ord1 vloc1 val1) (Event.read ex2 ord2 vloc2 val2)
| sim_event_write
    ex1 ord1 vloc1 vval1 res1
    ex2 ord2 vloc2 vval2 res2
    (EX: ex1 = ex2)
    (ORD: ord1 = ord2)
    (VLOC: sim_val_weak vloc1 vloc2)
    (VVAL: sim_val_weak vval1 vval2)
    (RES: sim_val_weak res1 res2):
    sim_event (Event.write ex1 ord1 vloc1 vval1 res1) (Event.write ex2 ord2 vloc2 vval2 res2)
| sim_event_barrier
    b1 b2
    (BARRIER: b1 = b2):
    sim_event (Event.barrier b1) (Event.barrier b2)
| sim_event_control
    ctrl1 ctrl2:
    sim_event (Event.control ctrl1) (Event.control ctrl2)
.
#[export]
Hint Constructors sim_event: core.

Definition sim_local_coh ex loc :=
  ⦗ex.(Execution.label_is) (Label.is_writing loc)⦘ ⨾
  (Execution.rfe ex)^? ⨾
  Execution.po.

Lemma sim_local_coh_step ex loc:
  sim_local_coh ex loc =
  (sim_local_coh ex loc ∪
   ⦗ex.(Execution.label_is) (Label.is_writing loc)⦘ ⨾ (Execution.rfe ex)^?) ⨾
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
  <<INTERNAL: (Execution.internal ex)⁺ eid1 eid2>> /\
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

Definition sim_local_vrn ex :=
  (⦗ex.(Execution.label_is) Label.is_read⦘ ⨾
   Execution.po ⨾
   ⦗ex.(Execution.label_is) (Label.is_barrier_c Barrier.is_dmb_rr)⦘ ⨾
   Execution.po) ∪

  (⦗ex.(Execution.label_is) Label.is_write⦘ ⨾
   Execution.po ⨾
   ⦗ex.(Execution.label_is) (Label.is_barrier_c Barrier.is_dmb_wr)⦘ ⨾
   Execution.po) ∪

  (((Execution.ctrl ex ∪ (ex.(Execution.addr) ⨾ Execution.po))) ⨾
   ⦗ex.(Execution.label_is) (eq (Label.barrier Barrier.isb))⦘ ⨾
   Execution.po) ∪

  (⦗ex.(Execution.label_is) (Label.is_acquire_pc)⦘ ⨾
   Execution.po).

Lemma sim_local_vrn_step ex:
  sim_local_vrn ex =
  (sim_local_vrn ex ∪
   ((⦗ex.(Execution.label_is) Label.is_read⦘ ⨾
     Execution.po ⨾
     ⦗ex.(Execution.label_is) (Label.is_barrier_c Barrier.is_dmb_rr)⦘) ∪

   (⦗ex.(Execution.label_is) Label.is_write⦘ ⨾
     Execution.po ⨾
     ⦗ex.(Execution.label_is) (Label.is_barrier_c Barrier.is_dmb_wr)⦘) ∪

    (((Execution.ctrl ex ∪ (ex.(Execution.addr) ⨾ Execution.po))) ⨾
     ⦗ex.(Execution.label_is) (eq (Label.barrier Barrier.isb))⦘) ∪

    (⦗ex.(Execution.label_is) (Label.is_acquire_pc)⦘))) ⨾
  Execution.po_adj.
Proof.
  unfold sim_local_vrn. rewrite ? (union_seq' Execution.po_adj), ? seq_assoc, ? union_assoc.
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

Lemma sim_local_vrn_spec
      p ex eid1 eid2
      (EX: Valid.ex p ex)
      (EID2: Execution.label_is ex Label.is_read eid2)
      (VRN: sim_local_vrn ex eid1 eid2):
  <<OB: Execution.ob ex eid1 eid2>>.
Proof.
  inv EID2. destruct l; inv LABEL. unfold sim_local_vrn in VRN.
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
    inv H0. des. rewrite seq_assoc. econs. splits; eauto.
    right. econs. splits; eauto. econs; ss. econs; eauto.
  - right. left. left. right.
    inv H. des. econs. splits; eauto.
Qed.

Definition sim_local_vwn ex :=
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

Lemma sim_local_vwn_step ex:
  sim_local_vwn ex =
  (sim_local_vwn ex ∪
   ((⦗ex.(Execution.label_is) Label.is_read⦘ ⨾
     Execution.po ⨾
     ⦗ex.(Execution.label_is) (Label.is_barrier_c Barrier.is_dmb_rw)⦘) ∪

   (⦗ex.(Execution.label_is) Label.is_write⦘ ⨾
     Execution.po ⨾
     ⦗ex.(Execution.label_is) (Label.is_barrier_c Barrier.is_dmb_ww)⦘) ∪

    (⦗ex.(Execution.label_is) (Label.is_acquire_pc)⦘))) ⨾
  Execution.po_adj.
Proof.
  unfold sim_local_vwn. rewrite ? (union_seq' Execution.po_adj), ? seq_assoc, ? union_assoc.
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

Lemma sim_local_vwn_spec
      p ex eid1 eid2
      (EX: Valid.ex p ex)
      (EID2: Execution.label_is ex Label.is_write eid2)
      (VWN: sim_local_vwn ex eid1 eid2):
  <<OB: Execution.ob ex eid1 eid2>>.
Proof.
  inv EID2. destruct l; inv LABEL. unfold sim_local_vwn in VWN.
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

Definition sim_local_vro ex :=
  ⦗ex.(Execution.label_is) (Label.is_read)⦘ ⨾ Execution.po.

Lemma sim_local_vro_step ex:
  sim_local_vro ex =
  (sim_local_vro ex ∪ ⦗ex.(Execution.label_is) (Label.is_read)⦘) ⨾
  Execution.po_adj.
Proof.
  unfold sim_local_vro. rewrite ? (union_seq' Execution.po_adj), ? seq_assoc, ? union_assoc.
  rewrite Execution.po_po_adj at 1.
  rewrite (clos_refl_union Execution.po), union_seq, eq_seq.
  rewrite ? (seq_union' (Execution.po ⨾ Execution.po_adj) Execution.po_adj), ? seq_assoc, ? union_assoc.
  refl.
Qed.

Definition sim_local_vwo ex :=
  ⦗ex.(Execution.label_is) (Label.is_write)⦘ ⨾ Execution.po.

Lemma sim_local_vwo_step ex:
  sim_local_vwo ex =
  (sim_local_vwo ex ∪ ⦗ex.(Execution.label_is) (Label.is_write)⦘) ⨾
  Execution.po_adj.
Proof.
  unfold sim_local_vwo. rewrite ? (union_seq' Execution.po_adj), ? seq_assoc, ? union_assoc.
  rewrite Execution.po_po_adj at 1.
  rewrite (clos_refl_union Execution.po), union_seq, eq_seq.
  rewrite ? (seq_union' (Execution.po ⨾ Execution.po_adj) Execution.po_adj), ? seq_assoc, ? union_assoc.
  refl.
Qed.

Definition sim_local_vcap ex :=
  Execution.ctrl ex ∪ (ex.(Execution.addr) ⨾ Execution.po).

Lemma sim_local_vcap_step ex:
  sim_local_vcap ex =
  (sim_local_vcap ex ∪ (ex.(Execution.ctrl0) ∪ ex.(Execution.addr))) ⨾
  Execution.po_adj.
Proof.
  unfold sim_local_vcap, Execution.ctrl.
  rewrite (union_seq' Execution.po_adj), ? seq_assoc, ? union_assoc.
  rewrite <- union_seq.
  rewrite Execution.po_po_adj at 1.
  rewrite (clos_refl_union Execution.po), (union_seq _ eq), eq_seq.
  rewrite ? (seq_union' (Execution.po ⨾ Execution.po_adj) Execution.po_adj), ? seq_assoc, ? union_assoc.
  refl.
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
  <<OB: Execution.ob ex eid1 eid2>>.
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
      (RFI: Execution.rfi ex eid1 eid2):
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
