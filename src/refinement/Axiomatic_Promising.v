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

Require Import Basic.
Require Import HahnRelationsMore.
Require Import Order.
Require Import Time.
Require Import Lang.
Require Import Promising.
Require Import Axiomatic.

Set Implicit Arguments.


Definition mem_of_ex
           (ex:Execution.t)
           (ob:list eidT):
  Memory.t :=
  filter_map
    (fun eid =>
       match Execution.label eid ex with
       | Some (Label.write ex ord loc val) => Some (Msg.mk loc val eid.(fst))
       | _ => None
       end)
    ob.

Lemma mem_of_ex_app ex ob1 ob2:
  mem_of_ex ex (ob1 ++ ob2) = mem_of_ex ex ob1 ++ mem_of_ex ex ob2.
Proof. apply filter_map_app. Qed.

Lemma mem_of_ex_in_length
      ex ob eid
      (IN: List.In eid ob)
      (EID: ex.(Execution.label_is) Label.is_write eid):
  length (mem_of_ex ex ob) <> 0.
Proof.
  eapply filter_map_in_length; eauto.
  inv EID. rewrite EID0. destruct l; ss.
Qed.

Inductive sim_mem (ex:Execution.t) (mem: Memory.t): Prop :=
| sim_mem_intro
    ob
    (EIDS: Permutation ob (Execution.eids ex))
    (MEM: mem = mem_of_ex ex ob)
.
Hint Constructors sim_mem.

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

Definition view_of_eid (ex:Execution.t) (ob: list eidT) (eid:eidT): option Time.t :=
  option_map
    (fun n => length (mem_of_ex ex (List.firstn (S n) ob)))
    (List_find_pos (fun eid' => eid' == eid) ob).

Lemma view_of_eid_inv
      ex ob eid view
      (VIEW: view_of_eid ex ob eid = Some view):
  exists n,
    <<N: List.nth_error ob n = Some eid>> /\
    <<VIEW: view = length (mem_of_ex ex (List.firstn (S n) ob))>>.
Proof.
  unfold view_of_eid in *.
  destruct ((List_find_pos (fun eid' : eidT => equiv_dec eid' eid) ob)) eqn:POS; inv VIEW.
  exploit List_find_pos_inv; eauto. i. des. destruct (equiv_dec a eid); ss. inv e.
  esplits; eauto.
Qed.

Lemma view_of_eid_ob_write_write
      ex ob eid1 eid2 view loc
      (VIEW1: view_of_eid ex ob eid1 = Some view)
      (VIEW2: view_of_eid ex ob eid2 = Some view)
      (WRITE1: Execution.label_is ex (Label.is_writing loc) eid1)
      (WRITE2: Execution.label_is ex (Label.is_writing loc) eid2):
  eid1 = eid2.
Proof.
  exploit view_of_eid_inv; try exact VIEW1; eauto. i. des.
  exploit view_of_eid_inv; try exact VIEW2; eauto. i. des.
  inv WRITE1. apply Label.is_writing_inv in LABEL. des. subst.
  inv WRITE2. apply Label.is_writing_inv in LABEL. des. subst.
  destruct (Nat.compare_spec n n0).
  - subst. congr.
  - rewrite (@List_firstn_le (S n) (S n0)) in VIEW0; [|lia].
    rewrite mem_of_ex_app, List.app_length in VIEW0.
    apply plus_minus in VIEW0. rewrite Nat.sub_diag, Nat.sub_succ in VIEW0.
    exploit List_nth_error_skipn; eauto. i.
    exploit @List_nth_error_firstn; [eauto| |i].
    { instantiate (1 := (n0 - n)). lia. }
    exploit List.nth_error_In; eauto. i.
    exfalso. eapply mem_of_ex_in_length; eauto.
  - symmetry in VIEW0.
    rewrite (@List_firstn_le (S n0) (S n)) in VIEW0; [|lia].
    rewrite mem_of_ex_app, List.app_length in VIEW0.
    apply plus_minus in VIEW0. rewrite Nat.sub_diag, Nat.sub_succ in VIEW0.
    exploit List_nth_error_skipn; try exact N; eauto. i.
    exploit @List_nth_error_firstn; [eauto| |i].
    { instantiate (1 := (n - n0)). lia. }
    exploit List.nth_error_In; eauto. i.
    exfalso. eapply mem_of_ex_in_length; eauto.
Qed.

Lemma view_of_eid_ob
      ex rel ob eid1 eid2 view1 view2
      (LINEARIZED: linearized rel ob)
      (OB: rel eid1 eid2)
      (VIEW1: view_of_eid ex ob eid1 = Some view1)
      (VIEW2: view_of_eid ex ob eid2 = Some view2):
  le view1 view2.
Proof.
  exploit view_of_eid_inv; try exact VIEW1; eauto. i. des.
  exploit view_of_eid_inv; try exact VIEW2; eauto. i. des.
  subst. exploit LINEARIZED; try exact OB; eauto. i.
  erewrite (@List_firstn_le (S n) (S n0)); [|lia].
  rewrite mem_of_ex_app, List.app_length. unfold le. lia.
Qed.

Lemma view_of_eid_ob_write
      ex rel ob eid1 eid2 view1 view2 loc
      (LINEARIZED: linearized rel ob)
      (OB: rel eid1 eid2)
      (VIEW1: view_of_eid ex ob eid1 = Some view1)
      (VIEW2: view_of_eid ex ob eid2 = Some view2)
      (WRITE2: Execution.label_is ex (Label.is_writing loc) eid2):
  view1 < view2.
Proof.
  exploit view_of_eid_inv; try exact VIEW1; eauto. i. des.
  exploit view_of_eid_inv; try exact VIEW2; eauto. i. des.
  subst. exploit LINEARIZED; try exact OB; eauto. i.
  erewrite (@List_firstn_le (S n) (S n0)); [|lia].
  rewrite mem_of_ex_app, List.app_length. apply Nat.lt_add_pos_r.
  exploit List_nth_error_skipn; eauto. i.
  exploit List_nth_error_firstn; [eauto| |i].
  { instantiate (1 := (S n0 - S n)). lia. }
  exploit List.nth_error_In; eauto. i.
  apply neq_0_lt. ii. eapply mem_of_ex_in_length; eauto.
  inv WRITE2. apply Label.is_writing_inv in LABEL. des. subst.
  econs; eauto.
Qed.

Inductive sim_view (ex:Execution.t) (ob: list eidT) (eids:eidT -> Prop) (view:Time.t): Prop :=
| sim_view_bot
    (VIEW: view = bot)
| sim_view_event
    eid v
    (EID: eids eid)
    (VIEW_OF_EID: view_of_eid ex ob eid = Some v)
    (VIEW: le view v)
.
Hint Constructors sim_view.

Lemma sim_view_join ex ob pred v1 v2
      (V1: sim_view ex ob pred v1)
      (V2: sim_view ex ob pred v2):
  sim_view ex ob pred (join v1 v2).
Proof.
  inv V1.
  { rewrite join_comm, bot_join; [|exact Time.order]. ss. }
  inv V2.
  { rewrite bot_join; [|exact Time.order]. econs 2; eauto. }

  generalize (Time.max_spec_le v1 v2). i. des.
  - unfold join, Time.join. rewrite H0. econs 2; try exact VIEW_OF_EID0; eauto.
  - unfold join, Time.join. rewrite H0. econs 2; try exact VIEW_OF_EID; eauto.
Qed.

Lemma sim_view_le ex ob pred1 pred2
      (PRED: pred1 <1= pred2):
  sim_view ex ob pred1 <1= sim_view ex ob pred2.
Proof.
  i. inv PR.
  - econs 1. ss.
  - econs 2; eauto.
Qed.

Inductive sim_val (tid:Id.t) (ex:Execution.t) (ob: list eidT) (avala:ValA.t (A:=nat -> Prop)) (vala:ValA.t (A:=View.t (A:=unit))): Prop :=
| sim_val_intro
    (VAL: avala.(ValA.val) = vala.(ValA.val))
    (VIEW: sim_view ex ob (fun eid => eid.(fst) = tid /\ avala.(ValA.annot) eid.(snd)) vala.(ValA.annot).(View.ts))
.
Hint Constructors sim_val.

Inductive sim_rmap (tid:Id.t) (ex:Execution.t) (ob: list eidT) (armap:RMap.t (A:=nat -> Prop)) (rmap:RMap.t (A:=View.t (A:=unit))): Prop :=
| sim_rmap_intro
    (RMAP: IdMap.Forall2 (fun reg => sim_val tid ex ob) armap rmap)
.
Hint Constructors sim_rmap.

Inductive sim_state (tid:Id.t) (ex:Execution.t) (ob: list eidT) (astate:State.t (A:=nat -> Prop)) (state:State.t (A:=View.t (A:=unit))): Prop :=
| sim_state_intro
    (STMTS: astate.(State.stmts) = state.(State.stmts))
    (RMAP: sim_rmap tid ex ob astate.(State.rmap) state.(State.rmap))
.
Hint Constructors sim_state.

Lemma sim_rmap_add
      tid ex ob armap rmap reg avala vala
      (SIM: sim_rmap tid ex ob armap rmap)
      (VAL: sim_val tid ex ob avala vala):
  sim_rmap tid ex ob (RMap.add reg avala armap) (RMap.add reg vala rmap).
Proof.
  econs. ii. unfold RMap.add. rewrite ? IdMap.add_spec.
  inv SIM. condtac; eauto.
Qed.

Lemma sim_rmap_expr
      tid ex ob armap rmap e
      (SIM: sim_rmap tid ex ob armap rmap):
  sim_val tid ex ob (sem_expr armap e) (sem_expr rmap e).
Proof.
  inv SIM. induction e; s.
  - (* const *)
    econs; ss. econs 1; ss.
  - (* reg *)
    specialize (RMAP reg). unfold RMap.find. inv RMAP; ss.
    econs; ss. econs 1; ss.
  - (* op1 *)
    inv IHe. econs; ss. congr.
  - (* op2 *)
    inv IHe1. inv IHe2. econs; ss.
    + congr.
    + apply sim_view_join; eapply sim_view_le; eauto.
      * s. i. des. subst. esplits; eauto. left. ss.
      * s. i. des. subst. esplits; eauto. right. ss.
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
      exploit EX.(Valid.RF). intros [RF1 RF2].
      exploit RF2.
      { esplits; eauto. }
      i. des.
      econs. left. left. left. econs; eauto.
    + destruct (equiv_dec loc0 loc); ss. inv e. econs; eauto. apply Label.write_is_writing.
Qed.

Definition sim_local_vrp ex :=
  (Execution.po ⨾
   ⦗ex.(Execution.label_is) (eq (Label.barrier Barrier.dmbsy))⦘ ⨾
   Execution.po) ∪

  (⦗ex.(Execution.label_is) Label.is_read⦘ ⨾
   Execution.po ⨾
   ⦗ex.(Execution.label_is) (eq (Label.barrier Barrier.dmbld))⦘ ⨾
   Execution.po) ∪

  ((ex.(Execution.ctrl) ∪ (ex.(Execution.addr) ⨾ Execution.po)) ⨾
   ⦗ex.(Execution.label_is) (eq (Label.barrier Barrier.isb))⦘ ⨾
   Execution.po) ∪

  (⦗ex.(Execution.label_is) (Label.is_acquire_pc)⦘ ⨾
   Execution.po).

Lemma sim_local_vrp_step ex:
  sim_local_vrp ex =
  (sim_local_vrp ex ∪
   ((Execution.po ⨾
    ⦗ex.(Execution.label_is) (eq (Label.barrier Barrier.dmbsy))⦘) ∪

    (⦗ex.(Execution.label_is) Label.is_read⦘ ⨾
     Execution.po ⨾
     ⦗ex.(Execution.label_is) (eq (Label.barrier Barrier.dmbld))⦘) ∪

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
  - right. left. left. left. left. left. ss.
  - right. left. left. left. right. ss.
  - left. left. right. right.
    inv H0. des. econs. splits; eauto.
    right. rewrite seq_assoc. econs. splits; eauto. econs; ss. econs; eauto.
  - right. left. left. right. ss.
Qed.

Definition sim_local_vwp ex :=
  (Execution.po ⨾
   ⦗ex.(Execution.label_is) (eq (Label.barrier Barrier.dmbsy))⦘ ⨾
   Execution.po) ∪

  (⦗ex.(Execution.label_is) Label.is_read⦘ ⨾
   Execution.po ⨾
   ⦗ex.(Execution.label_is) (eq (Label.barrier Barrier.dmbld))⦘ ⨾
   Execution.po) ∪

  (⦗ex.(Execution.label_is) Label.is_write⦘ ⨾
   Execution.po ⨾
   ⦗ex.(Execution.label_is) (eq (Label.barrier Barrier.dmbst))⦘ ⨾
   Execution.po) ∪

  (⦗ex.(Execution.label_is) (Label.is_acquire_pc)⦘ ⨾
   Execution.po).

Lemma sim_local_vwp_step ex:
  sim_local_vwp ex =
  (sim_local_vwp ex ∪
   ((Execution.po ⨾
     ⦗ex.(Execution.label_is) (eq (Label.barrier Barrier.dmbsy))⦘) ∪

    (⦗ex.(Execution.label_is) Label.is_read⦘ ⨾
     Execution.po ⨾
     ⦗ex.(Execution.label_is) (eq (Label.barrier Barrier.dmbld))⦘) ∪

    (⦗ex.(Execution.label_is) Label.is_write⦘ ⨾
     Execution.po ⨾
     ⦗ex.(Execution.label_is) (eq (Label.barrier Barrier.dmbst))⦘) ∪

    (⦗ex.(Execution.label_is) (Label.is_acquire_pc)⦘))) ⨾
  Execution.po_adj.
Proof.
  unfold sim_local_vwp. rewrite ? (union_seq' Execution.po_adj), ? seq_assoc, ? union_assoc.
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
  - right. left. left. left. left. right.
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
    { econs; eauto. apply Label.read_is_reading. }
    { econs; eauto. apply Label.write_is_writing. }
    { econs; ss. }
    i. inv x1.
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

Inductive sim_local (tid:Id.t) (ex:Execution.t) (ob: list eidT) (alocal:ALocal.t) (local:Local.t (A:=unit)): Prop := mk_sim_local {
  COH: forall loc,
        sim_view
          ex ob
          (inverse (sim_local_coh ex loc) (eq (tid, List.length (alocal.(ALocal.labels)))))
          (local.(Local.coh) loc);
  VRP: sim_view
         ex ob
         (inverse (sim_local_vrp ex) (eq (tid, List.length (alocal.(ALocal.labels)))))
         local.(Local.vrp).(View.ts);
  VWP: sim_view
         ex ob
         (inverse (sim_local_vwp ex) (eq (tid, List.length (alocal.(ALocal.labels)))))
         local.(Local.vwp).(View.ts);
  VRM: sim_view
         ex ob
         (inverse (sim_local_vrm ex) (eq (tid, List.length (alocal.(ALocal.labels)))))
         local.(Local.vrm).(View.ts);
  VWM: sim_view
         ex ob
         (inverse (sim_local_vwm ex) (eq (tid, List.length (alocal.(ALocal.labels)))))
         local.(Local.vwm).(View.ts);
  VCAP:
       sim_view
         ex ob
         (inverse (sim_local_vcap ex) (eq (tid, List.length (alocal.(ALocal.labels)))))
         local.(Local.vcap).(View.ts);
  VREL: sim_view
          ex ob
          (inverse (sim_local_vrel ex) (eq (tid, List.length (alocal.(ALocal.labels)))))
          local.(Local.vrel).(View.ts);
  FWDBANK: forall loc,
      match local.(Local.fwdbank) loc with
      | Some fwd =>
        exists eid,
        <<WRITE: sim_local_fwd ex loc eid (tid, List.length (alocal.(ALocal.labels)))>> /\
        <<TS: view_of_eid ex ob eid = Some fwd.(FwdItem.ts)>> /\
        <<VIEW: sim_view
                  ex ob
                  (inverse (ex.(Execution.addr) ∪ ex.(Execution.data)) (eq eid))
                  fwd.(FwdItem.view).(View.ts)>> /\
        <<EX: fwd.(FwdItem.ex) <-> ex.(Execution.label_is) (Label.is_ex) eid>>
      | None =>
        forall eid, ~ (inverse (sim_local_fwd_none ex loc) (eq (tid, List.length (alocal.(ALocal.labels)))) eid)
      end;
  EXBANK: opt_rel
            (fun aexbank exbank =>
               (forall eid v, ex.(Execution.rf) eid (tid, aexbank) -> view_of_eid ex ob eid = Some v -> le v exbank) /\
               exbank <> bot /\
               sim_view
                 ex ob
                 (inverse ex.(Execution.rf) (eq (tid, aexbank)))
                 exbank)
            alocal.(ALocal.exbank) local.(Local.exbank);
  PROMISES: forall view (VIEW: Promises.lookup view local.(Local.promises)),
      exists n,
        <<N: (length alocal.(ALocal.labels)) <= n>> /\
        <<WRITE: ex.(Execution.label_is) Label.is_write (tid, n)>> /\
        <<VIEW: view_of_eid ex ob (tid, n) = Some view>>;
}.
Hint Constructors sim_local.

Inductive sim_eu (tid:Id.t) (ex:Execution.t) (ob: list eidT) (aeu:AExecUnit.t) (eu:ExecUnit.t (A:=unit)): Prop :=
| sim_eu_intro
    (STATE: sim_state tid ex ob aeu.(AExecUnit.state) eu.(ExecUnit.state))
    (LOCAL: sim_local tid ex ob aeu.(AExecUnit.local) eu.(ExecUnit.local))
    (MEM: eu.(ExecUnit.mem) = mem_of_ex ex ob)
.
Hint Constructors sim_eu.

Lemma label_read_mem_of_ex
      eid ex ob exm ord loc val
      (OB: Permutation ob (Execution.eids ex))
      (LABEL: Execution.label eid ex = Some (Label.read exm ord loc val)):
  exists view,
    <<VIEW: view_of_eid ex ob eid = Some view>>.
Proof.
  generalize (Execution.eids_spec ex). i. des. rename NODUP into NODUP0.
  specialize (LABEL0 eid). rewrite LABEL in LABEL0.
  inv LABEL0. clear H0. exploit H; [congr|]. clear H. intro IN0.
  symmetry in OB. exploit Permutation_in; eauto. intro IN.
  exploit HahnList.Permutation_nodup; eauto. intro NODUP.
  generalize (List_in_find_pos _ ob IN). i. des.
  unfold view_of_eid. rewrite H. s. eauto.
Qed.

Lemma label_write_mem_of_ex_msg
      eid ex ob exm ord loc val
      (OB: Permutation ob (Execution.eids ex))
      (LABEL: Execution.label eid ex = Some (Label.write exm ord loc val)):
  exists n,
    <<VIEW: view_of_eid ex ob eid = Some (S n)>> /\
    <<MSG: List.nth_error (mem_of_ex ex ob) n = Some (Msg.mk loc val eid.(fst))>>.
Proof.
  generalize (Execution.eids_spec ex). i. des. rename NODUP into NODUP0.
  specialize (LABEL0 eid). rewrite LABEL in LABEL0.
  inv LABEL0. clear H0. exploit H; [congr|]. clear H. intro IN0.
  symmetry in OB. exploit Permutation_in; eauto. intro IN.
  exploit HahnList.Permutation_nodup; eauto. intro NODUP.
  generalize (List_in_find_pos _ ob IN). i. des.
  unfold view_of_eid. rewrite H.
  exploit List_find_pos_inv; eauto. i. des.
  destruct (equiv_dec a eid); [|done]. inversion e. subst.
  esplits.
  - unfold option_map. erewrite List_firstn_S; eauto.
    rewrite mem_of_ex_app, List.app_length.
    unfold mem_of_ex at 2. s. rewrite LABEL. s. rewrite Nat.add_1_r. ss.
  - rewrite <- (List.firstn_skipn n ob) at 1.
    rewrite mem_of_ex_app, List.nth_error_app2; [|lia].
    erewrite Nat.sub_diag, List_skipn_cons; eauto. s.
    unfold mem_of_ex. s. rewrite LABEL. ss.
Qed.

Lemma label_write_mem_of_ex
      eid ex ob exm ord loc val
      (OB: Permutation ob (Execution.eids ex))
      (LABEL: Execution.label eid ex = Some (Label.write exm ord loc val)):
  exists n,
    <<VIEW: view_of_eid ex ob eid = Some (S n)>> /\
    <<READ: Memory.read loc (S n) (mem_of_ex ex ob) = Some val>> /\
    <<MSG: Memory.get_msg (S n) (mem_of_ex ex ob) = Some (Msg.mk loc val eid.(fst))>>.
Proof.
  exploit label_write_mem_of_ex_msg; eauto. i. des.
  esplits; eauto.
  unfold Memory.read. s. rewrite MSG. s. condtac; [|congr]. ss.
Qed.

Lemma in_mem_of_ex
      ex ob view msg
      (NODUP: List.NoDup ob)
      (IN: List.nth_error (mem_of_ex ex ob) view = Some msg):
  exists n ex1 ord1,
    <<LABEL: Execution.label (msg.(Msg.tid), n) ex = Some (Label.write ex1 ord1 msg.(Msg.loc) msg.(Msg.val))>> /\
    <<VIEW: view_of_eid ex ob (msg.(Msg.tid), n) = Some (S view)>>.
Proof.
  unfold mem_of_ex in IN. exploit nth_error_filter_map_inv; eauto. i. des.
  destruct (Execution.label a ex) eqn:LABEL; ss. destruct t; inv FA. destruct a. ss.
  esplits.
  - eauto.
  - unfold view_of_eid.
    erewrite List_nth_error_find_pos; eauto. s. f_equal. ss.
Qed.

Lemma sim_eu_step
      p ex ob tid aeu1 eu1 aeu2
      (EX: Valid.ex p ex)
      (OB: Permutation ob (Execution.eids ex))
      (LINEARIZED: linearized ex.(Execution.ob) ob)
      (SIM: sim_eu tid ex ob aeu1 eu1)
      (STEP: AExecUnit.step aeu1 aeu2)
      (LABEL: forall n label (LABEL: List.nth_error aeu2.(AExecUnit.local).(ALocal.labels) n = Some label),
          Execution.label (tid, n) ex = Some label)
      (ADDR: tid_lift tid aeu2.(AExecUnit.local).(ALocal.addr) ⊆ ex.(Execution.addr))
      (DATA: tid_lift tid aeu2.(AExecUnit.local).(ALocal.data) ⊆ ex.(Execution.data))
      (CTRL: tid_lift tid aeu2.(AExecUnit.local).(ALocal.ctrl) ⊆ ex.(Execution.ctrl))
      (RMW: tid_lift tid aeu2.(AExecUnit.local).(ALocal.rmw) ⊆ ex.(Execution.rmw)):
  exists eu2,
    <<STEP: ExecUnit.state_step tid eu1 eu2>> /\
    <<SIM: sim_eu tid ex ob aeu2 eu2>>.
Proof.
  destruct eu1 as [[stmts1 rmap1] local1].
  destruct aeu1 as [[astmts1 armap1] alocal1].
  destruct aeu2 as [[astmts2 armap2] alocal2].
  inv SIM. inv STATE. ss. subst. rename LOCAL into SIM_LOCAL.
  inv STEP. ss. inv STATE; inv LOCAL; inv EVENT; ss.
  - (* skip *)
    eexists (ExecUnit.mk _ _ _). esplits.
    + econs 1. econs; ss.
      { econs; ss. }
      econs 1; ss.
    + econs; ss.
      inv SIM_LOCAL; econs; eauto. s.
      apply sim_view_join; ss. econs. ss.
  - (* assign *)
    eexists (ExecUnit.mk _ _ _). esplits.
    + econs 1. econs; ss.
      { econs; ss. }
      econs 1; ss.
    + econs; ss.
      * econs; ss. apply sim_rmap_add; ss. apply sim_rmap_expr; ss.
      * inv SIM_LOCAL; econs; eauto. s.
        apply sim_view_join; ss. econs. ss.
  - (* read *)
    exploit LABEL.
    { rewrite List.nth_error_app2; [|refl]. rewrite Nat.sub_diag. ss. }
    intro LABEL_LEN.
    exploit EX.(Valid.RF). intros [RF _]. exploit RF; eauto. clear RF. i. des.
    exploit sim_rmap_expr; eauto. instantiate (1 := eloc). intro X. inv X.
    exploit label_write_mem_of_ex; eauto. i. des.
    exploit label_read_mem_of_ex; eauto. i. des.

    assert (SIM_LOC: sim_view ex ob
                              (fun eid : eidT => fst eid = tid /\ ALocal.next_eid alocal1 = snd eid)
                              (ValA.annot (sem_expr rmap1 eloc)).(View.ts)).
    { econs 2; eauto; ss.
      inv VIEW.
      { rewrite VIEW2. apply bot_spec. }
      rewrite VIEW2. des. subst.
      eapply view_of_eid_ob; eauto.
      left. left. right. left. econs. splits; [|eauto]. left. apply ADDR. econs; ss. right. ss.
    }

    assert (SIM_VRP: sim_view ex ob
                              (fun eid : eidT => fst eid = tid /\ ALocal.next_eid alocal1 = snd eid)
                              local1.(Local.vrp).(View.ts)).
    { econs 2; eauto; ss.
      generalize SIM_LOCAL.(VRP). intro VRP.
      inv VRP.
      { rewrite VIEW2. apply bot_spec. }
      rewrite VIEW2. eapply view_of_eid_ob; eauto.
      inv EID. exploit sim_local_vrp_spec; eauto.
    }

    assert (SIM_VREL: sim_view ex ob
                               (fun eid : eidT => fst eid = tid /\ ALocal.next_eid alocal1 = snd eid)
                               (ifc (OrdR.ge ord OrdR.acquire) (Local.vrel local1)).(View.ts)).
    { econs 2; eauto; ss.
      generalize SIM_LOCAL.(VREL). intro VREL.
      destruct (OrdR.ge ord OrdR.acquire) eqn:ORD; ss; cycle 1.
      { apply bot_spec. }
      inv VREL.
      { rewrite VIEW2. apply bot_spec. }
      rewrite VIEW2. eapply view_of_eid_ob; eauto.
      inv EID. exploit sim_local_vrel_spec; eauto.
    }

    assert (SIM_FWD: sim_view ex ob
                              (fun eid : eidT => fst eid = tid /\ ALocal.next_eid alocal1 = snd eid)
                              (match Local.fwdbank local1 (ValA.val (sem_expr armap1 eloc)) with
                               | Some fwd => FwdItem.read_view fwd (S n) ord
                               | None => View.mk (S n) bot
                               end).(View.ts)).
    { econs 2; eauto; ss.
      generalize (SIM_LOCAL.(FWDBANK) (ValA.val (sem_expr armap1 eloc))).
      destruct (Local.fwdbank local1 (ValA.val (sem_expr armap1 eloc))) eqn:FWD.
      - (* fwdbank = Some *)
        destruct t. s. i. des. unfold FwdItem.read_view. s. condtac.
        + (* forwarded *)
          apply Bool.andb_true_iff in X. des.
          destruct (equiv_dec ts (S n)); ss. inv e.
          assert (eid2 = eid).
          { eapply view_of_eid_ob_write_write; eauto.
            - econs; eauto. apply Label.write_is_writing.
            - apply WRITE.
          }
          subst. inv VIEW2.
          { rewrite VIEW3. apply bot_spec. }
          rewrite VIEW3. eapply view_of_eid_ob; eauto.
          inv EID. inv WRITE. inv PO. ss. subst.
          left. left. right. left.
          econs. splits; eauto. econs 2. econs; eauto.
        + (* not forwarded *)
          eapply view_of_eid_ob; eauto.
          destruct eid2. destruct (t == tid); cycle 1.
          { left. left. left. left. left. econs; ss. }
          inv e.
          exploit rfi_sim_local_fwd; eauto.
          { econs; [|apply Label.write_is_writing]. eauto. }
          { econs; [|apply Label.read_is_reading]. eauto. }
          { econs; eauto. }
          i. exploit sim_local_fwd_functional; [exact WRITE|exact x0|]. i. subst.
          rewrite VIEW0 in TS. inv TS.
          apply Bool.andb_false_iff in X. des.
          { unfold Time.t in *. destruct (equiv_dec (S n) (S n)); ss. congr. }
          apply Bool.orb_false_iff in X. des. destruct ex0; ss. apply Bool.negb_false_iff in X0.
          inv WRITE. inv WRITE0. apply Label.is_writing_inv in LABEL1. des. subst.
          rewrite EID in LABEL0. inv LABEL0.
          exploit EX0; eauto. clear EX0. intro Y. inv Y. rewrite EID in EID0. inv EID0.
          exploit Valid.write_ex_codom_rmw; eauto.
          intro Y. inv Y. left. right. econs. splits.
          { econs; eauto. econs; eauto. }
          econs. splits.
          * econs; eauto.
          * econs; eauto.
      - (* fwdbank = None *)
        i. eapply view_of_eid_ob; eauto.
        destruct eid2. destruct (t == tid); cycle 1.
        { left. left. left. left. left. econs; ss. }
        inv e. exfalso. eapply H. econs; eauto. econs. splits.
        + econs; eauto. econs; eauto. apply Label.write_is_writing.
        + exploit rfi_sim_local_fwd; eauto.
          { econs; [|apply Label.write_is_writing]. eauto. }
          { econs; [|apply Label.read_is_reading]. eauto. }
          { econs; eauto. }
          intro X. apply X.
    }

    assert (SIM_EXT1: sim_view ex ob
                               (fun eid : eidT => fst eid = tid /\ ALocal.next_eid alocal1 = snd eid)
                               (joins [
                                    (ValA.annot (sem_expr rmap1 eloc));
                                    local1.(Local.vrp);
                                    (ifc (OrdR.ge ord OrdR.acquire) (Local.vrel local1))
                                ]).(View.ts)).
    { repeat apply sim_view_join; ss. econs; ss. }

    assert (SIM_EXT2: sim_view ex ob
                               (fun eid : eidT => fst eid = tid /\ ALocal.next_eid alocal1 = snd eid)
                               (join
                                  (joins [
                                       (ValA.annot (sem_expr rmap1 eloc));
                                       local1.(Local.vrp);
                                       (ifc (OrdR.ge ord OrdR.acquire) (Local.vrel local1))
                                   ])
                                  match Local.fwdbank local1 (ValA.val (sem_expr armap1 eloc)) with
                                  | Some fwd => FwdItem.read_view fwd (S n) ord
                                  | None => View.mk (S n) bot
                                  end).(View.ts)).
    { apply sim_view_join; ss. }

    eexists (ExecUnit.mk _ _ _). esplits.
    + econs. econs; ss.
      { econs; ss. }
      econs 2; ss. econs; eauto.
      * (* internal *)
        generalize (SIM_LOCAL.(COH) (ValA.val (sem_expr armap1 eloc))). intro X. inv X.
        { rewrite VIEW2. apply bot_spec. }
        rewrite VIEW2. inv EID. inv REL. inv H. inv H0.
        inv H2. apply Label.is_writing_inv in LABEL1. des. subst.
        inv H1. des. inv H.
        { exploit Valid.coherence_wr; try exact H0; eauto.
          all: try by econs; eauto; eauto using Label.write_is_writing, Label.read_is_reading.
          i. inv x1.
          - rewrite VIEW_OF_EID in VIEW0. inv VIEW0. refl.
          - eapply view_of_eid_ob; eauto. left. left. left. right. ss.
        }
        { inv H1.
          exploit EX.(Valid.RF). intros [_ RF']. exploit RF'; eauto. clear RF'. i. des.
          exploit Valid.coherence_rr; try exact H0; eauto.
          all: try by econs; eauto; eauto using Label.write_is_writing, Label.read_is_reading.
          i. inv x2.
          - rewrite VIEW_OF_EID in VIEW0. inv VIEW0. refl.
          - eapply view_of_eid_ob; eauto. left. left. left. right. ss.
        }
      * (* external *)
        ii.
        exploit in_mem_of_ex; swap 1 2; eauto.
        { eapply Permutation_NoDup; [by symmetry; eauto|].
          eapply Execution.eids_spec; eauto.
        }
        i. des. destruct msg. ss. subst.
        exploit EX.(Valid.CO). intros [CO _]. exploit CO.
        { rewrite LABEL0, LABEL1. esplits; eauto. }
        i. des; cycle 2.
        { cut (S ts < S n); [lia|].
          eapply view_of_eid_ob_write; eauto.
          - left. left. left. right. ss.
          - econs; eauto. apply Label.write_is_writing.
        }
        { subst. rewrite VIEW0 in VIEW2. inv VIEW2. lia. }
        assert (view < S ts).
        { eapply view_of_eid_ob_write; eauto.
          - left. left. left. left. right. econs; eauto.
          - econs; eauto. apply Label.write_is_writing.
        }
        inv SIM_EXT1.
        { rewrite VIEW3 in TS2. unfold bot, Time.bot in TS2. lia. }
        destruct eid. ss. des. subst.
        unfold ALocal.next_eid in VIEW_OF_EID. rewrite VIEW_OF_EID in VIEW1. inv VIEW1.
        unfold le in VIEW3. lia.
    + econs; ss.
      { econs; ss. apply sim_rmap_add; ss. }
      econs; ss.
      * (* sim_local coh *)
        i. rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_coh_step. rewrite inverse_step.
        rewrite inverse_union, fun_add_spec. condtac; cycle 1.
        { eapply sim_view_le; [|exact (SIM_LOCAL.(COH) loc)]. eauto. }
        inversion e. subst.
        destruct eid2. ss. destruct (t == tid).
        { inversion e0. subst. exploit rfi_sim_local_fwd.
          4: { econs; eauto. }
          all: eauto.
          { econs; eauto. apply Label.write_is_writing. }
          { econs; eauto. apply Label.read_is_reading. }
          i. inv x0. econs 2; try exact VIEW0; ss.
          left. econs; eauto. econs. splits.
          - econs; eauto.
          - econs. splits; eauto.
        }
        { econs 2; try exact VIEW0; ss.
          right. econs; eauto. econs. splits.
          - econs; eauto. econs; eauto. apply Label.write_is_writing.
          - econs 2. econs; eauto.
        }
      * (* sim_local vrp *)
        rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_vrp_step. rewrite inverse_step.
        rewrite ? inverse_union. apply sim_view_join.
        { eapply sim_view_le; [|exact SIM_LOCAL.(VRP)]. eauto. }
        destruct (OrdR.ge ord OrdR.acquire_pc) eqn:ORD; ss; eauto.
        eapply sim_view_le; [|exact SIM_EXT2].
        destruct x0. s. i. des. subst. right. right. econs; eauto. econs; eauto.
      * (* sim_local vwp *)
        rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_vwp_step. rewrite inverse_step.
        rewrite ? inverse_union. apply sim_view_join.
        { eapply sim_view_le; [|exact SIM_LOCAL.(VWP)]. eauto. }
        destruct (OrdR.ge ord OrdR.acquire_pc) eqn:ORD; ss; eauto.
        eapply sim_view_le; [|exact SIM_EXT2].
        destruct x0. s. i. des. subst. right. right. econs; eauto. econs; eauto.
      * (* sim_local vrm *)
        rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_vrm_step. rewrite inverse_step.
        rewrite ? inverse_union. apply sim_view_join; eauto.
        { eapply sim_view_le; [|exact SIM_LOCAL.(VRM)]. eauto. }
        eapply sim_view_le; [|exact SIM_EXT2].
        destruct x0. s. i. des. subst. right. econs; eauto. econs; eauto.
      * (* sim_local vwm *)
        rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_vwm_step. rewrite inverse_step.
        rewrite ? inverse_union. eapply sim_view_le; [|exact SIM_LOCAL.(VWM)]. eauto.
      * (* sim_local vcap *)
        rewrite List.app_length, Nat.add_1_r. apply sim_view_join.
        { eapply sim_view_le.
          { apply inverse_mon. eapply sim_local_vcap_po_adj. eauto. }
          rewrite inverse_step. apply SIM_LOCAL.
        }
        { eapply sim_view_le; [|exact VIEW]. destruct x0. s. i. des. subst.
          econs; eauto. right. econs. instantiate (1 := (tid, _)). splits.
          - apply ADDR. econs; eauto. right. econs; ss.
          - econs; ss.
        }
      * (* sim_local vrel *)
        rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_vrel_step. rewrite inverse_step.
        rewrite ? inverse_union. eapply sim_view_le; [|exact SIM_LOCAL.(VREL)]. eauto.
      * (* sim_local fwdbank *)
        rewrite List.app_length, Nat.add_1_r. i.
        generalize (SIM_LOCAL.(FWDBANK) loc). destruct (Local.fwdbank local1 loc) eqn:FWD.
        { i. des. rewrite sim_local_fwd_step. esplits; eauto.
          econs. instantiate (1 := (_, _)). splits; [|econs; ss].
          left. econs. splits; eauto. econs; eauto.
        }
        { ii. inv H0. inv REL. inv H0. rewrite Execution.po_po_adj in H2. inv H2. des.
          inv H2. destruct x0. ss. inv N. inv H0.
          - inv H1. inv H2. rewrite LABEL_LEN in EID. inv EID. ss.
          - eapply H. econs; eauto. econs; eauto.
        }
      * (* sim_local exbank *)
        destruct ex1.
        { econs. splits.
          - i. exploit EX.(Valid.RF_WF); [exact H|exact RF|]. i. subst.
            rewrite VIEW0 in H0. inv H0. refl.
          - ss.
          - econs 2; eauto. refl.
        }
        { apply SIM_LOCAL. }
      * (* sim_local promises *)
        i. exploit SIM_LOCAL.(PROMISES); eauto. i. des.
        esplits; cycle 1; eauto.
        rewrite List.app_length, Nat.add_1_r. inv N; [|lia].
        inv WRITE. destruct l; ss. congr.
  - (* write *)
    exploit LABEL.
    { rewrite List.nth_error_app2; [|refl]. rewrite Nat.sub_diag. ss. }
    intro LABEL_LEN.
    exploit label_write_mem_of_ex; eauto. i. des.
    exploit sim_rmap_expr; eauto. instantiate (1 := eloc). intro X. inv X.
    exploit sim_rmap_expr; eauto. instantiate (1 := eval). intro X. inv X.
    eexists (ExecUnit.mk _ _ _). esplits.
    + econs. econs; ss.
      { econs; ss. }
      econs 3; ss.
      econs; try refl.
      all: cycle 1.
      { rewrite <- VAL, <- VAL0. eauto. }
      econs; try refl.
      * (* internal *)
        rewrite <- VAL.
        generalize (SIM_LOCAL.(COH) (ValA.val (sem_expr armap1 eloc))).
        intro X. inv X.
        { rewrite VIEW2. unfold bot, Time.bot. lia. }
        eapply Time.le_lt_trans; eauto. inv EID. inv REL. inv H. inv H0.
        inv H2. apply Label.is_writing_inv in LABEL0. des. subst.
        inv H1. des. inv H.
        { exploit Valid.coherence_ww; try exact H0; eauto.
          all: try by econs; eauto; eauto using Label.write_is_writing, Label.read_is_reading.
          i. eapply view_of_eid_ob_write; eauto.
          - left. left. left. right. ss.
          - econs; eauto. apply Label.write_is_writing.
        }
        { inv H1.
          exploit EX.(Valid.RF). intros [_ RF1]. exploit RF1; eauto. clear RF1. i. des.
          exploit Valid.coherence_rw; try exact H0; eauto.
          all: try by econs; eauto; eauto using Label.write_is_writing, Label.read_is_reading.
          i. eapply view_of_eid_ob_write; eauto.
          - left. left. left. right. ss.
          - econs; eauto. apply Label.write_is_writing.
        }
      * (* external *)
        unfold lt. apply le_n_S. s. repeat apply join_spec.
        { inv VIEW0.
          { rewrite VIEW2. apply bot_spec. }
          rewrite VIEW2. destruct eid. ss. des. subst.
          apply lt_n_Sm_le. eapply view_of_eid_ob_write; eauto.
          - left. left. right. left. econs. splits.
            + instantiate (1 := (tid, _)).  left. apply ADDR. econs; eauto. right. ss.
            + eauto.
          - econs; eauto. apply Label.write_is_writing.
        }
        { inv VIEW1.
          { rewrite VIEW2. apply bot_spec. }
          rewrite VIEW2. destruct eid. ss. des. subst.
          apply lt_n_Sm_le. eapply view_of_eid_ob_write; eauto.
          - left. left. right. left. econs. splits.
            + instantiate (1 := (tid, _)).  right. apply DATA. econs; eauto. right. ss.
            + eauto.
          - econs; eauto. apply Label.write_is_writing.
        }
        { generalize SIM_LOCAL.(VCAP). intro X. inv X.
          { rewrite VIEW2. apply bot_spec. }
          rewrite VIEW2. inv EID.
          apply lt_n_Sm_le. eapply view_of_eid_ob_write; eauto.
          - left. left. right. right. econs. splits; eauto.
            left. econs; eauto.
          - econs; eauto. apply Label.write_is_writing.
        }
        { generalize SIM_LOCAL.(VWP). intro X. inv X.
          { rewrite VIEW2. apply bot_spec. }
          rewrite VIEW2. inv EID.
          apply lt_n_Sm_le. eapply view_of_eid_ob_write; eauto.
          - unfold sim_local_vwp in REL.
            repeat match goal with
                   | [H: (_ ∪ _) _ _ |- _] => inv H
                   end.
            + inv H. des. inv H1. des. inv H.
              right. left. left. left. left. left. econs. splits; eauto. econs. splits; eauto. econs; eauto.
            + inv H. des. inv H0. inv H1. des. inv H0. des. inv H1.
              right. left. left. left. right. econs. splits.
              { econs; eauto. }
              econs. splits; eauto. econs. splits; eauto. econs; eauto.
            + inv H0. des. inv H. inv H0. des. inv H0. des. inv H1.
              right. left. right. econs. splits.
              { econs; eauto. }
              econs. splits; eauto. econs. splits.
              { econs; eauto. }
              econs. splits; eauto. econs; eauto.
            + inv H. des.
              right. left. left. right. econs. splits; eauto.
          - econs; eauto. apply Label.write_is_writing.
        }
        { destruct (OrdW.ge ord OrdW.release) eqn:ORD; s; cycle 1.
          { apply bot_spec. }
          generalize SIM_LOCAL.(VRM). intro X. inv X.
          { rewrite VIEW2. apply bot_spec. }
          rewrite VIEW2. inv EID.
          apply lt_n_Sm_le. eapply view_of_eid_ob_write; eauto.
          - inv REL. des. inv H.
            right. right. econs. splits; eauto. econs; eauto.
          - econs; eauto. apply Label.write_is_writing.
        }
        { destruct (OrdW.ge ord OrdW.release) eqn:ORD; s; cycle 1.
          { apply bot_spec. }
          generalize SIM_LOCAL.(VWM). intro X. inv X.
          { rewrite VIEW2. apply bot_spec. }
          rewrite VIEW2. inv EID.
          apply lt_n_Sm_le. eapply view_of_eid_ob_write; eauto.
          - inv REL. des. inv H.
            right. right. econs. splits; eauto. econs; eauto.
          - econs; eauto. apply Label.write_is_writing.
        }
        { apply bot_spec. }
      * (* exclusive *)
        i. specialize (EX0 H). des. inv EX1.
        apply Label.is_reading_inv in PRED. des. subst. symmetry in H1.
        generalize (SIM_LOCAL.(EXBANK)). rewrite EX0. intro X. inv X. des.
        exploit List.nth_error_Some. rewrite H1. intros [X _]. exploit X; ss. clear X. intro X.
        exploit LABEL.
        { rewrite List.nth_error_app1; eauto. }
        intro LABEL_READ. inv REL1; ss. inv EID. exploit REL; eauto. i.
        assert (v = b) by (apply Time.le_antisymm; ss). subst.
        esplits; eauto. destruct ex1; ss. ii.
        exploit in_mem_of_ex; swap 1 2; eauto.
        { eapply Permutation_NoDup; [by symmetry; eauto|].
          eapply Execution.eids_spec; eauto.
        }
        i. des. destruct msg. ss. subst.

        exploit EX.(Valid.CO). intros [CO _]. exploit CO.
        { rewrite LABEL0. rewrite LABEL_LEN. esplits; eauto. f_equal. f_equal. ss. }
        clear CO. i. des; cycle 2.
        { cut (S n < S ts); [lia|].
          eapply view_of_eid_ob_write; eauto.
          - left. left. left. right. ss.
          - econs; eauto. apply Label.write_is_writing.
        }
        { inv x0. congr. }

        exploit Valid.rf_inv_write; eauto. i. des.
        exploit EX.(Valid.CO). intros [CO _]. exploit CO.
        { rewrite LABEL0. rewrite LABEL1. esplits; eauto. f_equal. f_equal. ss. }
        clear CO. i. des.
        { subst. rewrite VIEW_OF_EID in VIEW3. inv VIEW3. lia. }
        { cut (S ts < b); [lia|].
          eapply view_of_eid_ob_write; eauto.
          - left. left. left. right. ss.
          - econs; eauto. apply Label.write_is_writing.
        }

        eapply EX.(Valid.ATOMIC). econs; cycle 1.
        { econs. splits.
          - econs.
            + econs; eauto.
            + econs. s. congr.
          - econs; eauto.
        }
        { apply RMW. econs; eauto. right. econs; eauto. }
    + econs; ss.
      { econs; ss. apply sim_rmap_add; ss. econs; ss. econs 1. ss. }
      econs; ss.
      * i. rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_coh_step. rewrite inverse_step.
        rewrite inverse_union, fun_add_spec. condtac; ss.
        { inversion e. subst. econs 2; eauto; [|refl]. right. econs; eauto.
          econs. splits; eauto. econs; eauto. econs; eauto.
          rewrite VAL. apply Label.write_is_writing.
        }
        { eapply sim_view_le; [|exact (SIM_LOCAL.(COH) loc)]. eauto. }
      * rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_vrp_step. rewrite inverse_step.
        rewrite ? inverse_union. eapply sim_view_le; [|exact SIM_LOCAL.(VRP)]. eauto.
      * rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_vwp_step. rewrite inverse_step.
        rewrite ? inverse_union. eapply sim_view_le; [|exact SIM_LOCAL.(VWP)]. eauto.
      * rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_vrm_step. rewrite inverse_step.
        rewrite ? inverse_union. eapply sim_view_le; [|exact SIM_LOCAL.(VRM)]. eauto.
      * rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_vwm_step. rewrite inverse_step.
        rewrite ? inverse_union. apply sim_view_join.
        { eapply sim_view_le; [|exact SIM_LOCAL.(VWM)]. eauto. }
        { eapply sim_view_le; [by right; eauto|]. econs 2; eauto.
          - econs; eauto. econs; eauto.
          - refl.
        }
      * rewrite List.app_length, Nat.add_1_r. apply sim_view_join.
        { eapply sim_view_le.
          { apply inverse_mon. eapply sim_local_vcap_po_adj. eauto. }
          rewrite inverse_step. apply SIM_LOCAL.
        }
        { eapply sim_view_le; [|by eauto]. s. i. des. subst.
          econs; eauto. right. econs. instantiate (1 := (fst x0, _)). splits.
          - apply ADDR. econs; eauto. right. econs; ss.
          - econs; ss.
        }
      * rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_vrel_step. rewrite inverse_step.
        rewrite ? inverse_union. apply sim_view_join.
        { eapply sim_view_le; [|exact SIM_LOCAL.(VREL)]. eauto. }
        { destruct (OrdW.ge ord OrdW.release) eqn:ORD; [|by econs].
          eapply sim_view_le; [by right; eauto|]. econs 2; eauto.
          - econs; eauto. econs; eauto.
          - refl.
        }
      * rewrite List.app_length, Nat.add_1_r. i.
        generalize (SIM_LOCAL.(FWDBANK) loc). rewrite fun_add_spec. condtac; s; cycle 1.
        { generalize (SIM_LOCAL.(FWDBANK) loc). destruct (Local.fwdbank local1 loc) eqn:FWD.
          - i. des. rewrite sim_local_fwd_step. esplits; eauto.
            econs. instantiate (1 := (_, _)). splits; [|econs; ss].
            left. econs. splits; eauto. econs; eauto. econs; eauto. s.
            destruct (equiv_dec (ValA.val (sem_expr armap1 eloc)) loc); ss. congr.
          - i. rewrite sim_local_fwd_none_step, inverse_step. ii. inv H1. inv REL.
            + eapply H0; eauto.
            + inv H1. inv H3. apply Label.is_writing_inv in LABEL0. des. subst. congr.
        }
        { inversion e. subst. i. esplits; eauto.
          - econs; eauto.
            + econs; eauto. rewrite VAL. apply Label.write_is_writing.
            + i. destruct eid. inv PO. inv PO0. ss. subst. lia.
          - rewrite inverse_union. apply sim_view_join.
            + eapply sim_view_le; [|by apply VIEW0].
              i. destruct x0. ss. des. subst.
              left. econs; eauto. apply ADDR. econs; eauto. right. ss.
            + eapply sim_view_le; [|by apply VIEW1].
              i. destruct x0. ss. des. subst.
              right. econs; eauto. apply DATA. econs; eauto. right. ss.
          - econs; i.
            + econs; eauto.
            + inv H0. rewrite LABEL_LEN in EID. inv EID. ss.
        }
      * destruct ex1; ss. apply SIM_LOCAL.(EXBANK).
      * i. revert VIEW2. rewrite Promises.unset_o. condtac; ss. i.
        exploit SIM_LOCAL.(PROMISES); eauto. i. des.
        esplits; cycle 1; eauto.
        rewrite List.app_length, Nat.add_1_r. inv N; [|lia]. congr.
  - (* write_failure *)
    eexists (ExecUnit.mk _ _ _). esplits.
    + econs. econs; ss.
      { econs; ss. }
      econs 4; ss.
    + econs; ss.
      * econs; ss. apply sim_rmap_add; ss. econs; ss. econs 1. ss.
      * inv SIM_LOCAL; econs; eauto. econs.
  - (* barrier *)
    exploit LABEL.
    { rewrite List.nth_error_app2; ss. rewrite Nat.sub_diag. ss. }
    intro LABEL_LEN. destruct b0; eexists (ExecUnit.mk _ _ _).
    + (* isb *)
      esplits.
      { econs. econs; ss.
        - econs; ss.
        - econs 5; ss.
      }
      econs; ss.
      econs; ss.
      * rewrite List.app_length, Nat.add_1_r. s.
        i. rewrite sim_local_coh_step. rewrite inverse_step.
        rewrite inverse_union. eapply sim_view_le; [by left; eauto|].
        apply SIM_LOCAL.
      * rewrite List.app_length, Nat.add_1_r. s.
        rewrite sim_local_vrp_step. rewrite inverse_step.
        rewrite ? inverse_union. apply sim_view_join.
        { eapply sim_view_le; [|exact SIM_LOCAL.(VRP)]. eauto. }
        { eapply sim_view_le; [|exact SIM_LOCAL.(VCAP)].
          right. left. right.
          inv PR. econs; eauto. econs; splits; eauto.
          econs; eauto.
        }
      * rewrite List.app_length, Nat.add_1_r. s.
        rewrite sim_local_vwp_step. rewrite inverse_step.
        rewrite ? inverse_union. eapply sim_view_le; [|exact SIM_LOCAL.(VWP)]. eauto.
      * rewrite List.app_length, Nat.add_1_r. s.
        rewrite sim_local_vrm_step. rewrite inverse_step.
        rewrite ? inverse_union. eapply sim_view_le; [|exact SIM_LOCAL.(VRM)]. eauto.
      * rewrite List.app_length, Nat.add_1_r. s.
        rewrite sim_local_vwm_step. rewrite inverse_step.
        rewrite ? inverse_union. eapply sim_view_le; [|exact SIM_LOCAL.(VWM)]. eauto.
      * rewrite List.app_length, Nat.add_1_r. s.
        eapply sim_view_le.
        { apply inverse_mon. eapply sim_local_vcap_po_adj. eauto. }
        rewrite inverse_step. apply SIM_LOCAL.
      * rewrite List.app_length, Nat.add_1_r. s.
        rewrite sim_local_vrel_step. rewrite inverse_step.
        rewrite ? inverse_union. eapply sim_view_le; [|exact SIM_LOCAL.(VREL)]. eauto.
      * rewrite List.app_length, Nat.add_1_r. i.
        generalize (SIM_LOCAL.(FWDBANK) loc). destruct (Local.fwdbank local1 loc) eqn:FWD.
        { i. des. rewrite sim_local_fwd_step. esplits; eauto.
          econs. instantiate (1 := (_, _)). splits; [|econs; ss].
          left. econs. splits; eauto. econs; eauto.
        }
        { ii. inv H0. inv REL. inv H0. rewrite Execution.po_po_adj in H2. inv H2. des.
          destruct x, x0. inv H2. ss. inv N. inv H0.
          - inv H2. inv H1. inv H2. rewrite LABEL_LEN in EID. inv EID. ss.
          - inv H2. ss. subst. eapply H. econs; eauto. econs; eauto.
        }
      * apply SIM_LOCAL.
      * i. exploit SIM_LOCAL.(PROMISES); eauto. i. des.
        esplits; cycle 1; eauto.
        rewrite List.app_length, Nat.add_1_r. inv N; [|lia].
        inv WRITE. destruct l; ss. congr.
    + (* dmbst *)
      esplits.
      { econs. econs; ss.
        - econs; ss.
        - econs 6; ss.
      }
      econs; ss.
      econs; ss.
      * rewrite List.app_length, Nat.add_1_r. s.
        i. rewrite sim_local_coh_step. rewrite inverse_step.
        rewrite inverse_union. eapply sim_view_le; [by left; eauto|].
        apply SIM_LOCAL.
      * rewrite List.app_length, Nat.add_1_r. s.
        rewrite sim_local_vrp_step. rewrite inverse_step.
        rewrite ? inverse_union. eapply sim_view_le; [|exact SIM_LOCAL.(VRP)]. eauto.
      * rewrite List.app_length, Nat.add_1_r. s.
        rewrite sim_local_vwp_step. rewrite inverse_step.
        rewrite ? inverse_union. apply sim_view_join.
        { eapply sim_view_le; [|exact SIM_LOCAL.(VWP)]. eauto. }
        { eapply sim_view_le; [|exact SIM_LOCAL.(VWM)].
          right. left. right. rewrite seq_assoc.
          inv PR. econs; eauto. econs; splits; eauto.
          econs; eauto.
        }
      * rewrite List.app_length, Nat.add_1_r. s.
        rewrite sim_local_vrm_step. rewrite inverse_step.
        rewrite ? inverse_union. eapply sim_view_le; [|exact SIM_LOCAL.(VRM)]. eauto.
      * rewrite List.app_length, Nat.add_1_r. s.
        rewrite sim_local_vwm_step. rewrite inverse_step.
        rewrite ? inverse_union. eapply sim_view_le; [|exact SIM_LOCAL.(VWM)]. eauto.
      * rewrite List.app_length, Nat.add_1_r. s.
        eapply sim_view_le.
        { apply inverse_mon. eapply sim_local_vcap_po_adj. eauto. }
        rewrite inverse_step. apply SIM_LOCAL.
      * rewrite List.app_length, Nat.add_1_r. s.
        rewrite sim_local_vrel_step. rewrite inverse_step.
        rewrite ? inverse_union. eapply sim_view_le; [|exact SIM_LOCAL.(VREL)]. eauto.
      * rewrite List.app_length, Nat.add_1_r. i.
        generalize (SIM_LOCAL.(FWDBANK) loc). destruct (Local.fwdbank local1 loc) eqn:FWD.
        { i. des. rewrite sim_local_fwd_step. esplits; eauto.
          econs. instantiate (1 := (_, _)). splits; [|econs; ss].
          left. econs. splits; eauto. econs; eauto.
        }
        { ii. inv H0. inv REL. inv H0. rewrite Execution.po_po_adj in H2. inv H2. des.
          destruct x, x0. inv H2. ss. inv N. inv H0.
          - inv H2. inv H1. inv H2. rewrite LABEL_LEN in EID. inv EID. ss.
          - inv H2. ss. subst. eapply H. econs; eauto. econs; eauto.
        }
      * apply SIM_LOCAL.
      * i. exploit SIM_LOCAL.(PROMISES); eauto. i. des.
        esplits; cycle 1; eauto.
        rewrite List.app_length, Nat.add_1_r. inv N; [|lia].
        inv WRITE. destruct l; ss. congr.
    + (* dmbld *)
      esplits.
      { econs. econs; ss.
        - econs; ss.
        - econs 7; ss.
      }
      econs; ss.
      econs; ss.
      * rewrite List.app_length, Nat.add_1_r. s.
        i. rewrite sim_local_coh_step. rewrite inverse_step.
        rewrite inverse_union. eapply sim_view_le; [by left; eauto|].
        apply SIM_LOCAL.
      * rewrite List.app_length, Nat.add_1_r. s.
        rewrite sim_local_vrp_step. rewrite inverse_step.
        rewrite ? inverse_union. apply sim_view_join.
        { eapply sim_view_le; [|exact SIM_LOCAL.(VRP)]. eauto. }
        { eapply sim_view_le; [|exact SIM_LOCAL.(VRM)].
          right. left. left. right. rewrite seq_assoc.
          inv PR. econs; eauto. econs; splits; eauto.
          econs; eauto.
        }
      * rewrite List.app_length, Nat.add_1_r. s.
        rewrite sim_local_vwp_step. rewrite inverse_step.
        rewrite ? inverse_union. apply sim_view_join.
        { eapply sim_view_le; [|exact SIM_LOCAL.(VWP)]. eauto. }
        { eapply sim_view_le; [|exact SIM_LOCAL.(VRM)].
          right. left. left. right. rewrite seq_assoc.
          inv PR. econs; eauto. econs; splits; eauto.
          econs; eauto.
        }
      * rewrite List.app_length, Nat.add_1_r. s.
        rewrite sim_local_vrm_step. rewrite inverse_step.
        rewrite ? inverse_union. eapply sim_view_le; [|exact SIM_LOCAL.(VRM)]. eauto.
      * rewrite List.app_length, Nat.add_1_r. s.
        rewrite sim_local_vwm_step. rewrite inverse_step.
        rewrite ? inverse_union. eapply sim_view_le; [|exact SIM_LOCAL.(VWM)]. eauto.
      * rewrite List.app_length, Nat.add_1_r. s.
        eapply sim_view_le.
        { apply inverse_mon. eapply sim_local_vcap_po_adj. eauto. }
        rewrite inverse_step. apply SIM_LOCAL.
      * rewrite List.app_length, Nat.add_1_r. s.
        rewrite sim_local_vrel_step. rewrite inverse_step.
        rewrite ? inverse_union. eapply sim_view_le; [|exact SIM_LOCAL.(VREL)]. eauto.
      * rewrite List.app_length, Nat.add_1_r. i.
        generalize (SIM_LOCAL.(FWDBANK) loc). destruct (Local.fwdbank local1 loc) eqn:FWD.
        { i. des. rewrite sim_local_fwd_step. esplits; eauto.
          econs. instantiate (1 := (_, _)). splits; [|econs; ss].
          left. econs. splits; eauto. econs; eauto.
        }
        { ii. inv H0. inv REL. inv H0. rewrite Execution.po_po_adj in H2. inv H2. des.
          destruct x, x0. inv H2. ss. inv N. inv H0.
          - inv H2. inv H1. inv H2. rewrite LABEL_LEN in EID. inv EID. ss.
          - inv H2. ss. subst. eapply H. econs; eauto. econs; eauto.
        }
      * apply SIM_LOCAL.
      * i. exploit SIM_LOCAL.(PROMISES); eauto. i. des.
        esplits; cycle 1; eauto.
        rewrite List.app_length, Nat.add_1_r. inv N; [|lia].
        inv WRITE. destruct l; ss. congr.
    + (* dmbsy *)
      esplits.
      { econs. econs; ss.
        - econs; ss.
        - econs 8; ss.
      }
      econs; ss.
      econs; ss.
      * rewrite List.app_length, Nat.add_1_r. s.
        i. rewrite sim_local_coh_step. rewrite inverse_step.
        rewrite inverse_union. eapply sim_view_le; [by left; eauto|].
        apply SIM_LOCAL.
      * rewrite List.app_length, Nat.add_1_r. s.
        rewrite sim_local_vrp_step. rewrite inverse_step.
        rewrite ? inverse_union. repeat apply sim_view_join.
        { eapply sim_view_le; [|exact SIM_LOCAL.(VRP)]. eauto. }
        { eapply sim_view_le; [|exact SIM_LOCAL.(VRM)].
          right. left. left. left.
          inv PR. inv REL. des. inv H. econs; eauto. econs; splits; eauto.
          econs; eauto.
        }
        { eapply sim_view_le; [|exact SIM_LOCAL.(VWM)].
          right. left. left. left.
          inv PR. inv REL. des. inv H. econs; eauto. econs; splits; eauto.
          econs; eauto.
        }
        { econs. ss. }
      * rewrite List.app_length, Nat.add_1_r. s.
        rewrite sim_local_vwp_step. rewrite inverse_step.
        rewrite ? inverse_union. repeat apply sim_view_join.
        { eapply sim_view_le; [|exact SIM_LOCAL.(VWP)]. eauto. }
        { eapply sim_view_le; [|exact SIM_LOCAL.(VRM)].
          right. left. left. left.
          inv PR. inv REL. des. inv H. econs; eauto. econs; splits; eauto.
          econs; eauto.
        }
        { eapply sim_view_le; [|exact SIM_LOCAL.(VWM)].
          right. left. left. left.
          inv PR. inv REL. des. inv H. econs; eauto. econs; splits; eauto.
          econs; eauto.
        }
        { econs. ss. }
      * rewrite List.app_length, Nat.add_1_r. s.
        rewrite sim_local_vrm_step. rewrite inverse_step.
        rewrite ? inverse_union. eapply sim_view_le; [|exact SIM_LOCAL.(VRM)]. eauto.
      * rewrite List.app_length, Nat.add_1_r. s.
        rewrite sim_local_vwm_step. rewrite inverse_step.
        rewrite ? inverse_union. eapply sim_view_le; [|exact SIM_LOCAL.(VWM)]. eauto.
      * rewrite List.app_length, Nat.add_1_r. s.
        eapply sim_view_le.
        { apply inverse_mon. eapply sim_local_vcap_po_adj. eauto. }
        rewrite inverse_step. apply SIM_LOCAL.
      * rewrite List.app_length, Nat.add_1_r. s.
        rewrite sim_local_vrel_step. rewrite inverse_step.
        rewrite ? inverse_union. eapply sim_view_le; [|exact SIM_LOCAL.(VREL)]. eauto.
      * rewrite List.app_length, Nat.add_1_r. i.
        generalize (SIM_LOCAL.(FWDBANK) loc). destruct (Local.fwdbank local1 loc) eqn:FWD.
        { i. des. rewrite sim_local_fwd_step. esplits; eauto.
          econs. instantiate (1 := (_, _)). splits; [|econs; ss].
          left. econs. splits; eauto. econs; eauto.
        }
        { ii. inv H0. inv REL. inv H0. rewrite Execution.po_po_adj in H2. inv H2. des.
          destruct x, x0. inv H2. ss. inv N. inv H0.
          - inv H2. inv H1. inv H2. rewrite LABEL_LEN in EID. inv EID. ss.
          - inv H2. ss. subst. eapply H. econs; eauto. econs; eauto.
        }
      * apply SIM_LOCAL.
      * i. exploit SIM_LOCAL.(PROMISES); eauto. i. des.
        esplits; cycle 1; eauto.
        rewrite List.app_length, Nat.add_1_r. inv N; [|lia].
        i. inv WRITE. destruct l; ss. congr.
  - (* if *)
    eexists (ExecUnit.mk _ _ _). esplits.
    + econs. econs; ss.
      { econs; ss. }
      econs; ss.
    + econs; ss.
      * econs; eauto. s.
        generalize (sim_rmap_expr cond RMAP). intro X. inv X.
        rewrite VAL. ss.
      * inv SIM_LOCAL; econs; eauto. s.
        apply sim_view_join; ss.
        generalize (sim_rmap_expr cond RMAP). intro X. inv X.
        eapply sim_view_le; [|exact VIEW]. intros [tid' n']. s. i. des. subst.
        econs; eauto. left. apply CTRL. econs; eauto. s. right. econs; ss.
  - (* dowhile *)
    eexists (ExecUnit.mk _ _ _). esplits.
    + econs. econs; ss.
      { econs; ss. }
      * econs; ss.
    + econs; ss.
      inv SIM_LOCAL; econs; eauto. s.
      apply sim_view_join; ss. econs. ss.
Qed.

Lemma sim_eu_rtc_step
      p ex ob tid aeu1 eu1 aeu2
      (EX: Valid.ex p ex)
      (OB: Permutation ob (Execution.eids ex))
      (LINEARIZED: linearized ex.(Execution.ob) ob)
      (SIM: sim_eu tid ex ob aeu1 eu1)
      (WF: AExecUnit.wf aeu1)
      (STEP: rtc AExecUnit.step aeu1 aeu2)
      (LOCAL: IdMap.find tid EX.(Valid.aeus) = Some aeu2):
  exists eu2,
    <<SIM: sim_eu tid ex ob aeu2 eu2>> /\
    <<STEP: rtc (ExecUnit.state_step tid) eu1 eu2>>.
Proof.
  revert eu1 SIM. induction STEP.
  { esplits; eauto. }
  i.
  exploit AExecUnit.step_future; eauto. i. des.
  exploit AExecUnit.rtc_step_future; eauto. i. des.
  exploit sim_eu_step; eauto.
  { i. unfold Execution.label. s.
    rewrite EX.(Valid.LABELS), IdMap.map_spec, LOCAL. s.
    inv LE0. des. rewrite LABELS, List.nth_error_app1; ss.
    apply List.nth_error_Some. congr.
  }
  { rewrite EX.(Valid.ADDR). ii. econs.
    - rewrite IdMap.map_spec, LOCAL. ss.
    - eapply tid_lift_incl; eauto. inv LE0; ss.
  }
  { rewrite EX.(Valid.DATA). ii. econs.
    - rewrite IdMap.map_spec, LOCAL. ss.
    - eapply tid_lift_incl; eauto. inv LE0; ss.
  }
  { rewrite EX.(Valid.CTRL). ii. econs.
    - rewrite IdMap.map_spec, LOCAL. ss.
    - eapply tid_lift_incl; eauto. inv LE0; ss.
  }
  { rewrite EX.(Valid.RMW). ii. econs.
    - rewrite IdMap.map_spec, LOCAL. ss.
    - eapply tid_lift_incl; eauto. inv LE0; ss.
  }
  i. des.
  exploit IHSTEP; eauto. i. des.
  esplits; eauto.
Qed.

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

Theorem axiomatic_to_promising_pf
      p ex
      (EX: Valid.ex p ex):
  exists m,
    <<STEP: Machine.exec p m>> /\
    <<TERMINAL: EX.(Valid.is_terminal) -> Machine.is_terminal m>> /\
    <<MEM: sim_mem ex m.(Machine.mem)>>.
Proof.
  (* Linearize events and construct memory. *)
  exploit (linearize (Execution.eids ex)).
  { eapply EX.(Valid.EXTERNAL). }
  i. des. rename l' into ob.
  remember (mem_of_ex ex ob) as mem eqn:MEM.

  (* Construct promise steps. *)
  exploit (pf_init_with_promises p mem); eauto.
  { i. subst. unfold mem_of_ex in MSG. rewrite in_filter_map_iff in MSG. des.
    exploit Permutation_in; eauto. intro X.
    generalize (Execution.eids_spec ex). i. des.
    apply LABEL in X. destruct (Execution.label a ex) eqn:Y; ss.
    destruct t; ss. inv MSG0. s. unfold Execution.label in Y.
    rewrite EX.(Valid.LABELS), IdMap.map_spec in Y.
    destruct (IdMap.find (fst a) (Valid.PRE EX).(Valid.aeus)) eqn:Z; ss.
    generalize (EX.(Valid.AEUS) (fst a)). intro W. inv W; ss. congr.
  }
  unfold IdMap.Equal, init_with_promises. s. i. des. subst.
  setoid_rewrite IdMap.mapi_spec in TPOOL.

  (* It's sufficient to construct steps from the promised state. *)
  cut (exists m0,
          <<STEP: rtc (Machine.step ExecUnit.state_step) m m0>> /\
          <<NOPROMISE: Machine.no_promise m0>> /\
          <<TERMINAL: EX.(Valid.is_terminal) -> Machine.is_terminal m0>> /\
          <<MEM: sim_mem ex (Machine.mem m0)>>).
  { i. des. esplits; eauto. econs; eauto.
    etrans.
    - eapply rtc_mon; [|by eauto]. apply Machine.step_mon. right. ss.
    - eapply rtc_mon; [|by eauto]. apply Machine.step_mon. left. ss.
  }
  clear STEP.

  (* Execute threads one-by-one (induction). *)
  assert (IN: forall tid stmts
                (FIND1: IdMap.find tid p = Some stmts),
             IdMap.find tid m.(Machine.tpool) =
             Some (State.init stmts,
                   Local.init_with_promises (promises_from_mem tid (Machine.mem m)))).
  { i. rewrite TPOOL, FIND1, MEM0. ss. }
  assert (OUT: forall tid st lc
                 (FIND1: IdMap.find tid p = None)
                 (FIND2: IdMap.find tid m.(Machine.tpool) = Some (st, lc)),
             (EX.(Valid.is_terminal) -> State.is_terminal st) /\ lc.(Local.promises) = bot).
  { i. rewrite TPOOL, FIND1 in FIND2. ss. }
  assert (P: forall tid stmts
               (FIND1: IdMap.find tid p = Some stmts),
             IdMap.find tid p = Some stmts) by ss.

  clear TPOOL.
  setoid_rewrite IdMap.elements_spec in IN at 1.
  setoid_rewrite IdMap.elements_spec in OUT at 1.
  setoid_rewrite IdMap.elements_spec in P at 1.
  generalize (IdMap.elements_3w p). intro NODUP. revert NODUP.
  revert IN OUT P. generalize (IdMap.elements p). intro ps.
  revert m MEM0. induction ps; ss.
  { i. esplits; eauto.
    - econs. i. eapply OUT; eauto.
    - econs. i. exploit OUT; eauto. i. des. eauto.
  }
  i.

  destruct a as [tid stmts].
  exploit (IN tid); eauto.
  { destruct (equiv_dec tid tid); [|congr]. ss. }
  intro FIND.
  cut (exists st2 lc2,
          <<STEP: rtc (ExecUnit.state_step (A:=unit) tid)
                      (ExecUnit.mk
                         (State.init stmts)
                         (Local.init_with_promises (promises_from_mem tid (Machine.mem m)))
                         (Machine.mem m))
                      (ExecUnit.mk st2 lc2 (Machine.mem m))>> /\
          <<TERMINAL: EX.(Valid.is_terminal) -> State.is_terminal st2>> /\
          <<NOPROMISE: lc2.(Local.promises) = bot>>).
  { i. des. subst.
    exploit Machine.rtc_eu_step_step; try exact STEP; eauto. i.
    assert (NOTIN: SetoidList.findA (fun id' : IdMap.key => if equiv_dec tid id' then true else false) ps = None).
    { inv NODUP. revert H1. clear. induction ps; ss.
      destruct a. i. destruct (equiv_dec tid k); eauto.
      inv e. contradict H1. left. ss.
    }
    exploit (IHps (Machine.mk
                     (IdMap.add tid (st2, lc2) (Machine.tpool m))
                     (Machine.mem m))); ss.
    { i. rewrite IdMap.add_spec. condtac; ss.
      - inversion e. subst. congr.
      - apply IN. destruct (equiv_dec tid0 tid); ss.
    }
    { i. revert FIND2. rewrite IdMap.add_spec. condtac.
      - i. inv FIND2. inversion e. eauto.
      - apply OUT. destruct (equiv_dec tid0 tid); ss.
    }
    { i. generalize (P tid0 stmts0). destruct (equiv_dec tid0 tid); eauto.
      inv e. congr.
    }
    { inv NODUP. ss. }
    i. des. esplits; cycle 1; eauto. etrans; eauto.
  }
  generalize (P tid stmts). destruct (equiv_dec tid tid); [|congr].
  intro FINDP. specialize (FINDP eq_refl).
  rewrite MEM0 in *.
  clear NODUP IN OUT P IHps MEM0 FIND ps e m.

  (* Execute a thread `tid`. *)
  generalize (EX.(Valid.AEUS) tid). rewrite FINDP.
  intro X. inv X. des. rename b into aeu, H into AEU. clear FINDP.
  exploit (@sim_eu_rtc_step p ex ob tid); eauto.
  { instantiate (1 := ExecUnit.mk
                        (State.init stmts)
                        (Local.init_with_promises (promises_from_mem tid (mem_of_ex ex ob)))
                        (mem_of_ex ex ob)).
    econs; ss.
    - econs; ss. econs. ii. rewrite ? IdMap.gempty. ss.
    - econs; eauto; ss.
      + ii. inv H. inv REL1. inv H. inv H1. ss. lia.
      + econs.
      + i. destruct view; ss. exploit promises_from_mem_inv; eauto. i. des.
        exploit in_mem_of_ex; swap 1 2; eauto.
        { eapply Permutation_NoDup; [by symmetry; eauto|].
          eapply Execution.eids_spec; eauto.
        }
        s. i. des. esplits; cycle 1; eauto. lia.
  }
  { apply AExecUnit.wf_init. }
  i. des. destruct eu2 as [state2 local2 mem2]. inv SIM. ss. subst.
  esplits; eauto.
  - intro X. exploit X; eauto. i. inv STATE. congr.
  - apply Promises.ext. i. destruct (Promises.lookup i (Local.promises local2)) eqn:L; ss; cycle 1.
    { rewrite Promises.lookup_bot. ss. }
    exploit LOCAL.(PROMISES); eauto. i. des.
    exploit view_of_eid_inv; eauto. i. des. subst.
    inv WRITE. unfold Execution.label in EID. ss.
    rewrite EX.(Valid.LABELS), IdMap.map_spec, <- AEU in EID. ss.
    apply List.nth_error_None in N. congr.
Qed.
