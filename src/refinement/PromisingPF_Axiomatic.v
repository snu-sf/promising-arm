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
      exploit EX.(Valid.RF2); eauto. i. des.
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
            (fun aexbank lts =>
               ex.(Execution.label_is) (Label.is_reading lts.(fst)) (tid, aexbank) /\
               (forall eid v, ex.(Execution.rf) eid (tid, aexbank) -> view_of_eid ex ob eid = Some v -> le v lts.(snd)) /\
               sim_view
                 ex ob
                 (inverse ex.(Execution.rf) (eq (tid, aexbank)))
                 lts.(snd))
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

Inductive sim_trace (p: program) (mem: Memory.t) (tid: Id.t):
  forall (tr: list (ExecUnit.t (A:=unit))) (atr: list AExecUnit.t)
     (w: list (nat -> option Time.t)) (r: list (nat -> option Time.t))
     (cov: nat -> Time.t) (vext: nat -> Time.t), Prop :=
| sim_trace_init
    st lc stmts
    (FIND: IdMap.find tid (init_with_promises p mem).(Machine.tpool) = Some (st, lc))
    (STMT: IdMap.find tid p = Some stmts):
    sim_trace p mem tid [ExecUnit.mk st lc mem] [AExecUnit.mk (State.init stmts) ALocal.init]
              [fun _ => None] [fun _ => None] (fun _ => Time.bot) (fun _ => Time.bot)
| sim_trace_step
    e tr eu1 eu2 atr aeu1 aeu2 r r1 r2 w w1 w2 cov cov' vext vext'
    (STEP: ExecUnit.state_step0 tid e e eu1 eu2)
    (ASTEP: AExecUnit.step aeu1 aeu2)
    (STATE: sim_state_weak eu2.(ExecUnit.state) aeu2.(AExecUnit.state))
    (R: r2 = match e with
               | Event.read _ _ vloc _ =>
                 (fun eid => if Nat.eqb eid (ALocal.next_eid aeu1.(AExecUnit.local))
                            then Some (eu2.(ExecUnit.local).(Local.coh) vloc.(ValA.val))
                            else r1 eid)
               | _ => r1
               end)
    (W: w2 = match e with
             | Event.write _ _ vloc _ _ =>
               (fun eid => if Nat.eqb eid (ALocal.next_eid aeu1.(AExecUnit.local))
                         then Some (eu2.(ExecUnit.local).(Local.coh) vloc.(ValA.val))
                         else w1 eid)
             | _ => w1
             end)
    (COV: cov' = match e with
                 | Event.read _ _ vloc _
                 | Event.write _ _ vloc _ _ =>
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
                   | Event.write _ _ vloc _ _ =>
                     (fun eid => if Nat.eqb eid (ALocal.next_eid aeu1.(AExecUnit.local))
                                then eu2.(ExecUnit.local).(Local.coh) vloc.(ValA.val)
                                else vext eid)
                   | _ => vext
                   end)
    (TRACE: sim_trace p mem tid (eu1::tr) (aeu1::atr) (r1::r) (w1::w) cov vext):
    sim_trace p mem tid (eu2::eu1::tr) (aeu2::aeu1::atr) (r2::r1::r) (w2::w1::w) cov' vext'.

Definition sim_traces
           (p: program) (mem: Memory.t)
           (trs: IdMap.t (list (ExecUnit.t (A:=unit))))
           (atrs: IdMap.t (list AExecUnit.t))
           (rs: IdMap.t (list (nat -> option Time.t)))
           (ws: IdMap.t (list (Time.t -> option nat)))
           (covs: IdMap.t (nat -> Time.t))
           (vexts: IdMap.t (nat -> Time.t))
  : Prop :=
  IdMap.Forall6 (sim_trace p mem) trs atrs rs ws covs vexts.

Lemma promising_pf_traces
      p m
      (STEP: Machine.pf_exec p m):
  exists mem trs atrs rs ws covs vexts ex (PRE: Valid.pre_ex p ex),
    <<SIM: sim_traces p mem trs atrs rs ws covs vexts>> /\
    <<EUS: IdMap.Forall2
             (fun tid tr sl => exists l, tr = (ExecUnit.mk sl.(fst) sl.(snd) mem) :: l)
             trs m.(Machine.tpool)>> /\
    <<AEUS: IdMap.Forall2
              (fun tid atr aeu => exists l, atr = aeu :: l)
              atrs PRE.(Valid.aeus)>>.
Proof.
Admitted.

Inductive co_gen (m: Memory.t) (ws: IdMap.t (list (nat -> option Time.t))) (eid1 eid2: eidT): Prop :=
| co_gen_intro
    w1 wl1 ts1 loc1 val1 tid1 w2 wl2 ts2 loc2 val2 tid2
    (WS1: IdMap.find eid1.(fst) ws = Some (w1::wl1))
    (W1: w1 eid1.(snd) = Some ts1)
    (WS2: IdMap.find eid2.(fst) ws = Some (w2::wl2))
    (W2: w2 eid2.(snd) = Some ts2)
    (GET1: Memory.get_msg ts1 m = Some (Msg.mk loc1 val1 tid1))
    (GET1: Memory.get_msg ts2 m = Some (Msg.mk loc2 val2 tid2))
    (LOC: loc1 = loc2)
    (TS: Time.lt ts1 ts2)
.

Inductive rf_gen (ws: IdMap.t (list (nat -> option Time.t))) (rs: IdMap.t (list (nat -> option Time.t))) (eid1 eid2: eidT): Prop :=
| rf_gen_intro
    w wl ts1 r rl ts2
    (WS: IdMap.find eid1.(fst) ws = Some (w::wl))
    (W: w eid1.(snd) = Some ts1)
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

(* Lemma trace_w *)
(*       p mem tid tr atr rf w cov vext *)
(*       (SIM: sim_trace p mem tid tr atr rf w cov vext): *)
(*   exists l st lc, *)
(*     tr = l ++ [ExecUnit.mk st lc mem] /\ *)
(*     (forall ts loc val (GET: Memory.get_msg ts mem = Some (Msg.mk loc val tid)), *)
(*         (Promises.lookup ts lc.(Local.promises) = true \/ *)
(*          ts = Time.bot \/ *)
(*          exists eid, w ts = Some eid)). *)
(* Proof. *)

Lemma sim_trace_co
      p m
      mem trs atrs rs ws covs vexts ex
      (PROMISE: Machine.no_promise m)
      (PRE: Valid.pre_ex p ex)
      (SIM: sim_traces p mem trs atrs rs ws covs vexts)
      (EUS: IdMap.Forall2
              (fun tid tr sl => exists l, tr = (ExecUnit.mk sl.(fst) sl.(snd) mem) :: l)
              trs m.(Machine.tpool))
      (AEUS: IdMap.Forall2
               (fun tid atr aeu => exists l, atr = aeu :: l)
               atrs PRE.(Valid.aeus)):
  forall eid1 eid2,
    (exists loc
        ex1 ord1 val1
        ex2 ord2 val2,
        <<LABEL: Execution.label eid1 ex = Some (Label.write ex1 ord1 loc val1)>> /\
        <<LABEL: Execution.label eid2 ex = Some (Label.write ex2 ord2 loc val2)>>) <->
    (eid1 = eid2 \/ (co_gen mem ws) eid1 eid2 \/ (co_gen mem ws) eid2 eid1).
Proof.
Admitted.

Lemma promising_pf_traces
      p m
      (STEP: Machine.pf_exec p m):
  exists mem trs atrs rs ws covs vexts ex (PRE: Valid.pre_ex p ex),
    sim_traces p mem trs atrs rs ws covs vexts /\
    IdMap.Forall2
      (fun tid tr sl => exists l, tr = l ++ [ExecUnit.mk sl.(fst) sl.(snd) mem])
      trs m.(Machine.tpool) /\
    IdMap.Forall2
      (fun tid atr aeu => exists l, atr = l ++ [aeu])
      atrs pre.(Valid.aeus).
Proof.
Admitted.

Lemma promising_pf_valid
      p m
      (STEP: Machine.pf_exec p m):
  exists ex (PRE: Valid.pre_ex p ex) (cov: forall (eid: eidT), Time.t) (vext: forall (eid: eidT), Time.t),
    <<CO: Valid.co ex>> /\
    <<RF1: Valid.rf1 ex>> /\
    <<RF2': Valid.rf2' ex>> /\
    <<RF_WF: Valid.rf_wf ex>> /\
    <<INTERNAL:
      forall eid1 eid2 (INTERNAL: ex.(Execution.internal) eid1 eid2),
        Time.lt (cov eid1) (cov eid2) \/
        Time.le (cov eid1) (cov eid2) /\ Execution.po eid1 eid2>> /\
    <<EXTERNAL:
      forall eid1 eid2
         (LABEL1: Execution.label_is ex (join Label.is_read Label.is_write) eid1)
         (LABEL2: Execution.label_is ex (join Label.is_read Label.is_write) eid2),
        Time.lt (vext eid1) (vext eid2) \/
        Time.le (vext eid1) (vext eid2) /\ Execution.po eid1 eid2>> /\
    <<ATOMIC: le (ex.(Execution.rmw) ∩ (ex.(Execution.fre) ⨾ ex.(Execution.coe))) bot>> /\
    <<STATE: IdMap.Forall2
               (fun tid sl aeu => sim_state_weak sl.(fst) aeu.(AExecUnit.state))
               m.(Machine.tpool) pre.(Valid.aeus)>>.
Proof.
Admitted.

Theorem promising_pf_to_axiomatic
        p m
        (STEP: Machine.pf_exec p m):
  exists ex (EX: Valid.ex p ex),
    <<TERMINAL: Machine.is_terminal m -> EX.(Valid.is_terminal)>> /\
    <<MEM: sim_mem ex m.(Machine.mem)>>.
Proof.
  exploit promising_pf_valid; eauto. i. des.
  exists ex. eexists (Valid.mk_ex pre CO RF1 (Valid.rf2'_rf2 RF2') RF2' RF_WF _ _ ATOMIC).
  s. esplits.
  - ii. inv H. specialize (STATE tid). inv STATE; try congr.
    rewrite FIND in H. inv H. destruct a. destruct aeu. ss.
    exploit TERMINAL; eauto. i. des. inv REL. inv x. congr.
  - admit.
Grab Existential Variables.
{
  admit.
}
{ (* external *)
  ii. exploit Valid.ob_cycle; eauto. i. des.
  - clear - EXTERNAL NONBARRIER.
    cut (forall eid1 eid2
           (R: (Execution.ob ex ∩ (Execution.label_is_rel ex (fun label : Label.t => join Label.is_read Label.is_write label)))⁺ eid1 eid2),
            Time.lt (vext eid1) (vext eid2) \/
            Time.le (vext eid1) (vext eid2) /\ Execution.po eid1 eid2).
    { ii. exploit H; eauto. i. des; [inv x|inv x0]; lia. }
    i. induction R.
    + inv H. inv H1. eapply EXTERNAL; eauto.
    + des.
      * left. etrans; eauto.
      * left. eapply le_lt_trans; eauto.
      * left. eapply lt_le_trans; eauto.
      * right. split; etrans; eauto.
  - exploit Valid.barrier_ob_po; eauto. i. inv x1. lia.
}
{ (* internal *)
  clear - INTERNAL.
  cut (forall eid1 eid2 (R: ex.(Execution.internal)⁺ eid1 eid2),
          Time.lt (cov eid1) (cov eid2) \/
          Time.le (cov eid1) (cov eid2) /\ Execution.po eid1 eid2).
  { ii. exploit H; eauto. i. des; [inv x0|inv x1]; lia. }
  i. induction R; eauto. des.
  - left. etrans; eauto.
  - left. eapply le_lt_trans; eauto.
  - left. eapply lt_le_trans; eauto.
  - right. split; etrans; eauto.
}
Admitted.
