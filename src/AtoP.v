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
Require Import Classical.

Require Import Basic.
Require Import HahnRelationsMore.
Require Import Order.
Require Import Time.
Require Import Lang.
Require Import Memory.
Require Import Promising.
Require Import Axiomatic.

Set Implicit Arguments.


Lemma strong_nat_ind
      (P: nat -> Prop)
      (STEP: forall n, (forall m, m < n -> P m) -> P n):
  forall n, P n.
Proof.
  cut (forall n, forall m, m < n -> P m).
  { i. eapply H. eauto. }
  induction n; i; [lia|]. apply STEP. i. apply IHn. lia.
Qed.

Lemma partition A
      (l: list A)
      (pred: A -> Prop):
  exists l1 l2,
    Permutation (l1 ++ l2) l /\
    List.Forall pred l1 /\
    List.Forall (fun a => ~ (pred a)) l2.
Proof.
  induction l.
  { esplits; eauto. s. eauto. }
  des. destruct (classic (pred a)).
  - exists (a::l1), l2. esplits; eauto. s. econs. ss.
  - exists l1, (a::l2). esplits; eauto. rewrite <- Permutation_middle. econs. ss.
Qed.

Definition linearized A
           (rel:relation A)
           (l:list A): Prop :=
  forall i j x y
    (I: List.nth_error l i = Some x)
    (J: List.nth_error l j = Some y)
    (REL: rel x y),
    i < j.
Hint Unfold linearized.

Lemma linearize A
      (l: list A)
      (rel: relation A)
      (ACYCLIC: acyclic rel):
  exists l',
    <<PERM: Permutation l' l>> /\
    <<REL: linearized rel l'>>.
Proof.
  remember (length l) as n eqn:LEN. revert l LEN.
  induction n using strong_nat_ind. i. subst.
  destruct l.
  { esplits; eauto. ii. destruct i; ss. }
  generalize (partition l (fun b => rtc rel b a)). i. des.

  exploit (H (length l1)); ss.
  { erewrite <- (Permutation_length H0), List.app_length. lia. }
  i. des.

  exploit (H (length l2)); ss.
  { erewrite <- (Permutation_length H0), List.app_length. lia. }
  i. des.

  exists (l' ++ a :: l'0). esplits.
  { rewrite <- Permutation_middle. econs.
    rewrite Permutation_app; eauto.
  }
  rewrite List.Forall_forall in H1, H2. ii.
  destruct (Nat.compare_spec (length l') i), (Nat.compare_spec (length l') j);
    repeat (subst;
            match goal with
            | [X: List.nth_error (?l ++ _) (length ?l) = Some _ |- _] =>
              rewrite List.nth_error_app2 in X; ss
            | [X: List.nth_error (?l ++ _) ?i = Some _,
                  Y: ?i < length ?l |- _] =>
              rewrite List.nth_error_app1 in X; [|lia]
            | [X: List.nth_error (?l ++ _) ?i = Some _,
                  Y: length ?l < ?i |- _] =>
              rewrite List.nth_error_app2 in X; [|lia]
            | [X: List.nth_error (_ :: _) (?i - ?j) = Some _, Y: ?j < ?i |- _] =>
              let XX := fresh "XX" in
              hexploit Nat.sub_gt; try exact Y; eauto; i; destruct (i - j) eqn:XX
            | [X: context[?x - ?x] |- _] => rewrite Nat.sub_diag in X
            | [X: Some _ = Some _ |- _] => inv X
            end;
            ss).
  - exfalso. eapply ACYCLIC. econs. eauto.
  - hexploit H1.
    { eapply Permutation_in; eauto.
      eapply List.nth_error_In; eauto.
    }
    i. exfalso. eapply ACYCLIC. apply clos_t1n_trans.
    hexploit rtc_step_tc; eauto.
  - hexploit H2.
    { eapply Permutation_in; eauto.
      eapply List.nth_error_In; eauto.
    }
    i. contradict H5. econs; eauto.
  - exploit REL0; try exact REL1; eauto. lia.
  - hexploit H1.
    { eapply Permutation_in; eauto.
      eapply List.nth_error_In; eauto.
    }
    hexploit H2.
    { eapply Permutation_in; eauto.
      eapply List.nth_error_In; eauto.
    }
    i. contradict H6. etrans; eauto.
  - lia.
  - exploit REL; try exact REL1; eauto.
Qed.

Inductive sim_label (tid:Id.t): forall (label:Label.t) (msg:Msg.t), Prop :=
| sim_label_intro
    ex ord loc val:
    sim_label tid (Label.write ex ord loc val) (Msg.mk loc val tid)
.
Hint Constructors sim_label.

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

Definition list_rev_list_rect
           (A:Type)
           (P:list A -> Type)
           (INIT: P [])
	         (STEP: forall (a:A) (l:list A), P (List.rev l) -> P (List.rev (a :: l))):
	forall l:list A, P (List.rev l).
Proof.
  induction l; auto.
Defined.

Definition list_rev_rect
           (A:Type)
           (P:list A -> Type)
           (INIT: P [])
           (STEP: forall x l, P l -> P (l ++ [x])):
  forall l, P l.
Proof.
  intros.
  generalize (List.rev_involutive l).
  intros E; rewrite <- E.
  apply (list_rev_list_rect P).
  auto.

  simpl.
  intros.
  apply (STEP a (List.rev l0)).
  auto.
Defined.

Definition promises_from_mem
           (tid:Id.t) (mem: Memory.t): Promises.t.
Proof.
  induction mem using list_rev_rect.
  - apply Promises.empty.
  - destruct x.
    apply (if tid0 == tid
           then Promises.set (S (List.length (List.rev mem))) IHmem
           else IHmem).
Defined.

Lemma promises_from_mem_empty tid:
  promises_from_mem tid Memory.empty = Promises.empty.
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

Definition Local_init_with_promises
           (promises: Promises.t): Local.t :=
  Local.mk bot bot bot bot bot bot bot
           (fun _ => None)
           bot
           promises.

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

Fixpoint view_eid (ex:Execution.t) (ob: list eidT) (eid:eidT): option View.t :=
  match ob with
  | [] => None
  | e::ob =>
    option_map
      (Nat.add match Execution.label e ex with
               | Some label => if Label.is_write label then 1 else 0
               | None => 0
               end)
      (if e == eid
       then Some 0
       else view_eid ex ob eid)
  end.

Lemma view_eid_inv
      ex ob eid view
      (VIEW: view_eid ex ob eid = Some view):
  exists n,
    <<N: List.nth_error ob n = Some eid>> /\
         <<VIEW: view = length
                          (List.filter
                             (fun eid =>
                                match Execution.label eid ex with
                                | Some label => Label.is_write label
                                | _ => false
                                end)
                             (List.firstn (S n) ob))>>.
Proof.
  revert view VIEW. induction ob; ss. i.
  revert VIEW. condtac.
  - inversion e. subst. s. i. inv VIEW.
    exists 0. splits; ss.
    destruct (Execution.label eid ex); ss. destruct t; ss.
  - destruct (view_eid ex ob eid) eqn:EID; ss. i. inv VIEW.
    exploit IHob; eauto. i. des. subst.
    eexists (S _). esplits; eauto.
    destruct (Execution.label a ex); ss. destruct t; ss.
Qed.

Lemma view_eid_ob
      ex rel ob eid1 eid2 view1 view2
      (LINEARIZED: linearized rel ob)
      (OB: rel eid1 eid2)
      (VIEW1: view_eid ex ob eid1 = Some view1)
      (VIEW2: view_eid ex ob eid2 = Some view2):
  le view1 view2.
Proof.
  exploit view_eid_inv; try exact VIEW1; eauto. i. des.
  exploit view_eid_inv; try exact VIEW2; eauto. i. des.
  subst. exploit LINEARIZED; try exact OB; eauto. i.
  erewrite (@List_firstn_le (S n) (S n0)); [|lia].
  rewrite HahnList.filter_app, List.app_length.
  unfold le. lia.
Qed.

Lemma view_eid_ob_write
      ex rel ob eid1 eid2 view1 view2 loc
      (LINEARIZED: linearized rel ob)
      (OB: rel eid1 eid2)
      (VIEW1: view_eid ex ob eid1 = Some view1)
      (VIEW2: view_eid ex ob eid2 = Some view2)
      (WRITE2: Execution.label_is ex (Label.is_writing loc) eid2):
  view1 < view2.
Proof.
  exploit view_eid_inv; try exact VIEW1; eauto. i. des.
  exploit view_eid_inv; try exact VIEW2; eauto. i. des.
  subst. exploit LINEARIZED; try exact OB; eauto. i.
  erewrite (@List_firstn_le (S n) (S n0)); [|lia].
  rewrite HahnList.filter_app, List.app_length.
  match goal with
  | [|- _ < _ + ?a] => destruct a eqn:A; [|lia]
  end.
  exfalso.
  exploit List_nth_error_skipn; eauto. i.
  exploit List_nth_error_firstn; [eauto| |i].
  { instantiate (1 := (S n0 - S n)). lia. }
  exploit List.nth_error_In; eauto. i.
  inv WRITE2.
  revert A x3. clear N N0 x x1 x2. induction ((List.firstn (S n0 - S n) (List.skipn (S n) ob))); ss.
  destruct (Execution.label a ex) eqn:X; ss.
  { destruct (Label.is_write t) eqn:T; ss.
    i. des.
    - subst. rewrite EID in X. inv X. destruct t; ss.
    - exploit IHl0; eauto.
  }
  i. des.
  - subst. rewrite EID in X. inv X.
  - exploit IHl0; eauto.
Qed.

Inductive sim_view (ex:Execution.t) (ob: list eidT) (eids:eidT -> Prop) (view:View.t): Prop :=
| sim_view_bot
    (VIEW: view = bot)
| sim_view_event
    eid v
    (EID: eids eid)
    (VIEW_EID: view_eid ex ob eid = Some v)
    (VIEW: le view v)
.
Hint Constructors sim_view.

Lemma sim_view_join ex ob pred v1 v2
      (V1: sim_view ex ob pred v1)
      (V2: sim_view ex ob pred v2):
  sim_view ex ob pred (join v1 v2).
Proof.
  inv V1.
  { rewrite join_comm, bot_join; [|exact View.order]. ss. }
  inv V2.
  { rewrite bot_join; [|exact View.order]. econs 2; eauto. }

  generalize (View.max_spec_le v1 v2). i. des.
  - unfold join, View.join. rewrite H0. econs 2; try exact VIEW_EID0; eauto.
  - unfold join, View.join. rewrite H0. econs 2; try exact VIEW_EID; eauto.
Qed.

Lemma sim_view_le ex ob pred1 pred2
      (PRED: pred1 <1= pred2):
  sim_view ex ob pred1 <1= sim_view ex ob pred2.
Proof.
  i. inv PR.
  - econs 1. ss.
  - econs 2; eauto.
Qed.

Lemma sim_view_step
      ex ob (r:relation eidT) tid n view
      (SIM: sim_view ex ob (inverse r (eq (tid, n))) view):
  sim_view ex ob (inverse (r ⨾ Execution.po_adj) (eq (tid, S n))) view.
Proof.
  inv SIM; eauto. inv EID. econs 2; eauto. econs; eauto. econs; eauto.
Qed.

Inductive sim_val (tid:Id.t) (ex:Execution.t) (ob: list eidT) (avala:ValA.t (A:=nat -> Prop)) (vala:ValA.t (A:=View.t)): Prop :=
| sim_val_intro
    (VAL: avala.(ValA.val) = vala.(ValA.val))
    (VIEW: sim_view ex ob (fun eid => eid.(fst) = tid /\ avala.(ValA.annot) eid.(snd)) vala.(ValA.annot))
.
Hint Constructors sim_val.

Inductive sim_rmap (tid:Id.t) (ex:Execution.t) (ob: list eidT) (armap:RMap.t (A:=nat -> Prop)) (rmap:RMap.t (A:=View.t)): Prop :=
| sim_rmap_intro
    (RMAP: IdMap.Forall2 (sim_val tid ex ob) armap rmap)
.
Hint Constructors sim_rmap.

Inductive sim_state (tid:Id.t) (ex:Execution.t) (ob: list eidT) (astate:State.t (A:=nat -> Prop)) (state:State.t (A:=View.t)): Prop :=
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

Lemma sim_local_coh_internal
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
      econs; eauto. econs; eauto.
    + destruct (equiv_dec loc0 loc); ss. inv e. econs; eauto. apply Label.write_is_writing.
  - inv H1. splits.
    + econs 2; [econs|].
      { right. eauto. }
      exploit EX.(Valid.RF). intros [RF1 RF2].
      exploit RF2.
      { esplits; eauto. }
      i. des.
      econs. left. left. left. econs; eauto.
      econs; eauto. econs; eauto.
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

  (⦗ex.(Execution.label_is) (Label.is_acquire)⦘ ⨾
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

    (⦗ex.(Execution.label_is) (Label.is_acquire)⦘))) ⨾
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

  (⦗ex.(Execution.label_is) (Label.is_acquire)⦘ ⨾
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

    (⦗ex.(Execution.label_is) (Label.is_acquire)⦘))) ⨾
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

Inductive sim_local (tid:Id.t) (ex:Execution.t) (ob: list eidT) (alocal:ALocal.t) (local:Local.t): Prop := mk_sim_local {
  COH: forall loc,
        sim_view
          ex ob
          (inverse (sim_local_coh ex loc) (eq (tid, List.length (alocal.(ALocal.labels)))))
          (local.(Local.coh) loc);
  VRP: sim_view
         ex ob
         (inverse (sim_local_vrp ex) (eq (tid, List.length (alocal.(ALocal.labels)))))
         local.(Local.vrp);
  VWP: sim_view
         ex ob
         (inverse (sim_local_vwp ex) (eq (tid, List.length (alocal.(ALocal.labels)))))
         local.(Local.vwp);
  VRM: sim_view
         ex ob
         (inverse
            (⦗ex.(Execution.label_is) (Label.is_read)⦘ ⨾ Execution.po)
            (eq (tid, List.length (alocal.(ALocal.labels)))))
         local.(Local.vrm);
  VWM: sim_view
         ex ob
         (inverse
            (⦗ex.(Execution.label_is) (Label.is_write)⦘ ⨾ Execution.po)
            (eq (tid, List.length (alocal.(ALocal.labels)))))
         local.(Local.vwm);
  VCAP:
       sim_view
         ex ob
         (inverse
            (ex.(Execution.ctrl) ∪ (ex.(Execution.addr) ⨾ Execution.po))
            (eq (tid, List.length (alocal.(ALocal.labels)))))
         local.(Local.vcap);
  VREL: sim_view
          ex ob
          (inverse
             (⦗ex.(Execution.label_is) (Label.is_release)⦘ ⨾ Execution.po)
             (eq (tid, List.length (alocal.(ALocal.labels)))))
          local.(Local.vrel);
  EXBANK: opt_rel
            (fun aexbank exbank => view_eid ex ob (tid, aexbank) = Some exbank)
            alocal.(ALocal.exbank) local.(Local.exbank);
}.
Hint Constructors sim_local.
(* TODO: fwdbank *)
(* TODO: promises as (promises_from_mem tid (Machine.mem m)) - (fulfilled promises in local.labels) *)

Inductive sim_eu (tid:Id.t) (ex:Execution.t) (ob: list eidT) (aeu:AExecUnit.t) (eu:ExecUnit.t): Prop :=
| sim_eu_intro
    (STATE: sim_state tid ex ob aeu.(AExecUnit.state) eu.(ExecUnit.state))
    (LOCAL: sim_local tid ex ob aeu.(AExecUnit.local) eu.(ExecUnit.local))
    (MEM: eu.(ExecUnit.mem) = mem_of_ex ex ob)
.
Hint Constructors sim_eu.

Lemma label_write_mem_of_ex_msg
      eid ex ob exm ord loc val
      (OB: Permutation ob (Execution.eids ex))
      (LABEL: Execution.label eid ex = Some (Label.write exm ord loc val)):
  exists n,
    <<VIEW: view_eid ex ob eid = Some (S n)>> /\
    <<MSG: List.nth_error (mem_of_ex ex ob) n = Some (Msg.mk loc val eid.(fst))>>.
Proof.
  generalize (Execution.eids_spec ex). i. des. rename NODUP into NODUP0.
  specialize (LABEL0 eid). rewrite LABEL in LABEL0.
  inv LABEL0. clear H0. exploit H; [congr|]. clear H. intro IN0.
  symmetry in OB. exploit Permutation_in; eauto. intro IN.
  exploit HahnList.Permutation_nodup; eauto. intro NODUP.
  clear OB IN0 NODUP0. revert IN NODUP. induction ob; ss. i. des.
  - subst. condtac; [|congr]. s. esplits; eauto.
    + rewrite LABEL. s. eauto.
    + unfold mem_of_ex. ss. rewrite LABEL. ss.
  - condtac.
    { inversion e. subst. inv NODUP. congr. }
    inv NODUP. exploit IHob; eauto. i. des.
    rewrite VIEW. s. esplits; eauto.
    unfold mem_of_ex. s.
    destruct (Execution.label a ex) eqn:ALABEL; ss.
    destruct t; ss.
Qed.

Lemma label_write_mem_of_ex
      eid ex ob exm ord loc val
      (OB: Permutation ob (Execution.eids ex))
      (LABEL: Execution.label eid ex = Some (Label.write exm ord loc val)):
  exists n,
    <<VIEW: view_eid ex ob eid = Some (S n)>> /\
    <<READ: Memory.read (S n) loc (mem_of_ex ex ob) = Some val>> /\
    <<WRITE: Memory.write (S n) (Msg.mk loc val eid.(fst)) (mem_of_ex ex ob) = Some (mem_of_ex ex ob)>>.
Proof.
  exploit label_write_mem_of_ex_msg; eauto. i. des.
  esplits; eauto.
  - unfold Memory.read. s. rewrite MSG. s. condtac; [|congr]. ss.
  - unfold Memory.write. s. rewrite MSG. condtac; [|congr]. ss.
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
    <<STEP: ExecUnit.step tid eu1 eu2>> /\
    <<SIM: sim_eu tid ex ob aeu2 eu2>>.
Proof.
  destruct eu1 as [[stmts1 rmap1] local1].
  destruct aeu1 as [[astmts1 armap1] alocal1].
  destruct aeu2 as [[astmts2 armap2] alocal2].
  inv SIM. inv STATE. ss. subst. rename LOCAL into SIM_LOCAL.
  inv STEP. ss. inv STATE; inv LOCAL; inv EVENT; ss.
  - (* skip *)
    eexists (ExecUnit.mk _ _ _). esplits.
    + econs; ss.
      { econs; ss. }
      econs; ss.
    + econs; ss.
      inv SIM_LOCAL; econs; eauto. s.
      unfold join, bot. rewrite (bot_join (A:=View.t)); eauto.
      exact View.order.
  - (* assign *)
    eexists (ExecUnit.mk _ _ _). esplits.
    + econs; ss.
      { econs; ss. }
      econs; ss.
    + econs; ss.
      * econs; ss. apply sim_rmap_add; ss. apply sim_rmap_expr; ss.
      * inv SIM_LOCAL; econs; eauto. s.
        unfold join, bot. rewrite (bot_join (A:=View.t)); [|exact View.order].
        eauto.
  - (* read *)
    exploit LABEL; eauto.
    { rewrite List.nth_error_app2; [|refl]. rewrite Nat.sub_diag. ss. }
    intro LABEL_LEN.
    exploit EX.(Valid.RF). intros [RF _]. exploit RF; eauto. i. des.
    exploit label_write_mem_of_ex; eauto. i. des.
    exploit sim_rmap_expr; eauto. instantiate (1 := eloc). intro X. inv X.
    eexists (ExecUnit.mk _ _ _). esplits.
    + econs; ss.
      { econs; ss. }
      econs 2; ss. econs; eauto.
      * (* internal *)
        generalize (SIM_LOCAL.(COH) (ValA.val (sem_expr armap1 eloc))).
        intro X. inv X.
        { rewrite VIEW1. apply bot_spec. }
        rewrite VIEW1. inv EID.
        exploit sim_local_coh_internal; eauto.
        { econs; eauto. ss. eapply Label.read_is_accessing. }
        i. des. inv LABEL1. apply Label.is_writing_inv in LABEL2. des. subst.
        exploit EX.(Valid.CO). intros [CO _]. exploit CO.
        { esplits; [exact LABEL0|exact EID]. }
        i. des.
        { subst. rewrite VIEW in VIEW_EID. inv VIEW_EID. refl. }
        { exfalso. eapply EX.(Valid.INTERNAL). econs 2; eauto.
          econs. left. left. right. econs. splits; [|exact x]. apply RF0.
        }
        { eapply view_eid_ob; eauto. left. left. left. right. ss. }
      * admit. (* external *)
    + econs; ss.
      * econs; ss. apply sim_rmap_add; ss. econs; ss.
        admit. (* sim_view *)
      * admit. (* sim_local *)
  - (* write *)
    exploit LABEL.
    { rewrite List.nth_error_app2; [|refl]. rewrite Nat.sub_diag. ss. }
    intro LABEL_WRITE.
    exploit label_write_mem_of_ex; eauto. i. des.
    exploit sim_rmap_expr; eauto. instantiate (1 := eloc). intro X. inv X.
    exploit sim_rmap_expr; eauto. instantiate (1 := eval). intro X. inv X.
    eexists (ExecUnit.mk _ _ _). esplits.
    + econs; ss.
      { econs; ss. }
      econs 3; ss.
      econs;
        try match goal with
            | [|- _ = _] => refl
            end.
      all: cycle 2.
      * i. specialize (EX0 H). des.
        generalize (SIM_LOCAL.(EXBANK)). rewrite EX0. i. inv H0.
        esplits; eauto.
      * rewrite <- VAL, <- VAL0. eauto.
      * (* internal *)
        rewrite <- VAL.
        generalize (SIM_LOCAL.(COH) (ValA.val (sem_expr armap1 eloc))).
        intro X. inv X.
        { rewrite VIEW2. unfold bot, View.bot. lia. }
        eapply View.le_lt_trans; eauto. inv EID.
        exploit sim_local_coh_internal; eauto.
        { econs; eauto. apply Label.write_is_accessing. }
        i. des. inv LABEL0. apply Label.is_writing_inv in LABEL1. des. subst.
        exploit EX.(Valid.CO). intros [CO _]. exploit CO.
        { esplits; [exact LABEL_WRITE|exact EID]. }
        i. des.
        { subst. exfalso. eapply EX.(Valid.INTERNAL). eauto. }
        { exfalso. eapply EX.(Valid.INTERNAL). econs 2; eauto.
          econs. left. right. ss.
        }
        { eapply view_eid_ob_write; eauto.
          - left. left. left. right. ss.
          - econs; eauto. apply Label.write_is_writing.
        }
      * admit. (* external *)
    + econs; ss.
      * econs; ss. apply sim_rmap_add; ss. econs; ss.
        admit. (* sim_view *)
      * admit. (* sim_local *)
  - (* write_failure *)
    eexists (ExecUnit.mk _ _ _). esplits.
    + econs; ss.
      { econs; ss. }
      econs 4; ss.
    + econs; ss.
      * econs; ss. apply sim_rmap_add; ss. econs; ss. econs 1. ss.
      * inv SIM_LOCAL; econs; eauto. econs.
  - (* barrier *)
    destruct b0; eexists (ExecUnit.mk _ _ _).
    + (* isb *)
      esplits.
      { econs; ss.
        - econs; ss.
        - econs 5; ss.
      }
      econs; ss.
      econs; ss.
      * rewrite List.app_length. s. rewrite Nat.add_1_r.
        i. rewrite sim_local_coh_step. apply sim_view_step.
        rewrite inverse_union. eapply sim_view_le; [by left; eauto|].
        apply SIM_LOCAL.
      * rewrite List.app_length. s. rewrite Nat.add_1_r.
        rewrite sim_local_vrp_step. apply sim_view_step.
        rewrite ? inverse_union. apply sim_view_join.
        { eapply sim_view_le; [|exact SIM_LOCAL.(VRP)]. eauto. }
        { eapply sim_view_le; [|exact SIM_LOCAL.(VCAP)].
          right. left. right.
          inv PR. econs; eauto. econs; splits; eauto.
          econs; eauto. econs; eauto. apply LABEL.
          rewrite List.nth_error_app2; ss. rewrite Nat.sub_diag. ss.
        }
      * rewrite List.app_length. s. rewrite Nat.add_1_r.
        rewrite sim_local_vwp_step. apply sim_view_step.
        rewrite ? inverse_union. eapply sim_view_le; [|exact SIM_LOCAL.(VWP)]. eauto.
      * rewrite List.app_length. s. rewrite Nat.add_1_r.
        rewrite Execution.po_po_adj, clos_refl_union, union_seq, eq_seq.
        rewrite seq_union, inverse_union. eapply sim_view_le; [by left; eauto|].
        rewrite seq_assoc. apply sim_view_step; eauto. apply SIM_LOCAL.
      * rewrite List.app_length. s. rewrite Nat.add_1_r.
        rewrite Execution.po_po_adj, clos_refl_union, union_seq, eq_seq.
        rewrite seq_union, inverse_union. eapply sim_view_le; [by left; eauto|].
        rewrite seq_assoc. apply sim_view_step; eauto. apply SIM_LOCAL.
      * rewrite List.app_length. s. rewrite Nat.add_1_r.
        eapply sim_view_le; [|exact SIM_LOCAL.(VCAP)]. i. inv PR.
        eapply inverse_mon; [exact EX.(Valid.cap_po_adj)|].
        econs; eauto. econs. splits; eauto.
      * rewrite List.app_length. s. rewrite Nat.add_1_r.
        rewrite Execution.po_po_adj, clos_refl_union, union_seq, eq_seq.
        rewrite seq_union, inverse_union. eapply sim_view_le; [by left; eauto|].
        rewrite seq_assoc. apply sim_view_step; eauto. apply SIM_LOCAL.
      * apply SIM_LOCAL.
    + (* dmbst *)
      esplits.
      { econs; ss.
        - econs; ss.
        - econs 6; ss.
      }
      econs; ss.
      econs; ss.
      * rewrite List.app_length. s. rewrite Nat.add_1_r.
        i. rewrite sim_local_coh_step. apply sim_view_step.
        rewrite inverse_union. eapply sim_view_le; [by left; eauto|].
        apply SIM_LOCAL.
      * rewrite List.app_length. s. rewrite Nat.add_1_r.
        rewrite sim_local_vrp_step. apply sim_view_step.
        rewrite ? inverse_union. eapply sim_view_le; [|exact SIM_LOCAL.(VRP)]. eauto.
      * rewrite List.app_length. s. rewrite Nat.add_1_r.
        rewrite sim_local_vwp_step. apply sim_view_step.
        rewrite ? inverse_union. apply sim_view_join.
        { eapply sim_view_le; [|exact SIM_LOCAL.(VWP)]. eauto. }
        { eapply sim_view_le; [|exact SIM_LOCAL.(VWM)].
          right. left. right. rewrite seq_assoc.
          inv PR. econs; eauto. econs; splits; eauto.
          econs; eauto. econs; eauto. apply LABEL.
          rewrite List.nth_error_app2; ss. rewrite Nat.sub_diag. ss.
        }
      * rewrite List.app_length. s. rewrite Nat.add_1_r.
        rewrite Execution.po_po_adj, clos_refl_union, union_seq, eq_seq.
        rewrite seq_union, inverse_union. eapply sim_view_le; [by left; eauto|].
        rewrite seq_assoc. apply sim_view_step; eauto. apply SIM_LOCAL.
      * rewrite List.app_length. s. rewrite Nat.add_1_r.
        rewrite Execution.po_po_adj, clos_refl_union, union_seq, eq_seq.
        rewrite seq_union, inverse_union. eapply sim_view_le; [by left; eauto|].
        rewrite seq_assoc. apply sim_view_step; eauto. apply SIM_LOCAL.
      * rewrite List.app_length. s. rewrite Nat.add_1_r.
        eapply sim_view_le; [|exact SIM_LOCAL.(VCAP)]. i. inv PR.
        eapply inverse_mon; [exact EX.(Valid.cap_po_adj)|].
        econs; eauto. econs. splits; eauto.
      * rewrite List.app_length. s. rewrite Nat.add_1_r.
        rewrite Execution.po_po_adj, clos_refl_union, union_seq, eq_seq.
        rewrite seq_union, inverse_union. eapply sim_view_le; [by left; eauto|].
        rewrite seq_assoc. apply sim_view_step; eauto. apply SIM_LOCAL.
      * apply SIM_LOCAL.
    + (* dmbld *)
      esplits.
      { econs; ss.
        - econs; ss.
        - econs 7; ss.
      }
      econs; ss.
      econs; ss.
      * rewrite List.app_length. s. rewrite Nat.add_1_r.
        i. rewrite sim_local_coh_step. apply sim_view_step.
        rewrite inverse_union. eapply sim_view_le; [by left; eauto|].
        apply SIM_LOCAL.
      * rewrite List.app_length. s. rewrite Nat.add_1_r.
        rewrite sim_local_vrp_step. apply sim_view_step.
        rewrite ? inverse_union. apply sim_view_join.
        { eapply sim_view_le; [|exact SIM_LOCAL.(VRP)]. eauto. }
        { eapply sim_view_le; [|exact SIM_LOCAL.(VRM)].
          right. left. left. right. rewrite seq_assoc.
          inv PR. econs; eauto. econs; splits; eauto.
          econs; eauto. econs; eauto. apply LABEL.
          rewrite List.nth_error_app2; ss. rewrite Nat.sub_diag. ss.
        }
      * rewrite List.app_length. s. rewrite Nat.add_1_r.
        rewrite sim_local_vwp_step. apply sim_view_step.
        rewrite ? inverse_union. apply sim_view_join.
        { eapply sim_view_le; [|exact SIM_LOCAL.(VWP)]. eauto. }
        { eapply sim_view_le; [|exact SIM_LOCAL.(VRM)].
          right. left. left. right. rewrite seq_assoc.
          inv PR. econs; eauto. econs; splits; eauto.
          econs; eauto. econs; eauto. apply LABEL.
          rewrite List.nth_error_app2; ss. rewrite Nat.sub_diag. ss.
        }
      * rewrite List.app_length. s. rewrite Nat.add_1_r.
        rewrite Execution.po_po_adj, clos_refl_union, union_seq, eq_seq.
        rewrite seq_union, inverse_union. eapply sim_view_le; [by left; eauto|].
        rewrite seq_assoc. apply sim_view_step; eauto. apply SIM_LOCAL.
      * rewrite List.app_length. s. rewrite Nat.add_1_r.
        rewrite Execution.po_po_adj, clos_refl_union, union_seq, eq_seq.
        rewrite seq_union, inverse_union. eapply sim_view_le; [by left; eauto|].
        rewrite seq_assoc. apply sim_view_step; eauto. apply SIM_LOCAL.
      * rewrite List.app_length. s. rewrite Nat.add_1_r.
        eapply sim_view_le; [|exact SIM_LOCAL.(VCAP)]. i. inv PR.
        eapply inverse_mon; [exact EX.(Valid.cap_po_adj)|].
        econs; eauto. econs. splits; eauto.
      * rewrite List.app_length. s. rewrite Nat.add_1_r.
        rewrite Execution.po_po_adj, clos_refl_union, union_seq, eq_seq.
        rewrite seq_union, inverse_union. eapply sim_view_le; [by left; eauto|].
        rewrite seq_assoc. apply sim_view_step; eauto. apply SIM_LOCAL.
      * apply SIM_LOCAL.
    + (* dmbsy *)
      esplits.
      { econs; ss.
        - econs; ss.
        - econs 8; ss.
      }
      econs; ss.
      econs; ss.
      * rewrite List.app_length. s. rewrite Nat.add_1_r.
        i. rewrite sim_local_coh_step. apply sim_view_step.
        rewrite inverse_union. eapply sim_view_le; [by left; eauto|].
        apply SIM_LOCAL.
      * rewrite List.app_length. s. rewrite Nat.add_1_r.
        rewrite sim_local_vrp_step. apply sim_view_step.
        rewrite ? inverse_union. repeat apply sim_view_join.
        { eapply sim_view_le; [|exact SIM_LOCAL.(VRP)]. eauto. }
        { eapply sim_view_le; [|exact SIM_LOCAL.(VRM)].
          right. left. left. left.
          inv PR. inv REL. des. inv H. econs; eauto. econs; splits; eauto.
          econs; eauto. econs; eauto. apply LABEL.
          rewrite List.nth_error_app2; ss. rewrite Nat.sub_diag. ss.
        }
        { eapply sim_view_le; [|exact SIM_LOCAL.(VWM)].
          right. left. left. left.
          inv PR. inv REL. des. inv H. econs; eauto. econs; splits; eauto.
          econs; eauto. econs; eauto. apply LABEL.
          rewrite List.nth_error_app2; ss. rewrite Nat.sub_diag. ss.
        }
        { econs. ss. }
      * rewrite List.app_length. s. rewrite Nat.add_1_r.
        rewrite sim_local_vwp_step. apply sim_view_step.
        rewrite ? inverse_union. repeat apply sim_view_join.
        { eapply sim_view_le; [|exact SIM_LOCAL.(VWP)]. eauto. }
        { eapply sim_view_le; [|exact SIM_LOCAL.(VRM)].
          right. left. left. left.
          inv PR. inv REL. des. inv H. econs; eauto. econs; splits; eauto.
          econs; eauto. econs; eauto. apply LABEL.
          rewrite List.nth_error_app2; ss. rewrite Nat.sub_diag. ss.
        }
        { eapply sim_view_le; [|exact SIM_LOCAL.(VWM)].
          right. left. left. left.
          inv PR. inv REL. des. inv H. econs; eauto. econs; splits; eauto.
          econs; eauto. econs; eauto. apply LABEL.
          rewrite List.nth_error_app2; ss. rewrite Nat.sub_diag. ss.
        }
        { econs. ss. }
      * rewrite List.app_length. s. rewrite Nat.add_1_r.
        rewrite Execution.po_po_adj, clos_refl_union, union_seq, eq_seq.
        rewrite seq_union, inverse_union. eapply sim_view_le; [by left; eauto|].
        rewrite seq_assoc. apply sim_view_step; eauto. apply SIM_LOCAL.
      * rewrite List.app_length. s. rewrite Nat.add_1_r.
        rewrite Execution.po_po_adj, clos_refl_union, union_seq, eq_seq.
        rewrite seq_union, inverse_union. eapply sim_view_le; [by left; eauto|].
        rewrite seq_assoc. apply sim_view_step; eauto. apply SIM_LOCAL.
      * rewrite List.app_length. s. rewrite Nat.add_1_r.
        eapply sim_view_le; [|exact SIM_LOCAL.(VCAP)]. i. inv PR.
        eapply inverse_mon; [exact EX.(Valid.cap_po_adj)|].
        econs; eauto. econs. splits; eauto.
      * rewrite List.app_length. s. rewrite Nat.add_1_r.
        rewrite Execution.po_po_adj, clos_refl_union, union_seq, eq_seq.
        rewrite seq_union, inverse_union. eapply sim_view_le; [by left; eauto|].
        rewrite seq_assoc. apply sim_view_step; eauto. apply SIM_LOCAL.
      * apply SIM_LOCAL.
  - (* if *)
    eexists (ExecUnit.mk _ _ _). esplits.
    + econs; ss.
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
    + econs; ss.
      { econs; ss. }
      * econs; ss.
    + econs; ss.
      inv SIM_LOCAL; econs; eauto. s.
      unfold join, bot. rewrite (bot_join (A:=View.t)); eauto.
      exact View.order.
Admitted.

Lemma sim_eu_rtc_step
      p ex ob tid aeu1 eu1 aeu2
      (EX: Valid.ex p ex)
      (OB: Permutation ob (Execution.eids ex))
      (LINEARIZED: linearized ex.(Execution.ob) ob)
      (SIM: sim_eu tid ex ob aeu1 eu1)
      (WF: AExecUnit.wf aeu1)
      (STEP: rtc AExecUnit.step aeu1 aeu2)
      (LOCAL: IdMap.find tid EX.(Valid.locals) = Some aeu2.(AExecUnit.local)):
  exists eu2,
    <<SIM: sim_eu tid ex ob aeu2 eu2>> /\
    <<STEP: rtc (ExecUnit.step tid) eu1 eu2>>.
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

Lemma promise_mem
      p mem
      (MEM: forall msg (MSG: List.In msg mem), IdMap.find msg.(Msg.tid) p <> None):
  exists m,
    <<STEP: rtc Machine.step0 (Machine.init p) m>> /\
    <<TPOOL: forall tid, IdMap.find tid m.(Machine.tpool) =
                    option_map
                      (fun stmts => (State.init stmts,
                                  Local_init_with_promises (promises_from_mem tid m.(Machine.mem))))
                      (IdMap.find tid p)>> /\
    <<MEM: m.(Machine.mem) = mem>>.
Proof.
  revert MEM. induction mem using List.rev_ind; i.
  { esplits; eauto. i. s. rewrite IdMap.map_spec.
    destruct (IdMap.find tid p); ss.
    unfold Local.init, Local_init_with_promises. repeat f_equal.
    rewrite promises_from_mem_empty. ss.
  }
  exploit IHmem; eauto.
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
    + rewrite TPOOL, FIND. ss.
    + econs 2; ss. econs; eauto. ss.
    + ss.
  - s. i. rewrite IdMap.add_spec. condtac; ss.
    + inversion e. subst. rewrite FIND. s.
      unfold Local_init_with_promises. repeat f_equal.
      rewrite promises_from_mem_snoc. condtac; ss.
    + rewrite TPOOL. destruct (IdMap.find tid0 p); ss.
      unfold Local_init_with_promises. rewrite promises_from_mem_snoc. s.
      condtac; ss. congr.
  - ss.
Qed.

Theorem axiomatic_to_promising
      p ex
      (EX: Valid.ex p ex):
  exists (m: Machine.t),
    <<STEP: rtc Machine.step (Machine.init p) m>> /\
    <<TERMINAL: Machine.is_terminal m>> /\
    <<MEM: sim_mem ex m.(Machine.mem)>>.
Proof.
  (* Linearize events and construct memory. *)
  exploit (linearize (Execution.eids ex)).
  { eapply EX.(Valid.EXTERNAL). }
  i. des. rename l' into ob.
  remember (mem_of_ex ex ob) as mem eqn:MEM.

  (* Construct promise steps. *)
  exploit (promise_mem p mem); eauto.
  { i. subst. unfold mem_of_ex in MSG. rewrite in_filter_map_iff in MSG. des.
    exploit Permutation_in; eauto. intro X.
    generalize (Execution.eids_spec ex). i. des.
    apply LABEL in X. destruct (Execution.label a ex) eqn:Y; ss.
    destruct t; ss. inv MSG0. s. unfold Execution.label in Y.
    rewrite EX.(Valid.LABELS), IdMap.map_spec in Y.
    destruct (IdMap.find (fst a) (Valid.locals (Valid.PRE EX))) eqn:Z; ss.
    generalize (EX.(Valid.LOCALS) (fst a)). intro W. inv W; ss. congr.
  }
  i. des. subst.

  (* It's sufficient to construct steps from the promised state. *)
  cut (exists m0,
          <<STEP: rtc Machine.step0 m m0>> /\
          <<TERMINAL: Machine.is_terminal m0>> /\
          <<MEM: sim_mem ex (Machine.mem m0)>>).
  { i. des. esplits; cycle 1; eauto.
    apply Machine.rtc_step0_step.
    - etrans; eauto.
    - econs. i. inv TERMINAL. exploit TERMINAL0; eauto. i. des. ss.
  }
  clear STEP.

  (* Execute threads one-by-one (induction). *)
  assert (IN: forall tid stmts
                (FIND1: IdMap.find tid p = Some stmts),
             IdMap.find tid m.(Machine.tpool) =
             Some (State.init stmts,
                   Local_init_with_promises (promises_from_mem tid (Machine.mem m)))).
  { i. rewrite TPOOL, FIND1. ss. }
  assert (OUT: forall tid st lc
                 (FIND1: IdMap.find tid p = None)
                 (FIND2: IdMap.find tid m.(Machine.tpool) = Some (st, lc)),
             State.is_terminal st /\ Promises.is_empty lc.(Local.promises)).
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
  { i. esplits; eauto. }
  i.

  destruct a as [tid stmts].
  exploit (IN tid); eauto.
  { destruct (equiv_dec tid tid); [|congr]. ss. }
  intro FIND.
  cut (exists st2 lc2,
          <<STEP: rtc (ExecUnit.step tid)
                      (ExecUnit.mk
                         (State.init stmts)
                         (Local_init_with_promises (promises_from_mem tid (Machine.mem m)))
                         (Machine.mem m))
                      (ExecUnit.mk st2 lc2 (Machine.mem m))>> /\
          <<TERMINAL: State.is_terminal st2 /\ Promises.is_empty lc2.(Local.promises)>>).
  { i. des. subst.
    exploit Machine.rtc_eu_step_step0; try exact STEP; eauto. i.
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
  generalize (EX.(Valid.LOCALS) tid). rewrite FINDP.
  intro X. inv X. des. rename b into local, H into LOCAL. clear FINDP.
  exploit (@sim_eu_rtc_step p ex ob tid); eauto.
  { instantiate (1 := ExecUnit.mk
                        (State.init stmts)
                        (Local_init_with_promises (promises_from_mem tid (mem_of_ex ex ob)))
                        (mem_of_ex ex ob)).
    econs; ss.
    - econs; ss. econs. ii. rewrite ? IdMap.gempty. ss.
    - econs; eauto. s. econs.
  }
  { apply AExecUnit.wf_init. }
  i. des. destruct eu2 as [state2 local2 mem2]. inv SIM. ss. subst.
  esplits; eauto.
  - unfold State.is_terminal in *. inv STATE. congr.
  - admit. (* promises is empty. *)
Admitted.
