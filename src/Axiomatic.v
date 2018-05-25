Require Import Relations.
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

Set Implicit Arguments.


Module Label.
  Inductive t :=
  | read (ex:bool) (ord:ordT) (loc:Loc.t) (val:Val.t)
  | write (ex:bool) (ord:ordT) (loc:Loc.t) (val:Val.t)
  | barrier (b:Barrier.t)
  .

  Definition is_ex (label:t): bool :=
    match label with
    | read ex _ _ _ => ex
    | write ex _ _ _ => ex
    | barrier _ => false
    end.

  Definition is_read (label:t): bool :=
    match label with
    | read _ _ _ _ => true
    | _ => false
    end.

  Definition is_reading (loc:Loc.t) (label:t): bool :=
    match label with
    | read _ _ loc' _ => loc' == loc
    | _ => false
    end.

  (* TODO: define AcquirePC ordering *)
  Definition is_acquire_pc (label:t): bool :=
    match label with
    | read _ ord _ _ => ord_ge ord ra
    | _ => false
    end.

  Definition is_acquire (label:t): bool :=
    match label with
    | read _ ord _ _ => ord_ge ord ra
    | _ => false
    end.

  Definition is_release (label:t): bool :=
    match label with
    | write _ ord _ _ => ord_ge ord ra
    | _ => false
    end.

  Definition is_write (label:t): bool :=
    match label with
    | write _ _ _ _ => true
    | _ => false
    end.

  Definition is_writing (loc:Loc.t) (label:t): bool :=
    match label with
    | write _ _ loc' _ => loc' == loc
    | _ => false
    end.

  Definition is_accessing (loc:Loc.t) (label:t): bool :=
    match label with
    | read _ _ loc' _ => loc' == loc
    | write _ _ loc' _ => loc' == loc
    | _ => false
    end.

  Lemma read_is_reading ex ord loc val:
    is_reading loc (read ex ord loc val).
  Proof.
    s. destruct (equiv_dec loc loc); ss. exfalso. apply c. ss.
  Qed.

  Lemma write_is_writing ex ord loc val:
    is_writing loc (write ex ord loc val).
  Proof.
    s. destruct (equiv_dec loc loc); ss. exfalso. apply c. ss.
  Qed.

  Lemma read_is_accessing ex ord loc val:
    is_accessing loc (read ex ord loc val).
  Proof.
    s. destruct (equiv_dec loc loc); ss. exfalso. apply c. ss.
  Qed.

  Lemma write_is_accessing ex ord loc val:
    is_accessing loc (write ex ord loc val).
  Proof.
    s. destruct (equiv_dec loc loc); ss. exfalso. apply c. ss.
  Qed.

  Lemma is_writing_inv
        loc l
        (WRITING: is_writing loc l):
    exists ex ord val,
      l = write ex ord loc val.
  Proof.
    destruct l; ss. destruct (equiv_dec loc0 loc); ss. inv e. eauto.
  Qed.

  Lemma is_reading_inv
        loc l
        (WRITING: is_reading loc l):
    exists ex ord val,
      l = read ex ord loc val.
  Proof.
    destruct l; ss. destruct (equiv_dec loc0 loc); ss. inv e. eauto.
  Qed.
End Label.

Module ALocal.
  Inductive t := mk {
    labels: list Label.t;
    addr: relation nat;
    data: relation nat;
    ctrl: relation nat;
    rmw: relation nat;
    exbank: option nat;
  }.
  Hint Constructors t.

  Definition init: t := mk [] bot bot bot bot None.

  Definition next_eid (eu:t): nat :=
    List.length eu.(labels).

  Inductive step (event:Event.t (A:=nat -> Prop)) (alocal1:t) (alocal2:t): Prop :=
  | step_internal
      ctrl_e
      (EVENT: event = (Event.internal ctrl_e))
      (ALOCAL: alocal2 =
               mk
                 alocal1.(labels)
                 alocal1.(addr)
                 alocal1.(data)
                 (alocal1.(ctrl) ∪ (ctrl_e × (le (next_eid alocal1))))
                 alocal1.(rmw)
                 alocal1.(exbank))
  | step_read
      ex ord vloc res
      (EVENT: event = Event.read ex ord vloc (ValA.mk _ res (eq (next_eid alocal1))))
      (ALOCAL: alocal2 =
               mk
                 (alocal1.(labels) ++ [Label.read ex ord vloc.(ValA.val) res])
                 (alocal1.(addr) ∪ (vloc.(ValA.annot) × (eq (next_eid alocal1))))
                 alocal1.(data)
                 alocal1.(ctrl)
                 alocal1.(rmw)
                 (if ex then Some (next_eid alocal1) else alocal1.(exbank)))
  | step_write
      ex ord vloc vval
      (EVENT: event = Event.write ex ord vloc vval (ValA.mk _ 0 (eq (next_eid alocal1))))
      (EX: ex -> exists n,
           alocal1.(exbank) = Some n /\
           opt_pred (Label.is_reading vloc.(ValA.val)) (List.nth_error alocal1.(labels) n))
      (ALOCAL: alocal2 =
               mk
                 (alocal1.(labels) ++ [Label.write ex ord vloc.(ValA.val) vval.(ValA.val)])
                 (alocal1.(addr) ∪ (vloc.(ValA.annot) × (eq (next_eid alocal1))))
                 (alocal1.(data) ∪ (vval.(ValA.annot) × (eq (next_eid alocal1))))
                 alocal1.(ctrl)
                 (alocal1.(rmw) ∪ (if ex then (fun n => alocal1.(exbank) = Some n) × (eq (next_eid alocal1)) else bot))
                 (if ex then None else alocal1.(exbank)))
  | step_write_failure
      ord vloc vval
      (EVENT: event = Event.write true ord vloc vval (ValA.mk _ 1 bot))
      (ALOCAL: alocal2 =
               mk
                 alocal1.(labels)
                 alocal1.(addr)
                 alocal1.(data)
                 alocal1.(ctrl)
                 alocal1.(rmw)
                 None)
  | step_barrier
      b
      (EVENT: event = Event.barrier b)
      (ALOCAL: alocal2 =
               mk
                 (alocal1.(labels) ++ [Label.barrier b])
                 alocal1.(addr)
                 alocal1.(data)
                 alocal1.(ctrl)
                 alocal1.(rmw)
                 alocal1.(exbank))
  .
  Hint Constructors step.

  Inductive le (alocal1 alocal2:t): Prop :=
  | le_intro
      (LABELS: exists l, alocal2.(labels) = alocal1.(labels) ++ l)
      (ADDR: alocal1.(addr) ⊆ alocal2.(addr))
      (DATA: alocal1.(data) ⊆ alocal2.(data))
      (CTRL: alocal1.(ctrl) ⊆ alocal2.(ctrl))
      (RMW: alocal1.(rmw) ⊆ alocal2.(rmw))
  .

  Global Program Instance le_preorder: PreOrder le.
  Next Obligation.
    ii. econs.
    all: try by exists []; rewrite List.app_nil_r.
    all: try by apply inclusion_refl.
  Qed.
  Next Obligation.
    ii. inv H; inv H0. econs.
    all: try by eapply inclusion_trans; eauto.
    des. rewrite LABELS0, LABELS. rewrite <- List.app_assoc. eexists; eauto.
  Qed.
End ALocal.

Module AExecUnit.
  Inductive t := mk {
    state: State.t (A:=nat -> Prop);
    local: ALocal.t;
  }.
  Hint Constructors t.

  Inductive step (eu1 eu2:t): Prop :=
  | step_intro
      e
      (STATE: State.step e eu1.(state) eu2.(state))
      (LOCAL: ALocal.step e eu1.(local) eu2.(local))
  .

  Definition wf_rmap (rmap: RMap.t (A:=nat -> Prop)) (max:nat): Prop :=
    forall r n
      (N: (RMap.find r rmap).(ValA.annot) n),
      n < max.
  Hint Unfold wf_rmap.

  Lemma wf_rmap_expr
        rmap bound e n
        (WF: wf_rmap rmap bound)
        (N: (sem_expr rmap e).(ValA.annot) n):
    n < bound.
  Proof.
    revert n N. induction e; ss.
    - i. eapply WF. eauto.
    - i. inv N; eauto.
  Qed.

  Inductive wf (aeu:t): Prop :=
  | wf_intro
      (REG: wf_rmap aeu.(state).(State.rmap) (length aeu.(local).(ALocal.labels)))
      (ADDR: aeu.(local).(ALocal.addr) ⊆ lt)
      (DATA: aeu.(local).(ALocal.data) ⊆ lt)
      (CTRL: aeu.(local).(ALocal.ctrl) ⊆ lt)
      (CTRL_MON: aeu.(local).(ALocal.ctrl) ⨾ lt ⊆ aeu.(local).(ALocal.ctrl))
      (RMW: forall n ord loc val
              (LABEL: List.nth_error aeu.(local).(ALocal.labels) n = Some (Label.write true ord loc val)),
          codom_rel aeu.(local).(ALocal.rmw) n)
  .         
  Hint Constructors wf.

  Lemma wf_init stmts: wf (mk (State.init stmts) ALocal.init).
  Proof.
    econs; ss.
    - ii. unfold RMap.find, RMap.init in *. rewrite IdMap.gempty in *. inv N.
    - ii. inv H. des. inv H0.
    - i. apply List.nth_error_In in LABEL. inv LABEL.
  Qed.

  Lemma step_future
        eu1 eu2
        (WF: wf eu1)
        (STEP: step eu1 eu2):
    <<WF: wf eu2>> /\
    <<LE: ALocal.le eu1.(local) eu2.(local)>>.
  Proof.
    destruct eu1 as [state1 local1].
    destruct eu2 as [state2 local2].
    inv STEP. ss.
    inv STATE; inv LOCAL; inv EVENT; ss;
      repeat match goal with
             | [|- context[bot × _]] => rewrite cross_bot_l
             | [|- context[_ ∪ bot]] => rewrite union_bot_r
             end.
    - splits.
      + inv WF. ss.
      + destruct local1. refl.
    - splits.
      + inv WF. econs; ss.
        ii. revert N. unfold RMap.find, RMap.add. rewrite IdMap.add_spec. condtac; eauto.
        inversion e. subst. apply wf_rmap_expr. ss.
      + destruct local1. refl.
    - splits.
      + inv WF. econs; ss.
        * rewrite List.app_length. s.
          ii. revert N. unfold RMap.find, RMap.add. rewrite IdMap.add_spec. condtac.
          { inversion e. subst. i. inv N.
            unfold ALocal.next_eid. lia.
          }
          { i. exploit REG; eauto. lia. }
        * ii. inv H; eauto. inv H0. eapply wf_rmap_expr; eauto.
        * i. destruct (lt_dec n (length local1.(ALocal.labels))).
          { rewrite List.nth_error_app1 in LABEL; ss. eauto. }
          { rewrite List.nth_error_app2 in LABEL; [|lia].
            destruct ((n - length (ALocal.labels local1))) eqn:N; ss.
            apply List.nth_error_In in LABEL. inv LABEL.
          }
      + econs; ss.
        * esplits; eauto.
        * left. ss.
    - splits.
      + inv WF. econs; ss.
        * rewrite List.app_length. s.
          ii. revert N. unfold RMap.find, RMap.add. rewrite IdMap.add_spec. condtac.
          { inversion e. subst. i. inv N.
            unfold ALocal.next_eid. lia.
          }
          { i. exploit REG; eauto. lia. }
        * ii. inv H; eauto. inv H0. eapply wf_rmap_expr; eauto.
        * ii. inv H; eauto. inv H0. eapply wf_rmap_expr; eauto.
        * i. destruct (lt_dec n (length local1.(ALocal.labels))).
          { rewrite List.nth_error_app1 in LABEL; ss.
            exploit RMW; eauto. intro X. inv X. econs. left. eauto.
          }
          { rewrite List.nth_error_app2 in LABEL; [|lia].
            destruct ((n - length (ALocal.labels local1))) eqn:N; ss.
            - inv LABEL. assert (n = length (ALocal.labels local1)) by lia. subst.
              exploit EX; eauto. i. des.
              econs. right. econs; eauto. 
            - apply List.nth_error_In in LABEL. inv LABEL.
          }
      + econs; ss.
        * esplits; eauto.
        * left. ss.
        * left. ss.
        * left. ss.
    - splits.
      + inv WF. econs; ss.
        ii. revert N. unfold RMap.find, RMap.add. rewrite IdMap.add_spec. condtac; eauto.
        inversion e. subst. i. inv N.
      + econs; ss. eexists. rewrite List.app_nil_r. ss.
    - splits.
      + inv WF. econs; ss.
        * rewrite List.app_length. s.
          ii. exploit REG; eauto. lia.
        * i. destruct (lt_dec n (length local1.(ALocal.labels))).
          { rewrite List.nth_error_app1 in LABEL; ss. eauto. }
          { rewrite List.nth_error_app2 in LABEL; [|lia].
            destruct ((n - length (ALocal.labels local1))) eqn:N; ss.
            apply List.nth_error_In in LABEL. inv LABEL.
          }
      + econs; ss. eexists; eauto.
    - splits.
      + inv WF. econs; ss.
        * ii. inv H; eauto. inv H0.
          exploit wf_rmap_expr; eauto. i.
          unfold le, ALocal.next_eid in *. lia.
        * ii. inv H; eauto. inv H0. inv H.
          { left. apply CTRL_MON. econs; eauto. }
          { inv H0. right. econs; ss. unfold le in *. lia. }
      + econs; ss.
        * eexists. rewrite List.app_nil_r. ss.
        * left. ss.
    - splits.
      + inv WF. econs; ss.
      + destruct local1. refl.
  Qed.

  Lemma rtc_step_future
        eu1 eu2
        (WF: wf eu1)
        (STEP: rtc step eu1 eu2):
    <<WF: wf eu2>> /\
    <<LE: ALocal.le eu1.(local) eu2.(local)>>.
  Proof.
    revert WF. induction STEP; eauto.
    - esplits; eauto. refl.
    - i. exploit step_future; eauto. i. des.
      exploit IHSTEP; eauto. i. des.
      esplits; ss. etrans; eauto.
  Qed.
End AExecUnit.

Definition eidT := (Id.t * nat)%type.

Module Execution.
  Inductive t := mk {
    labels: IdMap.t (list Label.t);
    addr: relation eidT;
    data: relation eidT;
    ctrl: relation eidT;
    rmw: relation eidT;
    co: relation eidT;
    rf: relation eidT;
  }.

  Definition label (eid:eidT) (ex:t): option Label.t :=
    match IdMap.find eid.(fst) ex.(labels) with
    | None => None
    | Some labels => List.nth_error labels eid.(snd)
    end.

  Definition eids (ex:t): list eidT :=
    IdMap.fold
      (fun tid local eids => (List.map (fun i => (tid, i)) (List.seq 0 (List.length local))) ++ eids)
      ex.(labels)
      [].

  Lemma eids_spec ex:
    <<LABEL: forall eid, label eid ex <> None <-> List.In eid (eids ex)>> /\
    <<NODUP: List.NoDup (eids ex)>>.
  Proof.
    generalize (PositiveMap.elements_3w (labels ex)). intro NODUP.
    hexploit SetoidList.NoDupA_rev; eauto.
    { apply IdMap.eqk_equiv. }
    intro NODUP_REV. splits.
    - (* LABEL *)
      i. destruct eid. unfold label, eids. s.
      rewrite IdMap.fold_1, <- List.fold_left_rev_right, IdMap.elements_spec.
      rewrite SetoidList_findA_rev; eauto; cycle 1.
      { apply eq_equivalence. }
      { apply []. }
      revert NODUP_REV. induction (List.rev (IdMap.elements (labels ex))); ss.
      destruct a. i. inv NODUP_REV. s. rewrite List.in_app_iff, <- IHl; ss.
      match goal with
      | [|- context[if ?c then true else false]] => destruct c
      end; ss; i; cycle 1.
      { econs; eauto. i. des; ss.
        apply List.in_map_iff in H. des. inv H. congr.
      }
      inv e. rewrite List.nth_error_Some, List.in_map_iff.
      econs; i; des.
      + left. esplits; eauto. apply HahnList.in_seq0_iff. ss.
      + inv H. apply HahnList.in_seq0_iff. ss.
      + revert H.
        match goal with
        | [|- context[match ?f with Some _ => _ | None => _ end]] => destruct f eqn:FIND
        end; ss.
        apply SetoidList.findA_NoDupA in FIND; ss; cycle 1.
        { apply eq_equivalence. }
        exfalso. apply H1. revert FIND. clear. induction l; i; inv FIND.
        * destruct a. ss. des. inv H0. left. ss.
        * right. apply IHl. ss.
    - (* NODUP *)
      unfold eids. rewrite IdMap.fold_1, <- List.fold_left_rev_right.
      revert NODUP_REV. induction (List.rev (IdMap.elements (labels ex))); ss. i.
      inv NODUP_REV. destruct a. s.
      apply HahnList.nodup_app. splits; eauto.
      + apply FinFun.Injective_map_NoDup.
        * ii. inv H. ss.
        * apply List.seq_NoDup.
      + ii. apply List.in_map_iff in IN1. des. subst.
        apply H1. revert IN2. clear. induction l; ss.
        i. apply List.in_app_iff in IN2. des.
        * apply List.in_map_iff in IN2. des. inv IN2. left. ss.
        * right. eauto.
  Qed.

  Inductive label_is (ex:t) (pred:Label.t -> Prop) (eid:eidT): Prop :=
  | label_is_intro
      l
      (EID: label eid ex = Some l)
      (LABEL: pred l)
  .

  Inductive label_rel (ex:t) (rel:relation Label.t) (eid1 eid2:eidT): Prop :=
  | label_rel_intro
      l1 l2
      (EID1: label eid1 ex = Some l1)
      (EID2: label eid2 ex = Some l2)
      (LABEL: rel l1 l2)
  .

  Inductive label_loc (x y:Label.t): Prop :=
  | label_loc_intro
      loc
      (X: Label.is_accessing loc x)
      (Y: Label.is_accessing loc y)
  .

(* let obs = rfe | fr | co *)

(* let dob = *)
(* 	| (addr | data); rfi? *)
(* 	| (ctrl | (addr; po)); ([W] | [ISB]; po; [R]) *)

(* let aob = [range(rmw)]; rfi; [A | Q] *)

(* let bob = *)
(* 	| [R|W]; po; [dmb.full]; po; [R|W] *)
(* 	| [L]; po; [A] *)
(* 	| [R]; po; [dmb.ld]; po; [R|W] *)
(* 	| [A | Q]; po; [R|W] *)
(* 	| [W]; po; [dmb.st]; po; [W] *)
(* 	| [R|W]; po; [L] *)

(* let ob = obs | dob | aob | bob *)

(* acyclic po-loc | fr | co | rf as internal *)
(* acyclic ob as external *)
(* empty rmw & (fre; coe) as atomic *)

  Inductive po (eid1 eid2:eidT): Prop :=
  | po_intro
      (TID: eid1.(fst) = eid2.(fst))
      (N: eid1.(snd) < eid2.(snd))
  .
  Hint Constructors po.

  Global Program Instance po_trans: Transitive po.
  Next Obligation.
    ii. destruct x, y, z. inv H. inv H0. ss. subst. econs; ss. lia.
  Qed.

  Inductive po_adj (eid1 eid2:eidT): Prop :=
  | po_adj_intro
      (TID: eid1.(fst) = eid2.(fst))
      (N: eid2.(snd) = S eid1.(snd))
  .
  Hint Constructors po_adj.

  Lemma po_adj_po:
    po_adj ⊆ po.
  Proof.
    ii. destruct x, y. inv H. ss. subst. econs; ss.
  Qed.

  Lemma po_po_adj:
    po = po^? ⨾ po_adj.
  Proof.
    funext. i. funext. i. propext. econs; i.
    - inv H. destruct x, x0. ss. subst.
      destruct n0; [lia|].
      exists (t1, n0). splits; ss. inv N; [left|right]; eauto.
    - inv H. des. inv H0.
      + apply po_adj_po. ss.
      + etrans; eauto. apply po_adj_po. ss.
  Qed.

  Lemma po_po_adj_weak:
    (Execution.po ⨾ Execution.po_adj) ⊆ Execution.po.
  Proof.
    rewrite po_po_adj at 2. apply inclusion_seq_mon; ss.
    econs 2. ss.
  Qed.

  Inductive i (eid1 eid2:eidT): Prop :=
  | i_intro
      (TID: eid1.(fst) = eid2.(fst))
  .
  Hint Constructors i.

  Inductive e (eid1 eid2:eidT): Prop :=
  | e_intro
      (TID: eid1.(fst) <> eid2.(fst))
  .
  Hint Constructors e.

  Definition po_loc (ex:t): relation eidT := po ∩ ex.(label_rel) label_loc.
  Definition fr (ex:t): relation eidT := ex.(rf)⁻¹ ⨾ ex.(co).
  Definition rfi (ex:t): relation eidT := ex.(rf) ∩ i.
  Definition rfe (ex:t): relation eidT := ex.(rf) ∩ e.
  Definition fre (ex:t): relation eidT := ex.(fr) ∩ e.
  Definition coe (ex:t): relation eidT := ex.(co) ∩ e.

  Definition internal (ex:t): relation eidT := ex.(po_loc) ∪ ex.(fr) ∪ ex.(co) ∪ ex.(rf).

  Definition obs (ex:t): relation eidT := ex.(rfe) ∪ ex.(fr) ∪ ex.(co).

  Definition dob (ex:t): relation eidT :=
    ((ex.(addr) ∪ ex.(data)) ⨾ ex.(rfi)^?) ∪

    ((ex.(ctrl) ∪ (ex.(addr) ⨾ po)) ⨾
     (⦗ex.(label_is) Label.is_write⦘ ∪
      (⦗ex.(label_is) (eq (Label.barrier Barrier.isb))⦘ ⨾ po ⨾ ⦗ex.(label_is) Label.is_read⦘))).

  Definition aob (ex:t): relation eidT :=
    ⦗codom_rel ex.(rmw)⦘ ⨾ ex.(rfi) ⨾ ⦗ex.(label_is) Label.is_acquire_pc⦘.

  Definition bob (ex:t): relation eidT :=
    (po ⨾
     ⦗ex.(label_is) (eq (Label.barrier Barrier.dmbsy))⦘ ⨾
     po) ∪

    (⦗ex.(label_is) Label.is_release⦘ ⨾
     po ⨾
     ⦗ex.(label_is) Label.is_acquire⦘) ∪

    (⦗ex.(label_is) Label.is_read⦘ ⨾
     po ⨾
     ⦗ex.(label_is) (eq (Label.barrier Barrier.dmbld))⦘ ⨾
     po) ∪

    (⦗ex.(label_is) Label.is_acquire_pc⦘ ⨾
     po) ∪

    (⦗ex.(label_is) Label.is_write⦘ ⨾
     po ⨾
     ⦗ex.(label_is) (eq (Label.barrier Barrier.dmbst))⦘ ⨾
     po ⨾
     ⦗ex.(label_is) Label.is_write⦘) ∪

    (po ⨾
     ⦗ex.(label_is) Label.is_release⦘).

  Definition ob (ex:t): relation eidT :=
    ex.(obs) ∪ ex.(dob) ∪ ex.(aob) ∪ ex.(bob).
End Execution.

Inductive tid_lift (tid:Id.t) (rel:relation nat) (eid1 eid2:eidT): Prop :=
| tid_lift_intro
    (TID1: eid1.(fst) = tid)
    (TID1: eid2.(fst) = tid)
    (REL: rel eid1.(snd) eid2.(snd))
.
Hint Constructors tid_lift.

Lemma tid_lift_incl
      tid rel1 rel2
      (REL: rel1 ⊆ rel2):
  tid_lift tid rel1 ⊆ tid_lift tid rel2.
Proof.
  ii. inv H. econs; eauto.
Qed.

Inductive tid_join (rels: IdMap.t (relation nat)) (eid1 eid2:eidT): Prop :=
| tid_join_intro
    tid rel
    (RELS: IdMap.find tid rels = Some rel)
    (REL: tid_lift tid rel eid1 eid2)
.
Hint Constructors tid_join.

Module Valid.
  Inductive pre_ex (p:program) (ex:Execution.t) := mk_pre_ex {
    locals: IdMap.t ALocal.t;

    LOCALS: IdMap.Forall2
              (fun stmts local =>
                 exists state,
                   <<STEP: rtc AExecUnit.step
                               (AExecUnit.mk (State.init stmts) ALocal.init)
                               (AExecUnit.mk state local)>> /\
                   <<TERMINAL: State.is_terminal state>>)
              p locals;
    LABELS: ex.(Execution.labels) = IdMap.map (fun local => local.(ALocal.labels)) locals;
    ADDR: ex.(Execution.addr) = tid_join (IdMap.map (fun local => local.(ALocal.addr)) locals);
    DATA: ex.(Execution.data) = tid_join (IdMap.map (fun local => local.(ALocal.data)) locals);
    CTRL: ex.(Execution.ctrl) = tid_join (IdMap.map (fun local => local.(ALocal.ctrl)) locals);
    RMW: ex.(Execution.rmw) = tid_join (IdMap.map (fun local => local.(ALocal.rmw)) locals);
  }.
  Hint Constructors pre_ex.

  Inductive ex (p:program) (ex:Execution.t) := mk_ex {
    PRE: pre_ex p ex;
    CO: forall eid1 eid2,
        (exists loc
           ex1 ord1 val1
           ex2 ord2 val2,
            <<LABEL: Execution.label eid1 ex = Some (Label.write ex1 ord1 loc val1)>> /\
            <<LABEL: Execution.label eid2 ex = Some (Label.write ex2 ord2 loc val2)>>) <->
        (eid1 = eid2 \/ ex.(Execution.co) eid1 eid2 \/ ex.(Execution.co) eid2 eid1);
    RF: forall eid1 loc val,
        (exists ex1 ord1,
            <<LABEL: Execution.label eid1 ex = Some (Label.read ex1 ord1 loc val)>>) <->
        (exists eid2 ex2 ord2,
            <<LABEL: Execution.label eid2 ex = Some (Label.write ex2 ord2 loc val)>> /\
            <<RF: ex.(Execution.rf) eid2 eid1>>);
    INTERNAL: acyclic ex.(Execution.internal);
    EXTERNAL: acyclic ex.(Execution.ob);
    ATOMIC: ex.(Execution.rmw) ∩ (ex.(Execution.fre) ⨾ ex.(Execution.coe)) = bot;
  }.
  Hint Constructors ex.
  Coercion PRE: ex >-> pre_ex.

  Lemma inclusion_po
        p exec (EX: ex p exec):
    <<ADDR: exec.(Execution.addr) ⊆ Execution.po>> /\
    <<DATA: exec.(Execution.data) ⊆ Execution.po>> /\
    <<CTRL: exec.(Execution.ctrl) ⊆ Execution.po>>.
  Proof.
    rewrite EX.(ADDR), EX.(DATA), EX.(CTRL). splits.
    - ii. inv H. inv REL. destruct x, y. ss. subst. rewrite IdMap.map_spec in RELS.
      destruct (IdMap.find t (locals EX)) eqn:LOCAL; ss. inv RELS.
      generalize (EX.(LOCALS) t). rewrite LOCAL. intro X. inv X. des.
      exploit AExecUnit.rtc_step_future; eauto.
      { apply AExecUnit.wf_init. }
      s. i. des. econs; ss.
      inv WF. apply ADDR0. ss.
    - ii. inv H. inv REL. destruct x, y. ss. subst. rewrite IdMap.map_spec in RELS.
      destruct (IdMap.find t (locals EX)) eqn:LOCAL; ss. inv RELS.
      generalize (EX.(LOCALS) t). rewrite LOCAL. intro X. inv X. des.
      exploit AExecUnit.rtc_step_future; eauto.
      { apply AExecUnit.wf_init. }
      s. i. des. econs; ss.
      inv WF. apply DATA0. ss.
    - ii. inv H. inv REL. destruct x, y. ss. subst. rewrite IdMap.map_spec in RELS.
      destruct (IdMap.find t (locals EX)) eqn:LOCAL; ss. inv RELS.
      generalize (EX.(LOCALS) t). rewrite LOCAL. intro X. inv X. des.
      exploit AExecUnit.rtc_step_future; eauto.
      { apply AExecUnit.wf_init. }
      s. i. des. econs; ss.
      inv WF. apply CTRL0. ss.
  Qed.

  Lemma ctrl_po
        p exec (EX: ex p exec):
    exec.(Execution.ctrl) ⨾ Execution.po ⊆ exec.(Execution.ctrl).
  Proof.
    ii. inv H. des. destruct x, y, x0.
    rewrite EX.(CTRL) in *. des. ss. subst.
    inv H0. rewrite IdMap.map_spec in RELS.
    destruct (IdMap.find tid (locals EX)) eqn:LOCAL; ss. inv RELS.
    generalize (EX.(LOCALS) tid). rewrite LOCAL. intro X. inv X. des.
    inv REL. ss. subst.
    exploit AExecUnit.rtc_step_future; eauto.
    { apply AExecUnit.wf_init. }
    s. i. des. econs.
    - rewrite IdMap.map_spec, LOCAL. ss.
    - inv H1. ss. subst. econs; ss.
      inv WF. apply CTRL_MON. econs; eauto.
  Qed.

  Lemma cap_po_adj
        p exec (EX: ex p exec):
    (exec.(Execution.ctrl) ∪ exec.(Execution.addr) ⨾ Execution.po) ⨾ Execution.po_adj ⊆ (exec.(Execution.ctrl) ∪ exec.(Execution.addr) ⨾ Execution.po).
  Proof.
    ii. inv H.
    - des. inv H0.
      + left. apply EX.(Valid.ctrl_po). econs. splits; eauto. apply Execution.po_adj_po. ss.
      + right. inv H. des. econs. splits; eauto. etrans; eauto. apply Execution.po_adj_po. ss.
  Qed.

  Lemma write_ex_codom_rmw
        p exec eid
        (EX: ex p exec)
        (WRITE: exec.(Execution.label_is) (fun l => Label.is_write l /\ Label.is_ex l) eid):
    codom_rel exec.(Execution.rmw) eid.
  Proof.
    destruct eid as [tid n]. rewrite EX.(RMW).
    inv WRITE. des. destruct l; ss. destruct ex0; ss. revert EID. unfold Execution.label.
    rewrite EX.(LABELS), IdMap.map_spec. s.
    destruct (IdMap.find tid (locals EX)) eqn:LOCAL; ss. i.
    generalize (EX.(LOCALS) tid). rewrite LOCAL. intro X. inv X. des.
    exploit AExecUnit.rtc_step_future; eauto.
    { apply AExecUnit.wf_init. }
    s. i. des. inv WF. exploit RMW0; eauto. intro X. inv X. ss.
    econs. econs.
    - rewrite IdMap.map_spec, LOCAL. ss.
    - instantiate (1 := (_, _)). econs; ss; eauto.
  Qed.
End Valid.

Coercion Valid.PRE: Valid.ex >-> Valid.pre_ex.
