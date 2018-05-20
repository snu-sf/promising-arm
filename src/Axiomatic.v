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

  (* TODO: define AcquirePC ordering *)
  Definition is_acquire_pc (label:t): bool :=
    match label with
    | read _ ord _ _ => ord_le ra ord
    | _ => false
    end.

  Definition is_acquire (label:t): bool :=
    match label with
    | read _ ord _ _ => ord_le ra ord
    | _ => false
    end.

  Definition is_release (label:t): bool :=
    match label with
    | write _ ord _ _ => ord_le ra ord
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
End Label.

Module ALocal.
  Inductive t := mk {
    labels: list Label.t;
    addr: relation nat;
    data: relation nat;
    ctrl: relation nat;
  }.
  Hint Constructors t.

  Definition init: t := mk [] bot bot bot.

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
                 (alocal1.(ctrl) ∪ (ctrl_e × (le (next_eid alocal1)))))
  | step_read
      ex ord vloc res
      (EVENT: event = Event.read ex ord vloc (ValA.mk _ res (eq (next_eid alocal1))))
      (ALOCAL: alocal2 =
               mk
                 (alocal1.(labels) ++ [Label.read ex ord vloc.(ValA.val) res])
                 (alocal1.(addr) ∪ (vloc.(ValA.annot) × (eq (next_eid alocal1))))
                 alocal1.(data)
                 alocal1.(ctrl))
  | step_write
      ex ord vloc vval
      (EVENT: event = Event.write ex ord vloc vval (ValA.mk _ 0 (eq (next_eid alocal1))))
      (ALOCAL: alocal2 =
               mk
                 (alocal1.(labels) ++ [Label.write ex ord vloc.(ValA.val) vval.(ValA.val)])
                 (alocal1.(addr) ∪ (vloc.(ValA.annot) × (eq (next_eid alocal1))))
                 (alocal1.(data) ∪ (vval.(ValA.annot) × (eq (next_eid alocal1))))
                 alocal1.(ctrl))
  | step_write_failure
      ord vloc vval
      (EVENT: event = Event.write true ord vloc vval (ValA.mk _ 1 bot))
      (ALOCAL: alocal2 =
               mk
                 alocal1.(labels)
                 alocal1.(addr)
                 alocal1.(data)
                 alocal1.(ctrl))
  | step_barrier
      b
      (EVENT: event = Event.barrier b)
      (ALOCAL: alocal2 =
               mk
                 (alocal1.(labels) ++ [Label.barrier b])
                 alocal1.(addr)
                 alocal1.(data)
                 alocal1.(ctrl))
  .
  Hint Constructors step.

  Inductive future (alocal1 alocal2:t): Prop :=
  | future_intro
      (LABELS: exists l, alocal2.(labels) = alocal1.(labels) ++ l)
      (ADDR: alocal1.(addr) ⊆ alocal2.(addr))
      (DATA: alocal1.(data) ⊆ alocal2.(data))
      (CTRL: alocal1.(ctrl) ⊆ alocal2.(ctrl))
  .

  Global Program Instance future_preorder: PreOrder future.
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

  Lemma step_future e:
    step e <2= future.
  Proof.
    i. inv PR; econs; ss.
    all: try by eexists; eauto.
    all: try by exists []; rewrite List.app_nil_r.
    all: try by apply inclusion_union_r1.
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

  Lemma step_future
        eu1 eu2
        (STEP: step eu1 eu2):
    ALocal.future eu1.(local) eu2.(local).
  Proof.
    inv STEP. eapply ALocal.step_future. eauto.
  Qed.

  Lemma rtc_step_future
        eu1 eu2
        (STEP: rtc step eu1 eu2):
    ALocal.future eu1.(local) eu2.(local).
  Proof.
    induction STEP; eauto.
    - refl.
    - etrans; eauto. apply step_future. ss.
  Qed.
End AExecUnit.

Definition eidT := (Id.t * nat)%type.

Module Execution.
  Inductive t := mk {
    labels: IdMap.t (list Label.t);
    po: relation eidT;
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

  (* TODO: move *)
  Lemma SetoidList_findA_rev
        (A B : Type) (eqA : A -> A -> Prop)
        (EQUIV: Equivalence eqA)
        (eqA_dec : forall x y : A, {eqA x y} + {~ eqA x y})
        (l : list (A * B)) 
        (a : A) (b : B)
        (NODUP: SetoidList.NoDupA (fun p p' : A * B => eqA (fst p) (fst p')) l):
    SetoidList.findA (fun a' : A => if eqA_dec a a' then true else false) l =
    SetoidList.findA (fun a' : A => if eqA_dec a a' then true else false) (List.rev l).
  Proof.
    hexploit SetoidList.NoDupA_rev; try exact NODUP; [|i].
    { econs; ii.
      - refl.
      - symmetry. ss.
      - etrans; eauto.
    }

    match goal with
    | [|- ?f = _] => destruct f eqn:FIND
    end.
    { rewrite <- SetoidList.findA_NoDupA in FIND; ss.
      rewrite <- SetoidList.InA_rev in FIND.
      rewrite SetoidList.findA_NoDupA in FIND; ss.
      eauto.
    }

    match goal with
    | [|- _ = ?f] => destruct f eqn:FIND'
    end.
    { rewrite <- SetoidList.findA_NoDupA in FIND'; ss.
      rewrite SetoidList.InA_rev in FIND'.
      rewrite SetoidList.findA_NoDupA in FIND'; ss.
      rewrite FIND' in FIND. congr.
    }

    ss.
  Qed.

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

  Definition i: relation eidT :=
    fun x y => x.(fst) = y.(fst).

  Definition e: relation eidT :=
    fun x y => x.(fst) <> y.(fst).

  Definition po_loc (ex:t): relation eidT := ex.(label_rel) label_loc.
  Definition fr (ex:t): relation eidT := ex.(rf)⁻¹ ⨾ ex.(co).
  Definition rfi (ex:t): relation eidT := ex.(rf) ∩ i.
  Definition rfe (ex:t): relation eidT := ex.(rf) ∩ e.
  Definition fre (ex:t): relation eidT := ex.(fr) ∩ e.
  Definition coe (ex:t): relation eidT := ex.(co) ∩ e.

  Definition internal (ex:t): relation eidT := ex.(po_loc) ∪ ex.(fr) ∪ ex.(co) ∪ ex.(rf).

  Definition obs (ex:t): relation eidT := ex.(rfe) ∪ ex.(fr) ∪ ex.(co).

  Definition dob (ex:t): relation eidT :=
    ((ex.(addr) ∪ ex.(data)) ⨾ ex.(rfi)^?) ∪

    ((ex.(ctrl) ∪ (ex.(addr) ⨾ ex.(po))) ⨾
     (⦗ex.(label_is) Label.is_write⦘ ∪
      (⦗ex.(label_is) (eq (Label.barrier Barrier.isb))⦘ ⨾ ex.(po) ⨾ ⦗ex.(label_is) Label.is_read⦘))).

  Definition aob (ex:t): relation eidT :=
    ⦗codom_rel ex.(rmw)⦘ ⨾ ex.(rfi) ⨾ ⦗ex.(label_is) Label.is_acquire_pc⦘.

  Definition bob (ex:t): relation eidT :=
    (⦗ex.(label_is) Label.is_read \1/ ex.(label_is) Label.is_write⦘ ⨾
     ex.(po) ⨾
     ⦗ex.(label_is) (eq (Label.barrier Barrier.dmbsy))⦘ ⨾
     ex.(po) ⨾
     ⦗ex.(label_is) Label.is_read \1/ ex.(label_is) Label.is_write⦘) ∪

    (⦗ex.(label_is) Label.is_release⦘ ⨾
     ex.(po) ⨾
     ⦗ex.(label_is) Label.is_acquire⦘) ∪

    (⦗ex.(label_is) Label.is_read⦘ ⨾
     ex.(po) ⨾
     ⦗ex.(label_is) (eq (Label.barrier Barrier.dmbld))⦘ ⨾
     ex.(po) ⨾
     ⦗ex.(label_is) Label.is_read \1/ ex.(label_is) Label.is_write⦘) ∪

    (⦗ex.(label_is) Label.is_acquire_pc⦘ ⨾
     ex.(po) ⨾
     ⦗ex.(label_is) Label.is_read \1/ ex.(label_is) Label.is_write⦘) ∪

    (⦗ex.(label_is) Label.is_write⦘ ⨾
     ex.(po) ⨾
     ⦗ex.(label_is) (eq (Label.barrier Barrier.dmbst))⦘ ⨾
     ex.(po) ⨾
     ⦗ex.(label_is) Label.is_write⦘) ∪

    (⦗ex.(label_is) Label.is_read \1/ ex.(label_is) Label.is_write⦘ ⨾
     ex.(po) ⨾
     ⦗ex.(label_is) Label.is_release⦘).

  Definition ob (ex:t): relation eidT :=
    ex.(obs) ∪ ex.(dob) ∪ ex.(aob) ∪ ex.(bob).
End Execution.

Inductive tid_join (rels: IdMap.t (relation nat)) (eid1 eid2:eidT): Prop :=
| tid_join_intro
    tid rel
    (TID1: eid1.(fst) = tid)
    (TID2: eid2.(fst) = tid)
    (RELS: IdMap.find tid rels = Some rel)
    (REL: rel eid1.(snd) eid2.(snd))
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
    PO: ex.(Execution.po) = (fun eid1 eid2 => eid1.(fst) = eid2.(fst) /\ eid1.(snd) < eid2.(snd));
    ADDR: ex.(Execution.addr) = tid_join (IdMap.map (fun local => local.(ALocal.addr)) locals);
    DATA: ex.(Execution.data) = tid_join (IdMap.map (fun local => local.(ALocal.data)) locals);
    CTRL: ex.(Execution.ctrl) = tid_join (IdMap.map (fun local => local.(ALocal.ctrl)) locals);
    RMW: forall eid1 ord1 loc val1
           (LABEL1: Execution.label eid1 ex = Some (Label.write true ord1 loc val1)),
        exists eid2 ord2 val2,
          <<LABEL: Execution.label eid2 ex = Some (Label.read true ord2 loc val2)>> /\
          <<PO: ex.(Execution.po) eid2 eid1>> /\
          <<RMW: ex.(Execution.rmw) eid2 eid1>> /\
          <<BTW: forall eid3 label3
                   (PO23: ex.(Execution.po) eid2 eid3)
                   (PO31: ex.(Execution.po) eid3 eid1)
                   (LABEL3: Execution.label eid3 ex = Some label3),
              Label.is_ex label3 = false>>;
  }.
  Hint Constructors pre_ex.

  Inductive ex (p:program) (ex:Execution.t) := mk_ex {
    PRE: pre_ex p ex;
    CO: forall loc
          eid1 ex1 ord1 val1
          eid2 ex2 ord2 val2
          (EID: eid1 <> eid2)
          (LABEL1: Execution.label eid1 ex = Some (Label.write ex1 ord1 loc val1))
          (LABEL2: Execution.label eid2 ex = Some (Label.write ex2 ord2 loc val2)),
        ex.(Execution.co) eid1 eid2 \/ ex.(Execution.co) eid2 eid1;
    RF: forall eid1 ex1 ord1 loc val
          (LABEL1: Execution.label eid1 ex = Some (Label.read ex1 ord1 loc val)),
        exists eid2 ex2 ord2,
          <<LABEL: Execution.label eid2 ex = Some (Label.write ex2 ord2 loc val)>> /\
          <<RF: ex.(Execution.rf) eid2 eid1>>;
    INTERNAL: acyclic ex.(Execution.internal);
    EXTERNAL: acyclic ex.(Execution.ob);
    ATOMIC: le (ex.(Execution.rmw) ∩ (ex.(Execution.fre) ⨾ ex.(Execution.coe))) bot;
  }.
  Hint Constructors ex.
End Valid.

Coercion Valid.PRE: Valid.ex >-> Valid.pre_ex.
