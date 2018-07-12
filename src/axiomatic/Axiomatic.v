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
Require Import HahnSets.

Require Import PromisingArch.lib.Basic.
Require Import PromisingArch.lib.HahnRelationsMore.
Require Import PromisingArch.lib.Order.
Require Import PromisingArch.lib.Time.
Require Import PromisingArch.lib.Lang.

Set Implicit Arguments.


Module Label.
  Inductive t :=
  | read (ex:bool) (ord:OrdR.t) (loc:Loc.t) (val:Val.t)
  | write (ex:bool) (ord:OrdW.t) (loc:Loc.t) (val:Val.t)
  | barrier (b:Barrier.t)
  | ctrl
  .
  Hint Constructors t.

  Definition is_ex (label:t): bool :=
    match label with
    | read ex _ _ _ => ex
    | write ex _ _ _ => ex
    | _ => false
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

  Definition is_acquire_pc (label:t): bool :=
    match label with
    | read _ ord _ _ => OrdR.ge ord OrdR.acquire_pc
    | _ => false
    end.

  Definition is_acquire (label:t): bool :=
    match label with
    | read _ ord _ _ => OrdR.ge ord OrdR.acquire
    | _ => false
    end.

  Definition is_release (label:t): bool :=
    match label with
    | write _ ord _ _ => OrdW.ge ord OrdW.release
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

  Definition is_access (label:t): bool :=
    match label with
    | read _ _ _ _ => true
    | write _ _ _ _ => true
    | _ => false
    end.

  Definition is_accessing (loc:Loc.t) (label:t): bool :=
    match label with
    | read _ _ loc' _ => loc' == loc
    | write _ _ loc' _ => loc' == loc
    | _ => false
    end.

  Definition is_ctrl (label:t): bool :=
    match label with
    | ctrl => true
    | _ => false
    end.

  Definition is_barrier (label:t): bool :=
    match label with
    | barrier b => true
    | _ => false
    end.

  Definition is_barrier_c (c:Barrier.t -> bool) (label:t): bool :=
    match label with
    | barrier b => c b
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
        (READING: is_reading loc l):
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
      (EVENT: event = Event.internal)
      (ALOCAL: alocal2 =
               mk
                 alocal1.(labels)
                 alocal1.(addr)
                 alocal1.(data)
                 alocal1.(ctrl)
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
      (EVENT: event = Event.write ex ord vloc vval (ValA.mk _ 0 (ifc (ex && (arch == riscv)) (eq (next_eid alocal1)))))
      (EX: ex -> exists n,
           alocal1.(exbank) = Some n /\
           opt_pred (fun l => Label.is_read l /\ Label.is_ex l) (List.nth_error alocal1.(labels) n))
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
  | step_control
      ctrl_e
      (EVENT: event = (Event.control ctrl_e))
      (ALOCAL: alocal2 =
               mk
                 (alocal1.(labels) ++ [Label.ctrl])
                 alocal1.(addr)
                 alocal1.(data)
                 (alocal1.(ctrl) ∪ (ctrl_e × (eq (next_eid alocal1))))
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
  Hint Constructors le.

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
  Hint Constructors step.

  Inductive label_is (labels:list Label.t) (pred:Label.t -> Prop) (iid:nat): Prop :=
  | label_is_intro
      l
      (EID: List.nth_error labels iid = Some l)
      (LABEL: pred l)
  .
  Hint Constructors label_is.

  Definition wf_rmap (rmap: RMap.t (A:=nat -> Prop)) (labels:list Label.t): Prop :=
    forall r n
      (N: (RMap.find r rmap).(ValA.annot) n),
      label_is labels Label.is_access n.
  Hint Unfold wf_rmap.

  Lemma wf_rmap_expr
        rmap labels e n
        (WF: wf_rmap rmap labels)
        (N: (sem_expr rmap e).(ValA.annot) n):
    label_is labels Label.is_access n.
  Proof.
    revert n N. induction e; ss.
    - i. eapply WF. eauto.
    - i. inv N; eauto.
  Qed.

  Inductive wf (aeu:t): Prop :=
  | wf_intro
      (REG: wf_rmap aeu.(state).(State.rmap) aeu.(local).(ALocal.labels))
      (ADDR: aeu.(local).(ALocal.addr) ⊆ lt)
      (ADDR_LIMIT: forall e1 e2 (REL: aeu.(local).(ALocal.addr) e1 e2), e2 < List.length aeu.(local).(ALocal.labels))
      (ADDR_LABEL: aeu.(local).(ALocal.addr) ⊆ (label_is aeu.(local).(ALocal.labels) Label.is_access) × (label_is aeu.(local).(ALocal.labels) Label.is_access))
      (DATA: aeu.(local).(ALocal.data) ⊆ lt)
      (DATA_LIMIT: forall e1 e2 (REL: aeu.(local).(ALocal.data) e1 e2), e2 < List.length aeu.(local).(ALocal.labels))
      (DATA_LABEL: aeu.(local).(ALocal.data) ⊆ (label_is aeu.(local).(ALocal.labels) Label.is_access) × (label_is aeu.(local).(ALocal.labels) Label.is_write))
      (CTRL: aeu.(local).(ALocal.ctrl) ⊆ lt)
      (CTRL_LIMIT: forall e1 e2 (REL: aeu.(local).(ALocal.ctrl) e1 e2), e2 < List.length aeu.(local).(ALocal.labels))
      (CTRL_LABEL: aeu.(local).(ALocal.ctrl) ⊆ (label_is aeu.(local).(ALocal.labels) Label.is_access) × (label_is aeu.(local).(ALocal.labels) Label.is_ctrl))
      (RMW: aeu.(local).(ALocal.rmw) ⊆ lt)
      (RMW_LIMIT: forall e1 e2 (REL: aeu.(local).(ALocal.rmw) e1 e2), e2 < List.length aeu.(local).(ALocal.labels))
      (RMW1: forall n ord loc val
               (LABEL: List.nth_error aeu.(local).(ALocal.labels) n = Some (Label.write true ord loc val)),
          codom_rel aeu.(local).(ALocal.rmw) n)
      (RMW2: forall a b
               (RMW: aeu.(local).(ALocal.rmw) a b),
          exists ord1 loc1 val1 ord2 loc2 val2,
            <<LABEL1: List.nth_error aeu.(local).(ALocal.labels) a = Some (Label.read true ord1 loc1 val1)>> /\
            <<LABEL2: List.nth_error aeu.(local).(ALocal.labels) b = Some (Label.write true ord2 loc2 val2)>> /\
            <<BETWEEN: forall c ord3 loc3 val3 (C: a < c < b), List.nth_error aeu.(local).(ALocal.labels) c <> Some (Label.read true ord3 loc3 val3)>>)
      (EXBANK': forall eb (EB: aeu.(local).(ALocal.exbank) = Some eb),
          eb < List.length aeu.(local).(ALocal.labels))
      (EXBANK: forall eb c ord3 loc3 val3
                 (EB: aeu.(local).(ALocal.exbank) = Some eb)
                 (C: eb < c),
          List.nth_error aeu.(local).(ALocal.labels) c <> Some (Label.read true ord3 loc3 val3))
  .
  Hint Constructors wf.

  Lemma label_is_lt
        labels pred iid
        (LABEL: label_is labels pred iid):
    iid < length labels.
  Proof.
    inv LABEL. apply List.nth_error_Some. congr.
  Qed.

  Lemma label_is_mon
        labels1 labels2 pred:
    label_is labels1 pred <1= label_is (labels1 ++ labels2) pred.
  Proof.
    ii. inv PR. econs; eauto.
    rewrite List.nth_error_app1; ss.
    apply List.nth_error_Some. congr.
  Qed.

  Lemma union_mon
        A
        (p1 p2 q1 q2: A -> Prop)
        (P: p1 <1= p2)
        (Q: q1 <1= q2):
    (p1 ∪₁ q1) <1= (p2 ∪₁ q2).
  Proof.
    ii. inv PR.
    - left. eauto.
    - right. eauto.
  Qed.

  Lemma times_mon
        A
        (p1 p2 q1 q2: A -> Prop)
        (P: p1 <1= p2)
        (Q: q1 <1= q2):
    p1 × q1 <2= p2 × q2.
  Proof.
    ii. inv PR. econs; eauto.
  Qed.

  Lemma wf_init stmts: wf (mk (State.init stmts) ALocal.init).
  Proof.
    econs; ss.
    - ii. unfold RMap.find, RMap.init in *. rewrite IdMap.gempty in *. inv N.
    - i. destruct n; ss.
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
      + inv WF. econs; ss.
      + destruct local1. refl.
    - splits.
      + inv WF. econs; ss.
        ii. revert N. unfold RMap.find, RMap.add. rewrite IdMap.add_spec. condtac; eauto.
        inversion e. subst. apply wf_rmap_expr. ss.
      + destruct local1. refl.
    - splits.
      + inv WF. econs; ss.
        all: try rewrite List.app_length; s.
        all: unfold ALocal.next_eid in *.
        * ii. revert N. unfold RMap.find, RMap.add. rewrite IdMap.add_spec. condtac.
          { inversion e. subst. i. inv N.
            econs.
            - unfold ALocal.next_eid. rewrite List.nth_error_app2, Nat.sub_diag; ss.
            - ss.
          }
          { i. apply label_is_mon. exploit REG; eauto. }
        * ii. inv H.
          { exploit ADDR_LIMIT; eauto. }
          { inv H0. splits; eauto using label_is_lt, wf_rmap_expr. }
        * i. inv REL.
          { exploit ADDR_LIMIT; eauto. lia. }
          { inv H. lia. }
        * ii. inv H.
          { eapply times_mon; [| |by apply ADDR_LABEL].
            - apply label_is_mon.
            - i. apply label_is_mon. ss.
          }
          { inv H0. econs.
            - apply label_is_mon. eapply wf_rmap_expr; eauto.
            - econs.
              + unfold ALocal.next_eid. rewrite List.nth_error_app2, Nat.sub_diag; ss.
              + ss.
          }
        * ii. exploit DATA_LIMIT; eauto. lia.
        * ii. eapply times_mon; [| |by apply DATA_LABEL].
          { apply label_is_mon. }
          { apply label_is_mon. }
        * ii. exploit CTRL_LIMIT; eauto. lia.
        * ii. econs; ss.
          { apply label_is_mon. eapply CTRL_LABEL. eauto. }
          { apply label_is_mon. eapply CTRL_LABEL. eauto. }
        * ii. exploit RMW_LIMIT; eauto. lia.
        * i. apply nth_error_snoc_inv in LABEL. des; ss.
          eapply RMW1. eauto.
        * i. exploit RMW2; eauto. i. des. esplits; eauto using nth_error_app_mon.
          i. rewrite List.nth_error_app1; eauto. etrans; [apply C|]. apply List.nth_error_Some. congr.
        * i. destruct ex0; ss.
          { inv EB. lia. }
          { exploit EXBANK'; eauto. lia. }
        * ii. apply nth_error_snoc_inv in H. des; ss.
          { destruct ex0.
            { inv EB. unfold ALocal.next_eid in *. lia. }
            eapply EXBANK; eauto.
          }
          { subst. inv H0. inv EB. unfold ALocal.next_eid in *. lia. }
      + econs; ss.
        * esplits; eauto.
        * left. ss.
    - splits.
      + inv WF. econs; ss.
        all: try rewrite List.app_length; s.
        all: unfold ALocal.next_eid in *.
        * ii. revert N. unfold RMap.find, RMap.add. rewrite IdMap.add_spec. condtac.
          { inversion e. subst. s. unfold ifc. condtac; ss. i. subst. econs.
            - unfold ALocal.next_eid. rewrite List.nth_error_app2, Nat.sub_diag; ss.
            - ss.
          }
          { i. apply label_is_mon. exploit REG; eauto. }
        * ii. inv H.
          { exploit ADDR_LIMIT; eauto. }
          { inv H0. splits; eauto using label_is_lt, wf_rmap_expr. }
        * i. inv REL.
          { exploit ADDR_LIMIT; eauto. lia. }
          { inv H. lia. }
        * ii. inv H.
          { eapply times_mon; [| |by apply ADDR_LABEL].
            - apply label_is_mon.
            - apply label_is_mon.
          }
          { inv H0. econs.
            - apply label_is_mon. eapply wf_rmap_expr; eauto.
            - econs.
              + unfold ALocal.next_eid. rewrite List.nth_error_app2, Nat.sub_diag; ss.
              + ss.
          }
        * ii. inv H.
          { exploit DATA_LIMIT; eauto. }
          { inv H0. splits; eauto using label_is_lt, wf_rmap_expr. }
        * i. inv REL.
          { exploit DATA_LIMIT; eauto. lia. }
          { inv H. lia. }
        * ii. inv H.
          { eapply times_mon; [| |by apply DATA_LABEL].
            - apply label_is_mon.
            - apply label_is_mon.
          }
          { inv H0. econs.
            - apply label_is_mon. eapply wf_rmap_expr; eauto.
            - econs.
              + unfold ALocal.next_eid. rewrite List.nth_error_app2, Nat.sub_diag; ss.
              + ss.
          }
        * i. exploit CTRL_LIMIT; eauto. lia.
        * ii. econs; ss.
          { apply label_is_mon. eapply CTRL_LABEL. eauto. }
          { apply label_is_mon. eapply CTRL_LABEL. eauto. }
        * ii. inv H.
          { exploit RMW_LIMIT; eauto. }
          { destruct ex0; ss. inv H0. splits; eauto using label_is_lt, wf_rmap_expr. }
        * i. inv REL.
          { exploit RMW_LIMIT; eauto. lia. }
          { destruct ex0; ss. inv H. lia. }
        * i. apply nth_error_snoc_inv in LABEL. des.
          { exploit RMW1; eauto. i. inv x. econs. left. eauto. }
          { subst. inv LABEL0. exploit EX; eauto. i. des. econs. right. econs; eauto. }
        * i. inv RMW0.
          { exploit RMW2; eauto. i. des. esplits.
            - apply nth_error_app_mon. eauto.
            - apply nth_error_app_mon. eauto.
            - i. rewrite List.nth_error_app1; eauto. etrans; [apply C|]. apply List.nth_error_Some. congr.
          }
          { destruct ex0; ss. inv H. exploit EX; eauto. i. des. inv x0. des.
            destruct a0; ss. destruct ex; ss.
            rewrite H0 in x. inv x. symmetry in H1.
            esplits.
            - apply nth_error_app_mon. eauto.
            - rewrite List.nth_error_app2, Nat.sub_diag; ss.
            - ii. apply nth_error_snoc_inv in H. des.
              + eapply EXBANK; eauto.
              + unfold ALocal.next_eid in *. lia.
          }
        * i. destruct ex0; ss. exploit EXBANK'; eauto. lia.
        * ii. destruct ex0; ss. apply nth_error_snoc_inv in H. des; ss.
          eapply EXBANK; eauto.
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
        all: try rewrite List.app_length; s.
        all: unfold ALocal.next_eid in *.
        * ii. apply label_is_mon. exploit REG; eauto.
        * i. exploit ADDR_LIMIT; eauto. lia.
        * ii. eapply times_mon; [| |by apply ADDR_LABEL].
          { apply label_is_mon. }
          { apply label_is_mon. }
        * i. exploit DATA_LIMIT; eauto. lia.
        * ii. eapply times_mon; [| |by apply DATA_LABEL].
          { apply label_is_mon. }
          { apply label_is_mon. }
        * i. exploit CTRL_LIMIT; eauto. lia.
        * ii. econs; ss.
          { apply label_is_mon. eapply CTRL_LABEL. eauto. }
          { apply label_is_mon. eapply CTRL_LABEL. eauto. }
        * i. exploit RMW_LIMIT; eauto. lia.
        * i. apply nth_error_snoc_inv in LABEL. des; eauto. inv LABEL0.
        * i. exploit RMW2; eauto. i. des. esplits.
          { apply nth_error_app_mon. eauto. }
          { apply nth_error_app_mon. eauto. }
          { i. rewrite List.nth_error_app1; eauto. etrans; [apply C|]. apply List.nth_error_Some. congr. }
        * i. exploit EXBANK'; eauto. lia.
        * ii. apply nth_error_snoc_inv in H. des; ss.
          eapply EXBANK; eauto.
      + econs; ss. eexists; eauto.
    - splits.
      + inv WF. econs; ss.
        all: try rewrite List.app_length; s.
        all: unfold ALocal.next_eid in *.
        * ii. apply label_is_mon. exploit REG; eauto.
        * i. exploit ADDR_LIMIT; eauto. lia.
        * ii. eapply times_mon; [| |by apply ADDR_LABEL].
          { apply label_is_mon. }
          { apply label_is_mon. }
        * i. exploit DATA_LIMIT; eauto. lia.
        * ii. eapply times_mon; [| |by apply DATA_LABEL].
          { apply label_is_mon. }
          { apply label_is_mon. }
        * ii. inv H.
          { exploit CTRL_LIMIT; eauto. }
          { inv H0. splits; eauto using label_is_lt, wf_rmap_expr. }
        * i. inv REL.
          { exploit CTRL_LIMIT; eauto. lia. }
          { inv H. lia. }
        * ii. inv H.
          { eapply times_mon; [| |by apply CTRL_LABEL].
            - apply label_is_mon.
            - apply label_is_mon.
          }
          { inv H0. econs.
            - apply label_is_mon. eapply wf_rmap_expr; eauto.
            - econs.
              + unfold ALocal.next_eid. rewrite List.nth_error_app2, Nat.sub_diag; ss.
              + ss.
          }
        * i. exploit RMW_LIMIT; eauto. lia.
        * i. apply nth_error_snoc_inv in LABEL. des; eauto. inv LABEL0.
        * i. exploit RMW2; eauto. i. des. esplits.
          { apply nth_error_app_mon. eauto. }
          { apply nth_error_app_mon. eauto. }
          { i. rewrite List.nth_error_app1; eauto. etrans; [apply C|]. apply List.nth_error_Some. congr. }
        * i. exploit EXBANK'; eauto. lia.
        * ii. apply nth_error_snoc_inv in H. des; ss.
          eapply EXBANK; eauto.
      + econs; ss; eauto. left. ss.
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
  Hint Constructors t.

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
  Hint Constructors label_is.

  Inductive label_rel (ex:t) (rel:relation Label.t) (eid1 eid2:eidT): Prop :=
  | label_rel_intro
      l1 l2
      (EID1: label eid1 ex = Some l1)
      (EID2: label eid2 ex = Some l2)
      (LABEL: rel l1 l2)
  .
  Hint Constructors label_rel.

  Inductive label_is_rel (ex: t) (pred: Label.t -> Prop) (eid1 eid2: eidT): Prop :=
  | label_is_rel_intro
      l1 l2
      (EID1: label eid1 ex = Some l1)
      (EID2: label eid2 ex = Some l2)
      (LABEL1: pred l1)
      (LABEL2: pred l2)
  .
  Hint Constructors label_is_rel.

  Inductive label_loc (x y:Label.t): Prop :=
  | label_loc_intro
      loc
      (X: Label.is_accessing loc x)
      (Y: Label.is_accessing loc y)
  .
  Hint Constructors label_loc.

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
  Definition fr (ex:t): relation eidT :=
    (ex.(rf)⁻¹ ⨾ ex.(co)) ∪
    ((ex.(label_rel) label_loc) ∩
     ((ex.(label_is) Label.is_read) \₁ codom_rel ex.(rf)) × (ex.(label_is) Label.is_write)).
  Definition rfi (ex:t): relation eidT := ex.(rf) ∩ i.
  Definition rfe (ex:t): relation eidT := ex.(rf) ∩ e.
  Definition fre (ex:t): relation eidT := ex.(fr) ∩ e.
  Definition coe (ex:t): relation eidT := ex.(co) ∩ e.

  Definition internal (ex:t): relation eidT := ex.(po_loc) ∪ ex.(fr) ∪ ex.(co) ∪ ex.(rf).

  Definition obs (ex:t): relation eidT := ex.(rfe) ∪ ex.(fr) ∪ ex.(co).

  Definition dob (ex:t): relation eidT :=
    ((ex.(addr) ∪ ex.(data)) ⨾ ex.(rfi)^?) ∪

    ((ex.(ctrl) ∪ ex.(addr)) ⨾ po ⨾
     (⦗ex.(label_is) Label.is_write⦘ ∪
      (⦗ex.(label_is) (eq (Label.barrier Barrier.isb))⦘ ⨾ po ⨾ ⦗ex.(label_is) Label.is_read⦘))).

  Definition aob (ex:t): relation eidT :=
    ⦗codom_rel ex.(rmw)⦘ ⨾ ex.(rfi) ⨾ ⦗fun eid => arch = riscv \/ ex.(label_is) Label.is_acquire_pc eid⦘.

  Definition bob (ex:t): relation eidT :=
    (⦗ex.(label_is) Label.is_read⦘ ⨾
     po ⨾
     ⦗ex.(label_is) (Label.is_barrier_c Barrier.is_dmb_rr)⦘ ⨾
     po ⨾
     ⦗ex.(label_is) Label.is_read⦘) ∪

    (⦗ex.(label_is) Label.is_read⦘ ⨾
     po ⨾
     ⦗ex.(label_is) (Label.is_barrier_c Barrier.is_dmb_rw)⦘ ⨾
     po ⨾
     ⦗ex.(label_is) Label.is_write⦘) ∪

    (⦗ex.(label_is) Label.is_write⦘ ⨾
     po ⨾
     ⦗ex.(label_is) (Label.is_barrier_c Barrier.is_dmb_wr)⦘ ⨾
     po ⨾
     ⦗ex.(label_is) Label.is_read⦘) ∪

    (⦗ex.(label_is) Label.is_write⦘ ⨾
     po ⨾
     ⦗ex.(label_is) (Label.is_barrier_c Barrier.is_dmb_ww)⦘ ⨾
     po ⨾
     ⦗ex.(label_is) Label.is_write⦘) ∪

    (⦗ex.(label_is) Label.is_release⦘ ⨾
     po ⨾
     ⦗ex.(label_is) Label.is_acquire⦘) ∪

    (⦗ex.(label_is) Label.is_acquire_pc⦘ ⨾
     po) ∪

    (po ⨾
     ⦗ex.(label_is) Label.is_release⦘) ∪

    (ifc (arch == riscv) ex.(rmw)).

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
    aeus: IdMap.t AExecUnit.t;

    AEUS: IdMap.Forall2
            (fun tid stmts aeu =>
               rtc AExecUnit.step
                   (AExecUnit.mk (State.init stmts) ALocal.init)
                   aeu)
            p aeus;
    LABELS: ex.(Execution.labels) = IdMap.map (fun aeu => aeu.(AExecUnit.local).(ALocal.labels)) aeus;
    ADDR: ex.(Execution.addr) = tid_join (IdMap.map (fun aeu => aeu.(AExecUnit.local).(ALocal.addr)) aeus);
    DATA: ex.(Execution.data) = tid_join (IdMap.map (fun aeu => aeu.(AExecUnit.local).(ALocal.data)) aeus);
    CTRL: ex.(Execution.ctrl) = tid_join (IdMap.map (fun aeu => aeu.(AExecUnit.local).(ALocal.ctrl)) aeus);
    RMW: ex.(Execution.rmw) = tid_join (IdMap.map (fun aeu => aeu.(AExecUnit.local).(ALocal.rmw)) aeus);
  }.
  Hint Constructors pre_ex.

  Definition co1 (ex: Execution.t) :=
    forall eid1 eid2,
      (exists loc
          ex1 ord1 val1
          ex2 ord2 val2,
          <<LABEL: Execution.label eid1 ex = Some (Label.write ex1 ord1 loc val1)>> /\
          <<LABEL: Execution.label eid2 ex = Some (Label.write ex2 ord2 loc val2)>>) ->
      (eid1 = eid2 \/ ex.(Execution.co) eid1 eid2 \/ ex.(Execution.co) eid2 eid1).

  Definition co2 (ex: Execution.t) :=
    forall eid1 eid2,
      ex.(Execution.co) eid1 eid2 ->
      exists loc
         ex1 ord1 val1
         ex2 ord2 val2,
        <<LABEL: Execution.label eid1 ex = Some (Label.write ex1 ord1 loc val1)>> /\
        <<LABEL: Execution.label eid2 ex = Some (Label.write ex2 ord2 loc val2)>>.

  Definition rf1 (ex: Execution.t) :=
    forall eid1 ex1 ord1 loc val
       (LABEL: Execution.label eid1 ex = Some (Label.read ex1 ord1 loc val)),
      (<<NORF: ~ codom_rel ex.(Execution.rf) eid1>> /\ <<VAL: val = Val.default>>) \/
      (exists eid2 ex2 ord2,
          <<LABEL: Execution.label eid2 ex = Some (Label.write ex2 ord2 loc val)>> /\
          <<RF: ex.(Execution.rf) eid2 eid1>>).

  Definition rf2 (ex: Execution.t) :=
    forall eid1 eid2 (RF: ex.(Execution.rf) eid2 eid1),
    exists ex1 ex2 ord1 ord2 loc val,
      <<READ: Execution.label eid1 ex = Some (Label.read ex1 ord1 loc val)>> /\
      <<WRITE: Execution.label eid2 ex = Some (Label.write ex2 ord2 loc val)>>.

  Definition rf_wf (ex: Execution.t) := functional (ex.(Execution.rf))⁻¹.

  Inductive ex (p:program) (ex:Execution.t) := mk_ex {
    PRE: pre_ex p ex;
    CO1: co1 ex;
    CO2: co2 ex;
    RF1: rf1 ex;
    RF2: rf2 ex;
    RF_WF: rf_wf ex;
    INTERNAL: acyclic ex.(Execution.internal);
    EXTERNAL: acyclic ex.(Execution.ob);
    ATOMIC: le (ex.(Execution.rmw) ∩ (ex.(Execution.fre) ⨾ ex.(Execution.coe))) bot;
  }.
  Hint Constructors ex.
  Coercion PRE: ex >-> pre_ex.

  Definition is_terminal
             p ex (EX: pre_ex p ex): Prop :=
    forall tid aeu (FIND: IdMap.find tid EX.(aeus) = Some aeu),
      State.is_terminal aeu.(AExecUnit.state).

  Lemma data_is_po
        p exec
        (EX: pre_ex p exec):
    exec.(Execution.data) ⊆ Execution.po.
  Proof.
    rewrite EX.(DATA).
    ii. inv H. inv REL. destruct x, y. ss. subst. rewrite IdMap.map_spec in RELS.
    destruct (IdMap.find t EX.(aeus)) eqn:LOCAL; ss. inv RELS.
    generalize (EX.(AEUS) t). rewrite LOCAL. intro X. inv X. des.
    exploit AExecUnit.rtc_step_future; eauto.
    { apply AExecUnit.wf_init. }
    s. i. des. econs; ss.
    inv WF. apply DATA0. ss.
  Qed.

  Lemma ctrl_is_po
        p exec
        (EX: pre_ex p exec):
    exec.(Execution.ctrl) ⊆ Execution.po.
  Proof.
    rewrite EX.(CTRL).
    ii. inv H. inv REL. destruct x, y. ss. subst. rewrite IdMap.map_spec in RELS.
    destruct (IdMap.find t EX.(aeus)) eqn:LOCAL; ss. inv RELS.
    generalize (EX.(AEUS) t). rewrite LOCAL. intro X. inv X. des.
    exploit AExecUnit.rtc_step_future; eauto.
    { apply AExecUnit.wf_init. }
    s. i. des. econs; ss.
    inv WF. apply CTRL0. ss.
  Qed.

  Lemma addr_is_po
        p exec
        (EX: pre_ex p exec):
    exec.(Execution.addr) ⊆ Execution.po.
  Proof.
    rewrite EX.(ADDR).
    ii. inv H. inv REL. destruct x, y. ss. subst. rewrite IdMap.map_spec in RELS.
    destruct (IdMap.find t EX.(aeus)) eqn:LOCAL; ss. inv RELS.
    generalize (EX.(AEUS) t). rewrite LOCAL. intro X. inv X. des.
    exploit AExecUnit.rtc_step_future; eauto.
    { apply AExecUnit.wf_init. }
    s. i. des. econs; ss.
    inv WF. apply ADDR0. ss.
  Qed.

  Lemma rmw_is_po
        p exec
        (EX: pre_ex p exec):
    exec.(Execution.rmw) ⊆ Execution.po.
  Proof.
    rewrite EX.(RMW).
    ii. inv H. inv REL. destruct x, y. ss. subst. rewrite IdMap.map_spec in RELS.
    destruct (IdMap.find t EX.(aeus)) eqn:LOCAL; ss. inv RELS.
    generalize (EX.(AEUS) t). rewrite LOCAL. intro X. inv X. des.
    exploit AExecUnit.rtc_step_future; eauto.
    { apply AExecUnit.wf_init. }
    s. i. des. econs; ss.
    inv WF. apply RMW0. ss.
  Qed.

  Lemma write_ex_codom_rmw
        p exec
        (EX: pre_ex p exec)
        eid
        (WRITE: exec.(Execution.label_is) (fun l => Label.is_write l /\ Label.is_ex l) eid):
    codom_rel exec.(Execution.rmw) eid.
  Proof.
    destruct eid as [tid n]. rewrite EX.(RMW).
    inv WRITE. des. destruct l; ss. destruct ex0; ss. revert EID. unfold Execution.label.
    rewrite EX.(LABELS), IdMap.map_spec. s.
    destruct (IdMap.find tid EX.(aeus)) eqn:LOCAL; ss. i.
    generalize (EX.(AEUS) tid). rewrite LOCAL. intro X. inv X. des.
    exploit AExecUnit.rtc_step_future; eauto.
    { apply AExecUnit.wf_init. }
    s. i. des. inv WF. exploit RMW1; eauto. intro X. inv X.
    econs. econs.
    - rewrite IdMap.map_spec, LOCAL. ss.
    - instantiate (1 := (_, _)). econs; ss; eauto.
  Qed.

  Lemma rmw_spec
        p exec eid1 eid2
        (EX: pre_ex p exec)
        (RMW: exec.(Execution.rmw) eid1 eid2):
    <<PO: Execution.po eid1 eid2>> /\
    <<LABEL1: exec.(Execution.label_is) (fun l => Label.is_read l /\ Label.is_ex l) eid1>> /\
    <<LABEL2: exec.(Execution.label_is) (fun l => Label.is_write l /\ Label.is_ex l) eid2>> /\
    <<BETWEEN: forall eid3 (AC: Execution.po eid1 eid3) (AC: Execution.po eid3 eid2),
        ~ exec.(Execution.label_is) (fun l => Label.is_read l /\ Label.is_ex l) eid3>>.
  Proof.
    revert RMW. rewrite EX.(RMW).
    i. inv RMW0. inv REL. destruct eid1, eid2. ss. subst. rewrite IdMap.map_spec in RELS.
    destruct (IdMap.find t EX.(aeus)) eqn:LOCAL; ss. inv RELS.
    generalize (EX.(AEUS) t). rewrite LOCAL. intro X. inv X. des.
    exploit AExecUnit.rtc_step_future; eauto.
    { apply AExecUnit.wf_init. }
    s. i. des. inv WF. exploit RMW2; eauto. i. des. splits; eauto.
    - econs.
      + unfold Execution.label. rewrite EX.(LABELS), IdMap.map_spec. s. rewrite LOCAL. eauto.
      + ss.
    - econs.
      + unfold Execution.label. rewrite EX.(LABELS), IdMap.map_spec. s. rewrite LOCAL. eauto.
      + ss.
    - ii. inv AC. inv AC0. ss. subst. inv H. revert EID.
      unfold Execution.label. rewrite EX.(LABELS), IdMap.map_spec, LOCAL. s. i.
      des. destruct l; ss. destruct ex0; ss.
      eapply BETWEEN; eauto.
  Qed.

  Lemma po_label_pre
        p exec
        eid1 eid2 label2
        (PRE: pre_ex p exec)
        (PO: Execution.po eid1 eid2)
        (LABEL: Execution.label eid2 exec = Some label2):
    exists label1, <<LABEL: Execution.label eid1 exec = Some label1>>.
  Proof.
    destruct eid1, eid2. inv PO. ss. subst.
    revert LABEL. unfold Execution.label.
    rewrite PRE.(LABELS), ? IdMap.map_spec. s.
    destruct (IdMap.find t0 PRE.(aeus)) eqn:LOCAL; ss.
    generalize (PRE.(AEUS) t0). rewrite LOCAL. intro X. inv X. des.
    i. exploit List.nth_error_Some. rewrite LABEL. intros [X _]. exploit X; [congr|]. clear X. i.
    generalize (List.nth_error_Some t.(AExecUnit.local).(ALocal.labels) n). intros [_ X]. hexploit X; [lia|]. i.
    destruct (List.nth_error t.(AExecUnit.local).(ALocal.labels) n); ss. eauto.
  Qed.

  Lemma po_label
        p exec
        eid1 eid2 label2
        (EX: ex p exec)
        (PO: Execution.po eid1 eid2)
        (LABEL: Execution.label eid2 exec = Some label2):
    exists label1, <<LABEL: Execution.label eid1 exec = Some label1>>.
  Proof.
    inv EX. eapply po_label_pre; eauto.
  Qed.

  Lemma coherence_rw
        p exec
        eid1 eid2 eid3 loc
        (EX: ex p exec)
        (EID1: exec.(Execution.label_is) (Label.is_reading loc) eid1)
        (EID2: exec.(Execution.label_is) (Label.is_writing loc) eid2)
        (EID3: exec.(Execution.label_is) (Label.is_writing loc) eid3)
        (RF1: exec.(Execution.rf) eid3 eid1)
        (PO: Execution.po eid1 eid2):
    exec.(Execution.co) eid3 eid2.
  Proof.
    inv EID1. apply Label.is_reading_inv in LABEL. des. subst.
    inv EID2. apply Label.is_writing_inv in LABEL. des. subst.
    inv EID3. apply Label.is_writing_inv in LABEL. des. subst.
    exploit EX.(CO1).
    { rewrite EID0, EID1. esplits; eauto. }
    i. des.
    - subst. exfalso. eapply EX.(INTERNAL). econs 2; econs.
      + left. left. left. econs; eauto. econs; eauto.
        econs; eauto using Label.read_is_accessing, Label.write_is_accessing.
      + right. eauto.
    - exfalso. eapply EX.(INTERNAL). econs 2; [econs|econs 2; econs].
      + left. left. left. econs; eauto. econs; eauto.
        econs; eauto using Label.read_is_accessing, Label.write_is_accessing.
      + left. right. eauto.
      + right. eauto.
    - ss.
  Qed.

  Lemma coherence_ww
        p exec
        eid1 eid2 loc
        (EX: ex p exec)
        (EID1: exec.(Execution.label_is) (Label.is_writing loc) eid1)
        (EID2: exec.(Execution.label_is) (Label.is_writing loc) eid2)
        (PO: Execution.po eid1 eid2):
    exec.(Execution.co) eid1 eid2.
  Proof.
    inv EID1. apply Label.is_writing_inv in LABEL. des. subst.
    inv EID2. apply Label.is_writing_inv in LABEL. des. subst.
    exploit EX.(CO1).
    { rewrite EID, EID0. esplits; eauto. }
    i. des.
    - subst. inv PO. lia.
    - ss.
    - exfalso. eapply EX.(INTERNAL). econs 2; econs.
      + left. left. left. econs; eauto. econs; eauto.
        econs; eauto using Label.read_is_accessing, Label.write_is_accessing.
      + left. right. eauto.
  Qed.

  Lemma coherence_rr
        p exec
        eid1 eid2 eid3 loc
        (EX: ex p exec)
        (EID1: exec.(Execution.label_is) (Label.is_reading loc) eid1)
        (EID2: exec.(Execution.label_is) (Label.is_reading loc) eid2)
        (EID3: exec.(Execution.label_is) (Label.is_writing loc) eid3)
        (RF: exec.(Execution.rf) eid3 eid1)
        (PO: Execution.po eid1 eid2):
    exists eid4,
      <<RF: exec.(Execution.rf) eid4 eid2>> /\
      <<CO: exec.(Execution.co)^? eid3 eid4>>.
  Proof.
    inv EID1. apply Label.is_reading_inv in LABEL. des. subst.
    inv EID2. apply Label.is_reading_inv in LABEL. des. subst.
    inv EID3. apply Label.is_writing_inv in LABEL. des. subst.
    exploit EX.(RF1); eauto. i. des.
    { exfalso. eapply EX.(INTERNAL). econs 2; [econs|econs 2; econs].
      - left. left. right. econs 2. econs; cycle 1.
        + econs; eauto. econs; eauto.
        + econs; eauto. econs; eauto using Label.read_is_accessing, Label.write_is_accessing.
      - right. eauto.
      - left. left. left. econs; eauto. econs; eauto.
        econs; eauto using Label.read_is_accessing, Label.write_is_accessing.
    }
    esplits; eauto.
    exploit EX.(CO1).
    { rewrite EID1, LABEL. esplits; eauto. }
    i. des.
    - subst. eauto.
    - econs 2. ss.
    - exfalso. eapply EX.(INTERNAL). econs 2; [econs|econs 2; econs].
      + left. left. left. econs; eauto. econs; eauto.
        econs; eauto using Label.read_is_accessing, Label.write_is_accessing.
      + left. left. right. left. econs; eauto.
      + right. ss.
  Qed.

  Lemma coherence_wr
        p exec
        eid1 eid2 loc
        (EX: ex p exec)
        (EID1: exec.(Execution.label_is) (Label.is_writing loc) eid1)
        (EID2: exec.(Execution.label_is) (Label.is_reading loc) eid2)
        (PO: Execution.po eid1 eid2):
    exists eid3,
      <<RF: exec.(Execution.rf) eid3 eid2>> /\
      <<CO: exec.(Execution.co)^? eid1 eid3>>.
  Proof.
    inv EID1. apply Label.is_writing_inv in LABEL. des. subst.
    inv EID2. apply Label.is_reading_inv in LABEL. des. subst.
    exploit EX.(RF1); eauto. i. des.
    { exfalso. eapply EX.(INTERNAL). econs 2; econs.
      - left. left. right. econs 2. econs; cycle 1.
        + econs; eauto. econs; eauto.
        + econs; eauto. econs; eauto using Label.read_is_accessing, Label.write_is_accessing.
      - left. left. left. econs; eauto. econs; eauto.
        econs; eauto using Label.read_is_accessing, Label.write_is_accessing.
    }
    esplits; eauto.
    exploit EX.(CO1).
    { rewrite EID, LABEL. esplits; eauto. }
    i. des.
    - subst. eauto.
    - econs 2. ss.
    - exfalso. eapply EX.(INTERNAL). econs 2; econs.
      + left. left. left. econs; eauto. econs; eauto.
        econs; eauto using Label.read_is_accessing, Label.write_is_accessing.
      + left. left. right. left. econs; eauto.
  Qed.

  Lemma rf_inv_write
        p exec
        eid1 eid2 ex1 ord1 loc val
        (EX: ex p exec)
        (EID2: Execution.label eid2 exec = Some (Label.read ex1 ord1 loc val))
        (RF3: exec.(Execution.rf) eid1 eid2):
    exists ex2 ord2,
      <<LABEL: Execution.label eid1 exec = Some (Label.write ex2 ord2 loc val)>>.
  Proof.
    exploit EX.(RF1); eauto. i. des.
    - contradict NORF. econs. eauto.
    - exploit EX.(RF_WF); [exact RF3|exact RF|]. i. subst. eauto.
  Qed.

  Ltac obtac :=
    repeat
      (try match goal with
           | [H: Execution.ob _ _ _ |- _] => inv H
           | [H: Execution.obs _ _ _ |- _] => inv H
           | [H: Execution.dob _ _ _ |- _] => inv H
           | [H: Execution.aob _ _ _ |- _] => inv H
           | [H: Execution.bob _ _ _ |- _] => inv H
           | [H: Execution.fr _ _ _ |- _] => inv H
           | [H: Execution.rfe _ _ _ |- _] => inv H
           | [H: Execution.rfi _ _ _ |- _] => inv H
           | [H: (_⨾ _) _ _ |- _] => inv H
           | [H: ⦗_⦘ _ _ |- _] => inv H
           | [H: (_ ∪ _) _ _ |- _] => inv H
           | [H: (_ ∩ _) _ _ |- _] => inv H
           | [H: (_ × _) _ _ |- _] => inv H
           | [H: (minus_rel _ _) _ |- _] => inv H
           | [H: Execution.label_is _ _ _ |- _] => inv H
           | [H: Execution.label_rel _ _ _ _ |- _] => inv H
           | [H: Execution.label_loc _ _ |- _] => inv H
           end;
       des).


  Lemma addr_label
        p exec
        eid1 eid2
        (EX: pre_ex p exec)
        (ADDR: exec.(Execution.addr) eid1 eid2):
    <<EID1: Execution.label_is exec (Label.is_access) eid1>> /\
    <<EID2: Execution.label_is exec (Label.is_access) eid2>>.
  Proof.
    rewrite EX.(Valid.ADDR) in ADDR. inv ADDR.
    destruct eid1 as [tid1 iid1].
    destruct eid2 as [tid2 iid2].
    inv REL. ss. subst.
    rewrite IdMap.map_spec in RELS.
    destruct (IdMap.find tid1 EX.(aeus)) eqn:LOCAL; ss. inv RELS.
    generalize (EX.(AEUS) tid1). rewrite LOCAL. intro X. inv X.
    exploit AExecUnit.rtc_step_future; eauto.
    { apply AExecUnit.wf_init. }
    s. i. des.
    inv WF. exploit ADDR_LABEL; eauto. intro X. inv X.
    esplits.
    - inv H. econs; eauto.
      unfold Execution.label. s.
      rewrite EX.(LABELS), IdMap.map_spec, LOCAL. ss.
    - inv H1. econs; eauto. unfold Execution.label. s. rewrite EX.(LABELS), IdMap.map_spec, LOCAL. ss.
  Qed.

  Lemma data_label
        p exec
        eid1 eid2
        (EX: pre_ex p exec)
        (DATA: exec.(Execution.data) eid1 eid2):
    <<EID1: Execution.label_is exec (Label.is_access) eid1>> /\
    <<EID2: Execution.label_is exec (Label.is_write) eid2>>.
  Proof.
    rewrite EX.(Valid.DATA) in DATA. inv DATA.
    destruct eid1 as [tid1 iid1].
    destruct eid2 as [tid2 iid2].
    inv REL. ss. subst.
    rewrite IdMap.map_spec in RELS.
    destruct (IdMap.find tid1 EX.(aeus)) eqn:LOCAL; ss. inv RELS.
    generalize (EX.(AEUS) tid1). rewrite LOCAL. intro X. inv X.
    exploit AExecUnit.rtc_step_future; eauto.
    { apply AExecUnit.wf_init. }
    s. i. des.
    inv WF. exploit DATA_LABEL; eauto. intro X. inv X.
    esplits.
    - inv H. econs; eauto.
      unfold Execution.label. s.
      rewrite EX.(LABELS), IdMap.map_spec, LOCAL. ss.
    - inv H1. econs; eauto.
      unfold Execution.label. s.
      rewrite EX.(LABELS), IdMap.map_spec, LOCAL. ss.
  Qed.

  Lemma ctrl_label
        p exec
        eid1 eid2
        (EX: pre_ex p exec)
        (CTRL: exec.(Execution.ctrl) eid1 eid2):
    <<EID1: Execution.label_is exec (Label.is_access) eid1>> /\
    <<EID2: Execution.label_is exec (Label.is_ctrl) eid2>>.
  Proof.
    rewrite EX.(Valid.CTRL) in CTRL. inv CTRL.
    destruct eid1 as [tid1 iid1].
    destruct eid2 as [tid2 iid2].
    inv REL. ss. subst.
    rewrite IdMap.map_spec in RELS.
    destruct (IdMap.find tid1 EX.(aeus)) eqn:LOCAL; ss. inv RELS.
    generalize (EX.(AEUS) tid1). rewrite LOCAL. intro X. inv X.
    exploit AExecUnit.rtc_step_future; eauto.
    { apply AExecUnit.wf_init. }
    s. i. des.
    inv WF. exploit CTRL_LABEL; eauto. intro X. inv X.
    splits.
    - inv H. econs; eauto.
      unfold Execution.label. s.
      rewrite EX.(LABELS), IdMap.map_spec, LOCAL. ss.
    - inv H1. econs; eauto.
      unfold Execution.label. s.
      rewrite EX.(LABELS), IdMap.map_spec, LOCAL. ss.
  Qed.

  Lemma barrier_ob_po
        p exec
        eid1 eid2
        (EX: pre_ex p exec)
        (CO2: co2 exec)
        (RF2: rf2 exec)
        (EID1: Execution.label_is exec Label.is_barrier eid1)
        (OB: exec.(Execution.ob) eid1 eid2):
    Execution.po eid1 eid2.
  Proof.
    inv EID1. destruct l; ss. unfold co2, rf2 in *.
    obtac; ss.
    all: try by etrans; eauto.
    - exploit RF2; eauto. i. des. congr.
    - exploit RF2; eauto. i. des. congr.
    - destruct l1; try congr; ss.
    - exploit CO2; eauto. i. des. congr.
    - eapply addr_label in H1; eauto. des. inv EID1. destruct l; ss; congr.
    - eapply data_label in H1; eauto. des. inv EID1. destruct l; ss; congr.
    - etrans; eauto. eapply ctrl_is_po; eauto.
    - etrans; eauto. eapply addr_is_po; eauto.
    - etrans; eauto. etrans; eauto. eapply ctrl_is_po; eauto.
    - etrans; eauto. etrans; eauto. eapply addr_is_po; eauto.
    - exploit RF2; eauto. i. des. congr.
    - exploit RF2; eauto. i. des. congr.
    - revert H0. unfold ifc. condtac; ss. eapply rmw_spec. eauto.
  Qed.

  Lemma ob_barrier_ob
        p exec
        eid1 eid2 eid3
        (PRE: pre_ex p exec)
        (CO2: co2 exec)
        (RF2: rf2 exec)
        (EID2: Execution.label_is exec Label.is_barrier eid2)
        (OB1: exec.(Execution.ob) eid1 eid2)
        (OB2: exec.(Execution.ob) eid2 eid3):
    <<OB: exec.(Execution.ob) eid1 eid3>>.
  Proof.
    inv EID2. destruct l; ss. exploit barrier_ob_po; eauto. i.
    unfold co2, rf2 in *. clear OB2.
    obtac.
    all: try by rewrite EID in EID1; inv EID1; ss.
    all: try by rewrite EID in EID2; inv EID2; ss.
    all: try by destruct l; try congr; ss.
    - exploit RF2; eauto. i. des. congr.
    - exploit CO2; eauto. i. des. congr.
    - exploit CO2; eauto. i. des. congr.
    - inv H0.
      + eapply addr_label in H1; eauto. des. inv EID2. destruct l; ss; try congr.
      + inv H. exploit RF2; eauto. i. des. congr.
    - inv H0.
      + eapply data_label in H1; eauto. des. inv EID2. destruct l; ss. congr.
      + inv H. exploit RF2; eauto. i. des. congr.
    - exploit RF2; eauto. i. des. congr.
    - right. left. left. right. econs. splits; [by econs; eauto|]. etrans; eauto.
    - revert H0. unfold ifc. condtac; ss. i. exploit rmw_spec; eauto. i. des.
      inv LABEL2. rewrite EID in EID0. inv EID0. des. ss.
  Qed.

  Lemma ctrl_ob_po
        p exec
        eid1 eid2
        (EX: pre_ex p exec)
        (CO2: co2 exec)
        (RF2: rf2 exec)
        (EID1: Execution.label_is exec Label.is_ctrl eid1)
        (OB: exec.(Execution.ob) eid1 eid2):
    Execution.po eid1 eid2.
  Proof.
    inv EID1. destruct l; ss. unfold co2, rf2 in *.
    obtac; ss.
    all: try by etrans; eauto.
    - exploit RF2; eauto. i. des. congr.
    - exploit RF2; eauto. i. des. congr.
    - destruct l1; try congr; ss.
    - exploit CO2; eauto. i. des. congr.
    - eapply addr_label in H1; eauto. des. inv EID1. destruct l; ss; congr.
    - eapply data_label in H1; eauto. des. inv EID1. destruct l; ss; congr.
    - etrans; eauto. eapply ctrl_is_po; eauto.
    - etrans; eauto. eapply addr_is_po; eauto.
    - etrans; eauto. etrans; eauto. eapply ctrl_is_po; eauto.
    - etrans; eauto. etrans; eauto. eapply addr_is_po; eauto.
    - exploit RF2; eauto. i. des. congr.
    - exploit RF2; eauto. i. des. congr.
    - revert H0. unfold ifc. condtac; ss. eapply rmw_spec. eauto.
  Qed.

  Lemma ob_ctrl_ob
        p exec
        eid1 eid2 eid3
        (PRE: pre_ex p exec)
        (CO2: co2 exec)
        (RF2: rf2 exec)
        (EID2: Execution.label_is exec Label.is_ctrl eid2)
        (OB1: exec.(Execution.ob) eid1 eid2)
        (OB2: exec.(Execution.ob) eid2 eid3):
    <<OB: exec.(Execution.ob) eid1 eid3>>.
  Proof.
    inv EID2. destruct l; ss. exploit ctrl_ob_po; eauto. i.
    unfold co2, rf2 in *. clear OB2.
    obtac.
    all: try by rewrite EID in EID1; inv EID1; ss.
    all: try by rewrite EID in EID2; inv EID2; ss.
    all: try by destruct l; try congr; ss.
    - exploit RF2; eauto. i. des. congr.
    - exploit CO2; eauto. i. des. congr.
    - exploit CO2; eauto. i. des. congr.
    - inv H0.
      + eapply addr_label in H1; eauto. des. inv EID2. destruct l; ss; try congr.
      + inv H. exploit RF2; eauto. i. des. congr.
    - inv H0.
      + eapply data_label in H1; eauto. des. inv EID2. destruct l; ss. congr.
      + inv H. exploit RF2; eauto. i. des. congr.
    - exploit RF2; eauto. i. des. congr.
    - right. left. left. right. econs. splits; [by econs; eauto|]. etrans; eauto.
    - revert H0. unfold ifc. condtac; ss. i. exploit rmw_spec; eauto. i. des.
      inv LABEL2. rewrite EID in EID0. inv EID0. des. ss.
  Qed.

  Lemma ob_label
        p exec
        eid1 eid2
        (PRE: pre_ex p exec)
        (CO2: co2 exec)
        (RF2: rf2 exec)
        (OB: exec.(Execution.ob) eid1 eid2)
        (EID1: Execution.label eid1 exec = None):
    False.
  Proof.
    unfold co2, rf2 in *.
    obtac.
    all: try congr.
    all: try by exploit RF2; eauto; i; des; congr.
    all: try by exploit CO2; eauto; i; des; congr.
    - exploit addr_label; eauto. i. des. inv EID0. congr.
    - exploit data_label; eauto. i. des. inv EID0. congr.
    - exploit ctrl_label; eauto. i. des. inv EID0. congr.
    - exploit addr_label; eauto. i. des. inv EID0. congr.
    - exploit ctrl_label; eauto. i. des. inv EID2. congr.
    - exploit addr_label; eauto. i. des. inv EID2. congr.
    - exploit po_label_pre; try exact EID; eauto. i. des. congr.
    - revert H0. unfold ifc. condtac; ss. i. exploit rmw_spec; eauto. i. des. inv LABEL1. congr.
  Qed.

  Lemma ob_cycle
        p exec eid
        (PRE: pre_ex p exec)
        (CO2: co2 exec)
        (RF2: rf2 exec)
        (CYCLE: exec.(Execution.ob)⁺ eid eid):
    exists eid_nb,
      (exec.(Execution.ob) ∩ (Execution.label_is_rel exec Label.is_access))⁺ eid_nb eid_nb.
  Proof.
    exploit minimalize_cycle; eauto.
    { instantiate (1 := Execution.label_is exec Label.is_access).
      i. destruct (Execution.label b exec) eqn:LABEL.
      - destruct t; try by contradict H1; econs; eauto.
        + eapply ob_barrier_ob; eauto.
        + eapply ob_ctrl_ob; eauto.
      - exfalso. eapply ob_label; eauto.
    }
    i. des.
    - esplits. eapply clos_trans_mon; eauto. s. i. des.
      econs; ss. inv H0. inv H1. econs; eauto.
    - destruct (Execution.label a exec) eqn:LABEL.
      + destruct t; try by contradict x0; econs; eauto.
        * exploit barrier_ob_po; eauto. i. inv x2. lia.
        * exploit ctrl_ob_po; eauto. i. inv x2. lia.
      + exfalso. eapply ob_label; eauto.
  Qed.

  Lemma internal_rw
        p ex
        eid1 eid2
        (PRE: pre_ex p ex)
        (CO2: co2 ex)
        (RF2: rf2 ex)
        (INTERNAL: ex.(Execution.internal) eid1 eid2):
    <<EID1: ex.(Execution.label_is) Label.is_access eid1>> /\
    <<EID2: ex.(Execution.label_is) Label.is_access eid2>>.
  Proof.
    unfold Execution.internal in *. obtac.
    - inv H. inv H1. inv LABEL. splits.
      + destruct l1; ss; econs; eauto.
      + destruct l2; ss; econs; eauto.
    - exploit CO2; eauto. i. des.
      exploit RF2; eauto. i. des.
      splits; econs; eauto.
    - splits.
      + destruct l1; ss; econs; eauto.
      + destruct l2; ss; econs; eauto.
    - exploit CO2; eauto. i. des.
      splits; econs; eauto.
    - exploit RF2; eauto. i. des.
      splits; econs; eauto.
  Qed.

  Lemma internal_read_read_po
        p ex
        eid1 eid2
        (PRE: pre_ex p ex)
        (CO2: co2 ex)
        (RF2: rf2 ex)
        (INTERNAL: ex.(Execution.internal) eid1 eid2)
        (EID1: ex.(Execution.label_is) Label.is_read eid1)
        (EID2: ex.(Execution.label_is) Label.is_read eid2):
    Execution.po eid1 eid2.
  Proof.
    unfold Execution.internal in *. obtac.
    - inv H. ss.
    - exploit CO2; eauto. i. des.
      destruct l; ss. congr.
    - rewrite EID in EID0. inv EID0. destruct l0; ss.
    - exploit CO2; eauto. i. des.
      destruct l; ss. congr.
    - exploit RF2; eauto. i. des.
      destruct l0; ss. congr.
  Qed.

  Lemma ob_read_read_po
        p ex
        eid1 eid2
        (PRE: pre_ex p ex)
        (CO1: co1 ex)
        (CO2: co2 ex)
        (RF1: rf1 ex)
        (RF2: rf2 ex)
        (RF_WF: rf_wf ex)
        (INTERNAL: acyclic ex.(Execution.internal))
        (OB: ex.(Execution.ob) eid1 eid2)
        (EID1: ex.(Execution.label_is) Label.is_read eid1)
        (EID2: ex.(Execution.label_is) Label.is_read eid2):
    Execution.po eid1 eid2.
  Proof.
    inv EID1. inv EID2. destruct l; ss. destruct l0; ss.
    unfold Execution.ob in *. obtac; try congr.
    all: try by etrans; eauto.
    all: try by exploit RF2; eauto; i; des; congr.
    all: try by exploit CO2; eauto; i; des; congr.
    - inv H0. rewrite EID0 in EID1. inv EID1. inv LABEL1.
    - exploit addr_is_po; eauto. i. inv H0; ss. etrans; eauto.
      cut (Execution.po x eid2 \/ Execution.po eid2 x).
      { i. inv H. des; auto.
        exfalso. eapply INTERNAL. econs 2.
        - econs. right. eauto.
        - exploit RF2; eauto. i. des.
          econs. repeat left. repeat (econs; eauto); ss.
          + instantiate (1 := loc1).
            unfold equiv_dec. unfold Z_eqdec. unfold proj_sumbool.
            des_ifs; ss.
          + unfold equiv_dec. unfold Z_eqdec. unfold proj_sumbool.
            des_ifs; ss. }
      inv H. inv H2. destruct x as [t1 e1], eid2 as [t2 e2]. ss.
      exploit RF2; eauto. i. des.
      generalize (Nat.lt_trichotomy e1 e2). i. des; try congr.
      + left. econs; eauto.
      + right. econs; eauto.
    - exploit data_is_po; eauto. i. inv H0; ss. etrans; eauto.
      cut (Execution.po x eid2 \/ Execution.po eid2 x).
      { i. inv H. des; auto.
        exfalso. eapply INTERNAL. econs 2.
        - econs. right. eauto.
        - exploit RF2; eauto. i. des.
          econs. repeat left. repeat (econs; eauto); ss.
          + instantiate (1 := loc1).
            unfold equiv_dec. unfold Z_eqdec. unfold proj_sumbool.
            des_ifs; ss.
          + unfold equiv_dec. unfold Z_eqdec. unfold proj_sumbool.
            des_ifs; ss. }
      inv H. inv H2. destruct x as [t1 e1], eid2 as [t2 e2]. ss.
      exploit RF2; eauto. i. des.
      generalize (Nat.lt_trichotomy e1 e2). i. des; try congr.
      + left. econs; eauto.
      + right. econs; eauto.
    - etrans; eauto. eapply ctrl_is_po; eauto.
    - etrans; eauto. eapply addr_is_po; eauto.
    - rewrite <- H3, <- H1. eapply ctrl_is_po; eauto.
    - rewrite <- H3, <- H1. eapply addr_is_po; eauto.
    - revert H0. unfold ifc. condtac; ss. eapply rmw_spec. eauto.
  Qed.

  Lemma rfi_is_po
        ex eid1 eid2
        (RF2: Valid.rf2 ex)
        (INTERNAL: acyclic ex.(Execution.internal))
        (RFI: ex.(Execution.rfi) eid1 eid2):
    Execution.po eid1 eid2.
  Proof.
    destruct eid1 as [tid1 eid1], eid2 as [tid2 eid2].
    inv RFI. inv H0. ss. subst.
    exploit RF2; eauto. i. des.
    generalize (Nat.lt_trichotomy eid1 eid2). i. des.
    - econs; ss.
    - subst. congr.
    - exfalso. eapply INTERNAL. econs 2.
      + econs 1. right. eauto.
      + econs 1. left. left. left. econs; eauto.
        econs; eauto. econs; unfold Label.is_accessing; eauto.
        * instantiate (1 := loc).
          destruct (equiv_dec loc loc); ss.
          exfalso. apply c. ss.
        * destruct (equiv_dec loc loc); ss.
          exfalso. apply c. ss.
  Qed.

  Lemma po_loc_write_is_co
        ex eid1 eid2 loc
        (CO1: Valid.co1 ex)
        (INTERNAL: acyclic ex.(Execution.internal))
        (PO: Execution.po eid1 eid2)
        (LABEL1: ex.(Execution.label_is) (Label.is_writing loc) eid1)
        (LABEL2: ex.(Execution.label_is) (Label.is_writing loc) eid2):
    ex.(Execution.co) eid1 eid2.
  Proof.
    destruct eid1 as [tid1 eid1], eid2 as [tid2 eid2].
    inv LABEL1. inv LABEL2. destruct l, l0; ss.
    destruct (equiv_dec loc0 loc) eqn:Heq1; ss.
    destruct (equiv_dec loc1 loc) eqn:Heq2; ss.
    rewrite e, e0 in *.
    exploit CO1; eauto.
    { esplits; [exact EID|exact EID0]. }
    i. des; eauto.
    - inv x. inv PO. ss. lia.
    - exfalso. eapply INTERNAL. econs 2.
      + econs 1. left. left. left. econs; eauto.
        econs; eauto. econs; unfold Label.is_accessing; eauto.
        * instantiate (1 := loc).
          destruct (equiv_dec loc loc); ss.
        * destruct (equiv_dec loc loc); ss.
      + econs 1. left. right. eauto.
  Qed.
End Valid.

Coercion Valid.PRE: Valid.ex >-> Valid.pre_ex.
