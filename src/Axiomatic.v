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

  Definition is_accessing (label:t): option Loc.t :=
    match label with
    | read _ _ loc _ => Some loc
    | write _ _ loc _ => Some loc
    | barrier _ => None
    end.
End Label.

Module ALocal.
  Inductive t := mk {
    labels: list Label.t;
    addr: relation nat;
    data: relation nat;
    ctrl: relation nat;
    ctrl_src: nat -> Prop;
  }.
  Hint Constructors t.

  Definition init: t := mk [] bot bot bot bot.

  Definition next_eid (eu:t): nat :=
    List.length eu.(labels).

  Inductive step (event:Event.t (A:=nat -> Prop)) (ctor1:t) (ctor2:t): Prop :=
  | step_internal
      (EVENT: event = Event.internal)
      (CTOR: ctor2 = ctor1)
  | step_read
      ex ord vloc res
      (EVENT: event = Event.read ex ord vloc (ValA.mk _ res (eq (next_eid ctor1))))
      (CTOR: ctor2 =
             mk
               (ctor1.(labels) ++ [Label.read ex ord vloc.(ValA.val) res])
               (ctor1.(addr) ∪ (vloc.(ValA.annot) × (eq (next_eid ctor1))))
               ctor1.(data)
               (ctor1.(ctrl) ∪ (ctor1.(ctrl_src) × (eq (next_eid ctor1))))
               ctor1.(ctrl_src))
  | step_write
      ex ord vloc vval
      (EVENT: event = Event.write ex ord vloc vval (ValA.mk _ 0 (eq (next_eid ctor1))))
      (CTOR: ctor2 =
             mk
               (ctor1.(labels) ++ [Label.write ex ord vloc.(ValA.val) vval.(ValA.val)])
               (ctor1.(addr) ∪ (vloc.(ValA.annot) × (eq (next_eid ctor1))))
               (ctor1.(data) ∪ (vval.(ValA.annot) × (eq (next_eid ctor1))))
               (ctor1.(ctrl) ∪ (ctor1.(ctrl_src) × (eq (next_eid ctor1))))
               ctor1.(ctrl_src))
  | step_write_failure
      ord vloc vval
      (EVENT: event = Event.write true ord vloc vval (ValA.mk _ 1 bot))
      (CTOR: ctor2 =
             mk
               ctor1.(labels)
               ctor1.(addr)
               ctor1.(data)
               ctor1.(ctrl)
               ctor1.(ctrl_src))
  | step_barrier
      b
      (EVENT: event = Event.barrier b)
      (CTOR: ctor2 =
             mk
               (ctor1.(labels) ++ [Label.barrier b])
               ctor1.(addr)
               ctor1.(data)
               ctor1.(ctrl)
               ctor1.(ctrl_src))
  | step_ctrl
      src
      (EVENT: event = Event.ctrl src)
      (CTOR: ctor2 =
             mk
               ctor1.(labels)
               ctor1.(addr)
               ctor1.(data)
               ctor1.(ctrl)
               ((ctor1.(ctrl_src)) \1/ (src)))
  .
  Hint Constructors step.
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
      (X: Label.is_accessing x = Some loc)
      (Y: Label.is_accessing y = Some loc)
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

Definition tid_join
           (rels: IdMap.t (relation nat)):
  relation eidT :=
  fun x y =>
    exists tid rel,
      <<TID_LHS: x.(fst) = tid>> /\
      <<TID_RHS: y.(fst) = tid>> /\
      <<RELS: IdMap.find tid rels = Some rel>> /\
      <<REL: rel x.(snd) y.(snd)>>.
Hint Unfold tid_join.

Inductive is_valid_pre (p:program) (ex:Execution.t): Prop :=
| is_valid_pre_intro
    locals
    (LOCALS: IdMap.for_all
               (fun stmts local =>
                  exists state,
                    <<STEP: rtc AExecUnit.step
                                (AExecUnit.mk (State.init stmts) ALocal.init)
                                (AExecUnit.mk state local)>> /\
                    <<TERMINAL: State.is_terminal state>>)
               p locals)
    (LABELS: ex.(Execution.labels) = IdMap.map (fun local => local.(ALocal.labels)) locals)
    (PO: ex.(Execution.po) = tid_join (IdMap.map
                               (fun local =>
                                  fun x y =>
                                    0 <= x /\
                                    x < y /\
                                    y < List.length local.(ALocal.labels))
                               locals))
    (ADDR: ex.(Execution.addr) = tid_join (IdMap.map (fun local => local.(ALocal.addr)) locals))
    (DATA: ex.(Execution.data) = tid_join (IdMap.map (fun local => local.(ALocal.data)) locals))
    (CTRL: ex.(Execution.ctrl) = tid_join (IdMap.map (fun local => local.(ALocal.ctrl)) locals))
    (RMW: forall eid1 ord1 loc val1
           (LABEL1: Execution.label eid1 ex = Some (Label.write true ord1 loc val1)),
        exists eid2 ord2 val2,
          <<LABEL: Execution.label eid2 ex = Some (Label.read true ord2 loc val2)>> /\
          <<PO: ex.(Execution.po) eid2 eid1>> /\
          <<RMW: ex.(Execution.rmw) eid2 eid1>> /\
          <<BTW: forall eid3 label3
                   (PO23: ex.(Execution.po) eid2 eid3)
                   (PO31: ex.(Execution.po) eid3 eid1)
                   (LABEL3: Execution.label eid3 ex = Some label3),
              Label.is_ex label3 = false>>)
.
Hint Constructors is_valid_pre.

Inductive is_valid (p:program) (ex:Execution.t): Prop :=
| is_valid_intro
    (PRE: is_valid_pre p ex)
    (CO: forall loc
           eid1 ex1 ord1 val1
           eid2 ex2 ord2 val2
           (EID: eid1 <> eid2)
           (LABEL1: Execution.label eid1 ex = Some (Label.write ex1 ord1 loc val1))
           (LABEL2: Execution.label eid2 ex = Some (Label.write ex2 ord2 loc val2)),
        ex.(Execution.co) eid1 eid2 \/ ex.(Execution.co) eid2 eid1)
    (RF: forall eid1 ex1 ord1 loc val
           (LABEL1: Execution.label eid1 ex = Some (Label.read ex1 ord1 loc val)),
        exists eid2 ex2 ord2,
          <<LABEL: Execution.label eid2 ex = Some (Label.write ex2 ord2 loc val)>> /\
          <<RF: ex.(Execution.rf) eid2 eid1>>)
    (INTERNAL: acyclic ex.(Execution.internal))
    (EXTERNAL: acyclic ex.(Execution.ob))
    (ATOMIC: le (ex.(Execution.rmw) ∩ (ex.(Execution.fre) ⨾ ex.(Execution.coe))) bot)
.
Hint Constructors is_valid.
