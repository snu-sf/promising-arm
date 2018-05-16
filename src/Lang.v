Require Import NArith.
Require Import PArith.
Require Import ZArith.
Require Import Lia.
Require Import FMapPositive.
Require Import FSetPositive.
Require Import sflib.
Require Import EquivDec.

Require Import Order.
Require Import Time.

Set Implicit Arguments.

Module Id := Pos.

Module IdMap.
  Include PositiveMap.

  Inductive opt_pred A B (pred: A -> B -> Prop): forall (a:option A) (b:option B), Prop :=
  | opt_pred_None:
      opt_pred pred None None
  | opt_pred_Some
      a b
      (PRED: pred a b):
      opt_pred pred (Some a) (Some b)
  .

  Definition for_all A B
             (pred: A -> B -> Prop)
             (a: IdMap.t A)
             (b: IdMap.t B)
    : Prop :=
    forall id, opt_pred pred (find id a) (find id b).
End IdMap.

Module IdSet.
  Include PositiveSet.

  Lemma add_o x' x s:
    mem x' (add x s) =
    if x' == x
    then true
    else mem x' s.
  Proof.
    destruct (equiv_dec x' x).
    - inv e. apply mem_1. apply add_spec. intuition.
    - destruct (mem x' s) eqn:MEM.
      + apply mem_1. apply add_spec. intuition.
      + destruct (mem x' (add x s)) eqn:MEM'; ss.
        apply mem_1 in MEM'. apply add_spec in MEM'. des; intuition.
        apply mem_1 in MEM'. eauto.
  Qed.

  Lemma remove_o x' x s:
    mem x' (remove x s) =
    if x' == x
    then false
    else mem x' s.
  Proof.
    destruct (equiv_dec x' x).
    - inv e. destruct (mem x (remove x s)) eqn:MEM; ss.
      apply remove_spec in MEM. des; ss.
    - destruct (mem x' s) eqn:MEM.
      + apply mem_1. apply remove_spec. intuition.
      + destruct (mem x' (remove x s)) eqn:MEM'; ss.
        apply mem_1 in MEM'. apply remove_spec in MEM'. des.
        apply mem_1 in MEM'0. eauto.
  Qed.
End IdSet.

Module Val.
  Include Z.

  Definition default: t := 0.
End Val.

Module Loc := Val.

Inductive opT1 :=
| op_not
.
Hint Constructors opT1.

Inductive opT2 :=
| op_add
| op_sub
| op_mul
.
Hint Constructors opT2.

Inductive exprT :=
| expr_const (const:Val.t)
| expr_reg (reg:Id.t)
| expr_op1 (op:opT1) (e1:exprT)
| expr_op2 (op:opT2) (e1 e2:exprT)
.
Hint Constructors exprT.
Coercion expr_const: Val.t >-> exprT.
Coercion expr_reg: Id.t >-> exprT.

(* TODO: we need to deal with acquirePC ("[Q]" in the "Simplifying ARM Concurrency" paper). *)
Inductive ordT :=
| pln
| rlx
| ra
.
Hint Constructors ordT.

Definition ord_le (a b:ordT): bool :=
  match a, b with
  | pln, _ => true
  | _, ra => true
  | rlx, rlx => true
  | _, _ => false
  end.
Hint Unfold ord_le.

Module Barrier.
  Inductive t :=
  | isb
  | dmbst
  | dmbld
  | dmbsy
  .
  Hint Constructors t.
End Barrier.

Inductive instrT :=
| instr_skip
| instr_assign (lhs:Id.t) (rhs:exprT)
| instr_load (ex:bool) (ord:ordT) (res:Id.t) (eloc:exprT)
| instr_store (ex:bool) (ord:ordT) (res:Id.t) (eloc:exprT) (eval:exprT)
| instr_barrier (b:Barrier.t)
.
Hint Constructors instrT.
Coercion instr_barrier: Barrier.t >-> instrT.

Inductive stmtT :=
| stmt_instr (i:instrT)
| stmt_if (cond:exprT) (s1 s2:list stmtT)
| stmt_dowhile (s:list stmtT) (cond:exprT)
.
Hint Constructors stmtT.
Coercion stmt_instr: instrT >-> stmtT.

Definition program := IdMap.t (list stmtT).


Module ValA.
  Inductive t A `{_: orderC A} := mk {
    val: Val.t;
    annot: A;
  }.
  Hint Constructors t.
End ValA.

Module RMap.
Section RMap.
  Context A `{_: orderC A}.

  Definition t := IdMap.t (ValA.t (A:=A)).

  Definition init: t := IdMap.empty _.

  Definition find (reg:Id.t) (rmap:t): (ValA.t (A:=A)) :=
    match IdMap.find reg rmap with
    | Some v => v
    | None => ValA.mk _ 0 bot
    end.

  Definition add (reg:Id.t) (val:ValA.t (A:=A)) (rmap:t): t :=
    IdMap.add reg val rmap.

  Lemma add_o reg' reg val rmap:
    find reg' (add reg val rmap) =
    if reg' == reg
    then val
    else find reg' rmap.
  Proof.
    unfold add, find. rewrite PositiveMapAdditionalFacts.gsspec.
    repeat match goal with
           | [|- context[if ?c then _ else _]] => destruct c
           end; ss.
  Qed.
End RMap.
End RMap.

Definition sem0_op1 (op:opT1) (v1:Val.t): Val.t :=
  match op with
  | op_not => -v1
  end.

Definition sem0_op2 (op:opT2) (v1 v2:Val.t): Val.t :=
  match op with
  | op_add => v1 + v1
  | op_sub => v1 - v2
  | op_mul => v1 * v2
  end.

Section SEM.
  Context A `{_: orderC A}.

  Definition sem_op1 (op:opT1) (v1:ValA.t): (ValA.t (A:=A)) :=
    ValA.mk _ (sem0_op1 op v1.(ValA.val)) v1.(ValA.annot).

  Definition sem_op2 (op:opT2) (v1 v2:ValA.t): ValA.t :=
    ValA.mk _ (sem0_op2 op v1.(ValA.val) v2.(ValA.val)) (join v1.(ValA.annot) v2.(ValA.annot)).

  Fixpoint sem_expr (rmap:RMap.t (A:=A)) (e:exprT): ValA.t :=
    match e with
    | expr_const const => ValA.mk _ const bot
    | expr_reg reg => RMap.find reg rmap
    | expr_op1 op e1 => sem_op1 op (sem_expr rmap e1)
    | expr_op2 op e1 e2 => sem_op2 op (sem_expr rmap e1) (sem_expr rmap e2)
    end.
End SEM.

Module Event.
  Inductive t A `{_: orderC A} :=
  | internal
  | read (ex:bool) (ord:ordT) (vloc:ValA.t (A:=A)) (res:ValA.t (A:=A))
  | write (ex:bool) (ord:ordT) (vloc:ValA.t (A:=A)) (vval:ValA.t (A:=A)) (res:ValA.t (A:=A))
  | barrier (b:Barrier.t)
  | ctrl (a:A)
  .
End Event.

Module State.
Section State.
  Context A `{_: orderC A}.

  Inductive t := mk {
    stmts: list stmtT;
    rmap: RMap.t (A:=A);
  }.

  Definition init (stmts:list stmtT): t := mk stmts (RMap.init (A:=A)).

  Definition is_terminal (st:t): Prop :=
    st.(stmts) = [].
  Hint Unfold is_terminal.

  Inductive step: forall (e:Event.t (A:=A)) (st1 st2:t), Prop :=
  | step_skip
      stmts rmap:
      step Event.internal
           (mk ((stmt_instr instr_skip)::stmts) rmap)
           (mk stmts rmap)
  | step_assign
      lhs rhs stmts rmap rmap'
      (RMAP: rmap' = RMap.add lhs (sem_expr rmap rhs) rmap):
      step Event.internal
           (mk ((stmt_instr (instr_assign lhs rhs))::stmts) rmap)
           (mk stmts rmap')
  | step_load
      ex o res eloc stmts rmap vloc vres rmap'
      (LOC: vloc = sem_expr rmap eloc)
      (RMAP: rmap' = RMap.add res vres rmap):
      step (Event.read ex o vloc vres)
           (mk ((stmt_instr (instr_load ex o res eloc))::stmts) rmap)
           (mk stmts rmap')
  | step_store
      ex o res eloc eval stmts rmap vloc vval vres rmap'
      (LOC: vloc = sem_expr rmap eloc)
      (VAL: vval = sem_expr rmap eval)
      (RMAP: rmap' = RMap.add res vres rmap):
      step (Event.write ex o vloc vval vres)
           (mk ((stmt_instr (instr_store ex o res eloc eval))::stmts) rmap)
           (mk stmts rmap')
  | step_barrier
      b stmts rmap:
      step (Event.barrier b)
           (mk ((stmt_instr (instr_barrier b))::stmts) rmap)
           (mk stmts rmap)
  | step_if
      cond vcond s1 s2 stmts rmap stmts'
      (COND: vcond = sem_expr rmap cond)
      (STMTS: stmts' = (if vcond.(ValA.val) <> 0%Z then s1 else s2) ++ stmts):
      step (Event.ctrl vcond.(ValA.annot))
           (mk ((stmt_if cond s1 s2)::stmts) rmap)
           (mk stmts' rmap)
  | step_dowhile
      s cond stmts rmap stmts'
      (STMTS: stmts' = s ++ [stmt_if cond ((stmt_dowhile s cond) :: stmts) stmts]):
      step Event.internal
           (mk ((stmt_dowhile s cond)::stmts) rmap)
           (mk stmts' rmap)
  .
  Hint Constructors step.
End State.
End State.
