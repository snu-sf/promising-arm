Require Import NArith.
Require Import PArith.
Require Import Lia.
Require Import FMapPositive.
Require Import FSetPositive.
Require Import sflib.
Require Import EquivDec.

Require Import Order.

Set Implicit Arguments.

Module Id := Pos.
Module IdMap := PositiveMap.
Module IdSet := PositiveSet.

Module Val := Nat.
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


Module Time.
  Include Nat.

  Definition le (a b:t) := a <= b.
  Definition join (a b:t) := max a b.
  Definition bot: t := 0.

  Program Instance order: orderC join bot.
  Next Obligation. unfold join. lia. Qed.
  Next Obligation. unfold join. lia. Qed.
  Next Obligation. eauto using Max.max_assoc. Qed.
  Next Obligation. eauto using Max.max_comm. Qed.
  Next Obligation. unfold join. lia. Qed.
  Next Obligation. unfold bot. lia. Qed.

  Instance eqdec: EqDec t eq := nat_eq_eqdec.
End Time.

Module View := Time.

Module ValV.
  Inductive t := mk {
    val: Val.t;
    view: View.t;
  }.
  Hint Constructors t.
End ValV.

Module RMap.
  Definition t := IdMap.t ValV.t.

  Definition find (reg:Id.t) (rmap:t): ValV.t :=
    match IdMap.find reg rmap with
    | Some v => v
    | None => ValV.mk 0 bot
    end.
End RMap.

Fixpoint sem_expr (rmap:RMap.t) (e:exprT): ValV.t :=
  match e with
  | expr_const const => ValV.mk const bot
  | expr_reg reg => RMap.find reg rmap
  | expr_op1 op e1 => ValV.mk 0 bot (* TODO *)
  | expr_op2 op e1 e2 => ValV.mk 0 bot (* TODO *)
  end.

Module Event.
  Inductive t :=
  | internal
  | read (ex:bool) (ord:ordT) (vloc:ValV.t) (res:ValV.t)
  | write (ex:bool) (ord:ordT) (vloc:ValV.t) (vval:ValV.t) (res:ValV.t)
  | barrier (b:Barrier.t)
  | ctrl (view:View.t)
  .
End Event.

Module State.
  Inductive t := mk {
    stmt: list stmtT;
    rmap: RMap.t;
  }.

  Inductive step: forall (e:Event.t) (st1 st2:t), Prop :=
  | step_skip
      stmts rmap:
      step Event.internal (mk ((stmt_instr instr_skip)::stmts) rmap) (mk stmts rmap)
  | step_assign
      lhs rhs stmts rmap:
      step Event.internal (mk ((stmt_instr (instr_assign lhs rhs))::stmts) rmap) (mk stmts rmap) (* TODO *)
  | step_load
      ex o res eloc stmts rmap:
      step Event.internal (mk ((stmt_instr (instr_load ex o res eloc))::stmts) rmap) (mk stmts rmap) (* TODO *)
  | step_store
      ex o res eloc eval stmts rmap:
      step Event.internal (mk ((stmt_instr (instr_store ex o res eloc eval))::stmts) rmap) (mk stmts rmap) (* TODO *)
  | step_barrier
      b stmts rmap:
      step (Event.barrier b) (mk ((stmt_instr (instr_barrier b))::stmts) rmap) (mk stmts rmap)
  | step_if
      cond vcond s1 s2 stmts rmap
      (COND: vcond = sem_expr rmap cond):
      step (Event.ctrl vcond.(ValV.view)) (mk ((stmt_if cond s1 s2)::stmts) rmap) (mk ((if vcond.(ValV.val) <> 0 then s1 else s2) ++ stmts) rmap)
  | step_dowhile
      s cond stmts rmap:
      step Event.internal (mk ((stmt_dowhile s cond)::stmts) rmap) (mk (s ++ [stmt_if cond ((stmt_dowhile s cond) :: stmts) stmts]) rmap)
  .
End State.
