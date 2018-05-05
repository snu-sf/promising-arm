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

Inductive op1 :=
| op_not
.

Inductive op2 :=
| op_add
| op_sub
| op_mul
.

Inductive expr :=
| expr_const (const:Val.t)
| expr_reg (reg:Id.t)
| expr_op1 (op:op1) (e1:expr)
| expr_op2 (op:op2) (e1 e2:expr)
.

Inductive ord :=
| pln
| rlx
| ra
.
Hint Constructors ord.

Definition ord_le (a b:ord): bool :=
  match a, b with
  | pln, _ => true
  | _, ra => true
  | rlx, rlx => true
  | _, _ => false
  end.
Hint Unfold ord_le.

Inductive barrier :=
| isb
| dmbst
| dmbld
| dmbsy
.

Inductive instr :=
| instr_skip
| instr_assign (lhs:Id.t) (rhs:expr)
| instr_load (ex:bool) (o:ord) (lhs:Id.t) (eloc:expr)
| instr_store (ex:bool) (o:ord) (succ:Id.t) (eloc:expr) (eval:expr)
| instr_barrier (b:barrier)
.

Inductive stmt :=
| stmt_instr (i:instr)
| stmt_seq (s1 s2:stmt)
| stmt_if (cond:expr) (s1 s2:stmt)
.

Definition program := IdMap.t stmt.


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

Definition rmapT := IdMap.t ValV.t.
