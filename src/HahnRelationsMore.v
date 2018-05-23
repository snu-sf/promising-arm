Require Import sflib.
Require Import HahnRelationsBasic.

Require Import Basic.
Require Import Order.

Set Implicit Arguments.


Lemma seq_assoc A (r1 r2 r3:relation A):
  r1 ⨾ (r2 ⨾ r3) = (r1 ⨾ r2) ⨾ r3.
Proof.
  funext. i. funext. i. propext. econs; i.
  - inv H. des. inv H1. des. repeat econs; eauto.
  - inv H. des. inv H0. des. repeat econs; eauto.
Qed.

Lemma seq_union A (r1 r2 r3:relation A):
  r1 ⨾ (r2 ∪ r3) = (r1 ⨾ r2) ∪ (r1 ⨾ r3).
Proof.
  funext. i. funext. i. propext. econs; i.
  - inv H. des. inv H1.
    + left. econs; eauto.
    + right. econs; eauto.
  - inv H; inv H0; des.
    + econs; esplits; eauto. left. ss.
    + econs; esplits; eauto. right. ss.
Qed.

Lemma seq_union' A (r2 r3 r1:relation A):
  r1 ⨾ (r2 ∪ r3) = (r1 ⨾ r2) ∪ (r1 ⨾ r3).
Proof.
  apply seq_union.
Qed.

Lemma union_seq A (r1 r2 r3:relation A):
  (r1 ∪ r2) ⨾ r3 = (r1 ⨾ r3) ∪ (r2 ⨾ r3).
Proof.
  funext. i. funext. i. propext. econs; i.
  - inv H. des. inv H0.
    + left. econs; eauto.
    + right. econs; eauto.
  - inv H; inv H0; des.
    + econs; esplits; eauto. left. ss.
    + econs; esplits; eauto. right. ss.
Qed.

Lemma union_seq' A (r3 r1 r2:relation A):
  (r1 ∪ r2) ⨾ r3 = (r1 ⨾ r3) ∪ (r2 ⨾ r3).
Proof.
  apply union_seq.
Qed.

Lemma clos_refl_union
      A (r:relation A):
  r^? = r ∪ eq.
Proof.
  funext. i. funext. i. propext. econs; i.
  - inv H; [right|left]; ss.
  - inv H; [right|left]; ss.
Qed.

Lemma eq_seq
      A (r:relation A):
  eq ⨾ r = r.
Proof.
  funext. i. funext. i. propext. econs; i.
  - inv H. des. subst. ss.
  - econs; eauto.
Qed.

Lemma union_assoc A (r1 r2 r3: relation A):
  r1 ∪ (r2 ∪ r3) = (r1 ∪ r2) ∪ r3.
Proof.
  funext. i. funext. i. propext. econs; i.
  - inv H; [|inv H0].
    + left. left. ss.
    + left. right. ss.
    + right. ss.
  - inv H; [inv H0|].
    + left. ss.
    + right. left. ss.
    + right. right. ss.
Qed.

Lemma union_l
      A
      (r1 r2: relation A)
      a b
      (R1: r1 a b):
  (r1 ∪ r2) a b.
Proof. left. ss. Qed.

Lemma union_r
      A
      (r1 r2: relation A)
      a b
      (R2: r2 a b):
  (r1 ∪ r2) a b.
Proof. right. ss. Qed.

Lemma cross_bot_l
      A (pred:A -> Prop):
  bot × pred = bot.
Proof.
  funext. i. funext. i. propext.
  econs; intro X; inv X. inv H.
Qed.

Lemma cross_bot_r
      A (pred:A -> Prop):
  pred × bot = bot.
Proof.
  funext. i. funext. i. propext.
  econs; intro X; inv X. inv H0.
Qed.

Lemma union_bot_l
      A (rel: relation A):
  bot ∪ rel = rel.
Proof.
  funext. i. funext. i. propext.
  econs; intro X.
  - inv X; ss.
  - right. ss.
Qed.

Lemma union_bot_r
      A (rel: relation A):
  rel ∪ bot = rel.
Proof.
  funext. i. funext. i. propext.
  econs; intro X.
  - inv X; ss.
  - left. ss.
Qed.
