Require Import NArith.
Require Import PArith.
Require Import ZArith.
Require Import Lia.
Require Import sflib.
Require Import HahnRelationsBasic.

Require Import PromisingArch.lib.Basic.
Require Import PromisingArch.lib.Order.

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

Lemma minimalize_cycle
      A a
      (pred: A -> Prop)
      (rel: relation A)
      (MERGE: forall a b c, rel a b -> rel b c -> ~ pred b -> rel a c)
      (CYCLE: rel⁺ a a):
  (exists a, (fun a b => rel a b /\ pred a /\ pred b)⁺ a a) \/
  (exists a, ~ pred a /\ rel a a).
Proof.
  apply tc_rtcn in CYCLE. des. revert a CYCLE CYCLE0.
  induction n using strong_nat_ind. i. rename H into IH.
  match goal with
  | [|- ?g] => remember g as goal eqn:GOAL; guardH GOAL
  end.
  assert (REDUCE: forall a, rtcn rel n a a -> ~ pred a -> goal).
  { i. des. inv H; [lia|]. apply rtcn_inv in A23.
    unguardH GOAL. inv A23; eauto. apply rtcn_inv in A1.
    exploit IH.
    2: { econs 2; [|exact A1].  eauto. }
    all: ss. lia.
  }
  destruct (classic (pred a)); cycle 1.
  { eapply REDUCE; eauto. }
  rename H into PREDA.
  cut (goal \/ rtcn (fun a b => rel a b /\ pred a /\ pred b) n a a).
  { i. des; ss. unguardH GOAL. subst. left. esplits.
    eapply rtcn_tc; eauto.
  }
  cut (n <= n -> goal \/ exists b, rtcn (fun a b => rel a b /\ pred a /\ pred b) n a b /\ rtcn rel (n - n) b a).
  { i. exploit H; eauto. i. des; eauto.
    rewrite Nat.sub_diag in *. inv x0. eauto.
  }
  generalize n at 1 3 5 as m. induction m.
  { right. esplits; eauto. rewrite Nat.sub_0_r. ss. }
  i. exploit IHm; [lia|]. i. des; eauto. inv x0; [lia|].
  replace n with (S n0 + m) in * by lia. clear H1 H CYCLE0.
  replace (S n0 + m - S m) with n0 by lia.
  destruct (classic (pred b)); cycle 1.
  { left. eapply REDUCE; [|exact H]. eapply rtcn_app; eauto.
    eapply rtcn_imply; [|exact x]. s. i. des. ss.
  }
  destruct (classic (pred a2)); cycle 1.
  { left. eapply REDUCE; [|exact H0].
    replace (S n0 + m) with (n0 + S m) by lia.
    eapply rtcn_app; eauto. eapply rtcn_snoc; eauto.
    eapply rtcn_imply; [|exact x]. s. i. des. ss.
  }
  right. esplits; eauto. eapply rtcn_snoc; eauto.
Qed.
