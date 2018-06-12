Require Import Relations.
Require Import EquivDec.
Require Import Equality.
Require Import List.
Require Import Bool.
Require Import Lia.
Require Import NArith.
Require Import PArith.
Require Import ZArith.
Require Import FMapPositive.
Require Import FSetPositive.
Require Import EquivDec.
Require Import sflib.

Require Import Basic.
Require Import Order.
Require Import Time.
Require Import Lang.
Require Import Promising.
Require Import Certify.

Set Implicit Arguments.


Lemma no_promise_certify_init
      tid (eu:ExecUnit.t (A:=unit))
      (PROMISES: eu.(ExecUnit.local).(Local.promises) = bot):
  certify tid eu Lock.init.
Proof.
  econs; eauto. s. funext. i. propext. econs; ss.
  intro X. inv X. inv R.
Qed.

Lemma no_promise_certify_inv
      tid (eu:ExecUnit.t (A:=unit)) l
      (PROMISES: eu.(ExecUnit.local).(Local.promises) = bot)
      (CERTIFY: certify tid eu l):
  l = Lock.init.
Proof.
  destruct l. inv CERTIFY. ss. subst. inv STEPS.
  - ss. unfold Lock.init. f_equal. funext. i. propext. econs; i; ss.
    inv H. inv R.
  - inv H; inv STEP; ss.
Qed.

Inductive void_taint (v:Taint.t): Prop :=
| void_taint_intro
    (TAINT: forall from to loc, ~ v (Taint.W from to loc))
.

Inductive void_view (v:View.t (A:=Taint.t)): Prop :=
| void_view_intro
    (VIEW: void_taint v.(View.annot))
.

Inductive void_val (v:ValA.t (A:=View.t (A:=Taint.t))): Prop :=
| void_val_intro
    (VAL: void_view v.(ValA.annot))
.

Inductive void_rmap (rmap:RMap.t (A:=View.t (A:=Taint.t))): Prop :=
| void_rmap_intro
    (RMAP: IdMap.Forall (fun _ => void_val) rmap)
.

Inductive void_lc (tid:Id.t) (lc:Local.t (A:=Taint.t)) (mem:Memory.t): Prop :=
| void_lc_intro
    (VRP: void_view lc.(Local.vrp))
    (VWP: void_view lc.(Local.vwp))
    (VRM: void_view lc.(Local.vrm))
    (VWM: void_view lc.(Local.vwm))
    (VCAP: void_view lc.(Local.vcap))
    (VREL: void_view lc.(Local.vrel))
    (FWDBANK: forall l fwd (FWD: lc.(Local.fwdbank) l = Some fwd), void_view fwd.(FwdItem.view))
.

Inductive void_aeu (tid:Id.t) (aeu:AExecUnit.t): Prop :=
| void_aeu_intro
    (ST: void_rmap aeu.(ExecUnit.state).(State.rmap))
    (LC: void_lc tid aeu.(ExecUnit.local) aeu.(ExecUnit.mem))
    (TAINT: void_taint aeu.(AExecUnit.aux).(AExecUnit.taint))
    (RELEASE: aeu.(AExecUnit.aux).(AExecUnit.release) = bot)
.

Lemma void_taint_join
      l r
      (L: void_taint l)
      (R: void_taint r):
  void_taint (join l r).
Proof.
  inv L. inv R. econs. ii. inv H.
  - eapply TAINT. eauto.
  - eapply TAINT0. eauto.
Qed.

Lemma void_taint_bot:
  void_taint bot.
Proof.
  econs. ss.
Qed.

Lemma void_view_join
      v1 v2
      (V1: void_view v1)
      (V2: void_view v2):
  void_view (join v1 v2).
Proof.
  inv V1. inv V2. econs. eapply void_taint_join; eauto.
Qed.

Lemma void_view_bot:
  void_view bot.
Proof.
  econs. apply void_taint_bot.
Qed.

Lemma void_rmap_expr
      rmap e
      (RMAP: void_rmap rmap):
  void_view (sem_expr rmap e).(ValA.annot).
Proof.
  induction e; ss.
  - apply void_view_bot.
  - unfold RMap.find. destruct (IdMap.find reg rmap) eqn:V.
    + eapply RMAP. eauto.
    + apply void_view_bot.
  - apply void_view_join; ss.
Qed.

Lemma void_rmap_add
      l v rmap
      (RMAP: void_rmap rmap)
      (V: void_val v):
  void_rmap (RMap.add l v rmap).
Proof.
  inv RMAP. econs. ii. revert FIND.
  unfold RMap.add. rewrite IdMap.add_spec. condtac.
  - inversion e. i. inv FIND. ss.
  - apply RMAP0.
Qed.

Lemma void_aeu_step
      tid aeu1 aeu2
      (STEP: AExecUnit.state_step tid aeu1 aeu2)
      (SOUND: void_aeu tid aeu1):
  void_aeu tid aeu2.
Proof.
  destruct aeu1 as [[st1 lc1 mem1] aux1].
  destruct aeu2 as [[st2 lc2 mem2] aux2].
  inv STEP. inv STEP0. inv SOUND. ss. subst.
  inv LOCAL; ss; inv STATE; ss.
  - econs; ss.
    inv LC0. inv LC. econs; eauto using void_view_join, void_view_bot, void_rmap_expr.
  - econs; ss.
    + apply void_rmap_add; ss. econs. apply void_rmap_expr. ss.
    + inv LC0. inv LC. econs; eauto using void_view_join, void_view_bot, void_rmap_expr.
  - econs; ss.
    inv LC0. inv LC. econs; eauto using void_view_join, void_view_bot, void_rmap_expr.
  - econs; ss.
    inv LC0. inv LC. econs; eauto using void_view_join, void_view_bot, void_rmap_expr.
  - inv STEP. ss. econs; ss.
    + apply void_rmap_add; ss. econs. econs. s.
      admit.
    + inv LC. econs; s; eauto using void_view_join, void_view_bot, void_rmap_expr.
      all: admit.
    + destruct ex; ss.
    + destruct ex; ss.
  - inv STEP. ss. econs; ss.
    + apply void_rmap_add; ss. econs. admit. (* view_ext *)
    + inv LC. econs; s; eauto using void_view_join, void_view_bot, void_rmap_expr.
      all: admit.
    + admit.
  - inv STEP. econs; ss.
    + apply void_rmap_add; ss. econs; eauto using void_view_join, void_view_bot, void_rmap_expr.
    + inv LC. econs; eauto using void_view_join, void_view_bot, void_rmap_expr.
    + eauto using void_taint_join, void_taint_bot.
  - inv STEP. econs; ss.
    inv LC. econs; s; eauto using void_view_join, void_view_bot, void_rmap_expr.
  - inv STEP. econs; ss.
    inv LC. econs; s; eauto using void_view_join, void_view_bot, void_rmap_expr.
  - inv STEP. econs; ss.
    inv LC. econs; s; eauto using void_view_join, void_view_bot, void_rmap_expr.
  - inv STEP. econs; ss.
    inv LC. econs; s; eauto using void_view_join, void_view_bot, void_rmap_expr.
Admitted.

Lemma void_rtc_aeu_step
      tid aeu1 aeu2
      (STEP: rtc (AExecUnit.state_step tid) aeu1 aeu2)
      (SOUND: void_aeu tid aeu1):
  void_aeu tid aeu2.
Proof.
  revert SOUND. induction STEP; ss. i.
  exploit void_aeu_step; eauto.
Qed.

Lemma rtc_state_step_certify_bot
      tid (eu1 eu2:ExecUnit.t (A:=unit))
      (STEPS: rtc (ExecUnit.state_step tid) eu1 eu2)
      (NOPROMISE: eu2.(ExecUnit.local).(Local.promises) = bot):
  certify tid eu1 Lock.init.
Proof.
(* TODO:
 - define eqts
 - lift_state_step: eu state step -> aeu state step
 *)
Admitted.
