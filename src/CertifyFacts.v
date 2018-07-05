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

Section Eqts.
  Context `{A: Type, B: Type, _: orderC A eq, _: orderC B eq}.

  Inductive eqts_rmap (rmap1: RMap.t (A:=View.t (A:=A))) (rmap2: RMap.t (A:=View.t (A:=B))): Prop :=
  | eqts_rmap_intro
      (RMAP: IdMap.Forall2 (fun _ => eqts_val) rmap1 rmap2)
  .
  Hint Constructors eqts_rmap.

  Inductive eqts_st (st1: State.t (A:=View.t (A:=A))) (st2: State.t (A:=View.t (A:=B))): Prop :=
  | eqts_st_intro
      (STMTS: st1.(State.stmts) = st2.(State.stmts))
      (RMAP: eqts_rmap st1.(State.rmap) st2.(State.rmap))
  .
  Hint Constructors eqts_st.

  Inductive eqts_lc (lc1: Local.t (A:=A)) (lc2: Local.t (A:=B)): Prop :=
  | eqts_lc_intro
      (COH: forall loc, lc1.(Local.coh) loc = lc2.(Local.coh) loc)
      (VRP: eqts_view lc1.(Local.vrp) lc2.(Local.vrp))
      (VWP: eqts_view lc1.(Local.vwp) lc2.(Local.vwp))
      (VRM: eqts_view lc1.(Local.vrm) lc2.(Local.vrm))
      (VWM: eqts_view lc1.(Local.vwm) lc2.(Local.vwm))
      (VCAP: eqts_view lc1.(Local.vcap) lc2.(Local.vcap))
      (VREL: eqts_view lc1.(Local.vrel) lc2.(Local.vrel))
      (FWDBANK: forall loc, opt_rel eqts_fwd (lc1.(Local.fwdbank) loc) (lc2.(Local.fwdbank) loc))
      (EXBANK: lc1.(Local.exbank) = lc2.(Local.exbank))
      (PROMISES: lc1.(Local.promises) = lc2.(Local.promises))
  .
  Hint Constructors eqts_lc.

  Inductive eqts_eu (eu1: ExecUnit.t (A:=A)) (eu2: ExecUnit.t (A:=B)): Prop :=
  | eqts_eu_intro
      (ST: eqts_st eu1.(ExecUnit.state) eu2.(ExecUnit.state))
      (LC: eqts_lc eu1.(ExecUnit.local) eu2.(ExecUnit.local))
      (MEM: eu1.(ExecUnit.mem) = eu2.(ExecUnit.mem))
  .
  Hint Constructors eqts_eu.

  Lemma eqts_view_join
        (l1 l2:View.t (A:=A)) (r1 r2:View.t (A:=B))
        (EQTS1: eqts_view l1 r1)
        (EQTS2: eqts_view l2 r2):
    eqts_view (join l1 l2) (join r1 r2).
  Proof.
    inv EQTS1. inv EQTS2. econs. ss. congr.
  Qed.

  Lemma eqts_view_ifc
        c (l1:View.t (A:=A)) (r1:View.t (A:=B))
        (EQTS: eqts_view l1 r1):
    eqts_view (ifc c l1) (ifc c r1).
  Proof.
    destruct c; ss.
  Qed.

  Lemma eqts_view_bot:
    eqts_view (A:=A) (B:=B) bot bot.
  Proof.
    econs. ss.
  Qed.

  Lemma eqts_rmap_add
        (rmap1:RMap.t (A:=View.t (A:=A)))
        (rmap2:RMap.t (A:=View.t (A:=B)))
        x
        (l1:ValA.t (A:=View.t (A:=A)))
        (l2:ValA.t (A:=View.t (A:=B)))
        (RMAP: eqts_rmap rmap1 rmap2)
        (VAL: eqts_val l1 l2):
    eqts_rmap (RMap.add x l1 rmap1) (RMap.add x l2 rmap2).
  Proof.
    inv RMAP. econs. ii. unfold RMap.add. rewrite ? IdMap.add_spec.
    condtac; ss. inversion e. subst. econs. ss.
  Qed.

  Lemma eqts_rmap_expr
        (rmap1:RMap.t (A:=View.t (A:=A)))
        (rmap2:RMap.t (A:=View.t (A:=B)))
        (RMAP: eqts_rmap rmap1 rmap2)
        e:
    eqts_val (sem_expr rmap1 e) (sem_expr rmap2 e).
  Proof.
    induction e; ss.
    - inv RMAP. specialize (RMAP0 reg). unfold RMap.find. inv RMAP0; ss.
    - inv IHe. econs; ss. rewrite VAL. ss.
    - inv IHe1. inv IHe2. econs; ss; eauto using eqts_view_join.
      rewrite VAL, VAL0. ss.
  Qed.

  Lemma eqts_eu_state_step
        tid (eu1:ExecUnit.t (A:=A)) (eu2 eu2':ExecUnit.t (A:=B))
        (STEP: ExecUnit.state_step tid eu2 eu2')
        (EQTS: eqts_eu eu1 eu2):
    exists eu1',
      <<STEP: ExecUnit.state_step tid eu1 eu1'>> /\
      <<EQTS: eqts_eu eu1' eu2'>>.
  Proof.
    destruct eu1 as [[stmts1 rmap1] lc1 mem1].
    destruct eu2 as [[stmts2 rmap2] lc2 mem2].
    destruct eu2' as [[stmts2' rmap2'] lc2' mem2'].
    inv STEP. inv STEP0. ss. subst.
    inv EQTS. inv ST. inv LC. ss. subst.
    inv STATE; inv LOCAL; inv EVENT; ss.
    - inv LC. eexists (ExecUnit.mk _ _ _). splits.
      + econs. econs; ss.
        * econs 1; ss.
        * econs 1; ss.
      + econs; ss. econs; eauto using eqts_view_join, eqts_view_bot.
    - inv LC. eexists (ExecUnit.mk _ _ _). splits.
      + econs. econs; ss.
        * econs 2; ss.
        * econs 1; ss.
      + econs; ss.
        * econs; ss. eauto using eqts_rmap_add, eqts_rmap_expr.
        * econs; eauto using eqts_view_join, eqts_view_bot.
    - generalize (eqts_rmap_expr RMAP eloc). intro X. inv X.
      inv STEP. eexists (ExecUnit.mk _ _ _). splits.
      + econs. econs; ss.
        * econs 3; ss.
        * generalize (eqts_rmap_expr RMAP eloc). intro X. inv X.
          econs 2; ss.
          rewrite <- COH, <- VAL in COH0. econs; eauto.
          { match goal with
            | [H: Memory.latest ?a ?b ?c ?d |- Memory.latest ?e ?f ?g ?h] =>
              replace (Memory.latest e f g h) with (Memory.latest a b c d); ss
            end.
            f_equal; ss. symmetry.
            f_equal; [by apply VIEW|].
            f_equal; [by apply VRP|].
            f_equal. destruct (OrdR.ge ord OrdR.acquire); ss. apply VREL.
          }
          { rewrite VAL. eauto. }
      + assert (FWD: eqts_view
                       match Local.fwdbank lc1 (ValA.val (sem_expr rmap1 eloc)) with
                       | Some fwd => FwdItem.read_view fwd ts ord
                       | None => {| View.ts := ts; View.annot := bot |}
                       end
                       match Local.fwdbank lc2 (ValA.val (sem_expr rmap2 eloc)) with
                       | Some fwd => FwdItem.read_view fwd ts ord
                       | None => {| View.ts := ts; View.annot := bot |}
                       end).
        { rewrite VAL. generalize (FWDBANK (ValA.val (sem_expr rmap2 eloc))). intro X. inv X; ss.
          inv REL. unfold FwdItem.read_view. rewrite TS, EX. condtac; ss.
        }
        econs; ss.
        * econs; ss. apply eqts_rmap_add; ss.
          econs; ss. repeat apply eqts_view_join; eauto using eqts_view_ifc, eqts_view_bot.
        * econs; ss.
          { i. rewrite ? fun_add_spec, VAL. condtac; ss. }
          all: repeat (try apply eqts_view_join; try apply eqts_view_ifc; ss).
          destruct ex0; ss. rewrite VAL. ss.
    - generalize (eqts_rmap_expr RMAP eloc). intro X. inv X.
      generalize (eqts_rmap_expr RMAP eval). intro X. inv X.
      inv STEP. eexists (ExecUnit.mk _ _ _). splits.
      + econs. econs; ss.
        * econs 4; ss.
        * econs 3; ss. econs; ss.
          { instantiate (2 := ts). inv WRITABLE. econs; ss.
            - rewrite VAL, COH. ss.
            - ss.
              match goal with
              | [H: ?a < ts |- ?b <ts] =>
                replace b with a; ss
              end.
              repeat (match goal with
                      | [|- join _ _ = join _ _] => f_equal
                      | [|- ifc _ _ = ifc _ _] => f_equal
                      end; ss).
              + inv VIEW. ss.
              + inv VIEW0. ss.
              + inv VCAP. ss.
              + inv VWP. ss.
              + inv VRM. destruct (OrdW.ge ord OrdW.release); ss.
              + inv VWM. destruct (OrdW.ge ord OrdW.release); ss.
            - rewrite VAL, EXBANK. eauto.
          }
          { rewrite MSG. f_equal. f_equal; ss. }
      + econs; ss.
        * econs; ss. apply eqts_rmap_add; ss.
        * econs; ss.
          { i. rewrite ? fun_add_spec, VAL. condtac; ss. }
          all: repeat (try apply eqts_view_join; try apply eqts_view_ifc; ss).
          { i. rewrite ? fun_add_spec, VAL. condtac; ss. econs. econs; eauto using eqts_view_join. }
          { destruct ex0; ss. }
          { congr. }
    - inv STEP. eexists (ExecUnit.mk _ _ _). splits.
      + econs. econs; ss.
        * econs 4; ss.
        * econs 4; ss.
      + econs; ss.
        econs; ss. apply eqts_rmap_add; ss.
    - inv STEP. eexists (ExecUnit.mk _ _ _). splits.
      + econs. econs; ss.
        * econs 5; ss.
        * econs 5; ss.
      + econs; ss.
        econs; eauto using eqts_view_join, eqts_view_bot.
    - inv STEP. eexists (ExecUnit.mk _ _ _). splits.
      + econs. econs; ss.
        * econs 5; ss.
        * econs 6; ss.
      + econs; ss.
        econs; eauto 10 using eqts_view_join, eqts_view_ifc, eqts_view_bot.
    - inv LC. eexists (ExecUnit.mk _ _ _). splits.
      + econs. econs; ss.
        * econs 6; ss.
        * econs 1; ss.
      + generalize (eqts_rmap_expr RMAP cond). intro X. inv X.
        econs; ss.
        * econs; ss. rewrite VAL. ss.
        * econs; ss. eauto using eqts_view_join, eqts_view_bot.
    - inv LC. eexists (ExecUnit.mk _ _ _). splits.
      + econs. econs; ss.
        * econs 7; ss.
        * econs 1; ss.
      + econs; ss.
        econs; eauto using eqts_view_join, eqts_view_bot.
  Qed.
End Eqts.

Lemma eqts_rmap_refl
      `{A: Type, _: orderC A eq}
      (rmap:RMap.t (A:=View.t (A:=A))):
  eqts_rmap rmap rmap.
Proof.
  econs. ii. destruct (IdMap.find id rmap); ss. econs.
  econs; ss.
Qed.

Lemma eqts_eu_init tid eu:
  eqts_eu (AExecUnit.init tid eu) eu.
Proof.
  econs; ss.
  - econs; ss. unfold AExecUnit.init_rmap. econs. ii.
    rewrite IdMap.map_spec. destruct (IdMap.find id (State.rmap (ExecUnit.state eu))); ss.
    econs. econs; ss.
  - unfold AExecUnit.init_lc, AExecUnit.init_view. econs; ss.
    i. destruct (Local.fwdbank (ExecUnit.local eu) loc); ss. econs. econs; ss.
Qed.

Lemma lift_state_step
      aux (e:Event.t (A:=View.t (A:=Taint.t))) st1 st2
      (STEP: State.step e st1 st2):
  exists st2',
    <<STEP: State.step (AExecUnit.taint_read_event aux e) st1 st2'>> /\
    <<EQTS: eqts_st st2 st2'>>.
Proof.
  inv STEP.
  - eexists (State.mk _ _). splits.
    + econs 1; eauto.
    + econs; ss. apply eqts_rmap_refl.
  - eexists (State.mk _ _). splits.
    + econs 2; eauto.
    + econs; ss. apply eqts_rmap_add; ss. apply eqts_rmap_refl.
  - eexists (State.mk _ _). splits.
    + econs 3; eauto.
    + econs; ss. apply eqts_rmap_add; ss. apply eqts_rmap_refl.
  - eexists (State.mk _ _). splits.
    + econs 4; eauto.
    + econs; ss. apply eqts_rmap_add; ss. apply eqts_rmap_refl.
  - eexists (State.mk _ _). splits.
    + econs 5; eauto.
    + econs; ss. apply eqts_rmap_refl.
  - eexists (State.mk _ _). splits.
    + econs 6; eauto.
    + econs; ss. apply eqts_rmap_refl.
  - eexists (State.mk _ _). splits.
    + econs 7; eauto.
    + econs; ss. apply eqts_rmap_refl.
Qed.

Lemma lift_eu_state_step
      tid (eu1 eu2:ExecUnit.t (A:=unit))
      (STEP: ExecUnit.state_step tid eu1 eu2)
      (eu1': AExecUnit.t)
      (PROMISES: Local.promises (ExecUnit.local eu1') <> bot)
      (EQTS: eqts_eu eu1' eu1):
  exists eu2',
    <<STEP: AExecUnit.state_step tid eu1' eu2'>> /\
    <<EQTS: eqts_eu eu2' eu2>>.
Proof.
  generalize (eqts_eu_state_step STEP EQTS). i. des.
  inv STEP0. inv STEP1. destruct eu1'0 as [st1' lc1' mem1']. ss.
  exploit lift_state_step; eauto. i. des.
  eexists (AExecUnit.mk (ExecUnit.mk _ lc1' mem1') _). ss. esplits.
  - econs; ss. econs; eauto.
  - destruct eu2 as [st2 lc2 mem2].
    inv EQTS0. econs; ss.
    destruct st1' as [stmts1' rmap1'].
    destruct st2' as [stmts2' rmap2'].
    destruct st2 as [stmts2 rmap2].
    inv EQTS1. inv ST. ss. subst. econs; ss.
    inv RMAP. inv RMAP0. econs. ii.
    specialize (RMAP1 id). specialize (RMAP id). revert RMAP1 RMAP.
    destruct (IdMap.find id rmap1'), (IdMap.find id rmap2'), (IdMap.find id rmap2);
      i; inv RMAP1; inv RMAP; ss.
    econs. destruct t, t0, t1. inv REL. inv REL0. ss. subst.
    econs; ss. inv VIEW. inv VIEW0. econs. congr.
Qed.

Lemma lift_rtc_eu_state_step
      tid (eu1 eu2:ExecUnit.t (A:=unit))
      (STEP: rtc (ExecUnit.state_step tid) eu1 eu2)
      (eu1': AExecUnit.t)
      (EQTS: eqts_eu eu1' eu1):
  exists eu2',
    <<STEP: rtc (AExecUnit.state_step tid) eu1' eu2'>> /\
    <<EQTS: __guard__ (eqts_eu eu2' eu2 \/ Local.promises (ExecUnit.local eu2') = bot)>>.
Proof.
  revert eu1' EQTS. induction STEP; i.
  { esplits; eauto. left. ss. }
  destruct (classic (Local.promises (ExecUnit.local eu1') = bot)).
  { esplits; eauto. right. ss. }
  exploit lift_eu_state_step; eauto. i. des.
  exploit IHSTEP; eauto. i. des.
  esplits.
  - econs 2; eauto.
  - eauto.
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

Lemma void_taint_ifc
      c v
      (V: void_taint v):
  void_taint (ifc c v).
Proof.
  unfold ifc. condtac; ss. apply void_taint_bot.
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

Lemma void_view_ifc
      c v
      (V: void_view v):
  void_view (ifc c v).
Proof.
  unfold ifc. condtac; ss. apply void_view_bot.
Qed.

Lemma void_view_const ts:
  void_view (View.mk ts bot).
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

Lemma void_aeu_init
      tid eu:
  void_aeu tid (AExecUnit.init tid eu).
Proof.
  econs; ss; eauto using void_taint_bot.
  - unfold AExecUnit.init_rmap. econs. ii. revert FIND.
    rewrite IdMap.map_spec. destruct (IdMap.find id (State.rmap (ExecUnit.state eu))); ss.
    i. inv FIND. econs. eauto using void_view_const.
  - unfold AExecUnit.init_lc, AExecUnit.init_view.
    econs; ss; eauto using void_view_const.
    + econs. econs. s. ii. destruct (Local.exbank (ExecUnit.local eu)) as [[]|] eqn:EX; ss.
    + i. revert FWD. destruct (Local.fwdbank (ExecUnit.local eu) l); ss. i. inv FWD.
      eauto using void_view_const.
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
  - inv STEP. ss.
    assert (FWD:
              void_view
                (match Local.fwdbank lc1 (ValA.val (sem_expr rmap eloc)) with
                 | Some fwd => FwdItem.read_view fwd ts ord
                 | None => {| View.ts := ts; View.annot := bot |}
                 end)).
    { destruct (Local.fwdbank lc1 (ValA.val (sem_expr rmap eloc))) eqn:FWD;
        eauto using void_view_const.
      unfold FwdItem.read_view. condtac; eauto using void_view_const.
      eapply LC. eauto.
    }
    econs; ss.
    + apply void_rmap_add; ss. econs. econs. s.
      repeat apply void_taint_join.
      * apply void_rmap_expr. ss.
      * apply LC.
      * unfold ifc. condtac; eauto using void_taint_bot. apply LC.
      * eauto using void_taint_bot.
      * apply FWD.
      * destruct ex; ss. apply void_taint_bot.
    + inv LC. econs; s; repeat apply void_view_join;
        eauto 10 using void_view_join, void_view_ifc, void_view_bot, void_rmap_expr.
    + destruct ex; ss.
    + destruct ex; ss.
  - inv STEP. ss.
    assert (VIEW_EXT: void_taint (View.annot view_ext)).
    { inv WRITABLE. s.
      repeat apply void_taint_join.
      all: try by apply void_rmap_expr.
      all: try (unfold ifc; condtac).
      all: try by apply void_taint_bot.
      all: try by apply LC.
    }
    econs; ss.
    + apply void_rmap_add; ss.
    + inv LC. econs; s; eauto using void_view_join, void_view_bot, void_view_const, void_rmap_expr.
      i. revert FWD. rewrite fun_add_spec. condtac; eauto. i.
      inversion e. inv FWD. s.
      eauto using void_view_join, void_view_bot, void_view_const, void_rmap_expr.
    + apply void_taint_join; ss.
  - inv STEP. econs; ss.
    + apply void_rmap_add; ss. econs; eauto using void_view_join, void_view_bot, void_rmap_expr.
    + inv LC. econs; eauto using void_view_join, void_view_bot, void_rmap_expr.
    + eauto using void_taint_join, void_taint_bot.
  - inv STEP. econs; ss.
    inv LC. econs; s; eauto using void_view_join, void_view_bot, void_rmap_expr.
  - inv STEP. econs; ss.
    inv LC. econs; s; eauto 20 using void_view_join, void_view_ifc, void_view_bot, void_rmap_expr.
Qed.

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
  exploit lift_rtc_eu_state_step; eauto.
  { apply eqts_eu_init. }
  i. des.
  exploit void_rtc_aeu_step; eauto.
  { apply void_aeu_init. }
  i. econs.
  - eapply rtc_mon; [|by eauto]. left. ss.
  - unguardH EQTS. des; ss. inv EQTS. inv LC. rewrite PROMISES. ss.
  - funext. i. propext. econs; i; ss. inv H.
    inv x0. inv TAINT. eapply TAINT0. eauto.
  - inv x0. rewrite RELEASE. ss.
Qed.
