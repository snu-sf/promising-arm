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

Set Implicit Arguments.


Module Msg.
  Inductive t := mk {
    loc: Loc.t;
    val: Val.t;
    tid: Id.t;
  }.
  Hint Constructors t.

  Global Program Instance eqdec: EqDec t eq.
  Next Obligation.
    destruct x, y.

    destruct (loc0 == loc1); cycle 1.
    { right. intro X. inv X. intuition. }

    destruct (val0 == val1); cycle 1.
    { right. intro X. inv X. intuition. }

    destruct (tid0 == tid1); cycle 1.
    { right. intro X. inv X. intuition. }

    left. f_equal; intuition.
  Defined.
End Msg.

Module Memory.
  Definition t := list Msg.t.

  Definition empty: t := [].

  Definition read (loc:Loc.t) (ts:Time.t) (mem:t): option Val.t :=
    match Time.pred_opt ts with
    | None => Some Val.default
    | Some ts =>
      match List.nth_error mem ts with
      | None => None
      | Some msg =>
        if msg.(Msg.loc) == loc
        then Some msg.(Msg.val)
        else None
      end
    end.

  Definition get_msg (ts:Time.t) (mem:t): option Msg.t :=
    match Time.pred_opt ts with
    | None => None
    | Some ts => List.nth_error mem ts
    end.

  Definition append (msg:Msg.t) (mem:t): Time.t * t :=
    (S (length mem), mem ++ [msg]).

  Definition no_msgs (from to:nat) (pred:Msg.t -> Prop) (mem:t): Prop :=
    forall ts msg
      (TS1: from < S ts)
      (TS2: S ts <= to)
      (MSG: List.nth_error mem ts = Some msg),
      ~ pred msg.

  Definition latest (loc:Loc.t) (from to:Time.t) (mem:t): Prop :=
    Memory.no_msgs from to (fun msg => msg.(Msg.loc) = loc) mem.

  Definition exclusive (tid:Id.t) (loc:Loc.t) (from to:Time.t) (mem:t): Prop :=
    forall val (READ: Memory.read loc from mem = Some val),
      Memory.no_msgs from to (fun msg => msg.(Msg.loc) = loc /\ msg.(Msg.tid) <> tid) mem.

  Lemma read_mon ts loc val mem1 mem2
        (READ: Memory.read loc ts mem1 = Some val):
    Memory.read loc ts (mem1 ++ mem2) = Some val.
  Proof.
    revert READ. unfold Memory.read. destruct (Time.pred_opt ts); ss.
    destruct (nth_error mem1 t0) eqn:NTH; ss.
    rewrite nth_error_app1, NTH; ss.
    apply List.nth_error_Some. congr.
  Qed.

  Lemma get_msg_mon ts msg mem1 mem2
        (READ: Memory.get_msg ts mem1 = Some msg):
    Memory.get_msg ts (mem1 ++ mem2) = Some msg.
  Proof.
    revert READ. unfold Memory.get_msg. destruct (Time.pred_opt ts); ss.
    destruct (nth_error mem1 t0) eqn:NTH; ss.
    rewrite nth_error_app1, NTH; ss.
    apply List.nth_error_Some. congr.
  Qed.

  Lemma get_msg_snoc_inv
        ts mem msg m
        (GET: get_msg ts (mem ++ [msg]) = Some m):
    (ts <= length mem /\ get_msg ts mem = Some m) \/
    (ts = S (length mem) /\ msg = m).
  Proof.
    unfold get_msg in *. destruct ts; ss.
    destruct (lt_dec ts (length mem)).
    - rewrite nth_error_app1 in GET; eauto.
    - rewrite nth_error_app2 in GET; [|lia].
      destruct (ts - length mem) eqn:SUB; ss; cycle 1.
      { destruct n0; ss. }
      assert (ts = length mem) by lia. inv GET. eauto.
  Qed.
End Memory.

Module View.
Section View.
  Context `{A: Type, _: orderC A eq}.

  Inductive t := mk {
    ts: Time.t;
    annot: A;
  }.
  Hint Constructors t.

  Inductive _le (a b:t): Prop :=
  | _le_intro
      (TS: le a.(ts) b.(ts))
      (ANNOT: le a.(annot) b.(annot))
  .

  Definition _join (a b:t): t :=
    mk (join a.(ts) b.(ts)) (join a.(annot) b.(annot)).

  Definition _bot: t := mk bot bot.

  Global Program Instance preorder: PreOrder _le.
  Next Obligation. ii. econs; refl. Qed.
  Next Obligation. ii. inv H1. inv H2. econs; etrans; eauto. Qed.

  Global Program Instance partialorder: PartialOrder eq _le.
  Next Obligation.
    ii. econs.
    - i. subst. econs; refl.
    - i. destruct x, x0. inv H1. inv H2. inv H3. ss. f_equal.
      + intuition.
      + antisym; ss.
  Qed.

  Global Program Instance order:
    @orderC
      t
      eq
      _le
      _join
      _bot
      _ _ _.
  Next Obligation.
    unfold _join. destruct a, b; ss. econs; s; apply join_l.
  Qed.
  Next Obligation.
    unfold _join. destruct a, b; ss. econs; s; apply join_r.
  Qed.
  Next Obligation.
    unfold _join. destruct a, b, c; ss. f_equal; apply join_assoc.
  Qed.
  Next Obligation.
    unfold _join. destruct a, b; ss. f_equal; apply join_comm.
  Qed.
  Next Obligation.
    inv AC. inv BC. econs; s; apply join_spec; ss.
  Qed.
  Next Obligation.
    econs; apply bot_spec.
  Qed.

  Lemma ts_join a b:
    (join a b).(View.ts) = join (a.(View.ts)) (b.(View.ts)).
  Proof. destruct a, b; ss. Qed.

  Lemma ts_ifc a b:
    (ifc a b).(View.ts) = ifc a b.(View.ts).
  Proof. destruct a; ss. Qed.

  Lemma ts_bot:
    bot.(View.ts) = bot.
  Proof. ss. Qed.

  Inductive eqts (v1 v2:t): Prop :=
  | eqts_intro
      (TS: v1.(ts) = v2.(ts))
  .
  Hint Constructors eqts.

  Global Program Instance eqts_equiv: Equivalence eqts.
  Next Obligation. econs. inv H1. ss. Qed.
  Next Obligation. econs. inv H1. inv H2. etrans; eauto. Qed.
End View.
End View.

Module FwdItem.
Section FwdItem.
  Context `{A: Type, _: orderC A eq}.

  Inductive t := mk {
    ts: Time.t;
    view: View.t (A:=A);
    ex: bool;
  }.
  Hint Constructors t.

  Definition read_view (fwd:t) (tsx:Time.t) (ord:OrdR.t): View.t (A:=A) :=
    if andb (fwd.(ts) == tsx) (orb (negb fwd.(ex)) (negb (OrdR.ge ord OrdR.acquire_pc)))
    then fwd.(view)
    else View.mk tsx bot.

  Inductive eqts (fwd1 fwd2:t): Prop :=
  | eqts_intro
      (TS: fwd1.(ts) = fwd2.(ts))
      (VIEW: View.eqts fwd1.(view) fwd2.(view))
      (EX: fwd1.(ex) = fwd2.(ex))
  .
  Hint Constructors eqts.

  Global Program Instance eqts_equiv: Equivalence eqts.
  Next Obligation. econs; ss. Qed.
  Next Obligation. ii. destruct x, y. inv H1. ss. subst. econs; ss. symmetry. ss. Qed.
  Next Obligation. ii. destruct x, y, z. inv H1. inv H2. ss. subst. econs; ss. etrans; eauto. Qed.
End FwdItem.
End FwdItem.

Module Promises.
  Definition t := Id.t -> bool.

  Definition id_of_time (ts:Time.t): option positive :=
    option_map Pos.of_succ_nat (Time.pred_opt ts).

  Lemma id_of_time_inj ts ts'
        (EQ: id_of_time ts = id_of_time ts'):
    ts = ts'.
  Proof.
    revert EQ. unfold id_of_time, Time.pred_opt.
    destruct ts, ts'; ss. i. inv EQ.
    f_equal. apply SuccNat2Pos.inj. ss.
  Qed.

  Definition lookup (ts:Time.t) (promises:t): bool :=
    match id_of_time ts with
    | None => false
    | Some ts => promises ts
    end.

  Definition set (ts:Time.t) (promises:t): t :=
    match id_of_time ts with
    | None => promises
    | Some ts => fun_add ts true promises
    end.

  Lemma set_o ts' ts promises:
    lookup ts' (set ts promises) =
    if ts' == ts
    then ts' <> 0
    else lookup ts' promises.
  Proof.
    unfold lookup, set.
    destruct (id_of_time ts') eqn:X', (id_of_time ts) eqn:X, (equiv_dec ts' ts); ss;
      destruct ts, ts'; ss;
      try rewrite fun_add_spec in *.
    - inv e. rewrite X in X'. inv X'. condtac; ss. congr.
    - condtac; ss. inversion e. subst.
      rewrite <- X' in X. apply id_of_time_inj in X. inv X. intuition.
  Qed.

  Definition unset (ts:Time.t) (promises:t): t :=
    match id_of_time ts with
    | None => promises
    | Some ts => fun_add ts false promises
    end.

  Lemma unset_o ts' ts promises:
    lookup ts' (unset ts promises) =
    if ts' == ts
    then false
    else lookup ts' promises.
  Proof.
    unfold lookup, unset.
    destruct (id_of_time ts') eqn:X', (id_of_time ts) eqn:X, (equiv_dec ts' ts); ss;
      destruct ts, ts'; ss;
      try rewrite fun_add_spec in *.
    - inv e. rewrite X in X'. inv X'. condtac; intuition.
    - condtac; ss. inversion e. subst.
      rewrite <- X' in X. apply id_of_time_inj in X. inv X. intuition.
  Qed.

  Lemma set_unset a b promises
        (DIFF: a <> b):
    set a (unset b promises) = unset b (set a promises).
  Proof.
    funext. i. unfold set, unset.
    destruct a, b; ss.
    rewrite ? fun_add_spec. repeat condtac; ss.
    inversion e. inversion e0. subst.
    apply SuccNat2Pos.inj in H0. congr.
  Qed.

  Lemma lookup_bot view:
    lookup view bot = false.
  Proof.
    unfold lookup. destruct (id_of_time view); ss.
  Qed.

  Lemma ext p1 p2
        (EQ: forall i, lookup i p1 = lookup i p2):
    p1 = p2.
  Proof.
    funext. i. specialize (EQ (Pos.to_nat x)).
    unfold lookup, id_of_time in *.
    destruct (Id.eq_dec 1 x).
    { subst. ss. }
    exploit (Pos2Nat.inj_pred x); [lia|].
    destruct (Pos.to_nat x) eqn:NAT; ss.
    - destruct x; ss. destruct x; ss.
    - i. subst. rewrite Pos2SuccNat.id_succ in *.
      generalize (Pos.succ_pred_or x). i. des; [congr|].
      rewrite H in *. ss.
  Qed.
End Promises.

Module Local.
Section Local.
  Context `{A: Type, _: orderC A eq}.

  Inductive t := mk {
    coh: Loc.t -> Time.t;
    vrp: View.t (A:=A);
    vwp: View.t (A:=A);
    vrm: View.t (A:=A);
    vwm: View.t (A:=A);
    vcap: View.t (A:=A);
    vrel: View.t (A:=A);
    fwdbank: Loc.t -> option (FwdItem.t (A:=A));
    exbank: option Time.t;
    promises: Promises.t;
  }.
  Hint Constructors t.

  Definition init: t := mk bot bot bot bot bot bot bot (fun _ => None) bot bot.

  Definition init_with_promises (promises: Promises.t): Local.t :=
    mk bot bot bot bot bot bot bot (fun _ => None) bot promises.

  Inductive promise (loc:Loc.t) (val:Val.t) (tid:Id.t) (lc1:t) (mem1:Memory.t) (lc2:t) (mem2:Memory.t): Prop :=
  | promise_intro
      ts
      (LC2: lc2 =
            mk
              lc1.(coh)
              lc1.(vrp)
              lc1.(vwp)
              lc1.(vrm)
              lc1.(vwm)
              lc1.(vcap)
              lc1.(vrel)
              lc1.(fwdbank)
              lc1.(exbank)
              (Promises.set ts lc1.(promises)))
      (MEM2: Memory.append (Msg.mk loc val tid) mem1 = (ts, mem2))
  .
  Hint Constructors promise.

  Inductive internal (ctrl:View.t) (lc1 lc2:t): Prop :=
  | internal_intro
      (LC2: lc2 =
            mk
              lc1.(coh)
              lc1.(vrp)
              lc1.(vwp)
              lc1.(vrm)
              lc1.(vwm)
              (join lc1.(vcap) ctrl)
              lc1.(vrel)
              lc1.(fwdbank)
              lc1.(exbank)
              lc1.(promises))
  .
  Hint Constructors internal.

  Inductive read (ex:bool) (ord:OrdR.t) (vloc res:ValA.t (A:=View.t (A:=A))) (lc1:t) (mem1: Memory.t) (lc2:t): Prop :=
  | read_intro
      ts loc val view
      view_ext1 view_ext2
      (LOC: loc = vloc.(ValA.val))
      (VIEW: view = vloc.(ValA.annot))
      (VIEW_EXT1: view_ext1 = joins [view; lc1.(vrp); (ifc (OrdR.ge ord OrdR.acquire) lc1.(vrel))])
      (COH: le (lc1.(coh) loc) ts)
      (LATEST: Memory.latest loc ts view_ext1.(View.ts) mem1)
      (MSG: Memory.read loc ts mem1 = Some val)
      (VIEW_EXT2: view_ext2 = join view_ext1 (match lc1.(fwdbank) loc with
                                              | None => View.mk ts bot
                                              | Some fwd => fwd.(FwdItem.read_view) ts ord
                                              end))
      (RES: res = ValA.mk _ val view_ext2)
      (LC2: lc2 =
            mk
              (fun_add loc ts lc1.(coh))
              (join lc1.(vrp) (ifc (OrdR.ge ord OrdR.acquire_pc) view_ext2))
              (join lc1.(vwp) (ifc (OrdR.ge ord OrdR.acquire_pc) view_ext2))
              (join lc1.(vrm) view_ext2)
              lc1.(vwm)
              (join lc1.(vcap) view)
              lc1.(vrel)
              lc1.(fwdbank)
              (if ex then Some ts else lc1.(exbank))
              lc1.(promises))
  .
  Hint Constructors read.

  Inductive writable (ex:bool) (ord:OrdW.t) (vloc vval:ValA.t (A:=View.t (A:=A))) (tid:Id.t) (lc1:t) (mem1: Memory.t) (ts:Time.t) (view_ext:View.t (A:=A)): Prop :=
  | writable_intro
      loc val
      view_loc view_val
      (LOC: loc = vloc.(ValA.val))
      (VIEW_LOC: view_loc = vloc.(ValA.annot))
      (VAL: val = vval.(ValA.val))
      (VIEW_VAL: view_val = vval.(ValA.annot))
      (VIEW_EXT: view_ext = joins [
                                view_loc; view_val; lc1.(vcap); lc1.(vwp);
                                ifc (OrdW.ge ord OrdW.release) lc1.(vrm);
                                ifc (OrdW.ge ord OrdW.release) lc1.(vwm)
                             ])
      (COH: lt (lc1.(coh) loc) ts)
      (EXT: lt view_ext.(View.ts) ts)
      (EX: ex -> exists tsx,
           <<TSX: lc1.(exbank) = Some tsx>> /\
           <<EX: Memory.exclusive tid loc tsx ts mem1>>)
  .
  Hint Constructors writable.

  Inductive fulfill (ex:bool) (ord:OrdW.t) (vloc vval res:ValA.t (A:=View.t (A:=A))) (tid:Id.t) (lc1:t) (mem1: Memory.t) (lc2:t): Prop :=
  | fulfill_intro
      ts loc val
      view_loc view_val view_ext
      (LOC: loc = vloc.(ValA.val))
      (VIEW_LOC: view_loc = vloc.(ValA.annot))
      (VAL: val = vval.(ValA.val))
      (VIEW_VAL: view_val = vval.(ValA.annot))
      (WRITABLE: writable ex ord vloc vval tid lc1 mem1 ts view_ext)
      (MSG: Memory.get_msg ts mem1 = Some (Msg.mk loc val tid))
      (RES: res = ValA.mk _ 0 (View.mk bot view_ext.(View.annot)))
      (LC2: lc2 =
            mk
              (fun_add loc ts lc1.(coh))
              lc1.(vrp)
              lc1.(vwp)
              lc1.(vrm)
              (join lc1.(vwm) (View.mk ts bot))
              (join lc1.(vcap) view_loc)
              (join lc1.(vrel) (View.mk (ifc (OrdW.ge ord OrdW.release) ts) bot))
              (fun_add loc (Some (FwdItem.mk ts (join view_loc view_val) ex)) lc1.(fwdbank))
              (if ex then None else lc1.(exbank))
              (Promises.unset ts lc1.(promises)))
  .
  Hint Constructors fulfill.

  Inductive write_failure (ex:bool) (res: ValA.t (A:=View.t (A:=A))) (lc1:t) (lc2:t): Prop :=
  | write_failure_intro
      (EX: ex)
      (RES: res = ValA.mk _ 1 bot)
      (LC2: lc2 =
            mk
              lc1.(coh)
              lc1.(vrp)
              lc1.(vwp)
              lc1.(vrm)
              lc1.(vwm)
              lc1.(vcap)
              lc1.(vrel)
              lc1.(fwdbank)
              None
              lc1.(promises))
  .
  Hint Constructors write_failure.

  Inductive isb (lc1 lc2:t): Prop :=
  | isb_intro
      (LC2: lc2 =
            mk
              lc1.(coh)
              (join lc1.(vrp) lc1.(vcap))
              lc1.(vwp)
              lc1.(vrm)
              lc1.(vwm)
              lc1.(vcap)
              lc1.(vrel)
              lc1.(fwdbank)
              lc1.(exbank)
              lc1.(promises))
  .
  Hint Constructors isb.

  Inductive dmbst (lc1 lc2:t): Prop :=
  | dmbst_intro
      (LC2: lc2 =
            mk
              lc1.(coh)
              lc1.(vrp)
              (join lc1.(vwp) lc1.(vwm))
              lc1.(vrm)
              lc1.(vwm)
              lc1.(vcap)
              lc1.(vrel)
              lc1.(fwdbank)
              lc1.(exbank)
              lc1.(promises))
  .
  Hint Constructors dmbst.

  Inductive dmbld (lc1 lc2:t): Prop :=
  | dmbld_intro
      (LC2: lc2 =
            mk
              lc1.(coh)
              (join lc1.(vrp) lc1.(vrm))
              (join lc1.(vwp) lc1.(vrm))
              lc1.(vrm)
              lc1.(vwm)
              lc1.(vcap)
              lc1.(vrel)
              lc1.(fwdbank)
              lc1.(exbank)
              lc1.(promises))
  .
  Hint Constructors dmbld.

  Inductive dmbsy (lc1 lc2:t): Prop :=
  | dmbsy_intro
      (LC2: lc2 =
            mk
              lc1.(coh)
              (joins [lc1.(vrp); lc1.(vrm); lc1.(vwm)])
              (joins [lc1.(vwp); lc1.(vrm); lc1.(vwm)])
              lc1.(vrm)
              lc1.(vwm)
              lc1.(vcap)
              lc1.(vrel)
              lc1.(fwdbank)
              lc1.(exbank)
              lc1.(promises))
  .
  Hint Constructors dmbsy.

  Inductive step (event:Event.t (A:=View.t (A:=A))) (tid:Id.t) (mem:Memory.t) (lc1 lc2:t): Prop :=
  | step_internal
      ctrl
      (EVENT: event = (Event.internal ctrl))
      (LC: internal ctrl lc1 lc2)
  | step_read
      ex ord vloc res
      (EVENT: event = Event.read ex ord vloc res)
      (STEP: read ex ord vloc res lc1 mem lc2)
  | step_fulfill
      ex ord vloc vval res
      (EVENT: event = Event.write ex ord vloc vval res)
      (STEP: fulfill ex ord vloc vval res tid lc1 mem lc2)
  | step_write_failure
      ex ord vloc vval res
      (EVENT: event = Event.write ex ord vloc vval res)
      (STEP: write_failure ex res lc1 lc2)
  | step_isb
      (EVENT: event = Event.barrier Barrier.isb)
      (STEP: isb lc1 lc2)
  | step_dmbst
      (EVENT: event = Event.barrier Barrier.dmbst)
      (STEP: dmbst lc1 lc2)
  | step_dmbld
      (EVENT: event = Event.barrier Barrier.dmbld)
      (STEP: dmbld lc1 lc2)
  | step_dmbsy
      (EVENT: event = Event.barrier Barrier.dmbsy)
      (STEP: dmbsy lc1 lc2)
  .
  Hint Constructors step.

  Inductive wf (tid:Id.t) (mem:Memory.t) (lc:t): Prop :=
  | wf_intro
      (COH: forall loc, lc.(coh) loc <= List.length mem)
      (VRP: lc.(vrp).(View.ts) <= List.length mem)
      (VWP: lc.(vwp).(View.ts) <= List.length mem)
      (VRM: lc.(vrm).(View.ts) <= List.length mem)
      (VWM: lc.(vwm).(View.ts) <= List.length mem)
      (VCAP: lc.(vcap).(View.ts) <= List.length mem)
      (VREL: lc.(vrel).(View.ts) <= List.length mem)
      (FWDBANK: forall loc fwd,
          lc.(fwdbank) loc = Some fwd ->
          fwd.(FwdItem.ts) <= List.length mem /\
          fwd.(FwdItem.view).(View.ts) <= List.length mem)
      (EXBANK: forall ts, lc.(exbank) = Some ts -> ts <= List.length mem)
      (PROMISES: forall ts (IN: Promises.lookup ts lc.(promises)), ts <= List.length mem)
      (PROMISES: forall ts msg
                   (MSG: Memory.get_msg ts mem = Some msg)
                   (TID: msg.(Msg.tid) = tid)
                   (TS: lc.(coh) msg.(Msg.loc) < ts),
          Promises.lookup ts lc.(promises))
  .
  Hint Constructors wf.

  Lemma init_wf tid: wf tid Memory.empty init.
  Proof.
    econs; ss; i; try by apply bot_spec.
    - rewrite Promises.lookup_bot in IN. ss.
    - destruct ts; ss. destruct ts; ss.
  Qed.
End Local.
End Local.

Ltac viewtac :=
  repeat
    (try match goal with
         | [|- join _ _ <= _] => apply join_spec
         | [|- bot <= _] => apply bot_spec
         | [|- ifc ?c _ <= _] => destruct c; s

         | [|- Time.join _ _ <= _] => apply join_spec
         | [|- Time.bot <= _] => apply bot_spec

         | [|- context[View.ts (join _ _)]] => rewrite View.ts_join
         | [|- context[View.ts bot]] => rewrite View.ts_bot
         | [|- context[View.ts (ifc _ _)]] => rewrite View.ts_ifc
         end;
     ss; eauto).

Module ExecUnit.
Section ExecUnit.
  Context `{A: Type, _: orderC A eq}.

  Inductive t := mk {
    state: State.t (A:=View.t (A:=A));
    local: Local.t (A:=A);
    mem: Memory.t;
  }.
  Hint Constructors t.

  Inductive state_step0 (tid:Id.t) (e1 e2:Event.t (A:=View.t (A:=A))) (eu1 eu2:t): Prop :=
  | state_step0_intro
      (STATE: State.step e1 eu1.(state) eu2.(state))
      (LOCAL: Local.step e2 tid eu1.(mem) eu1.(local) eu2.(local))
      (MEM: eu2.(mem) = eu1.(mem))
  .
  Hint Constructors state_step0.

  Inductive state_step (tid:Id.t) (eu1 eu2:t): Prop :=
  | state_step_intro
      e
      (STEP: state_step0 tid e e eu1 eu2)
  .
  Hint Constructors state_step.

  Inductive promise_step (tid:Id.t) (eu1 eu2:t): Prop :=
  | promise_step_intro
      loc val
      (STATE: eu1.(state) = eu2.(state))
      (LOCAL: Local.promise loc val tid eu1.(local) eu1.(mem) eu2.(local) eu2.(mem))
  .
  Hint Constructors promise_step.

  Inductive step (tid:Id.t) (eu1 eu2:t): Prop :=
  | step_state (STEP: state_step tid eu1 eu2)
  | step_promise (STEP: promise_step tid eu1 eu2)
  .
  Hint Constructors step.

  Inductive rmap_wf (mem:Memory.t) (rmap:RMap.t (A:=View.t (A:=A))): Prop :=
  | rmap_wf_intro
      (RMAP: forall r, (RMap.find r rmap).(ValA.annot).(View.ts) <= List.length mem)
  .
  Hint Constructors rmap_wf.

  Inductive wf (tid:Id.t) (eu:t): Prop :=
  | wf_intro
      (STATE: rmap_wf eu.(mem) eu.(state).(State.rmap))
      (LOCAL: Local.wf tid eu.(mem) eu.(local))
  .
  Hint Constructors wf.

  Lemma rmap_add_wf
        mem rmap loc (val:ValA.t (A:=View.t (A:=A)))
        (WF: rmap_wf mem rmap)
        (VAL: val.(ValA.annot).(View.ts) <= List.length mem):
    rmap_wf mem (RMap.add loc val rmap).
  Proof.
    inv WF. econs. i. unfold RMap.find, RMap.add. rewrite IdMap.add_spec.
    condtac; viewtac.
  Qed.

  Lemma expr_wf
        mem rmap e
        (RMAP: rmap_wf mem rmap):
    (sem_expr rmap e).(ValA.annot).(View.ts) <= List.length mem.
  Proof.
    induction e; viewtac. apply RMAP.
  Qed.

  Lemma read_wf
        ts loc val mem
        (READ: Memory.read loc ts mem = Some val):
    ts <= List.length mem.
  Proof.
    revert READ. unfold Memory.read. destruct ts; [lia|]. s.
    destruct (nth_error mem ts) eqn:NTH; ss. condtac; ss.
    i. eapply List.nth_error_Some. congr.
  Qed.

  Lemma get_msg_wf
        ts msg mem
        (READ: Memory.get_msg ts mem = Some msg):
    ts <= List.length mem.
  Proof.
    revert READ. unfold Memory.get_msg. destruct ts; [lia|]. s.
    destruct (nth_error mem ts) eqn:NTH; ss. i. inv READ.
    eapply List.nth_error_Some. congr.
  Qed.

  Inductive eqts_val (v1 v2:ValA.t (A:=View.t (A:=A))): Prop :=
  | eqts_val_intro
      (VAL: v1.(ValA.val) = v2.(ValA.val))
      (VIEW: View.eqts v1.(ValA.annot) v2.(ValA.annot))
  .
  Hint Constructors eqts_val.

  Global Program Instance eqts_val_equiv: Equivalence eqts_val.
  Next Obligation. econs; ss. Qed.
  Next Obligation. ii. destruct x, y. inv H1. ss. subst. econs; ss. symmetry. ss. Qed.
  Next Obligation. ii. destruct x, y, z. inv H1. inv H2. ss. subst. econs; ss. etrans; eauto. Qed.

  Inductive eqts_event: forall (e1 e2:Event.t (A:=View.t (A:=A))), Prop :=
  | eqts_event_internal
      ctrl:
      eqts_event (Event.internal ctrl) (Event.internal ctrl)
  | eqts_event_read
      ex ord vloc1 vloc2 res1 res2
      (VLOC: eqts_val vloc1 vloc2)
      (RES: eqts_val res1 res2):
      eqts_event (Event.read ex ord vloc1 res1) (Event.read ex ord vloc2 res2)
  | eqts_event_write
      ex ord vloc1 vloc2 vval1 vval2 res1 res2
      (VLOC: eqts_val vloc1 vloc2)
      (VVAL: eqts_val vval1 vval2)
      (RES: eqts_val res1 res2):
      eqts_event (Event.write ex ord vloc1 vval1 res1) (Event.write ex ord vloc2 vval2 res2)
  | eqts_event_barrier
      b:
      eqts_event (Event.barrier b) (Event.barrier b)
  .
  Hint Constructors eqts_event.

  Global Program Instance eqts_event_equiv: Equivalence eqts_event.
  Next Obligation. ii. destruct x; econs; ss. Qed.
  Next Obligation.
    ii. inv H1; econs; ss.
    all: symmetry; ss.
  Qed.
  Next Obligation.
    ii. inv H1; inv H2; econs; ss.
    all: etrans; eauto.
  Qed.

  Lemma state_step0_wf tid e1 e2 eu1 eu2
        (STEP: state_step0 tid e1 e2 eu1 eu2)
        (EVENT: eqts_event e1 e2)
        (WF: wf tid eu1):
    wf tid eu2.
  Proof.
    destruct eu1 as [state1 local1 mem1].
    destruct eu2 as [state2 local2 mem2].
    inv WF. inv STEP. ss. subst.

    assert (FWD:
              forall loc ord ts,
                ts <= List.length mem1 ->
                (match Local.fwdbank local1 loc with
                 | Some fwd => FwdItem.read_view fwd ts ord
                 | None => View.mk ts bot
                 end).(View.ts) <= length mem1).
    { inv LOCAL. i. destruct (Local.fwdbank local1 loc) eqn:FWD; ss.
      exploit FWDBANK; eauto. i. des.
      unfold FwdItem.read_view. condtac; ss.
    }

    inv STATE0; inv LOCAL0; inv EVENT; inv LOCAL; ss.
    - inv LC. econs; ss. econs; viewtac.
    - inv LC. econs; ss.
      + eauto using rmap_add_wf, expr_wf.
      + econs; viewtac.
    - inv RES. inv VIEW. inv VLOC. inv VIEW.
      inv STEP. ss. subst.
      econs; ss.
      + apply rmap_add_wf; viewtac.
        rewrite TS, <- TS0. viewtac.
        * eauto using expr_wf.
        * apply FWD. eauto using read_wf.
      + econs; viewtac; eauto using expr_wf.
        all: try by rewrite <- TS0; eauto using expr_wf.
        all: try by apply FWD; eauto using read_wf.
        * i. rewrite fun_add_spec. condtac; viewtac.
          eapply read_wf. eauto.
        * destruct ex0; ss. i. inv H1. eapply read_wf. eauto.
        * i. eapply PROMISES0; eauto. eapply Time.le_lt_trans; [|by eauto].
          rewrite fun_add_spec. condtac; ss. inversion e. rewrite H2. ss.
    - inv RES. inv VIEW. inv VVAL. inv VIEW. inv VLOC. inv VIEW.
      inv STEP. inv WRITABLE. econs; ss.
      + apply rmap_add_wf; viewtac.
        rewrite TS. apply bot_spec.
      + econs; viewtac; rewrite <- ? TS0, <- ? TS1; eauto using get_msg_wf, expr_wf.
        * i. rewrite fun_add_spec. condtac; viewtac.
        * i. revert H1. rewrite fun_add_spec. condtac; viewtac.
          i. inv H1. s. rewrite <- TS0, <- TS1. splits; viewtac; eauto using get_msg_wf, expr_wf.
        * destruct ex0; ss.
        * i. revert IN. rewrite Promises.unset_o. condtac; ss. eauto.
        * i. rewrite Promises.unset_o. rewrite fun_add_spec in TS2. condtac.
          { inversion e. subst. rewrite MSG in MSG0. destruct msg. inv MSG0. ss.
            revert TS2. condtac; intuition.
          }
          { eapply PROMISES0; eauto. revert TS2. condtac; ss. i.
            inversion e. rewrite H2. rewrite COH0. ss.
          }
    - inv STEP. econs; ss. apply rmap_add_wf; viewtac.
      inv RES. inv VIEW. rewrite TS. s. apply bot_spec.
    - inv STEP. econs; ss. econs; viewtac.
    - inv STEP. econs; ss. econs; viewtac.
    - inv STEP. econs; ss. econs; viewtac.
    - inv STEP. econs; ss. econs; viewtac.
    - inv LC. econs; ss. econs; viewtac. eauto using expr_wf.
    - inv LC. econs; ss. econs; viewtac.
  Qed.

  Lemma state_step_wf tid eu1 eu2
        (STEP: state_step tid eu1 eu2)
        (WF: wf tid eu1):
    wf tid eu2.
  Proof.
    inv STEP. eapply state_step0_wf; eauto. refl.
  Qed.

  Lemma rmap_append_wf
        mem msg rmap
        (WF: rmap_wf mem rmap):
    rmap_wf (mem ++ [msg]) rmap.
  Proof.
    inv WF. econs. i. rewrite RMAP. rewrite List.app_length. lia.
  Qed.

  Lemma promise_step_wf tid eu1 eu2
        (STEP: promise_step tid eu1 eu2)
        (WF: wf tid eu1):
    wf tid eu2.
  Proof.
    destruct eu1 as [state1 local1 mem1].
    destruct eu2 as [state2 local2 mem2].
    inv WF. inv STEP. ss. subst.
    inv LOCAL. inv LOCAL0. inv MEM2. econs; ss.
    - apply rmap_append_wf. ss.
    - econs.
      all: try rewrite List.app_length; s; try lia.
      + i. rewrite COH. lia.
      + i. exploit FWDBANK; eauto. i. des. lia.
      + i. rewrite EXBANK; ss. lia.
      + i. revert IN. rewrite Promises.set_o. condtac.
        * inversion e. i. inv IN. lia.
        * i. exploit PROMISES; eauto. lia.
      + i. rewrite Promises.set_o. apply Memory.get_msg_snoc_inv in MSG. des.
        * destruct ts; ss. condtac; ss.
          eapply PROMISES0; eauto.
        * subst. condtac; ss. congr.
  Qed.

  Lemma step_wf tid eu1 eu2
        (STEP: step tid eu1 eu2)
        (WF: wf tid eu1):
    wf tid eu2.
  Proof.
    inv STEP.
    - eapply state_step_wf; eauto.
    - eapply promise_step_wf; eauto.
  Qed.
End ExecUnit.
End ExecUnit.

Module Machine.
  Inductive t := mk {
    tpool: IdMap.t (State.t (A:=View.t (A:=unit)) * Local.t (A:=unit));
    mem: Memory.t;
  }.
  Hint Constructors t.

  Definition init (p:program): t :=
    mk
      (IdMap.map (fun stmts => (State.init stmts, Local.init)) p)
      Memory.empty.

  Inductive is_terminal (m:t): Prop :=
  | is_terminal_intro
      (TERMINAL:
         forall tid st lc
           (FIND: IdMap.find tid m.(tpool) = Some (st, lc)),
           State.is_terminal st /\ lc.(Local.promises) = bot)
  .
  Hint Constructors is_terminal.

  Inductive no_promise (m:t): Prop :=
  | no_promise_intro
      (PROMISES:
         forall tid st lc
           (FIND: IdMap.find tid m.(tpool) = Some (st, lc)),
           lc.(Local.promises) = bot)
  .
  Hint Constructors no_promise.

  Lemma is_terminal_no_promise
        m
        (TERMINAL: is_terminal m):
    no_promise m.
  Proof.
    econs. i. eapply TERMINAL. eauto.
  Qed.

  Inductive step (eustep: forall (tid:Id.t) (eu1 eu2:ExecUnit.t (A:=unit)), Prop) (m1 m2:t): Prop :=
  | step_intro
      tid st1 lc1 st2 lc2
      (FIND: IdMap.find tid m1.(tpool) = Some (st1, lc1))
      (STEP: eustep tid (ExecUnit.mk st1 lc1 m1.(mem)) (ExecUnit.mk st2 lc2 m2.(mem)))
      (TPOOL: m2.(tpool) = IdMap.add tid (st2, lc2) m1.(tpool))
  .
  Hint Constructors step.

  Lemma rtc_eu_step_step
        eustep tid m st1 lc1 mem1 st2 lc2 mem2
        (FIND: IdMap.find tid m.(tpool) = Some (st1, lc1))
        (MEM: m.(mem) = mem1)
        (EX: rtc (eustep tid)
                 (ExecUnit.mk st1 lc1 mem1)
                 (ExecUnit.mk st2 lc2 mem2)):
    rtc (step eustep)
        m
        (mk
           (IdMap.add tid (st2, lc2) m.(tpool))
           mem2).
  Proof.
    revert m FIND MEM.
    depind EX.
    { i. subst. destruct m. s. rewrite PositiveMapAdditionalFacts.gsident; ss. refl. }
    destruct y. i. subst. econs.
    - instantiate (1 := mk _ _). econs; ss; eauto.
    - exploit IHEX; eauto.
      + instantiate (1 := mk _ _). s.
        rewrite IdMap.add_spec. condtac; eauto. exfalso. apply c. ss.
      + ss.
      + s. rewrite (IdMap.add_add tid (st2, lc2)). eauto.
  Qed.

  Inductive wf (m:t): Prop :=
  | wf_intro
      (WF: forall tid st lc
             (FIND: IdMap.find tid m.(tpool) = Some (st, lc)),
          ExecUnit.wf tid (ExecUnit.mk st lc m.(mem)))
  .
  Hint Constructors wf.

  Lemma init_wf p:
    wf (init p).
  Proof.
    econs. i. ss.
    rewrite IdMap.map_spec in FIND. destruct (IdMap.find tid p); inv FIND.
    econs; ss.
    - econs. i. unfold RMap.find, RMap.init. rewrite IdMap.gempty. ss.
    - apply Local.init_wf.
  Qed.

  Lemma init_no_promise p:
    no_promise (init p).
  Proof.
    econs. s. i.
    revert FIND. rewrite IdMap.map_spec. destruct (IdMap.find tid p); ss. i. inv FIND.
    ss.
  Qed.

  Lemma step_state_step_wf
        m1 m2
        (STEP: step ExecUnit.state_step m1 m2)
        (WF: wf m1):
    wf m2.
  Proof.
    destruct m1 as [tpool1 mem1].
    destruct m2 as [tpool2 mem2].
    inv STEP. inv STEP0. inv WF. econs. ss. subst.
    i. revert FIND0. rewrite IdMap.add_spec. condtac.
    - inversion e0. i. inv FIND0.
      eapply ExecUnit.state_step_wf; eauto. econs; eauto.
    - inv STEP. ss. i. subst. exploit WF0; eauto.
  Qed.

  Lemma step_promise_step_wf
        m1 m2
        (STEP: step ExecUnit.promise_step m1 m2)
        (WF: wf m1):
    wf m2.
  Proof.
    destruct m1 as [tpool1 mem1].
    destruct m2 as [tpool2 mem2].
    inv STEP. inv STEP0. inv LOCAL. inv MEM2. inv WF. econs. ss. subst.
    i. revert FIND0. rewrite IdMap.add_spec. condtac.
    - inversion e. i. inv FIND0.
      eapply ExecUnit.promise_step_wf; eauto. econs; eauto. econs; eauto.
      + econs; eauto.
      + refl.
    - i. exploit WF0; eauto. i. inv x. ss. econs; ss.
      + apply ExecUnit.rmap_append_wf. ss.
      + inv LOCAL. econs.
        all: try rewrite List.app_length; s; try lia.
        * i. rewrite COH. lia.
        * i. exploit FWDBANK; eauto. i. des. lia.
        * i. rewrite EXBANK; ss. lia.
        * i. exploit PROMISES; eauto. lia.
        * i. apply Memory.get_msg_snoc_inv in MSG. des.
          { eapply PROMISES0; eauto. }
          { subst. ss. congr. }
  Qed.

  Lemma rtc_step_promise_step_wf
        m1 m2
        (STEP: rtc (step ExecUnit.promise_step) m1 m2)
        (WF: wf m1):
    wf m2.
  Proof.
    revert WF. induction STEP; ss. i. apply IHSTEP.
    eapply step_promise_step_wf; eauto.
  Qed.

  Lemma step_step_wf
        m1 m2
        (STEP: step ExecUnit.step m1 m2)
        (WF: wf m1):
    wf m2.
  Proof.
    inv STEP. inv STEP0.
    - eapply step_state_step_wf; eauto.
    - eapply step_promise_step_wf; eauto.
  Qed.

  Lemma step_mon
        (eustep1 eustep2: _ -> _ -> _ -> Prop)
        (EUSTEP: forall tid m1 m2, eustep1 tid m1 m2 -> eustep2 tid m1 m2):
    forall m1 m2, step eustep1 m1 m2 -> step eustep2 m1 m2.
  Proof.
    i. inv H. econs; eauto.
  Qed.

  Lemma rtc_step_mon
        (eustep1 eustep2: _ -> _ -> _ -> Prop)
        (EUSTEP: forall tid m1 m2, eustep1 tid m1 m2 -> eustep2 tid m1 m2):
    forall m1 m2, rtc (step eustep1) m1 m2 -> rtc (step eustep2) m1 m2.
  Proof.
    i. induction H; eauto. econs; eauto. eapply step_mon; eauto.
  Qed.

  Inductive exec (p:program) (m:t): Prop :=
  | exec_intro
      (STEP: rtc (step ExecUnit.step) (init p) m)
      (NOPROMISE: no_promise m)
  .
  Hint Constructors exec.

  Inductive state_exec (m1 m2:Machine.t): Prop :=
  | state_exec_intro
      (TPOOL: IdMap.Forall2
                (fun tid sl1 sl2 =>
                   rtc (ExecUnit.state_step tid)
                       (ExecUnit.mk sl1.(fst) sl1.(snd) m1.(mem))
                       (ExecUnit.mk sl2.(fst) sl2.(snd) m1.(mem)))
                m1.(tpool) m2.(tpool))
      (MEM: m1.(mem) = m2.(mem))
  .      

  Inductive pf_exec (p:program) (m:Machine.t): Prop :=
  | pf_exec_intro
      m1
      (STEP1: rtc (Machine.step ExecUnit.promise_step) (Machine.init p) m1)
      (STEP2: state_exec m1 m)
      (NOPROMISE: no_promise m)
  .
  Hint Constructors pf_exec.

  Inductive equiv (m1 m2:Machine.t): Prop :=
  | equiv_intro
      (TPOOL: IdMap.Equal m1.(tpool) m2.(tpool))
      (MEM: m1.(mem) = m2.(mem))
  .

  Lemma equiv_no_promise
        m1 m2
        (EQUIV: equiv m1 m2)
        (NOPROMISE: no_promise m1):
    no_promise m2.
  Proof.
    inv EQUIV. inv NOPROMISE. econs. i.
    specialize (TPOOL tid). rewrite FIND in TPOOL.
    eapply PROMISES. eauto.
  Qed.

  Lemma unlift_step_state_step
        m1 m2 tid st1 lc1
        (STEPS: rtc (step ExecUnit.state_step) m1 m2)
        (TPOOL: IdMap.find tid m1.(tpool) = Some (st1, lc1)):
    exists st2 lc2,
      <<TPOOL: IdMap.find tid m2.(tpool) = Some (st2, lc2)>> /\
               <<STEPS: rtc (ExecUnit.state_step tid)
                            (ExecUnit.mk st1 lc1 m1.(mem))
                            (ExecUnit.mk st2 lc2 m2.(mem))>>.
  Proof.
    revert st1 lc1 TPOOL. induction STEPS; eauto. i.
    destruct x as [tpool1 mem1].
    destruct y as [tpool2 mem2].
    destruct z as [tpool3 mem3].
    inv H. ss.
    assert (mem2 = mem1).
    { inv STEP. inv STEP0. ss. }
    subst. exploit IHSTEPS.
    { rewrite IdMap.add_spec, TPOOL.
      instantiate (1 := if equiv_dec tid tid0 then lc2 else lc1).
      instantiate (1 := if equiv_dec tid tid0 then st2 else st1).
      condtac; ss.
    }
    i. des.
    esplits; eauto. rewrite <- STEPS0. condtac; eauto.
    inversion e. subst. rewrite TPOOL in FIND. inv FIND. econs; eauto.
  Qed.
End Machine.
