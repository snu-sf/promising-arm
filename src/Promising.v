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

  Definition read (ts:Time.t) (loc:Loc.t) (mem:t): option Val.t :=
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

  Lemma read_mon ts loc val mem1 mem2
        (READ: Memory.read ts loc mem1 = Some val):
    Memory.read ts loc (mem1 ++ mem2) = Some val.
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

  Inductive read (ex:bool) (ord:OrdR.t) (vloc:ValA.t (A:=View.t)) (res: ValA.t (A:=View.t)) (lc1:t) (mem1: Memory.t) (lc2:t): Prop :=
  | read_intro
      ts loc val view
      view_ext1 view_ext2
      (LOC: loc = vloc.(ValA.val))
      (VIEW: view = vloc.(ValA.annot))
      (VIEW_EXT1: view_ext1 = joins [view; lc1.(vrp); (ifc (OrdR.ge ord OrdR.acquire) lc1.(vrel))])
      (COH: le (lc1.(coh) loc) ts)
      (LATEST: Memory.no_msgs ts view_ext1.(View.ts) (fun msg => msg.(Msg.loc) = loc) mem1)
      (MSG: Memory.read ts loc mem1 = Some val)
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

  Inductive fulfill (ex:bool) (ord:OrdW.t) (vloc:ValA.t (A:=View.t)) (vval:ValA.t (A:=View.t)) (res: ValA.t (A:=View.t)) (tid:Id.t) (lc1:t) (mem1: Memory.t) (lc2:t): Prop :=
  | fulfill_intro
      ts loc val
      view_loc view_val view_ext
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
           <<LATEST: forall valx (READ: Memory.read tsx loc mem1 = Some valx),
               Memory.no_msgs tsx ts (fun msg => msg.(Msg.loc) = loc /\ msg.(Msg.tid) <> tid) mem1>>)
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

  Inductive write_failure (ex:bool) (res: ValA.t (A:=View.t)) (lc1:t) (lc2:t): Prop :=
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

  Inductive step (event:Event.t (A:=View.t)) (tid:Id.t) (mem:Memory.t) (lc1 lc2:t): Prop :=
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

  Inductive wf (mem:Memory.t) (lc:t): Prop :=
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
  .
  Hint Constructors wf.

  Lemma init_wf mem: wf mem init.
  Proof.
    econs; ss; i; try by apply bot_spec.
    rewrite Promises.lookup_bot in IN. ss.
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

  Inductive state_step (tid:Id.t) (eu1 eu2:t): Prop :=
  | state_step_intro
      e
      (STATE: State.step e eu1.(state) eu2.(state))
      (LOCAL: Local.step e tid eu1.(mem) eu1.(local) eu2.(local))
      (MEM: eu2.(mem) = eu1.(mem))
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

  Inductive rmap_wf (mem:Memory.t) (rmap:RMap.t (A:=View.t)): Prop :=
  | rmap_wf_intro
      (RMAP: forall r, (RMap.find r rmap).(ValA.annot).(View.ts) <= List.length mem)
  .
  Hint Constructors rmap_wf.

  Inductive wf (eu:t): Prop :=
  | wf_intro
      (STATE: rmap_wf eu.(mem) eu.(state).(State.rmap))
      (LOCAL: Local.wf eu.(mem) eu.(local))
  .
  Hint Constructors wf.

  Lemma rmap_add_wf
        mem rmap loc val
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
        (READ: Memory.read ts loc mem = Some val):
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

  Lemma state_step_wf tid eu1 eu2
        (STEP: state_step tid eu1 eu2)
        (WF: wf eu1):
    wf eu2.
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
    - inv STEP. econs; ss.
      + apply rmap_add_wf; viewtac.
        * eauto using expr_wf.
        * apply FWD. eauto using read_wf.
      + econs; viewtac; eauto using expr_wf.
        * i. rewrite fun_add_spec. condtac; viewtac.
          eapply read_wf. eauto.
        * apply FWD. eauto using read_wf.
        * apply FWD. eauto using read_wf.
        * apply FWD. eauto using read_wf.
        * destruct ex0; ss. i. inv H1. eapply read_wf. eauto.
    - inv STEP. econs; ss.
      + apply rmap_add_wf; viewtac.
      + econs; viewtac; eauto using get_msg_wf, expr_wf.
        * i. rewrite fun_add_spec. condtac; viewtac.
          eapply get_msg_wf. eauto.
        * i. revert H1. rewrite fun_add_spec. condtac; viewtac.
          i. inv H1. s. splits; viewtac; eauto using get_msg_wf, expr_wf.
        * destruct ex0; ss.
        * i. revert IN. rewrite Promises.unset_o. condtac; ss. eauto.
    - inv STEP. econs; ss. apply rmap_add_wf; viewtac.
    - inv STEP. econs; ss. econs; viewtac.
    - inv STEP. econs; ss. econs; viewtac.
    - inv STEP. econs; ss. econs; viewtac.
    - inv STEP. econs; ss. econs; viewtac.
    - inv LC. econs; ss. econs; viewtac. eauto using expr_wf.
    - inv LC. econs; ss. econs; viewtac.
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
        (WF: wf eu1):
    wf eu2.
  Proof.
    destruct eu1 as [state1 local1 mem1].
    destruct eu2 as [state2 local2 mem2].
    inv WF. inv STEP. ss. subst.
    inv LOCAL. inv LOCAL0. inv MEM2. econs; ss.
    - apply rmap_append_wf. ss.
    - econs.
      all: rewrite List.app_length; s; try lia.
      + i. rewrite COH. lia.
      + i. exploit FWDBANK; eauto. i. des. lia.
      + i. rewrite EXBANK; ss. lia.
      + i. revert IN. rewrite Promises.set_o. condtac.
        * inversion e. i. inv IN. lia.
        * i. exploit PROMISES; eauto. lia.
  Qed.

  Lemma step_wf tid eu1 eu2
        (STEP: step tid eu1 eu2)
        (WF: wf eu1):
    wf eu2.
  Proof.
    inv STEP; eauto using state_step_wf, promise_step_wf.
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
          ExecUnit.wf (ExecUnit.mk st lc m.(mem)))
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
    - i. exploit WF0; eauto.
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
        all: rewrite List.app_length; s; try lia.
        * i. rewrite COH. lia.
        * i. exploit FWDBANK; eauto. i. des. lia.
        * i. rewrite EXBANK; ss. lia.
        * i. exploit PROMISES; eauto. lia.
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

  Inductive pf_exec (p:program) (m:Machine.t): Prop :=
  | pf_exec_intro
      m1
      (STEP1: rtc (Machine.step ExecUnit.promise_step) (Machine.init p) m1)
      (STEP2: rtc (Machine.step ExecUnit.state_step) m1 m)
      (NOPROMISE: Machine.no_promise m)
  .
  Hint Constructors pf_exec.
End Machine.
