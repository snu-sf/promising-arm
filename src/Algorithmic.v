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

Set Implicit Arguments.


Module Lock.
  Inductive t := mk {
    loc: Loc.t;
    from: nat;
    to: nat;
    guarantee: Loc.t -> nat;
  }.
  Hint Constructors t.

  Inductive is_final (locks: Lock.t -> Prop) (c: Loc.t -> nat): Prop :=
  | is_final_intro
      (LOCK: forall lock (LOCK: locks lock), lock.(to) <= (c lock.(loc)))
  .
End Lock.

Module Taint.
  Inductive elt :=
  | R (id:nat) (from:nat)
  | W (id:nat) (to:nat) (loc:Loc.t) (guarantee:Loc.t -> nat)
  .
  Hint Constructors elt.

  Definition t := elt -> Prop.

  Inductive is_locked (taint:t) (lock:Lock.t): Prop :=
  | is_locked_intro
      id
      (R: taint (R id lock.(Lock.from)))
      (W: taint (W id lock.(Lock.to) lock.(Lock.loc) lock.(Lock.guarantee)))
  .
  Hint Constructors is_locked.
End Taint.

Module AExecUnit.
  Inductive aux_t := mk_aux {
    ex_counter: nat;
    st_counter: Loc.t -> nat;
    taint: Taint.t;
  }.
  Hint Constructors aux_t.

  Inductive t := mk {
    eu: ExecUnit.t (A:=Taint.t);
    aux: aux_t;
  }.
  Hint Constructors t.
  Coercion eu: t >-> ExecUnit.t.

  Definition taint_read_event (aux:aux_t) (e:Event.t (A:=View.t (A:=Taint.t))): Event.t (A:=View.t (A:=Taint.t)) :=
    match e with
    | Event.read true ord vloc res =>
      Event.read true ord vloc
                 (ValA.mk _ res.(ValA.val)
                          (View.mk res.(ValA.annot).(View.ts)
                                   (join res.(ValA.annot).(View.annot) (eq (Taint.R (S aux.(ex_counter)) (aux.(st_counter) vloc.(ValA.val)))))))
    | _ => e
    end.

  Definition state_step_aux (e:Event.t (A:=View.t (A:=Taint.t))) (aux:aux_t): aux_t :=
    match e with
    | Event.read true _ _ _ =>
      mk_aux
        (S aux.(ex_counter))
        aux.(st_counter)
        aux.(taint)
    | Event.write _ _ vloc _ res =>
      mk_aux
        aux.(ex_counter)
        aux.(st_counter)
        (join aux.(taint) res.(ValA.annot).(View.annot))
    | _ =>
      aux
    end.

  Inductive state_step (tid:Id.t) (aeu1 aeu2:t): Prop :=
  | state_step_intro
      e1 e2
      (EVENT: e2 = taint_read_event aeu2.(aux) e1)
      (STATE: State.step e2 aeu1.(ExecUnit.state) aeu2.(ExecUnit.state))
      (LOCAL: Local.step e1 tid aeu1.(ExecUnit.mem) aeu1.(ExecUnit.local) aeu2.(eu).(ExecUnit.local))
      (MEM: aeu2.(ExecUnit.mem) = aeu1.(ExecUnit.mem))
      (AUX: aeu2.(aux) = state_step_aux e1 aeu1.(aux))
  .
  Hint Constructors state_step.

  Definition taint_write (ord:OrdW.t) (loc:Loc.t) (aux:aux_t): Taint.elt :=
    Taint.W aux.(ex_counter) (S (aux.(st_counter) loc)) loc (ifc (OrdW.ge ord OrdW.release) aux.(st_counter)).

  Definition taint_write_res (aux:aux_t) (ex:bool) (ord:OrdW.t) (loc:Loc.t) (res:ValA.t (A:=View.t (A:=Taint.t))): ValA.t (A:=View.t (A:=Taint.t)) :=
    if negb ex
    then res
    else ValA.mk _ res.(ValA.val) (View.mk res.(ValA.annot).(View.ts) (join res.(ValA.annot).(View.annot) (eq (taint_write ord loc aux)))).

  Definition taint_write_lc (aux:aux_t) (ex:bool) (ord:OrdW.t) (loc:Loc.t) (lc: Local.t (A:=Taint.t)): Local.t (A:=Taint.t) :=
    if negb ex
    then lc
    else
      Local.mk
        lc.(Local.coh)
        lc.(Local.vrp)
        lc.(Local.vwp)
        lc.(Local.vrm)
        lc.(Local.vwm)
        lc.(Local.vcap)
        lc.(Local.vrel)
        (fun_add
           loc
           (option_map
              (fun fwd => (FwdItem.mk
                          fwd.(FwdItem.ts)
                          (View.mk fwd.(FwdItem.view).(View.ts)
                                   (join fwd.(FwdItem.view).(View.annot) (eq (taint_write ord loc aux))))
                          fwd.(FwdItem.ex)))
              (lc.(Local.fwdbank) loc))
           lc.(Local.fwdbank))
        lc.(Local.exbank)
        lc.(Local.promises).

  Definition write_step_aux (loc:Loc.t) (aux:aux_t): aux_t :=
    mk_aux
      aux.(ex_counter)
      (fun_add loc (S (aux.(st_counter) loc)) aux.(st_counter))
      aux.(taint).

  Inductive write_step (tid:Id.t) (aeu1 aeu2:t): Prop :=
  | write_step_intro
      ex ord vloc vval res1 res2 lc1 lc2
      (RES: res2 = taint_write_res aeu1.(aux) ex ord vloc.(ValA.val) res1)
      (STATE: State.step (Event.write ex ord vloc vval res2) aeu1.(ExecUnit.state) aeu2.(ExecUnit.state))
      (LOCAL1: Local.promise vloc.(ValA.val) vval.(ValA.val) tid aeu1.(ExecUnit.local) aeu1.(ExecUnit.mem) lc1 aeu2.(ExecUnit.mem))
      (LOCAL2: Local.fulfill ex ord vloc vval res1 tid lc1 aeu2.(ExecUnit.mem) lc2)
      (LOCAL3: aeu2.(ExecUnit.local) = taint_write_lc aeu2.(aux) ex ord vloc.(ValA.val) lc2)
      (AUX: aeu2.(aux) = write_step_aux vloc.(ValA.val) aeu1.(aux))
  .
  Hint Constructors write_step.

  Inductive step (tid:Id.t) (aeu1 aeu2:t): Prop :=
  | step_state (STEP: state_step tid aeu1 aeu2)
  | step_write (STEP: write_step tid aeu1 aeu2)
  .
  Hint Constructors step.

  Definition init_view (v:View.t (A:=unit)): View.t (A:=Taint.t) :=
    View.mk v.(View.ts) bot.

  Definition init_lc (lc:Local.t (A:=unit)): Local.t (A:=Taint.t) :=
    Local.mk
      lc.(Local.coh)
      (init_view lc.(Local.vrp))
      (init_view lc.(Local.vwp))
      (init_view lc.(Local.vrm))
      (init_view lc.(Local.vwm))
      (View.mk lc.(Local.vcap).(View.ts) (eq (Taint.R 0 0)))
      (init_view lc.(Local.vrel))
      (fun loc =>
         option_map
           (fun fwd => FwdItem.mk fwd.(FwdItem.ts) (init_view fwd.(FwdItem.view)) fwd.(FwdItem.ex))
           (lc.(Local.fwdbank) loc))
      lc.(Local.exbank)
      lc.(Local.promises).

  Definition init_aux: aux_t := mk_aux 0 (fun _ => 0) bot.

  Definition init_rmap (rmap:RMap.t (A:=View.t (A:=unit))): RMap.t (A:=View.t (A:=Taint.t)) :=
    IdMap.map (fun vala => ValA.mk _ vala.(ValA.val) (init_view vala.(ValA.annot))) rmap.

  Definition init_st (st:State.t (A:=View.t (A:=unit))): State.t (A:=View.t (A:=Taint.t)) :=
    State.mk st.(State.stmts) (init_rmap st.(State.rmap)).

  Definition init (eu:ExecUnit.t (A:=unit)): t :=
    mk
      (ExecUnit.mk (init_st eu.(ExecUnit.state)) (init_lc eu.(ExecUnit.local)) eu.(ExecUnit.mem))
      init_aux.
End AExecUnit.
Coercion AExecUnit.eu: AExecUnit.t >-> ExecUnit.t.

Inductive certify (tid:Id.t) (eu:ExecUnit.t (A:=unit)) (locks:Lock.t -> Prop): Prop :=
| certify_intro
    aeu
    (STEPS: rtc (AExecUnit.step tid) (AExecUnit.init eu) aeu)
    (NOPROMISE: aeu.(ExecUnit.local).(Local.promises) = bot)
    (LOCKS: locks = Taint.is_locked aeu.(AExecUnit.aux).(AExecUnit.taint))
.
Hint Constructors certify.

Lemma wf_certify
      tid (eu:ExecUnit.t (A:=unit))
      (PROMISES: eu.(ExecUnit.local).(Local.promises) = bot)
      (WF: ExecUnit.wf eu):
  certify tid eu bot.
Proof.
  econs; eauto. s. funext. i. propext. econs; ss.
  intro X. inv X. inv R.
Qed.

Module AMachine.
  Inductive t := mk {
    machine: Machine.t;
    tlocks: IdMap.t (Lock.t -> Prop);
  }.
  Hint Constructors t.
  Coercion machine: t >-> Machine.t.

  Definition init (p:program): t :=
    mk
      (Machine.init p)
      (IdMap.map (fun _ => bot) p).

  Inductive consistent (am: IdMap.t ((Lock.t -> Prop) * (Loc.t -> nat))): Prop :=
  | consistent_final
      (FINAL: IdMap.Forall (fun _ th => Lock.is_final th.(fst) th.(snd)) am)
  | consistent_step
      (TODO: False)
  .
  Hint Constructors consistent.

  Inductive wf (m:t): Prop :=
  | wf_intro
      (MACHINE: Machine.wf m.(machine))
      (CERTIFY: IdMap.Forall2
                  (fun tid th tlock => certify tid (ExecUnit.mk th.(fst) th.(snd) m.(Machine.mem)) tlock)
                  m.(Machine.tpool) m.(tlocks))
      (CONSISTENT: consistent (IdMap.map (fun tlock => (tlock, bot)) m.(tlocks)))
  .
  Hint Constructors wf.

  Lemma init_wf p:
    wf (init p).
  Proof.
    econs.
    - apply Machine.init_wf.
    - s. ii. rewrite ? IdMap.map_spec. destruct (IdMap.find id p); ss.
      econs. s. apply wf_certify; ss.
      econs; ss.
      + econs. i. unfold RMap.find, RMap.init. rewrite IdMap.gempty. ss.
      + apply Local.init_wf.
    - econs. s. intros ? ?. rewrite ? IdMap.map_spec.
      destruct (IdMap.find id p); ss. i. inv FIND. ss.
  Qed.

  Inductive step (eustep: forall (tid:Id.t) (eu1 eu2:ExecUnit.t (A:=unit)), Prop) (m1 m2:t): Prop :=
  | step_intro
      tid st1 lc1 st2 lc2 tlock
      (FIND: IdMap.find tid m1.(Machine.tpool) = Some (st1, lc1))
      (STEP: eustep tid (ExecUnit.mk st1 lc1 m1.(Machine.mem)) (ExecUnit.mk st2 lc2 m2.(Machine.mem)))
      (TPOOL: m2.(Machine.tpool) = IdMap.add tid (st2, lc2) m1.(Machine.tpool))
      (TLOCKS: m2.(tlocks) = IdMap.add tid tlock m1.(tlocks))
      (CERTIFY: certify tid (ExecUnit.mk st2 lc2 m2.(Machine.mem)) tlock)
      (INTERFERE: True) (* TODO: doesn't bother other's lock *)
      (CONSISTENT: consistent (IdMap.map (fun tlock => (tlock, bot)) m2.(tlocks)))
  .
  Hint Constructors step.

  Lemma step_state_step_wf
        m1 m2
        (STEP: step ExecUnit.state_step m1 m2)
        (WF: wf m1):
    wf m2.
  Proof.
    inv WF. inv STEP. econs; eauto.
    - eapply Machine.step_state_step_wf; eauto.
    - rewrite TPOOL, TLOCKS. ii. rewrite ? IdMap.add_spec. condtac.
      + inversion e. eauto.
      + inv STEP0. ss. rewrite MEM. eauto.
  Qed.

  Lemma step_promise_step_wf
        m1 m2
        (STEP: step ExecUnit.promise_step m1 m2)
        (WF: wf m1):
    wf m2.
  Proof.
    inv WF. inv STEP. econs; eauto.
    - eapply Machine.step_promise_step_wf; eauto.
    - rewrite TPOOL, TLOCKS. ii. rewrite ? IdMap.add_spec. condtac.
      + inversion e. eauto.
      + admit. (* certify after changing mem; "INTERFERE" is important here. *)
  Admitted.

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

  Inductive exec (p:program) (m:Machine.t): Prop :=
  | exec_intro
      am
      (STEP: rtc (step ExecUnit.step) (init p) am)
      (MACHINE: m = am.(machine))
      (NOPROMISE: Machine.no_promise m)
  .
  Hint Constructors exec.

  Inductive pf_exec (p:program) (m:Machine.t): Prop :=
  | pf_exec_intro
      am1
      (STEP1: rtc (step ExecUnit.promise_step) (init p) am1)
      (STEP2: rtc (Machine.step ExecUnit.state_step) am1.(machine) m)
      (NOPROMISE: Machine.no_promise m)
  .
  Hint Constructors pf_exec.
End AMachine.
Coercion AMachine.machine: AMachine.t >-> Machine.t.
