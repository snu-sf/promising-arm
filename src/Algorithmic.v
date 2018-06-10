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
  Inductive ex_t := mk_ex {
    loc: Loc.t;
    from: nat;
    to: nat;
  }.
  Hint Constructors ex.

  Inductive t := mk {
    ex: ex_t -> Prop;
    release: (Loc.t * nat) -> Loc.t -> nat;
  }.

  Definition init: t := mk bot bot.

  Inductive is_locked (lock:t) (c:Loc.t -> nat) (l:Loc.t): Prop :=
  | is_locked_intro
      exlock
      (LOCK: lock.(ex) exlock)
      (LOC: l = exlock.(loc))
      (RANGE: exlock.(from) <= c l /\ c l < exlock.(to))
  .

  Inductive is_final (lock:t) (c:Loc.t -> nat): Prop :=
  | is_final_intro
      (LOCK: forall exlock (LOCK: lock.(ex) exlock), exlock.(to) <= (c exlock.(loc)))
  .
End Lock.

Module Taint.
  Inductive elt :=
  | R (id:nat) (from:nat)
  | W (id:nat) (to:nat) (loc:Loc.t)
  .
  Hint Constructors elt.

  Definition t := elt -> Prop.

  Inductive is_locked (taint:t) (lock:Lock.ex_t): Prop :=
  | is_locked_intro
      id
      (R: taint (R id lock.(Lock.from)))
      (W: taint (W id lock.(Lock.to) lock.(Lock.loc)))
  .
  Hint Constructors is_locked.
End Taint.

Module AExecUnit.
  Inductive aux_t := mk_aux {
    ex_counter: nat;
    st_counter: Loc.t -> nat;
    taint: Taint.t;
    release: (Loc.t * nat) -> Loc.t -> nat;
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
    | Event.read ex ord vloc res =>
      Event.read
        ex ord vloc
        (ValA.mk _ res.(ValA.val)
                   (View.mk res.(ValA.annot).(View.ts)
                            (join res.(ValA.annot).(View.annot) (ifc ex (eq (Taint.R (S aux.(ex_counter)) (aux.(st_counter) vloc.(ValA.val))))))))
    | _ => e
    end.

  Definition state_step_aux (e:Event.t (A:=View.t (A:=Taint.t))) (aux:aux_t): aux_t :=
    match e with
    | Event.read true _ _ _ =>
      mk_aux
        (S aux.(ex_counter))
        aux.(st_counter)
        aux.(taint)
        aux.(release)
    | Event.write _ _ vloc _ res =>
      mk_aux
        aux.(ex_counter)
        aux.(st_counter)
        (join aux.(taint) res.(ValA.annot).(View.annot))
        aux.(release)
    | _ =>
      aux
    end.

  Inductive state_step (tid:Id.t) (aeu1 aeu2:t): Prop :=
  | state_step_intro
      e
      (STEP: ExecUnit.state_step0 tid (taint_read_event aeu2.(aux) e) e aeu1 aeu2)
      (AUX: aeu2.(aux) = state_step_aux e aeu1.(aux))
  .
  Hint Constructors state_step.

  Definition taint_write (ord:OrdW.t) (loc:Loc.t) (aux:aux_t): Taint.elt :=
    Taint.W aux.(ex_counter) (S (aux.(st_counter) loc)) loc.

  Definition taint_write_res (aux:aux_t) (ex:bool) (ord:OrdW.t) (loc:Loc.t) (res:ValA.t (A:=View.t (A:=Taint.t))): ValA.t (A:=View.t (A:=Taint.t)) :=
    ValA.mk _ res.(ValA.val) (View.mk res.(ValA.annot).(View.ts) (join res.(ValA.annot).(View.annot) (ifc ex (eq (taint_write ord loc aux))))).

  Definition taint_write_lc (aux:aux_t) (ex:bool) (ord:OrdW.t) (loc:Loc.t) (lc: Local.t (A:=Taint.t)): Local.t (A:=Taint.t) :=
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
            (fun fwd => FwdItem.mk
                       fwd.(FwdItem.ts)
                       (View.mk fwd.(FwdItem.view).(View.ts)
                                (join fwd.(FwdItem.view).(View.annot) (ifc ex (eq (taint_write ord loc aux)))))
                       fwd.(FwdItem.ex))
            (lc.(Local.fwdbank) loc))
         lc.(Local.fwdbank))
      lc.(Local.exbank)
      lc.(Local.promises).

  Definition write_step_aux (loc:Loc.t) (ord:OrdW.t) (aux:aux_t): aux_t :=
    mk_aux
      aux.(ex_counter)
      (fun_add loc (S (aux.(st_counter) loc)) aux.(st_counter))
      aux.(taint)
      (if OrdW.ge ord OrdW.release
       then fun_add (loc, S (aux.(st_counter) loc)) aux.(st_counter) aux.(release)
       else aux.(release)).

  Inductive local_write (ex:bool) (ord:OrdW.t) (vloc vval res:ValA.t (A:=View.t (A:=Taint.t))) (tid:Id.t) (lc1:Local.t) (mem1:Memory.t) (aux:aux_t) (lc2:Local.t): Prop :=
  | fulfill_intro
      ts loc val
      view_loc view_val view_ext
      (LOC: loc = vloc.(ValA.val))
      (VIEW_LOC: view_loc = vloc.(ValA.annot))
      (VAL: val = vval.(ValA.val))
      (VIEW_VAL: view_val = vval.(ValA.annot))
      (TS: ts = S (length mem1))
      (WRITABLE: Local.writable ex ord vloc vval tid lc1 mem1 ts view_ext)
      (RES: res = ValA.mk _ 0 (View.mk bot (join view_ext.(View.annot) (ifc ex (eq (taint_write ord loc aux))))))
      (LC2: lc2 =
            Local.mk
              (fun_add loc ts lc1.(Local.coh))
              lc1.(Local.vrp)
              lc1.(Local.vwp)
              lc1.(Local.vrm)
              (join lc1.(Local.vwm) (View.mk ts bot))
              (join lc1.(Local.vcap) view_loc)
              (join lc1.(Local.vrel) (View.mk (ifc (OrdW.ge ord OrdW.release) ts) bot))
              (fun_add loc (Some (FwdItem.mk ts (join view_loc view_val) ex)) lc1.(Local.fwdbank))
              (if ex then None else lc1.(Local.exbank))
              lc1.(Local.promises))
  .
  Hint Constructors local_write.

  Inductive write_step (tid:Id.t) (aeu1 aeu2:t): Prop :=
  | write_step_intro
      ex ord vloc vval res
      (STATE: State.step (Event.write ex ord vloc vval res) aeu1.(ExecUnit.state) aeu2.(ExecUnit.state))
      (LOCAL: local_write ex ord vloc vval res tid aeu1.(ExecUnit.local) aeu1.(ExecUnit.mem) aeu1.(aux) aeu2.(ExecUnit.local))
      (MEM: aeu2.(ExecUnit.mem) = aeu1.(ExecUnit.mem) ++ [Msg.mk vloc.(ValA.val) vval.(ValA.val) tid])
      (AUX: aeu2.(aux) = write_step_aux vloc.(ValA.val) ord aeu1.(aux))
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

  Definition init_aux: aux_t := mk_aux 0 (fun _ => 0) bot bot.

  Definition init_rmap (rmap:RMap.t (A:=View.t (A:=unit))): RMap.t (A:=View.t (A:=Taint.t)) :=
    IdMap.map (fun vala => ValA.mk _ vala.(ValA.val) (init_view vala.(ValA.annot))) rmap.

  Definition init_st (st:State.t (A:=View.t (A:=unit))): State.t (A:=View.t (A:=Taint.t)) :=
    State.mk st.(State.stmts) (init_rmap st.(State.rmap)).

  Definition init (eu:ExecUnit.t (A:=unit)): t :=
    mk
      (ExecUnit.mk (init_st eu.(ExecUnit.state)) (init_lc eu.(ExecUnit.local)) eu.(ExecUnit.mem))
      init_aux.

  Lemma taint_read_event_eqts aux e:
    ExecUnit.eqts_event (taint_read_event aux e) e.
  Proof.
    destruct e; try refl.
    econs; ss.
  Qed.

  Lemma state_step_wf
        tid aeu1 aeu2
        (STEP: state_step tid aeu1 aeu2)
        (WF: ExecUnit.wf tid aeu1):
    ExecUnit.wf tid aeu2.
  Proof.
    inv STEP.
    eapply ExecUnit.state_step0_wf in STEP0; ss.
    apply taint_read_event_eqts.
  Qed.

  Lemma write_step_wf
        tid aeu1 aeu2
        (STEP: write_step tid aeu1 aeu2)
        (WF: ExecUnit.wf tid aeu1):
    ExecUnit.wf tid aeu2.
  Proof.
    destruct aeu1 as [[st1 lc1 mem1] aux1].
    destruct aeu2 as [[st2 lc2 mem2] aux2].
    inv STEP. ss. subst.
    inv STATE. inv LOCAL. inv WRITABLE. inv WF. econs; ss.
    - apply ExecUnit.rmap_add_wf; viewtac.
      inv STATE. econs. i. rewrite app_length. s.
      rewrite RMAP. intuition.
    - inv LOCAL. econs; ss.
      all: try rewrite app_length; s.
      all: viewtac; intuition.
      + rewrite fun_add_spec. condtac; intuition.
      + rewrite ExecUnit.expr_wf; eauto. intuition.
      + revert H. rewrite fun_add_spec. condtac.
        * inversion e. i. inv H0. s. intuition.
        * i. exploit FWDBANK; eauto. i. des. intuition.
      + revert H. rewrite fun_add_spec. condtac.
        * inversion e. i. inv H0. s. apply join_spec.
          { rewrite ExecUnit.expr_wf; eauto. intuition. }
          { rewrite ExecUnit.expr_wf; eauto. intuition. }
        * i. exploit FWDBANK; eauto. i. des. intuition.
      + destruct ex; ss. rewrite EXBANK; ss. intuition.
      + apply Memory.get_msg_snoc_inv in MSG.
        revert TS. rewrite fun_add_spec. condtac.
        { i. des; intuition. }
        des.
        * eapply PROMISES0; eauto.
        * subst. ss. congr.
  Qed.      

  Lemma step_wf
        tid aeu1 aeu2
        (STEP: step tid aeu1 aeu2)
        (WF: ExecUnit.wf tid aeu1):
    ExecUnit.wf tid aeu2.
  Proof.
    inv STEP; eauto using state_step_wf, write_step_wf.
  Qed.
End AExecUnit.
Coercion AExecUnit.eu: AExecUnit.t >-> ExecUnit.t.

Inductive certify
          (tid:Id.t) (eu:ExecUnit.t (A:=unit)) (lock:Lock.t): Prop :=
| certify_intro
    aeu
    (STEPS: rtc (AExecUnit.step tid) (AExecUnit.init eu) aeu)
    (NOPROMISE: aeu.(ExecUnit.local).(Local.promises) = bot)
    (EX: lock.(Lock.ex) = Taint.is_locked aeu.(AExecUnit.aux).(AExecUnit.taint))
    (RELEASE: lock.(Lock.release) = aeu.(AExecUnit.aux).(AExecUnit.release))
.
Hint Constructors certify.

Lemma wf_certify
      tid (eu:ExecUnit.t (A:=unit))
      (PROMISES: eu.(ExecUnit.local).(Local.promises) = bot)
      (WF: ExecUnit.wf tid eu):
  certify tid eu Lock.init.
Proof.
  econs; eauto. s. funext. i. propext. econs; ss.
  intro X. inv X. inv R.
Qed.

Module AMachine.
  Inductive t := mk {
    machine: Machine.t;
    tlocks: IdMap.t Lock.t;
  }.
  Hint Constructors t.
  Coercion machine: t >-> Machine.t.

  Definition init (p:program): t :=
    mk
      (Machine.init p)
      (IdMap.map (fun _ => Lock.init) p).

  Inductive consistent (am: IdMap.t (Lock.t * (Loc.t -> nat))): Prop :=
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
      + inv STEP0. inv STEP. ss. rewrite MEM. eauto.
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
