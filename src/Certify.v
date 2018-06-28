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
Require Import HahnSets.

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

  Inductive is_locked (lock:t) (l:Loc.t): Prop :=
  | is_locked_intro
      exlock
      (LOCK: lock.(ex) exlock)
      (LOC: exlock.(loc) = l)
      (RANGE: exlock.(from) = 0)
  .

  Inductive proceed (l:Loc.t) (lock1 lock2:t): Prop :=
  | proceed_intro
      (LOCK:
         forall elt,
           lock2.(ex) elt =
           lock1.(ex) (mk_ex elt.(loc) (S elt.(from)) (S elt.(to))) \/
           (elt.(from) = 0 /\ 0 < elt.(to) /\ lock1.(ex) (mk_ex elt.(loc) 0 (S elt.(to)))))
      (RELEASE:
         forall l' n' l'',
           lock2.(release) (l', n') l'' =
           let l1 := lock1.(release) (l', if l' == l then S n' else n') l'' in
           if l'' == l then Nat.pred l1 else l1)
  .
End Lock.

Module Taint.
  Inductive elt :=
  | R (id:nat) (loc:Loc.t) (from:nat)
  | W (id:nat) (loc:Loc.t) (to:nat)
  .
  Hint Constructors elt.

  Definition t := elt -> Prop.

  Inductive is_locked (taint:t) (lock:Lock.ex_t): Prop :=
  | is_locked_intro
      id
      (R: taint (R id lock.(Lock.loc) lock.(Lock.from)))
      (W: taint (W id lock.(Lock.loc) lock.(Lock.to)))
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
                            (join res.(ValA.annot).(View.annot) (ifc ex (eq (Taint.R aux.(ex_counter) vloc.(ValA.val) (aux.(st_counter) vloc.(ValA.val))))))))
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
      (PROMISE: aeu1.(ExecUnit.local).(Local.promises) <> bot)
      (STEP: ExecUnit.state_step0 tid (taint_read_event aeu2.(aux) e) e aeu1 aeu2)
      (AUX: aeu2.(aux) = state_step_aux e aeu1.(aux))
  .
  Hint Constructors state_step.

  Definition taint_write (ord:OrdW.t) (loc:Loc.t) (aux:aux_t): Taint.elt :=
    Taint.W aux.(ex_counter) loc (S (aux.(st_counter) loc)).

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
      (RES: res = ValA.mk _ 0 (View.mk bot (join view_ext.(View.annot) ((fun _ => ex) ∩₁ (eq (taint_write ord loc aux))))))
      (LC2: lc2 =
            Local.mk
              (fun_add loc ts lc1.(Local.coh))
              lc1.(Local.vrp)
              lc1.(Local.vwp)
              lc1.(Local.vrm)
              (join lc1.(Local.vwm) (View.mk ts bot))
              (join lc1.(Local.vcap) view_loc)
              (join lc1.(Local.vrel) (View.mk (ifc (OrdW.ge ord OrdW.release) ts) bot))
              (fun_add loc (Some (FwdItem.mk ts
                                             (joins [view_loc; view_val; View.mk bot ((fun _ => ex) ∩₁ (eq (taint_write ord loc aux)))])
                                             ex)) lc1.(Local.fwdbank))
              (if ex then None else lc1.(Local.exbank))
              lc1.(Local.promises))
  .
  Hint Constructors local_write.

  Inductive write_step (tid:Id.t) (aeu1 aeu2:t): Prop :=
  | write_step_intro
      ex ord vloc vval res
      (PROMISE: aeu1.(ExecUnit.local).(Local.promises) <> bot)
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

  Definition init_lc (tid:Id.t) (lc:Local.t (A:=unit)) (mem:Memory.t): Local.t (A:=Taint.t) :=
    Local.mk
      lc.(Local.coh)
      (init_view lc.(Local.vrp))
      (init_view lc.(Local.vwp))
      (init_view lc.(Local.vrm))
      (init_view lc.(Local.vwm))
      (View.mk lc.(Local.vcap).(View.ts)
               (match lc.(Local.exbank) with
                | Some (loc, _) => eq (Taint.R 0 loc 0)
                | None => bot
                end))
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

  Definition init (tid:Id.t) (eu:ExecUnit.t (A:=unit)): t :=
    mk
      (ExecUnit.mk (init_st eu.(ExecUnit.state)) (init_lc tid eu.(ExecUnit.local) eu.(ExecUnit.mem)) eu.(ExecUnit.mem))
      init_aux.

  Lemma taint_read_event_eqts aux e:
    eqts_event (taint_read_event aux e) e.
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
      + subst. revert H. rewrite fun_add_spec. condtac.
        * inversion e. i. inv H0. s. intuition.
        * i. exploit FWDBANK; eauto. i. des. intuition.
      + revert H. rewrite fun_add_spec. condtac.
        * inversion e. i. inv H0. s. repeat apply join_spec.
          all: try rewrite ExecUnit.expr_wf; eauto.
          all: intuition.
        * i. exploit FWDBANK; eauto. i. des. intuition.
      + destruct ex; ss.
        exploit EXBANK; eauto. i. des.
        eexists. apply Memory.read_mon. eauto.
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

  Lemma rtc_step_wf
        tid aeu1 aeu2
        (STEP: rtc (step tid) aeu1 aeu2)
        (WF: ExecUnit.wf tid aeu1):
    ExecUnit.wf tid aeu2.
  Proof.
    revert WF. induction STEP; ss.
    i. apply IHSTEP. eapply step_wf; eauto.
  Qed.

  Lemma init_wf
        tid (eu:ExecUnit.t (A:=unit))
        (WF: ExecUnit.wf tid eu):
    ExecUnit.wf tid (init tid eu).
  Proof.
    destruct eu as [st lc mem]. s.
    inv WF. econs; ss.
    - inv STATE. econs. i. specialize (RMAP r). revert RMAP.
      unfold RMap.find, init_rmap. rewrite IdMap.map_spec.
      destruct (IdMap.find r (State.rmap st)); ss.
    - inv LOCAL. econs; ss. i.
      destruct (Local.fwdbank lc loc) eqn:FWD; inv H. ss.
      exploit FWDBANK; eauto.
  Qed.
End AExecUnit.
Coercion AExecUnit.eu: AExecUnit.t >-> ExecUnit.t.

Inductive certify
          (tid:Id.t) (eu:ExecUnit.t (A:=unit)) (lock:Lock.t): Prop :=
| certify_intro
    aeu
    (STEPS: rtc (AExecUnit.step tid) (AExecUnit.init tid eu) aeu)
    (NOPROMISE: aeu.(ExecUnit.local).(Local.promises) = bot)
    (EX: lock.(Lock.ex) = Taint.is_locked aeu.(AExecUnit.aux).(AExecUnit.taint))
    (RELEASE: lock.(Lock.release) = aeu.(AExecUnit.aux).(AExecUnit.release))
.
Hint Constructors certify.
