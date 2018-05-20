Require Import Relations.
Require Import Permutation.
Require Import NArith.
Require Import PArith.
Require Import ZArith.
Require Import Lia.
Require Import FMapPositive.
Require Import FSetPositive.
Require Import EquivDec.
Require Import sflib.
Require Import paco.
Require Import HahnRelationsBasic.

Require Import Order.
Require Import Time.
Require Import Lang.
Require Import Memory.
Require Import Promising.
Require Import Axiomatic.

Set Implicit Arguments.


Lemma linearize A
      (l: list A)
      (rel: relation A)
      (ACYCLIC: acyclic rel):
  exists l',
    <<PERM: Permutation l' l>> /\
    <<REL: forall i j x y
             (X: List.nth_error l' i = Some x)
             (Y: List.nth_error l' j = Some y)
             (REL: rel x y),
        i < j>>.
Proof.
Admitted.

Inductive sim_label (tid:Id.t): forall (label:Label.t) (msg:Msg.t), Prop :=
| sim_label_intro
    ex ord loc val:
    sim_label tid (Label.write ex ord loc val) (Msg.mk loc val tid)
.
Hint Constructors sim_label.

(* TODO: move *)
Fixpoint filter_map A B (f: A -> option B) (l: list A): list B :=
  match l with
  | [] => []
  | a::l =>
    match f a with
    | None => filter_map f l
    | Some b => b :: filter_map f l
    end
  end.

Lemma in_filter_map_iff A B (f: A -> option B) (l: list A) (b: B):
  List.In b (filter_map f l) <-> exists a, List.In a l /\ f a = Some b.
Proof.
  induction l; ss.
  { econs; i; des; ss. }
  destruct (f a) eqn:FA; ss.
  - rewrite IHl. intuition; des; subst; eauto.
    rewrite FA in H2. inv H2. auto.
  - rewrite IHl. intuition; des; subst; eauto. congr.
 Qed.

Definition mem_of_ex
           (ex:Execution.t)
           (eids:list eidT):
  Memory.t :=
  filter_map
    (fun eid =>
       match Execution.label eid ex with
       | Some (Label.write ex ord loc val) => Some (Msg.mk loc val eid.(fst))
       | _ => None
       end)
    eids.

Definition list_rev_list_rect
           (A:Type)
           (P:list A -> Type)
           (INIT: P [])
	         (STEP: forall (a:A) (l:list A), P (List.rev l) -> P (List.rev (a :: l))):
	forall l:list A, P (List.rev l).
Proof.
  induction l; auto.
Defined.

Definition list_rev_rect
           (A:Type)
           (P:list A -> Type)
           (INIT: P [])
           (STEP: forall x l, P l -> P (l ++ [x])):
  forall l, P l.
Proof.
  intros.
  generalize (List.rev_involutive l).
  intros E; rewrite <- E.
  apply (list_rev_list_rect P).
  auto.

  simpl.
  intros.
  apply (STEP a (List.rev l0)).
  auto.
Defined.

Definition promises_from_mem
           (tid:Id.t) (mem: Memory.t): Promises.t.
Proof.
  induction mem using list_rev_rect.
  - apply Promises.empty.
  - destruct x.
    apply (if tid0 == tid
           then Promises.set (S (List.length (List.rev mem))) IHmem
           else IHmem).
Defined.

Lemma promises_from_mem_empty tid:
  promises_from_mem tid Memory.empty = Promises.empty.
Proof.
  unfold promises_from_mem, list_rev_rect, eq_rect. ss.
  match goal with
  | [|- context[match ?c with | eq_refl => _ end]] => destruct c
  end; ss.
Qed.

Lemma promises_from_mem_snoc tid mem msg:
  promises_from_mem tid (mem ++ [msg]) =
  if msg.(Msg.tid) == tid
  then Promises.set (S (List.length mem)) (promises_from_mem tid mem)
  else promises_from_mem tid mem.
Proof.
  unfold promises_from_mem at 1, list_rev_rect, eq_rect.
  match goal with
  | [|- context[match ?c with | eq_refl => _ end]] => destruct c
  end; ss.
  rewrite List.rev_involutive, List.rev_app_distr. ss.
  destruct msg. s. condtac.
  - inversion e. subst. rewrite ? List.rev_length.
    f_equal.
    unfold promises_from_mem, list_rev_rect, eq_rect.
    match goal with
    | [|- context[match ?c with | eq_refl => _ end]] => destruct c
    end; ss.
  - unfold promises_from_mem, list_rev_rect, eq_rect.
    match goal with
    | [|- context[match ?c with | eq_refl => _ end]] => destruct c
    end; ss.
Qed.

Definition Local_init_with_promises
           (promises: Promises.t): Local.t :=
  Local.mk bot bot bot bot bot bot bot
           (fun _ => None)
           bot
           promises.

Inductive sim_mem (ex:Execution.t) (mem: Memory.t): Prop :=
| sim_mem_intro
    eids
    (EIDS: Permutation eids (Execution.eids ex))
    (MEM: mem = mem_of_ex ex eids)
.
Hint Constructors sim_mem.

Inductive inverse A (rel:relation A) (codom:A -> Prop) (a:A): Prop :=
| inverse_intro
    a'
    (REL: rel a a')
    (CODOM: codom a')
.

Fixpoint view_eid (ex:Execution.t) (ob: list eidT) (eid:eidT): View.t :=
  match ob with
  | [] => 0
  | e::ob =>
    (if match Execution.label e ex with
        | Some label => Label.is_write label
        | None => false
        end
     then 1
     else 0) +
    (if e == eid
     then 0
     else view_eid ex ob eid)
  end.

Inductive sim_view (ex:Execution.t) (ob: list eidT) (eids:eidT -> Prop) (view:View.t): Prop :=
| sim_view_bot
    (VIEW: view = bot)
| sim_view_event
    eid
    (EID: eids eid)
    (VIEW: le view (view_eid ex ob eid))
.

Inductive sim_state (tid:Id.t) (ex:Execution.t) (ob: list eidT) (astate:State.t (A:=nat -> Prop)) (state:State.t (A:=View.t)): Prop :=
| sim_state_intro
    (STMTS: astate.(State.stmts) = state.(State.stmts))
    (RMAP: IdMap.Forall2
             (fun avala vala =>
                avala.(ValA.val) = vala.(ValA.val) /\
                sim_view ex ob (fun eid => eid.(fst) = tid /\ avala.(ValA.annot) eid.(snd)) vala.(ValA.annot))
             astate.(State.rmap) state.(State.rmap))
.
Hint Constructors sim_state.


Inductive sim_local (tid:Id.t) (ex:Execution.t) (ob: list eidT) (alocal:ALocal.t) (local:Local.t): Prop :=
| sim_local_intro
    eid
    (EID: eid = (tid, List.length (alocal.(ALocal.labels))))
    (COH: forall loc,
        sim_view
          ex ob
          (inverse
             (⦗ex.(Execution.label_is) (Label.is_writing loc)⦘ ⨾
              ex.(Execution.rfe)^? ⨾
              ex.(Execution.po))
             (eq eid))
          (local.(Local.coh) loc))
    (VRP:
       sim_view
         ex ob
         (inverse
            ((ex.(Execution.po) ⨾
              ⦗ex.(Execution.label_is) (eq (Label.barrier Barrier.dmbsy))⦘ ⨾
              (ex.(Execution.po))) ∪

             (⦗ex.(Execution.label_is) Label.is_read⦘ ⨾
              ex.(Execution.po) ⨾
              ⦗ex.(Execution.label_is) (eq (Label.barrier Barrier.dmbld))⦘ ⨾
              (ex.(Execution.po))) ∪

             ((ex.(Execution.ctrl) ∪ (ex.(Execution.addr) ⨾ ex.(Execution.po))) ⨾
              ⦗ex.(Execution.label_is) (eq (Label.barrier Barrier.isb))⦘ ⨾
              (ex.(Execution.po))) ∪

             (⦗ex.(Execution.label_is) (Label.is_acquire)⦘ ⨾
              (ex.(Execution.po))))
            (eq eid))
         local.(Local.vrp))
    (VWP:
       sim_view
         ex ob
         (inverse
            ((ex.(Execution.po) ⨾
              ⦗ex.(Execution.label_is) (eq (Label.barrier Barrier.dmbsy))⦘ ⨾
              (ex.(Execution.po))) ∪

             (⦗ex.(Execution.label_is) Label.is_read⦘ ⨾
              ex.(Execution.po) ⨾
              ⦗ex.(Execution.label_is) (eq (Label.barrier Barrier.dmbld))⦘ ⨾
              (ex.(Execution.po))) ∪

             (⦗ex.(Execution.label_is) Label.is_write⦘ ⨾
              ex.(Execution.po) ⨾
              ⦗ex.(Execution.label_is) (eq (Label.barrier Barrier.dmbst))⦘ ⨾
              (ex.(Execution.po))) ∪

             (⦗ex.(Execution.label_is) (Label.is_acquire)⦘ ⨾
              (ex.(Execution.po))))
            (eq eid))
         local.(Local.vwp))
    (VRM:
       sim_view
         ex ob
         (inverse
            (⦗ex.(Execution.label_is) (Label.is_read)⦘ ⨾ ex.(Execution.po))
            (eq eid))
         local.(Local.vrm))
    (VWM:
       sim_view
         ex ob
         (inverse
            (⦗ex.(Execution.label_is) (Label.is_write)⦘ ⨾ ex.(Execution.po))
            (eq eid))
         local.(Local.vwm))
    (VCAP:
       sim_view
         ex ob
         (inverse
            ((ex.(Execution.ctrl) ∪ (ex.(Execution.addr) ⨾ ex.(Execution.po))) ⨾ (ex.(Execution.po)))
            (eq eid))
         local.(Local.vcap))
    (VREL:
       sim_view
         ex ob
         (inverse
            (⦗ex.(Execution.label_is) (Label.is_release)⦘ ⨾ ex.(Execution.po))
            (eq eid))
         local.(Local.vrel))
.
Hint Constructors sim_local.
(* TODO: fwdbank, exbank, promises *)

Inductive sim_eu (tid:Id.t) (ex:Execution.t) (ob: list eidT) (aeu:AExecUnit.t) (eu:ExecUnit.t): Prop :=
| sim_eu_intro
    (STATE: sim_state tid ex ob aeu.(AExecUnit.state) eu.(ExecUnit.state))
    (LOCAL: sim_local tid ex ob aeu.(AExecUnit.local) eu.(ExecUnit.local))
    (MEM: eu.(ExecUnit.mem) = mem_of_ex ex ob)
.
Hint Constructors sim_eu.

Inductive tid_lift (tid:Id.t) (rel:relation nat) (eid1 eid2:eidT): Prop :=
| tid_lift_intro
    (TID1: eid1.(fst) = tid)
    (TID1: eid2.(fst) = tid)
    (REL: rel eid1.(snd) eid2.(snd))
.

Lemma sim_eu_step
      p ex ob tid aeu1 eu1 aeu2
      (EX: Valid.ex p ex)
      (OB: Permutation ob (Execution.eids ex))
      (SIM: sim_eu tid ex ob aeu1 eu1)
      (STEP: AExecUnit.step aeu1 aeu2)
      (ADDR: tid_lift tid aeu2.(AExecUnit.local).(ALocal.addr) ⊆ ex.(Execution.addr))
      (DATA: tid_lift tid aeu2.(AExecUnit.local).(ALocal.data) ⊆ ex.(Execution.data))
      (CTRL: tid_lift tid aeu2.(AExecUnit.local).(ALocal.ctrl) ⊆ ex.(Execution.ctrl)):
  exists eu2,
    <<STEP: ExecUnit.step tid eu1 eu2>> /\
    <<SIM: sim_eu tid ex ob aeu2 eu2>>.
Proof.
  destruct eu1 as [[stmts1 rmap1] local1].
  destruct aeu1 as [[astmts1 armap1] alocal1].
  destruct aeu2 as [[astmts2 armap2] alocal2].
  inv SIM. inv STATE. ss. subst. rename LOCAL into SIM_LOCAL.
  inv STEP. ss. inv STATE; inv LOCAL; inv EVENT; ss.
  - (* skip *)
    eexists (ExecUnit.mk _ _ _). esplits.
    + econs; ss.
      * econs; ss.
      * econs; ss.
    + econs; ss.
      admit. (* sim_local is proper w.r.t. relations *)
  - (* assign *)
    eexists (ExecUnit.mk _ _ _). esplits.
    + econs; ss.
      * econs; ss.
      * econs; ss.
    + econs; ss.
      * admit. (* sim_state after rmap update *)
      * admit. (* sim_local is proper w.r.t. relations *)
  - (* read *)
    eexists (ExecUnit.mk _ _ _). esplits.
    + econs; ss.
      * econs; ss.
      * econs 2; ss.
        admit. (* Local.read *)
    + admit. (* sim_eu *)
  - (* write *)
    admit.
  - (* write_failure *)
    admit.
  - destruct b0; eexists (ExecUnit.mk _ _ _).
    + (* isb *)
      esplits.
      * econs; ss.
        { econs; ss. }
        { econs 5; ss. }
      * admit. (* sim_eu *)
    + (* dmbst *)
      admit.
    + (* dmbld *)
      admit.
    + (* dmbsy *)
      admit.
  - (* if *)
    eexists (ExecUnit.mk _ _ _). esplits.
    + econs; ss.
      * econs; ss.
      * econs; ss.
    + econs; ss.
      * admit. (* sem_expr calculates the same value *)
      * admit. (* sim_local *)
  - (* dowhile *)
    eexists (ExecUnit.mk _ _ _). esplits.
    + econs; ss.
      * econs; ss.
      * econs; ss.
    + econs; ss.
      admit. (* sim_local is proper w.r.t. relations *)
Admitted.

Lemma sim_eu_rtc_step
      p ex ob tid aeu1 eu1 aeu2
      (EX: Valid.ex p ex)
      (OB: Permutation ob (Execution.eids ex))
      (SIM: sim_eu tid ex ob aeu1 eu1)
      (STEP: rtc AExecUnit.step aeu1 aeu2)
      (AEU: IdMap.find tid EX.(Valid.locals) = Some aeu2.(AExecUnit.local)):
  exists eu2,
    <<SIM: sim_eu tid ex ob aeu2 eu2>> /\
    <<STEP: rtc (ExecUnit.step tid) eu1 eu2>>.
Proof.
  revert eu1 SIM. induction STEP.
  { esplits; eauto. }
  i.
  assert (FUTURE: ALocal.future y.(AExecUnit.local) z.(AExecUnit.local)).
  { apply AExecUnit.rtc_step_future. ss. }
  exploit sim_eu_step; eauto.
  { rewrite EX.(Valid.ADDR).
    ii. destruct x0, y0. inv H0. ss. subst.
    econs; [eauto|eauto|s|s].
    - rewrite IdMap.map_spec, AEU. ss.
    - apply FUTURE. ss.
  }
  { rewrite EX.(Valid.DATA).
    ii. destruct x0, y0. inv H0. ss. subst.
    econs; [eauto|eauto|s|s].
    - rewrite IdMap.map_spec, AEU. ss.
    - apply FUTURE. ss.
  }
  { rewrite EX.(Valid.CTRL).
    ii. destruct x0, y0. inv H0. ss. subst.
    econs; [eauto|eauto|s|s].
    - rewrite IdMap.map_spec, AEU. ss.
    - apply FUTURE. ss.
  }
  i. des.
  exploit IHSTEP; eauto. i. des.
  esplits; eauto.
Qed.

Lemma promise_mem
      p mem
      (MEM: forall msg (MSG: List.In msg mem), IdMap.find msg.(Msg.tid) p <> None):
  exists m,
    <<STEP: rtc Machine.step0 (Machine.init p) m>> /\
    <<TPOOL: forall tid, IdMap.find tid m.(Machine.tpool) =
                    option_map
                      (fun stmts => (State.init stmts,
                                  Local_init_with_promises (promises_from_mem tid m.(Machine.mem))))
                      (IdMap.find tid p)>> /\
    <<MEM: m.(Machine.mem) = mem>>.
Proof.
  revert MEM. induction mem using List.rev_ind; i.
  { esplits; eauto. i. s. rewrite IdMap.map_spec.
    destruct (IdMap.find tid p); ss.
    unfold Local.init, Local_init_with_promises. repeat f_equal.
    rewrite promises_from_mem_empty. ss.
  }
  exploit IHmem; eauto.
  { i. apply MEM. apply List.in_app_iff. intuition. }
  i. des. subst. destruct x.
  hexploit MEM.
  { apply List.in_app_iff. right. left. eauto. }
  match goal with
  | [|- context[?f]] => destruct f eqn:FIND
  end; ss.
  intro X. clear X.
  eexists (Machine.mk _ _). esplits.
  - etrans; [eauto|]. econs 2; [|refl].
    econs.
    + rewrite TPOOL, FIND. ss.
    + econs 2; ss. econs; eauto. ss.
    + ss.
  - s. i. rewrite IdMap.add_spec. condtac; ss.
    + inversion e. subst. rewrite FIND. s.
      unfold Local_init_with_promises. repeat f_equal.
      rewrite promises_from_mem_snoc. condtac; ss.
    + rewrite TPOOL. destruct (IdMap.find tid0 p); ss.
      unfold Local_init_with_promises. rewrite promises_from_mem_snoc. s.
      condtac; ss. congr.
  - ss.
Qed.

Theorem axiomatic_to_promising
      p ex
      (EX: Valid.ex p ex):
  exists (m: Machine.t),
    <<STEP: rtc Machine.step (Machine.init p) m>> /\
    <<TERMINAL: Machine.is_terminal m>> /\
    <<MEM: sim_mem ex m.(Machine.mem)>>.
Proof.
  (* Linearize events and construct memory. *)
  exploit (linearize (Execution.eids ex)).
  { eapply EX.(Valid.EXTERNAL). }
  i. des. rename l' into eids.
  remember (mem_of_ex ex eids) as mem eqn:MEM.

  (* Construct promise steps. *)
  exploit (promise_mem p mem); eauto.
  { i. subst. unfold mem_of_ex in MSG. rewrite in_filter_map_iff in MSG. des.
    exploit Permutation_in; eauto. intro X.
    generalize (Execution.eids_spec ex). i. des.
    apply LABEL in X. destruct (Execution.label a ex) eqn:Y; ss.
    destruct t; ss. inv MSG0. s. unfold Execution.label in Y.
    rewrite EX.(Valid.LABELS), IdMap.map_spec in Y.
    destruct (IdMap.find (fst a) (Valid.locals (Valid.PRE EX))) eqn:Z; ss.
    generalize (EX.(Valid.LOCALS) (fst a)). intro W. inv W; ss. congr.
  }
  i. des. subst.

  (* It's sufficient to construct steps from the promised state. *)
  cut (exists m0,
          <<STEP: rtc Machine.step0 m m0>> /\
          <<TERMINAL: Machine.is_terminal m0>> /\
          <<MEM: sim_mem ex (Machine.mem m0)>>).
  { i. des. esplits; cycle 1; eauto.
    apply Machine.rtc_step0_step.
    - etrans; eauto.
    - econs. i. inv TERMINAL. exploit TERMINAL0; eauto. i. des. ss.
  }
  clear STEP.

  (* Execute threads one-by-one (induction). *)
  assert (IN: forall tid stmts
                (FIND1: IdMap.find tid p = Some stmts),
             IdMap.find tid m.(Machine.tpool) =
             Some (State.init stmts,
                   Local_init_with_promises (promises_from_mem tid (Machine.mem m)))).
  { i. rewrite TPOOL, FIND1. ss. }
  assert (OUT: forall tid st lc
                 (FIND1: IdMap.find tid p = None)
                 (FIND2: IdMap.find tid m.(Machine.tpool) = Some (st, lc)),
             State.is_terminal st /\ Promises.is_empty lc.(Local.promises)).
  { i. rewrite TPOOL, FIND1 in FIND2. ss. }
  assert (P: forall tid stmts
               (FIND1: IdMap.find tid p = Some stmts),
             IdMap.find tid p = Some stmts) by ss.

  clear TPOOL.
  setoid_rewrite IdMap.elements_spec in IN at 1.
  setoid_rewrite IdMap.elements_spec in OUT at 1.
  setoid_rewrite IdMap.elements_spec in P at 1.
  generalize (IdMap.elements_3w p). intro NODUP. revert NODUP.
  revert IN OUT P. generalize (IdMap.elements p). intro ps.
  revert m MEM0. induction ps; ss.
  { i. esplits; eauto. }
  i.

  destruct a as [tid stmts].
  exploit (IN tid); eauto.
  { destruct (equiv_dec tid tid); [|congr]. ss. }
  intro FIND.
  cut (exists st2 lc2,
          <<STEP: rtc (ExecUnit.step tid)
                      (ExecUnit.mk
                         (State.init stmts)
                         (Local_init_with_promises (promises_from_mem tid (Machine.mem m)))
                         (Machine.mem m))
                      (ExecUnit.mk st2 lc2 (Machine.mem m))>> /\
          <<TERMINAL: State.is_terminal st2 /\ Promises.is_empty lc2.(Local.promises)>>).
  { i. des. subst.
    exploit Machine.rtc_eu_step_step0; try exact STEP; eauto. i.
    assert (NOTIN: SetoidList.findA (fun id' : IdMap.key => if equiv_dec tid id' then true else false) ps = None).
    { inv NODUP. revert H1. clear. induction ps; ss.
      destruct a. i. destruct (equiv_dec tid k); eauto.
      inv e. contradict H1. left. ss.
    }
    exploit (IHps (Machine.mk
                     (IdMap.add tid (st2, lc2) (Machine.tpool m))
                     (Machine.mem m))); ss.
    { i. rewrite IdMap.add_spec. condtac; ss.
      - inversion e. subst. congr.
      - apply IN. destruct (equiv_dec tid0 tid); ss.
    }
    { i. revert FIND2. rewrite IdMap.add_spec. condtac.
      - i. inv FIND2. inversion e. eauto.
      - apply OUT. destruct (equiv_dec tid0 tid); ss.
    }
    { i. generalize (P tid0 stmts0). destruct (equiv_dec tid0 tid); eauto.
      inv e. congr.
    }
    { inv NODUP. ss. }
    i. des. esplits; cycle 1; eauto. etrans; eauto.
  }
  generalize (P tid stmts). destruct (equiv_dec tid tid); [|congr].
  intro FINDP. specialize (FINDP eq_refl).
  rewrite MEM0 in *.
  clear NODUP IN OUT P IHps MEM0 FIND ps e m.

  (* Execute a thread `tid`. *)
  generalize (EX.(Valid.LOCALS) tid). rewrite FINDP.
  intro X. inv X. des. rename b into local, H into LOCAL. clear FINDP.
  
  (* aex: (init stmts, init) -> (state, local)
   * ->
   * pex: (init stmts, init w/ promises) -> (state', local')
   * state ~= state': the same program state
   * local ~= local': the simulation relation
     - view: as @cp546 said
     - promises: (promises_from_mem tid (Machine.mem m)) - (fulfilled promises in local.labels)
       (finally we have to prove that (promises_from_mem tid (Machine.mem m)) = (fulfilled promises in local.labels))
   *)

  exploit (@sim_eu_rtc_step p ex eids tid); eauto.
  { instantiate (1 := ExecUnit.mk
                        (State.init stmts)
                        (Local_init_with_promises (promises_from_mem tid (mem_of_ex ex eids)))
                        (mem_of_ex ex eids)).
    econs; ss.
    - econs; ss. ii. rewrite ? IdMap.gempty. ss.
    - admit. (* sim_local holds initially. *)
  }
  i. des. destruct eu2 as [state2 local2 mem2]. inv SIM. ss. subst.
  esplits; eauto.
  - unfold State.is_terminal in *. inv STATE. congr.
  - admit. (* promises is empty. *)
Admitted.
