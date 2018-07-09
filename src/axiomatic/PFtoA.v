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

Require Import PromisingArch.lib.Basic.
Require Import PromisingArch.lib.HahnRelationsMore.
Require Import PromisingArch.lib.Order.
Require Import PromisingArch.lib.Time.
Require Import PromisingArch.lib.Lang.
Require Import PromisingArch.promising.Promising.
Require Import PromisingArch.promising.StateExecFacts.
Require Import PromisingArch.axiomatic.Axiomatic.
Require Import PromisingArch.axiomatic.CommonAxiomatic.

Set Implicit Arguments.


Definition sim_view (vext: eidT -> Time.t) (view: Time.t) (eids: eidT -> Prop): Prop :=
  forall eid (EID: eids eid), le (vext eid) view.

Inductive sim_view_rev (vext: eidT -> Time.t) (view: Time.t) (eids: eidT -> Prop): Prop :=
| sim_view_rev_bot
    (VIEW: view = bot)
| sim_view_rev_event
    eid
    (EID: eids eid)
    (VIEW: le view (vext eid))
.
Hint Constructors sim_view_rev.

Definition sim_view_eq (vext: eidT -> Time.t) (view: Time.t) (eids: eidT -> Prop): Prop :=
  sim_view vext view eids /\ sim_view_rev vext view eids.

Inductive sim_val (tid:Id.t) (vext:eidT -> Time.t) (vala:ValA.t (A:=View.t (A:=unit))) (avala:ValA.t (A:=nat -> Prop)): Prop :=
| sim_val_intro
    (VAL: vala.(ValA.val) = avala.(ValA.val))
    (VIEW: sim_view vext vala.(ValA.annot).(View.ts) (fun eid => eid.(fst) = tid /\ avala.(ValA.annot) eid.(snd)))
.
Hint Constructors sim_val.

Inductive sim_rmap (tid:Id.t) (vext:eidT -> Time.t) (rmap:RMap.t (A:=View.t (A:=unit))) (armap:RMap.t (A:=nat -> Prop)): Prop :=
| sim_rmap_intro
    (RMAP: IdMap.Forall2 (fun reg => sim_val tid vext) rmap armap)
.
Hint Constructors sim_rmap.

Inductive sim_state (tid:Id.t) (vext:eidT -> Time.t) (state:State.t (A:=View.t (A:=unit))) (astate:State.t (A:=nat -> Prop)): Prop :=
| sim_state_intro
    (STMTS: state.(State.stmts) = astate.(State.stmts))
    (RMAP: sim_rmap tid vext state.(State.rmap) astate.(State.rmap))
.
Hint Constructors sim_state.

Lemma sim_rmap_add
      tid vext rmap armap reg vala avala
      (SIM: sim_rmap tid vext rmap armap)
      (VAL: sim_val tid vext vala avala):
  sim_rmap tid vext (RMap.add reg vala rmap) (RMap.add reg avala armap).
Proof.
  econs. ii. unfold RMap.add. rewrite ? IdMap.add_spec.
  inv SIM. condtac; eauto.
Qed.

Lemma sim_rmap_expr
      tid vext rmap armap e
      (SIM: sim_rmap tid vext rmap armap):
  sim_val tid vext (sem_expr rmap e) (sem_expr armap e).
Proof.
  inv SIM. induction e; s.
  - (* const *)
    econs; ss. ii. inv EID. inv H0.
  - (* reg *)
    specialize (RMAP reg). unfold RMap.find. inv RMAP; ss.
    econs; ss. ii. inv EID. inv H2.
  - (* op1 *)
    inv IHe. econs; ss. congr.
  - (* op2 *)
    inv IHe1. inv IHe2. econs; ss.
    + congr.
    + ii. des. inv EID0.
      * etrans; [|eapply join_l]; eauto.
      * etrans; [|eapply join_r]; eauto.
Qed.

Inductive sim_local (tid:Id.t) (ex: Execution.t) (vext: eidT -> Time.t) (local:Local.t (A:=unit)) (alocal:ALocal.t): Prop := mk_sim_local {
  COH: forall loc,
        sim_view
          vext
          (local.(Local.coh) loc)
          (inverse (sim_local_coh ex loc) (eq (tid, List.length (alocal.(ALocal.labels)))));
  VRP: sim_view
         vext
         local.(Local.vrp).(View.ts)
         (inverse (sim_local_vrp ex) (eq (tid, List.length (alocal.(ALocal.labels)))));
  VWP: sim_view
         vext
         local.(Local.vwp).(View.ts)
         (inverse (sim_local_vwp ex) (eq (tid, List.length (alocal.(ALocal.labels)))));
  VRM: sim_view
         vext
         local.(Local.vrm).(View.ts)
         (inverse (sim_local_vrm ex) (eq (tid, List.length (alocal.(ALocal.labels)))));
  VWM: sim_view
         vext
         local.(Local.vwm).(View.ts)
         (inverse (sim_local_vwm ex) (eq (tid, List.length (alocal.(ALocal.labels)))));
  VCAP: sim_view
          vext
          local.(Local.vcap).(View.ts)
          (inverse (sim_local_vcap ex) (eq (tid, List.length (alocal.(ALocal.labels)))));
  VREL: sim_view
          vext
          local.(Local.vrel).(View.ts)
          (inverse (sim_local_vrel ex) (eq (tid, List.length (alocal.(ALocal.labels)))));
  FWDBANK: forall loc,
      (exists eid,
          <<TS_NONZERO: (local.(Local.fwdbank) loc).(FwdItem.ts) > 0>> /\
          <<WRITE: sim_local_fwd ex loc eid (tid, List.length (alocal.(ALocal.labels)))>> /\
          <<TS: vext eid = (local.(Local.fwdbank) loc).(FwdItem.ts)>> /\
          <<VIEW: sim_view
                    vext
                    (local.(Local.fwdbank) loc).(FwdItem.view).(View.ts)
                    (inverse (ex.(Execution.addr) ∪ ex.(Execution.data)) (eq eid))>> /\
          <<EX: (local.(Local.fwdbank) loc).(FwdItem.ex) <-> ex.(Execution.label_is) (Label.is_ex) eid>>) \/
      ((local.(Local.fwdbank) loc) = FwdItem.init /\
       forall eid, ~ (inverse (sim_local_fwd_none ex loc) (eq (tid, List.length (alocal.(ALocal.labels)))) eid));
  EXBANK: opt_rel
            (fun aeb eb =>
               ex.(Execution.label_is) (Label.is_reading eb.(Exbank.loc)) (tid, aeb) /\
               sim_view_eq
                 vext
                 eb.(Exbank.ts)
                 (inverse ex.(Execution.rf) (eq (tid, aeb))) /\
               sim_view
                 vext
                 eb.(Exbank.view).(View.ts)
                 (eq (tid, aeb)))
            alocal.(ALocal.exbank) local.(Local.exbank);
  PROMISES: forall view (VIEW: Promises.lookup view local.(Local.promises)),
      exists n,
        <<N: (length alocal.(ALocal.labels)) <= n>> /\
        <<WRITE: ex.(Execution.label_is) Label.is_write (tid, n)>> /\
        <<VIEW: vext (tid, n) = view>>;
}.
Hint Constructors sim_local.

Inductive sim_eu (tid:Id.t) (ex:Execution.t) (vext: eidT -> Time.t) (eu:ExecUnit.t (A:=unit)) (aeu:AExecUnit.t): Prop :=
| sim_eu_intro
    (STATE: sim_state tid vext eu.(ExecUnit.state) aeu.(AExecUnit.state))
    (LOCAL: sim_local tid ex vext eu.(ExecUnit.local) aeu.(AExecUnit.local))
.
Hint Constructors sim_eu.

Inductive sim_val_weak (vala:ValA.t (A:=View.t (A:=unit))) (avala:ValA.t (A:=nat -> Prop)): Prop :=
| sim_val_weak_intro
    (VAL: vala.(ValA.val) = avala.(ValA.val))
.
Hint Constructors sim_val_weak.

Inductive sim_rmap_weak (rmap:RMap.t (A:=View.t (A:=unit))) (armap:RMap.t (A:=nat -> Prop)): Prop :=
| sim_rmap_weak_intro
    (RMAP: IdMap.Forall2 (fun reg => sim_val_weak) rmap armap)
.
Hint Constructors sim_rmap_weak.

Inductive sim_state_weak (state:State.t (A:=View.t (A:=unit))) (astate:State.t (A:=nat -> Prop)): Prop :=
| sim_state_weak_intro
    (STMTS: state.(State.stmts) = astate.(State.stmts))
    (RMAP: sim_rmap_weak state.(State.rmap) astate.(State.rmap))
.
Hint Constructors sim_state_weak.

Lemma sim_state_weak_init stmts:
  sim_state_weak (State.init stmts) (State.init stmts).
Proof.
  econs; ss. econs. ii. unfold RMap.init. rewrite ? IdMap.gempty. econs.
Qed.

Lemma sim_rmap_weak_add
      rmap armap reg vala avala
      (SIM: sim_rmap_weak rmap armap)
      (VAL: sim_val_weak vala avala):
  sim_rmap_weak (RMap.add reg vala rmap) (RMap.add reg avala armap).
Proof.
  econs. ii. unfold RMap.add. rewrite ? IdMap.add_spec.
  inv SIM. condtac; eauto.
Qed.

Lemma sim_rmap_weak_expr
      rmap armap e
      (SIM: sim_rmap_weak rmap armap):
  sim_val_weak (sem_expr rmap e) (sem_expr armap e).
Proof.
  inv SIM. induction e; s.
  - (* const *)
    econs; ss.
  - (* reg *)
    specialize (RMAP reg). unfold RMap.find. inv RMAP; ss.
  - (* op1 *)
    inv IHe. econs; ss. congr.
  - (* op2 *)
    inv IHe1. inv IHe2. econs; ss; try congr.
Qed.

Inductive sim_event: forall (e1: Event.t (A:=View.t (A:=unit))) (e2: Event.t (A:=nat -> Prop)), Prop :=
| sim_event_internal
    ctrl1 ctrl2:
    sim_event (Event.internal ctrl1) (Event.internal ctrl2)
| sim_event_read
    ex1 ord1 vloc1 val1
    ex2 ord2 vloc2 val2
    (EX: ex1 = ex2)
    (ORD: ord1 = ord2)
    (VLOC: sim_val_weak vloc1 vloc2)
    (VAL: sim_val_weak val1 val2):
    sim_event (Event.read ex1 ord1 vloc1 val1) (Event.read ex2 ord2 vloc2 val2)
| sim_event_write
    ex1 ord1 vloc1 vval1 res1
    ex2 ord2 vloc2 vval2 res2
    (EX: ex1 = ex2)
    (ORD: ord1 = ord2)
    (VLOC: sim_val_weak vloc1 vloc2)
    (VVAL: sim_val_weak vval1 vval2)
    (RES: sim_val_weak res1 res2):
    sim_event (Event.write ex1 ord1 vloc1 vval1 res1) (Event.write ex2 ord2 vloc2 vval2 res2)
| sim_event_barrier
    b1 b2
    (BARRIER: b1 = b2):
    sim_event (Event.barrier b1) (Event.barrier b2)
.
Hint Constructors sim_event.

Inductive sim_trace (p: program) (mem: Memory.t) (tid: Id.t):
  forall (tr: list (ExecUnit.t (A:=unit))) (atr: list AExecUnit.t)
     (wl: list (nat -> option (Loc.t * Time.t))) (rl: list (nat -> option (Loc.t * Time.t)))
     (cov: list (nat -> Time.t)) (vext: list (nat -> Time.t)), Prop :=
| sim_trace_init
    st lc stmts
    (FIND: IdMap.find tid (init_with_promises p mem).(Machine.tpool) = Some (st, lc))
    (STMT: IdMap.find tid p = Some stmts):
    sim_trace p mem tid [ExecUnit.mk st lc mem] [AExecUnit.mk (State.init stmts) ALocal.init]
              [fun _ => None] [fun _ => None] [fun _ => Time.bot] [fun _ => Time.bot]
| sim_trace_step
    e ae tr eu1 eu2 atr aeu1 aeu2 rl r1 r2 wl w1 w2 covl cov1 cov2 vextl vext1 vext2
    (STEP: ExecUnit.state_step0 tid e e eu1 eu2)
    (ASTATE_STEP: State.step ae aeu1.(AExecUnit.state) aeu2.(AExecUnit.state))
    (ALOCAL_STEP: ALocal.step ae aeu1.(AExecUnit.local) aeu2.(AExecUnit.local))
    (EVENT: sim_event e ae)
    (STATE: sim_state_weak eu2.(ExecUnit.state) aeu2.(AExecUnit.state))
    (W: w2 = match e with
             | Event.write _ _ vloc _ (ValA.mk _ 0 _) =>
               (fun eid => if Nat.eqb eid (ALocal.next_eid aeu1.(AExecUnit.local))
                         then Some (vloc.(ValA.val), (eu2.(ExecUnit.local).(Local.coh) vloc.(ValA.val)))
                         else w1 eid)
             | _ => w1
             end)
    (R: r2 = match e with
               | Event.read _ _ vloc _ =>
                 (fun eid => if Nat.eqb eid (ALocal.next_eid aeu1.(AExecUnit.local))
                            then Some (vloc.(ValA.val), (eu2.(ExecUnit.local).(Local.coh) vloc.(ValA.val)))
                            else r1 eid)
               | _ => r1
               end)
    (COV: cov2 = match e with
                 | Event.read _ _ vloc _
                 | Event.write _ _ vloc _ (ValA.mk _ 0 _) =>
                   (fun eid => if Nat.eqb eid (ALocal.next_eid aeu1.(AExecUnit.local))
                              then eu2.(ExecUnit.local).(Local.coh) vloc.(ValA.val)
                              else cov1 eid)
                 | _ => cov1
                 end)
    (VEXT: vext2 = match e with
                   | Event.read _ _ _ res =>
                     (fun eid => if Nat.eqb eid (ALocal.next_eid aeu1.(AExecUnit.local))
                                then res.(ValA.annot).(View.ts)
                                else vext1 eid)
                   | Event.write _ _ vloc _ (ValA.mk _ 0 _) =>
                     (fun eid => if Nat.eqb eid (ALocal.next_eid aeu1.(AExecUnit.local))
                                then eu2.(ExecUnit.local).(Local.coh) vloc.(ValA.val)
                                else vext1 eid)
                   | _ => vext1
                   end)
    (TRACE: sim_trace p mem tid (eu1::tr) (aeu1::atr) (w1::wl) (r1::rl) (cov1::covl) (vext1::vextl)):
    sim_trace p mem tid (eu2::eu1::tr) (aeu2::aeu1::atr) (w2::w1::wl) (r2::r1::rl) (cov2::cov1::covl) (vext2::vext1::vextl)
.

Definition sim_traces
           (p: program) (mem: Memory.t)
           (trs: IdMap.t (list (ExecUnit.t (A:=unit))))
           (atrs: IdMap.t (list AExecUnit.t))
           (ws: IdMap.t (list (nat -> option (Loc.t * Time.t))))
           (rs: IdMap.t (list (nat -> option (Loc.t * Time.t))))
           (covs: IdMap.t (list (nat -> Time.t)))
           (vexts: IdMap.t (list (nat -> Time.t)))
  : Prop :=
  IdMap.Forall6 (sim_trace p mem) trs atrs ws rs covs vexts.

Lemma sim_trace_last
      p mem tid tr atr wl rl covl vextl
      (SIM: sim_trace p mem tid tr atr wl rl covl vextl):
  exists eu tr' aeu atr' w wl' r rl' cov covl' vext vextl',
    <<HDTR: tr = eu :: tr'>> /\
    <<HDATR: atr = aeu :: atr'>> /\
    <<HDWL: wl = w :: wl'>> /\
    <<HDRL: rl = r :: rl'>> /\
    <<HDCOVL: covl = cov :: covl'>> /\
    <<HDVEXTL: vextl = vext :: vextl'>>.
Proof.
  inv SIM; esplits; eauto.
Qed.

Lemma sim_trace_length
      p mem tid tr atr wl rl covl vextl
      (SIM: sim_trace p mem tid tr atr wl rl covl vextl):
  <<LENGTH_ATR: List.length atr = List.length tr>> /\
  <<LENGTH_WL: List.length wl = List.length tr>> /\
  <<LENGTH_RL: List.length rl = List.length tr>> /\
  <<LENGTH_COVL: List.length covl = List.length tr>> /\
  <<LENGTH_VEXTL: List.length vextl = List.length tr>>.
Proof.
  induction SIM; ss. des. splits; congr.
Qed.

Lemma sim_traces_memory
      p trs atrs rs ws covs vexts
      m
      ts loc val tid
      (STEP: Machine.pf_exec p m)
      (SIM: sim_traces p m.(Machine.mem) trs atrs ws rs covs vexts)
      (TR: IdMap.Forall2
             (fun tid tr sl => exists l, tr = (ExecUnit.mk sl.(fst) sl.(snd) m.(Machine.mem)) :: l)
             trs m.(Machine.tpool))
      (GET: Memory.get_msg ts m.(Machine.mem) = Some (Msg.mk loc val tid)):
  exists eu, IdMap.find tid trs = Some eu.
Proof.
  generalize (SIM tid). intro X. inv X; eauto.
  generalize (TR tid). rewrite <- H0. intro X. inv X.
  inv STEP. hexploit state_exec_rtc_state_step; [by eauto|]. i. des.
  exploit step_get_msg_tpool.
  - etrans.
    + eapply Machine.rtc_step_mon; [|by eauto]. right. ss.
    + eapply Machine.rtc_step_mon; [|by eauto]. left. ss.
  - inv EQUIV. rewrite <- MEM. eauto.
  - s. i. des. inv EQUIV. generalize (TPOOL tid). congr.
Qed.

Ltac simplify :=
  repeat
    (try match goal with
         | [H1: _ = IdMap.find ?id ?m, H2: _ = IdMap.find ?id ?m |- _] =>
           rewrite <- H1 in H2; inv H2
         | [H1: IdMap.find ?id ?m = _, H2: IdMap.find ?id ?m = _ |- _] =>
           rewrite H1 in H2; inv H2
         | [H1: IdMap.find ?id ?m = _, H2: _ = IdMap.find ?id ?m |- _] =>
           rewrite H1 in H2; inv H2
         | [H: Some _ = Some _ |- _] => inv H
         | [H: _::_ = _::_ |- _] => inv H
         end).

Lemma promising_pf_sim_step
      tid e (eu1 eu2:ExecUnit.t (A:=unit)) aeu1
      (EU: sim_state_weak eu1.(ExecUnit.state) aeu1.(AExecUnit.state))
      (STEP: ExecUnit.state_step0 tid e e eu1 eu2):
  exists ae aeu2,
    <<ASTATE_STEP: State.step ae aeu1.(AExecUnit.state) aeu2.(AExecUnit.state)>> /\
    <<ALOCAL_STEP: ALocal.step ae aeu1.(AExecUnit.local) aeu2.(AExecUnit.local)>> /\
    <<EVENT: sim_event e ae>> /\
    <<STATE: sim_state_weak eu2.(ExecUnit.state) aeu2.(AExecUnit.state)>>.
Proof.
  destruct eu1 as [st1 lc1 mem1].
  destruct eu2 as [st2 lc2 mem2].
  destruct aeu1 as [[astmt1 armap1] alc1].
  inv EU. inv STEP. ss. subst. inv STATE; inv LOCAL; inv EVENT; ss.
  - inv LC.
    eexists _, (AExecUnit.mk (State.mk _ _) _). splits; ss.
    + econs 1.
    + econs; ss.
    + ss.
  - inv LC.
    eexists _, (AExecUnit.mk (State.mk _ _) _). splits; ss.
    + econs 2. ss.
    + econs; ss.
    + econs; ss. eauto using sim_rmap_weak_add, sim_rmap_weak_expr.
  - inv STEP. ss.
    eexists _, (AExecUnit.mk (State.mk _ _) _). splits; ss.
    + econs 3; ss.
    + econs 2; ss.
    + econs; ss. eauto using sim_rmap_weak_add, sim_rmap_weak_expr.
    + econs; ss. eauto using sim_rmap_weak_add, sim_rmap_weak_expr.
  - inv STEP. ss.
    eexists _, (AExecUnit.mk (State.mk _ _) _). splits; ss.
    + econs 4; ss.
    + econs 3; ss. inv WRITABLE. i. specialize (EX H). des.
      admit. (* exclusive *)
    + econs; ss.
      * eauto using sim_rmap_weak_add, sim_rmap_weak_expr.
      * eauto using sim_rmap_weak_add, sim_rmap_weak_expr.
    + econs; ss. eauto using sim_rmap_weak_add, sim_rmap_weak_expr.
  - inv STEP. destruct ex0; ss.
    eexists _, (AExecUnit.mk (State.mk _ _) _). splits; ss.
    + econs 4; ss.
    + econs 4; ss.
    + econs; ss.
      * eauto using sim_rmap_weak_add, sim_rmap_weak_expr.
      * eauto using sim_rmap_weak_add, sim_rmap_weak_expr.
    + econs; ss. eauto using sim_rmap_weak_add, sim_rmap_weak_expr.
  - inv STEP.
    eexists _, (AExecUnit.mk (State.mk _ _) _). splits; ss.
    + econs 5; ss.
    + econs 5; ss.
    + econs; ss.
    + econs; ss.
  - inv STEP.
    eexists _, (AExecUnit.mk (State.mk _ _) _). splits; ss.
    + econs 5; ss.
    + econs 5; ss.
    + econs; ss.
    + econs; ss.
  - inv LC.
    eexists _, (AExecUnit.mk (State.mk _ _) _). splits; ss.
    + econs 6; ss.
    + econs; ss.
    + econs; ss.
      exploit sim_rmap_weak_expr; eauto. intro X. inv X.
      inv VAL. rewrite H0. ss.
  - inv LC.
    eexists _, (AExecUnit.mk (State.mk _ _) _). splits; ss.
    + econs 7. ss.
    + econs; ss.
    + ss.
Admitted.

Lemma promising_pf_sim_traces
      p m
      (STEP: Machine.pf_exec p m):
  exists trs atrs ws rs covs vexts ex (PRE: Valid.pre_ex p ex),
    <<SIM: sim_traces p m.(Machine.mem) trs atrs ws rs covs vexts>> /\
    <<TR: IdMap.Forall2
            (fun tid tr sl => exists l, tr = (ExecUnit.mk sl.(fst) sl.(snd) m.(Machine.mem)) :: l)
            trs m.(Machine.tpool)>> /\
    <<ATR: IdMap.Forall2
             (fun tid atr aeu => exists l, atr = aeu :: l)
             atrs PRE.(Valid.aeus)>>.
Proof.
  inv STEP. exploit state_exec_rtc_state_step; eauto. i. des.
  eapply Machine.equiv_no_promise in NOPROMISE; eauto. revert NOPROMISE.
  cut (exists trs atrs ws rs covs vexts ex (PRE: Valid.pre_ex p ex),
    <<SIM: sim_traces p (Machine.mem m2') trs atrs ws rs covs vexts>> /\
    <<TR: forall tid, opt_rel
            (fun tr sl => exists l, tr = (ExecUnit.mk sl.(fst) sl.(snd) (Machine.mem m2')) :: l)
            (IdMap.find tid trs)
            (IdMap.find tid (Machine.tpool m2'))>> /\
    <<ATR: IdMap.Forall2
             (fun tid atr aeu => exists l, atr = aeu :: l)
             atrs PRE.(Valid.aeus)>>).
  { inv EQUIV. rewrite MEM. i. des. esplits; eauto. ii. rewrite TPOOL. ss. }
  clear m STEP2 EQUIV.
  apply clos_rt_rt1n_iff, clos_rt_rtn1_iff in EXEC. induction EXEC.
  { eexists (IdMap.map (fun x => [x]) (IdMap.mapi (fun _ _ => _) p)).
    eexists (IdMap.map (fun x => [x]) (IdMap.mapi (fun _ _ => _) p)).
    eexists (IdMap.mapi (fun _ _ => [fun _ => None]) p).
    eexists (IdMap.mapi (fun _ _ => [fun _ => None]) p).
    eexists (IdMap.mapi (fun _ _ => [bot]) p).
    eexists (IdMap.mapi (fun _ _ => [bot]) p).
    eexists (Execution.mk (IdMap.mapi (fun _ _ => _) p) bot bot bot bot bot bot).
    eexists (@Valid.mk_pre_ex _ _ (IdMap.mapi (fun tid stmts => AExecUnit.mk (State.init stmts) ALocal.init) p)  _ _ _ _ _ _).
    hexploit rtc_promise_step_spec; eauto. s. intro X.
    s. splits; cycle 1.
    - i. specialize (X tid). rewrite ? IdMap.map_spec, ? IdMap.mapi_spec in *.
      rewrite X. destruct (IdMap.find tid p); ss. econs. eauto.
    - ii. rewrite ? IdMap.map_spec, ? IdMap.mapi_spec. destruct (IdMap.find id p); ss. eauto.
    - ii. rewrite ? IdMap.map_spec, ? IdMap.mapi_spec. destruct (IdMap.find id p) eqn:STMTS; ss. econs.
      econs 1; ss. rewrite IdMap.mapi_spec, STMTS. s. ss.
  }
  des.
  destruct y as [tpool1 mem1].
  destruct z as [tpool2 mem2].
  ss. inv H. ss. subst. inv STEP. inv STEP0. ss. subst.
  generalize (TR tid). rewrite FIND. intro Y. inv Y. des. subst. rename H0 into TRS. symmetry in TRS.
  generalize (SIM tid). intro Y. inv Y; [congr|]. rewrite TRS in H0. inv H0.
  hexploit sim_trace_last; eauto. i. des. subst. simplify.
  exploit promising_pf_sim_step; eauto.
  { inv REL6; eauto. s.
    unfold init_with_promises in FIND0. ss.
    rewrite IdMap.mapi_spec, STMT in *. inv FIND0.
    apply sim_state_weak_init.
  }
  { instantiate (1 := ExecUnit.mk _ _ _). econs; ss; eauto. }
  i. des.

  eexists (IdMap.add tid _ trs).
  eexists (IdMap.add tid _ atrs).
  eexists (IdMap.add tid _ ws).
  eexists (IdMap.add tid _ rs).
  eexists (IdMap.add tid _ covs).
  eexists (IdMap.add tid _ vexts).
  eexists (Execution.mk _ _ _ _ _ _ _).
  eexists (@Valid.mk_pre_ex _ _ (IdMap.add tid _ PRE.(Valid.aeus))  _ _ _ _ _ _).
  s. splits; cycle 1.
  - i. rewrite ? IdMap.add_spec. condtac; eauto.
  - ii. rewrite ? IdMap.add_spec. condtac; eauto.
  - s. ii. rewrite ? IdMap.add_spec. condtac; eauto. inversion e0. subst. clear e0 X. econs.
    econs 2; eauto. econs; eauto.
Grab Existential Variables.
all: ss.
1: { ii. generalize (PRE.(Valid.AEUS) id). intro X.
     rewrite IdMap.add_spec. condtac; ss. inversion e0. subst. clear e0 X0.
     generalize (ATR tid). rewrite <- H. intro Y. inv Y. des. inv REL.
     rewrite <- H6 in X. inv X. econs. etrans; eauto.
}
3: { funext. i. funext. i. propext. econs; ss. i. inv H.
     rewrite IdMap.map_spec, IdMap.mapi_spec in RELS. destruct (IdMap.find tid p); ss.
     inv RELS. inv REL. ss.
}
3: { funext. i. funext. i. propext. econs; ss. i. inv H.
     rewrite IdMap.map_spec, IdMap.mapi_spec in RELS. destruct (IdMap.find tid p); ss.
     inv RELS. inv REL. ss.
}
3: { funext. i. funext. i. propext. econs; ss. i. inv H.
     rewrite IdMap.map_spec, IdMap.mapi_spec in RELS. destruct (IdMap.find tid p); ss.
     inv RELS. inv REL. ss.
}
3: { funext. i. funext. i. propext. econs; ss. i. inv H.
     rewrite IdMap.map_spec, IdMap.mapi_spec in RELS. destruct (IdMap.find tid p); ss.
     inv RELS. inv REL. ss.
}
4: { ii. rewrite IdMap.mapi_spec. destruct (IdMap.find id p); ss. econs. refl. }
3: { unfold IdMap.map.

     (* TODO: move *)
     Lemma IdMap_mapi_mapi
           A B C
           (f: Id.t -> A -> B)
           (g: Id.t -> B -> C)
           m:
       IdMap.mapi g (IdMap.mapi f m) = IdMap.mapi (fun tid a => g tid (f tid a)) m.
     Proof.
       unfold IdMap.mapi. generalize 1%positive. induction m; ss.
       i. rewrite IHm1, IHm2. f_equal. destruct o; ss.
     Qed.

     rewrite IdMap_mapi_mapi. f_equal.
}
1: { apply bot. (* it's ex's co. *) }
1: { apply bot. (* it's ex's rf. *) }
Qed.      

Inductive co_gen (ws: IdMap.t (list (nat -> option (Loc.t * Time.t)))) (eid1 eid2: eidT): Prop :=
| co_gen_intro
    w1 wl1 ts1 loc1 w2 wl2 ts2 loc2
    (WS1: IdMap.find eid1.(fst) ws = Some (w1::wl1))
    (W1: w1 eid1.(snd) = Some (loc1, ts1))
    (WS2: IdMap.find eid2.(fst) ws = Some (w2::wl2))
    (W2: w2 eid2.(snd) = Some (loc2, ts2))
    (LOC: loc1 = loc2)
    (TS: Time.lt ts1 ts2)
.

Inductive rf_gen (ws: IdMap.t (list (nat -> option (Loc.t * Time.t)))) (rs: IdMap.t (list (nat -> option (Loc.t *Time.t)))) (eid1 eid2: eidT): Prop :=
| rf_gen_intro
    w wl ts1 loc1 r rl loc2 ts2
    (WS: IdMap.find eid1.(fst) ws = Some (w::wl))
    (W: w eid1.(snd) = Some (loc1, ts1))
    (RS: IdMap.find eid2.(fst) rs = Some (r::rl))
    (R: r eid2.(snd) = Some (loc2, ts2))
    (LOC: loc1 = loc2)
    (TS: ts1 = ts2)
.

Definition v_gen (vs: IdMap.t (list (nat -> Time.t))) (eid: eidT): Time.t :=
  match IdMap.find eid.(fst) vs with
  | Some (v::vl) => v eid.(snd)
  | _ => Time.bot
  end
.

Inductive sim_th
          (p:program) (mem:Memory.t) (tid:Id.t)
          (eu:ExecUnit.t (A:=unit))
          (aeu:AExecUnit.t)
          (w: nat -> option (Loc.t * Time.t))
          (r: nat -> option (Loc.t * Time.t))
          (cov: nat -> Time.t)
          (vext: nat -> Time.t): Prop := mk {
  WPROP1:
    forall ts loc val
      (GET: Memory.get_msg ts mem = Some (Msg.mk loc val tid)),
      ((Promises.lookup ts eu.(ExecUnit.local).(Local.promises) = true /\
        forall eid, w eid <> Some (loc, ts)) \/
       (Promises.lookup ts eu.(ExecUnit.local).(Local.promises) = false /\
        exists eid ex ord,
          w eid = Some (loc, ts) /\
          List.nth_error aeu.(AExecUnit.local).(ALocal.labels) eid = Some (Label.write ex ord loc val)));
  WPROP2:
    forall eid ex ord loc val
      (GET: List.nth_error aeu.(AExecUnit.local).(ALocal.labels) eid = Some (Label.write ex ord loc val)),
    exists ts,
      w eid = Some (loc, ts) /\
      Memory.get_msg ts mem = Some (Msg.mk loc val tid);
  WPROP3:
    forall eid loc ts (GET: w eid = Some (loc, ts)),
      Time.lt Time.bot ts /\
      le ts (eu.(ExecUnit.local).(Local.coh) loc) /\
      exists ex ord val,
        List.nth_error aeu.(AExecUnit.local).(ALocal.labels) eid = Some (Label.write ex ord loc val) /\
        Memory.get_msg ts mem = Some (Msg.mk loc val tid);
  WPROP4:
    forall eid1 loc1 eid2 loc2 ts (W1: w eid1 = Some (loc1, ts)) (W2: w eid2 = Some (loc2, ts)),
      eid1 = eid2;
  RPROP1:
    forall eid ex ord loc val
      (GET: List.nth_error aeu.(AExecUnit.local).(ALocal.labels) eid = Some (Label.read ex ord loc val)),
    exists ts tid',
      r eid = Some (loc, ts) /\
      __guard__ ((ts = Time.bot /\ val = Val.default) \/
                 Memory.get_msg ts mem = Some (Msg.mk loc val tid'));
  RPROP2:
    forall eid loc ts (GET: r eid = Some (loc, ts)),
    le ts (eu.(ExecUnit.local).(Local.coh) loc) /\
    exists ex ord val tid',
      List.nth_error aeu.(AExecUnit.local).(ALocal.labels) eid = Some (Label.read ex ord loc val) /\
      __guard__ ((ts = Time.bot /\ val = Val.default) \/
                 Memory.get_msg ts mem = Some (Msg.mk loc val tid'));
  WCV: forall eid ts (W: w eid = Some ts),
      (exists ex ord loc val,
          List.nth_error aeu.(AExecUnit.local).(ALocal.labels) eid = Some (Label.write ex ord loc val)) /\
      cov eid = ts.(snd) /\
      vext eid = ts.(snd);
  RCV: forall eid ts (R: r eid = Some ts),
      (exists ex ord loc val,
          List.nth_error aeu.(AExecUnit.local).(ALocal.labels) eid = Some (Label.read ex ord loc val)) /\
      cov eid = ts.(snd);
  PO: forall iid1 iid2 label1 label2
     (PO: iid1 < iid2)
     (LABEL1: List.nth_error aeu.(AExecUnit.local).(ALocal.labels) iid1 = Some label1)
     (LABEL2: List.nth_error aeu.(AExecUnit.local).(ALocal.labels) iid2 = Some label2)
     (REL: Execution.label_loc label1 label2),
      <<PO_LOC_WRITE:
        Label.is_write label2 ->
        Time.lt (cov iid1) (cov iid2)>> /\
      <<PO_LOC_READ:
        Label.is_read label2 ->
        Time.le (cov iid1) (cov iid2)>>;
}.

Lemma sim_trace_sim_th
      p mem tid
      tr eu tr'
      atr aeu atr'
      wl w wl'
      rl r rl'
      covl cov covl'
      vextl vext vextl'
      (SIM: sim_trace p mem tid tr atr wl rl covl vextl)
      (EU: tr = eu :: tr')
      (AEU: atr = aeu :: atr')
      (RL: rl = r :: rl')
      (WL: wl = w :: wl')
      (COV: covl = cov :: covl')
      (VEXT: vextl = vext :: vextl'):
      (* (MEM: mem = eu.(ExecUnit.mem)): TODO: enable it *)
  sim_th p mem tid eu aeu w r cov vext.
Proof.
  revert r rl' w wl' eu tr' aeu atr' cov covl' vext vextl' RL WL EU AEU COV VEXT. induction SIM.
  (* revert r rl' w wl' eu tr' aeu atr' cov covl' vext vextl' RL WL EU AEU COV VEXT MEM. induction SIM. *)
  { i. simplify. ss. econs; ss.
    - rewrite IdMap.mapi_spec, STMT in FIND. inv FIND. s. i.
      left. splits; ss. admit. (* promises_from_mem *)
    - rewrite IdMap.mapi_spec, STMT in FIND. inv FIND. s. i.
      destruct eid; ss.
    - rewrite IdMap.mapi_spec, STMT in FIND. inv FIND. s. i.
      destruct eid; ss.
    - i. destruct iid1; ss.
  }
  i. simplify.
  destruct eu1 as [st1 lc1 mem1].
  destruct eu as [st2 lc2 mem2].
  destruct aeu1 as [ast1 alc1].
  destruct aeu as [ast2 alc2].
  assert (mem1 = mem) by admit. subst.
  ss. exploit IHSIM; eauto.
  (* { admit. (* mem is preserved *) } *)
  i. des. rename x into IH.
  inv STEP. inv ALOCAL_STEP; inv EVENT; ss; eauto.
  { (* internal *)
    inv LOCAL; ss. inv LC. inv EVENT. econs; ss; try by apply IH.
  }
  { (* read *)
    inv LOCAL; ss. inv STEP. inv STATE0. inv ASTATE_STEP. ss. inv EVENT.

    (* TODO: move *)
    Lemma sim_trace_sim_state_weak
          p mem tid
          tr eu tr'
          atr aeu atr'
          wl w wl'
          rl r rl'
          covl cov covl'
          vextl vext vextl'
          (SIM: sim_trace p mem tid tr atr wl rl covl vextl)
          (EU: tr = eu :: tr')
          (AEU: atr = aeu :: atr')
          (RL: rl = r :: rl')
          (WL: wl = w :: wl')
          (COV: covl = cov :: covl')
          (VEXT: vextl = vext :: vextl'):
      sim_state_weak eu.(ExecUnit.state) aeu.(AExecUnit.state).
    Proof.
      subst. inv SIM; ss.
      rewrite IdMap.mapi_spec, STMT in FIND. inv FIND.
      eapply sim_state_weak_init.
    Qed.

    exploit sim_trace_sim_state_weak; eauto. s. intro Y. inv Y. ss. inv STMTS.
    exploit sim_rmap_weak_expr; eauto. intro Y. inv Y.

    econs; ss.
    - i. exploit IH.(WPROP1); eauto. s. i. des; [left|right]; esplits; eauto.
      eapply nth_error_app_mon. eauto.
    - i. exploit IH.(WPROP2); eauto.
      apply nth_error_app_inv in GET. des; eauto.
      apply nth_error_singleton_inv in GET0. des. congr.
    - i. exploit IH.(WPROP3); eauto. s. i. des. esplits; eauto.
      + rewrite fun_add_spec. des_ifs; eauto. inv e. etrans; eauto.
      + eapply nth_error_app_mon. eauto.
    - eapply IH.(WPROP4).
    - i. apply nth_error_app_inv in GET. des.
      + exploit IH.(RPROP1); eauto. i. des. esplits; eauto.
        des_ifs. apply Nat.eqb_eq in Heq. subst. unfold ALocal.next_eid in *. lia.
      + apply nth_error_singleton_inv in GET0. des.
        replace eid with (length (ALocal.labels alc1)) in * by lia.
        des_ifs; cycle 1.
        { apply Nat.eqb_neq in Heq. unfold ALocal.next_eid in *. congr. }
        rewrite fun_add_spec. condtac; [|congr].
        inv VLOC. inv VAL. ss. subst. rewrite VAL1 in *.

        (* TODO: move *)
        Lemma read_get_msg
              loc ts mem val
              (READ: Memory.read loc ts mem = Some val):
          (ts = Time.bot /\ val = Val.default) \/
          (exists tid, Memory.get_msg ts mem = Some (Msg.mk loc val tid)).
        Proof.
          revert READ. unfold Memory.read, Memory.get_msg. destruct ts; ss.
          - i. inv READ. left. eauto.
          - destruct (List.nth_error mem ts); ss. des_ifs. i. inv READ. inv e.
            destruct t. s. right. eauto.
        Qed.

        exploit read_get_msg; eauto. i. des.
        { esplits; eauto. left. eauto. }
        esplits; eauto. right. eauto.
    - i. des_ifs.
      + apply Nat.eqb_eq in Heq. subst. rewrite fun_add_spec. des_ifs; [|congr].
        inv VLOC. inv VAL. ss. subst. rewrite VAL1 in *.
        exploit read_get_msg; eauto. i. des.
        { esplits; ss.
          - rewrite List.nth_error_app2, Nat.sub_diag; [|refl]. ss.
          - left. ss.
        }
        esplits; ss.
        * rewrite List.nth_error_app2, Nat.sub_diag; [|refl]. ss.
        * right. eauto.
      + exploit IH.(RPROP2); eauto. s. i. des. esplits; eauto.
        * rewrite fun_add_spec. des_ifs; eauto. inv e. etrans; eauto.
        * eapply nth_error_app_mon. eauto.
    - i. exploit IH.(WCV); eauto. s. i. des. des_ifs.
      { exfalso. apply Nat.eqb_eq in Heq. subst.
        unfold ALocal.next_eid in *.
        assert (H: List.nth_error (ALocal.labels alc1) (length (ALocal.labels alc1)) <> None) by (ii; congr).
        apply List.nth_error_Some in H. lia.
      }
      esplits; eauto. eapply nth_error_app_mon. eauto.
    - i. des_ifs.
      + apply Nat.eqb_eq in Heq. subst. esplits; eauto.
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
      + exploit IH.(RCV); eauto. s. i. des. esplits; eauto.
        eapply nth_error_app_mon. eauto.
    - admit. (* po *)
  }
  { (* write *)
    inv LOCAL; inv EVENT; inv RES; inv STEP; ss. inv STATE. ss. econs; ss.
    - i. exploit IH.(WPROP1); eauto. s. i. rewrite Promises.unset_o. des_ifs.
      { inv e. right. rewrite MSG in GET. inv GET. esplits; ss.
        - instantiate (1 := ALocal.next_eid alc1). des_ifs; cycle 1.
          { apply Nat.eqb_neq in Heq. congr. }
          rewrite fun_add_spec. des_ifs. congr.
        - rewrite List.nth_error_app2, Nat.sub_diag; ss.
          inv VLOC. inv VVAL. rewrite VAL0, VAL1. eauto.
      }
      des; [left|right]; splits; ss.
      + i. des_ifs; eauto. apply Nat.eqb_eq in Heq. subst. ii. inv H.
        rewrite fun_add_spec in c. des_ifs; [|congr]. congr.
      + esplits; eauto.
        * des_ifs; eauto. apply Nat.eqb_eq in Heq. subst. unfold ALocal.next_eid in *.
          assert (H: List.nth_error (ALocal.labels alc1) (length (ALocal.labels alc1)) <> None) by (ii; congr).
          apply List.nth_error_Some in H. lia.
        * eapply nth_error_app_mon. eauto.
    - i. unfold ALocal.next_eid in *. apply nth_error_app_inv in GET. des.
      + des_ifs.
        { apply Nat.eqb_eq in Heq. subst. lia. }
        eapply IH.(WPROP2); eauto.
      + apply nth_error_singleton_inv in GET0. des.
        des_ifs; cycle 1.
        { apply Nat.eqb_neq in Heq. lia. }
        esplits; eauto.
        * inv VLOC. rewrite VAL0. eauto.
        * rewrite fun_add_spec. des_ifs; [|congr].
          inv VLOC. inv VVAL. rewrite <- VAL0, <- VAL1. eauto.
    - i. unfold ALocal.next_eid in *. des_ifs.
      + apply Nat.eqb_eq in Heq. subst. rewrite fun_add_spec. des_ifs; [|congr]. inv e.
        destruct ts; ss. esplits; eauto.
        * unfold Time.lt, Time.bot. lia.
        * refl.
        * rewrite List.nth_error_app2, Nat.sub_diag; ss.
          inv VLOC. inv VVAL. rewrite VAL0, VAL1. eauto.
      + exploit IH.(WPROP3); eauto. s. i. des. esplits; eauto.
        * rewrite fun_add_spec. des_ifs; eauto. inv e. etrans; eauto.
          inv WRITABLE. apply Nat.lt_le_incl. ss.
        * eapply nth_error_app_mon. eauto.
    - i. unfold ALocal.next_eid in *. des_ifs.
      + apply Nat.eqb_eq in Heq. apply Nat.eqb_eq in Heq0. subst. ss.
      + rewrite fun_add_spec in *. des_ifs; [|congr].
        exploit IH.(WPROP3); eauto. s. i. des.
        exploit IH.(WPROP1); eauto. s. rewrite PROMISE. i. des; ss.
        rewrite MSG in x3. inv x3. clear -WRITABLE x1. unfold le in x1. inv WRITABLE. lia.
      + rewrite fun_add_spec in *. des_ifs; [|congr].
        exploit IH.(WPROP3); eauto. s. i. des.
        exploit IH.(WPROP1); eauto. s. rewrite PROMISE. i. des; ss.
        rewrite MSG in x3. inv x3. clear -WRITABLE x1. unfold le in x1. inv WRITABLE. lia.
      + eapply IH.(WPROP4); eauto.
    - i. exploit IH.(RPROP1); eauto.
      apply nth_error_app_inv in GET. des; eauto.
      apply nth_error_singleton_inv in GET0. des. congr.
    - i. exploit IH.(RPROP2); eauto. s. i. des. esplits; eauto.
      * rewrite fun_add_spec. des_ifs; eauto. inv e. etrans; eauto.
        inv WRITABLE. apply Nat.lt_le_incl. ss.
      * eapply nth_error_app_mon. eauto.
    - i. des_ifs.
      + rewrite Nat.eqb_eq in Heq. subst. esplits; eauto.
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
      + exploit IH.(WCV); eauto. s. i. des. esplits; eauto.
        eapply nth_error_app_mon. eauto.
    - i. exploit IH.(RCV); eauto. s. i. des. esplits; eauto.
      + eapply nth_error_app_mon. eauto.
      + des_ifs.
        exfalso. apply Nat.eqb_eq in Heq. subst.
        unfold ALocal.next_eid in *.
        assert (H: List.nth_error (ALocal.labels alc1) (length (ALocal.labels alc1)) <> None) by (ii; congr).
        apply List.nth_error_Some in H. lia.
    - admit. (* po *)
  }
  { (* write failure *)
    inv RES. destruct res1. ss. subst.
    inv LOCAL; ss; inv STEP; ss. inv EVENT. econs; ss; try by apply IH.
  }
  { (* barrier *)
    inv LOCAL; ss.
    { (* isb *)
      inv STEP. inv ASTATE_STEP. ss. inv EVENT. econs; ss.
      - i. exploit IH.(WPROP1); eauto. s. i. des; [left|right]; esplits; eauto.
        eapply nth_error_app_mon. eauto.
      - i. exploit IH.(WPROP2); eauto.
        apply nth_error_app_inv in GET. des; eauto.
        apply nth_error_singleton_inv in GET0. des. congr.
      - i. exploit IH.(WPROP3); eauto. i. des. esplits; eauto.
        eapply nth_error_app_mon. eauto.
      - eapply IH.(WPROP4).
      - i. exploit IH.(RPROP1); eauto.
        apply nth_error_app_inv in GET. des; eauto.
        apply nth_error_singleton_inv in GET0. des. congr.
      - i. exploit IH.(RPROP2); eauto. s. i. des. esplits; eauto.
        eapply nth_error_app_mon. eauto.
      - i. exploit IH.(WCV); eauto. s. i. des. esplits; eauto.
        eapply nth_error_app_mon. eauto.
      - i. exploit IH.(RCV); eauto. s. i. des. esplits; eauto.
        eapply nth_error_app_mon. eauto.
      - i. apply nth_error_app_inv in LABEL1. des; cycle 1.
        { apply nth_error_singleton_inv in LABEL0. des. subst. inv REL. inv X. }
        apply nth_error_app_inv in LABEL2. des; cycle 1.
        { apply nth_error_singleton_inv in LABEL3. des. subst. inv REL. inv Y. }
        eapply IH.(PO); eauto.
    }
    { (* isb *)
      inv STEP. inv ASTATE_STEP. ss. inv EVENT. econs; ss.
      - i. exploit IH.(WPROP1); eauto. s. i. des; [left|right]; esplits; eauto.
        eapply nth_error_app_mon. eauto.
      - i. exploit IH.(WPROP2); eauto.
        apply nth_error_app_inv in GET. des; eauto.
        apply nth_error_singleton_inv in GET0. des. congr.
      - i. exploit IH.(WPROP3); eauto. s. i. des. esplits; eauto.
        eapply nth_error_app_mon. eauto.
      - eapply IH.(WPROP4).
      - i. exploit IH.(RPROP1); eauto.
        apply nth_error_app_inv in GET. des; eauto.
        apply nth_error_singleton_inv in GET0. des. congr.
      - i. exploit IH.(RPROP2); eauto. s. i. des. esplits; eauto.
        eapply nth_error_app_mon. eauto.
      - i. exploit IH.(WCV); eauto. s. i. des. esplits; eauto.
        eapply nth_error_app_mon. eauto.
      - i. exploit IH.(RCV); eauto. s. i. des. esplits; eauto.
        eapply nth_error_app_mon. eauto.
      - i. apply nth_error_app_inv in LABEL1. des; cycle 1.
        { apply nth_error_singleton_inv in LABEL0. des. subst. inv REL. inv X. }
        apply nth_error_app_inv in LABEL2. des; cycle 1.
        { apply nth_error_singleton_inv in LABEL3. des. subst. inv REL. inv Y. }
        eapply IH.(PO); eauto.
    }
 }
Qed.

(* Lemma sim_trace_cov_po_loc *)
(*       p mem tid tr atr wl rl cov vext r rl' w wl' eu tr' aeu atr' covf cov' *)
(*       (SIM: sim_trace p mem tid tr atr wl rl cov vext) *)
(*       (RL: rl = r :: rl') *)
(*       (WL: wl = w :: wl') *)
(*       (EU: tr = eu :: tr') *)
(*       (AEU: atr = aeu :: atr') *)
(*       (COV: cov = covf :: cov'): *)
(*   <<W: forall iid loc ts (W: w iid = Some (loc, ts)), le ts (eu.(ExecUnit.local).(Local.coh) loc)>> /\ *)
(*   (* TODO: enable it *) *)
(*   (* (forall iid loc ts (R: r iid = Some (loc, ts), le ts (eu.(ExecUnit.local).(Local.coh) loc)) /\ *) *)
(*   <<LABEL: forall iid1 iid2 label1 label2 *)
(*      (PO: iid1 < iid2) *)
(*      (LABEL1: List.nth_error aeu.(AExecUnit.local).(ALocal.labels) iid1 = Some label1) *)
(*      (LABEL2: List.nth_error aeu.(AExecUnit.local).(ALocal.labels) iid2 = Some label2) *)
(*      (REL: Execution.label_loc label1 label2), *)
(*       <<PO_LOC_WRITE: *)
(*         Label.is_write label2 -> *)
(*         Time.lt (covf iid1) (covf iid2)>> /\ *)
(*       <<PO_LOC_READ: *)
(*         Label.is_read label2 -> *)
(*         Time.le (covf iid1) (covf iid2)>>>>. *)
(* Proof. *)
(*   revert r rl' w wl' eu tr' aeu atr' covf cov' RL WL EU AEU COV. induction SIM. *)
(*   { i. simplify. ss. splits; ss. i. destruct iid1; ss. } *)
(*   i. simplify. *)
(*   destruct eu1 as [st1 lc1 mem1]. *)
(*   destruct eu as [st2 lc2 mem2]. *)
(*   destruct aeu1 as [ast1 alc1]. *)
(*   destruct aeu as [ast2 alc2]. *)
(*   ss. exploit IHSIM; eauto. i. des. *)
(*   inv STEP. inv ALOCAL_STEP; inv EVENT; ss; eauto. *)
(*   - (* internal *) *)
(*     admit. *)
(*   - (* read *) *)
(*     inv LOCAL; ss. inv ASTATE_STEP; ss. splits; eauto. *)
(*     { i. etrans; eauto. inv STEP. s. rewrite fun_add_spec. condtac; ss. inversion e. subst. ss. } *)
(*     i. unfold ALocal.next_eid in *. *)
(*     apply nth_error_app_inv in LABEL1. *)
(*     apply nth_error_app_inv in LABEL2. *)
(*     des. *)
(*     + repeat condtac; ss. *)
(*       all: try apply Nat.eqb_eq in X; ss; subst; try lia. *)
(*       all: try apply Nat.eqb_eq in X0; ss; subst; try lia. *)
(*       eapply LABEL; eauto. *)
(*     + lia. *)
(*     + apply nth_error_singleton_inv in LABEL0. des. subst. *)
(*       repeat condtac; ss. *)
(*       all: try apply Nat.eqb_eq in X; ss; subst; try lia. *)
(*       all: try apply Nat.eqb_neq in X0; ss; try lia. *)
(*       splits; ss. exploit sim_trace_vext_cov; eauto. i. des. simplify. ss. *)
      
      
(*       admit. *)
(*     + apply nth_error_singleton_inv in LABEL0. des. subst. *)
(*       repeat condtac; ss. *)
(*       all: try apply Nat.eqb_eq in X; ss; try lia. *)
(*   - (* write *) *)
(*     inv ASTATE_STEP; ss; eauto. *)
(*     destruct res1; ss. destruct val; ss. unfold ALocal.next_eid in *. *)
(*     apply nth_error_app_inv in LABEL1. *)
(*     apply nth_error_app_inv in LABEL2. *)
(*     des. *)
(*     + repeat condtac; ss. *)
(*       all: try apply Nat.eqb_eq in X; ss; subst; try lia. *)
(*       all: try apply Nat.eqb_eq in X0; ss; subst; try lia. *)
(*       eauto. *)
(*     + apply nth_error_singleton_inv in LABEL3. des. subst. *)
(*       repeat condtac; ss. *)
(*       all: try apply Nat.eqb_eq in X; ss; subst; try lia. *)
(*       all: try apply Nat.eqb_neq in X0; ss; try lia. *)
(*       admit. *)
(*     + lia. *)
(*     + apply nth_error_singleton_inv in LABEL3. des. subst. *)
(*       repeat condtac; ss. *)
(*       all: try apply Nat.eqb_eq in X; ss; try lia. *)
(*   - (* isb *) *)
(*     destruct res1; ss. destruct val; ss. eauto. *)
(*   - (* write *) *)
(*     apply nth_error_app_inv in LABEL1. des; cycle 1. *)
(*     { apply nth_error_singleton_inv in LABEL0. des. subst. *)
(*       inv REL. inv X. *)
(*     } *)
(*     apply nth_error_app_inv in LABEL2. des; cycle 1. *)
(*     { apply nth_error_singleton_inv in LtABEL3. des. subst. *)
(*       inv REL. inv Y. *)
(*     } *)
(*     eauto. *)
(* Admitted. *)

Lemma sim_traces_co1
      p mem trs atrs rs ws covs vexts ex
      (PRE: Valid.pre_ex p ex)
      (SIM: sim_traces p mem trs atrs ws rs covs vexts)
      (ATR: IdMap.Forall2
              (fun tid atr aeu => exists l, atr = aeu :: l)
              atrs PRE.(Valid.aeus)):
  forall eid1 eid2,
    (exists loc
        ex1 ord1 val1
        ex2 ord2 val2,
        <<LABEL: Execution.label eid1 ex = Some (Label.write ex1 ord1 loc val1)>> /\
        <<LABEL: Execution.label eid2 ex = Some (Label.write ex2 ord2 loc val2)>>) ->
    (eid1 = eid2 \/ (co_gen ws) eid1 eid2 \/ (co_gen ws) eid2 eid1).
Proof.
  i. des. destruct PRE, ex. unfold Execution.label in *. ss.
  destruct eid1 as [tid1 eid1], eid2 as [tid2 eid2]. ss.
  destruct (IdMap.find tid1 labels) eqn:FIND1, (IdMap.find tid2 labels) eqn:FIND2; ss.
  subst. rewrite IdMap.map_spec in *.
  generalize (ATR tid1). intro ATR1.
  generalize (ATR tid2). intro ATR2.
  generalize (SIM tid1). intro SIM1. inv SIM1.
  { inv ATR1; try congr. rewrite <- H7 in FIND1. ss. }
  generalize (SIM tid2). intro SIM2. inv SIM2.
  { inv ATR2; try congr. rewrite <- H13 in FIND2. ss. }
  inv ATR1; inv ATR2; try congr. des.
  rewrite <- H13 in *. rewrite <- H15 in *. ss.
  inv FIND1. inv FIND2.
  exploit sim_trace_last; try exact REL6; eauto. i. des. simplify.
  exploit sim_trace_last; try exact REL0; eauto. i. des. simplify.
  exploit sim_trace_sim_th; try exact REL6; eauto. intro TH1.
  exploit sim_trace_sim_th; try exact REL0; eauto. intro TH2.
  exploit TH1.(WPROP2); try exact LABEL; eauto. intro W1. des.
  exploit TH2.(WPROP2); try exact LABEL0; eauto. intro W2. des.
  destruct (Id.eq_dec tid1 tid2); subst; simplify.
  - specialize (Nat.lt_trichotomy ts ts0). i. des; subst.
    + right. left. econs; eauto.
    + exploit TH1.(WPROP4); [exact W1|exact W2|..]. auto.
    + right. right. econs; eauto.
  - specialize (Nat.lt_trichotomy ts ts0). i. des; subst.
    + right. left. econs; eauto.
    + congr.
    + right. right. econs; eauto.
Qed.

Lemma sim_traces_co2
      p mem trs atrs rs ws covs vexts ex
      (PRE: Valid.pre_ex p ex)
      (SIM: sim_traces p mem trs atrs ws rs covs vexts)
      (ATR: IdMap.Forall2
              (fun tid atr aeu => exists l, atr = aeu :: l)
              atrs PRE.(Valid.aeus)):
  forall eid1 eid2,
    (co_gen ws) eid1 eid2 ->
    exists loc
       ex1 ord1 val1
       ex2 ord2 val2,
      <<LABEL: Execution.label eid1 ex = Some (Label.write ex1 ord1 loc val1)>> /\
      <<LABEL: Execution.label eid2 ex = Some (Label.write ex2 ord2 loc val2)>>.
Proof.
  i. destruct PRE, ex. unfold Execution.label in *. ss.
  destruct eid1 as [tid1 eid1], eid2 as [tid2 eid2]. inv H. ss.
  generalize (SIM tid1). intro SIM1. inv SIM1; try congr.
  generalize (SIM tid2). intro SIM2. inv SIM2; try congr.
  generalize (ATR tid1). intro ATR1. inv ATR1; try congr.
  generalize (ATR tid2). intro ATR2. inv ATR2; try congr.
  des. simplify.
  repeat rewrite IdMap.map_spec.
  rewrite <- H13. rewrite <- H15. ss.
  exploit sim_trace_last; try exact REL6; eauto. i. des. simplify.
  exploit sim_trace_last; try exact REL0; eauto. i. des. simplify.
  exploit sim_trace_sim_th; try exact REL6; eauto. intro TH1.
  exploit sim_trace_sim_th; try exact REL0; eauto. intro TH2.
  exploit TH1.(WPROP3); eauto. i. des.
  exploit TH2.(WPROP3); eauto. i. des.
  esplits; eauto.
Qed.

Lemma sim_traces_rf1_aux
      p trs atrs rs ws covs vexts ex m
      (STEP: Machine.pf_exec p m)
      (PRE: Valid.pre_ex p ex)
      (NOPROMISE: Machine.no_promise m)
      (SIM: sim_traces p m.(Machine.mem) trs atrs ws rs covs vexts)
      (TR: IdMap.Forall2
             (fun tid tr sl => exists l, tr = (ExecUnit.mk sl.(fst) sl.(snd) m.(Machine.mem)) :: l)
             trs m.(Machine.tpool))
      (ATR: IdMap.Forall2
              (fun tid atr aeu => exists l, atr = aeu :: l)
              atrs PRE.(Valid.aeus)):
  forall eid1 ex1 ord1 loc val
     (LABEL: Execution.label eid1 ex = Some (Label.read ex1 ord1 loc val)),
    (<<NORF: ~ codom_rel (rf_gen ws rs) eid1>> /\ <<VAL: val = Val.default >> /\
     <<R: exists r rl loc, IdMap.find eid1.(fst) rs = Some (r::rl) /\ r eid1.(snd) = Some (loc, Time.bot)>>) \/
    (exists eid2 ex2 ord2,
        <<LABEL: Execution.label eid2 ex = Some (Label.write ex2 ord2 loc val)>> /\
        <<RF: (rf_gen ws rs) eid2 eid1>>).
Proof.
  i. destruct eid1 as [tid1 eid1].
  destruct PRE, ex. unfold Execution.label in *. ss.
  rewrite LABELS in *. rewrite IdMap.map_spec in *.
  destruct (IdMap.find tid1 aeus) eqn:FIND1; ss.
  generalize (ATR tid1). intro ATR1. inv ATR1; try congr.
  generalize (SIM tid1). intro SIM1. inv SIM1; try congr.
  des. simplify.
  exploit sim_trace_last; eauto. i. des. simplify.
  exploit sim_trace_sim_th; eauto. intro TH.
  (* exploit r_property; eauto. i. des. simplify. *)
  exploit TH.(RPROP1); eauto. i. des. unguardH x1. des.
  - left. esplits; subst; eauto.
    ii. inv H. inv H1.
    destruct x as [tid2 eid2]. ss. simplify.
    rewrite R in x0. inv x0.
    generalize (SIM tid2). intro SIM1. inv SIM1; try congr.
    simplify.
    exploit sim_trace_last; try exact REL0; eauto. i. des. simplify.
    exploit sim_trace_sim_th; try exact REL0; eauto. intro TH'.
    exploit TH'.(WPROP3); eauto. i. des.
    unfold Memory.get_msg in x0. ss.
  - right. exploit sim_traces_memory; eauto. i. des.
    generalize (TR tid'). intro TR2. inv TR2; try congr.
    generalize (SIM tid'). intro SIM2. inv SIM2; try congr.
    des. simplify.
    exploit sim_trace_last; try exact REL0; eauto. i. des. simplify.
    exploit sim_trace_sim_th; try exact REL0; eauto. intro TH'.
    exploit TH'.(WPROP1); eauto. i. des; ss.
    + destruct b. ss. inv NOPROMISE.
      exploit PROMISES0; eauto. i. rewrite x in x3.
      rewrite Promises.lookup_bot in x3. ss.
    + generalize (ATR tid'). intro ATR2. inv ATR2; try congr.
      des. simplify. eexists (tid', eid). esplits; ss.
      * rewrite IdMap.map_spec. rewrite <- H8. ss. eauto.
      * econs; eauto.
Qed.

Lemma sim_traces_rf1
      p trs atrs rs ws covs vexts ex m
      (ETEP: Machine.pf_exec p m)
      (PRE: Valid.pre_ex p ex)
      (NOPROMISE: Machine.no_promise m)
      (SIM: sim_traces p m.(Machine.mem) trs atrs ws rs covs vexts)
      (TR: IdMap.Forall2
             (fun tid tr sl => exists l, tr = (ExecUnit.mk sl.(fst) sl.(snd) m.(Machine.mem)) :: l)
             trs m.(Machine.tpool))
      (ATR: IdMap.Forall2
              (fun tid atr aeu => exists l, atr = aeu :: l)
              atrs PRE.(Valid.aeus)):
  forall eid1 ex1 ord1 loc val
     (LABEL: Execution.label eid1 ex = Some (Label.read ex1 ord1 loc val)),
    (<<NORF: ~ codom_rel (rf_gen ws rs) eid1>> /\ <<VAL: val = Val.default >>) \/
    (exists eid2 ex2 ord2,
        <<LABEL: Execution.label eid2 ex = Some (Label.write ex2 ord2 loc val)>> /\
        <<RF: (rf_gen ws rs) eid2 eid1>>).
Proof.
  ii. exploit sim_traces_rf1_aux; eauto. i. des.
  - left. esplits; eauto.
  - right. esplits; eauto.
Qed.

Lemma sim_traces_rf2
      p mem trs atrs rs ws covs vexts ex
      (PRE: Valid.pre_ex p ex)
      (SIM: sim_traces p mem trs atrs ws rs covs vexts)
      (ATR: IdMap.Forall2
              (fun tid atr aeu => exists l, atr = aeu :: l)
              atrs PRE.(Valid.aeus)):
  forall eid1 eid2 (RF: (rf_gen ws rs) eid2 eid1),
  exists ex1 ex2 ord1 ord2 loc val,
    <<READ: Execution.label eid1 ex = Some (Label.read ex1 ord1 loc val)>> /\
    <<WRITE: Execution.label eid2 ex = Some (Label.write ex2 ord2 loc val)>>.
Proof.
  i. inv RF. destruct eid1 as [tid1 eid1], eid2 as [tid2 eid2]. ss.
  generalize (SIM tid1). intro SIM1. inv SIM1; try congr.
  generalize (SIM tid2). intro SIM2. inv SIM2; try congr.
  simplify.
  exploit sim_trace_last; try exact REL0; eauto. i. des. simplify.
  exploit sim_trace_sim_th; try exact REL0; eauto. intro TH1.
  exploit sim_trace_last; try exact REL6; eauto. i. des. simplify.
  exploit sim_trace_sim_th; try exact REL6; eauto. intro TH2.
  exploit TH1.(WPROP3); eauto. i. des.
  exploit TH2.(RPROP2); eauto. i. des. unguardH x4. des; subst; ss.
  rewrite x4 in x2. inv x2.
  generalize (ATR tid1). intro ATR1. inv ATR1; try congr.
  generalize (ATR tid2). intro ATR2. inv ATR2; try congr.
  des. simplify. destruct PRE, ex. unfold Execution.label. ss.
  rewrite LABELS. repeat rewrite IdMap.map_spec.
  rewrite <- H8. rewrite <- H13. ss. esplits; eauto.
Qed.

Lemma sim_traces_rf_wf
      p mem trs atrs rs ws covs vexts
      (SIM: sim_traces p mem trs atrs ws rs covs vexts):
  functional (rf_gen ws rs)⁻¹.
Proof.
  ii. inv H. inv H0.
  destruct y as [tid1 eid1], z as [tid2 eid2]. ss.
  simplify. rewrite R in R0. inv R0.
  destruct (Id.eq_dec tid1 tid2); subst; simplify.
  - specialize (SIM tid2). inv SIM; try congr.
    exploit sim_trace_last; eauto. i. des. simplify.
    exploit sim_trace_sim_th; eauto. intro TH.
    exploit TH.(WPROP4); [exact W|exact W0|..]. i. subst. refl.
  - generalize (SIM tid1). intro SIM1. inv SIM1; try congr.
    generalize (SIM tid2). intro SIM2. inv SIM2; try congr.
    exploit sim_trace_last; try exact REL6; eauto. i. des. simplify.
    exploit sim_trace_sim_th; try exact REL6; eauto. intro TH1.
    exploit sim_trace_last; try exact REL0; eauto. i. des. simplify.
    exploit sim_trace_sim_th; try exact REL0; eauto. intro TH2.
    simplify.
    exploit TH1.(WPROP3); eauto. i. des.
    exploit TH2.(WPROP3); eauto. i. des.
    congr.
Qed.

Lemma sim_traces_cov_co
      p mem trs atrs ws rs covs vexts
      ex
      (SIM: sim_traces p mem trs atrs ws rs covs vexts)
      (CO: ex.(Execution.co) = co_gen ws):
  <<CO:
    forall eid1 eid2
      (CO: ex.(Execution.co) eid1 eid2),
      Time.lt ((v_gen covs) eid1) ((v_gen covs) eid2)>>.
Proof.
  ii. rewrite CO in *. inv CO0.
  destruct eid1 as [tid1 eid1], eid2 as [tid2 eid2]. ss.
  generalize (SIM tid1). intro SIM1. inv SIM1; try congr.
  generalize (SIM tid2). intro SIM2. inv SIM2; try congr. simplify.
  exploit sim_trace_last; try exact REL6; eauto. i. des. simplify.
  exploit sim_trace_sim_th; try exact REL6; eauto. intro TH1.
  exploit sim_trace_last; try exact REL0; eauto. i. des. simplify.
  exploit sim_trace_sim_th; try exact REL0; eauto. intro TH2.
  exploit TH1.(WCV); eauto. i. des.
  exploit TH2.(WCV); eauto. i. des.
  unfold v_gen. ss. rewrite <- H4. rewrite <- H10.
  rewrite x1, x4. auto.
Qed.

Lemma sim_traces_cov_rf
      p mem trs atrs ws rs covs vexts
      ex
      (SIM: sim_traces p mem trs atrs ws rs covs vexts)
      (RF: ex.(Execution.rf) = rf_gen ws rs):
  <<RF:
    forall eid1 eid2
      (RF: ex.(Execution.rf) eid1 eid2),
      Time.eq ((v_gen covs) eid1) ((v_gen covs) eid2)>>.
Proof.
  ii. rewrite RF in *. inv RF0.
  destruct eid1 as [tid1 eid1], eid2 as [tid2 eid2]. ss.
  generalize (SIM tid1). intro SIM1. inv SIM1; try congr.
  generalize (SIM tid2). intro SIM2. inv SIM2; try congr. simplify.
  exploit sim_trace_last; try exact REL6; eauto. i. des. simplify.
  exploit sim_trace_sim_th; try exact REL6; eauto. intro TH1.
  exploit sim_trace_last; try exact REL0; eauto. i. des. simplify.
  exploit sim_trace_sim_th; try exact REL0; eauto. intro TH2.
  exploit TH1.(WCV); eauto. i. des.
  exploit TH2.(RCV); eauto. i. des.
  unfold v_gen. ss. rewrite <- H4. rewrite <- H10.
  rewrite x1, x4. refl.
Qed.

Lemma sim_traces_cov_fr
      p trs atrs ws rs covs vexts
      ex m
      (STEP: Machine.pf_exec p m)
      (SIM: sim_traces p m.(Machine.mem) trs atrs ws rs covs vexts)
      (CO: ex.(Execution.co) = co_gen ws)
      (RF: ex.(Execution.rf) = rf_gen ws rs)
      (PRE: Valid.pre_ex p ex)
      (NOPROMISE: Machine.no_promise m)
      (TR: IdMap.Forall2
             (fun tid tr sl => exists l, tr = (ExecUnit.mk sl.(fst) sl.(snd) m.(Machine.mem)) :: l)
             trs m.(Machine.tpool))
      (ATR: IdMap.Forall2
              (fun tid atr aeu => exists l, atr = aeu :: l)
              atrs PRE.(Valid.aeus)):
  <<FR:
    forall eid1 eid2
      (FR: ex.(Execution.fr) eid1 eid2),
      Time.lt ((v_gen covs) eid1) ((v_gen covs) eid2)>>.
Proof.
  ii. inv FR.
  - inv H. des.
    exploit sim_traces_cov_co; eauto. i.
    exploit sim_traces_cov_rf; eauto. i.
    rewrite <- x2. auto.
  - inv H. inv H1. inv H. inv H1. destruct l; ss.
    exploit sim_traces_rf1_aux; eauto. i. des.
    + inv H2. destruct l; ss. destruct PRE.
      unfold Execution.label in EID0.
      rewrite LABELS in EID0. rewrite IdMap.map_spec in EID0.
      destruct eid1 as [tid1 eid1], eid2 as [tid2 eid2]. ss.
      destruct (IdMap.find tid2 aeus) eqn:FIND2; ss.
      generalize (ATR tid2). intro ATR2. inv ATR2; try congr. des. simplify.
      generalize (SIM tid2). intro SIM2. inv SIM2; try congr. simplify.
      exploit sim_trace_last; try exact REL6; eauto. i. des. simplify.
      exploit sim_trace_sim_th; try exact REL6; eauto. intro TH1.
      exploit TH1.(WPROP2); eauto. i. des.
      exploit TH1.(WPROP3); eauto. i. des.
      clear ex2 ord1 val0 x3 x4.
      generalize (SIM tid1). intro SIM1. inv SIM1; try congr. simplify.
      exploit sim_trace_last; try exact REL0; eauto. i. des. simplify.
      exploit sim_trace_sim_th; try exact REL0; eauto. intro TH2.
      exploit TH1.(WCV); eauto. i. des.
      exploit TH2.(RCV); eauto. i. des.
      unfold v_gen. ss. rewrite <- H12. rewrite <- H7.
      rewrite x7, x4. auto.
    + exfalso.
      rewrite RF in *. eapply H3. unfold codom_rel.
      eexists. eauto.
Qed.

Lemma sim_traces_cov_po_loc
      p mem trs atrs ws rs covs vexts
      ex
      (SIM: sim_traces p mem trs atrs ws rs covs vexts)
      (PRE: Valid.pre_ex p ex)
      (ATR: IdMap.Forall2
              (fun tid atr aeu => exists l, atr = aeu :: l)
              atrs PRE.(Valid.aeus)):
  forall eid1 eid2 (PO_LOC: ex.(Execution.po_loc) eid1 eid2),
     <<PO_LOC_WRITE:
       ex.(Execution.label_is) Label.is_write eid2 ->
       Time.lt ((v_gen covs) eid1) ((v_gen covs) eid2)>> /\
     <<PO_LOC_READ:
       ex.(Execution.label_is) Label.is_read eid2 ->
       Time.le ((v_gen covs) eid1) ((v_gen covs) eid2)>>.
Proof.
  i. destruct eid1 as [tid1 iid1], eid2 as [tid2 iid2]. inv PO_LOC. inv H. ss. subst.
  inv H0. unfold Execution.label in *. ss. rewrite PRE.(Valid.LABELS), IdMap.map_spec in *.
  generalize (ATR tid2). intro X. inv X; ss; rewrite <- H in *; ss.
  des. subst. generalize (SIM tid2). i. inv H1; simplify.
  exploit sim_trace_last; eauto. i. des. subst. simplify.
  exploit sim_trace_sim_th; eauto. intro TH.
  exploit TH.(PO); eauto. i. des.
  unfold v_gen. s. rewrite <- H7. splits; i.
  - inv H1. unfold Execution.label in *. ss.
    rewrite PRE.(Valid.LABELS), IdMap.map_spec, <- H in *. inv EID.
    rewrite EID2 in H2. inv H2. eauto.
  - inv H1. unfold Execution.label in *. ss.
    rewrite PRE.(Valid.LABELS), IdMap.map_spec, <- H in *. inv EID.
    rewrite EID2 in H2. inv H2. eauto.
Qed.

Lemma sim_traces_vext_co
      p mem trs atrs ws rs covs vexts
      ex
      (SIM: sim_traces p mem trs atrs ws rs covs vexts)
      (CO: ex.(Execution.co) = co_gen ws):
  <<CO:
    forall eid1 eid2
      (CO: ex.(Execution.co) eid1 eid2),
      Time.lt ((v_gen vexts) eid1) ((v_gen vexts) eid2)>>.
Proof.
  ii. rewrite CO in *. inv CO0.
  destruct eid1 as [tid1 eid1], eid2 as [tid2 eid2]. ss.
  generalize (SIM tid1). intro SIM1. inv SIM1; try congr.
  generalize (SIM tid2). intro SIM2. inv SIM2; try congr. simplify.
  exploit sim_trace_last; try exact REL6; eauto. i. des. simplify.
  exploit sim_trace_sim_th; try exact REL6; eauto. intro TH1.
  exploit sim_trace_last; try exact REL0; eauto. i. des. simplify.
  exploit sim_trace_sim_th; try exact REL0; eauto. intro TH2.
  exploit TH1.(WCV); eauto. i. des.
  exploit TH2.(WCV); eauto. i. des.
  unfold v_gen. ss. rewrite <- H5. rewrite <- H11.
  rewrite x5, x2. auto.
Qed.

Lemma sim_trace_lastn
      p mem tid tr atr wl rl covl vextl
      n
      (SIM: sim_trace p mem tid tr atr wl rl covl vextl):
  sim_trace p mem tid
            (lastn (S n) tr) (lastn (S n) atr) (lastn (S n) wl)
            (lastn (S n) rl) (lastn (S n) covl) (lastn (S n) vextl).
Proof.
  revert n atr wl rl covl vextl SIM. induction tr; i; [by inv SIM|].
  exploit sim_trace_length; eauto. s. i. des.
  destruct (le_lt_dec (length tr) n).
  { rewrite ? lastn_all in *; ss; try lia. }
  exploit sim_trace_last; eauto. i. des. simplify. ss.
  rewrite ? lastn_cons; try lia. eapply IHtr.
  inv SIM; ss. lia.
Qed.

Lemma sim_traces_ex
      p mem trs atrs ws rs covs vexts
      ex
      tid n atr aeu atr' covl cov covl' vextl vext vextl'
      (SIM: sim_traces p mem trs atrs ws rs covs vexts)
      (PRE: Valid.pre_ex p ex)
      (ATR: IdMap.Forall2
              (fun _ atr aeu => exists l, atr = aeu :: l)
              atrs (Valid.aeus PRE))
      (FIND_ATR: IdMap.find tid atrs = Some atr)
      (FIND_COVL: IdMap.find tid covs = Some covl)
      (FIND_VEXTL: IdMap.find tid vexts = Some vextl)
      (AEU: lastn (S n) atr = aeu :: atr')
      (COV: lastn (S n) covl = cov :: covl')
      (VEXT: lastn (S n) vextl = vext :: vextl'):
  <<LABELS:
    forall eid label
      (EID: eid < List.length aeu.(AExecUnit.local).(ALocal.labels))
      (LABEL: Execution.label (tid, eid) ex = Some label),
      List.nth_error aeu.(AExecUnit.local).(ALocal.labels) eid = Some label>> /\
  <<ADDR:
    forall eid1 eid2
      (EID2: eid2 < List.length aeu.(AExecUnit.local).(ALocal.labels))
      (ADDR: ex.(Execution.addr) (tid, eid1) (tid, eid2)),
      aeu.(AExecUnit.local).(ALocal.addr) eid1 eid2>> /\
  <<DATA:
    forall eid1 eid2
      (EID2: eid2 < List.length aeu.(AExecUnit.local).(ALocal.labels))
      (DATA: ex.(Execution.data) (tid, eid1) (tid, eid2)),
      aeu.(AExecUnit.local).(ALocal.data) eid1 eid2>> /\
  <<CTRL:
    forall eid1 eid2
      (EID2: eid2 < List.length aeu.(AExecUnit.local).(ALocal.labels))
      (CTRL: ex.(Execution.ctrl) (tid, eid1) (tid, eid2)),
      aeu.(AExecUnit.local).(ALocal.ctrl) eid1 eid2>> /\
  <<RMW:
    forall eid1 eid2
      (EID2: eid2 < List.length aeu.(AExecUnit.local).(ALocal.labels))
      (ADDR: ex.(Execution.rmw) (tid, eid1) (tid, eid2)),
      aeu.(AExecUnit.local).(ALocal.rmw) eid1 eid2>> /\
  <<COV:
    forall eid
      (EID: eid < List.length aeu.(AExecUnit.local).(ALocal.labels)),
      (v_gen covs) (tid, eid) = cov eid>> /\
  <<VEXT:
    forall eid
      (EID: eid < List.length aeu.(AExecUnit.local).(ALocal.labels)),
      (v_gen vexts) (tid, eid) = vext eid>>.
Proof.
Admitted.

Definition ob' (ex: Execution.t): relation eidT :=
  ex.(Execution.rfe) ∪ ex.(Execution.dob) ∪ ex.(Execution.aob) ∪ ex.(Execution.bob).

Ltac des_union :=
  repeat
    (try match goal with
         | [H: Execution.internal _ _ _ |- _] => inv H
         | [H: Execution.ob _ _ _ |- _] => inv H
         | [H: Execution.obs _ _ _ |- _] => inv H
         | [H: (_ ∪ _) _ _ |- _] => inv H
         end).

Lemma ob_ob'
      ex eid1 eid2:
  ex.(Execution.ob) eid1 eid2 <->
  (ex.(Execution.fr) ∪ ex.(Execution.co) ∪ ex.(ob')) eid1 eid2.
Proof.
  split; i.
  - des_union.
    + right. left. left. left. auto.
    + left. left. auto.
    + left. right. auto.
    + right. left. left. right. auto.
    + right. left. right. auto.
    + right. right. auto.
  - unfold ob' in *. des_union.
    + left. left. left. left. right. auto.
    + left. left. left. right. auto.
    + left. left. left. left. left. auto.
    + left. left. right. auto.
    + left. right. auto.
    + right. auto.
Qed.

Lemma sim_traces_sim_eu
      p mem trs atrs ws rs covs vexts
      m ex
      (SIM: sim_traces p mem trs atrs ws rs covs vexts)
      (NOPROMISE: Machine.no_promise m)
      (PRE: Valid.pre_ex p ex)
      (CO: ex.(Execution.co) = co_gen ws)
      (RF: ex.(Execution.rf) = rf_gen ws rs)
      (CO1: Valid.co1 ex)
      (CO2: Valid.co2 ex)
      (RF1: Valid.rf1 ex)
      (RF2: Valid.rf2 ex)
      (RF_WF: Valid.rf_wf ex)
      (TR: IdMap.Forall2
             (fun _ tr sl => exists l, tr = (ExecUnit.mk sl.(fst) sl.(snd) mem) :: l)
             trs m.(Machine.tpool))
      (ATR: IdMap.Forall2
              (fun _ atr aeu => exists l, atr = aeu :: l)
              atrs (Valid.aeus PRE)):
  forall tid tr atr covl vextl
    n eu tr' aeu atr' cov covl' vext vextl'
    (FIND_TR: IdMap.find tid trs = Some tr)
    (FIND_ATR: IdMap.find tid atrs = Some atr)
    (FIND_COVL: IdMap.find tid covs = Some covl)
    (FIND_VEXTL: IdMap.find tid vexts = Some vextl)
    (EU: lastn (S n) tr = eu :: tr')
    (AEU: lastn (S n) atr = aeu :: atr')
    (COV: lastn (S n) covl = cov :: covl')
    (VEXT: lastn (S n) vextl = vext :: vextl'),
    <<SIM_EU: sim_eu tid ex (v_gen vexts) eu aeu>> /\
    <<OB_WRITE:
      forall eid1 eid2
        (LABEL: eid2 < List.length aeu.(AExecUnit.local).(ALocal.labels))
        (OB: ex.(ob') eid1 (tid, eid2))
        (EID2: ex.(Execution.label_is) Label.is_write (tid, eid2)),
        Time.lt ((v_gen vexts) eid1) (vext eid2)>> /\
    <<OB_READ:
      forall eid1 eid2
        (LABEL: eid2 < List.length aeu.(AExecUnit.local).(ALocal.labels))
        (AOB: ex.(ob') eid1 (tid, eid2))
        (EID2: ex.(Execution.label_is) Label.is_read (tid, eid2)),
        Time.le ((v_gen vexts) eid1) (vext eid2)>> /\
    <<FR:
      forall eid1 eid2
        (LABEL: eid1 < List.length aeu.(AExecUnit.local).(ALocal.labels))
        (FR: ex.(Execution.fr) (tid, eid1) eid2),
        Time.lt (vext eid1) ((v_gen vexts) eid2)>>.
Proof.
  i. generalize (SIM tid). intro X. inv X; simplify.
  revert eu aeu tr' atr' cov covl' vext vextl' EU AEU COV VEXT. induction n.
  { i.
    exploit (lastn_one tr).
    { exploit sim_trace_last; eauto. i. des. subst. ss. lia. }
    i. des.
    exploit (lastn_one atr).
    { exploit sim_trace_last; eauto. i. des. subst. ss. lia. }
    i. des.
    (* exploit (lastn_one covl). *)
    (* { exploit sim_trace_last; eauto. i. des. subst. ss. lia. } *)
    (* i. des. *)
    (* exploit (lastn_one vextl). *)
    (* { exploit sim_trace_last; eauto. i. des. subst. ss. lia. } *)
    (* i. des. *)
    rewrite EU in x0. symmetry in x0. inv x0.
    rewrite AEU in x1. symmetry in x1. inv x1.
    (* rewrite COV in x2. symmetry in x2. inv x2. *)
    (* rewrite VEXT in x3. symmetry in x3. inv x3. *)
    exploit sim_trace_lastn; eauto. rewrite AEU. i.
    inv x0. ss. splits; i; try lia.
    admit.
  }
  i. rename c into wl, d into rl.
  destruct (Nat.le_gt_cases (List.length tr) (S n)).
  { exploit sim_trace_length; eauto. i. des.
    rewrite lastn_all in EU; [|lia]. subst.
    rewrite lastn_all in AEU; [|lia]. subst.
    rewrite lastn_all in COV; [|lia]. subst.
    rewrite lastn_all in VEXT; [|lia]. subst.
    eapply IHn; apply lastn_all; lia. }
  exploit sim_trace_length; eauto. i. des.
  exploit (lastn_S (S n) wl); try rewrite LENGTH_WL; try lia. intro W. des.
  exploit (lastn_S (S n) rl); try rewrite LENGTH_RL; try lia. intro R. des.
  exploit lastn_S1; try exact EU; eauto. intro EU'.
  exploit lastn_S1; try exact AEU; try rewrite LENGTH_ATR; eauto. intro AEU'.
  exploit lastn_S1; try exact WL; try rewrite LENGTH_WL; eauto. intro W'.
  exploit lastn_S1; try exact RL; try rewrite LENGTH_RL; eauto. intro R'.
  exploit lastn_S1; try exact COV; try rewrite LENGTH_COVL; eauto. intro COV'.
  exploit lastn_S1; try exact VEXT; try rewrite LENGTH_VEXTL; eauto. intro VEXT'.
  exploit (lastn_S n tr); try lia. i. des.
  exploit (lastn_S n atr); try lia. i. des.
  exploit (lastn_S n wl); try lia. i. des.
  exploit (lastn_S n rl); try lia. i. des.
  exploit (lastn_S n covl); try lia. i. des.
  exploit (lastn_S n vextl); try lia. i. des.
  rewrite EU' in x0. rewrite x0 in *. clear x0 tr'.
  rewrite AEU' in x1. rewrite x1 in *. clear x1 atr'.
  rewrite W' in x2. rewrite x2 in *. clear x2 l'.
  rewrite R' in x3. rewrite x3 in *. clear x3 l'0.
  rewrite COV' in x4. rewrite x4 in *. clear x4 covl'.
  rewrite VEXT' in x5. rewrite x5 in *. clear x5 vextl'.
  rename a1 into eu1, l'1 into tr'.
  rename a2 into aeu1, l'2 into atr'.
  rename a into w, a3 into w1, l'3 into wl'.
  rename a0 into r, a4 into r1, l'4 into rl'.
  rename a5 into cov1, l'5 into covl'.
  rename a6 into vext1, l'6 into vextl'.
  exploit IHn; eauto. i. des.
  exploit sim_trace_lastn; try exact REL6; eauto.
  rewrite EU', AEU', W', R', COV', VEXT'. intro SIM1.
  exploit sim_trace_lastn; try exact REL6; eauto.
  rewrite EU, AEU, W, R, COV, VEXT. intro SIM2.
  exploit sim_traces_ex; try exact AEU'; eauto. i. des.
  exploit sim_traces_ex; try exact AEU; eauto. i. des.
  clear IHn. (* clear as much as possible *)
  splits; cycle 1.
  { admit. }
  { admit. }
  { i. inv FR0.
    - admit.
    - (* inv H0. inv H6. inv H0. inv H6. *)
      (* exploit LABELS0; eauto. intro LABEL1. destruct l; ss. *)
      (* rewrite VEXT0; eauto. *)
      (* exploit r_property; try exact SIM2. i. des. simplify. *)
      (* exploit RPROP1; eauto. i. des. *)
      (* + inv SIM2. inv EVENT; ss. *)
      (* generalize (ATR tid). intro ATR1. inv ATR1; try congr. des. simplify. *)
      (* destruct PRE. unfold Execution.label in EID. ss. *)
      (* rewrite LABELS1 in EID. rewrite IdMap.map_spec in EID. *)
      (* rewrite <- H9 in EID. ss. simplify. *)
      (* exploit w_property; try exact REL6. i. des. *)
      admit.
  }
  admit.
Admitted.

Lemma sim_traces_vext_valid
      p mem trs atrs ws rs covs vexts
      m ex
      (SIM: sim_traces p mem trs atrs ws rs covs vexts)
      (NOPROMISE: Machine.no_promise m)
      (PRE: Valid.pre_ex p ex)
      (CO: ex.(Execution.co) = co_gen ws)
      (RF: ex.(Execution.rf) = rf_gen ws rs)
      (CO1: Valid.co1 ex)
      (CO2: Valid.co2 ex)
      (RF1: Valid.rf1 ex)
      (RF2: Valid.rf2 ex)
      (RF_WF: Valid.rf_wf ex)
      (TR: IdMap.Forall2
             (fun _ tr sl => exists l, tr = (ExecUnit.mk sl.(fst) sl.(snd) mem) :: l)
             trs m.(Machine.tpool))
      (ATR: IdMap.Forall2
              (fun _ atr aeu => exists l, atr = aeu :: l)
              atrs (Valid.aeus PRE)):
  <<FR:
    forall eid1 eid2
      (FR: ex.(Execution.fr) eid1 eid2),
      Time.lt ((v_gen vexts) eid1) ((v_gen vexts) eid2)>> /\
  <<OB_WRITE:
    forall eid1 eid2
      (OB: ex.(ob') eid1 eid2)
      (EID2: ex.(Execution.label_is) Label.is_write eid2),
      Time.lt ((v_gen vexts) eid1) ((v_gen vexts) eid2)>> /\
  <<OB_READ:
    forall eid1 eid2
      (OB: ex.(ob') eid1 eid2)
      (EID2: ex.(Execution.label_is) Label.is_read eid2),
      Time.le ((v_gen vexts) eid1) ((v_gen vexts) eid2)>>.
Proof.
Admitted.

Lemma sim_traces_valid
      p trs atrs ws rs covs vexts
      m ex
      (STEP: Machine.pf_exec p m)
      (SIM: sim_traces p m.(Machine.mem) trs atrs ws rs covs vexts)
      (PRE: Valid.pre_ex p ex)
      (CO: ex.(Execution.co) = co_gen ws)
      (RF: ex.(Execution.rf) = rf_gen ws rs)
      (CO1: Valid.co1 ex)
      (CO2: Valid.co2 ex)
      (RF1: Valid.rf1 ex)
      (RF2: Valid.rf2 ex)
      (RF_WF: Valid.rf_wf ex)
      (TR: IdMap.Forall2
             (fun _ tr sl => exists l, tr = (ExecUnit.mk sl.(fst) sl.(snd) m.(Machine.mem)) :: l)
             trs m.(Machine.tpool))
      (ATR: IdMap.Forall2
              (fun _ atr aeu => exists l, atr = aeu :: l)
              atrs (Valid.aeus PRE)):
  <<INTERNAL:
    forall eid1 eid2
      (INTERNAL: ex.(Execution.internal) eid1 eid2),
      (Time.lt ((v_gen covs) eid1) ((v_gen covs) eid2) /\ ex.(Execution.label_is) Label.is_write eid2) \/
      (Time.le ((v_gen covs) eid1) ((v_gen covs) eid2) /\ ex.(Execution.label_is) Label.is_read eid2)>> /\
  <<EXTERNAL:
    forall eid1 eid2
      (OB: ex.(Execution.ob) eid1 eid2)
      (LABEL1: Execution.label_is ex Label.is_access eid1)
      (LABEL2: Execution.label_is ex Label.is_access eid2),
      (Time.lt ((v_gen vexts) eid1) ((v_gen vexts) eid2) /\ ex.(Execution.label_is) Label.is_write eid2) \/
      (Time.le ((v_gen vexts) eid1) ((v_gen vexts) eid2) /\ ex.(Execution.label_is) Label.is_read eid2)>> /\
  <<ATOMIC: le (ex.(Execution.rmw) ∩ (ex.(Execution.fre) ⨾ ex.(Execution.coe))) bot>>.
Proof.
  generalize STEP. intro X. inv X. splits.
  - ii. exploit Valid.internal_rw; eauto. i. des.
    inv EID2. destruct l; ss.
    + right. des_union.
      * exploit sim_traces_cov_po_loc; eauto. i. des.
        exploit PO_LOC_READ; eauto.
      * exploit sim_traces_cov_fr; eauto. i.
        split; eauto using Nat.lt_le_incl.
      * exploit sim_traces_cov_co; eauto. i.
        split; eauto using Nat.lt_le_incl.
      * exploit sim_traces_cov_rf; eauto. i.
        split; eauto. rewrite x0. auto.
    + left. des_union.
      * exploit sim_traces_cov_po_loc; eauto. i. des.
        exploit PO_LOC_WRITE; eauto.
      * exploit sim_traces_cov_fr; eauto.
      * exploit sim_traces_cov_co; eauto.
      * exploit RF2; eauto. i. des. congr.
  - exploit sim_traces_vext_valid; eauto. i. des.
    inv LABEL2. destruct l; ss.
    + right. rewrite ob_ob' in OB. des_union.
      * exploit FR; eauto. i.
        split; eauto using Nat.lt_le_incl.
      * exploit sim_traces_vext_co; eauto. i.
        split; eauto using Nat.lt_le_incl.
      * exploit OB_READ; eauto.
    + left. rewrite ob_ob' in OB. des_union.
      * exploit FR; eauto.
      * exploit sim_traces_vext_co; eauto.
      * exploit OB_WRITE; eauto.
  - admit.
Admitted.

Lemma internal_acyclic
      ex cov
      (INTERNAL: forall eid1 eid2 (INTERNAL: ex.(Execution.internal)⁺ eid1 eid2),
          Time.lt (cov eid1) (cov eid2) \/
          (Time.le (cov eid1) (cov eid2) /\
           Execution.po eid1 eid2 /\
           ex.(Execution.label_is) Label.is_read eid1 /\
           ex.(Execution.label_is) Label.is_read eid2) \/
          (Time.le (cov eid1) (cov eid2) /\
           ex.(Execution.label_is) Label.is_write eid1 /\
           ex.(Execution.label_is) Label.is_read eid2)):
  acyclic ex.(Execution.internal).
Proof.
  ii. exploit INTERNAL; eauto. i. des.
  - inv x0; lia.
  - inv x1. lia.
  - inv x1. inv x2. rewrite EID in EID0. inv EID0. destruct l0; ss; congr.
Qed.

Lemma promising_pf_valid
      p m
      (STEP: Machine.pf_exec p m):
  exists ex (PRE: Valid.pre_ex p ex) (cov: forall (eid: eidT), Time.t) (vext: forall (eid: eidT), Time.t),
    <<CO1: Valid.co1 ex>> /\
    <<CO2: Valid.co2 ex>> /\
    <<RF1: Valid.rf1 ex>> /\
    <<RF2: Valid.rf2 ex>> /\
    <<RF_WF: Valid.rf_wf ex>> /\
    <<INTERNAL:
      forall eid1 eid2
        (INTERNAL: ex.(Execution.internal)⁺ eid1 eid2),
        Time.lt (cov eid1) (cov eid2) \/
        (Time.le (cov eid1) (cov eid2) /\
         Execution.po eid1 eid2 /\
         ex.(Execution.label_is) Label.is_read eid1 /\
         ex.(Execution.label_is) Label.is_read eid2) \/
        (Time.le (cov eid1) (cov eid2) /\
         ex.(Execution.label_is) Label.is_write eid1 /\
         ex.(Execution.label_is) Label.is_read eid2)>> /\
    <<EXTERNAL:
      forall eid1 eid2
        (OB: (ex.(Execution.ob) ∩ (ex.(Execution.label_is_rel) Label.is_access))⁺ eid1 eid2),
        Time.lt (vext eid1) (vext eid2) \/
        (Time.le (vext eid1) (vext eid2) /\
         Execution.po eid1 eid2 /\
         ex.(Execution.label_is) Label.is_read eid1 /\
         ex.(Execution.label_is) Label.is_read eid2) \/
        (Time.le (vext eid1) (vext eid2) /\
         ex.(Execution.label_is) Label.is_write eid1 /\
         ex.(Execution.label_is) Label.is_read eid2)>> /\
    <<ATOMIC: le (ex.(Execution.rmw) ∩ (ex.(Execution.fre) ⨾ ex.(Execution.coe))) bot>> /\
    <<STATE: IdMap.Forall2
               (fun tid sl aeu => sim_state_weak sl.(fst) aeu.(AExecUnit.state))
               m.(Machine.tpool) PRE.(Valid.aeus)>>.
Proof.
  exploit promising_pf_sim_traces; eauto. i. des.
  destruct PRE, ex. ss.
  remember (Execution.mk labels addr data ctrl rmw (co_gen ws) (rf_gen ws rs)) as ex'.
  replace labels with ex'.(Execution.labels) in LABELS; [|subst; ss].
  replace addr with ex'.(Execution.addr) in ADDR; [|subst; ss].
  replace data with ex'.(Execution.data) in DATA; [|subst; ss].
  replace ctrl with ex'.(Execution.ctrl) in CTRL; [|subst; ss].
  replace rmw with ex'.(Execution.rmw) in RMW; [|subst; ss].
  remember (@Valid.mk_pre_ex p ex' aeus AEUS LABELS ADDR DATA CTRL RMW) as PRE'.
  replace aeus with PRE'.(Valid.aeus) in ATR; [|subst; ss].
  exists ex'. exists PRE'. exists (v_gen covs). exists (v_gen vexts).
  generalize STEP. intro X. inversion X.
  generalize (sim_traces_co1 PRE' SIM ATR). intro CO1.
  generalize (sim_traces_co2 PRE' SIM ATR). intro CO2.
  generalize (sim_traces_rf1 STEP PRE' NOPROMISE SIM TR ATR). intro RF1.
  generalize (sim_traces_rf2 PRE' SIM ATR). intro RF2.
  generalize (sim_traces_rf_wf SIM). intro RF_WF.
  replace (co_gen ws) with (ex'.(Execution.co)) in CO1, CO2;[|subst; ss].
  replace (rf_gen ws rs) with (ex'.(Execution.rf)) in RF1, RF2, RF_WF; [|subst; ss].
  exploit sim_traces_valid; eauto; try by (subst; ss). i. des.
  assert (INTERNAL': forall eid1 eid2 (INTERNAL: ex'.(Execution.internal)⁺ eid1 eid2),
             Time.lt (v_gen covs eid1) (v_gen covs eid2) \/
             (Time.le (v_gen covs eid1) (v_gen covs eid2) /\
              Execution.po eid1 eid2 /\
              ex'.(Execution.label_is) Label.is_read eid1 /\
              ex'.(Execution.label_is) Label.is_read eid2) \/
             (Time.le (v_gen covs eid1) (v_gen covs eid2) /\
              ex'.(Execution.label_is) Label.is_write eid1 /\
              ex'.(Execution.label_is) Label.is_read eid2)).
  { i. induction INTERNAL0.
    + exploit INTERNAL; eauto. i. des; eauto.
      { exploit Valid.internal_rw; eauto. i. des.
        inversion EID1. inversion EID2.
        destruct l0; ss.
        - destruct l; ss.
          + exploit Valid.internal_read_read_po; eauto. i.
            right. left. splits; eauto.
          + right. right. split; eauto.
        - inversion x1. rewrite EID0 in EID3. inversion EID3.
          rewrite H1 in *. destruct l0; ss; congr. }
    + des.
      * left. etrans; eauto.
      * left. eapply le_lt_trans; eauto.
      * left. eapply le_lt_trans; eauto.
      * left. eapply lt_le_trans; eauto.
      * right. left. splits; try etrans; eauto.
      * right. right. splits; try etrans; eauto.
      * left. eapply lt_le_trans; eauto.
      * inversion IHINTERNAL0_6. inversion IHINTERNAL0_0.
        rewrite EID in EID0. inversion EID0. rewrite H0 in *.
        destruct l0; ss; congr.
      * inversion IHINTERNAL0_5. inversion IHINTERNAL0_0.
        rewrite EID in EID0. inversion EID0. rewrite H0 in *.
        destruct l0; ss; congr. }
  esplits; eauto.
  - generalize (internal_acyclic _ INTERNAL'). intro ACYCLIC.
    clear INTERNAL'. i. induction OB.
    + inversion H. inversion H1.
      exploit EXTERNAL; eauto. i. des; eauto.
      { destruct l1.
        - exploit Valid.ob_read_read_po; eauto. i.
          right. left. splits; eauto.
        - right. right. splits; eauto.
        - inv LABEL1. }
    + des.
      * left. etrans; eauto.
      * left. eapply le_lt_trans; eauto.
      * left. eapply le_lt_trans; eauto.
      * left. eapply lt_le_trans; eauto.
      * right. left. splits; try etrans; eauto.
      * right. right. splits; try etrans; eauto.
      * left. eapply lt_le_trans; eauto.
      * inversion IHOB6. inversion IHOB0. rewrite EID in EID0.
        inversion EID0. rewrite H0 in *. ss. destruct l0; ss; congr.
      * inversion IHOB5. inversion IHOB0. rewrite EID in EID0.
        inversion EID0. rewrite H0 in *. ss. destruct l0; ss; congr.
  - clear - SIM TR ATR.
    ii. generalize (SIM id). i. inv H; ss.
    + generalize (TR id). i. inv H; try congr.
      generalize (ATR id). i. inv H; try congr.
      econs.
    + generalize (TR id). i. inv H; try congr.
      generalize (ATR id). i. inv H; try congr.
      des. simplify. inv REL6; auto.
      { econs. unfold init_with_promises in *. ss.
        rewrite IdMap.mapi_spec in *. rewrite STMT in FIND. ss.
        symmetry in FIND. inv FIND. rewrite H0.
        apply sim_state_weak_init. }
Qed.

Theorem promising_pf_to_axiomatic
        p m
        (STEP: Machine.pf_exec p m):
  exists ex (EX: Valid.ex p ex),
    <<TERMINAL: Machine.is_terminal m -> EX.(Valid.is_terminal)>> /\
    <<STATE: IdMap.Forall2
               (fun tid sl aeu => sim_state_weak sl.(fst) aeu.(AExecUnit.state))
               m.(Machine.tpool) EX.(Valid.aeus)>>.
Proof.
  exploit promising_pf_valid; eauto. i. des.
  exists ex. eexists (Valid.mk_ex PRE CO1 CO2 RF1 RF2 RF_WF _ _ ATOMIC).
  s. esplits; eauto.
  ii. inv H. specialize (STATE tid). inv STATE; try congr.
  rewrite FIND in H. inv H. destruct a. destruct aeu. ss.
  exploit TERMINAL; eauto. i. des. inv REL. inv x. congr.
Grab Existential Variables.
{ (* external *)
  ii. exploit Valid.ob_cycle; eauto. i. des.
  - clear - EXTERNAL NONBARRIER.
    exploit EXTERNAL; eauto. i. des.
    + inv x; lia.
    + inv x0. lia.
    + inv x0. inv x1. rewrite EID in EID0. inv EID0. destruct l0; ss; congr.
  - exploit Valid.barrier_ob_po; eauto. i. inv x1. lia.
}
{ (* internal *)
  clear - INTERNAL.
  eapply internal_acyclic. auto.
}
Qed.
