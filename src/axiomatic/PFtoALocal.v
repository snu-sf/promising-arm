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

Inductive sim_local_weak (local: Local.t (A:=unit)) (alocal: ALocal.t): Prop :=
| sim_local_weak_none
    (LOCAL_EX: local.(Local.exbank) = None)
    (ALOCAL_EX: alocal.(ALocal.exbank) = None)
| sim_local_weak_some
    eb aeb ex ord loc val
    (LOCAL_EX: local.(Local.exbank) = Some eb)
    (ALOCAL_EX: alocal.(ALocal.exbank) = Some aeb)
    (LABEL_EX: List.nth_error alocal.(ALocal.labels) aeb = Some (Label.read ex ord loc val))
    (EX_EX: ex = true)
    (EX_LOC: loc = eb.(Exbank.loc))
.
Hint Constructors sim_local_weak.

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
| sim_event_internal:
    sim_event Event.internal Event.internal
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
| sim_event_control
    ctrl1 ctrl2:
    sim_event (Event.control ctrl1) (Event.control ctrl2)
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
    (LOCAL: sim_local_weak eu2.(ExecUnit.local) aeu2.(AExecUnit.local))
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

Lemma sim_trace_memory
      p mem tid tr atr rl wl covl vextl
      eu tr'
      (SIM: sim_trace p mem tid tr atr rl wl covl vextl)
      (EU: tr = eu :: tr'):
  mem = eu.(ExecUnit.mem).
Proof.
  revert eu tr' EU.
  induction SIM.
  - ii. inv EU. ss.
  - ii. inv EU. exploit IHSIM; try refl. i.
    inv STEP. ss.
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
      (STATE1: sim_state_weak eu1.(ExecUnit.state) aeu1.(AExecUnit.state))
      (LOCAL1: sim_local_weak eu1.(ExecUnit.local) aeu1.(AExecUnit.local))
      (STEP: ExecUnit.state_step0 tid e e eu1 eu2):
  exists ae aeu2,
    <<ASTATE_STEP: State.step ae aeu1.(AExecUnit.state) aeu2.(AExecUnit.state)>> /\
    <<ALOCAL_STEP: ALocal.step ae aeu1.(AExecUnit.local) aeu2.(AExecUnit.local)>> /\
    <<EVENT: sim_event e ae>> /\
    <<STATE2: sim_state_weak eu2.(ExecUnit.state) aeu2.(AExecUnit.state)>> /\
    <<LOCAL2: sim_local_weak eu2.(ExecUnit.local) aeu2.(AExecUnit.local)>>.
Proof.
  destruct eu1 as [st1 lc1 mem1].
  destruct eu2 as [st2 lc2 mem2].
  destruct aeu1 as [[astmt1 armap1] alc1].
  inv STATE1. inv STEP. ss. subst. inv STATE; inv LOCAL; inv EVENT; ss.
  - eexists _, (AExecUnit.mk (State.mk _ _) _). splits; ss.
    + econs 1.
    + econs; ss.
    + ss.
    + ss.
    + inv LOCAL1; [econs 1|econs 2]; eauto.
  - eexists _, (AExecUnit.mk (State.mk _ _) _). splits; ss.
    + econs 2. ss.
    + econs; ss.
    + econs; ss.
    + econs; ss. eauto using sim_rmap_weak_add, sim_rmap_weak_expr.
    + inv LOCAL1; [econs 1|econs 2]; eauto.
  - inv STEP. ss.
    eexists _, (AExecUnit.mk (State.mk _ _) _). splits; ss.
    + econs 3; ss.
    + econs 2; ss.
    + econs; ss. eauto using sim_rmap_weak_add, sim_rmap_weak_expr.
    + econs; ss. eauto using sim_rmap_weak_add, sim_rmap_weak_expr.
    + destruct ex0.
      * econs 2; ss.
        rewrite List.nth_error_app2, minus_diag; ss.
        specialize (@sim_rmap_weak_expr rmap armap1 eloc RMAP). i.
        inv H. rewrite VAL. refl.
      * inv LOCAL1; [econs 1|econs 2]; eauto; ss.
        rewrite List.nth_error_app1; eauto.
        eapply List.nth_error_Some. ii. congr.
  - inv STEP. ss.
    eexists _, (AExecUnit.mk (State.mk _ _) _). splits; ss.
    + econs 4; ss.
    + econs 3; ss. inv WRITABLE. i. specialize (EX H). des.
      inv LOCAL1; try congr.
      rewrite TSX in LOCAL_EX. inv LOCAL_EX.
      esplits; eauto. rewrite LABEL_EX; eauto.
    + econs; ss.
      * eauto using sim_rmap_weak_add, sim_rmap_weak_expr.
      * eauto using sim_rmap_weak_add, sim_rmap_weak_expr.
    + econs; ss. eauto using sim_rmap_weak_add, sim_rmap_weak_expr.
    + destruct ex0; eauto.
      inv LOCAL1; [econs 1|econs 2]; ss.
      { eauto. }
      { eauto. }
      rewrite List.nth_error_app1; eauto.
      eapply List.nth_error_Some. ii. congr.
  - inv STEP. destruct ex0; ss.
    eexists _, (AExecUnit.mk (State.mk _ _) _). splits; ss.
    + econs 4; ss.
    + econs 4; ss.
    + econs; ss.
      * eauto using sim_rmap_weak_add, sim_rmap_weak_expr.
      * eauto using sim_rmap_weak_add, sim_rmap_weak_expr.
    + econs; ss. eauto using sim_rmap_weak_add, sim_rmap_weak_expr.
    + eauto.
  - inv STEP.
    eexists _, (AExecUnit.mk (State.mk _ _) _). splits; ss.
    + econs 5; ss.
    + econs 5; ss.
    + econs; ss.
    + econs; ss.
    + inv LOCAL1; [econs 1|econs 2]; eauto; ss.
      rewrite List.nth_error_app1; eauto.
      eapply List.nth_error_Some. ii. congr.
  - inv STEP.
    eexists _, (AExecUnit.mk (State.mk _ _) _). splits; ss.
    + econs 5; ss.
    + econs 5; ss.
    + econs; ss.
    + econs; ss.
    + inv LOCAL1; [econs 1|econs 2]; eauto; ss.
      rewrite List.nth_error_app1; eauto.
      eapply List.nth_error_Some. ii. congr.
  - inv LC.
    eexists _, (AExecUnit.mk (State.mk _ _) _). splits; ss.
    + econs 6; ss.
    + econs 6; ss.
    + econs; ss.
      exploit sim_rmap_weak_expr; eauto. intro X. inv X.
      inv VAL. rewrite <- H0. ss.
    + inv LOCAL1; [econs 1|econs 2]; eauto.
  - eexists _, (AExecUnit.mk (State.mk _ _) _). splits; ss.
    + econs 7. ss.
    + econs; ss.
    + ss.
    + ss.
    + inv LOCAL1; [econs 1|econs 2]; eauto.
Qed.

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
  { inv REL6; eauto. s.
    unfold init_with_promises in FIND0. ss.
    rewrite IdMap.mapi_spec, STMT in *. inv FIND0.
    auto.
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
      cov eid = ts /\
      vext eid = ts /\
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
    cov eid = ts /\
    le ts (eu.(ExecUnit.local).(Local.coh) loc) /\
    exists ex ord val tid',
      List.nth_error aeu.(AExecUnit.local).(ALocal.labels) eid = Some (Label.read ex ord loc val) /\
      __guard__ ((ts = Time.bot /\ val = Val.default) \/
                 Memory.get_msg ts mem = Some (Msg.mk loc val tid'));
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
  sim_th p mem tid eu aeu w r cov vext.
Proof.
  revert r rl' w wl' eu tr' aeu atr' cov covl' vext vextl' RL WL EU AEU COV VEXT. induction SIM.
  { i. simplify. ss. econs; ss.
    - rewrite IdMap.mapi_spec, STMT in FIND. inv FIND. s. i.
      left. splits; ss. admit. (* promises_from_mem *)
    - rewrite IdMap.mapi_spec, STMT in FIND. inv FIND. s. i.
      destruct eid; ss.
    - rewrite IdMap.mapi_spec, STMT in FIND. inv FIND. s. i.
      destruct eid; ss.
    - i. destruct iid1; ss.
  }
  clear LOCAL.
  i. simplify.
  destruct eu1 as [st1 lc1 mem1].
  destruct eu as [st2 lc2 mem2].
  destruct aeu1 as [ast1 alc1].
  destruct aeu as [ast2 alc2].
  assert (mem1 = mem); subst.
  { exploit sim_trace_memory; eauto. }
  ss. exploit IHSIM; eauto.
  i. rename x into IH.
  inv STEP. inv ALOCAL_STEP; inv EVENT; ss; eauto.
  { (* internal *)
    inv LOCAL; ss. inv EVENT. econs; ss; try by apply IH.
  }
  { (* read *)
    inv LOCAL; ss. inv STEP. inv STATE0. inv ASTATE_STEP. ss. inv EVENT.
    exploit sim_trace_sim_state_weak; eauto. s. intro Y. inv Y. ss. inv STMTS.
    exploit sim_rmap_weak_expr; eauto. intro Y. inv Y.

    econs; ss.
    - i. exploit IH.(WPROP1); eauto. s. i. des; [left|right]; esplits; eauto.
      eapply nth_error_app_mon. eauto.
    - i. exploit IH.(WPROP2); eauto.
      apply nth_error_app_inv in GET. des; eauto.
      apply nth_error_singleton_inv in GET0. des. congr.
    - i. exploit IH.(WPROP3); eauto. s. i. des. des_ifs.
      { exfalso. apply Nat.eqb_eq in Heq. subst.
        unfold ALocal.next_eid in *.
        assert (H: List.nth_error (ALocal.labels alc1) (length (ALocal.labels alc1)) <> None) by (ii; congr).
        apply List.nth_error_Some in H. lia.
      }
      esplits; eauto.
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
    - i. unfold ALocal.next_eid in *.
      apply nth_error_app_inv in LABEL1. apply nth_error_app_inv in LABEL2. des.
      + repeat condtac.
        all: try apply Nat.eqb_eq in X; ss; subst; try lia.
        all: try apply Nat.eqb_eq in X0; ss; subst; try lia.
        eapply IH.(PO); eauto.
      + lia.
      + apply nth_error_singleton_inv in LABEL0. des. subst.
        repeat condtac; ss.
        all: try apply Nat.eqb_eq in X; ss; subst; try lia.
        all: try apply Nat.eqb_neq in X0; ss; try lia.
        replace iid2 with (length (ALocal.labels alc1)) in * by lia.
        splits; ss. rewrite fun_add_spec. des_ifs; [|congr].
        inv REL. destruct label1; ss.
        * destruct (equiv_dec loc0 loc); ss. inv e0.
          destruct (equiv_dec (ValA.val (sem_expr rmap0 eloc0)) loc); ss. inv e0.
          exploit IH.(RPROP1); eauto. i. des.
          exploit IH.(RPROP2); eauto. s. i. des. subst.
          exploit sim_rmap_weak_expr; eauto. i. inv x2. rewrite VAL1 in COH.
          etrans; eauto.
        * destruct (equiv_dec loc0 loc); ss. inv e0.
          destruct (equiv_dec (ValA.val (sem_expr rmap0 eloc0)) loc); ss. inv e0.
          exploit IH.(WPROP2); eauto. i. des.
          exploit IH.(WPROP3); eauto. s. i. des. subst.
          exploit sim_rmap_weak_expr; eauto. i. inv x3. rewrite VAL1 in COH.
          etrans; eauto.
      + apply nth_error_singleton_inv in LABEL0. des. subst.
        repeat condtac; ss.
        all: try apply Nat.eqb_eq in X; ss; try lia.
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
      + clear Heq0. rewrite fun_add_spec in *. des_ifs; [|congr].
        exploit IH.(WPROP3); eauto. s. i. des.
        exploit IH.(WPROP1); eauto. s. rewrite PROMISE. i. des; ss.
        rewrite MSG in x5. inv x5. clear -WRITABLE x3. unfold le in x3. inv WRITABLE. lia.
      + rewrite fun_add_spec in *. des_ifs; [|congr].
        exploit IH.(WPROP3); eauto. s. i. des.
        exploit IH.(WPROP1); eauto. s. rewrite PROMISE. i. des; ss.
        rewrite MSG in x5. inv x5. clear -WRITABLE x3. unfold le in x3. inv WRITABLE. lia.
      + eapply IH.(WPROP4); eauto.
    - i. exploit IH.(RPROP1); eauto.
      apply nth_error_app_inv in GET. des; eauto.
      apply nth_error_singleton_inv in GET0. des. congr.
    - i. exploit IH.(RPROP2); eauto. s. i. des. esplits; eauto.
      * des_ifs.
        exfalso. apply Nat.eqb_eq in Heq. subst.
        unfold ALocal.next_eid in *.
        assert (H: List.nth_error (ALocal.labels alc1) (length (ALocal.labels alc1)) <> None) by (ii; congr).
        apply List.nth_error_Some in H. lia.
      * rewrite fun_add_spec. des_ifs; eauto. inv e. etrans; eauto.
        inv WRITABLE. apply Nat.lt_le_incl. ss.
      * eapply nth_error_app_mon. eauto.
    - inv ASTATE_STEP; ss; eauto. subst.
      inv VLOC. inv VVAL. rewrite VAL0, VAL1 in *. unfold ALocal.next_eid in *.
      i. apply nth_error_app_inv in LABEL1. apply nth_error_app_inv in LABEL2. des.
      + repeat condtac; ss.
        all: try apply Nat.eqb_eq in X; ss; subst; try lia.
        all: try apply Nat.eqb_eq in X0; ss; subst; try lia.
        eapply IH.(PO); eauto.
      + lia.
      + apply nth_error_singleton_inv in LABEL0. des. subst.
        repeat condtac; ss.
        all: try apply Nat.eqb_eq in X; ss; subst; try lia.
        all: try apply Nat.eqb_neq in X0; ss; try lia.
        splits; ss. rewrite fun_add_spec. des_ifs; [|congr].
        inv REL. destruct label1; ss.
        * destruct (equiv_dec loc0 loc); ss. inv e0.
          destruct (equiv_dec (ValA.val (sem_expr rmap eloc)) loc); ss. inv e0.
          exploit IH.(RPROP1); eauto. i. des.
          exploit IH.(RPROP2); eauto. s. i. des. subst.
          eapply Nat.le_lt_trans; eauto. inv WRITABLE. rewrite VAL0 in *. ss.
        * destruct (equiv_dec loc0 loc); ss. inv e0.
          destruct (equiv_dec (ValA.val (sem_expr rmap eloc)) loc); ss. inv e0.
          exploit IH.(WPROP2); eauto. i. des.
          exploit IH.(WPROP3); eauto. s. i. des. subst.
          eapply Nat.le_lt_trans; eauto. inv WRITABLE. rewrite VAL0 in *. ss.
      + apply nth_error_singleton_inv in LABEL0. des. subst.
        repeat condtac; ss.
        all: try apply Nat.eqb_eq in X; ss; try lia.
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
      - i. apply nth_error_app_inv in LABEL1. des; cycle 1.
        { apply nth_error_singleton_inv in LABEL0. des. subst. inv REL. inv X. }
        apply nth_error_app_inv in LABEL2. des; cycle 1.
        { apply nth_error_singleton_inv in LABEL3. des. subst. inv REL. inv Y. }
        eapply IH.(PO); eauto.
    }
  }
  { (* internal *)
    inv LOCAL; ss. inv LC. inv EVENT. econs; ss; try by apply IH.
  }
Admitted.
