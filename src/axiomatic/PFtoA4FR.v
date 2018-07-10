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
Require Import HahnSets.

Require Import PromisingArch.lib.Basic.
Require Import PromisingArch.lib.HahnRelationsMore.
Require Import PromisingArch.lib.Order.
Require Import PromisingArch.lib.Time.
Require Import PromisingArch.lib.Lang.
Require Import PromisingArch.promising.Promising.
Require Import PromisingArch.promising.StateExecFacts.
Require Import PromisingArch.axiomatic.Axiomatic.
Require Import PromisingArch.axiomatic.CommonAxiomatic.
Require Import PromisingArch.axiomatic.PFtoA1.
Require Import PromisingArch.axiomatic.PFtoA2.
Require Import PromisingArch.axiomatic.PFtoA3.

Set Implicit Arguments.


Lemma sim_traces_sim_th'_fr
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
  forall tid tr atr covl vextl
    n eu1 eu2 tr' aeu1 aeu2 atr' cov1 cov2 covl' vext1 vext2 vextl'
    (FIND_TR: IdMap.find tid trs = Some tr)
    (FIND_ATR: IdMap.find tid atrs = Some atr)
    (FIND_COVL: IdMap.find tid covs = Some covl)
    (FIND_VEXTL: IdMap.find tid vexts = Some vextl)
    (EU: lastn (S n) tr = eu2 :: eu1 :: tr')
    (AEU: lastn (S n) atr = aeu2 :: aeu1 :: atr')
    (COV: lastn (S n) covl = cov2 :: cov1 :: covl')
    (VEXT: lastn (S n) vextl = vext2 :: vext1 :: vextl')
    (SIM_TH': sim_th' tid ex (v_gen vexts) eu1 aeu1),
    sim_fr tid ex (v_gen vexts) eu2 aeu2.
Proof.
  i. rename SIM_TH' into L.
  generalize (SIM tid). intro X. inv X; simplify. rename c into wl, d into rl.
  destruct n.
  { generalize (lastn_length 1 tr). rewrite EU. destruct tr; ss. }
  exploit sim_trace_lastn; eauto. instantiate (1 := S n). intro SIMTR.
  exploit sim_traces_ex; eauto. intro EX2.
  inversion SIMTR; subst; simplify; [congr|].
  repeat match goal with
         | [H1: lastn ?a ?b = ?c, H2: ?d = lastn ?a ?b |- _] =>
           rewrite H1 in H2; inv H2
         end.
  exploit sim_trace_sim_state_weak; eauto. intro STATE1.
  rename H2 into WS, H3 into RS, H4 into WL, H5 into RL.

  ii.
  destruct (le_lt_dec (length (ALocal.labels (AExecUnit.local aeu1))) eid1); cycle 1.
  { eapply L; eauto. }
  assert (LABEL1: Execution.label_is ex (fun label : Label.t => Label.is_read label) (tid, eid1)).
  { inv FR.
    - inv H. des. exploit RF2; eauto. i. des. econs; eauto.
    - inv H. inv H1. inv H. ss.
  }
  assert (LABEL2: Execution.label_is ex (fun label : Label.t => Label.is_write label) eid2).
  { inv FR.
    - inv H. des. exploit CO2; eauto. i. des. econs; eauto.
    - inv H. inv H1. ss.
  }
  inv LABEL1. destruct l0; ss.
  inv LABEL2. destruct l0; ss.
  destruct eid2 as [tid2 eid2].
  generalize (SIM tid2). intro SIMTR2. inv SIMTR2.
  { generalize (ATR tid2). rewrite <- H. intro X. inv X.
    unfold Execution.label in EID0. ss.
    rewrite PRE.(Valid.LABELS), IdMap.map_spec, <- H1 in EID0. ss.
  }
  rename REL0 into SIMTR2, a into tr2, b into atr2, c into wl2, d into rl2, e0 into covl2, f into vextl2.
  rename H0 into TR2, H into ATR2, H2 into WL2, H3 into RL2, H4 into COVL4, H5 into VEXTL5.
  destruct eu1 as [st1 lc1 mem1].
  destruct eu2 as [st2 lc2 mem2].
  destruct aeu1 as [ast1 alc1].
  destruct aeu2 as [ast2 alc2].
  inv ASTATE_STEP; inv EVENT; inv ALOCAL_STEP; inv EVENT; repeat (ss; subst).
  all: try (clear - LABEL l; lia).
  all: rewrite List.app_length in LABEL; ss.
  all: assert (EID1: eid1 = length (ALocal.labels alc1)) by (clear - LABEL l; lia); subst.
  all: exploit LABELS; eauto; ss.
  all: try by clear; rewrite List.app_length; s; lia.
  all: intro NTH; apply nth_error_snoc_inv_last in NTH; inv NTH.
  rewrite EU, AEU, COV, VEXT, <- WL, <- RL in SIMTR.
  exploit sim_trace_sim_th; try exact SIMTR; eauto. intro L2.
  exploit sim_trace_sim_th; try exact TRACE; eauto. intro L1.
  exploit L2.(RPROP1); ss.
  { apply nth_error_last. apply Nat.eqb_eq. ss. }
  unfold ALocal.next_eid in *. condtac; cycle 1.
  { apply Nat.eqb_neq in X. congr. }
  i. des. inv x0. rewrite EX2.(XVEXT) in *; s; cycle 1.
  { rewrite List.app_length. s. clear. lia. }
  rewrite X.
  inv STEP0. ss. subst. inv LOCAL0; inv EVENT.
  generalize L1.(EU_WF). intro WF. inv WF. ss.

  (* TODO: move *)
  Lemma read_spec
        `{A: Type, _: orderC A eq}
        tid mem ex ord vloc res ts (lc1 lc2:Local.t (A:=A))
        (WF: Local.wf tid mem lc1)
        (READ: Local.read ex ord vloc res ts lc1 mem lc2):
    <<LATEST: Memory.latest vloc.(ValA.val) ts res.(ValA.annot).(View.ts) mem>> /\
    <<TS: ts = lc2.(Local.coh) vloc.(ValA.val)>>.
  Proof.
    inv READ. ss. rewrite fun_add_spec. condtac; [|congr]. splits; ss.
    ii. eapply LATEST; eauto.
    exploit Local.fwd_read_view_le; eauto. instantiate (1 := ord). i.
    unfold join, Time.join in *. lia.
  Qed.

  Lemma latest_lt
        loc ts1 ts2 ts3 mem msg
        (LATEST: Memory.latest loc ts1 ts2 mem)
        (LT: ts1 < ts3)
        (MSG: Memory.get_msg ts3 mem = Some msg)
        (LOC: msg.(Msg.loc) = loc):
    ts2 < ts3.
  Proof.
    destruct ts3; ss.
    destruct (le_lt_dec (S ts3) ts2); ss.
    exfalso. eapply LATEST; eauto. 
  Qed.

  generalize (read_spec LOCAL0 STEP0). i. des. subst.
  exploit sim_traces_cov_fr; eauto.
  { inv STEP. ss. }
  rewrite EX2.(XCOV) in *; s; cycle 1.
  { rewrite List.app_length. s. clear. lia. }
  rewrite X. i.
  eapply latest_lt; eauto.
  all: admit. (* remaining work: finding w's message. *)
Admitted.
