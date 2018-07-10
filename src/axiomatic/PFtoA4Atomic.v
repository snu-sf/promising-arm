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
Require Import PromisingArch.axiomatic.PFtoA4FR.

Set Implicit Arguments.


Lemma sim_traces_sim_th'_atomic
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
    sim_atomic tid ex (v_gen vexts) eu2 aeu2.
Proof.
  i. rename SIM_TH' into L.
  exploit sim_traces_sim_th'_fr; eauto. intro SIM_FR.
  specialize (SIM_FR cov2 covl' vext1 vext2 vextl'
                     FIND_TR FIND_ATR FIND_COVL FIND_VEXTL EU AEU COV VEXT L).
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
  destruct (le_lt_dec (length (ALocal.labels (AExecUnit.local aeu1))) eid2); cycle 1.
  { eapply L; eauto. }
  exploit Valid.rmw_spec; eauto. i. des.
  inv LABEL2. des. destruct l0; ss. destruct ex0; ss.
  destruct eu1 as [st1 lc1 mem1].
  destruct eu2 as [st2 lc2 mem2].
  destruct aeu1 as [ast1 alc1].
  destruct aeu2 as [ast2 alc2].
  inv ASTATE_STEP; inv EVENT; inv ALOCAL_STEP; inv EVENT; repeat (ss; subst).
  all: try (clear - LABEL l; lia).
  all: rewrite List.app_length in LABEL; ss.
  all: assert (EID2: eid2 = length (ALocal.labels alc1)) by (clear - LABEL l; lia); subst.
  all: exploit LABELS; eauto; ss.
  all: try by clear; rewrite List.app_length; s; lia.
  all: intro NTH; apply nth_error_snoc_inv_last in NTH; inv NTH.
  rewrite EU, AEU, COV, VEXT, <- WL, <- RL in SIMTR.
  destruct eid1 as [tid1 eid1]. inv PO. ss. subst.
  inv FRE. exploit SIM_FR; try exact H; [|intro X]; ss.
  { rewrite List.app_length; ss. etrans; eauto. }
  destruct eid as [tid' eid'].
  inv COE. exploit sim_traces_vext_co; eauto. intro Y.
  rewrite CO in H1. inv H1. ss.
  generalize (SIM tid'). intro SIM'. inv SIM'; simplify.
  exploit sim_trace_last; try exact REL0. i. des. simplify.
  exploit sim_trace_sim_th; try exact REL0; eauto. intro L'.
  exploit L'.(WPROP3); eauto. i. des.
  exploit sim_trace_memory; try exact SIMTR; eauto. intro MEM. ss.
  inv STEP0. ss. subst.
  inv LOCAL0; inv EVENT; cycle 1.
  { inv STEP0. inv RES. inv VAL. }
  inv STEP0. inv WRITABLE. exploit EX0; ss. i. des.
  destruct L.(LC). ss.
  rewrite TSX in EXBANK. inv EXBANK. des.
  exploit EX2.(RMW); eauto; ss.
  { rewrite List.app_length. ss. }
  i. inv x1.
  { admit. (* use well-formedness *) }
  inv H1. rewrite <- H5 in H9. inv H9.
  assert (LOC: Exbank.loc eb = ValA.val vloc).
  { admit. (* use fr and co *) }
  specialize (EX1 LOC). unfold Memory.exclusive in EX1.
  unfold Memory.no_msgs in EX1.
  destruct (cov eid'); ss.
  move x5 at bottom.
  unfold Memory.get_msg in x5. ss.
  exploit EX1; try exact x5; eauto.
  { admit. }
  { admit. }
  { ss. split.
    - admit.
    - inv H0. auto. }
Admitted.
