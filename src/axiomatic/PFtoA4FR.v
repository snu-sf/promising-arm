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
  { inv FR. inv H.
    - des. exploit RF2; eauto. i. des. econs; eauto.
    - inv H. inv H1. inv H. ss.
  }
  inv LABEL1. destruct l0; ss.
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
  exploit sim_trace_sim_th; try exact SIMTR; eauto. intro L'.
  exploit L'.(RPROP1); ss.
  { apply nth_error_last. apply Nat.eqb_eq. ss. }
  unfold ALocal.next_eid in *. condtac; cycle 1.
  { apply Nat.eqb_neq in X. congr. }
  exploit L'.(RPROP2); ss.
  { rewrite X. eauto. }
  rewrite X. i. des. inv x1. apply nth_error_snoc_inv_last in x4. inv x4.
  clear x0 x3 x5 tid'0.
  rewrite EX2.(XVEXT); s; cycle 1.
  { rewrite List.app_length. s. clear. lia. }
  rewrite X. 
  inv STEP0. ss. subst. inv LOCAL0; inv EVENT.
  admit. (* should be true from STEP0 *)

  (* ii. inversion FR0. *)
  (* - admit. (* read from non-initial value *) *)
  (* - inv H. inv H1. inv H. inv H1. *)
  (*   exploit LABELS; eauto. intro LABEL1. destruct l; ss. *)
  (*   rewrite EU, AEU, COV, VEXT, <- WL, <- RL in SIMTR. *)
  (*   exploit sim_trace_sim_th; try exact SIMTR; eauto. intro L'. *)
  (*   exploit L'.(RPROP1); eauto. i. des. unguardH x1. des. *)
  (*   + subst. *)
  (*     inv EVENT; ss. *)
  (*     * eapply FR; eauto. inv ALOCAL_STEP; ss. *)
  (*     * des_ifs; cycle 1. *)
  (*       { eapply FR; eauto. inv ALOCAL_STEP; ss. *)
  (*         eapply nth_error_not_last; eauto. } *)
  (*       { inv STEP0. ss. inv LOCAL0; ss. inv STEP0. inv EVENT. ss. *)
  (*         rewrite fun_add_spec in H1. *)
  (*         destruct (equiv_dec (ValA.val vloc) (ValA.val vloc)); try congr. *)
  (*         admit. *)
  (*       } *)
  (*     * inv STEP0. ss. inv LOCAL0; ss; inv EVENT. *)
  (*       { inv STEP0. ss. inv ALOCAL_STEP; ss. *)
  (*         - destruct (Nat.eqb eid1 (ALocal.next_eid alc1)) eqn:HEID1. *)
  (*           + rewrite nth_error_last in LABEL1; auto. inv LABEL1. *)
  (*           + eapply FR; eauto. eapply nth_error_not_last; eauto. *)
  (*         - inv EVENT. inv RES. ss. } *)
  (*       { inv STEP0. ss. eapply FR; eauto. inv ALOCAL_STEP; ss. *)
  (*         destruct (Nat.eqb eid1 (List.length (ALocal.labels alc1))) eqn:HEID1. *)
  (*         - rewrite nth_error_last in LABEL1; eauto. inv LABEL1. *)
  (*         - eapply nth_error_not_last; eauto. } *)
  (*     * inv STEP0. ss. inv LOCAL0; ss; inv EVENT. *)
  (*       { inv STEP0. ss. eapply FR; eauto. inv ALOCAL_STEP; ss. *)
  (*         destruct (Nat.eqb eid1 (List.length (ALocal.labels alc1))) eqn:HEID1. *)
  (*         - rewrite nth_error_last in LABEL1; eauto. inv LABEL1. *)
  (*         - eapply nth_error_not_last; eauto. } *)
  (*       { inv STEP0. ss. eapply FR; eauto. inv ALOCAL_STEP; ss. *)
  (*         destruct (Nat.eqb eid1 (List.length (ALocal.labels alc1))) eqn:HEID1. *)
  (*         - rewrite nth_error_last in LABEL1; eauto. inv LABEL1. *)
  (*         - eapply nth_error_not_last; eauto. } *)
  (*     * inv STEP0. ss. inv LOCAL0; ss; inv EVENT. *)
  (*       inv LC0. ss. eapply FR; eauto. inv ALOCAL_STEP; ss. *)
  (*       destruct (Nat.eqb eid1 (List.length (ALocal.labels alc1))) eqn:HEID1. *)
  (*       { rewrite nth_error_last in LABEL1; eauto. inv LABEL1. } *)
  (*       { eapply nth_error_not_last; eauto. } *)
  (*   + exploit sim_traces_memory; eauto. i. des. *)
  (*     generalize (SIM tid'). intro SIM'. inv SIM'; try congr. simplify. *)
  (*     exploit sim_trace_last; try exact REL0. i. des. subst. *)
  (*     exploit sim_trace_sim_th; try exact REL0; eauto. i. destruct x3. *)
  (*     exploit WPROP0; eauto. i. des. *)
  (*     * inv STEP. inv NOPROMISE. *)
  (*       generalize (TR tid'). intro TR'. inv TR'; try congr. des. simplify. *)
  (*       destruct b. exploit PROMISES0; eauto. i. *)
  (*       ss. rewrite x4 in *. rewrite Promises.lookup_bot in x1. ss. *)
  (*     * exfalso. apply H3. econs. rewrite RF. *)
  (*       instantiate (1 := (tid', eid)). *)
  (*       exploit sim_trace_last; try exact REL6. i. des. subst. *)
  (*       econs; try refl; ss; eauto. *)
  (*       admit. (* should prove that r includes r2 *) *)
Admitted.
