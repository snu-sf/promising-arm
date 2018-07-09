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

Set Implicit Arguments.


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

Lemma nth_error_last A (l: list A) a n
      (N: Nat.eqb n (List.length l) = true):
  List.nth_error (l ++ [a]) n = Some a.
Proof.
  apply Nat.eqb_eq in N. subst.
  rewrite List.nth_error_app2, Nat.sub_diag; ss. 
Qed.

Lemma nth_error_not_last A (l: list A) a b n
      (NTH: List.nth_error (l ++ [a]) n = Some b)
      (N: Nat.eqb n (List.length l) = false):
  n < List.length l.
Proof.
  apply nth_error_snoc_inv in NTH. des; ss. subst.
  apply Nat.eqb_neq in N. lia.
Qed.

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

Definition sim_ob_write
           (tid:Id.t) (ex:Execution.t) (vext: eidT -> Time.t)
           (eu:ExecUnit.t (A:=unit)) (aeu:AExecUnit.t): Prop :=
  forall eid1 eid2
    (LABEL: eid2 < List.length aeu.(AExecUnit.local).(ALocal.labels))
    (OB: ex.(ob') eid1 (tid, eid2))
    (EID2: ex.(Execution.label_is) Label.is_write (tid, eid2)),
    Time.lt (vext eid1) (vext (tid, eid2)).

Definition sim_ob_read
           (tid:Id.t) (ex:Execution.t) (vext: eidT -> Time.t)
           (eu:ExecUnit.t (A:=unit)) (aeu:AExecUnit.t): Prop :=
  forall eid1 eid2
    (LABEL: eid2 < List.length aeu.(AExecUnit.local).(ALocal.labels))
    (AOB: ex.(ob') eid1 (tid, eid2))
    (EID2: ex.(Execution.label_is) Label.is_read (tid, eid2)),
    Time.le (vext eid1) (vext (tid, eid2)).

Definition sim_fr
           (tid:Id.t) (ex:Execution.t) (vext: eidT -> Time.t)
           (eu:ExecUnit.t (A:=unit)) (aeu:AExecUnit.t): Prop :=
  forall eid1 eid2
    (LABEL: eid1 < List.length aeu.(AExecUnit.local).(ALocal.labels))
    (FR: ex.(Execution.fr) (tid, eid1) eid2),
    Time.lt (vext (tid, eid1)) (vext eid2).

Inductive sim_th'
          (tid:Id.t) (ex:Execution.t) (vext: eidT -> Time.t)
          (eu:ExecUnit.t (A:=unit)) (aeu:AExecUnit.t): Prop := {
  ST: sim_state tid vext eu.(ExecUnit.state) aeu.(AExecUnit.state);
  LC: sim_local tid ex vext eu.(ExecUnit.local) aeu.(AExecUnit.local);
  OBW: sim_ob_write tid ex vext eu aeu;
  OBR: sim_ob_read tid ex vext eu aeu;
  FR: sim_fr tid ex vext eu aeu;
}.
Hint Constructors sim_th'.
