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

Require Import PromisingArch.lib.Basic.
Require Import PromisingArch.lib.Order.
Require Import PromisingArch.lib.Time.
Require Import PromisingArch.lib.Lang.
Require Import PromisingArch.promising.Promising.
Require Import PromisingArch.lcertify.Certify.
Require Import PromisingArch.lcertify.CertifySim.

Set Implicit Arguments.


Inductive certified_promise (tid:Id.t) (eu1:ExecUnit.t (A:=unit)) (loc:Loc.t) (val:Val.t): Prop :=
| certified_promise_intro
    eu2 eu3 eu4 mem2' view_pre
    (STEP2: rtc (certify_step tid) eu1 eu2)
    (STEP3: write_step tid loc val view_pre eu2 eu3)
    (STEP4: rtc (certify_step tid) eu3 eu4)
    (MEM: eu2.(ExecUnit.mem) = eu1.(ExecUnit.mem) ++ mem2')
    (MEM2': Forall (fun msg => msg.(Msg.loc) <> loc) mem2')
    (VIEW_PRE: view_pre.(View.ts) <= length eu1.(ExecUnit.mem))
.

Theorem certified_promise_complete
        tid (eu1 eu2:ExecUnit.t (A:=unit)) loc val ts
        (STATE: eu1.(ExecUnit.state) = eu2.(ExecUnit.state))
        (LOCAL: Local.promise loc val ts tid
                              eu1.(ExecUnit.local) eu1.(ExecUnit.mem)
                              eu2.(ExecUnit.local) eu2.(ExecUnit.mem))
        (CERTIFY: certify tid eu2):
  certified_promise tid eu1 loc val.
Proof.
Admitted.

Lemma promise_sim_eu
      tid (eu1:ExecUnit.t (A:=unit)) loc val
      (WF: ExecUnit.wf tid eu1):
  exists eu2,
    <<STEP: Local.promise loc val (S (length eu1.(ExecUnit.mem))) tid
                          eu1.(ExecUnit.local) eu1.(ExecUnit.mem)
                          eu2.(ExecUnit.local) eu2.(ExecUnit.mem)>> /\
    <<SIM: sim_eu tid (length eu1.(ExecUnit.mem)) (Promises.set (S (length eu1.(ExecUnit.mem))) bot) eu2 eu1>>.
Proof.
  destruct eu1 as [st1 lc1 mem1]. eexists (ExecUnit.mk st1 _ _). splits; ss.
  econs; ss.
  - admit. (* sim_state refl *)
  - econs; ss.
    + admit. (* sim_fwdbank *)
    + admit. (* sim_exbank *)
    + i. rewrite Promises.set_o. condtac; ss. clear X. inv e. lia.
    + i. rewrite ? Promises.set_o, Promises.lookup_bot. condtac; ss.
      eapply Local_wf_promises_above; eauto. apply WF.
  - econs; ss.
    + rewrite app_nil_r. ss.
    + i. revert TSP. rewrite Promises.set_o, Promises.lookup_bot. condtac; ss. clear X. inv e.
      rewrite app_length. s. clear. lia.
    + i. revert TSP. rewrite Promises.set_o, Promises.lookup_bot. condtac; ss. clear X. inv e.
      apply nth_error_snoc_inv in MSG. des; subst; ss.
      * lia.
      * splits; ss. inv WF. inv LOCAL. ss. eapply le_lt_trans; [apply COH|]. ss.
    + i. apply nth_error_singleton_inv in NTH. des. subst.
      revert PROMISES. rewrite Promises.set_o. condtac; ss.
      exfalso. apply c. rewrite Time.add_0_r. refl.
Admitted.

Theorem certified_promise_sound
        tid (eu1:ExecUnit.t (A:=unit)) loc val
        (WF: ExecUnit.wf tid eu1)
        (CERTIFY: certified_promise tid eu1 loc val):
  exists eu2 ts,
    <<STATE: eu1.(ExecUnit.state) = eu2.(ExecUnit.state)>> /\
    <<LOCAL: Local.promise loc val ts tid
                           eu1.(ExecUnit.local) eu1.(ExecUnit.mem)
                           eu2.(ExecUnit.local) eu2.(ExecUnit.mem)>> /\
    <<CERTIFY: certify tid eu2>>.
Proof.
  inv CERTIFY.
  exploit promise_sim_eu; eauto. i. des. rename eu0 into eu1', STEP into STEP1', SIM into SIM1.
  exploit sim_eu_rtc_step; eauto.
  { i. revert TSP. rewrite Promises.set_o. condtac; ss. clear X. inv e.
    admit. (* view_pre *)
  }
  { admit. (* wf *) }
  { rewrite <- VIEW_PRE.
    destruct eu2 as [st2 lc2 mem2].
    destruct eu3 as [st3 lc3 mem3].
    inv STEP3. inv PROMISE. inv FULFILL. inv WRITABLE. ss. subst.
    rewrite <- join_r, <- join_r, <- join_l. ss.
  }
  i. des. rename eu1'0 into eu2', STEP into STEP2', SIM into SIM2.
  admit. (* [write] and [to-the-end] *)
Admitted.
