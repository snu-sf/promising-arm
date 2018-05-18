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
           (tid: Id.t) (mem: Memory.t): Promises.t.
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
      (VALID: is_valid p ex):
  exists (m: Machine.t),
    <<STEP: rtc Machine.step (Machine.init p) m>> /\
    <<TERMINAL: Machine.is_terminal m>> /\
    <<MEM: sim_mem ex m.(Machine.mem)>>.
Proof.
  (* Linearize events and construct memory. *)
  exploit (linearize (Execution.eids ex)).
  { inv VALID. apply EXTERNAL. }
  i. des. rename l' into eids.
  remember (mem_of_ex ex eids) as mem eqn:MEM.

  (* Construct promise steps. *)
  exploit (promise_mem p mem); eauto.
  { i. subst. unfold mem_of_ex in MSG. rewrite in_filter_map_iff in MSG. des.
    exploit Permutation_in; eauto. intro X.
    generalize (Execution.eids_spec ex). i. des.
    apply LABEL in X. destruct (Execution.label a ex) eqn:Y; ss.
    destruct t; ss. inv MSG0. s. unfold Execution.label in Y.
    inv VALID. inv PRE. rewrite LABELS, IdMap.map_spec in Y.
    destruct (IdMap.find (fst a) locals) eqn:Z; ss.
    specialize (LOCALS (fst a)). inv LOCALS; ss. congr.
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

  clear TPOOL.
  setoid_rewrite IdMap.elements_spec in IN at 1.
  setoid_rewrite IdMap.elements_spec in OUT at 1.
  generalize (IdMap.elements_3w p). intro NODUP. revert NODUP.
  revert IN OUT. generalize (IdMap.elements p). intro ps.
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
    exploit (IHps (Machine.mk
                     (IdMap.add tid (st2, lc2) (Machine.tpool m))
                     (Machine.mem m))); ss.
    { i. rewrite IdMap.add_spec. condtac; ss.
      - inversion e. subst. inv NODUP. contradict H2.
        revert H. clear. induction ps; ss. destruct a.
        destruct (equiv_dec tid k); ss.
        + inv e. left. ss.
        + i. right. apply IHps. ss.
      - apply IN. destruct (equiv_dec tid0 tid); ss.
    }
    { i. revert FIND2. rewrite IdMap.add_spec. condtac.
      - i. inv FIND2. inversion e. eauto.
      - apply OUT. destruct (equiv_dec tid0 tid); ss.
    }
    { inv NODUP. ss. }
    i. des. esplits; cycle 1; eauto. etrans; eauto.
  }
  clear NODUP IN OUT IHps ps.

  (* Execute a thread `tid`. *)
  admit.
Admitted.
