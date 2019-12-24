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

Require Import PromisingArch.lib.Basic.
Require Import PromisingArch.lib.Order.
Require Import PromisingArch.lib.Time.
Require Import PromisingArch.lib.Lang.

Set Implicit Arguments.


Module Msg.
  Inductive t := mk {
    loc: Loc.t;
    val: Val.t;
    tid: Id.t;
  }.
  Hint Constructors t.

  Global Program Instance eqdec: EqDec t eq.
  Next Obligation.
    destruct x, y.

    destruct (loc0 == loc1); cycle 1.
    { right. intro X. inv X. intuition. }

    destruct (val0 == val1); cycle 1.
    { right. intro X. inv X. intuition. }

    destruct (tid0 == tid1); cycle 1.
    { right. intro X. inv X. intuition. }

    left. f_equal; intuition.
  Defined.
End Msg.

Module Memory.
  Definition t := list Msg.t.

  Definition empty: t := [].

  Definition read (loc:Loc.t) (ts:Time.t) (mem:t): option Val.t :=
    match Time.pred_opt ts with
    | None => Some Val.default
    | Some ts =>
      match List.nth_error mem ts with
      | None => None
      | Some msg =>
        if msg.(Msg.loc) == loc
        then Some msg.(Msg.val)
        else None
      end
    end.

  Definition get_msg (ts:Time.t) (mem:t): option Msg.t :=
    match Time.pred_opt ts with
    | None => None
    | Some ts => List.nth_error mem ts
    end.

  Definition append (msg:Msg.t) (mem:t): Time.t * t :=
    (S (length mem), mem ++ [msg]).

  Definition no_msgs (from to:nat) (pred:Msg.t -> Prop) (mem:t): Prop :=
    forall ts msg
      (TS1: from < S ts)
      (TS2: S ts <= to)
      (MSG: List.nth_error mem ts = Some msg),
      ~ pred msg.

  Definition latest (loc:Loc.t) (from to:Time.t) (mem:t): Prop :=
    Memory.no_msgs from to (fun msg => msg.(Msg.loc) = loc) mem.

  Fixpoint latest_ts (loc:Loc.t) (to:Time.t) (mem:t): Time.t :=
    match to with
    | O => O
    | S to =>
      match List.nth_error mem to with
      | Some (Msg.mk loc0 _ _) =>
        if (Loc.eq_dec loc0 loc) then S to else latest_ts loc to mem
      | _ => latest_ts loc to mem
      end
    end
  .

  Definition exclusive (tid:Id.t) (loc:Loc.t) (from to:Time.t) (mem:t): Prop :=
    Memory.no_msgs from to (fun msg => msg.(Msg.loc) = loc /\ msg.(Msg.tid) <> tid) mem.

  Lemma read_mon ts loc val mem1 mem2
        (READ: Memory.read loc ts mem1 = Some val):
    Memory.read loc ts (mem1 ++ mem2) = Some val.
  Proof.
    revert READ. unfold Memory.read. destruct (Time.pred_opt ts); ss.
    destruct (nth_error mem1 t0) eqn:NTH; ss.
    rewrite nth_error_app1, NTH; ss.
    apply List.nth_error_Some. congr.
  Qed.

  Lemma get_msg_mon ts msg mem1 mem2
        (READ: Memory.get_msg ts mem1 = Some msg):
    Memory.get_msg ts (mem1 ++ mem2) = Some msg.
  Proof.
    revert READ. unfold Memory.get_msg. destruct (Time.pred_opt ts); ss.
    destruct (nth_error mem1 t0) eqn:NTH; ss.
    rewrite nth_error_app1, NTH; ss.
    apply List.nth_error_Some. congr.
  Qed.

  Lemma get_msg_read ts mem loc val tid
        (GET: get_msg ts mem = Some (Msg.mk loc val tid)):
    read loc ts mem = Some val.
  Proof.
    destruct ts; ss.
    unfold get_msg, read in *. ss.
    rewrite GET. ss. des_ifs. exfalso. apply c. ss.
  Qed.

  Lemma read_get_msg
        loc ts mem val
        (READ: read loc ts mem = Some val):
    (ts = Time.bot /\ val = Val.default) \/
    (exists tid, get_msg ts mem = Some (Msg.mk loc val tid)).
  Proof.
    revert READ. unfold read, get_msg. destruct ts; ss.
    - i. inv READ. left. eauto.
    - destruct (List.nth_error mem ts); ss. des_ifs. i. inv READ. inv e.
      destruct t0. s. right. eauto.
  Qed.

  Lemma get_msg_app_inv
        ts mem1 mem2 m
        (GET: get_msg ts (mem1 ++ mem2) = Some m):
    (ts <= length mem1 /\ get_msg ts mem1 = Some m) \/
    (ts > length mem1 /\ List.nth_error mem2 (ts - (S (length mem1))) = Some m).
  Proof.
    unfold get_msg in *. destruct ts; ss.
    destruct (lt_dec ts (length mem1)).
    - rewrite nth_error_app1 in GET; eauto.
    - rewrite nth_error_app2 in GET; [|lia]. right. splits; ss. lia.
  Qed.

  Lemma get_msg_snoc_inv
        ts mem msg m
        (GET: get_msg ts (mem ++ [msg]) = Some m):
    (ts <= length mem /\ get_msg ts mem = Some m) \/
    (ts = S (length mem) /\ msg = m).
  Proof.
    exploit get_msg_app_inv; eauto. i. des; [left|right]; ss.
    destruct ts; ss.
    destruct (ts - length mem) eqn:SUB; ss.
    - assert (ts = length mem) by lia. inv x1. ss.
    - destruct n; ss.
  Qed.

  Lemma get_latest
        loc mem:
    exists ts val,
      (forall ts' val (READ: read loc ts' mem = Some val), ts' <= ts) /\
      read loc ts mem = Some val.
  Proof.
    induction mem using List.rev_ind.
    { exists 0, Val.default. splits; ss. i. destruct ts'; ss. destruct ts'; ss. }
    destruct (loc == x.(Msg.loc)).
    { inversion e. subst. exists (S (length mem)), x.(Msg.val). splits.
      - i. unfold read in READ. destruct ts'; [lia|]. ss.
        destruct (nth_error (mem ++ [x]) ts') eqn:NTH; ss.
        apply nth_error_snoc_inv in NTH. des; [lia|]. subst. ss.
      - unfold read. ss. rewrite nth_error_app2, Nat.sub_diag; ss. condtac; ss.
    }
    des. exists ts, val. splits.
    - ii. eapply IHmem. rewrite <- READ.
      destruct (read loc ts' mem) eqn:READ'.
      { erewrite read_mon; eauto. }
      unfold read in *. destruct ts'; ss.
      destruct (nth_error (mem ++ [x]) ts') eqn:NTH; ss.
      apply nth_error_snoc_inv in NTH. des; ss.
      { rewrite NTH0 in READ'. ss. }
      subst. revert READ. condtac; ss. inversion e. subst. congr.
    - apply read_mon. ss.
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

  Lemma ge_latest loc ts1 ts2 mem
        (GE: ts2 <= ts1):
    Memory.latest loc ts1 ts2 mem.
  Proof. ii. lia. Qed.

  Lemma latest_mon1
        loc ts1 ts2 ts3 mem
        (LATEST: latest loc ts1 ts3 mem)
        (LT: ts1 <= ts2):
    latest loc ts2 ts3 mem.
  Proof.
    ii. eapply LATEST; try eapply MSG; eauto.
    eapply le_lt_trans; eauto.
  Qed.

  Lemma latest_mon2
        loc ts1 ts2 ts3 mem
        (LATEST: latest loc ts1 ts3 mem)
        (LT: ts2 <= ts3):
    latest loc ts1 ts2 mem.
  Proof.
    ii. eapply LATEST; try eapply MSG; eauto.
    eapply lt_le_trans; eauto.
  Qed.

  Lemma latest_join
        loc ts ts1 ts2 mem
        (LATEST1: latest loc ts ts1 mem)
        (LATEST2: latest loc ts ts2 mem):
    latest loc ts (join ts1 ts2) mem.
  Proof.
    destruct (le_dec ts1 ts2).
    - eapply latest_mon2; try exact LATEST2.
      rewrite max_r; auto.
    - eapply latest_mon2; try exact LATEST1.
      rewrite max_l; auto. lia.
  Qed.

  Lemma latest_ts_spec
        loc to mem:
    <<LE: latest_ts loc to mem <= to>> /\
    <<READ: exists val, read loc (latest_ts loc to mem) mem = Some val>>.
  Proof.
    induction to; i.
    - ss. esplits; ss.
    - ss. destruct (nth_error mem to) eqn:NTH.
      + destruct t0. des_ifs.
        * esplits; eauto. unfold read. ss. rewrite NTH.
          ss. des_ifs. exfalso. apply c. refl.
        * des. split; auto. esplits. eauto.
      + des. split; auto. esplits. eauto.
  Qed.

  Lemma latest_ts_mon
        loc to1 to2 mem
        (LE: to1 <= to2):
    latest_ts loc to1 mem <= latest_ts loc to2 mem.
  Proof.
    revert to1 LE. induction to2.
    - i. specialize (latest_ts_spec loc to1 mem). i. des.
      inv LE. inv LE0. auto.
    - i. inv LE; auto. rewrite IHto2; auto.
      clear. unfold latest_ts at 2. des_ifs.
      specialize (latest_ts_spec loc to2 mem). i. des.
      rewrite LE. auto.
  Qed.

  Lemma latest_ts_append
        loc to mem1 mem2:
    latest_ts loc to mem1 <= latest_ts loc to (mem1++mem2).
  Proof.
    induction to; ss.
    destruct (nth_error mem1 to) eqn:NTH.
    - exploit nth_error_app_mon; eauto. i.
      rewrite x0. destruct t0. condtac; ss.
    - destruct (nth_error (mem1++mem2) to); ss.
      destruct t0. condtac; ss.
      exploit latest_ts_spec. i. des. rewrite LE. lia.
  Qed.

  Lemma latest_ts_latest
        loc from to mem
        (LATEST: latest_ts loc to mem = from):
    latest loc from to mem.
  Proof.
    revert from LATEST.
    induction to; ii; try lia.
    ss. destruct (nth_error mem to) eqn:NTH.
    - destruct t0. revert LATEST. condtac.
      + i. subst. lia.
      + i. eapply IHto; eauto.
        destruct (le_lt_dec (S ts) to); auto.
        apply lt_le_S in l. exploit le_antisym; eauto. i.
        inv x0. destruct msg. ss. rewrite NTH in MSG. inv MSG.
        contradiction.
    - eapply IHto; eauto.
      destruct (le_lt_dec (S ts) to); auto.
      apply lt_le_S in l. exploit le_antisym; eauto. i.
      inv x0. rewrite NTH in MSG. inv MSG.
  Qed.

  Lemma latest_latest_ts
        loc from to mem
        (LATEST: latest loc from to mem):
    latest_ts loc to mem <= from.
  Proof.
    revert from LATEST.
    induction to; ii; ss; try lia.
    destruct (nth_error mem to) eqn:NTH.
    - destruct t0. condtac.
      + destruct (le_lt_dec (S to) from); auto.
        exfalso. eapply LATEST; eauto.
      + eapply IHto; eauto. eapply latest_mon2; eauto.
    - eapply IHto; eauto. eapply latest_mon2; eauto.
  Qed.

  Lemma latest_ts_read_lt
        loc from to mem v val
        (LATEST: latest_ts loc to mem = from)
        (READ: read loc v mem = Some val)
        (LT: from < v):
    to < v.
  Proof.
    generalize (latest_ts_latest mem LATEST). i.
    destruct (le_dec v to); try lia.
    destruct v; try by inv LT.
    unfold read in *. ss.
    destruct (nth_error mem v) eqn:NTH; ss. des_ifs.
    exfalso. eapply H; eauto.
  Qed.

  Lemma latest_ts_read_le
        loc to mem v val
        (READ: read loc v mem = Some val)
        (LE: v <= to):
    v <= latest_ts loc to mem.
  Proof.
    revert v val LE READ. induction to; ss; i.
    des_ifs.
    - inv LE; eauto.
      unfold read in READ. ss. rewrite Heq in READ.
      des_ifs.
    - inv LE; eauto.
      unfold read in READ. ss. rewrite Heq in READ. inv READ.
  Qed.

  Lemma no_msgs_split
        a b c pred mem
        (AB: a <= b)
        (BC: b <= c):
    no_msgs a c pred mem <->
    no_msgs a b pred mem /\ no_msgs b c pred mem.
  Proof.
    econs; intro X.
    - split; ii; eapply X; try exact MSG; ss.
      + lia.
      + lia.
    - des. ii.  destruct (le_lt_dec (S ts) b).
      + eapply X; eauto.
      + eapply X0; eauto.
  Qed.

  Lemma no_msgs_split'
        a b c pred mem:
    no_msgs a b pred mem /\ no_msgs b c pred mem ->
    no_msgs a c pred mem.
  Proof.
    i. des. ii. destruct (le_lt_dec (S ts) b).
    + eapply H; eauto.
    + eapply H0; eauto.
  Qed.

  Lemma no_msgs_full
        pred from to mem1 mem2
        (TO: to <= length mem1)
        (NOMSGS: no_msgs from to pred mem1):
    no_msgs from to pred (mem1 ++ mem2).
  Proof.
    ii. eapply NOMSGS; eauto.
    apply nth_error_app_inv in MSG. des; subst; ss. lia.
  Qed.

  Lemma no_msgs_weaken
        a b c pred mem1 mem2
        (BC: b <= c)
        (NOMSGS: no_msgs a c pred (mem1 ++ mem2)):
    no_msgs a b pred mem1.
  Proof.
    ii. eapply NOMSGS; eauto.
    - lia.
    - rewrite nth_error_app1; ss. apply nth_error_Some. congr.
  Qed.

  Lemma ge_no_msgs
        ts1 ts2 pred mem
        (GE: ts2 <= ts1):
    no_msgs ts1 ts2 pred mem.
  Proof.
    ii. lia.
  Qed.

  Lemma latest_uniq
        ts1 ts2 ts loc mem val1 val2
        (TS1: ts1 <= ts)
        (TS2: ts2 <= ts)
        (LATEST1: latest loc ts1 ts mem)
        (LATEST2: latest loc ts2 ts mem)
        (MSG1: read loc ts1 mem = Some val1)
        (MSG2: read loc ts2 mem = Some val2):
    ts1 = ts2.
  Proof.
    destruct (Nat.lt_trichotomy ts1 ts2); des; ss.
    - destruct ts2; [lia|]. exfalso.
      revert MSG2. unfold read. s. destruct (nth_error mem ts2) eqn:NTH; ss.
      condtac; ss. inversion e. subst. i. inv MSG2.
      eapply LATEST1; eauto.
    - destruct ts1; [lia|]. exfalso.
      revert MSG1. unfold read. s. destruct (nth_error mem ts1) eqn:NTH; ss.
      condtac; ss. inversion e. subst. i. inv MSG1.
      eapply LATEST2; eauto.
  Qed.
End Memory.

Module View.
Section View.
  Context `{A: Type, _: orderC A eq}.

  Inductive t := mk {
    ts: Time.t;
    annot: A;
  }.
  Hint Constructors t.

  Inductive _le (a b:t): Prop :=
  | _le_intro
      (TS: le a.(ts) b.(ts))
      (ANNOT: le a.(annot) b.(annot))
  .

  Definition _join (a b:t): t :=
    mk (join a.(ts) b.(ts)) (join a.(annot) b.(annot)).

  Definition _bot: t := mk bot bot.

  Global Program Instance preorder: PreOrder _le.
  Next Obligation. ii. econs; refl. Qed.
  Next Obligation. ii. inv H1. inv H2. econs; etrans; eauto. Qed.

  Global Program Instance partialorder: PartialOrder eq _le.
  Next Obligation.
    ii. econs.
    - i. subst. econs; refl.
    - i. destruct x, x0. inv H1. inv H2. inv H3. ss. f_equal.
      + intuition.
      + antisym; ss.
  Qed.

  Global Program Instance order:
    @orderC
      t
      eq
      _le
      _join
      _bot
      _ _ _.
  Next Obligation.
    unfold _join. destruct a, b; ss. econs; s; apply join_l.
  Qed.
  Next Obligation.
    unfold _join. destruct a, b; ss. econs; s; apply join_r.
  Qed.
  Next Obligation.
    unfold _join. destruct a, b, c; ss. f_equal; apply join_assoc.
  Qed.
  Next Obligation.
    unfold _join. destruct a, b; ss. f_equal; apply join_comm.
  Qed.
  Next Obligation.
    inv AC. inv BC. econs; s; apply join_spec; ss.
  Qed.
  Next Obligation.
    econs; apply bot_spec.
  Qed.

  Lemma ts_join a b:
    (join a b).(View.ts) = join (a.(View.ts)) (b.(View.ts)).
  Proof. destruct a, b; ss. Qed.

  Lemma ts_ifc a b:
    (ifc a b).(View.ts) = ifc a b.(View.ts).
  Proof. destruct a; ss. Qed.

  Lemma ts_bot:
    bot.(View.ts) = bot.
  Proof. ss. Qed.

  Lemma eq_time_eq
        (v1 v2:t)
        (EQ: v1 = v2):
    v1.(ts) = v2.(ts).
  Proof.
    subst. ss.
  Qed.
End View.
End View.

Module FwdItem.
Section FwdItem.
  Context `{A: Type, _: orderC A eq}.

  Inductive t := mk {
    ts: Time.t;
    view: View.t (A:=A);
    ex: bool;
  }.
  Hint Constructors t.

  Definition init: t := mk bot bot false.

  Definition read_view (fwd:t) (tsx:Time.t) (ord:OrdR.t): View.t (A:=A) :=
    if andb (fwd.(ts) == tsx) (negb (andb fwd.(ex) (orb (arch == riscv) (OrdR.ge ord OrdR.acquire_pc))))
    then fwd.(view)
    else View.mk tsx bot.
End FwdItem.
End FwdItem.

Module Exbank.
Section Exbank.
  Context `{A: Type, _: orderC A eq}.

  Inductive t := mk {
    loc: Loc.t;
    ts: Time.t;
    view: View.t (A:=A);
  }.
  Hint Constructors t.
End Exbank.
End Exbank.

Section Eqts.
  Context `{A: Type, B: Type, _: orderC A eq, _: orderC B eq}.

  Inductive eqts_view (v1: View.t (A:=A)) (v2: View.t (A:=B)): Prop :=
  | eqts_view_intro
      (TS: v1.(View.ts) = v2.(View.ts))
  .
  Hint Constructors eqts_view.

  Inductive eqts_fwd (fwd1:FwdItem.t (A:=A)) (fwd2:FwdItem.t (A:=B)): Prop :=
  | eqts_fwd_intro
      (TS: fwd1.(FwdItem.ts) = fwd2.(FwdItem.ts))
      (VIEW: eqts_view fwd1.(FwdItem.view) fwd2.(FwdItem.view))
      (EX: fwd1.(FwdItem.ex) = fwd2.(FwdItem.ex))
  .
  Hint Constructors eqts_fwd.

  Inductive eqts_val (v1:ValA.t (A:=View.t (A:=A))) (v2:ValA.t (A:=View.t (A:=B))): Prop :=
  | eqts_val_intro
      (VAL: v1.(ValA.val) = v2.(ValA.val))
      (VIEW: eqts_view v1.(ValA.annot) v2.(ValA.annot))
  .
  Hint Constructors eqts_val.

  Inductive eqts_event: forall (e1:Event.t (A:=View.t (A:=A))) (e2:Event.t (A:=View.t (A:=B))), Prop :=
  | eqts_event_internal:
      eqts_event Event.internal Event.internal
  | eqts_event_read
      ex ord vloc1 vloc2 res1 res2
      (VLOC: eqts_val vloc1 vloc2)
      (RES: eqts_val res1 res2):
      eqts_event (Event.read ex ord vloc1 res1) (Event.read ex ord vloc2 res2)
  | eqts_event_write
      ex ord vloc1 vloc2 vval1 vval2 res1 res2
      (VLOC: eqts_val vloc1 vloc2)
      (VVAL: eqts_val vval1 vval2)
      (RES: eqts_val res1 res2):
      eqts_event (Event.write ex ord vloc1 vval1 res1) (Event.write ex ord vloc2 vval2 res2)
  | eqts_event_barrier
      b:
      eqts_event (Event.barrier b) (Event.barrier b)
  | eqts_event_control
      ctrl1 ctrl2
      (CTRL: eqts_view ctrl1 ctrl2):
      eqts_event (Event.control ctrl1) (Event.control ctrl2)
  .
  Hint Constructors eqts_event.
End Eqts.

Section EqtsEquiv.
  Context `{A: Type, _: orderC A eq}.

  Global Program Instance eqts_view_equiv: Equivalence (@eqts_view A A).
  Next Obligation. econs. ss. Qed.
  Next Obligation. econs. inv H1. ss. Qed.
  Next Obligation. econs. inv H1. inv H2. etrans; eauto. Qed.

  Global Program Instance eqts_fwd_equiv: Equivalence (@eqts_fwd A A).
  Next Obligation. econs; ss. Qed.
  Next Obligation. ii. destruct x, y. inv H1. ss. subst. econs; ss. symmetry. ss. Qed.
  Next Obligation. ii. destruct x, y, z. inv H1. inv H2. ss. subst. econs; ss. etrans; eauto. Qed.

  Global Program Instance eqts_val_equiv: Equivalence eqts_val.
  Next Obligation. econs; ss. Qed.
  Next Obligation. ii. destruct x, y. inv H1. ss. subst. econs; ss. symmetry. ss. Qed.
  Next Obligation. ii. destruct x, y, z. inv H1. inv H2. ss. subst. econs; ss. etrans; eauto. Qed.

  Global Program Instance eqts_event_equiv: Equivalence eqts_event.
  Next Obligation. ii. destruct x; econs; ss. Qed.
  Next Obligation.
    ii. inv H1; econs; ss.
    all: symmetry; ss.
  Qed.
  Next Obligation.
    ii. inv H1; inv H2; econs; ss.
    all: etrans; eauto.
  Qed.
End EqtsEquiv.

Module Promises.
  Definition t := Id.t -> bool.

  Definition id_of_time (ts:Time.t): option positive :=
    option_map Pos.of_succ_nat (Time.pred_opt ts).

  Lemma id_of_time_inj ts ts'
        (EQ: id_of_time ts = id_of_time ts'):
    ts = ts'.
  Proof.
    revert EQ. unfold id_of_time, Time.pred_opt.
    destruct ts, ts'; ss. i. inv EQ.
    f_equal. apply SuccNat2Pos.inj. ss.
  Qed.

  Lemma id_of_time_le ts ts' p p'
        (P: id_of_time ts = Some p)
        (P': id_of_time ts' = Some p')
        (LE: (p <= p')%positive):
    ts <= ts'.
  Proof.
    revert P P' LE. unfold id_of_time, Time.pred_opt.
    destruct ts, ts'; ss. i. inv P. inv P'. lia.
  Qed.

  Lemma id_of_time_lt ts ts' p p'
        (P: id_of_time ts = Some p)
        (P': id_of_time ts' = Some p')
        (LE: (p < p')%positive):
    ts < ts'.
  Proof.
    revert P P' LE. unfold id_of_time, Time.pred_opt.
    destruct ts, ts'; ss. i. inv P. inv P'. lia.
  Qed.

  Definition lookup (ts:Time.t) (promises:t): bool :=
    match id_of_time ts with
    | None => false
    | Some ts => promises ts
    end.

  Definition set (ts:Time.t) (promises:t): t :=
    match id_of_time ts with
    | None => promises
    | Some ts => fun_add ts true promises
    end.

  Lemma set_o ts' ts promises:
    lookup ts' (set ts promises) =
    if ts' == ts
    then ts' <> 0
    else lookup ts' promises.
  Proof.
    unfold lookup, set.
    destruct (id_of_time ts') eqn:X', (id_of_time ts) eqn:X, (equiv_dec ts' ts); ss;
      destruct ts, ts'; ss;
      try rewrite fun_add_spec in *.
    - inv e. rewrite X in X'. inv X'. condtac; ss. congr.
    - condtac; ss. inversion e. subst.
      rewrite <- X' in X. apply id_of_time_inj in X. inv X. intuition.
  Qed.

  Definition unset (ts:Time.t) (promises:t): t :=
    match id_of_time ts with
    | None => promises
    | Some ts => fun_add ts false promises
    end.

  Lemma unset_o ts' ts promises:
    lookup ts' (unset ts promises) =
    if ts' == ts
    then false
    else lookup ts' promises.
  Proof.
    unfold lookup, unset.
    destruct (id_of_time ts') eqn:X', (id_of_time ts) eqn:X, (equiv_dec ts' ts); ss;
      destruct ts, ts'; ss;
      try rewrite fun_add_spec in *.
    - inv e. rewrite X in X'. inv X'. condtac; intuition.
    - condtac; ss. inversion e. subst.
      rewrite <- X' in X. apply id_of_time_inj in X. inv X. intuition.
  Qed.

  Definition clear_below (ts:Time.t) (promises:t): t :=
    match id_of_time ts with
    | None => promises
    | Some ts => fun i =>
                  if Pos.leb i ts
                  then false
                  else promises i
    end.

  Lemma clear_below_o ts' ts promises:
    lookup ts' (clear_below ts promises) = lookup ts' promises && Time.ltb ts ts'.
  Proof.
    unfold lookup, clear_below.
    destruct (id_of_time ts') eqn:X', (id_of_time ts) eqn:X; destruct ts, ts'; ss.
    - destruct (Pos.leb_spec0 p p0); ss.
      + exploit id_of_time_le; try exact l; eauto.
        destruct (promises p), (S ts <? S ts') eqn:CMP; ss.
        apply Time.ltb_lt in CMP. lia.
      + assert ((p0 < p)%positive) by lia.
        exploit id_of_time_lt; try exact H; eauto.
        destruct (promises p), (S ts <? S ts') eqn:CMP; ss.
        apply Time.ltb_ge in CMP. lia.
    - destruct (promises p); ss.
  Qed.

  Lemma set_unset a b promises
        (DIFF: a <> b):
    set a (unset b promises) = unset b (set a promises).
  Proof.
    funext. i. unfold set, unset.
    destruct a, b; ss.
    rewrite ? fun_add_spec. repeat condtac; ss.
    inversion e. inversion e0. subst.
    apply SuccNat2Pos.inj in H0. congr.
  Qed.

  Lemma lookup_bot view:
    lookup view bot = false.
  Proof.
    unfold lookup. destruct (id_of_time view); ss.
  Qed.

  Lemma ext p1 p2
        (EQ: forall i, lookup i p1 = lookup i p2):
    p1 = p2.
  Proof.
    funext. i. specialize (EQ (Pos.to_nat x)).
    unfold lookup, id_of_time in *.
    destruct (Id.eq_dec 1 x).
    { subst. ss. }
    exploit (Pos2Nat.inj_pred x); [lia|].
    destruct (Pos.to_nat x) eqn:NAT; ss.
    - destruct x; ss. destruct x; ss.
    - i. subst. rewrite Pos2SuccNat.id_succ in *.
      generalize (Pos.succ_pred_or x). i. des; [congr|].
      rewrite H in *. ss.
  Qed.
End Promises.

Module Local.
Section Local.
  Context `{A: Type, _: orderC A eq}.

  Inductive t := mk {
    coh: Loc.t -> View.t (A:=A);
    vrn: View.t (A:=A);
    vwn: View.t (A:=A);
    vro: View.t (A:=A);
    vwo: View.t (A:=A);
    vcap: View.t (A:=A);
    vrel: View.t (A:=A);
    fwdbank: Loc.t -> (FwdItem.t (A:=A));
    exbank: option (Exbank.t (A:=A));
    promises: Promises.t;
  }.
  Hint Constructors t.

  Definition init: t := mk bot bot bot bot bot bot bot (fun _ => FwdItem.init) None bot.

  Definition init_with_promises (promises: Promises.t): Local.t :=
    mk bot bot bot bot bot bot bot (fun _ => FwdItem.init) None promises.

  Inductive promise (loc:Loc.t) (val:Val.t) (ts:Time.t) (tid:Id.t) (lc1:t) (mem1:Memory.t) (lc2:t) (mem2:Memory.t): Prop :=
  | promise_intro
      (LC2: lc2 =
            mk
              lc1.(coh)
              lc1.(vrn)
              lc1.(vwn)
              lc1.(vro)
              lc1.(vwo)
              lc1.(vcap)
              lc1.(vrel)
              lc1.(fwdbank)
              lc1.(exbank)
              (Promises.set ts lc1.(promises)))
      (MEM2: Memory.append (Msg.mk loc val tid) mem1 = (ts, mem2))
  .
  Hint Constructors promise.

  Inductive control (ctrl:View.t) (lc1 lc2:t): Prop :=
  | control_intro
      (LC2: lc2 =
            mk
              lc1.(coh)
              lc1.(vrn)
              lc1.(vwn)
              lc1.(vro)
              lc1.(vwo)
              (join lc1.(vcap) ctrl)
              lc1.(vrel)
              lc1.(fwdbank)
              lc1.(exbank)
              lc1.(promises))
  .
  Hint Constructors control.

  Inductive read (ex:bool) (ord:OrdR.t) (vloc res:ValA.t (A:=View.t (A:=A))) (ts:Time.t) (lc1:t) (mem1: Memory.t) (lc2:t): Prop :=
  | read_intro
      loc val view
      view_pre view_msg view_post
      (LOC: loc = vloc.(ValA.val))
      (VIEW: view = vloc.(ValA.annot))
      (VIEW_PRE: view_pre = joins [view; lc1.(vrn); (ifc (OrdR.ge ord OrdR.acquire) lc1.(vrel))])
      (COH: Memory.latest loc ts (lc1.(coh) loc).(View.ts) mem1)
      (LATEST: Memory.latest loc ts view_pre.(View.ts) mem1)
      (MSG: Memory.read loc ts mem1 = Some val)
      (VIEW_MSG: view_msg = FwdItem.read_view (lc1.(fwdbank) loc) ts ord)
      (VIEW_POST: view_post = join view_pre view_msg)
      (RES: res = ValA.mk _ val view_post)
      (LC2: lc2 =
            mk
              (fun_add loc (join (lc1.(coh) loc) view_post) lc1.(coh))
              (join lc1.(vrn) (ifc (OrdR.ge ord OrdR.acquire_pc) view_post))
              (join lc1.(vwn) (ifc (OrdR.ge ord OrdR.acquire_pc) view_post))
              (join lc1.(vro) view_post)
              lc1.(vwo)
              (join lc1.(vcap) view)
              lc1.(vrel)
              lc1.(fwdbank)
              (if ex then Some (Exbank.mk loc ts view_post) else lc1.(exbank))
              lc1.(promises))
  .
  Hint Constructors read.

  Inductive writable (ex:bool) (ord:OrdW.t) (vloc vval:ValA.t (A:=View.t (A:=A))) (tid:Id.t) (lc1:t) (mem1: Memory.t) (ts:Time.t) (view_pre:View.t (A:=A)): Prop :=
  | writable_intro
      loc val
      view_loc view_val
      (LOC: loc = vloc.(ValA.val))
      (VIEW_LOC: view_loc = vloc.(ValA.annot))
      (VAL: val = vval.(ValA.val))
      (VIEW_VAL: view_val = vval.(ValA.annot))
      (VIEW_PRE: view_pre = joins [
                                view_loc; view_val; lc1.(vcap); lc1.(vwn);
                                ifc (OrdW.ge ord OrdW.release_pc) lc1.(vro);
                                ifc (OrdW.ge ord OrdW.release_pc) lc1.(vwo);
                                ifc (ex && (arch == riscv))
                                    (match lc1.(exbank) with
                                     | Some exbank => exbank.(Exbank.view)
                                     | None => bot
                                     end)
                             ])
      (COH: lt (lc1.(coh) loc).(View.ts) ts)
      (EXT: lt view_pre.(View.ts) ts)
      (EX: ex -> exists eb,
           <<TSX: lc1.(exbank) = Some eb>> /\
           <<EX: eb.(Exbank.loc) = loc -> Memory.exclusive tid loc eb.(Exbank.ts) ts mem1>>)
  .
  Hint Constructors writable.

  Inductive fulfill (ex:bool) (ord:OrdW.t) (vloc vval res:ValA.t (A:=View.t (A:=A))) (ts:Time.t) (tid:Id.t) (view_pre:View.t (A:=A)) (lc1:t) (mem1: Memory.t) (lc2:t): Prop :=
  | fulfill_intro
      loc val
      view_loc view_val
      (LOC: loc = vloc.(ValA.val))
      (VIEW_LOC: view_loc = vloc.(ValA.annot))
      (VAL: val = vval.(ValA.val))
      (VIEW_VAL: view_val = vval.(ValA.annot))
      (WRITABLE: writable ex ord vloc vval tid lc1 mem1 ts view_pre)
      (MSG: Memory.get_msg ts mem1 = Some (Msg.mk loc val tid))
      (PROMISE: Promises.lookup ts lc1.(promises))
      (RES: res = ValA.mk _ 0 (View.mk (ifc (ex && (arch == riscv)) ts) view_pre.(View.annot)))
      (LC2: lc2 =
            mk
              (fun_add loc (View.mk ts bot) lc1.(coh))
              lc1.(vrn)
              lc1.(vwn)
              lc1.(vro)
              (join lc1.(vwo) (View.mk ts bot))
              (join lc1.(vcap) view_loc)
              (join lc1.(vrel) (View.mk (ifc (OrdW.ge ord OrdW.release) ts) bot))
              (fun_add loc (FwdItem.mk ts (join view_loc view_val) ex) lc1.(fwdbank))
              (if ex then None else lc1.(exbank))
              (Promises.unset ts lc1.(promises)))
  .
  Hint Constructors fulfill.

  Inductive write_failure (ex:bool) (res: ValA.t (A:=View.t (A:=A))) (lc1:t) (lc2:t): Prop :=
  | write_failure_intro
      (EX: ex)
      (RES: res = ValA.mk _ 1 bot)
      (LC2: lc2 =
            mk
              lc1.(coh)
              lc1.(vrn)
              lc1.(vwn)
              lc1.(vro)
              lc1.(vwo)
              lc1.(vcap)
              lc1.(vrel)
              lc1.(fwdbank)
              None
              lc1.(promises))
  .
  Hint Constructors write_failure.

  Inductive isb (lc1 lc2:t): Prop :=
  | isb_intro
      (LC2: lc2 =
            mk
              lc1.(coh)
              (join lc1.(vrn) lc1.(vcap))
              lc1.(vwn)
              lc1.(vro)
              lc1.(vwo)
              lc1.(vcap)
              lc1.(vrel)
              lc1.(fwdbank)
              lc1.(exbank)
              lc1.(promises))
  .
  Hint Constructors isb.

  Inductive dmb (rr rw wr ww:bool) (lc1 lc2:t): Prop :=
  | dmb_intro
      (LC2: lc2 =
            mk
              lc1.(coh)
              (joins [lc1.(vrn); ifc rr lc1.(vro); ifc wr lc1.(vwo)])
              (joins [lc1.(vwn); ifc rw lc1.(vro); ifc ww lc1.(vwo)])
              lc1.(vro)
              lc1.(vwo)
              lc1.(vcap)
              lc1.(vrel)
              lc1.(fwdbank)
              lc1.(exbank)
              lc1.(promises))
  .
  Hint Constructors dmb.

  Inductive step (event:Event.t (A:=View.t (A:=A))) (tid:Id.t) (mem:Memory.t) (lc1 lc2:t): Prop :=
  | step_internal
      (EVENT: event = Event.internal)
      (LC: lc2 = lc1)
  | step_read
      ex ord vloc res ts
      (EVENT: event = Event.read ex ord vloc res)
      (STEP: read ex ord vloc res ts lc1 mem lc2)
  | step_fulfill
      ex ord vloc vval res ts view_pre
      (EVENT: event = Event.write ex ord vloc vval res)
      (STEP: fulfill ex ord vloc vval res ts tid view_pre lc1 mem lc2)
  | step_write_failure
      ex ord vloc vval res
      (EVENT: event = Event.write ex ord vloc vval res)
      (STEP: write_failure ex res lc1 lc2)
  | step_isb
      (EVENT: event = Event.barrier Barrier.isb)
      (STEP: isb lc1 lc2)
  | step_dmb
      rr rw wr ww
      (EVENT: event = Event.barrier (Barrier.dmb rr rw wr ww))
      (STEP: dmb rr rw wr ww lc1 lc2)
  | step_control
      ctrl
      (EVENT: event = Event.control ctrl)
      (LC: control ctrl lc1 lc2)
  .
  Hint Constructors step.

  Inductive wf_fwdbank (loc:Loc.t) (mem:Memory.t) (coh: Time.t) (fwd:FwdItem.t (A:=A)): Prop :=
  | wf_fwdbank_intro
      (TS: fwd.(FwdItem.ts) <= Memory.latest_ts loc coh mem)
      (VIEW: fwd.(FwdItem.view).(View.ts) <= fwd.(FwdItem.ts))
      (VAL: exists val, Memory.read loc fwd.(FwdItem.ts) mem = Some val)
  .

  Inductive wf_exbank (mem:Memory.t) (coh: Time.t) (eb:Exbank.t (A:=A)): Prop :=
  | wf_exbank_intro
      (TS: eb.(Exbank.ts) <= Memory.latest_ts eb.(Exbank.loc) coh mem)
      (VIEW: eb.(Exbank.view).(View.ts) <= coh)
      (VAL: exists val, Memory.read eb.(Exbank.loc) eb.(Exbank.ts) mem = Some val)
  .

  Inductive wf (tid:Id.t) (mem:Memory.t) (lc:t): Prop :=
  | wf_intro
      (COH: forall loc, (lc.(coh) loc).(View.ts) <= List.length mem)
      (VRN: lc.(vrn).(View.ts) <= List.length mem)
      (VWN: lc.(vwn).(View.ts) <= List.length mem)
      (VRO: lc.(vro).(View.ts) <= List.length mem)
      (VWO: lc.(vwo).(View.ts) <= List.length mem)
      (VCAP: lc.(vcap).(View.ts) <= List.length mem)
      (VREL: lc.(vrel).(View.ts) <= List.length mem)
      (FWDBANK: forall loc, wf_fwdbank loc mem (lc.(coh) loc).(View.ts) (lc.(fwdbank) loc))
      (EXBANK: forall eb, lc.(exbank) = Some eb -> wf_exbank mem (lc.(coh) eb.(Exbank.loc)).(View.ts) eb)
      (PROMISES: forall ts (IN: Promises.lookup ts lc.(promises)), ts <= List.length mem)
      (PROMISES: forall ts msg
                   (MSG: Memory.get_msg ts mem = Some msg)
                   (TID: msg.(Msg.tid) = tid)
                   (TS: (lc.(coh) msg.(Msg.loc)).(View.ts) < ts),
          Promises.lookup ts lc.(promises))
  .
  Hint Constructors wf.

  Lemma init_wf tid: wf tid Memory.empty init.
  Proof.
    econs; ss; i; try by apply bot_spec.
    - econs; ss. eexists. ss.
    - destruct ts; ss.
    - destruct ts; ss. destruct ts; ss.
  Qed.

  Lemma control_bot_inv
        lc1 lc2
        (LC: control bot lc1 lc2):
    lc2 = lc1.
  Proof.
    inv LC. destruct lc1. s. f_equal.
    rewrite bot_join; ss. apply View.order.
  Qed.

  (* Lemma fwd_read_view_coh_le *)
  (*       tid mem lc *)
  (*       (WF: wf tid mem lc) *)
  (*       loc ord ts *)
  (*       (COH: (lc.(coh) loc).(View.ts) <= ts): *)
  (*   ((lc.(Local.fwdbank) loc).(FwdItem.read_view) ts ord).(View.ts) <= ts. *)
  (* Proof. *)
  (*   inv WF. exploit FWDBANK; eauto. i. des. *)
  (*   unfold FwdItem.read_view. condtac; ss. etrans; eauto. etrans; eauto. *)
  (* Qed. *)

  Lemma fwd_view_le
        tid mem lc loc ts ord
        (WF: wf tid mem lc)
        (COH: Memory.latest loc ts (lc.(coh) loc).(View.ts) mem):
    (lc.(fwdbank) loc).(FwdItem.view).(View.ts) <=
    (FwdItem.read_view (lc.(fwdbank) loc) ts ord).(View.ts).
  Proof.
    unfold FwdItem.read_view. condtac; ss.
    inv WF. exploit FWDBANK. intro Y. inv Y.
    rewrite VIEW, TS. apply Memory.latest_latest_ts. ss.
  Qed.

  Lemma fwd_read_view_le
        tid mem lc loc ts ord
        (WF: wf tid mem lc)
        (COH: Memory.latest loc ts (lc.(coh) loc).(View.ts) mem):
    (FwdItem.read_view (lc.(fwdbank) loc) ts ord).(View.ts) <= ts.
  Proof.
    inv WF. destruct (FWDBANK loc). des.
    unfold FwdItem.read_view. condtac; ss.
    destruct (equiv_dec (FwdItem.ts (fwdbank lc loc)) ts); ss. inv e. ss.
  Qed.

  Lemma read_spec
        tid mem ex ord vloc res ts lc1 lc2
        (WF: Local.wf tid mem lc1)
        (READ: Local.read ex ord vloc res ts lc1 mem lc2):
    <<LATEST: Memory.latest vloc.(ValA.val) ts res.(ValA.annot).(View.ts) mem>> /\
    <<COH: ts = Memory.latest_ts vloc.(ValA.val) (lc2.(Local.coh) vloc.(ValA.val)).(View.ts) mem>>.
  Proof.
    inv READ. ss. rewrite fun_add_spec. condtac; [|congr]. splits.
    - apply Memory.latest_join; auto.
      apply Memory.ge_latest. eapply fwd_read_view_le; eauto.
    - unfold join. ss. apply le_antisym.
      + unfold FwdItem.read_view. des_ifs.
        * rewrite Bool.andb_true_iff in Heq. des.
          destruct (equiv_dec (FwdItem.ts (fwdbank lc1 (ValA.val vloc))) ts); ss.
          inv e0. inv WF. exploit FWDBANK. intro Y. inv Y.
          eapply Memory.latest_ts_read_le; eauto.
          rewrite TS, Memory.latest_latest_ts.
          { apply join_l. }
          { apply Memory.ge_latest. ss. }
        * eapply Memory.latest_ts_read_le; eauto.
          ss. repeat rewrite <- join_r. auto.
      + hexploit fwd_read_view_le; eauto. i.
        apply Memory.latest_latest_ts.
        apply Memory.latest_join; ss.
        apply Memory.latest_join; ss.
        apply Memory.ge_latest. etrans; eauto.
  Qed.

  Lemma interference_wf
        tid (lc:t) mem mem_interference
        (INTERFERENCE: Forall (fun msg => msg.(Msg.tid) <> tid) mem_interference)
        (WF: wf tid mem lc):
    wf tid (mem ++ mem_interference) lc.
  Proof.
    inv WF. econs; i.
    all: try rewrite app_length.
    all: try lia.
    - rewrite COH. lia.
    - destruct (FWDBANK loc). des. econs; esplits; eauto.
      + rewrite TS, Memory.latest_ts_append. ss.
      + apply Memory.read_mon. eauto.
    - exploit EXBANK; eauto. intro Y. inv Y. des. econs; esplits; eauto.
      + rewrite TS, Memory.latest_ts_append. ss.
      + apply Memory.read_mon. eauto.
    - exploit PROMISES; eauto. lia.
    - apply Memory.get_msg_app_inv in MSG. des.
      + eapply PROMISES0; eauto.
      + apply nth_error_In in MSG0. eapply Forall_forall in INTERFERENCE; eauto.
        subst. destruct (nequiv_dec (Msg.tid msg) (Msg.tid msg)); ss. congr.
  Qed.

  Lemma wf_promises_above
        tid mem (lc:t) ts
        (WF: wf tid mem lc)
        (ABOVE: length mem < ts):
    Promises.lookup ts lc.(promises) = false.
  Proof.
    destruct (Promises.lookup ts (Local.promises lc)) eqn:X; ss.
    inv WF. exploit PROMISES; eauto. clear -ABOVE. lia.
  Qed.

  Inductive le (lhs rhs:t): Prop :=
  | le_intro
      (COH: forall loc, Order.le (lhs.(coh) loc).(View.ts) (rhs.(coh) loc).(View.ts))
      (VRN: Order.le lhs.(vrn).(View.ts) rhs.(vrn).(View.ts))
      (VWN: Order.le lhs.(vwn).(View.ts) rhs.(vwn).(View.ts))
      (VRO: Order.le lhs.(vro).(View.ts) rhs.(vro).(View.ts))
      (VWO: Order.le lhs.(vwo).(View.ts) rhs.(vwo).(View.ts))
      (VCAP: Order.le lhs.(vcap).(View.ts) rhs.(vcap).(View.ts))
      (VREL: Order.le lhs.(vrel).(View.ts) rhs.(vrel).(View.ts))
  .

  Global Program Instance le_partial_order: PreOrder le.
  Next Obligation. econs; refl. Qed.
  Next Obligation. ii. inv H1. inv H2. econs; etrans; eauto. Qed.

  Lemma promise_incr
        loc val ts tid lc1 mem1 lc2 mem2
        (LC: promise loc val ts tid lc1 mem1 lc2 mem2):
    le lc1 lc2.
  Proof.
    inv LC. econs; ss; try refl; try apply join_l.
  Qed.

  Lemma control_incr
        ctrl lc1 lc2
        (LC: control ctrl lc1 lc2):
    le lc1 lc2.
  Proof.
    inv LC. econs; ss; try refl; try apply join_l.
  Qed.

  Lemma read_incr
        ex ord vloc res ts lc1 mem1 lc2
        (LC: read ex ord vloc res ts lc1 mem1 lc2):
    le lc1 lc2.
  Proof.
    inv LC. econs; ss; try refl; try apply join_l.
    i. rewrite fun_add_spec. condtac; try refl.
    clear X. inv e. s. apply join_l.
  Qed.

  Lemma fulfill_incr
        ex ord vloc vval res ts tid view_pre lc1 mem1 lc2
        (LC: fulfill ex ord vloc vval res ts tid view_pre lc1 mem1 lc2):
    le lc1 lc2.
  Proof.
    inv LC. econs; ss; try refl; try apply join_l.
    i. rewrite fun_add_spec. condtac; try refl.
    clear X. inv e. s.
    (* TODO: fulfill should update COH's taint, too. *)
    inv WRITABLE. unfold Order.le. clear -COH. lia.
  Qed.
  
  Lemma write_failure_incr
        ex res lc1 lc2
        (LC: write_failure ex res lc1 lc2):
    le lc1 lc2.
  Proof.
    inv LC. econs; ss; try refl; try apply join_l.
  Qed.

  Lemma isb_incr
        lc1 lc2
        (LC: isb lc1 lc2):
    le lc1 lc2.
  Proof.
    inv LC. econs; ss; try refl; try apply join_l.
  Qed.

  Lemma dmb_incr
        rr rw wr ww lc1 lc2
        (LC: dmb rr rw wr ww lc1 lc2):
    le lc1 lc2.
  Proof.
    inv LC. econs; ss; try refl; try apply join_l.
  Qed.

  Lemma step_incr
        e tid mem lc1 lc2
        (LC: step e tid mem lc1 lc2):
    le lc1 lc2.
  Proof.
    inv LC; try refl.
    - eapply read_incr. eauto.
    - eapply fulfill_incr. eauto.
    - eapply write_failure_incr. eauto.
    - eapply isb_incr. eauto.
    - eapply dmb_incr. eauto.
    - eapply control_incr. eauto.
  Qed.
End Local.
End Local.

Ltac viewtac :=
  repeat
    (try match goal with
         | [|- join _ _ <= _] => apply join_spec
         | [|- bot <= _] => apply bot_spec
         | [|- ifc ?c _ <= _] => destruct c; s

         | [|- Time.join _ _ <= _] => apply join_spec
         | [|- Time.bot <= _] => apply bot_spec

         | [|- context[View.ts (join _ _)]] => rewrite View.ts_join
         | [|- context[View.ts bot]] => rewrite View.ts_bot
         | [|- context[View.ts (ifc _ _)]] => rewrite View.ts_ifc
         end;
     ss; eauto).

Module ExecUnit.
Section ExecUnit.
  Context `{A: Type, _: orderC A eq}.

  Inductive t := mk {
    state: State.t (A:=View.t (A:=A));
    local: Local.t (A:=A);
    mem: Memory.t;
  }.
  Hint Constructors t.

  Inductive state_step0 (tid:Id.t) (e1 e2:Event.t (A:=View.t (A:=A))) (eu1 eu2:t): Prop :=
  | state_step0_intro
      (STATE: State.step e1 eu1.(state) eu2.(state))
      (LOCAL: Local.step e2 tid eu1.(mem) eu1.(local) eu2.(local))
      (MEM: eu2.(mem) = eu1.(mem))
  .
  Hint Constructors state_step0.

  Inductive state_step (tid:Id.t) (eu1 eu2:t): Prop :=
  | state_step_intro
      e
      (STEP: state_step0 tid e e eu1 eu2)
  .
  Hint Constructors state_step.

  Inductive promise_step (tid:Id.t) (eu1 eu2:t): Prop :=
  | promise_step_intro
      loc val ts
      (STATE: eu1.(state) = eu2.(state))
      (LOCAL: Local.promise loc val ts tid eu1.(local) eu1.(mem) eu2.(local) eu2.(mem))
  .
  Hint Constructors promise_step.

  Inductive step (tid:Id.t) (eu1 eu2:t): Prop :=
  | step_state (STEP: state_step tid eu1 eu2)
  | step_promise (STEP: promise_step tid eu1 eu2)
  .
  Hint Constructors step.

  Inductive rmap_wf (mem:Memory.t) (rmap:RMap.t (A:=View.t (A:=A))): Prop :=
  | rmap_wf_intro
      (RMAP: forall r, (RMap.find r rmap).(ValA.annot).(View.ts) <= List.length mem)
  .
  Hint Constructors rmap_wf.

  Inductive wf (tid:Id.t) (eu:t): Prop :=
  | wf_intro
      (STATE: rmap_wf eu.(mem) eu.(state).(State.rmap))
      (LOCAL: Local.wf tid eu.(mem) eu.(local))
  .
  Hint Constructors wf.

  Lemma rmap_add_wf
        mem rmap loc (val:ValA.t (A:=View.t (A:=A)))
        (WF: rmap_wf mem rmap)
        (VAL: val.(ValA.annot).(View.ts) <= List.length mem):
    rmap_wf mem (RMap.add loc val rmap).
  Proof.
    inv WF. econs. i. unfold RMap.find, RMap.add. rewrite IdMap.add_spec.
    condtac; viewtac.
  Qed.

  Lemma expr_wf
        mem rmap e
        (RMAP: rmap_wf mem rmap):
    (sem_expr rmap e).(ValA.annot).(View.ts) <= List.length mem.
  Proof.
    induction e; viewtac. apply RMAP.
  Qed.

  Lemma read_wf
        ts loc val mem
        (READ: Memory.read loc ts mem = Some val):
    ts <= List.length mem.
  Proof.
    revert READ. unfold Memory.read. destruct ts; [lia|]. s.
    destruct (nth_error mem ts) eqn:NTH; ss. condtac; ss.
    i. eapply List.nth_error_Some. congr.
  Qed.

  Lemma get_msg_wf
        ts msg mem
        (READ: Memory.get_msg ts mem = Some msg):
    ts <= List.length mem.
  Proof.
    revert READ. unfold Memory.get_msg. destruct ts; [lia|]. s.
    destruct (nth_error mem ts) eqn:NTH; ss. i. inv READ.
    eapply List.nth_error_Some. congr.
  Qed.

  Lemma state_step0_wf tid e1 e2 eu1 eu2
        (STEP: state_step0 tid e1 e2 eu1 eu2)
        (EVENT: eqts_event e1 e2)
        (WF: wf tid eu1):
    wf tid eu2.
  Proof.
    destruct eu1 as [state1 local1 mem1].
    destruct eu2 as [state2 local2 mem2].
    inv WF. inv STEP. ss. subst.

    assert (FWDVIEW: forall loc ts ord,
               Memory.latest loc ts (View.ts (Local.coh local1 loc)) mem1 ->
               ts <= length mem1 ->
               View.ts (FwdItem.read_view (Local.fwdbank local1 loc) ts ord) <= length mem1).
    { i. rewrite Local.fwd_read_view_le; eauto. }
    generalize LOCAL. intro WF_LOCAL1.
    inv STATE0; inv LOCAL0; inv EVENT; inv LOCAL; ss.
    - econs; ss.
      eauto using rmap_add_wf, expr_wf.
    - inv RES. inv VIEW. inv VLOC. inv VIEW.
      exploit Local.read_spec; eauto. intro READ_SPEC. guardH READ_SPEC.
      inv STEP. ss. subst.
      exploit FWDVIEW; eauto.
      { eapply read_wf. eauto. }
      i. econs; ss.
      + apply rmap_add_wf; viewtac.
        rewrite TS, <- TS0. viewtac.
        eauto using expr_wf.
      + econs; viewtac; eauto using expr_wf.
        all: try by rewrite <- TS0; eauto using expr_wf.
        * i. rewrite fun_add_spec. condtac; viewtac.
          rewrite <- TS0. eauto using expr_wf.
        * i. exploit FWDBANK; eauto. intro Y. inv Y. des.
          econs; eauto. rewrite TS1, fun_add_spec. condtac; ss. inversion e. subst.
          apply Memory.latest_ts_mon. apply join_l.
        * i. rewrite fun_add_spec in *. destruct ex0.
          { inv H1. ss. condtac; [|congr]. econs; eauto.
            - desH READ_SPEC. rewrite COH1 at 1. ss.
            - s. apply join_r.
          }
          { exploit EXBANK; eauto. intro Y. inv Y. des. econs; eauto.
            - rewrite TS1. apply Memory.latest_ts_mon.
              condtac; ss. inversion e. apply join_l.
            - rewrite VIEW. condtac; ss. inversion e. rewrite H3. apply join_l.
          }
        * i. eapply PROMISES0; eauto. eapply Time.le_lt_trans; [|by eauto].
          rewrite fun_add_spec. condtac; ss. inversion e. rewrite H2. apply join_l.
    - inv RES. inv VIEW. inv VVAL. inv VIEW. inv VLOC. inv VIEW.
      inv STEP. inv WRITABLE. econs; ss.
      + apply rmap_add_wf; viewtac.
        rewrite TS. unfold ifc. condtac; [|by apply bot_spec]. eapply get_msg_wf. eauto.
      + econs; viewtac; rewrite <- ? TS0, <- ? TS1; eauto using get_msg_wf, expr_wf.
        * i. rewrite fun_add_spec. condtac; viewtac.
        * i. rewrite ? fun_add_spec. condtac; viewtac.
          inversion e. subst.
          econs; viewtac; rewrite <- TS0, <- TS1 in *.
          { unfold Memory.get_msg in MSG. destruct ts; ss. rewrite MSG. condtac; ss. }
          { etrans; [|apply Nat.lt_le_incl; eauto]. rewrite <- join_l. ss. }
          { etrans; [|apply Nat.lt_le_incl; eauto]. rewrite <- join_r, <- join_l. ss. }
          { revert MSG. unfold Memory.read, Memory.get_msg.
            destruct ts; ss. i. rewrite MSG. ss. eexists. des_ifs.
          }
        * destruct ex0; ss. i. exploit EXBANK; eauto. intro Y. inv Y. des. econs; eauto.
          { rewrite TS2, fun_add_spec. condtac; ss. inversion e. rewrite H3.
            apply Memory.latest_ts_mon. apply Nat.le_lteq. left. ss.
          }
          { rewrite VIEW, fun_add_spec. condtac; ss. inversion e. rewrite H3. clear -COH0. lia. }
        * i. revert IN. rewrite Promises.unset_o. condtac; ss. eauto.
        * i. rewrite Promises.unset_o. rewrite fun_add_spec in TS2. condtac.
          { inversion e. subst. rewrite MSG in MSG0. destruct msg. inv MSG0. ss.
            revert TS2. condtac; ss; intuition.
          }
          { eapply PROMISES0; eauto. revert TS2. condtac; ss. i.
            inversion e. rewrite H2. rewrite COH0. ss.
          }
    - inv STEP. econs; ss. apply rmap_add_wf; viewtac.
      inv RES. inv VIEW. rewrite TS. s. apply bot_spec.
    - inv STEP. econs; ss. econs; viewtac.
    - inv STEP. econs; ss. econs; viewtac.
    - inv LC. econs; ss. econs; viewtac.
      inv CTRL. rewrite <- TS. eauto using expr_wf.
  Qed.

  Lemma state_step_wf tid eu1 eu2
        (STEP: state_step tid eu1 eu2)
        (WF: wf tid eu1):
    wf tid eu2.
  Proof.
    inv STEP. eapply state_step0_wf; eauto. refl.
  Qed.

  Lemma rmap_append_wf
        mem msg rmap
        (WF: rmap_wf mem rmap):
    rmap_wf (mem ++ [msg]) rmap.
  Proof.
    inv WF. econs. i. rewrite RMAP. rewrite List.app_length. lia.
  Qed.

  Lemma rmap_interference_wf
        mem rmap mem_interference
        (WF: rmap_wf mem rmap):
    rmap_wf (mem ++ mem_interference) rmap.
  Proof.
    inv WF. econs. i. rewrite RMAP, app_length. lia.
  Qed.

  Lemma promise_step_wf tid eu1 eu2
        (STEP: promise_step tid eu1 eu2)
        (WF: wf tid eu1):
    wf tid eu2.
  Proof.
    destruct eu1 as [state1 local1 mem1].
    destruct eu2 as [state2 local2 mem2].
    inv WF. inv STEP. ss. subst.
    inv LOCAL. inv LOCAL0. inv MEM2. econs; ss.
    - apply rmap_append_wf. ss.
    - econs; eauto.
      all: try rewrite List.app_length; s; try lia.
      + i. rewrite COH. lia.
      + i. destruct (FWDBANK loc0). des. econs; esplits; ss.
        * rewrite TS. apply Memory.latest_ts_append.
        * apply Memory.read_mon; eauto.
      + i. exploit EXBANK; eauto. intro Y. inv Y. des.
        econs; esplits; ss.
        * rewrite TS. apply Memory.latest_ts_append.
        * apply Memory.read_mon. eauto.
      + i. revert IN. rewrite Promises.set_o. condtac.
        * inversion e. i. inv IN. lia.
        * i. exploit PROMISES; eauto. lia.
      + i. rewrite Promises.set_o. apply Memory.get_msg_snoc_inv in MSG. des.
        * destruct ts; ss. condtac; ss.
          eapply PROMISES0; eauto.
        * subst. condtac; ss. congr.
  Qed.

  Lemma step_wf tid eu1 eu2
        (STEP: step tid eu1 eu2)
        (WF: wf tid eu1):
    wf tid eu2.
  Proof.
    inv STEP.
    - eapply state_step_wf; eauto.
    - eapply promise_step_wf; eauto.
  Qed.

  Inductive le (eu1 eu2:t): Prop :=
  | le_intro
      mem'
      (LC: Local.le eu1.(local) eu2.(local))
      (MEM: eu2.(mem) = eu1.(mem) ++ mem')
  .

  Global Program Instance le_partial_order: PreOrder le.
  Next Obligation.
    econs.
    - refl.
    - rewrite app_nil_r. ss.
  Qed.
  Next Obligation.
    ii. inv H1. inv H2. econs; etrans; eauto.
    rewrite MEM, app_assoc. eauto.
  Qed.

  Lemma state_step_incr tid eu1 eu2
        (STEP: state_step tid eu1 eu2):
    le eu1 eu2.
  Proof.
    inv STEP. inv STEP0. econs.
    - eapply Local.step_incr. eauto.
    - rewrite MEM, app_nil_r. ss.
  Qed.

  Lemma promise_step_incr tid eu1 eu2
        (STEP: promise_step tid eu1 eu2):
    le eu1 eu2.
  Proof.
    inv STEP. econs.
    - eapply Local.promise_incr. eauto.
    - inv LOCAL. inv MEM2. ss.
  Qed.

  Lemma step_incr tid eu1 eu2
        (STEP: step tid eu1 eu2):
    le eu1 eu2.
  Proof.
    inv STEP.
    - eapply state_step_incr. eauto.
    - eapply promise_step_incr. eauto.
  Qed.
End ExecUnit.
End ExecUnit.

Module Machine.
  Inductive t := mk {
    tpool: IdMap.t (State.t (A:=View.t (A:=unit)) * Local.t (A:=unit));
    mem: Memory.t;
  }.
  Hint Constructors t.

  Definition init (p:program): t :=
    mk
      (IdMap.map (fun stmts => (State.init stmts, Local.init)) p)
      Memory.empty.

  Inductive is_terminal (m:t): Prop :=
  | is_terminal_intro
      (TERMINAL:
         forall tid st lc
           (FIND: IdMap.find tid m.(tpool) = Some (st, lc)),
           State.is_terminal st /\ lc.(Local.promises) = bot)
  .
  Hint Constructors is_terminal.

  Inductive no_promise (m:t): Prop :=
  | no_promise_intro
      (PROMISES:
         forall tid st lc
           (FIND: IdMap.find tid m.(tpool) = Some (st, lc)),
           lc.(Local.promises) = bot)
  .
  Hint Constructors no_promise.

  Lemma is_terminal_no_promise
        m
        (TERMINAL: is_terminal m):
    no_promise m.
  Proof.
    econs. i. eapply TERMINAL. eauto.
  Qed.

  Inductive step (eustep: forall (tid:Id.t) (eu1 eu2:ExecUnit.t (A:=unit)), Prop) (m1 m2:t): Prop :=
  | step_intro
      tid st1 lc1 st2 lc2
      (FIND: IdMap.find tid m1.(tpool) = Some (st1, lc1))
      (STEP: eustep tid (ExecUnit.mk st1 lc1 m1.(mem)) (ExecUnit.mk st2 lc2 m2.(mem)))
      (TPOOL: m2.(tpool) = IdMap.add tid (st2, lc2) m1.(tpool))
  .
  Hint Constructors step.

  Lemma rtc_eu_step_step
        eustep tid m st1 lc1 mem1 st2 lc2 mem2
        (FIND: IdMap.find tid m.(tpool) = Some (st1, lc1))
        (MEM: m.(mem) = mem1)
        (EX: rtc (eustep tid)
                 (ExecUnit.mk st1 lc1 mem1)
                 (ExecUnit.mk st2 lc2 mem2)):
    rtc (step eustep)
        m
        (mk
           (IdMap.add tid (st2, lc2) m.(tpool))
           mem2).
  Proof.
    revert m FIND MEM.
    depind EX.
    { i. subst. destruct m. s. rewrite PositiveMapAdditionalFacts.gsident; ss. refl. }
    destruct y. i. subst. econs.
    - instantiate (1 := mk _ _). econs; ss; eauto.
    - exploit IHEX; eauto.
      + instantiate (1 := mk _ _). s.
        rewrite IdMap.add_spec. condtac; eauto. exfalso. apply c. ss.
      + ss.
      + s. rewrite (IdMap.add_add tid (st2, lc2)). eauto.
  Qed.

  Inductive wf (m:t): Prop :=
  | wf_intro
      (WF: forall tid st lc
             (FIND: IdMap.find tid m.(tpool) = Some (st, lc)),
          ExecUnit.wf tid (ExecUnit.mk st lc m.(mem)))
  .
  Hint Constructors wf.

  Lemma init_wf p:
    wf (init p).
  Proof.
    econs. i. ss.
    rewrite IdMap.map_spec in FIND. destruct (IdMap.find tid p); inv FIND.
    econs; ss.
    - econs. i. unfold RMap.find, RMap.init. rewrite IdMap.gempty. ss.
    - apply Local.init_wf.
  Qed.

  Lemma init_no_promise p:
    no_promise (init p).
  Proof.
    econs. s. i.
    revert FIND. rewrite IdMap.map_spec. destruct (IdMap.find tid p); ss. i. inv FIND.
    ss.
  Qed.

  Lemma step_state_step_wf
        m1 m2
        (STEP: step ExecUnit.state_step m1 m2)
        (WF: wf m1):
    wf m2.
  Proof.
    destruct m1 as [tpool1 mem1].
    destruct m2 as [tpool2 mem2].
    inv STEP. inv STEP0. inv WF. econs. ss. subst.
    i. revert FIND0. rewrite IdMap.add_spec. condtac.
    - inversion e0. i. inv FIND0.
      eapply ExecUnit.state_step_wf; eauto. econs; eauto.
    - inv STEP. ss. i. subst. exploit WF0; eauto.
  Qed.

  Lemma step_promise_step_wf
        m1 m2
        (STEP: step ExecUnit.promise_step m1 m2)
        (WF: wf m1):
    wf m2.
  Proof.
    destruct m1 as [tpool1 mem1].
    destruct m2 as [tpool2 mem2].
    inv STEP. inv STEP0. inv LOCAL. inv MEM2. inv WF. econs. ss. subst.
    i. revert FIND0. rewrite IdMap.add_spec. condtac.
    - inversion e. i. inv FIND0.
      eapply ExecUnit.promise_step_wf; eauto. econs; eauto. econs; eauto.
      + econs; eauto.
      + refl.
    - i. exploit WF0; eauto. i. inv x. ss. econs; ss.
      + apply ExecUnit.rmap_append_wf. ss.
      + inv LOCAL. econs; eauto.
        all: try rewrite List.app_length; s; try lia.
        * i. rewrite COH. lia.
        * i. destruct (FWDBANK loc0). des. econs; esplits; ss.
          { rewrite TS. apply Memory.latest_ts_append. }
          { apply Memory.read_mon; eauto. }
        * i. exploit EXBANK; eauto. intro Y. inv Y. des.
          econs; esplits; ss.
          { rewrite TS. apply Memory.latest_ts_append. }
          { apply Memory.read_mon. eauto. }
        * i. exploit PROMISES; eauto. lia.
        * i. apply Memory.get_msg_snoc_inv in MSG. des.
          { eapply PROMISES0; eauto. }
          { subst. ss. congr. }
  Qed.

  Lemma rtc_step_promise_step_wf
        m1 m2
        (STEP: rtc (step ExecUnit.promise_step) m1 m2)
        (WF: wf m1):
    wf m2.
  Proof.
    revert WF. induction STEP; ss. i. apply IHSTEP.
    eapply step_promise_step_wf; eauto.
  Qed.

  Lemma step_step_wf
        m1 m2
        (STEP: step ExecUnit.step m1 m2)
        (WF: wf m1):
    wf m2.
  Proof.
    inv STEP. inv STEP0.
    - eapply step_state_step_wf; eauto.
    - eapply step_promise_step_wf; eauto.
  Qed.

  Lemma rtc_step_step_wf
        m1 m2
        (STEP: rtc (step ExecUnit.step) m1 m2)
        (WF: wf m1):
    wf m2.
  Proof.
    revert WF. induction STEP; ss. i. apply IHSTEP.
    eapply step_step_wf; eauto.
  Qed.

  Lemma step_mon
        (eustep1 eustep2: _ -> _ -> _ -> Prop)
        (EUSTEP: forall tid m1 m2, eustep1 tid m1 m2 -> eustep2 tid m1 m2):
    forall m1 m2, step eustep1 m1 m2 -> step eustep2 m1 m2.
  Proof.
    i. inv H. econs; eauto.
  Qed.

  Lemma rtc_step_mon
        (eustep1 eustep2: _ -> _ -> _ -> Prop)
        (EUSTEP: forall tid m1 m2, eustep1 tid m1 m2 -> eustep2 tid m1 m2):
    forall m1 m2, rtc (step eustep1) m1 m2 -> rtc (step eustep2) m1 m2.
  Proof.
    i. induction H; eauto. econs; eauto. eapply step_mon; eauto.
  Qed.

  Inductive exec (p:program) (m:t): Prop :=
  | exec_intro
      (STEP: rtc (step ExecUnit.step) (init p) m)
      (NOPROMISE: no_promise m)
  .
  Hint Constructors exec.

  Inductive state_exec (m1 m2:t): Prop :=
  | state_exec_intro
      (TPOOL: IdMap.Forall2
                (fun tid sl1 sl2 =>
                   rtc (ExecUnit.state_step tid)
                       (ExecUnit.mk (fst sl1) (snd sl1) m1.(mem))
                       (ExecUnit.mk (fst sl2) (snd sl2) m1.(mem)))
                m1.(tpool) m2.(tpool))
      (MEM: m1.(mem) = m2.(mem))
  .

  Inductive pf_exec (p:program) (m:t): Prop :=
  | pf_exec_intro
      m1
      (STEP1: rtc (step ExecUnit.promise_step) (init p) m1)
      (STEP2: state_exec m1 m)
      (NOPROMISE: no_promise m)
  .
  Hint Constructors pf_exec.

  Inductive equiv (m1 m2:t): Prop :=
  | equiv_intro
      (TPOOL: IdMap.Equal m1.(tpool) m2.(tpool))
      (MEM: m1.(mem) = m2.(mem))
  .

  Lemma equiv_no_promise
        m1 m2
        (EQUIV: equiv m1 m2)
        (NOPROMISE: no_promise m1):
    no_promise m2.
  Proof.
    inv EQUIV. inv NOPROMISE. econs. i.
    specialize (TPOOL tid). rewrite FIND in TPOOL.
    eapply PROMISES. eauto.
  Qed.

  Lemma unlift_step_state_step
        m1 m2 tid st1 lc1
        (STEPS: rtc (step ExecUnit.state_step) m1 m2)
        (TPOOL: IdMap.find tid m1.(tpool) = Some (st1, lc1)):
    exists st2 lc2,
      <<TPOOL: IdMap.find tid m2.(tpool) = Some (st2, lc2)>> /\
      <<STEPS: rtc (ExecUnit.state_step tid)
                   (ExecUnit.mk st1 lc1 m1.(mem))
                   (ExecUnit.mk st2 lc2 m2.(mem))>>.
  Proof.
    revert st1 lc1 TPOOL. induction STEPS; eauto. i.
    destruct x as [tpool1 mem1].
    destruct y as [tpool2 mem2].
    destruct z as [tpool3 mem3].
    inv H. ss.
    assert (mem2 = mem1).
    { inv STEP. inv STEP0. ss. }
    subst. exploit IHSTEPS.
    { rewrite IdMap.add_spec, TPOOL.
      instantiate (1 := if equiv_dec tid tid0 then lc2 else lc1).
      instantiate (1 := if equiv_dec tid tid0 then st2 else st1).
      condtac; ss.
    }
    i. des.
    esplits; eauto. rewrite <- STEPS0. condtac; eauto.
    inversion e. subst. rewrite TPOOL in FIND. inv FIND. econs; eauto.
  Qed.

  Lemma step_get_msg_tpool
        p m ts msg
        (STEPS: rtc (step ExecUnit.step) (init p) m)
        (MSG: Memory.get_msg ts m.(mem) = Some msg):
    exists sl, IdMap.find msg.(Msg.tid) m.(tpool) = Some sl.
  Proof.
    apply clos_rt_rt1n_iff in STEPS.
    apply clos_rt_rtn1_iff in STEPS.
    revert ts msg MSG. induction STEPS; ss.
    { destruct ts; ss. destruct ts; ss. }
    destruct y as [tpool1 mem1].
    destruct z as [tpool2 mem2].
    ss. inv H. ss. i. inv STEP.
    - rewrite IdMap.add_spec. condtac; eauto.
      inv STEP0. inv STEP. ss. subst. eauto.
    - rewrite IdMap.add_spec. condtac; eauto.
      inv STEP0. ss. subst. inv LOCAL. inv MEM2.
      apply Memory.get_msg_snoc_inv in MSG. des; eauto. subst.
      ss. congr.
  Qed.

  Definition promises_from_mem
             (tid:Id.t) (mem: Memory.t): Promises.t.
  Proof.
    induction mem using list_rev_rect.
    - exact bot.
    - destruct x.
      apply (if tid0 == tid
             then Promises.set (S (List.length (List.rev mem0))) IHmem
             else IHmem).
  Defined.

  Lemma promises_from_mem_nil tid:
    promises_from_mem tid Memory.empty = bot.
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

  Lemma promises_from_mem_inv
        ts tid mem
        (LOOKUP: Promises.lookup (S ts) (promises_from_mem tid mem)):
    exists loc val, List.nth_error mem ts = Some (Msg.mk loc val tid).
  Proof.
    revert LOOKUP. induction mem using List.rev_ind.
    { rewrite promises_from_mem_nil, Promises.lookup_bot. ss. }
    rewrite promises_from_mem_snoc. condtac.
    { rewrite Promises.set_o. condtac.
      - inversion e. inversion e0. subst.
        rewrite List.nth_error_app2; [|lia].
        rewrite Nat.sub_diag. ss.
        destruct x. esplits; eauto.
      - i. exploit IHmem; eauto.  i. des.
        rewrite List.nth_error_app1; eauto.
        apply List.nth_error_Some. congr.
    }
    i. exploit IHmem; eauto.  i. des.
    rewrite List.nth_error_app1; eauto.
    apply List.nth_error_Some. congr.
  Qed.

  Lemma promises_from_mem_lookup
        mem ts loc val tid
        (GET: List.nth_error mem ts = Some (Msg.mk loc val tid)):
    Promises.lookup (S ts) (promises_from_mem tid mem).
  Proof.
    revert GET. induction mem using List.rev_ind.
    { i. apply List.nth_error_In in GET. inv GET. }
    rewrite promises_from_mem_snoc. condtac.
    - rewrite Promises.set_o. condtac.
      + inversion e. inversion e0. subst.
        rewrite List.nth_error_app2; [|lia].
        rewrite Nat.sub_diag. ss.
      + i. apply IHmem.
        erewrite <- List.nth_error_app1; eauto.
        assert (H: ts < List.length (mem0 ++ [x])).
        { rewrite <- List.nth_error_Some. ii. congr. }
        rewrite List.app_length in H.
        rewrite Nat.add_1_r in H. inv H; try lia.
        exfalso. apply c. ss.
    - i. apply IHmem.
      destruct (Nat.eq_dec ts (List.length mem0)) eqn:Heq.
      + inv Heq. rewrite List.nth_error_app2 in GET; try lia.
        rewrite Nat.sub_diag in GET. ss. inv GET. ss.
        exfalso. apply c. ss.
      + rewrite List.nth_error_app1 in GET; auto.
        assert (H: ts < List.length (mem0 ++ [x])).
        { rewrite <- List.nth_error_Some. ii. congr. }
        rewrite List.app_length in H.
        rewrite Nat.add_1_r in H. inv H; try lia; congr.
  Qed.

  Lemma promises_from_mem_spec
        ts tid mem:
    Promises.lookup (S ts) (promises_from_mem tid mem) <->
    exists loc val, List.nth_error mem ts = Some (Msg.mk loc val tid).
  Proof.
    induction mem using List.rev_ind.
    { econs.
      - rewrite promises_from_mem_nil, Promises.lookup_bot. ss.
      - i. des. destruct ts; ss.
    }
    rewrite promises_from_mem_snoc. econs.
    - condtac.
      + inversion e. subst. rewrite Promises.set_o. condtac.
        * inversion e0. subst. i.
          rewrite List.nth_error_app2, Nat.sub_diag; [|lia]. ss.
          destruct x. ss. eauto.
        * intro Y. apply IHmem in Y. des.
          esplits; eauto. apply nth_error_app_mon. eauto.
      + intro Y. apply IHmem in Y. des.
        esplits; eauto. apply nth_error_app_mon. eauto.
    - i. des. apply nth_error_snoc_inv in H. des; ss.
      { condtac; eauto. rewrite Promises.set_o. condtac; eauto. }
      subst. condtac; ss; [|congr]. rewrite Promises.set_o. condtac; [|congr]. ss.
  Qed.

  Definition init_with_promises (p:program) (mem:Memory.t): Machine.t :=
    Machine.mk
      (IdMap.mapi (fun tid stmts =>
                     (State.init stmts,
                      Local.init_with_promises (promises_from_mem tid mem)))
                  p)
      mem.

  Lemma pf_init_with_promises
        p promises
        (MEM: forall msg (MSG: List.In msg promises), IdMap.find msg.(Msg.tid) p <> None):
    exists m,
      <<STEP: rtc (Machine.step ExecUnit.promise_step) (Machine.init p) m>> /\
      <<TPOOL: IdMap.Equal m.(Machine.tpool) (init_with_promises p promises).(Machine.tpool)>> /\
      <<MEM: m.(Machine.mem) = promises>>.
  Proof.
    revert MEM. induction promises using List.rev_ind; i.
    { esplits; eauto. ii. s. rewrite IdMap.map_spec, IdMap.mapi_spec.
      destruct (IdMap.find y p); ss.
      unfold Local.init, Local.init_with_promises. repeat f_equal.
      rewrite promises_from_mem_nil. ss.
    }
    exploit IHpromises; eauto.
    { i. apply MEM. apply List.in_app_iff. intuition. }
    i. des. subst. destruct x.
    hexploit MEM.
    { apply List.in_app_iff. right. left. eauto. }
    match goal with
    | [|- context[(?f <> None) -> _]] => destruct f eqn:FIND
    end; ss.
    intro X. clear X.
    eexists (Machine.mk _ _). esplits.
    - etrans; [eauto|]. econs 2; [|refl].
      econs.
      + rewrite TPOOL, IdMap.mapi_spec, FIND. ss.
      + econs; ss.
      + ss.
    - s. ii. rewrite IdMap.add_spec. condtac; ss.
      + inversion e. subst. rewrite IdMap.mapi_spec, FIND. s.
        unfold Local.init_with_promises. repeat f_equal.
        rewrite promises_from_mem_snoc. condtac; ss.
      + rewrite TPOOL, ? IdMap.mapi_spec. destruct (IdMap.find y p); ss.
        unfold Local.init_with_promises. rewrite promises_from_mem_snoc. s.
        condtac; ss. congr.
    - ss.
  Qed.

  Lemma rtc_promise_step_spec
        p m
        (STEP: rtc (step ExecUnit.promise_step) (init p) m):
    IdMap.Equal m.(tpool) (init_with_promises p m.(mem)).(tpool).
  Proof.
    apply clos_rt_rt1n_iff in STEP.
    apply clos_rt_rtn1_iff in STEP.
    induction STEP.
    { s. ii. rewrite IdMap.map_spec, IdMap.mapi_spec.
      destruct (IdMap.find y p); ss. f_equal. f_equal.
      rewrite promises_from_mem_nil. ss.
    }
    destruct y as [tpool2 mem2].
    destruct z as [tpool3 mem3].
    ss. inv H. inv STEP0. inv LOCAL. ss. subst. inv MEM2.
    ii. generalize (IHSTEP y). rewrite IdMap.add_spec, ? IdMap.mapi_spec.
    rewrite promises_from_mem_snoc. s.
    repeat condtac; try congr.
    inversion e. subst. rewrite FIND. destruct (IdMap.find tid p); ss. i. inv H. ss.
  Qed.
End Machine.
