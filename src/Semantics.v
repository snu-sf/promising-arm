Require Import NArith.
Require Import PArith.
Require Import FMapPositive.
Require Import FSetPositive.

Require Import sflib.

Require Import Configuration.

Module Event.
  Inductive t: Type :=
  | read (ts:Time.t) (msg:Msg.t)
  | write (ts:Time.t) (msg:Msg.t)
  .
  Hint Constructors t.
End Event.

Module Ord.
  Inductive t: Type :=
  | pln
  | rlx
  | ra
  .
  Hint Constructors t.

  Definition le (a b:t): bool :=
    match a, b with
    | pln, _ => true
    | _, ra => true
    | rlx, rlx => true
    | _, _ => false
    end.
  Hint Unfold le.
End Ord.

Module LStep.
  Inductive read (ex:bool) (ord:Ord.t) (e:ValV.t) (lc1:Local.t) (mem1: Memory.t) (event:Event.t) (lc2:Local.t): Prop :=
  | read_intro
      loc view ts
      view1_ext view2_ext
      (E: e = ValV.mk loc view)
      (EXT1: view1_ext = Order.join e.(ValV.view) (Order.join lc1.(Local.vrp) (Order.bot_unless (Ord.le Ord.ra ord) lc1.(Local.vrel))))
      (COH: Order.le (lc1.(Local.coh) loc) ts)
      (LATEST: Order.le (Memory.latest mem1 loc view1_ext) ts)
      (EXT2: view2_ext = Order.join view1_ext Order.bot) (* TODO: readview(ti.fwd(l), t, mo) *)
      (LC2: lc2 =
            Local.mk
              lc1.(Local.rmap)
              (fun_add loc ts lc1.(Local.coh))
              (Order.join lc1.(Local.vrp) (Order.bot_unless (Ord.le Ord.ra ord) view2_ext))
              (Order.join lc1.(Local.vwp) (Order.bot_unless (Ord.le Ord.ra ord) view2_ext))
              (Order.join lc1.(Local.vrm) view2_ext)
              lc1.(Local.vwm)
              (Order.join lc1.(Local.vcap) view)
              lc1.(Local.vrel)
              lc1.(Local.fwd)
              (if ex then Some ts else lc1.(Local.ex))
              lc1.(Local.promises))
  .
  Hint Constructors read.
End LStep.
