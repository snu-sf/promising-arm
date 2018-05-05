Require Import sflib.

Require Import EquivDec.
Require Import Order.
Require Import Lang.

Set Implicit Arguments.


Module Msg.
  Inductive t := mk {
    loc: Loc.t;
    val: Val.t;
    tid: Id.t;
  }.
  Hint Constructors t.
End Msg.

Module Memory.
  Definition t := list Msg.t.

  Definition get (ts:Time.t) (mem:t): option Msg.t :=
    List.nth_error mem ts.

  Definition latest (mem:t) (loc:Loc.t) (view:View.t): Time.t := Order.bot. (* TODO *)
End Memory.

Module FwdItem.
  Inductive t := mk {
    ts: Time.t;
    view: View.t;
    ex: bool;
  }.
  Hint Constructors t.

  Definition read_view (fwd:t) (tsx:Time.t) (o:ord): View.t :=
    if andb (fwd.(ts) == tsx) (orb (negb fwd.(ex)) (ord_le o pln))
    then fwd.(view)
    else tsx.

End FwdItem.

Definition fwdBankT := Loc.t -> option FwdItem.t.

Definition exBankT := option Time.t.

Definition cohT := Loc.t -> Time.t.

Definition promisesT := IdSet.t.

Module Local.
  Inductive t := mk {
    coh: cohT;
    vrp: View.t;
    vwp: View.t;
    vrm: View.t;
    vwm: View.t;
    vcap: View.t;
    vrel: View.t;
    fwd: fwdBankT;
    ex: exBankT;
    promises: promisesT;
  }.
  Hint Constructors t.
End Local.

Module Thread.
  Inductive t := mk {
    lang: stmt;
    local: Local.t;
  }.
  Hint Constructors t.
End Thread.

Definition threadPoolT := IdMap.t Thread.t.

Module Machine.
  Inductive t := mk {
    tpool: threadPoolT;
    mem: Memory.t;
  }.
  Hint Constructors t.
End Machine.
