Require Import Setoid PArith.
From hahn Require Import Hahn.
Require Import PromisingLib.
From Promising2 Require Import TView View Time Event Cell Thread Memory Configuration.
Require Import MemoryAux.

Definition closedness_preserved memory memory' :=
  forall view,
    Memory.closed_timemap view memory ->
    Memory.closed_timemap view memory'.

Lemma closedness_preserved_id memory :
  closedness_preserved memory memory.
Proof. by intros view. Qed.

Lemma closedness_preserved_add memory memory'
      loc from to msg
      (ADD : Memory.add memory loc from to msg memory'):
  closedness_preserved memory memory'.
Proof.
  intros view CP. red.
  intros loc'.
  erewrite Memory.add_o; eauto.
  destruct (loc_ts_eq_dec (loc', view loc') (loc, to)) as [[A B]|NEQ]; simpls.
  subst.
  exfalso.
  apply Memory.add_get0 in ADD. desf.
  specialize (CP loc). desf. rewrite ADD in CP. inv CP.
Qed.

Lemma closedness_preserved_split memory memory'
      loc from to to' msg msg'
      (SPLIT : Memory.split memory loc from to to' msg msg' memory'):
  closedness_preserved memory memory'.
Proof.
  intros view CP. red.
  intros loc'.
  set (MM:=SPLIT).
  apply Memory.split_get0 in MM. desf.
  erewrite Memory.split_o; eauto.
  destruct (loc_ts_eq_dec (loc', view loc') (loc, to)) as [[A B]|NEQ]; simpls; subst.
  { specialize (CP loc). desf. rewrite MM in CP. inv CP. }
  destruct (loc_ts_eq_dec (loc', view loc') (loc, to')) as [[A B]|NEQ']; simpls; desf.
  specialize (CP loc). desf. rewrite MM0 in CP. inv CP.
  eauto.
Qed.

Lemma tview_closedness_preserved_add tview memory memory'
      loc from to msg 
      (ADD : Memory.add memory loc from to msg memory')
      (MEM_CLOSE : memory_close tview memory) :
  memory_close tview memory'.
Proof.
  red; splits; ins.
  all: eapply closedness_preserved_add; eauto.
  all: by apply MEM_CLOSE.
Qed.

Lemma tview_closedness_preserved_split tview memory memory'
      loc from to to' val val' rel rel'
      (SPLIT : Memory.split memory loc from to to' val val' rel rel' memory')
      (MEM_CLOSE : memory_close tview memory) :
  memory_close tview memory'.
Proof.
  red; splits; ins.
  all: eapply closedness_preserved_split; eauto.
  all: by apply MEM_CLOSE.
Qed.
