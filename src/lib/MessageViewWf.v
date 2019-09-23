From hahn Require Import Hahn.
Require Import PromisingLib.
From Promising2 Require Import Memory View Time Cell TView.
Require Import MemoryAux.

Definition message_view_wf memory :=
  forall loc to from val released
         (GET : Memory.get loc to memory = 
                Some (from, Message.full val released)),
    View.opt_wf released.

Lemma message_view_wf_add
      memory loc from to msg memory'
      (REL_WF : message_view_wf memory)
      (PROM : Memory.add memory loc from to msg memory') :
  message_view_wf memory'.
Proof using.
  red. ins.
  erewrite Memory.add_o in GET; eauto.
  desf.
  2: by eapply REL_WF; eauto.
  simpls; desf.
  inv PROM. inv ADD. inv MSG_WF.
Qed.

Lemma message_view_wf_split
      memory loc from to to' msg msg' memory'
      (REL_WF : message_view_wf memory)
      (PROM : Memory.split memory loc from to to' msg msg' memory') :
  message_view_wf memory'.
Proof using.
  red. ins.
  erewrite Memory.split_o in GET; eauto.
  desf.
  3: by eapply REL_WF; eauto.
  all: simpls; desf.
  { inv PROM. inv SPLIT. inv MSG_WF. }
  inv PROM. inv SPLIT.
  eapply REL_WF.
  apply GET2.
Qed.

Lemma message_view_wf_lower
      memory loc from to msg msg' memory'
      (REL_WF : message_view_wf memory)
      (PROM : Memory.lower memory loc from to msg msg' memory') :
  message_view_wf memory'.
Proof using.
  red. ins.
  erewrite Memory.lower_o in GET; eauto.
  desf.
  2: by eapply REL_WF; eauto.
  simpls; desf.
  inv PROM. inv LOWER. inv MSG_WF.
Qed.

Lemma message_view_wf_remove
      memory loc from to msg memory'
      (REL_WF : message_view_wf memory)
      (PROM : Memory.remove memory loc from to msg memory') :
  message_view_wf memory'.
Proof using.
  red. ins.
  erewrite Memory.remove_o in GET; eauto.
  desf. simpls.
  eapply REL_WF; eauto.
Qed.

Lemma message_view_wf_op
      memory loc from to msg memory' kind
      (REL_WF : message_view_wf memory)
      (PROM : Memory.op memory loc from to msg memory' kind) :
  message_view_wf memory'.
Proof using.
  destruct PROM.
  { eapply message_view_wf_add; eauto. }
  { eapply message_view_wf_split; eauto. }
  { eapply message_view_wf_lower; eauto. }
  eapply message_view_wf_remove; eauto.
Qed.

Lemma message_view_wf_promise
      promises memory loc from to msg promises' memory' kind
      (REL_WF : message_view_wf memory)
      (PROM : Memory.promise promises memory loc from to
                             msg promises' memory' kind) :
  message_view_wf memory'.
Proof using.
  destruct PROM.
  { eapply message_view_wf_add; eauto. }
  { eapply message_view_wf_split; eauto. }
  { eapply message_view_wf_lower; eauto. }
  eapply message_view_wf_remove; eauto.
Qed.

Lemma message_view_wf_init : message_view_wf Memory.init.
Proof using.
  red. ins. apply memory_init_o in GET. desf.
  unfold Message.elt in *. desf.
Qed.

Lemma message_view_wf_future memory memory'
      (MVW    : message_view_wf memory)
      (FUTURE : Memory.future memory memory') :
  message_view_wf memory'.
Proof using.
  induction FUTURE; auto.
  apply IHFUTURE.
  destruct H.
  eapply message_view_wf_op; eauto.
Qed.

Lemma message_view_wf_future_init memory
      (FUTURE : Memory.future Memory.init memory) :
  message_view_wf memory.
Proof using.
  eapply message_view_wf_future; eauto.
  apply message_view_wf_init.
Qed.
