From hahn Require Import Hahn.
Require Import PromisingLib.
From Promising2 Require Import Memory View Time Cell TView.
Require Import AuxRel2.

Definition memory_close tview memory :=
  ⟪ CLOSED_CUR :
    Memory.closed_timemap (View.rlx (TView.cur tview)) memory ⟫ /\
  ⟪ CLOSED_ACQ :
    Memory.closed_timemap (View.rlx (TView.acq tview)) memory ⟫ /\
  ⟪ CLOSED_REL :
    forall loc,
      Memory.closed_timemap (View.rlx (TView.rel tview loc)) memory ⟫.

Lemma memory_closed_timemap_le view memory memory'
      (MEM_LE : Memory.le memory memory')
      (MEM_CLOS : Memory.closed_timemap view memory) :
  Memory.closed_timemap view memory'.
Proof using.
  red; ins. specialize (MEM_CLOS loc). desf.
  apply MEM_LE in MEM_CLOS.
  eauto.
Qed.

Lemma memory_close_le tview memory memory'
      (MEM_LE : Memory.le memory memory')
      (MEM_CLOS : memory_close tview memory) :
  memory_close tview memory'.
Proof using.
  cdes MEM_CLOS.
  red; splits; ins.
  all: eapply memory_closed_timemap_le; eauto.
Qed.

Lemma loc_ts_eq_dec_eq {A} {a b : A} l ts :
  (if loc_ts_eq_dec (l, ts) (l, ts) then a else b) = a.
Proof using. edestruct loc_ts_eq_dec; desf. Qed.

Lemma loc_ts_eq_dec_neq {A} {a b : A} {l ts l' ts'}
      (NEQ: l <> l' \/ ts <> ts'):
  (if loc_ts_eq_dec (l, ts) (l', ts') then a else b) = b.
Proof using. edestruct loc_ts_eq_dec; desf. Qed.

Lemma memory_add_le memory memory' loc from to msg 
      (ADD : Memory.add memory loc from to msg memory'):
  Memory.le memory memory'.
Proof using.
  red. ins. erewrite Memory.add_o; eauto.
  destruct (loc_ts_eq_dec (loc0, to0) (loc, to)); [simpls; desf|done].
  exfalso. eapply Memory.add_get0 in ADD. desf.
  rewrite ADD in LHS. inv LHS.
Qed.

Lemma memory_remove_le memory memory' loc from to msg
      (ADD : Memory.remove memory loc from to msg memory'):
  Memory.le memory' memory.
Proof using.
  red. ins. erewrite Memory.remove_o in LHS; eauto.
    by destruct (loc_ts_eq_dec (loc0, to0) (loc, to)) in LHS; [desf|].
Qed.

Set Implicit Arguments.
Remove Hints plus_n_O.

Lemma memory_init_o loc to from msg
      (GET : Memory.get loc to Memory.init = Some (from, msg)) :
  to = Time.bot /\ from = Time.bot /\ msg = Message.elt.
Proof using.
  unfold Memory.init, Cell.init, Cell.Raw.init in *.
  unfold Memory.get, Cell.get in *; simpls.
  apply IdentMap.singleton_find_inv in GET.
  desf.
Qed.

Lemma inhabited_init : Memory.inhabited Memory.init.
Proof using. red. ins. Qed.

Lemma inhabited_future memory memory'
      (INHAB : Memory.inhabited memory)
      (FUTURE : Memory.future memory memory') :
  Memory.inhabited memory'.
Proof using.
  destruct FUTURE; auto.
  apply clos_rt1n_rt in FUTURE.
  apply clos_rt_rtn1 in FUTURE.
  induction FUTURE; auto.
  { destruct H.
    eapply Memory.op_inhabited; eauto. }
  destruct H0.
  eapply Memory.op_inhabited; eauto.
Qed.

Lemma inhabited_future_init memory (FUTURE : Memory.future Memory.init memory) :
  Memory.inhabited memory.
Proof using. eapply inhabited_future; eauto. apply inhabited_init. Qed.

Lemma inhabited_le memory memory' (LE : Memory.le memory memory')
      (INHAB : Memory.inhabited memory) :
  Memory.inhabited memory'.
Proof using. red. ins. apply LE. apply INHAB. Qed.

Definition ts_lt_or_bot memory :=
  forall loc to from msg (GET : Memory.get loc to memory = Some (from, msg)),
    (to = Time.bot /\ from = Time.bot) \/
    ⟪ FTLT : Time.lt from to ⟫.

Lemma ts_lt_or_bot_init : ts_lt_or_bot Memory.init.
Proof using. red. ins. apply memory_init_o in GET. left. desf. Qed.

Definition message_disjoint memory :=
  forall loc to1 from1 msg1 to2 from2 msg2
         (GET1 : Memory.get loc to1 memory = Some (from1, msg1))
         (GET2 : Memory.get loc to2 memory = Some (from2, msg2)),
    to1 = to2 \/ Interval.disjoint (from1, to1) (from2, to2).

Lemma message_disjoint_init : message_disjoint Memory.init.
Proof using.
  red. ins.
  apply memory_init_o in GET1.
  apply memory_init_o in GET2.
  desf. by left.
Qed.

Lemma ts_lt_or_bot_add loc from to msg memory memory_add
      (TLOB : ts_lt_or_bot memory)
      (ADD : Memory.add memory loc from to msg memory_add) :
  ts_lt_or_bot memory_add.
Proof using.
  red. ins.
  erewrite Memory.add_o in GET; eauto.
  desf; simpls; desf.
  { right. inv ADD. inv ADD0. }
  all: by eapply TLOB; eauto.
Qed.

Lemma message_disjoint_add loc from to msg memory memory_add
      (MD : message_disjoint memory)
      (ADD : Memory.add memory loc from to msg memory_add) :
  message_disjoint memory_add.
Proof using.
  red. ins.
  erewrite Memory.add_o in GET1; eauto.
  erewrite Memory.add_o in GET2; eauto.
  desf; simpls; desf.
  { by left. }
  { right. inv ADD. inv ADD0.
    symmetry.
    eapply DISJOINT; eauto. }
  { right. inv ADD. inv ADD0.
    eapply DISJOINT; eauto. }
  all: by eapply MD; eauto.
Qed.

Lemma ts_lt_or_bot_lower loc from to msg released' memory memory_lower
      (TLOB : ts_lt_or_bot memory)
      (LOWER : Memory.lower memory loc from to msg released' memory_lower) :
  ts_lt_or_bot memory_lower.
Proof using.
  red. ins.
  erewrite Memory.lower_o in GET; eauto.
  desf; simpls; desf.
  { right. inv LOWER. inv LOWER0. }
  all: by eapply TLOB; eauto.
Qed.

Lemma message_disjoint_lower loc from to msg released' memory memory_lower
      (MD : message_disjoint memory)
      (LOWER : Memory.lower memory loc from to msg released' memory_lower) :
  message_disjoint memory_lower.
Proof using.
  red. ins.
  erewrite Memory.lower_o in GET1; eauto.
  erewrite Memory.lower_o in GET2; eauto.
  desf; simpls; desf.
  { by left. }
  all: inv LOWER; inv LOWER0; eapply MD; eauto.
Qed.

Lemma ts_lt_or_bot_split loc from to to' msg msg' memory memory_split
      (TLOB : ts_lt_or_bot memory)
      (SPLIT : Memory.split memory loc from to to' msg msg' memory_split) :
  ts_lt_or_bot memory_split.
Proof using.
  red. ins.
  erewrite Memory.split_o in GET; eauto.
  desf; simpls; desf.
  1,2: by right; inv SPLIT; inv SPLIT0.
  all: eapply TLOB; eauto.
Qed.

Lemma ts_lt_or_bot_remove loc from to msg memory memory'
      (REMOVE : Memory.remove memory loc from to msg memory')
      (TLOB : ts_lt_or_bot memory) :
  ts_lt_or_bot memory'.
Proof using.
  red. ins.
  erewrite Memory.remove_o in GET; eauto.
  desf; simpls; desf.
  all: eapply TLOB; eauto.
Qed.

Lemma ts_lt_or_bot_op loc from to msg kind memory memory'
      (TLOB : ts_lt_or_bot memory)
      (OP : Memory.op memory loc from to msg memory' kind) :
  ts_lt_or_bot memory'.
Proof using.
  destruct OP.
  { eapply ts_lt_or_bot_add; eauto. }
  { eapply ts_lt_or_bot_split; eauto. }
  { eapply ts_lt_or_bot_lower; eauto. }
  eapply ts_lt_or_bot_remove; eauto.
Qed.

Lemma ts_lt_or_bot_future memory memory'
      (TLOB : ts_lt_or_bot memory)
      (FUTURE : Memory.future memory memory') :
  ts_lt_or_bot memory'.
Proof using.
  apply clos_rt1n_rt in FUTURE.
  apply clos_rt_rtn1 in FUTURE.
  induction FUTURE; auto.
  destruct H.
  eapply ts_lt_or_bot_op; eauto.
Qed.

Lemma ts_lt_or_bot_future_init memory
      (FUTURE : Memory.future Memory.init memory) :
  ts_lt_or_bot memory.
Proof using. eapply ts_lt_or_bot_future; eauto. apply ts_lt_or_bot_init. Qed.

Lemma message_disjoint_split loc from to to' msg msg' memory memory_split
      (MD : message_disjoint memory)
      (SPLIT : Memory.split memory loc from to to' msg msg' memory_split) :
  message_disjoint memory_split.
Proof using.
  assert (exists msg, Memory.get loc to' memory = Some (from, msg))
    as [msg'' GETI].
  { inv SPLIT. inv SPLIT0. eexists. apply GET2. }
  assert (Time.lt from to /\ Time.lt to to') as [LTF LTT].
  { inv SPLIT. inv SPLIT0. }
  assert (Interval.le (from, to) (from, to')) as ILE1.
  { constructor; simpls. reflexivity. apply Time.le_lteq. by left. }
  assert (Interval.le (to, to') (from, to')) as ILE2.
  { constructor; simpls. 2: reflexivity. apply Time.le_lteq. by left. }
  red. ins.
  erewrite Memory.split_o in GET1; eauto.
  erewrite Memory.split_o in GET2; eauto.
  desf; simpls; desf.
  all: try by left.
  all: try by (eapply MD in GET1; eapply GET1 in GET2; desf).
  all: right.
  { symmetry. apply Interval.disjoint_imm. }
  { symmetry.
    eapply Interval.le_disjoint; eauto.
    eapply MD in GET1. eapply GET1 in GETI.
    symmetry.
    desf. }
  { apply Interval.disjoint_imm. }
  { symmetry.
    eapply Interval.le_disjoint; eauto.
    eapply MD in GET1. eapply GET1 in GETI.
    symmetry.
    desf. }
  all: eapply Interval.le_disjoint; eauto.
  all: eapply MD in GET2; eapply GET2 in GETI.
  all: symmetry.
  all: desf.
Qed.

Lemma message_disjoint_remove loc from to msg memory memory'
      (MD : message_disjoint memory)
      (SPLIT : Memory.remove memory loc from to msg memory') :
  message_disjoint memory'.
Proof using.
  red. ins.
  erewrite Memory.remove_o in GET1; eauto.
  erewrite Memory.remove_o in GET2; eauto.
  desf; simpls; desf.
  all: by eapply MD; eauto.
Qed.

Lemma message_disjoint_op loc from to msg memory memory' kind
      (MD : message_disjoint memory)
      (OP : Memory.op memory loc from to msg memory' kind) :
  message_disjoint memory'.
Proof using.
  destruct OP.
  { eapply message_disjoint_add; eauto. }
  { eapply message_disjoint_split; eauto. }
  { eapply message_disjoint_lower; eauto. }
  eapply message_disjoint_remove; eauto.
Qed.

Lemma message_disjoint_future memory memory'
      (TLOB : message_disjoint memory)
      (FUTURE : Memory.future memory memory') :
  message_disjoint memory'.
Proof using.
  apply clos_rt1n_rt in FUTURE.
  apply clos_rt_rtn1 in FUTURE.
  induction FUTURE; auto.
  destruct H.
  eapply message_disjoint_op; eauto.
Qed.

Lemma message_disjoint_future_init memory
      (FUTURE : Memory.future Memory.init memory) :
  message_disjoint memory.
Proof using. eapply message_disjoint_future; eauto. apply message_disjoint_init. Qed.

Lemma time_le_rect a b c d (AB : Time.le a b) (CD : Time.le c d) :
  Time.le (Time.join a c) (Time.join b d).
Proof using.
  unfold Time.join.
  desf.
  { apply Time.le_lteq. left.
    eapply TimeFacts.le_lt_lt; eauto. }
  etransitivity; eauto.
Qed.

Lemma timemap_le_rect a b c d (AB : TimeMap.le a b) (CD : TimeMap.le c d) :
  TimeMap.le (TimeMap.join a c) (TimeMap.join b d).
Proof using.
  unfold TimeMap.join. intros x.
  all: by apply time_le_rect.
Qed.

Lemma view_le_rect a b c d (AB : View.le a b) (CD : View.le c d) :
  View.le (View.join a c) (View.join b d).
Proof using.
  unfold View.join in *.
  destruct AB. destruct CD.
  constructor; simpls; intros x.
  all: by apply timemap_le_rect.
Qed.

Lemma memory_split_get_old memory memory_split
      loc from to ts msg msg' 
      (SP : Memory.split memory loc from to ts msg msg' memory_split) :
  Memory.get loc ts memory = Some (from, msg').
Proof using. inv SP. inv SPLIT. Qed.

Lemma interval_le_not_disjoint la ra lb rb
      (LTA : Time.lt la ra)
      (LTB : Time.lt lb rb)
      (NEQ : ra <> rb)
      (ILE : Interval.le (la, ra) (lb, rb)) :
  ~ Interval.disjoint (la, ra) (lb, rb).
Proof using.
  inv ILE. simpls.
  intros HH. eapply HH; constructor; simpls; eauto.
  { reflexivity. }
  eapply TimeFacts.le_lt_lt; eauto.
Qed.

Lemma closed_view_le view memory memory'
      (LE : Memory.le memory memory')
      (CLOS : Memory.closed_view view memory) :
  Memory.closed_view view memory'.
Proof using.
  destruct CLOS.
  constructor; red; [clear RLX; rename PLN into RLX|]; ins.
  all: specialize (RLX loc); desc.
  all: apply LE in RLX; eauto.
Qed.

Lemma memory_le_add2 mem1 mem1' mem2 mem2' loc from to msg
      (LE : Memory.le mem1 mem2)
      (ADD1 : Memory.add mem1 loc from to msg mem1')
      (ADD2 : Memory.add mem2 loc from to msg mem2') :
  Memory.le mem1' mem2'.
Proof using.
  red. ins.
  erewrite Memory.add_o in LHS; eauto.
  erewrite Memory.add_o; [|by apply ADD2].
  desf. by apply LE.
Qed.

Lemma memory_le_split2 mem1 mem1' mem2 mem2' loc from to to' msg msg'
      (LE : Memory.le mem1 mem2)
      (SPLIT1 : Memory.split mem1 loc from to to' msg msg' mem1')
      (SPLIT2 : Memory.split mem2 loc from to to' msg msg' mem2') :
  Memory.le mem1' mem2'.
Proof using.
  red. ins.
  erewrite Memory.split_o in LHS; eauto.
  erewrite Memory.split_o; [|by apply SPLIT2].
  desf. by apply LE.
Qed.

Lemma memory_le_remove2 mem1 mem1' mem2 mem2' loc from to msg
      (LE : Memory.le mem1 mem2)
      (REMOVE1 : Memory.remove mem1 loc from to msg mem1')
      (REMOVE2 : Memory.remove mem2 loc from to msg mem2') :
  Memory.le mem1' mem2'.
Proof using.
  red. ins.
  erewrite Memory.remove_o in LHS; eauto.
  erewrite Memory.remove_o; [|by apply REMOVE2].
  desf. by apply LE.
Qed.

Lemma interval_disjoint_imm_le a b c d (LE : Time.le b c):
  Interval.disjoint (a, b) (c, d).
Proof using.
  red; ins.
  destruct LHS as [LFROM LTO].
  destruct RHS as [RFROM RTO]; simpls.
  eapply Time.lt_strorder.
  eapply TimeFacts.le_lt_lt.
  2: by apply RFROM.
  etransitivity; [by apply LTO|].
  done.
Qed.

Lemma message_max_ts_disjoint loc to from msg memory
      (GET : Memory.get loc to memory = Some (from, msg)) :
  Interval.disjoint (Memory.max_ts loc memory, Time.incr (Memory.max_ts loc memory))
                    (from, to).
Proof using.
  symmetry.
  apply interval_disjoint_imm_le.
  eapply Memory.max_ts_spec; eauto.
Qed.

Lemma message_disjoint_cap lprom memory memory' 
      (CLOSED : Memory.closed memory)
      (DISJOINT : message_disjoint memory)
      (CAP : Memory.cap lprom memory memory') :
  message_disjoint memory'.
Proof using.
  assert (Memory.le memory memory') as SOUND by inv CAP.
  red. ins.
  destruct (classic (to1 = to2)) as [|TNEQ]; subst; eauto.
  right.
  set (G1A:=GET1). eapply Memory.cap_inv in G1A; eauto. desf.
  3: { set (G2A:=GET2). eapply Memory.cap_inv in G2A; eauto. desf.
       { eapply message_max_ts_disjoint; eauto. }
       inv G2A0.
       symmetry.
       eapply interval_disjoint_imm_le.
       set (EE:=GET3).
       apply Memory.get_ts in EE. desf.
       apply Time.le_lteq. left. eapply TimeFacts.lt_le_lt; eauto.
       eapply Memory.max_ts_spec; eauto. }
  { set (G2A:=GET2). eapply Memory.cap_inv in G2A; eauto. desf.
    { edestruct DISJOINT with (to1:=to1) (to2:=to2); eauto. desf. }
    2: { symmetry. eapply message_max_ts_disjoint; eauto. }
    inv G2A0.
    destruct (TimeFacts.le_lt_dec to1 from2) as [|AA].
    { by apply interval_disjoint_imm_le. }
    destruct (TimeFacts.le_lt_dec to2 from1) as [|BB].
    { symmetry. by apply interval_disjoint_imm_le. }
    destruct (TimeFacts.le_lt_dec to1 to2) as [|CC].
    { exfalso. rewrite EMPTY in G1A; auto. inv G1A. }
    destruct (TimeFacts.le_lt_dec to1 to0) as [|DD].
    { edestruct DISJOINT with (to1:=to1) (to2:=to0) as [|EE]; eauto; subst.
      { exfalso. apply SOUND in GET3. rewrite GET3 in GET1. inv GET1.
        eapply Time.lt_strorder; eauto. }
      exfalso. eapply EE with (x:=to1); constructor; simpls.
      2: by apply DenseOrder_le_PreOrder.
      apply Memory.get_ts in GET1. desf.
      exfalso. eby eapply time_lt_bot. }
    edestruct DISJOINT with (to1:=to1) (to2:=to0) as [|EE]; eauto; subst.
    { exfalso. eapply Time.lt_strorder; eauto. }
    assert (Time.lt to2 to0) as FF.
    { apply Memory.get_ts in GET3. desf.
      exfalso. eby eapply time_lt_bot. }
    exfalso. eapply EE with (x:=to0); constructor; simpls.
    { etransitivity; eauto. }
    { by apply Time.le_lteq; auto. }
      by apply DenseOrder_le_PreOrder. }
  set (G2A:=GET2). eapply Memory.cap_inv in G2A; eauto. desf.
  { inv G1A0.
    destruct (TimeFacts.le_lt_dec to1 from2) as [|AA].
    { by apply interval_disjoint_imm_le. }
    destruct (TimeFacts.le_lt_dec to2 from1) as [|BB].
    { symmetry. by apply interval_disjoint_imm_le. }
    destruct (TimeFacts.le_lt_dec to2 to1) as [|CC].
    { exfalso. rewrite EMPTY in G2A; auto. inv G2A. }
    destruct (TimeFacts.le_lt_dec to2 to0) as [|DD].
    { edestruct DISJOINT with (to1:=to2) (to2:=to0) as [|EE]; eauto; subst.
      { exfalso. apply SOUND in GET3. rewrite GET3 in GET2. inv GET2.
        eapply Time.lt_strorder; eauto. }
      exfalso. eapply EE with (x:=to2); constructor; simpls.
      2: by apply DenseOrder_le_PreOrder.
      apply Memory.get_ts in GET2. desf.
      exfalso. eby eapply time_lt_bot. }
    edestruct DISJOINT with (to1:=to2) (to2:=to0) as [|EE]; eauto; subst.
    { exfalso. eapply Time.lt_strorder; eauto. }
    assert (Time.lt to1 to0) as FF.
    { apply Memory.get_ts in GET3. desf.
      exfalso. eby eapply time_lt_bot. }
    exfalso. eapply EE with (x:=to0); constructor; simpls.
    { etransitivity; eauto. }
    { by apply Time.le_lteq; auto. }
      by apply DenseOrder_le_PreOrder. }
Admitted.

(*********************************************)
(* TODO: explanation. Maybe a separate file. *)
(*********************************************)
Lemma opt_wf_unwrap (view : option View.t) (H: View.wf (View.unwrap view)) :
  View.opt_wf view.
Proof using. by destruct view; simpls; constructor. Qed.

Lemma view_join_bot_r (lhs : View.t): View.join lhs View.bot = lhs.
Proof using. rewrite View.join_comm. apply View.join_bot_l. Qed.

Lemma view_join_id l : View.join l l = l.
Proof using. rewrite View.le_join_l; reflexivity. Qed.

Lemma time_join_le_r lhs rhs (LE : Time.le lhs rhs): Time.join lhs rhs = rhs.
Proof using.
  unfold Time.join. desf.
  exfalso. eapply DenseOrder.lt_strorder. eapply TimeFacts.lt_le_lt; eauto.
Qed.

Lemma time_join_le_l lhs rhs (LE : Time.le rhs lhs): Time.join lhs rhs = lhs.
Proof using. unfold Time.join. desf. by apply TimeFacts.antisym. Qed.

Lemma time_join_bot_r lhs: Time.join lhs Time.bot = lhs.
Proof using. apply time_join_le_l. apply Time.bot_spec. Qed.

Lemma time_join_bot_l rhs: Time.join Time.bot rhs = rhs.
Proof using. apply time_join_le_r. apply Time.bot_spec. Qed.

Lemma time_lt_join_l lhs rlhs rrhs (LT : Time.lt lhs rlhs) :
  Time.lt lhs (Time.join rlhs rrhs).
Proof using. unfold Time.join. desf. eapply TimeFacts.lt_le_lt; eauto. Qed.

Lemma time_lt_join_r lhs rlhs rrhs (LT : Time.lt lhs rrhs) :
  Time.lt lhs (Time.join rlhs rrhs).
Proof using. unfold Time.join. desf. etransitivity; eauto. Qed.
