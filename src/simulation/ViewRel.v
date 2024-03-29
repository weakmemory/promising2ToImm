Require Import PArith.
From hahn Require Import Hahn.
Require Import PromisingLib.
From Promising2 Require Import TView View Time Event Cell Thread Memory Configuration Local.

From imm Require Import Events.
From imm Require Import Execution.
From imm Require Import imm_s.
From imm Require Import imm_s_hb.
From imm Require Import imm_bob imm_s_ppo.
From imm Require Import CombRelations.
From imm Require Import CombRelationsMore.
    From imm Require Import Prog. 

From imm Require Import TlsViewRelHelpers.
(* From imm Require Import TraversalConfig. *)
Require Import MaxValue.
Require Import Event_imm_promise.
From imm Require Import TraversalOrder.
From imm Require Import TLSCoherency.
From imm Require Import IordCoherency.
From imm Require Import SimClosure.
From imm Require Import TlsEventSets.
From imm Require Import Next.
From imm Require Import EventsTraversalOrder.

Set Implicit Arguments.

Section ViewRel.
Variable G : execution.
Variable WF : Wf G.
Variable sc : relation actid.

(* Notation "'acts'" := (acts G). *)
Notation "'co'" := (co G).
Notation "'sw'" := (sw G).
Notation "'hb'" := (hb G).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'rmw'" := (rmw G).
Notation "'lab'" := (lab G).
Notation "'msg_rel'" := (msg_rel G).
Notation "'urr'" := (urr G sc).
Notation "'release'" := (release G).
Notation "'t_cur'" := (t_cur G sc).
Notation "'t_acq'" := (t_acq G sc).
Notation "'t_rel'" := (t_rel G sc).
Notation "'rfe'" := (rfe G).
Notation "'rfi'" := (rfi G).

Notation "'E'" := (acts_set G).
Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'Loc_' l" := (fun x => loc lab x = Some l) (at level 1). (* , format "'Loc_'  l"). *)
Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'W_'" := (fun l => W ∩₁ Loc_ l).
(* Notation "'RW'" := (fun x => R x \/ W x). *)
Notation "'FR'" := (fun x => F x \/ R x).
Notation "'FW'" := (fun x => F x \/ W x).

Notation "'Pln'" := (fun a => is_true (is_only_pln lab a)).
Notation "'Rlx'" := (is_rlx lab).
Notation "'Rel'" := (is_rel lab).
Notation "'Acq'" := (is_acq lab).
Notation "'Acqrel'" := (is_acqrel lab).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

Definition sim_msg f_to b rel :=
  forall l, max_value f_to 
              (fun a => msg_rel sc l a b \/ Loc_ l b /\ a = b) 
              (LocFun.find l (View.rlx rel)).

Definition sim_mem_helper f_to b from v rel :=
  ⟪ VAL: Some v = val lab b ⟫ /\
  ⟪ FROM: Time.lt from (f_to b) \/ 
    is_init b /\ from = Time.bot /\ (f_to b) = Time.bot ⟫ /\ 
  ⟪ SIMMSG: sim_msg f_to b rel ⟫.

Definition sim_rel C f_to rel i :=
  forall l' l, max_value f_to 
    (t_rel i l l' C ∪₁
     if Loc.eq_dec l l'
     then W_ l' ∩₁ Tid_ i ∩₁ C
     else ∅)
    (LocFun.find l (LocFun.find l' rel).(View.rlx)).

Definition sim_cur C f_to cur i :=
  forall l,
    max_value f_to (t_cur i l C)
              (LocFun.find l (View.rlx cur)).

Definition sim_acq C f_to acq i :=
  forall l,
    max_value f_to (t_acq i l C) 
    (LocFun.find l (View.rlx acq)).

Definition sim_tview C f_to tview i :=
  ⟪ CUR: sim_cur C f_to (TView.cur tview) i ⟫ /\
  ⟪ ACQ: sim_acq C f_to (TView.acq tview) i ⟫ /\
  ⟪ REL: sim_rel C f_to (TView.rel tview) i ⟫.

Lemma sim_tview_read_step
      f_to f_from
      w r locr valr xrmw ordr C tview thread rel mem
      (COH : coherence G)
      (Wf_sc : wf_sc G sc)
      (SIMTVIEW : sim_tview C f_to tview thread)
      (RRLX : Rlx r)
      (NC : ~ C r)
      (SBC : forall y, C y /\ tid y = tid r -> sb y r)
      (PRC : doma (sb ⨾ ⦗ eq r ⦘) C)
      (RF : rf w r)
      (TID : tid r = thread)
      (RPARAMS : lab r = Aload xrmw ordr locr valr)
      (GET : Memory.get locr (f_to w) mem =
             Some (f_from w, Message.full valr rel))
      (HELPER : sim_mem_helper f_to w (f_from w) valr (View.unwrap rel)) :
  sim_tview
    (C ∪₁ eq r) f_to
    (TView.read_tview tview locr (f_to w) rel (rmod ordr))
    thread.
Proof using WF.
  assert (R r) as RR by type_solver.
  assert (W w) as WW by (apply (wf_rfD WF) in RF; revert RF; basic_solver).
  assert (Loc_ locr w) as WLOC.
  { assert (loc lab w = loc lab r) as H.
    { eapply loceq_rf; eauto. }
    by rewrite H; unfold loc; rewrite RPARAMS. }
  assert (~ is_init r) as RNINIT.
  { intros INIT. apply (init_w WF) in INIT. type_solver. }
  assert (E r) as RACTS by (apply (wf_rfE WF) in RF; revert RF; basic_solver).
  assert (loc lab r = Some locr) as RLOC.
  { by unfold loc; rewrite RPARAMS. }

  assert (~ F r) as NF.
  { intros H. type_solver. }
  
  assert (Ordering.le Ordering.relaxed (rmod ordr) = Rlx r) as ORDRLX.
    by unfold is_rlx, mode_le, mod; rewrite RPARAMS; destruct ordr; simpls.
  assert (Ordering.le Ordering.acqrel (rmod ordr) = Acq r) as ORDACQ.
    by unfold is_acq, mode_le, mod; rewrite RPARAMS; destruct ordr; simpls.

  assert 
    (forall l (P : actid -> bool),
     dom_rel
     ((msg_rel sc l ∪ ⦗Loc_ l⦘) ⨾ rf ⨾ ⦗P⦘ ⨾ ⦗eq r⦘) ≡₁
     if P r
     then
       (fun a => msg_rel sc l a w \/ loc lab w = Some l /\ a = w)
     else ∅) as MSGALT.
  { ins; desf; [|basic_solver 21].
    split; [|basic_solver 21].
    unfolder; ins; desc.
    assert (z = w); subst.
      by eapply (wf_rff WF); eauto.
    basic_solver 21. }

  assert (forall l, W_ l ∩₁ eq r ≡₁ ∅) as DR'.
    by type_solver 21.

  assert (forall S l, W_ l ∩₁ eq r ∪₁ S ≡₁ S) as DR.
   by intros; rewrite DR'; apply set_union_empty_l.

  assert (forall l l',
   t_rel (tid r) l l' (C ∪₁ eq r) ∪₁
   (if LocSet.Facts.eq_dec l l'
    then W ∩₁ Loc_ l' ∩₁ Tid_ (tid r) ∩₁ (C ∪₁ eq r)
    else ∅) ≡₁
   t_rel (tid r) l l' C ∪₁
   (if LocSet.Facts.eq_dec l l'
    then W ∩₁ Loc_ l' ∩₁ Tid_ (tid r) ∩₁ C
    else ∅)) as RELALT.
  { ins; rewrite t_rel_union_eqv; auto.
    by desf; apply set_equiv_union; [done| type_solver 21].
    by revert PRC; basic_solver. }

  red in SIMTVIEW; desf.
  red in CUR; desf.
  red in ACQ; desf.
  red in REL; desf.
  cdes HELPER; clear FROM.
  red in SIMMSG; desf.
  red; splits; intros l; simpls;
    unfold LocFun.find, TimeMap.join in *;
    (try rewrite ORDRLX); try (rewrite ORDACQ).
  { eapply max_value_same_set.
    2: apply t_cur_urr_union_eqv; auto; revert PRC; basic_solver.
    simpls.
    rewrite Time.join_assoc.
    unfold CombRelations.t_cur, CombRelations.c_cur in CUR.
    eapply max_value_join; eauto.
    eapply max_value_join; eauto.
    { eapply max_value_same_set; [|by apply DR].
      eapply max_value_same_set; [|by eapply dom_rel_r; eauto].
      unfold TimeMap.singleton, LocFun.add, LocFun.find, LocFun.init.
      destruct (Loc.eq_dec l locr) as [EQ|NEQ]; simpls; subst.
      { by apply max_value_singleton. }
      apply max_value_empty; intros x HH; desf. }
    specialize (MSGALT l (Acq)).
    eapply max_value_same_set; [|by apply MSGALT].
    destruct (Acq r) eqn: RACQ; unfold View.rlx; simpls.
    by apply max_value_empty; intros x HH; desf. }
  { eapply max_value_same_set.
    2: apply t_acq_urr_union_eqv; auto; revert PRC; basic_solver.
    rewrite Time.join_assoc.
    unfold CombRelations.t_acq, CombRelations.c_acq in ACQ.
    eapply max_value_join; eauto.
    eapply max_value_join; eauto.
    { eapply max_value_same_set; [|by apply DR].
      eapply max_value_same_set; [|by eapply (dom_rel_r WF l); eauto].
      destruct (LocSet.Facts.eq_dec l locr); simpls; subst;
        unfold TimeMap.singleton, LocFun.add, LocFun.find, LocFun.init.
      { rewrite Loc.eq_dec_eq. by apply max_value_singleton. }
      rewrite Loc.eq_dec_neq; auto.
      apply max_value_empty. intros x HH; desf. }
    apply set_equiv_union; [reflexivity|].
    specialize (MSGALT l (fun x => true)).
    simpl in MSGALT. rewrite <- MSGALT.
    arewrite (⦗fun _ : actid => true⦘ ≡ ⦗fun _ : actid => True⦘).
    { split; intros x y H; red; red in H; desf. }
    by rewrite seq_id_l. }
  intros l'.
  eapply max_value_same_set; [by apply REL|].
  apply RELALT.
Qed.

Lemma sim_tview_write_step f_to f_from
      w locw valw xmw ordw C tview thread rel mem sc_view
      (COH : coherence G)
      (Wf_sc : wf_sc G sc)
      (CINE : C ⊆₁ E)
      (CCLOS : doma (sb ⨾ ⦗C⦘) C)
      (SIMTVIEW : sim_tview C f_to tview thread)
      (NC : ~ C w)
      (SBC : forall y, C y /\ tid y = tid w -> sb y w)
      (PRC : doma (sb ⨾ ⦗ eq w ⦘) C)
      (TID : tid w = thread)
      (NINIT : ~ is_init w)
      (WACTS : E w)
      (WPARAMS : lab w = Astore xmw ordw locw valw)
      (GET : Memory.get locw (f_to w) mem =
             Some (f_from w, Message.full valw rel))
      (HELPER : sim_mem_helper f_to w (f_from w) valw (View.unwrap rel))
 : sim_tview
    (C ∪₁ eq w) f_to
    (TView.write_tview
       tview sc_view locw (f_to w) (wmod ordw))
    thread.
Proof using WF.
  assert (W w) as WW.
  { by unfold is_w; rewrite WPARAMS. }
  assert (loc lab w = Some locw) as LOC.
  { by unfold loc; rewrite WPARAMS. }
  assert (~ F w) as NF.
  { intros H; type_solver. }

  assert (forall S l, S ∪₁ dom_rel (⦗Loc_ l⦘ ⨾ rf ⨾ ⦗eq w⦘) ≡₁ S) as DR1.
    by ins; rewrite (dom_r (wf_rfD WF)); type_solver.

  assert (forall S O l,
             S ∪₁
             dom_rel ((msg_rel sc l ∪ ⦗Loc_ l⦘) ⨾ rf ⨾ ⦗O⦘ ⨾ ⦗eq w⦘) ≡₁ S)
    as DR2.
    by ins; rewrite (dom_r (wf_rfD WF)); type_solver.

  assert (forall S l,
             S ∪₁
             dom_rel ((msg_rel sc l ∪ ⦗Loc_ l⦘) ⨾ rf ⨾ ⦗eq w⦘) ≡₁ S)
    as DR5.
  { ins.
    arewrite (⦗eq w⦘ ≡ ⦗ fun _ => True ⦘ ⨾ ⦗eq w⦘).
    2: by apply DR2.
    by rewrite seq_id_l. }
  
  assert (forall l,
             W_ l ∩₁ eq w ≡₁
             if LocSet.Facts.eq_dec l locw then eq w else ∅) as DR3.
    by basic_solver.

  assert (Ordering.le Ordering.acqrel (wmod ordw) = Rel w)
    as ORDREL.
  { unfold is_rel, mode_le, mod; rewrite WPARAMS; destruct ordw; simpls. }
  
  red in SIMTVIEW; desf.
  red in CUR; desf.
  red in ACQ; desf.
  red in REL; desf.
  cdes HELPER; clear FROM.
  red in SIMMSG; desf.
  red; splits; intros l; simpls;
    unfold LocFun.find, TimeMap.join in *; try (rewrite ORDREL).
  { eapply max_value_same_set.
    2: apply t_cur_urr_union_eqv; auto; revert PRC; basic_solver.
    unfold CombRelations.t_cur, CombRelations.c_cur in CUR.
    eapply max_value_join; eauto.
    eapply max_value_same_set; [|eapply DR2].
    eapply max_value_same_set; [|eapply DR1].
    eapply max_value_same_set; [|eapply DR3].
    unfold TimeMap.singleton, LocFun.add, LocFun.find, LocFun.init.
    destruct (Loc.eq_dec l locw) as [EQ|NEQ]; simpls; subst.
    { by apply max_value_singleton. }
    apply max_value_empty; intros x HH; desf. }
  { eapply max_value_same_set.
    2: apply t_acq_urr_union_eqv; auto; revert PRC; basic_solver.
    unfold CombRelations.t_acq, CombRelations.c_acq in ACQ.
    eapply max_value_join; eauto.
    eapply max_value_same_set; [|eapply DR5].
    eapply max_value_same_set; [|eapply DR1].
    eapply max_value_same_set; [|eapply DR3].
    unfold TimeMap.singleton, LocFun.add, LocFun.find, LocFun.init.
    destruct (Loc.eq_dec l locw) as [EQ|NEQ]; simpls; subst.
    { by apply max_value_singleton. }
    apply max_value_empty; intros x HH; desf. }
  intros l0.
  eapply max_value_same_set; [|eapply t_rel_w_union_eqv; eauto]; cycle 2.
  3: by apply urr_refl.
  { ins.
    rewrite ((urr_rel_n_f_alt_union_eqv WF) sc Wf_sc l1 l' C w (tid w)); eauto.
    basic_solver 42.
    revert PRC; basic_solver 42. }
  unfold TimeMap.join, TimeMap.singleton, View.singleton_ur,
  LocFun.add, LocFun.find, LocFun.init.
  destruct (Loc.eq_dec l locw) as [EQ|NEQ]; simpls; subst.
  destruct (Rel w); simpls; eapply max_value_join; eauto.
  all: unfold TimeMap.singleton, LocFun.add, LocFun.find, LocFun.init.
  all: destruct (Loc.eq_dec l0 locw); subst.
  all: try by apply max_value_singleton.
  all: try by apply max_value_empty; auto.
Qed.

Lemma sim_tview_f_issued f_to f_to' T tview thread
      (* (TCCOH : tc_coherent G sc T) *)
      (TCOH: tls_coherent G T)
      (ICOH: iord_coherent G sc T)
      (IMMCON : imm_consistent G sc)
      (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
      (ISSEQ : forall e (ISS: issued T e), f_to' e = f_to e)
      (SIMTVIEW : sim_tview (covered T) f_to tview thread):
  sim_tview (covered T) f_to' tview thread.
Proof using WF.
  assert (wf_sc G sc) as WFSC by (apply IMMCON). 
  cdes SIMTVIEW.
  red; splits; red; ins; eapply max_value_new_f.
  1, 3, 5: by eauto.
  { intros x H. apply t_cur_covered in H; auto. }
  { intros x H. apply t_acq_covered in H; auto. }
  intros x [H|H].
  { apply t_rel_covered in H; auto. }
  destruct (classic (l = l')) as [LEQ|LNEQ].
  2: { rewrite Loc.eq_dec_neq in H; desf. }
  apply ISSEQ; subst.
  rewrite Loc.eq_dec_eq in H.
  eapply w_covered_issued; eauto. 
  revert H; basic_solver 21.
Qed.

Lemma sim_sc_fence_step
      T f_to
      f ordf ordr ordw tview thread sc_view
      (TCOH : tls_coherent G T)
      (ICOH : iord_coherent G sc T)
      (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
      (IMMCON : imm_consistent G sc)
      (NEXT : next G (covered T) f)
      (TID : tid f = thread)
      (FPARAMS : lab f = Afence ordf)
      (SAME_MOD : fmod ordf ordr ordw)
      (SIMTVIEW : sim_tview (covered T) f_to tview thread)
      (SC_VIEW :
         forall (l : Loc.t),
           max_value f_to (S_tm G l (covered T))
                     (LocFun.find l sc_view)) :
  forall l : Loc.t,
    max_value f_to (S_tm G l (covered T ∪₁ eq f))
              (LocFun.find
                 l (TView.write_fence_sc
                      (TView.read_fence_tview tview ordr) 
                      sc_view ordw)).
Proof using WF.
  cdes IMMCON.
  intros l. specialize (SC_VIEW l).
  destruct (classic (is_sc lab f)) as [FISSC|FISNOSC].
  all: unfold TView.write_fence_sc.
  { assert (Ordering.le Ordering.seqcst ordw /\
            Ordering.le Ordering.acqrel ordr) as [LLW LLR].
    { red in SAME_MOD.
      unfold is_sc, mod in FISSC. rewrite FPARAMS in FISSC.
      desf; desf. }
    unfold TView.read_fence_tview.
    rewrite LLW, LLR; simpls.
    unfold LocFun.find, TimeMap.join.
    eapply max_value_same_set.
    2: { eapply s_tm_cov_sc_fence; eauto. }  
    eapply max_value_join.
    3: by eauto.
    { done. }
    apply SIMTVIEW. }
  assert (covered T ⊆₁ covered T ∪₁ eq f) as CCC.
  { basic_solver. }
  eapply max_value_same_set. 
  2: apply s_tm_n_f_steps.
  3: by apply CCC.
  2: { by apply init_covered. }
  2: { unfolder. ins. intros [? ?]. des; vauto. }  
  assert (~ Ordering.le Ordering.seqcst ordw) as LL; [|by desf].
  intros H. subst.
  assert (ordw = Ordering.seqcst) as SS.
  { destruct ordw; desf. }
  unfold is_sc, mod in FISNOSC.
  red in SAME_MOD; simpls;
    rewrite FPARAMS in *; simpls.
  destruct ordf; desf.
Qed.

Lemma sim_tview_fence_step T
      f_to
      f ordf ordr ordw tview thread sc_view
      (* (TCCOH : tc_coherent G sc T) *)
      (TCOH: tls_coherent G T)
      (ICOH: iord_coherent G sc T)
      (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
      (IMMCON : imm_consistent G sc)
      (COV : coverable G sc T f)
      (NCOV : ~ covered T f)
      (TID : tid f = thread)
      (SAME_MOD : fmod ordf ordr ordw)
      (FPARAMS : lab f = Afence ordf)
      (SIMTVIEW : sim_tview (covered T) f_to tview thread)
      (SC_VIEW :
         ~ (E∩₁F∩₁Sc ⊆₁ (covered T)) ->
         forall (l : Loc.t),
           max_value f_to (S_tm G l (covered T)) (LocFun.find l sc_view)) :
  sim_tview (covered T ∪₁ eq f) f_to
    (TView.write_fence_tview
       (TView.read_fence_tview tview ordr) 
       sc_view ordw) (tid f).
Proof using WF.
  cdes IMMCON.
  assert (is_f lab f) as FENCE.
  { by unfold is_f; rewrite FPARAMS. }
  assert (E f) as EF.
  { apply COV. }
  red; splits.
  all: unfold TView.read_fence_tview, TView.write_fence_tview,
    TView.write_fence_sc; simpls.
  all: red; simpls.
  { intros l.
    eapply max_value_same_set.
    2: apply t_cur_fence_step; eauto.
    red in SAME_MOD.
    unfold is_sc, is_acq, mod; rewrite FPARAMS in *.
    destruct ordf; simpls; destruct SAME_MOD; subst.
    all: desf; simpls.
    1-5: by apply SIMTVIEW.
    unfold set_union; unfold LocFun.find.
    eapply max_value_join.
    { apply SC_VIEW.
      intros H. apply NCOV. apply H; split; [split|]; auto.
      unfold is_sc, mod. by rewrite FPARAMS. }
    { by apply SIMTVIEW. }
    basic_solver. }
  { intros l.
    eapply max_value_same_set.
    2: by apply t_acq_fence_step.
    red in SAME_MOD.
    unfold is_sc, is_acq, mod; rewrite FPARAMS in *.
    destruct ordf; simpls; destruct SAME_MOD; subst.
    all: desf; simpls.
    1-5: unfold LocFun.find, TimeMap.join, TimeMap.bot; simpls.
    1-5: eapply max_value_join; eauto; [|apply max_value_empty; intros x H; desf].
    1-5: by apply SIMTVIEW.
    rewrite TimeMap.join_comm, TimeMap.join_assoc, TimeMap.join_comm.
    eapply max_value_join; eauto.
    { rewrite TimeMap.le_join_r; [by apply SIMTVIEW|].
      apply TimeMap.le_PreOrder. }
    apply SC_VIEW.
    intros H. apply NCOV. apply H; split; [split|]; auto.
    unfold is_sc, mod. by rewrite FPARAMS. }
  intros l' l.
  eapply max_value_same_set; [| by eapply t_rel_fence_step].
  red in SAME_MOD.
  unfold is_sc, is_acq, is_acqrel, is_rel, mod, mode_le; rewrite FPARAMS in *.
  destruct ordf; simpls; destruct SAME_MOD; subst.
  all: cdes SIMTVIEW; red in REL.
  all: desf; simpls.
  unfold LocFun.find, TimeMap.join, TimeMap.bot; simpls.
  eapply max_value_join; eauto.
  apply SC_VIEW.
  intros H. apply NCOV. apply H; split; [split|]; auto.
  unfold is_sc, mod. by rewrite FPARAMS.
Qed.

Lemma sim_tview_other_thread_step f_to
      C C' tview thread
      (CINIT : is_init ∩₁ E ⊆₁ C)
      (CINCL : C ⊆₁ C')
      (CE : C' ⊆₁ E)
      (COVSTEP : forall a, tid a = thread -> C' a -> C a)
      (SIMTVIEW : sim_tview C f_to tview thread) :
  sim_tview C' f_to tview thread.
Proof using WF.
  red; splits; red; splits; ins.
  all: eapply max_value_same_set.
  all: try by (apply SIMTVIEW).
  { apply t_cur_other_thread; eauto. }
  { apply t_acq_other_thread; eauto. }
  apply t_rel_if_other_thread; eauto.
Qed.


Lemma rel_le_cur PC thread T f_to l langst local
      (SIM_TVIEW : sim_tview (covered T) f_to (Local.tview local) thread)
      (TID : IdentMap.find thread (Configuration.threads PC) = Some (langst, local)) :
  TimeMap.le (View.rlx (TView.rel (Local.tview local) l))
             (View.rlx (TView.cur (Local.tview local))).
Proof using WF.
  cdes SIM_TVIEW.
  intros l'.
  specialize (CUR l').
  specialize (REL l l').
  unfold LocFun.find in *.
  set (srel := t_rel thread l' l (covered T)).
  set (scur := t_cur thread l' (covered T)).
  assert (srel ⊆₁ scur) as SS.
  { unfold scur, srel.
    intros x H.
    red in H. red.
    eapply dom_rel_mori; [|apply H].
    unfold c_rel, c_cur.
    rewrite inclusion_seq_eqv_l.
      by rewrite inclusion_seq_eqv_l. }
  cdes REL.
  destruct MAX as [[MAX MAX'] | MAX].
  { rewrite MAX'. apply Time.bot_spec. }
  desc.
  etransitivity; [apply LB'|].
  cdes CUR.
  apply UB0.
  destruct INam as [|INam]; [by apply SS|].
  destruct (Loc.eq_dec l' l) as [LL|NLL]; subst.
  2:  by red in INam.
  exists a_max. red.
  hahn_rewrite <- seqA.
  unfolder in INam; desc.
  do 2 (apply seq_eqv_r; split; auto).
  { by apply urr_refl. }
    by left.
Qed.

End ViewRel.

Add Parametric Morphism : sim_tview with signature
    eq ==> (@same_relation actid) ==> (@set_equiv actid) ==>
    eq ==> eq ==> eq ==> Basics.impl as sim_tview_more_impl.
Proof using.
  unfold Basics.impl. ins. red in H1. desc. red. splits.
  { red. ins. red. red in CUR. specialize (CUR l).
    red in CUR. desc. splits.
    { ins. apply UB.
      eapply set_equiv_exp; [| apply INa]. by rewrite H, H0. }
    des.
    { left. split; auto. ins. intros TCUR. apply (MAX a).
      eapply set_equiv_exp; [| apply TCUR]. by rewrite H, H0. }
    right. eexists. splits; eauto.
    eapply set_equiv_exp; [| apply INam]. by rewrite H, H0. 
  }
  { red in ACQ. red. ins. specialize (ACQ l). red in ACQ. desc.
    red. splits.
    { ins. apply UB. eapply set_equiv_exp; [| apply INa]. by rewrite H, H0. }
    des.
    { left. split; eauto. ins. intros TCUR. apply (MAX a).
      eapply set_equiv_exp; [| apply TCUR]. by rewrite H, H0. }
    right. eexists. splits; eauto.
    eapply set_equiv_exp; [| apply INam]. by rewrite H, H0. }
  red in REL. red. ins. specialize (REL l' l). red in REL. desc.
  red. splits.
  { ins. eapply UB; eauto. 
    eapply set_equiv_exp; [| apply INa]. rewrite !H, !H0.
    destruct (RegSet.Facts.eq_dec l l'); rewrite ?H, ?H0; basic_solver. }
  { des.
    { left. splits; eauto. ins. intros TCUR. apply (MAX a).
      eapply set_equiv_exp; [| apply TCUR]. rewrite !H, !H0.
      destruct (RegSet.Facts.eq_dec l l'); rewrite ?H, ?H0; basic_solver. }
    right. eexists. splits; eauto. 
    eapply set_equiv_exp; [| apply INam]. rewrite !H, !H0.
    destruct (RegSet.Facts.eq_dec l l'); rewrite ?H, ?H0; basic_solver. }
Qed.  

Add Parametric Morphism : sim_tview with signature
    eq ==> (@same_relation actid) ==> (@set_equiv actid) ==>
    eq ==> eq ==> eq ==> iff as sim_tview_more.
Proof using.
  split; apply sim_tview_more_impl; eauto.
  all: symmetry; auto. 
Qed. 
