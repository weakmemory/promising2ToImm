Require Import PArith Lia Setoid.
From hahn Require Import Hahn.
Require Import PromisingLib.
From Promising2 Require Import TView View Time Event Cell Thread Memory Configuration.

From imm Require Import Events Execution.
From imm Require Import ProgToExecution.
From imm Require Import ProgToExecutionProperties.
Require Import SimulationRel.
Require Import Event_imm_promise.
Require Import SimState.
Require Import MaxValue.
Require Import ViewRel.
Require Import PromiseLTS.
From imm Require Import TraversalOrder.
From imm Require Import TLSCoherency.
From imm Require Import IordCoherency.
From imm Require Import SimClosure. 
From imm Require Import Next.
From imm Require Import TlsEventSets.

Set Implicit Arguments.

Section SimStateHelper.
  Variable G : execution.
  Variable WF : Wf G.
  Variable sc : relation actid.

Notation "'E'" := (acts_set G).
(* Notation "'acts'" := (acts G). *)
Notation "'co'" := (co G).
Notation "'coi'" := (coi G).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'rfe'" := (rfe G).
Notation "'rmw'" := (rmw G).
Notation "'lab'" := (lab G).

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

Notation "'W_ex'" := (W_ex G).
Notation "'W_ex_acq'" := (W_ex ∩₁ (fun a => is_true (is_xacq lab a))).

Lemma next_event_representation e state state' T smode
      (* (TCCOH : tc_coherent G sc T) *)
      (TCOH: tls_coherent G T)
      (GPC : wf_thread_state (tid e) state)
      (STEPS : (step (tid e))＊ state state')
      (TEH  : thread_restricted_execution G (tid e) state'.(ProgToExecution.G))
      (NEXT : next G (covered T) e)
      (STATE : @sim_state G smode (covered T) (tid e) state) :
  e = ThreadEvent (tid e) (eindex state).
Proof using.
  assert (~ is_init e) as NINIT.
  { intros H. apply NEXT. eapply init_covered; eauto.    
    split; auto. apply NEXT. }
  destruct e; desf. simpls.
  assert (index = (eindex state)); [|by subst].
  cdes STATE.
  destruct (classic (index < (eindex state))) as [LT|GE].
  { exfalso. apply NEXT. by apply PCOV. }
  destruct (classic (index > (eindex state))) as [GT|].
  2: lia.
  exfalso.
  assert (covered T (ThreadEvent thread (eindex state))) as HH.
  2: { apply PCOV in HH. lia. }
  apply NEXT. red. eexists. apply seq_eqv_r. split; eauto.
  unfold Execution.sb.
  apply seq_eqv_l; split.
  2: { apply seq_eqv_r; split.
       done. by apply NEXT. }
  assert (E (ThreadEvent thread index)) as EI.
  { apply NEXT. }
  assert (acts_set (ProgToExecution.G state') (ThreadEvent thread index)) as EI'.
  { apply (tr_acts_set TEH). by split. }
  apply (tr_acts_set TEH).
  assert (wf_thread_state thread state') as GPC'.
  { eapply wf_thread_state_steps; eauto. }
  eapply GPC'.(acts_clos).
  eapply acts_rep in EI'; eauto.
  desc. inv REP.
  lia.
Qed.

Lemma step_to_lts_step thread :
      (step thread) ⊆ (fun x y => exists pe, lts_step thread pe x y). 
Proof using.
  intros state state' STEP.
  unfold lts_step. red in STEP.
  desc. cdes STEP.
  assert (exists pe, lab_imm_promise lbls pe) as [pe XX].
  2: { exists pe. exists lbls. splits; auto. }
  unfold lab_imm_promise.
  destruct ISTEP0.
  all: rewrite LABELS.
  1,2: by exists ProgramEvent.silent.
  { eexists (ProgramEvent.read l val (rmod ord)).
    by splits. }
  { exists (ProgramEvent.write l v (wmod ord)).
    by splits. }
  { assert (exists ordr ordw, fmod ord ordr ordw) as XX.
    2: { desc. by exists (ProgramEvent.fence ordr ordw). }
    unfold fmod.
    clear -ord. desf; eauto. }
  { exists (ProgramEvent.read l val (rmod ordr)).
    by splits. }
  all: eexists (ProgramEvent.update _ _ _ _ _); splits; eauto.
Qed.

Lemma sim_state_to_events_helper_add
      thread state yst state' labels llab ll s1 s2 s3 s4 smode
      (STEPS' : rtc (fun x y => exists pe : ProgramEvent.t, lts_step thread pe x y)
                    yst state')
      (EE : E (ThreadEvent thread (eindex state)))
      (GPC : wf_thread_state thread state)
      (TERMINAL : smode = sim_normal -> is_terminal state')
      (TEH : thread_restricted_execution G thread (ProgToExecution.G state'))
      (ISTEP : istep thread labels state yst)
      (LABS : lab_imm_promise labels llab)
      (LABELS : labels = ll :: nil)
      (UG : ProgToExecution.G yst =
            add (ProgToExecution.G state) thread (eindex state)
                ll s1 s2 s3 s4)
      (UINDEX : eindex yst = eindex state + 1) :
  let e  := ThreadEvent thread (eindex state) in
  let e' := ThreadEvent thread (S (eindex state)) in
  exists ev state'' state''',
    ⟪ ESTEPS : (lts_step thread ProgramEvent.silent)＊ state state'' ⟫ /\
    ⟪ STEP : lts_step thread ev state'' state''' ⟫ /\
    ⟪ SAME_NRMW : ~ dom_rel rmw e ->
                  same_g_events lab (e :: nil) ev ⟫ /\
    ⟪ SAME_RMW  :   dom_rel rmw e -> same_g_events lab (e' :: e :: nil) ev ⟫ /\
    ⟪ INDEX_NRMW : ~ dom_rel rmw e ->
                   state'''.(eindex) = 1 + (eindex state) ⟫ /\
    ⟪ INDEX_RMW  :  dom_rel rmw e ->
                    state'''.(eindex) = 2 + (eindex state) ⟫ /\
    ⟪ SSH : @sim_state_helper G smode thread state''' state' ⟫.
Proof using WF.
  eexists. exists state. exists yst.
  assert (wf_thread_state thread yst) as GPC'.
  { eapply wf_thread_state_step; eauto.
    red. eauto. }
  assert ((step thread)＊ yst state') as STYZ.
  { apply clos_rt1n_rt in STEPS'.
    eapply clos_refl_trans_mori; eauto.
    unfold lts_step, step. basic_solver. }
  assert (~ dom_rel rmw (ThreadEvent thread (eindex state))) as XX.
  { intros [w RMW].
    assert (Tid_ thread w) as WTID.
    { apply (wf_rmwt WF) in RMW. red in RMW. simpls. }
    set (r := ThreadEvent thread (eindex state)).
    assert (Execution.rmw state'.(ProgToExecution.G) r w) as YY.
    { apply (tr_rmw TEH).
      apply seq_eqv_l. split; auto.
      apply seq_eqv_r. split; auto. }
    assert ((⦗ acts_set (ProgToExecution.G yst) ⦘ ⨾
            Execution.rmw state'.(ProgToExecution.G)) r w) as ZZ.
    { apply seq_eqv_l. split; auto.
      rewrite UG. unfold add, acts_set. simpls. by left. }
    eapply steps_dont_add_rmw in ZZ; eauto.
    apply (dom_r GPC'.(wft_rmwE)) in ZZ.
    apply seq_eqv_r in ZZ. destruct ZZ as [AA ZZ].
    apply GPC'.(wft_rmwIndex) in AA. desc.
    unfold r in RI. inv RI.
    apply GPC'.(acts_rep) in ZZ. desc.
    inv REP. lia. }
  splits; eauto.
  { apply rt_refl. }
  { red. eexists. splits; eauto. }
  1-4: ins; desf.
  { red. unfold map.
    erewrite lab_thread_eq_thread_restricted_lab.
    3: by apply TEH.
    2: { apply (tr_acts_set TEH). by split. }
    assert (ll = Execution.lab (ProgToExecution.G state')
                               (ThreadEvent thread (eindex state))); subst; auto.
    erewrite steps_preserve_lab with (state:=yst) (state':=state'); eauto.
    2: { rewrite UG. unfold add, acts_set. simpls. by left. }
    rewrite UG. unfold add. simpl. by rewrite upds. }
  { lia. }
  red. splits; eauto.
Qed.

Lemma sim_state_to_events_helper_add_rmw
      thread state yst state' labels llab rl wl s1 s2 s3 s4 smode
      (STEPS' : rtc (fun x y => exists pe : ProgramEvent.t, lts_step thread pe x y)
                    yst state')
      (EE : E (ThreadEvent thread (eindex state)))
      (GPC : wf_thread_state thread state)
      (TERMINAL : smode = sim_normal -> is_terminal state')
      (TEH : thread_restricted_execution G thread (ProgToExecution.G state'))
      (ISTEP : istep thread labels state yst)
      (LABS : lab_imm_promise labels llab)
      (LABELS : labels = wl :: rl :: nil)
      (UG : ProgToExecution.G yst =
            add_rmw (ProgToExecution.G state) thread (eindex state)
                    rl wl s1 s2 s3 s4)
      (UINDEX : eindex yst = eindex state + 2) :
  let e  := ThreadEvent thread (eindex state) in
  let e' := ThreadEvent thread (S (eindex state)) in
  exists ev state'' state''',
    ⟪ ESTEPS : (lts_step thread ProgramEvent.silent)＊ state state'' ⟫ /\
    ⟪ STEP : lts_step thread ev state'' state''' ⟫ /\
    ⟪ SAME_NRMW : ~ dom_rel rmw e ->
                  same_g_events lab (e :: nil) ev ⟫ /\
    ⟪ SAME_RMW  :   dom_rel rmw e -> same_g_events lab (e' :: e :: nil) ev ⟫ /\
    ⟪ INDEX_NRMW : ~ dom_rel rmw e ->
                   state'''.(eindex) = 1 + (eindex state) ⟫ /\
    ⟪ INDEX_RMW  :  dom_rel rmw e ->
                    state'''.(eindex) = 2 + (eindex state) ⟫ /\
    ⟪ SSH : @sim_state_helper G smode thread state''' state' ⟫.
Proof using.
  eexists. exists state. exists yst.
  assert ((step thread)＊ yst state') as STYZ.
  { apply clos_rt1n_rt in STEPS'.
    eapply clos_refl_trans_mori; eauto.
    unfold lts_step, step. basic_solver. }
  assert (dom_rel rmw (ThreadEvent thread (eindex state))) as XX.
  { eexists. eapply rmw_in_thread_restricted_rmw; eauto.
    eapply steps_preserve_rmw; eauto.
    rewrite UG. unfold add_rmw. simpls. by left. }
  assert (wf_thread_state thread yst) as GPC'.
  { eapply wf_thread_state_step; eauto.
    red. eauto. }
  splits; eauto.
  { apply rt_refl. }
  { red. eexists. splits; eauto. }
  1-4: ins; desf.
  3: by red; splits; eauto.
  2: lia.
  red. unfold map.
  assert (acts_set (ProgToExecution.G yst) (ThreadEvent thread (eindex state)))
    as EI'.
  { rewrite UG. unfold add_rmw, acts_set. simpls.
    vauto. }
  assert (acts_set (ProgToExecution.G yst) (ThreadEvent thread (S (eindex state))))
    as EI.
  { rewrite UG. unfold add_rmw, acts_set. simpls.
    left. rewrite Const.add_comm. vauto. }
  assert (E (ThreadEvent thread (S (eindex state)))) as EEI.
  { eapply (tr_acts_set TEH).
    eapply steps_preserve_E; eauto. }
  erewrite lab_thread_eq_thread_restricted_lab with (G':=(ProgToExecution.G state')); eauto.
  2: { apply (tr_acts_set TEH). by split. }
  erewrite lab_thread_eq_thread_restricted_lab with (G:=G) (G':=(ProgToExecution.G state'));
    eauto.
  2: { apply (tr_acts_set TEH). by split. }
  erewrite steps_preserve_lab with (state:=yst) (state':=state'); eauto.
  erewrite steps_preserve_lab with (state:=yst) (state':=state'); eauto.
  rewrite UG. unfold add_rmw. simpls.
  rewrite Const.add_comm. rewrite upds. rewrite updo.
  2: { intros HH. inv HH. lia. }
  rewrite upds. apply LABS.
Qed.
 
Lemma sim_state_to_events_helper smode thread
      (state state' : Language.state (thread_lts thread))
      (GPC : wf_thread_state thread state)
      (SSH : sim_state_helper G smode state state')
      (EE : E (ThreadEvent thread (eindex state))) :
  let e  := ThreadEvent thread (eindex state) in
  let e' := ThreadEvent thread (1 + (eindex state)) in
  exists ev state'' state''',
    ⟪ ESTEPS : (lts_step thread ProgramEvent.silent)＊ state state'' ⟫ /\
    ⟪ STEP : lts_step thread ev state'' state''' ⟫ /\
    ⟪ SAME_NRMW : ~ dom_rel rmw e ->
                  same_g_events lab (e :: nil) ev ⟫ /\
    ⟪ SAME_RMW  :   dom_rel rmw e -> same_g_events lab (e' :: e :: nil) ev ⟫ /\
    ⟪ INDEX_NRMW : ~ dom_rel rmw e ->
                   state'''.(eindex) = 1 + (eindex state) ⟫ /\
    ⟪ INDEX_RMW  :  dom_rel rmw e ->
                    state'''.(eindex) = 2 + (eindex state) ⟫ /\
    ⟪ SSH : sim_state_helper G smode state''' state' ⟫.
Proof using WF.
  red in SSH. desc.
  assert ((fun x y => exists pe, lts_step thread pe x y)＊ state state') as STEPS'.
  { eapply clos_refl_trans_mori; eauto. apply step_to_lts_step. }
  apply clos_rt_rt1n in STEPS'.
  clear STEPS.
  induction STEPS'.
  { exfalso. clear TERMINAL. rename x into s.
    assert (acts_set (ProgToExecution.G s) (ThreadEvent thread (eindex s))) as TT.
    { apply (tr_acts_set TEH). by split. }
    apply (acts_rep GPC) in TT.
    desc. inv REP. lia. }
  destruct H as [llab H].
  cdes H. cdes ISTEP.
  destruct ISTEP0.
  { rewrite UINDEX in *.
    destruct IHSTEPS' as [ev HH]; auto.
    { eapply wf_thread_state_step; eauto.
      red. eauto. }
    desc. exists ev. exists state''. exists state'''.
    splits; auto.
    apply rt_begin. right. exists y. split; auto.
    subst. cdes LABS. desf. }
  { rewrite UINDEX in *.
    destruct IHSTEPS' as [ev HH]; auto.
    { eapply wf_thread_state_step; eauto.
      red. eauto. }
    desc. exists ev. exists state''. exists state'''.
    splits; auto.
    apply rt_begin. right. exists y. split; auto.
    subst. cdes LABS. desf. }
  1-4: by eapply sim_state_to_events_helper_add; eauto.
  all: by eapply sim_state_to_events_helper_add_rmw; eauto.
Qed.

Lemma sim_state_to_events e state state' T smode
      (GPC : wf_thread_state (tid e) state)
      (NEXT : next G (covered T) e)
      (TCOH: tls_coherent G T)
      (PCOV : forall index, covered T (ThreadEvent (tid e) index) <-> index < (eindex state))
      (SSH : sim_state_helper G smode state state') :
  exists ev state'' state''',
    ⟪ GPC : wf_thread_state (tid e) state''' ⟫ /\
    ⟪ REPR : ThreadEvent (tid e) (eindex state) = e ⟫ /\
    ⟪ ESTEPS : (lts_step (tid e) ProgramEvent.silent)＊ state state'' ⟫ /\
    ⟪ STEP : lts_step (tid e) ev state'' state''' ⟫ /\
    ⟪ SAME_NRMW : ~ dom_rel rmw e -> same_g_events lab (e :: nil) ev ⟫ /\
    ⟪ SAME_RMW  : forall w (RMW: rmw e w),
        same_g_events lab (w :: e :: nil) ev /\
        ThreadEvent (tid e) (S (eindex state)) = w
    ⟫ /\
    ⟪ INDEX_NRMW : ~ dom_rel rmw e ->
                   state'''.(eindex) = 1 + (eindex state) ⟫ /\
    ⟪ INDEX_RMW  : forall w (RMW: rmw e w),
        state'''.(eindex) = 2 + (eindex state) ⟫ /\
    ⟪ SSH : @sim_state_helper G smode (tid e) state''' state' ⟫.
Proof using WF. 
  assert (e = ThreadEvent (tid e) (eindex state)) as HH.
  { cdes SSH.
    eapply next_event_representation; eauto.
    red. splits; eauto. }
  rewrite HH in *. 
  edestruct sim_state_to_events_helper as [ev BB]; eauto.
  { apply NEXT. }
  desc.
  assert (forall w (RMW : rmw e w), w = ThreadEvent (tid e) (S (eindex state))) as YY.
  { intros. simpls.
    assert (wf_thread_state (tid e) state') as GPC'.
    { cdes SSH. eapply wf_thread_state_steps; eauto. }
    edestruct (GPC'.(wft_rmwIndex) e w) as [ii].
    2: { desc. rewrite HH in RI. inv RI. }
    cdes SSH. apply (tr_rmw TEH).
    apply seq_eqv_l. split; auto.
    apply seq_eqv_r. split; auto.
    symmetry. by apply (wf_rmwt WF). }
  eexists. eexists. exists state'''. splits; eauto.
  { eapply wf_thread_state_step. 
    2: { cdes STEP. red. eauto. }
    eapply wf_thread_state_steps; eauto. 
    simpls.
    assert (lts_step (tid e) ProgramEvent.silent ⊆ step (tid e)) as XX.
    { unfold lts_step, step. basic_solver. }
    clear -XX ESTEPS.
    eapply clos_refl_trans_mori in XX.
      by apply XX. }
  { ins. rewrite HH in YY. rewrite (YY w RMW).
    split; auto.
    apply SAME_RMW. eexists. eauto. }
  ins. rewrite HH in YY.
  apply INDEX_RMW. eexists. eauto.
Qed.

Lemma sim_state_cover_event C e index'
      (REPR : ThreadEvent (tid e) index' = e)
      (PCOV : forall index : nat,
          C (ThreadEvent (tid e) index) <-> index < index'):
  forall index : nat,
      (C ∪₁ eq e) (ThreadEvent (tid e) index) <-> index < S index'.
Proof using.
  ins. split.
  { rewrite <- REPR. intros [HH|HH]; simpls.
    2: by inv HH.
    etransitivity; [by apply PCOV|].
    done. }
  intros AA.
  assert (index < index' \/ index = index') as [II|] by lia; subst; [left|right]; auto.
  now apply PCOV. 
Qed.

Lemma sim_state_cover_rmw_events C e e' index'
      (REPR1 : ThreadEvent (tid e)    index'  = e )
      (REPR2 : ThreadEvent (tid e) (S index') = e')
      (PCOV : forall index : nat,
          C (ThreadEvent (tid e) index) <-> index < index'):
  forall index : nat,
      (C ∪₁ eq e ∪₁ eq e') (ThreadEvent (tid e) index) <-> index < S (S index').
Proof using.
  ins. split.
  { rewrite <- REPR1, <- REPR2. intros [[HH|HH]|HH]; simpls.
    2-3: inv HH; lia.
    etransitivity; [by apply PCOV|].
    lia. }
  intros AA.
  assert (index < S index' \/ index = S index') as [II|] by lia; subst; [left|right]; auto.
  assert (index < index' \/ index = index') as [BB|] by lia; subst; [left|right]; auto.
  now apply PCOV.
Qed.

End SimStateHelper.
