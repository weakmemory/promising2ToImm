Require Import PArith Arith.
From hahn Require Import Hahn.
Require Import PromisingLib.
From Promising2 Require Import Configuration TView View Time Event Cell Thread Memory Local.
From imm Require Import Events.
From imm Require Import Execution.
From imm Require Import Execution_eco.
From imm Require Import imm_s_hb.
From imm Require Import imm_s.
From imm Require Import imm_common.
From imm Require Import CombRelations.
From imm Require Import CombRelationsMore.
From imm Require Import ProgToExecution.

Require Import TraversalConfig.
Require Import ExtTraversal.
Require Import MaxValue.
Require Import ViewRel.
Require Import ViewRelHelpers.
Require Import SimulationRel.
Require Import SimulationPlainStepAux.
Require Import PlainStepBasic.
Require Import SimState.
Require Import SimStateHelper.
Require Import PromiseLTS.
Require Import MemoryAux.
Require Import FtoCoherent.
Require Import AuxRel2.

Set Implicit Arguments.

Section WritePlainStep.

Variable G : execution.
Variable WF : Wf G.
Variable sc : relation actid.
Variable CON : imm_consistent G sc.

Notation "'E'" := G.(acts_set).
Notation "'sb'" := G.(sb).
Notation "'rf'" := G.(rf).
Notation "'co'" := G.(co).
Notation "'rmw'" := G.(rmw).
Notation "'data'" := G.(data).
Notation "'addr'" := G.(addr).
Notation "'ctrl'" := G.(ctrl).

Notation "'fr'" := G.(fr).
Notation "'coe'" := G.(coe).
Notation "'coi'" := G.(coi).
Notation "'deps'" := G.(deps).
Notation "'rfi'" := G.(rfi).
Notation "'rfe'" := G.(rfe).
Notation "'detour'" := G.(detour).
Notation "'hb'" := G.(hb).
Notation "'sw'" := G.(sw).

Notation "'lab'" := G.(lab).

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'RW'" := (R ∪₁ W).
Notation "'FR'" := (F ∪₁ R).
Notation "'FW'" := (F ∪₁ W).

Notation "'Pln'" := (fun a => is_true (is_only_pln lab a)).
Notation "'Rlx'" := (fun a => is_true (is_rlx lab a)).
Notation "'Rel'" := (fun a => is_true (is_rel lab a)).
Notation "'Acq'" := (fun a => is_true (is_acq lab a)).
Notation "'Acqrel'" := (fun a => is_true (is_acqrel lab a)).
Notation "'Acq/Rel'" := (fun a => is_true (is_ra lab a)).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

Notation "'Loc_' l" := (fun x => loc lab x = Some l) (at level 1).
Notation "'W_ex'" := G.(W_ex).
Notation "'W_ex_acq'" := (W_ex ∩₁ (fun a => is_true (is_xacq lab a))).

Lemma rlx_write_promise_step PC T S f_to f_from thread w smode
      (SIMREL_THREAD : simrel_thread G sc PC T S f_to f_from thread smode)
      (TID : tid w = thread)
      (TSTEP : ext_itrav_step
                 G sc w (mkETC T S) (mkETC (mkTC (covered T) (issued T ∪₁ eq w))
                                           (S ∪₁ eq w)))
      (NREL : ~ is_rel lab w) :
  let T' := (mkTC (covered T) (issued T ∪₁ eq w)) in
  let S' := S ∪₁ eq w in
  exists PC' f_to' f_from',
    ⟪ PCSTEP : plain_step MachineEvent.silent thread PC PC' ⟫ /\
    ⟪ SIMREL_THREAD : simrel_thread G sc PC' T' S' f_to' f_from' thread smode ⟫ /\
    ⟪ SIMREL :
        smode = sim_normal -> simrel G sc PC T S f_to f_from ->
        simrel G sc PC' T' S' f_to' f_from' ⟫.
Proof using WF CON.
  cdes SIMREL_THREAD. cdes COMMON. cdes LOCAL.

  assert (ISS : issuable G sc T w).
  { eapply ext_itrav_step_iss_issuable with (T:=mkETC T S); eauto. }
  assert (WNISS : ~ issued T w).
  { eapply ext_itrav_step_iss_nI with (T:=mkETC T S); eauto. }

  assert (W w /\ E w) as [TYPE WACT].
  { split; apply ISS. }

  assert (tc_coherent G sc T) as sTCCOH by apply TCCOH.

  assert (~ covered T w) as WNCOV.
  { intros H. apply WNISS.
    eapply w_covered_issued; eauto. split; auto. }

  assert (~ is_init w) as WNINIT.
  { intros H; apply WNCOV. by apply TCCOH. }
  
  assert (tc_coherent G sc (mkTC (covered T) (issued T ∪₁ eq w))) as TCCOH_NEW.
  { apply TSTEP. }
 
  assert (exists ex ordw locw valw,
             lab w = Astore ex ordw locw valw) as PARAMS; desf.
  { unfold is_w in TYPE.
    destruct (lab w); desf; eexists; eauto. }
  assert (loc lab w = Some locw) as WLOC.
  { by unfold loc; rewrite PARAMS. }
  assert (val lab w = Some valw) as WVAL.
  { by unfold val; rewrite PARAMS. }

  assert (W ∩₁ Rel ∩₁ (issued T ∪₁ eq w) ⊆₁ covered T) as RELCOV_NEW.
  { simpls. rewrite !set_inter_union_r.
    rewrite (set_interA W Rel (eq w)).
    arewrite (Rel ∩₁ eq w ⊆₁ ∅).
    { intros x [H]; desf. }
    generalize RELCOV; basic_solver. }
  
  cdes SIM_MEM. 
  edestruct write_promise_step_helper as [p_rel H].
  13: by apply FCOH.
  all: eauto.
  desc. destruct H1 as [H|H].
  { cdes H; clear H.
    set (pe :=
           ThreadEvent.promise
             locw (f_from' w) (f_to' w) valw
             (Some
                (View.join
                   (View.join
                      (if is_rel lab w
                       then TView.cur (Local.tview local)
                       else TView.rel (Local.tview local) locw) (View.unwrap p_rel))
                   (View.singleton_ur locw (f_to' w))))
             Memory.op_kind_add).

    eexists; exists f_to'; exists f_from'.
    apply and_assoc. apply pair_app; unnw.
    { split.
      { set (pe' := None).
        assert (pe' = ThreadEvent.get_event pe) as H.
        { unfold pe. simpls. }
        rewrite H. clear H.
        econstructor; eauto.
        apply Thread.step_promise.
        constructor.
        2: by simpls.
        constructor; eauto. }
      destruct (is_rel lab w); simpls; subst.
      red; splits; red; splits; eauto.
      simpls.
      exists state; eexists.
      rewrite IdentMap.gss.
      splits; eauto.
      eapply sim_tview_f_issued; eauto. }
    intros [PCSTEP SIMREL_THREAD']; split; auto.
    intros SMODE SIMREL.
    eapply simrel_f_issued in SIMREL; eauto.
    eapply full_simrel_step.
    13: by apply SIMREL.
    11: { ins. rewrite IdentMap.Facts.add_in_iff.
          split; auto. intros [|]; auto; subst.
          apply IdentMap.Facts.in_find_iff.
            by rewrite LLH. }
    all: simpls; eauto.
    7: by eapply msg_preserved_add; eauto.
    6: by eapply closedness_preserved_add; eauto.
    { eapply coveredE; eauto. }
    rewrite issuedE; eauto.
    all: basic_solver. }
  cdes H. clear H.
  set (pe :=
         ThreadEvent.promise
           locw (f_from' w) (f_to' w) valw rel 
           (Memory.op_kind_split (f_to' ws) valws relws)).
  eexists; exists f_to'; exists f_from'.
  apply and_assoc. apply pair_app; unnw.
  { split.
    { set (pe' := MachineEvent.silent).
      assert (pe' = ThreadEvent.get_machine_event pe) as H.
      { unfold pe. simpls. }
      rewrite H. clear H.
      econstructor; eauto.
      apply Thread.step_promise.
      constructor.
      2: by simpls.
      constructor; eauto. }
    subst.
    red; splits; red; splits; eauto.
    { intros. desf. }
    simpls.
    exists state; eexists.
    rewrite IdentMap.gss.
    destruct (is_rel lab w); simpls.
    splits; eauto.
    { eapply sim_tview_f_issued; eauto. }
    eapply tview_closedness_preserved_split; eauto. }
  intros [PCSTEP SIMREL_THREAD']; split; auto.
  intros SMODE'. desf.
Qed.

Lemma rel_write_step PC T f_to f_from thread w smode
      (SIMREL_THREAD : simrel_thread G sc PC thread T f_to f_from smode)
      (TID : tid w = thread)
      (NEXT : next G (covered T) w)
      (TYPE : W w)
      (REL : Rel w)
      (NRMW : ~ codom_rel rmw w)
      (TS1 : itrav_step G sc w T (mkTC (covered T) (issued T ∪₁ eq w)))
      (TS2 : itrav_step G sc w
                        (mkTC (covered T) (issued T ∪₁ eq w))
                        (mkTC (covered T ∪₁ eq w) (issued T ∪₁ eq w))) :
  let T' := (mkTC (covered T ∪₁ eq w) (issued T ∪₁ eq w)) in
  exists PC' f_to' f_from',
    ⟪ PCSTEP : plain_step None thread PC PC' ⟫ /\
    ⟪ SIMREL_THREAD : simrel_thread G sc PC' thread T' f_to' f_from' smode ⟫ /\
    ⟪ SIMREL :
        smode = sim_normal -> simrel G sc PC T f_to f_from ->
        simrel G sc PC' T' f_to' f_from' ⟫.
Proof using WF CON.
  cdes SIMREL_THREAD. cdes COMMON. cdes LOCAL.

  assert (~ covered T w) as WNCOV.
  { apply NEXT. }
  
  assert (issuable G T w) as WISS.
  { eapply issuable_next_w; eauto. split; auto. }

  cdes STATE. rewrite <- TID in *.
  edestruct sim_state_to_events as [ev HH]; eauto.
  desc.

  apply clos_rt_rt1n in ESTEPS.
  eapply (rtc_lang_tau_step_rtc_thread_tau_step
            _ _ _ local PC.(Configuration.sc) PC.(Configuration.memory)) in ESTEPS.

  assert (E w) as WACT by apply NEXT.
  assert (Rlx w) as WRLX by mode_solver.

  assert (exists ex ordw locw valw, lab w = Astore ex ordw locw valw) as PARAMS; desf.
  { unfold is_w in TYPE.
    destruct (lab w); desf; eexists; eauto. }
  assert (loc lab w = Some locw) as WLOC.
  { by unfold loc; rewrite PARAMS. }
  assert (val lab w = Some valw) as WPVAL.
  { by unfold val; rewrite PARAMS. }
  assert (Events.mod lab w = ordw) as WMOD.
  { by unfold Events.mod; rewrite PARAMS. }

  assert (~ is_init w) as NINIT.
  { intros IIN. apply WNCOV. apply TCCOH. by split. }
  assert (~ issued T w) as WNISS.
  { intros ISS. apply WNCOV. apply RELCOV.
    split; [split|]; auto. }

  assert (Ordering.le Ordering.relaxed (Event_imm_promise.wmod ordw)) as NRLX_PROM_W.
  { unfold Event_imm_promise.wmod, is_rel, is_rlx, mode_le, Events.mod in *.
    rewrite PARAMS in *.
    destruct ordw; simpls. }

  assert (Ordering.le Ordering.strong_relaxed (Event_imm_promise.wmod ordw)) as NSRLX_PROM_W.
  { unfold Event_imm_promise.wmod, is_rel, is_rlx, mode_le, Events.mod in *.
    rewrite PARAMS in *.
    destruct ordw; simpls. }
  assert (Ordering.le Ordering.acqrel (Event_imm_promise.wmod ordw)) as NREL_PROM_W.
  { unfold Event_imm_promise.wmod, is_rel, is_rlx, mode_le, Events.mod in *.
    rewrite PARAMS in *.
    destruct ordw; simpls. }

  edestruct write_promise_step_helper as [p_rel H].
  13: by apply FCOH.
  all: eauto.
  desc. destruct H1 as [H|H].
  2: by cdes H; desf.
  cdes H; clear H. destruct (is_rel lab w) eqn:RELVV; [|by red in REL; desf].
  simpls.

  assert (~ dom_rel rmw w) as NNRMW.
  { intros [x HH].
    apply (dom_l WF.(wf_rmwD)) in HH. apply seq_eqv_l in HH.
    type_solver. }
  
  assert (Event_imm_promise.same_g_events lab (w :: nil) ev) as SAME.
  { by apply SAME_NRMW. }
  
  assert (ev = ProgramEvent.write locw valw (Event_imm_promise.wmod ordw)) as EV.
  { red in SAME; red in SAME; simpls.
    rewrite PARAMS in *; simpls.
    destruct ev; desf; vauto. }
  set (pe := ThreadEvent.write locw (f_from' w) (f_to' w) valw
                               (Some (View.join
                                        (View.join
                                           (TView.cur (Local.tview local))
                                           (View.unwrap p_rel))
                                        (View.singleton_ur locw (f_to' w))))
                               (Event_imm_promise.wmod ordw)).
  assert (ev = ThreadEvent.get_program_event pe) as EV' by done; subst.

  assert (p_rel = None); subst.
  { destruct P_REL_CH as [H|H]; desc; auto.
    exfalso. destruct INRMW as [z [_ RMW]].
    eapply NRMW. eexists; eauto. }

  eexists; exists f_to'; exists f_from'.
  apply and_assoc. apply pair_app; unnw.
  { split.
    { set (pe' := None).
      assert (pe' = ThreadEvent.get_event pe) as H.
      { unfold pe. simpls. }
      rewrite H. clear H.
      econstructor; eauto.
      apply Thread.step_program.
      constructor.
      { rewrite <- EV'; eauto. }
      eapply Local.step_write.
      constructor.
      { unfold TView.write_released, TView.write_tview; simpls.
        unfold LocFun.add. rewrite Loc.eq_dec_eq.
        destruct (Ordering.le Ordering.relaxed
                              (Event_imm_promise.wmod (Events.mod lab w))); simpls.
        destruct (Ordering.le Ordering.acqrel
                              (Event_imm_promise.wmod (Events.mod lab w))); simpls.
        rewrite View.join_bot_l. by rewrite view_join_bot_r. }
      { by constructor. }
      { econstructor; eauto. }
      ins; split; auto. }
    red; splits; red; splits; eauto; ins.
    { eapply trav_step_coherence. exists w. apply TS2.
      eapply trav_step_coherence; eauto. by exists w. }
    { generalize RELCOV. basic_solver 10. }
    { apply WF.(wf_rmwD) in RMW.
      apply seq_eqv_l in RMW; destruct RMW as [RR RMW].
      apply seq_eqv_r in RMW; destruct RMW as [RMW WW].
      split; intros [HH|HH]; left; auto.
      { erewrite <- RMWCOV; eauto. }
      { type_solver. }
      { erewrite RMWCOV; eauto. }
      subst. exfalso. apply NRMW. eexists; eauto. }
    { destruct (classic (tid e = tid w)) as [EQ|NEQ].
      { rewrite EQ. rewrite IdentMap.gss. eauto. }
      rewrite IdentMap.gso; auto. }
    { destruct (classic (thread' = tid w)) as [EQ|NEQ].
      { rewrite EQ in *. rewrite IdentMap.gss in *.
        inv TID. eapply PROM_IN_MEM0.
          by rewrite IdentMap.gss. }
      rewrite IdentMap.gso in *; auto.
      etransitivity.
      { eapply PROM_IN_MEM; eauto. }
      eapply memory_add_le; eauto. }
    { etransitivity; [by apply SC_COV|].
      basic_solver. }
    { eapply max_value_same_set.
      { apply SC_REQ0; auto. }
      apply s_tm_n_f_steps.
      { apply TCCOH. }
      { basic_solver. }
      intros a [BB|BB] OO; [by desf|intros CC; subst].
      type_solver. }
    exists state'''; eexists. splits; simpls.
    { eapply tau_steps_rmw_is_xacq; eauto. }
    { rewrite IdentMap.gss. simpls. }
    { ins. eapply PROM_DISJOINT0; eauto.
      rewrite IdentMap.gso in *; eauto. }
    { red; ins. }
    { ins. }
    { eapply sim_tview_write_step; eauto.
      1,2: by apply CON.
      { intros a H. apply TCCOH in H. apply H. }
      { arewrite (covered T ⊆₁ coverable G sc T) by apply TCCOH.
        intros x y H. apply seq_eqv_r in H; destruct H as [H1 H2].
        apply H2. exists y; apply seq_eqv_r. desf. }
      { eapply sim_tview_f_issued; eauto. }
      { intros y [COVY TIDY].
        destruct (same_thread G w y) as [[EQ|SB]|SB]; auto.
        { apply TCCOH in COVY. apply COVY. }
        { desf. }
        exfalso. apply WNCOV. apply TCCOH in COVY. apply COVY.
        exists y. apply seq_eqv_r; split; auto. }
      { intros x y H. apply seq_eqv_r in H; desc; subst.
        apply NEXT. eexists. apply seq_eqv_r; split; eauto. }
      { erewrite Memory.add_o.
        { rewrite loc_ts_eq_dec_eq; eauto. }
        apply PADD. }
      simpls. }
    { cdes PLN_RLX_EQ.
      simpls. red. unfold TView.write_tview. simpls; splits.
      { by rewrite EQ_CUR. }
      { by rewrite EQ_ACQ. }
      ins. unfold LocFun.add, LocFun.find.
      destruct (Loc.eq_dec l locw).
      2: by rewrite EQ_REL.
      destruct (Ordering.le Ordering.acqrel (Event_imm_promise.wmod (Events.mod lab w))).
      all: unfold View.join; simpls.
        by rewrite EQ_CUR. }
    { desf. }
    red. splits; eauto.
    ins. rewrite INDEX_NRMW; auto.
    apply sim_state_cover_event; auto. }
  intros [PCSTEP SIMREL_THREAD']; split; auto.
  intros SMODE SIMREL.
  eapply simrel_f_issued in SIMREL; eauto.
  eapply full_simrel_step.
  13: by apply SIMREL.
  11: { ins. rewrite IdentMap.Facts.add_in_iff.
        split; auto. intros [|]; auto; subst.
        apply IdentMap.Facts.in_find_iff.
          by rewrite LLH. }
  all: eauto; simpls.
  8: by eapply msg_preserved_add; eauto.
  7: by eapply closedness_preserved_add; eauto.      
  rewrite coveredE; eauto.
  2: rewrite issuedE; eauto.
  all: basic_solver.
Qed.

End WritePlainStep.
