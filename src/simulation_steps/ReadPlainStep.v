Require Import PArith Arith.
From hahn Require Import Hahn.
Require Import PromisingLib.
From Promising2 Require Import Configuration TView View Time Event Cell Thread Memory Local.

From imm Require Import Events.
From imm Require Import Execution.
From imm Require Import Execution_eco.
From imm Require Import imm_s.
From imm Require Import imm_s_hb.
From imm Require Import imm_bob imm_s_ppo.
From imm Require Import ProgToExecution.
From imm Require Import CombRelations CombRelationsMore.
From imm Require Import Prog.
From imm Require Import ProgToExecution.
From imm Require Import SimClosure.

Require Import AuxRel.
From imm Require Import AuxRel2.
From imm Require Import TraversalOrder. 
From imm Require Import TLSCoherency.
From imm Require Import IordCoherency.
Require Import TlsEventSets.
Require Import ExtTraversalConfig.
Require Import ExtTraversal.
Require Import ViewRelHelpers.
Require Import PlainStepBasic.
Require Import MemoryAux.
Require Import SimulationRel.
Require Import SimState.
Require Import SimStateHelper.
Require Import PromiseLTS.
Require Import MaxValue.
Require Import ViewRel.
Require Import SimulationPlainStepAux.
Require Import FtoCoherent.
Require Import ReadPlainStepHelper.
Require Import Next.
Require Import EventsTraversalOrder.

Set Implicit Arguments.

Section ReadPlainStep.

Variable G : execution.
Variable WF : Wf G.
Variable sc : relation actid.
Variable CON : imm_consistent G sc.

Notation "'E'" := (acts_set G).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'rmw'" := (rmw G).
Notation "'data'" := (data G).
Notation "'addr'" := (addr G).
Notation "'ctrl'" := (ctrl G).

Notation "'fr'" := (fr G).
Notation "'coe'" := (coe G).
Notation "'coi'" := (coi G).
Notation "'deps'" := (deps G).
Notation "'rfi'" := (rfi G).
Notation "'rfe'" := (rfe G).
Notation "'detour'" := (detour G).
Notation "'hb'" := (hb G).
Notation "'sw'" := (sw G).

Notation "'lab'" := (lab G).
(* Notation "'loc'" := (loc lab). *)
(* Notation "'val'" := (val lab). *)
(* Notation "'mod'" := (mod lab). *)
(* Notation "'same_loc'" := (same_loc lab). *)

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
Notation "'W_ex'" := (W_ex G).
Notation "'W_ex_acq'" := (W_ex ∩₁ (fun a => is_true (is_xacq lab a))).

Lemma read_step PC T f_to f_from thread r smode
      (SIMREL_THREAD : simrel_thread G sc PC T f_to f_from thread smode)
      (TID : tid r = thread)
      (TSTEP : ext_itrav_step
                 G sc (mkTL ta_cover r) T (T ∪₁ eq (mkTL ta_cover r)))
      (TYPE : R r)
      (NRMW : ~ dom_rel rmw r):
  let T' := (T ∪₁ eq (mkTL ta_cover r)) in
  exists PC',
    ⟪ PCSTEP : plain_step MachineEvent.silent thread PC PC' ⟫ /\
    ⟪ SIMREL_THREAD : simrel_thread G sc PC' T' f_to f_from thread smode ⟫ /\
    ⟪ SIMREL :
        smode = sim_normal -> simrel G sc PC T f_to f_from ->
        simrel G sc PC' T' f_to f_from ⟫.
Proof using WF CON.
  cdes SIMREL_THREAD. cdes COMMON. cdes LOCAL.

  assert (COV : coverable G sc T r).
  { eapply ext_itrav_step_cov_coverable; eauto. }
  assert (NEXT : next G (covered T) r).
  { eapply ext_itrav_step_cov_next; eauto. }

  assert (sc_per_loc G) as SC_PER_LOC.
  { by apply coherence_sc_per_loc; cdes CON. }

  assert (~ covered T r) as RNCOV.
  { apply NEXT. }
  
  cdes STATE. rewrite <- TID in *.
  edestruct sim_state_to_events as [ev HH]; eauto.
  desc.

  apply clos_rt_rt1n in ESTEPS.
  eapply (rtc_lang_tau_step_rtc_thread_tau_step
            _ _ _ local (Configuration.sc PC) (Configuration.memory PC)) in ESTEPS.

  assert (E r) as RACT.
  { apply NEXT. }
  assert (~ is_init r) as RNINIT.
  { intros H; apply (init_w WF) in H. type_solver. }
  assert (Rlx r) as RRLX.
  { apply ALLRLX. by split. }

  assert (exists locr, loc lab r = Some locr) as [locr RLOC].
  { unfold loc. desf; eauto. type_solver. }
  assert (exists valr, val lab r = Some valr) as [valr RVAL].
  { unfold val. desf; eauto. type_solver. }
  assert (exists xrmw, rmwmod lab r = Some xrmw) as [xrmw RXRMW].
  { unfold rmwmod. desf; eauto. all: type_solver. }
  
  assert (lab r = Aload xrmw (Events.mod lab r) locr valr) as PARAMS.
  { unfold loc, val, Events.mod, rmwmod in *. desf. }

  assert (exists w, rf w r) as [w RF].
  { by cdes CON; eapply Comp; split. }

  assert (issued T w) as WISS.
  { eapply dom_rf_coverable; eauto. basic_solver 10. }

  assert (loc lab w = Some locr) as WPLOC.
  { assert (loc lab w = loc lab r) as HH.
    { by apply (wf_rfl WF). }
      by rewrite HH. }
  assert (val lab w = Some valr) as WPVAL.
  { assert (val lab w = val lab r) as HH.
    { by apply wf_rfv. }
      by rewrite HH. }

  assert (W w) as WPWRITE.
  { apply (wf_rfD WF) in RF. apply seq_eqv_l in RF; desf. }
  assert (E w) as WPACT.
  { apply (wf_rfE WF) in RF. apply seq_eqv_l in RF; desf. }

  cdes SIM_MEM.
  edestruct SIM_MEM0 with (b:=w) as [rel DOM']; eauto.
  desc.

  assert (Event_imm_promise.same_g_events lab (r :: nil) ev) as SAME.
  { by apply SAME_NRMW. }
  
  assert (ev = ProgramEvent.read locr valr (Event_imm_promise.rmod (Events.mod lab r))) as EV.
  { red in SAME; red in SAME; simpls.
    rewrite PARAMS in *.
    destruct ev; desf; vauto. }

  set (pe := ThreadEvent.read locr (f_to w) valr rel (Event_imm_promise.rmod (Events.mod lab r))).
  assert (ev = ThreadEvent.get_program_event pe) as EV'.
  { done. }

  assert (Ordering.le Ordering.relaxed (Event_imm_promise.rmod (Events.mod lab r))) as RLX_ORDR.
  { unfold is_rlx, mode_le in *.
    destruct (Events.mod lab r); simpls. }
  
  assert (forall y : actid, covered T y /\ tid y = tid r -> sb y r) as COVSB.
  { intros y [COVY TIDY].
    destruct (same_thread G r y) as [[ST|ST]|ST]; subst; auto.
    { eapply coveredE; eauto. }
    { done. }
    assert (covered T r) as CC.
    2: by apply NEXT in CC.
    eapply dom_sb_covered; eauto. basic_solver 10. }
  
  eexists.
  apply and_assoc. apply pair_app.
  { split.
    { set (pe' := MachineEvent.silent).
      assert (pe' = ThreadEvent.get_machine_event pe) as H.
      { unfold pe. simpls. }
      rewrite H. clear H.
      econstructor; eauto.
      apply Thread.step_program.
      constructor.
      { rewrite EV' in STEP; eauto. }
      unfold pe; eapply Local.step_read.
      econstructor; eauto.
      assert
        (Time.le (View.rlx (TView.cur (Local.tview local)) locr) (f_to w))
        as PP.
      2: constructor; auto.
      2: by cdes PLN_RLX_EQ; rewrite EQ_CUR.
      edestruct (max_event_cur) as [a_max]; eauto; desc.
      assert (E a_max) as EA.
      { apply (wf_urrE WF) in CCUR.
        revert CCUR; unfold seq; unfolder; ins; desf.
        apply CON. }
      assert (issued T a_max) as AISS.
      { assert (A: (urr G sc locr ⨾ ⦗coverable G sc T⦘) a_max r).
        by basic_solver.
        apply (urr_coverable) in A; try done.
        2: { by apply CON. }
        revert A; unfold seq; unfolder; ins; desf. }
      
      destruct (classic (a_max = w)) as [AWEQ|AWNEQ]; [by desf|].
      edestruct (@wf_co_total G WF (Some locr) a_max) as [AWCO|AWCO].
      3: apply AWNEQ.
      2: basic_solver.
      apply set_interA; split; auto.
      hahn_rewrite (@wf_urrD G sc locr) in CCUR.
      revert CCUR; clear; basic_solver 12.
      3: by subst.
      { etransitivity; eauto.
        cdes FCOH.
        apply Time.le_lteq; left. eapply f_to_co_mon; eauto.
        all: by eapply rcoh_I_in_S; eauto. }
      exfalso.
      eapply transp_rf_co_urr_irr; eauto.
      1-3: by apply CON.
      exists w; split.
      { right; red; apply RF. }
      exists a_max; split; eauto. }
    edestruct (@read_step_helper G WF sc CON); eauto.
    { done. }
    desc. unnw.
    red; splits; red; splits; simpls; eauto.
    { intros. apply (wf_rmwD WF) in RMW.
      apply seq_eqv_l in RMW; destruct RMW as [RR RMW].
      apply seq_eqv_r in RMW; destruct RMW as [RMW WW].
      split; intros [HH|HH%covered_singleton]%covered_union; apply covered_union; left; auto.
      { erewrite <- RMWCOV; eauto. }
      { subst. exfalso. apply NRMW. basic_solver 10. }
      { erewrite RMWCOV; eauto. }
      type_solver. }
    { eapply f_to_coherent_more; [..| apply FCOH]; eauto.
      clear. by simplify_tls_events. }
    rewrite IdentMap.gss.
    eexists; eexists; eexists; splits; eauto; simpls.
    { erewrite tau_steps_step_same_instrs; eauto. }
    { ins.
      rewrite IdentMap.gso in TID'; auto.
      eapply PROM_DISJOINT; eauto. }
    { eapply sim_res_prom_issued_reserved_subset; [..| apply SIM_RPROM]; eauto.
      all: clear; by simplify_tls_events. }
    { eapply sim_res_mem_issued_reserved_subsets; [..| apply SIM_RES_MEM]; eauto.
      all: clear; by simplify_tls_events. }
    red. splits; eauto.
    ins. rewrite INDEX_NRMW; auto.
    etransitivity; [apply set_equiv_exp; clear; by simplify_tls_events| ]. 
    apply sim_state_cover_event; auto. }
  intros [PCSTEP SIMREL_THREAD']; split; auto.
  intros SMODE SIMREL.
  eapply full_simrel_step.
  17: by apply SIMREL.
  15: { ins. rewrite IdentMap.Facts.add_in_iff.
        split; auto. intros [|]; auto; subst.
        apply IdentMap.Facts.in_find_iff.
          by rewrite LLH. }
  14: by eapply msg_preserved_refl; eauto.
  11: by eapply same_other_threads_step; eauto.
  all: simpls; eauto.
  9: { subst. vauto. }
  all: clear -RACT TLSCOH WF; simplify_tls_events.
  1: generalize RACT; rewrite coveredE; eauto.
  2: rewrite issuedE; eauto. 
  all: basic_solver. 
Qed.

End ReadPlainStep.
