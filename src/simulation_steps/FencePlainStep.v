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

From imm Require Import AuxRel.
From imm Require Import AuxRel2.
From imm Require Import TraversalOrder. 
From imm Require Import TLSCoherency.
From imm Require Import IordCoherency.
From imm Require Import SimClosure.
From imm Require Import TlsEventSets.
From imm Require Import Next. 
Require Import ExtTraversalConfig.
Require Import ExtTraversal.
Require Import ExtTraversalProperties.
From imm Require Import TlsViewRelHelpers.
Require Import PlainStepBasic.
Require Import MemoryAux.
Require Import SimulationRel.
Require Import SimulationRelProperties. 
Require Import SimState.
Require Import SimStateHelper.
Require Import PromiseLTS.
Require Import MaxValue.
Require Import ViewRel.
Require Import SimulationPlainStepAux.
Require Import FtoCoherent.
From imm Require Import EventsTraversalOrder.

Set Implicit Arguments.

Section FenceStep.

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

Lemma fence_step PC T f_to f_from thread f smode
      (SIMREL_THREAD : simrel_thread G sc PC T f_to f_from thread smode)
      (TID : tid f = thread)
      (TSTEP: ext_itrav_step G sc (mkTL ta_cover f) T (T ∪₁ eq (mkTL ta_cover f)))
      (TYPE : F f):
  let T' := (T ∪₁ eq (mkTL ta_cover f)) in
  exists PC',
    ⟪ PCSTEP : plain_step MachineEvent.silent thread PC PC' ⟫ /\
    ⟪ SIMREL_THREAD : simrel_thread G sc PC' T' f_to f_from thread smode ⟫ /\
    ⟪ SIMREL :
        smode = sim_normal -> simrel G sc PC T f_to f_from ->
        simrel G sc PC' T' f_to f_from ⟫.
Proof using WF CON.
  cdes SIMREL_THREAD. cdes COMMON. cdes LOCAL.

  assert (COV : coverable G sc T f).
  { eapply ext_itrav_step_cov_coverable in TSTEP; eauto. }
  assert (NEXT : next G (covered T) f).
  { eapply ext_itrav_step_cov_next in TSTEP; eauto. }

  assert (sc_per_loc G) as SC_PER_LOC.
  { by apply coherence_sc_per_loc; cdes CON. }

  assert (~ covered T f) as FNCOV.
  { apply NEXT. }

  cdes STATE. rewrite <- TID in *.
  edestruct sim_state_to_events as [ev HH]; eauto.
  desc.

  apply clos_rt_rt1n in ESTEPS.
  eapply (rtc_lang_tau_step_rtc_thread_tau_step
            _ _ _ local (Configuration.sc PC) (Configuration.memory PC)) in ESTEPS.

  assert (E f) as FACT.
  { apply NEXT. }

  assert (exists ordf, lab f = Afence ordf) as FPARAMS; desc.
  { unfold is_f in TYPE.
    destruct (lab f); desf; eexists; eauto. }

  assert (~ is_init f) as FNINIT.
  { intros H; apply (init_w WF) in H. type_solver. }
  
  assert (~ dom_rel rmw f) as NRMW.
  { intros [x HH].
    apply (dom_l (wf_rmwD WF)) in HH. apply seq_eqv_l in HH.
    type_solver. }
  
  assert (Event_imm_promise.same_g_events lab (f :: nil) ev) as SAME.
  { by apply SAME_NRMW. }
  
  assert (exists ordr ordw, ev = ProgramEvent.fence ordr ordw)
    as [ordr [ordw EV]].
  { red in SAME; red in SAME; simpls.
    rewrite FPARAMS in *; simpls.
    destruct ev; vauto. }
  set (pe := ThreadEvent.fence ordr ordw).
  assert (ev = ThreadEvent.get_program_event pe) as EV'.
  { done. }
  
  assert (Ordering.le Ordering.acqrel ordw ->
          forall l to, Memory.get l to (Local.promises local) = None) as REL_NO_PROM.
  { intros ORD l to.
    destruct (Memory.get l to (Local.promises local)) as [[from msg]|] eqn: HH; auto.
    exfalso.
    assert (exists w,
               ⟪ EW : E w ⟫ /\
               ⟪ WW : W w ⟫ /\
               ⟪ NCOV : ~ covered T w ⟫ /\
               ⟪ WTID : tid w = tid f ⟫ /\
               ⟪ WS   : dom_rel (⦗F ∩₁ Acq/Rel⦘ ⨾ sb ⨾ ⦗eq w⦘) ⊆₁ covered T ⟫).
    { destruct msg as [val rel|].
      { edestruct SIM_PROM as [w]; eauto; desc.
        (* apply TCCOH in ISS. *)
        exists w. splits; auto.
        { eapply issuedW; eauto. }
        sin_rewrite sb_from_f_in_fwbob.
        rewrite <- fwbob_I_in_C; eauto.
        basic_solver. }
      edestruct SIM_RPROM as [w]; eauto; desc.
      assert (W w) as WW.
      { eapply (reservedW WF); eauto. }
      exists w. splits; auto.
      { intros NCOV. apply NOISS. eapply w_covered_issued; eauto.
        split; auto. }
      rewrite <- rcoh_F_sb_S; eauto. clear -RES. basic_solver 10. }
    desc.
    edestruct (same_thread G w f) as [SBB|SBB]; eauto.
    { intros H. apply NCOV. eapply init_covered; eauto. by split. }
    { destruct SBB as [|SBB]; [subst; type_solver|].
      exfalso. apply NCOV.
      eapply NEXT. eexists; apply seq_eqv_r; split; eauto. }
    apply FNCOV. apply WS. exists w.
    apply seq_eqv_lr. splits; auto.
    split; auto. subst.
    clear -ORD SAME FPARAMS.
    unfold is_ra, is_acq, is_rel, mode_le, Events.mod.
    red in SAME; red in SAME; simpls;
      rewrite FPARAMS in *; simpls.
    unnw. red in SAME. desf; desf. }

  assert (Ordering.le Ordering.acqrel ordw <-> Ordering.le Ordering.strong_relaxed ordw)
    as REL_SRLX.
  { subst. clear -SAME FPARAMS.
    unfold mode_le, Events.mod.
    red in SAME; red in SAME; simpls;
      rewrite FPARAMS in *; simpls; desf.
    unnw; red in SAME.
    desf; desf. }
  clear TID.
  eexists.
  apply and_assoc. apply pair_app; unnw.
  { split.
    { set (pe' := MachineEvent.silent).
      assert (pe' = ThreadEvent.get_machine_event pe) as H.
      { unfold pe. simpls. }
      rewrite H. clear H.
      econstructor; eauto.
      apply Thread.step_program.
      constructor.
      { rewrite EV' in STEP; eauto. }
      unfold pe; eapply Local.step_fence.
      2: done.
      econstructor; eauto.
      intros ORD_SRLX l; red.
      intros from to msg MSG.
      exfalso. (* There should be no promised message. *)
      apply REL_SRLX in ORD_SRLX.
      specialize (REL_NO_PROM ORD_SRLX l to).
      desf. }
    red; splits; red; splits; simpls.
    1-3: by apply TSTEP.
    { clear -RELCOV. simplify_tls_events. rewrite RELCOV. basic_solver. } 
    { intros. apply wf_rmwD, seq_eqv_lr in RMW; eauto. desc.
      specialize (RMWCOV _ _ RMW0). 
      split.
      all: intros [? | ->%covered_singleton]%covered_union; [| type_solver];
        apply covered_union; left; by apply RMWCOV. }
    { intros e' EE. 
      apply IdentMap.Facts.add_in_iff.
      destruct (Ident.eq_dec e' (tid f)) as [|NEQ]; subst; auto. }
    { ins.
      destruct (Ident.eq_dec thread' (tid f)) as [EQ|NEQ].
      { subst. rewrite IdentMap.gss in TID.
        assert (Local.promises local0 = Local.promises local) as H.
        { inv TID. }
        rewrite H.
        eapply PROM_IN_MEM; eauto. }
      red; ins. rewrite IdentMap.gso in TID; auto.
      eapply PROM_IN_MEM; eauto. }
    { by simplify_tls_events. }
    { ins; subst. rewrite SC_COV; auto.
      clear. simplify_tls_events. basic_solver. }
    { ins; subst. 
      simplify_tls_events. eapply sim_sc_fence_step; eauto.
      red in SAME; red in SAME; simpls.
      rewrite FPARAMS in *; simpls. }
    { eapply reserved_time_same_issued_reserved; eauto.
      all: clear; by simplify_tls_events. } 
    { unfold TView.read_fence_tview, TView.write_fence_sc; simpls.
      red. splits; simpls.
      all: desf; ins.
      all: repeat (apply Memory.join_closed_timemap).
      all: try apply MEM_CLOSE.
      all: try by apply CLOSED_SC. }
    rewrite IdentMap.gss.
    eexists; eexists; eexists; splits; eauto; simpls.
    { erewrite tau_steps_step_same_instrs; eauto. }
    { ins.
      rewrite IdentMap.gso in TID'; auto.
      eapply PROM_DISJOINT; eauto. }
    { red. ins.
      (* TODO: generalize the proof! It's used a couple of times. *)
      edestruct SIM_PROM as [w]; eauto.

      exists w; desc; auto.
      assert (W w) as WW.
      { eapply issuedW; eauto. }
      splits; eauto. 
      { clear -ISS. find_event_set. }
      assert (f <> w) as NEQ by (intros ->; type_solver 10). 
      clear -NCOV NEQ. separate_set_event. }
    { eapply sim_res_prom_issued_reserved_subset; [..| apply SIM_RPROM].
      all: clear; by simplify_tls_events. }
    { red; splits; simpls.
      eapply set_equiv_exp in ISSB; [| by simplify_tls_events]. 
      edestruct SIM_MEM as [rel]; eauto.
      simpls; desc.
      exists rel; splits; auto.
      intros TIDBF COVBF. 
      assert (~ covered T b) as COVB.
      { intros B; apply COVBF. clear -B. find_event_set. }
      destruct H1 as [PROM REL]; auto; unnw; splits; auto.
      subst. 
      destruct (Ordering.le Ordering.acqrel ordw) eqn: LL; auto.
      { exfalso. rewrite REL_NO_PROM in PROM; desf. }
      desc. eexists. splits; eauto. des; [left | right]; splits; eauto.
      { intros CB. apply REL0. eapply set_equiv_exp; [| apply CB].
        clear. by simplify_tls_events. }
      eexists. splits; eauto. clear -REL0. find_event_set. }
    
    (***)
    { red; simpls. ins.
      eapply set_equiv_exp in RESB; [| by simplify_tls_events].
      eapply set_equiv_exp with (x := b) in NISSB.
      2: { apply set_equiv_compl. clear. simplify_tls_events. reflexivity. }
      edestruct SIM_RES_MEM as [rel]; eauto. }    
    { simplify_tls_events. 
      eapply sim_tview_fence_step; eauto.
      { red in SAME; red in SAME; simpls.
        rewrite FPARAMS in *; desf. }
      intros H. apply SC_REQ.
      destruct smode; auto.
      exfalso. apply H. by apply SC_COV. }
    { cdes PLN_RLX_EQ. 
      unfold TView.read_fence_tview, TView.write_fence_tview.
      red; splits; simpls.
       all: desf; simpls.
      all: try rewrite EQ_CUR.
      all: try rewrite EQ_ACQ.
      all: reflexivity. }
    { unfold TView.read_fence_tview, TView.write_fence_tview, TView.write_fence_sc; simpls.
      red; splits; simpls.
      all: desf; ins.
      all: repeat (apply Memory.join_closed_timemap).
      all: try apply MEM_CLOSE.
      all: try apply CLOSED_SC.
      all: by apply Memory.closed_timemap_bot. }
    red. splits; eauto.
    ins. rewrite INDEX_NRMW; auto.
    etransitivity; [eapply set_equiv_exp; by simplify_tls_events| ].     
    apply sim_state_cover_event; auto. }
  intros [PCSTEP SIMREL_THREAD']; split; auto.
  intros SMODE SIMREL.
  eapply full_simrel_step with (T := T); eauto.
  1-8: clear -TLSCOH FACT WF; simplify_tls_events; try basic_solver.
  { rewrite coveredE; basic_solver. }
  { rewrite issuedE; basic_solver. }
  (* 5: by apply SIMREL. *)
  4: { ins. rewrite IdentMap.Facts.add_in_iff.
        split; auto. intros [|]; auto; subst.
        apply IdentMap.Facts.in_find_iff. by rewrite LLH. }
  3: by eapply msg_preserved_refl; eauto.
  { by eapply same_other_threads_step; eauto. }
  simpls; eauto. subst. apply SIMREL_THREAD'. 
Qed.

End FenceStep.
