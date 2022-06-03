Require Import PArith Arith.
From hahn Require Import Hahn.
Require Import PromisingLib.
From Promising2 Require Import Configuration TView View Time Event Cell Thread Memory Local.
From imm Require Import Events.
From imm Require Import Execution.
From imm Require Import Execution_eco.
From imm Require Import imm_s_hb.
From imm Require Import imm_s.
From imm Require Import imm_bob imm_s_ppo.
From imm Require Import CombRelations.
From imm Require Import CombRelationsMore.
From imm Require Import ProgToExecution.
From imm Require Import FairExecution.

From imm Require Import TraversalOrder.
From imm Require Import TLSCoherency.
From imm Require Import IordCoherency.
From imm Require Import SimClosure. 
From imm Require Import AuxDef. 
Require Import TlsEventSets.
Require Import ExtTraversalConfig.
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
From imm Require Import AuxRel2.
Require Import MemoryClosedness.
Require Import SimulationRelProperties.
Require Import ExistsIssueInterval.
Require Import IssueNextStepHelper.
Require Import EventsTraversalOrder.
Require Import AuxRel.

Set Implicit Arguments.

(* TODO: move *)
Global Add Parametric Morphism G: (@dom_sb_S_rfrmw G) with signature
       (@set_equiv trav_label) ==> (@same_relation actid) ==> (@set_equiv actid)
                               ==> (@set_equiv actid) as dom_sb_S_rfrmw_more. 
Proof using. ins. unfold dom_sb_S_rfrmw. rewrite H, H0, H1. reflexivity. Qed.

Section IssuePlainStep.

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

(* TODO: move *)
Lemma dom_sb_S_rfrmw_union_S T r S1 S2:
  dom_sb_S_rfrmw G T r (S1 ∪₁ S2) ≡₁ dom_sb_S_rfrmw G T r S1 ∪₁ dom_sb_S_rfrmw G T r S2.
Proof using. unfold dom_sb_S_rfrmw. basic_solver 10. Qed. 

(* TODO: move *)
Lemma dom_sb_S_rfrmw_union_T T1 T2 r S:
  dom_sb_S_rfrmw G (T1 ∪₁ T2) r S ≡₁ dom_sb_S_rfrmw G T1 r S ∪₁ dom_sb_S_rfrmw G T2 r S.
Proof using. unfold dom_sb_S_rfrmw. rewrite reserved_union. basic_solver 10. Qed.

(* TODO: move to Eventstraversalorder, update proof of dom_detour_rfe_rmw_rfi_rmw_rt_I_in_I *)
Lemma dom_detour_rfe_rmw_rfi_rmw_rt_issuable_in_I T
      (TLSCOH: tls_coherent G T) (IORDCOH: iord_coherent G sc T):
  dom_rel ((((detour ∪ rfe) ⨾ (rmw ⨾ rfi)＊) ⨾ rmw) ⨾ ⦗issuable G sc T⦘) ⊆₁ issued T.
Proof using WF. 
  rewrite !seqA. seq_rewrite rt_seq_swap. rewrite seqA.
  assert (dom_rel ((rfi ⨾ rmw)＊ ⨾ ⦗issuable G sc T⦘) ⊆₁ (issuable G sc T)) as D2.
  { apply dom_rel_clos_refl_trans_eqv.
    transitivity (issued T); [| apply issued_in_issuable; auto].
    rewrite <- rf_ppo_loc_issuable_in_I with (sc := sc); eauto.
    rewrite rfi_in_rf, rmw_in_ppo_loc; auto. basic_solver. }
  apply dom_rel_helper in D2. rewrite D2.
  rewrite <- !seqA. do 2 rewrite dom_seq. rewrite seqA.

  unfold issuable. rewrite id_inter. rewrite <- !seqA. 
  apply dom_rel_iord_ext_parts.
  3: { erewrite init_issued; eauto. basic_solver. }
  2: { rewrite rmw_in_sb, detour_in_sb, wf_rfeE, wf_sbE, no_sb_to_init; basic_solver. }
  transitivity (AR G sc); [| unfold iord_simpl; basic_solver 10].
  unfold AR. hahn_frame. apply map_rel_mori; [done| ].
  rewrite (dom_l (wf_detourD WF)), (dom_l (wf_rfeD WF)), <- seq_union_r.
  erewrite eqv_rel_mori with (x := _ ∩₁ W); [| intro; apply proj2].
  hahn_frame. 
  rewrite <- ct_unit, <- ct_step. unfold ar. apply seq_mori.
  { unfold ar_int. basic_solver 10. }
  rewrite rmw_in_ar_int; auto. basic_solver 10. 
Qed. 

(* TODO: move to ExtTraversalConfig *)
Lemma reserve_coherent_add_issue_reserve T w
      (TCOH: tls_coherent G T)
      (ICOH: iord_coherent G sc T)
      (RCOH: reserve_coherent G T)
      (I'w: issuable G sc T w)
      :
      reserve_coherent G
    (T ∪₁ eq (mkTL ta_issue w) ∪₁ eq ta_reserve <*> (eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w))). 
Proof using.
  remember (T ∪₁ eq (mkTL ta_issue w) ∪₁ eq ta_reserve <*> (eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w))) as T'.
  assert (covered T' ≡₁ covered T) as COV' by (subst; simplify_tls_events; basic_solver).
  assert (issued T' ≡₁ issued T ∪₁ eq w) as ISS' by (subst; simplify_tls_events; basic_solver).
  assert (reserved T' ≡₁ reserved T ∪₁ eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w)) as RES' by (subst; simplify_tls_events; basic_solver).
  apply set_subset_eq in I'w as I'w_.
  assert (forall T r D, dom_sb_S_rfrmw G T r D ⊆₁ dom_rel (sb ⨾ ⦗reserved T⦘)) as DSS_HELPER. 
  { unfold dom_sb_S_rfrmw. ins. basic_solver. }

  pose proof RCOH as RCOH_. destruct RCOH_. 
  split; rewrite ?COV', ?ISS', ?RES'.
  { rewrite rcoh_S_in_E, ExtTraversalProperties.dom_sb_S_rfrmwE; auto.
    arewrite (eq w ⊆₁ E); [apply set_subset_eq, I'w| ]. basic_solver. }
  { rewrite rcoh_I_in_S. basic_solver. }
  { rewrite ExtTraversalProperties.dom_sb_S_rfrmw_in_W_ex.
    (* TODO: introduce tactic for relation simplification *)
    clear -rcoh_S_I_in_W_ex. relsf. splits; try basic_solver.
    generalize rcoh_S_I_in_W_ex. basic_solver. }
  { rewrite !id_union. repeat case_union _ _. rewrite !dom_union.
    repeat (apply set_subset_union_l; split; auto).
    { rewrite <- fwbob_issuable_in_C with (sc := sc); eauto.
      rewrite <- sb_from_f_in_fwbob. rewrite I'w_. basic_solver. }
    rewrite DSS_HELPER. rewrite <- seqA, dom_rel_eqv_dom_rel, seqA.
    by sin_rewrite sb_sb. }
  { remember (detour ∪ rfe) as REL. 
    rewrite !id_union. repeat case_union _ _. rewrite !dom_union.
    subst REL. repeat (apply set_subset_union_l; split).
    { rewrite rcoh_dr_R_acq_I. basic_solver. }
    { rewrite I'w_ at 1. rewrite dom_detour_rmwrfi_rfe_acq_sb_issuable; basic_solver. }
    rewrite DSS_HELPER. rewrite <- !seqA, dom_rel_eqv_dom_rel, seqA.
    sin_rewrite sb_sb.
    rewrite !seqA, rcoh_dr_R_acq_I. basic_solver. }
  { rewrite !id_union. repeat case_union _ _. rewrite !dom_union.
    repeat (apply set_subset_union_l; split; auto).
    { rewrite rcoh_W_ex_sb_I. basic_solver. }
    { rewrite I'w_ at 1. rewrite dom_wex_sb_issuable; basic_solver. }
    rewrite DSS_HELPER. rewrite <- !seqA, dom_rel_eqv_dom_rel, seqA.
    sin_rewrite sb_sb.
    rewrite rcoh_W_ex_sb_I. basic_solver. }
  { subst T'. rewrite !dom_sb_S_rfrmw_union_S, !dom_sb_S_rfrmw_union_T.
    repeat (apply set_subset_union_l; split).
    { rewrite rcoh_sb_S. basic_solver. }
    { unfold dom_sb_S_rfrmw. simplify_tls_events. basic_solver. }
    { 
      (* rewrite set_pair_union_r. rewrite dom_sb_S_rfrmw_union_T. *)
      (* apply set_subset_union_l; split. *)
      (* 2: { unfold dom_sb_S_rfrmw. simplify_tls_events. *)
      (*      unfolder. ins. desc. subst.  *)
      (*      (* ? *) *)
      (*      right. split. *)
      (*      { exists y0. splits; eauto. eapply sb_trans; eauto. } *)
      (*      eexists. splits; eauto. eexists. splits; eauto.  *)
       
      (* rewrite <- rcoh_sb_S. do 2 unionR left.   *)
      (* unfold dom_sb_S_rfrmw. apply set_subset_inter; [| basic_solver].  *)
      (* simplify_tls_events. *)
      (* erewrite dom_rel_mori. *)
      (* 2: { rewrite id_union. case_union _ _.  *)
      admit. }
    { admit. }
    { unfold dom_sb_S_rfrmw. simplify_tls_events. basic_solver. }
    { admit. }
  }
  { remember (detour ∪ rfe) as REL. remember (data ∪ rfi ∪ rmw) as REL'.
    rewrite !id_union. repeat case_union _ _. rewrite !dom_union.
    subst REL REL'. repeat (apply set_subset_union_l; split; auto).
    { rewrite rcoh_rppo_S. basic_solver. }
    { rewrite I'w_ at 1.
      sin_rewrite detour_rfe_data_rfi_rmw_rppo_in_detour_rfe_ppo; auto. 
      rewrite seqA. sin_rewrite dom_detour_rfe_ppo_issuable; basic_solver. }
    rewrite DSS_HELPER. rewrite <- !seqA, dom_rel_eqv_dom_rel, seqA.
    arewrite (rppo G ⨾ sb ⨾ ⦗reserved T⦘ ⊆ rppo G ⨾ ⦗reserved T⦘).
    { rewrite <- seq_eqvK at 1. hahn_frame.
      rewrite reservedW; eauto. apply rppo_sb_in_rppo; auto. }
    rewrite rcoh_rppo_S. basic_solver. }
  { rewrite !id_union. repeat case_union _ _. rewrite !dom_union.
    repeat (apply set_subset_union_l; split; auto).
    { rewrite rcoh_d_rmw_S. basic_solver. }
    { unionR left. 
      rewrite <- dom_detour_rfe_rmw_rfi_rmw_rt_issuable_in_I; eauto.
      rewrite I'w_. apply dom_rel_mori. hahn_frame. }
    unfold dom_sb_S_rfrmw. 
    (* can be proved if we assume RMWREX *)
    admit. }
  repeat rewrite set_inter_union_l. repeat (apply set_subset_union_l; split; auto).
  { rewrite rcoh_S_W_ex_rfrmw_I. basic_solver 10. }
  { red. intros ? [<- WEXw]. red in WEXw.
    destruct WEXw as [r RMWrw].
    cdes CON. specialize (Comp r). specialize_full Comp.
    { erewrite same_relation_exp in RMWrw; [| rewrite wf_rmwD, wf_rmwE; eauto].
      generalize RMWrw. clear. basic_solver. }
    destruct Comp as [w' RFw'r].
    exists w'. apply seq_eqv_l. split; [| basic_solver]. left.
    eapply rfrmw_coverable_issuable_in_I; eauto.
    exists w. apply seqA. eexists. split; [basic_solver| ]. vauto. } 
  unfold dom_sb_S_rfrmw. rewrite rfi_in_rf. basic_solver 10.
Admitted. 
        

      

Lemma issue_rlx_step_next PC T f_to f_from thread w wnext smode
      (SIMREL_THREAD : simrel_thread G sc PC T f_to f_from thread smode)
      (TSTEP : ext_itrav_step
                 G sc (mkTL ta_issue w) T
                 (* (mkETC *)
                 (*    (mkTC (covered T) (issued T ∪₁ eq w)) *)
                 (*    (S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G (mkETC T S) rfi (eq w))) *)
                 (T ∪₁ eq (mkTL ta_issue w) ∪₁ (eq ta_reserve <*> (eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w))))
      )
      (NWEX : ~ W_ex w)
      (NREL : ~ Rel w)
      (NEXT : dom_sb_S_rfrmw G T rfi (eq w) wnext)
      (WTID : thread = tid w)
      (FAIR: mem_fair G)
  :
  exists f_to' f_from' PC',
    ⟪ PCSTEP : (plain_step MachineEvent.silent thread)⁺ PC PC' ⟫ /\
    ⟪ SIMREL_THREAD : simrel_thread G sc PC' (T ∪₁ eq (mkTL ta_issue w) ∪₁ (eq ta_reserve <*> (eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w)))) f_to' f_from' thread smode ⟫ /\
    ⟪ SIMREL :
        smode = sim_normal -> simrel G sc PC T f_to f_from ->
        simrel G sc PC' (T ∪₁ eq (mkTL ta_issue w) ∪₁ (eq ta_reserve <*> (eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w)))) f_to' f_from' ⟫.
Proof using WF CON.
  cdes SIMREL_THREAD. cdes COMMON. cdes LOCAL.
  subst.
  remember (T ∪₁ eq (mkTL ta_issue w) ∪₁ (eq ta_reserve <*> (eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w)))) as T'. 
  
  assert (~ issued T w) as NISSB.
  { eapply ext_itrav_step_iss_nI; eauto. }
  assert (issuable G sc T w) as ISSUABLE.
  { eapply ext_itrav_step_iss_issuable; eauto. }
  assert (reserved T ⊆₁ E ∩₁ W) as SEW.
  { apply set_subset_inter_r. split; [by apply RCOH|].
    eapply reservedW; eauto. }
  assert (E w /\ W w) as [EW WW] by (by apply ISSUABLE).
  assert (~ is_init w) as NINIT.
  { intros AA. apply NISSB. eapply init_issued; eauto. by split. }

  assert (exists locw, loc lab w = Some locw) as [locw WLOC] by (by apply is_w_loc).
  assert (exists valw, val lab w = Some valw) as [valw WVAL] by (by apply is_w_val).
  
  assert (NSW : ~ reserved T w).
  { intros HH. apply NWEX. apply RCOH. by split. }
  
  edestruct issue_step_helper_next as [p_rel]; eauto. simpls; desf.
  set (rel'' := TView.rel (Local.tview local) locw).
  set (rel' := (View.join (View.join rel'' (View.unwrap p_rel))
                          (View.singleton_ur locw (f_to' w)))).

  set (pe1 :=
         ThreadEvent.promise
           locw (f_from' w) (f_to' w) (Message.full valw (Some rel'))
           Memory.op_kind_add).
  set (pe2 :=
         ThreadEvent.promise
           locw (f_from' wnext) (f_to' wnext) Message.reserve
           Memory.op_kind_add).
  
  assert (Memory.closed_message (Message.full valw (Some rel')) memory_add) as CLOS_MSG.
  { by do 2 constructor. }
  
  exists f_to', f_from'. eexists.
  apply and_assoc. apply pair_app; unnw.
  { split.
    { eapply t_trans; eapply t_step.
      { set (pe' := MachineEvent.silent).
        arewrite (pe' = ThreadEvent.get_machine_event pe1) by simpls.
        eapply plain_step_intro with (lang:=thread_lts (tid w)); eauto.
        2: by unfold pe1; clear; desf.
        apply Thread.step_promise.
        constructor.
        2: by simpls.
        econstructor; eauto. }
      set (pe' := MachineEvent.silent).
      arewrite (pe' = ThreadEvent.get_machine_event pe2) by simpls.
      eapply plain_step_intro with (lang:=thread_lts (tid w)); eauto.
      { simpls. rewrite IdentMap.gss. eauto. }
      2: by unfold pe2; clear; desf.
      apply Thread.step_promise.
      constructor.
      2: by simpls.
      econstructor; eauto. }
    destruct (is_rel lab w) eqn:RELB; [by desf|].
    subst.
    red; splits; red; splits; eauto; simpls.
    all: try (rewrite IdentMap.add_add_eq; eauto).
    { apply TSTEP. }
    { generalize RELB RELCOV. clear. basic_solver. }
    { do 2 (eapply Memory.add_closed; eauto). }
    simpls.
    exists state; eexists.
    rewrite IdentMap.gss.
    splits; eauto.
    { simpls. eapply sim_tview_f_issued with (f_to:=f_to); eauto. }
    do 2 (eapply tview_closedness_preserved_add; eauto). }
  assert (IdentMap.In (tid w) (Configuration.threads PC)) as INTT.
  { apply IdentMap.Facts.in_find_iff. rewrite LLH. desf. }

  intros [PCSTEP SIMREL_THREAD']; split; auto.
  intros SMODE SIMREL.
  subst. desc. red.
  splits; [by apply SIMREL_THREAD'|].
  simpls. ins.
  destruct (classic (thread = tid w)) as [|TNEQ]; subst.
  { apply SIMREL_THREAD'. }
  set (AA:=TP).
  apply IdentMap.Facts.add_in_iff in AA.
  destruct AA as [AA|AA]; subst; auto.
  { apply SIMREL_THREAD'. }
  apply IdentMap.Facts.add_in_iff in AA.
  destruct AA as [AA|AA]; subst; auto.
  { exfalso. by apply TNEQ. }
  apply SIMREL in AA. cdes AA.
  eapply simrel_thread_local_step with (thread:=tid w) (PC:=PC) (T:=T) (S:=S); eauto.
  10: { simpls. eapply msg_preserved_trans; eapply msg_preserved_add; eauto. }
  9: { simpls. eapply closedness_preserved_trans; eapply closedness_preserved_add; eauto. }
  8: by eapply same_other_threads_steps; eauto.
  all: simpls; eauto.
  { eapply coveredE; eauto. }
  { rewrite issuedE; eauto. generalize EW. clear. basic_solver. }
  1-4: clear; basic_solver.
  { rewrite dom_sb_S_rfrmw_same_tid; auto. clear. basic_solver. }
  { ins.
    destruct (classic (thread0 = tid w)); subst.
    { split; ins; auto. apply IdentMap.Facts.add_in_iff; eauto. }
    split; intros HH; auto.
    { apply IdentMap.Facts.add_in_iff; eauto. right.
      apply IdentMap.Facts.add_in_iff; eauto. }
    apply IdentMap.Facts.add_in_iff in HH. desf.
    apply IdentMap.Facts.add_in_iff in HH. desf. }
  { apply IdentMap.Facts.add_in_iff in TP. destruct TP as [HH|HH]; auto; subst.
    { clear -TNEQ. desf. }
    apply IdentMap.Facts.add_in_iff in HH. destruct HH; eauto; subst.
    clear -TNEQ. desf. }
  { eapply sim_prom_f_issued; eauto. }
  { red. ins. apply SIM_RPROM0 in RES. desc.
    assert (b <> w) as NBW.
    { intros HH; subst. clear -TNEQ. desf. }
    exists b. splits; auto.
    { rewrite REQ_FROM; auto. }
    rewrite REQ_TO; eauto. }
  { eapply sim_mem_f_issued; eauto. }
  { ins.
    assert (b <> w) as BNW.
    { intros HH. subst. clear -TNEQ. desf. }
    rewrite REQ_TO; eauto.
    rewrite REQ_FROM; eauto.
    apply SIM_RES_MEM1; auto. }
  eapply sim_tview_f_issued; eauto.
Qed.

End IssuePlainStep.
