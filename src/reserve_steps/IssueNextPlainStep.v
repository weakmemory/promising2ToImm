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
      

(* TODO: move to IMM*)  
Lemma iord_no_reserve:
  iord G sc ≡ restr_rel (set_compl (action ↓₁ eq ta_reserve)) (iord G sc).
Proof using.
  rewrite restr_relE. split; [| basic_solver]. apply dom_helper_3.
  unfold iord. iord_dom_unfolder; ins; subst; vauto. 
Qed.

(* TODO: move to IMM*)  
Lemma iord_coherent_equiv_wo_reserved T1 T2
      (EQ': T1 \₁ action ↓₁ eq ta_reserve ≡₁ T2 \₁ action ↓₁ eq ta_reserve)
      (ICOH: iord_coherent G sc T1):
  iord_coherent G sc T2. 
Proof using. 
  red. red in ICOH.
  rewrite iord_no_reserve, restr_relE in *.
  rewrite !seqA, seq_eqvC, <- id_inter in *.
  transitivity (T2 \₁ action ⋄₁ eq ta_reserve); [| basic_solver].
  rewrite <- EQ'. rewrite !set_minusE in EQ'. rewrite EQ' in ICOH.
  rewrite set_minusE. apply set_subset_inter_r. split; [| basic_solver].
  rewrite ICOH. basic_solver. 
Qed.

(* TODO: move to IMM *)
Global Add Parametric Morphism : msg_rel with signature
       eq ==> (@same_relation actid) ==> eq ==>
          (@same_relation actid) as msg_rel_more. 
Proof using. ins. unfold msg_rel. rewrite H. basic_solver. Qed. 

(* TODO: move*)
Global Add Parametric Morphism : sim_prom with signature
       eq ==> (@same_relation actid) ==> (@set_equiv trav_label) ==> eq ==> eq ==> eq
          ==> (@set_subset Memory.t) as sim_prom_more_impl. 
Proof using.
  ins. unfold sim_prom. red. ins.
  specialize (H1 l to from v rel PROM). desc.
  eexists. splits; eauto.
  { eapply issued_more; [symmetry| ]; eauto. }
  { intros ?. apply NCOV. eapply covered_more; eauto. }
  red in HELPER. desc. 
  red. splits; eauto.
  red in SIMMSG. red. ins. specialize (SIMMSG l0).
  eapply max_value_more; eauto.
  eapply set_equiv_union; [| basic_solver].
  enough (msg_rel y y0 l0 ≡ msg_rel y x l0) by (generalize H1; basic_solver). 
  apply msg_rel_more; auto. by symmetry. 
Qed. 
  
(* TODO: move*)
Global Add Parametric Morphism : sim_prom with signature
       eq ==> (@same_relation actid) ==> (@set_equiv trav_label) ==> eq ==> eq ==> eq
          ==> (@set_equiv Memory.t) as sim_prom_more. 
Proof using. 
  ins. split; apply sim_prom_more_impl; auto; by symmetry. 
Qed. 

(* TODO: move*)
Global Add Parametric Morphism : sim_res_prom with signature
       eq ==> (@set_equiv trav_label) ==> eq ==> eq ==> eq
          ==> (@set_subset Memory.t) as sim_res_prom_more_impl.
Proof using. 
  ins. unfold sim_res_prom. red. ins.
  specialize (H0 l to from RES). desc. eexists. splits; eauto.
  { eapply reserved_more; [symmetry| ]; eauto. }
  intros ?. apply NOISS. eapply issued_more; eauto. 
Qed. 
 

(* TODO: move*)
Global Add Parametric Morphism : sim_res_prom with signature
       eq ==> (@set_equiv trav_label) ==> eq ==> eq ==> eq
          ==> (@set_equiv Memory.t) as sim_res_prom_more. 
Proof using. 
  ins. split; apply sim_res_prom_more_impl; auto; by symmetry. 
Qed. 

(* TODO: move*)
Global Add Parametric Morphism : sim_mem with signature
       eq ==> (@same_relation actid) ==> (@set_equiv trav_label) ==>
       eq ==> eq ==> eq ==> eq ==>
       (@set_subset Memory.t) as sim_mem_more_impl.
Proof using. 
  ins. unfold sim_mem. red. ins.
  specialize (H1 l b). specialize_full H1; eauto.
  { eapply issued_more; eauto. }
  desc. eexists. splits; eauto.
  { red in HELPER. red. desc. splits; eauto.
    red in SIMMSG. red. desc. splits; eauto. 
    eapply max_value_more; eauto.
    eapply set_equiv_union; [| basic_solver].
    enough (msg_rel y y0 l0 ≡ msg_rel y x l0) as MM by (generalize MM; basic_solver). 
    apply msg_rel_more; auto. by symmetry. }
  ins. specialize_full H1; eauto.
  { intro. apply H3. symmetry in H0. eapply covered_more; eauto. }
  desc. splits; eauto. 
  exists p_rel. rewrite REL. splits; vauto. des.
  { left. split; auto. intro. apply NINRMW.
    eapply set_equiv_exp; [rewrite H0| ]; eauto. }
  right. exists p. splits; eauto.
  symmetry  in H0. eapply issued_more; eauto.    
Qed. 
 

(* TODO: move*)
Global Add Parametric Morphism : sim_mem with signature
       eq ==> (@same_relation actid) ==> (@set_equiv trav_label) ==>
       eq ==> eq ==> eq ==> eq ==>
       (@set_equiv Memory.t) as sim_mem_more.
Proof using. 
  ins. split; apply sim_mem_more_impl; auto; by symmetry. 
Qed. 

(* TODO: move*)
Global Add Parametric Morphism : sim_res_mem with signature
       eq ==> (@set_equiv trav_label) ==>
       eq ==> eq ==> eq ==> eq ==>
       (@set_subset Memory.t) as sim_res_mem_more_impl.
Proof using. 
  ins. unfold sim_res_mem. red. ins.
  specialize (H0 l b). specialize_full H0; eauto.
  { eapply reserved_more; eauto. }
  intro. apply NISSB. symmetry in H. eapply issued_more; eauto.
Qed.  

(* TODO: move*)
Global Add Parametric Morphism : sim_res_mem with signature
       eq ==> (@set_equiv trav_label) ==>
       eq ==> eq ==> eq ==> eq ==>
       (@set_equiv Memory.t) as sim_res_mem_more.
Proof using. 
  ins. split; apply sim_res_mem_more_impl; auto; by symmetry. 
Qed. 

(* TODO: move*)
Global Add Parametric Morphism : sim_state with signature
       eq ==> eq ==> (@set_equiv actid) ==> eq ==> eq ==>
          Basics.impl as sim_state_more_impl.
Proof using.
  ins. red. unfold sim_state. ins. desc. splits; eauto.
  ins. split; ins.
  { apply PCOV, H. auto. }
  apply H, PCOV. auto. 
Qed. 

(* TODO: move*)
Global Add Parametric Morphism : sim_state with signature
       eq ==> eq ==> (@set_equiv actid) ==> eq ==> eq ==>
          iff as sim_state_more.
Proof using.
  ins. split; apply sim_state_more_impl; auto; by symmetry. 
Qed.

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
  
  edestruct issue_step_helper_next as [p_rel]; eauto. simpls. desf.
  set (rel'' := TView.rel (Local.tview local) locw).
  set (rel' := (View.join (View.join rel'' (View.unwrap p_rel))
                          (View.singleton_ur locw (f_to' w)))).

  remember (T ∪₁ eq (mkTL ta_issue w) ∪₁ (eq ta_reserve <*> (eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w)))) as T'.   

  set (pe1 :=
         ThreadEvent.promise
           locw (f_from' w) (f_to' w) (Message.full valw (Some rel'))
           Memory.op_kind_add).
  set (pe2 :=
         ThreadEvent.promise
           locw (f_from' wnext) (f_to' wnext) Message.reserve
           Memory.op_kind_add).
  
  assert (Memory.closed_message (Message.full valw (Some rel')) memory_add) as CLOS_MSG.
  { simpls. desf. by do 2 constructor. }
  
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
    assert (W ∩₁ Rel ∩₁ issued T' ⊆₁ covered T') as RELCOV'. 
    { subst T'. clear -RELB RELCOV. simplify_tls_events.
      generalize RELCOV. basic_solver 10. }

    subst.

    red; splits; red; splits; eauto; simpls.
    all: try (rewrite IdentMap.add_add_eq; eauto).
    all: try by apply TSTEP.
    { ins. etransitivity; [etransitivity| ].
      2: { apply RMWCOV; eauto. }
      all: apply set_equiv_exp; simplify_tls_events; basic_solver. }
    { eapply f_to_coherent_more; [..| apply FCOH0]; eauto.
      simplify_tls_events. basic_solver. }
    { ins. simplify_tls_events. rewrite SC_COV; auto. basic_solver. }
    { ins. clear -SC_REQ0 H0 l.
      eapply max_value_more; [..| apply SC_REQ0]; auto.
      simplify_tls_events. relsf. }
    { eapply reserved_time_more; [..| apply RESERVED_TIME0]; auto.
      clear. simplify_tls_events. basic_solver. }
    { do 2 (eapply Memory.add_closed; eauto). }
    simpls.
    exists state; eexists.
    rewrite IdentMap.gss.
    splits; eauto.
    { eapply sim_prom_more; [..| apply SIM_PROM0]; auto. clear. basic_solver. }
    { eapply sim_res_prom_more; [..| apply SIM_RES_PROM]; auto.
      clear. basic_solver. }
    { eapply sim_mem_more; [..| apply SIM_MEM0]; auto.
      clear. basic_solver. }
    { eapply sim_res_mem_more; [..| apply SIM_RES_MEM0]; auto.
      clear. basic_solver. }
    { eapply sim_tview_more.
      3: { simplify_tls_events. relsf. }
      all: eauto. 
      eapply sim_tview_f_issued; eauto. }
    do 2 (eapply tview_closedness_preserved_add; eauto).
    eapply sim_state_more; [.. | apply STATE]; auto.
    simplify_tls_events. basic_solver. 
  }
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
  eapply simrel_thread_local_step with (thread:=tid w) (PC:=PC) (T:=T); eauto.
  1-8: clear -WF TLSCOH ISSUABLE NINIT; simplify_tls_events; rewrite !set_union_empty_r.
  1-8: try by basic_solver. 
  { by apply coveredE. }
  { apply issuableE, set_subset_eq in ISSUABLE. rewrite issuedE, ISSUABLE; basic_solver. }
  { rewrite dom_sb_S_rfrmw_same_tid; auto. basic_solver. }

  3: try by (simpls; eapply msg_preserved_trans; eapply msg_preserved_add; eauto).
  2: { simpls. eapply closedness_preserved_trans; eapply closedness_preserved_add; eauto. }
  { by eapply same_other_threads_steps; eauto. }
  all: simpls; eauto.
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
