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
From imm Require Import FairExecution.

Require Import AuxRel.
From imm Require Import AuxRel2.
From imm Require Import AuxDef. 
Require Import ExtTraversalConfig.
Require Import ExtTraversal.
Require Import ExtSimTraversal.
From imm Require Import TLSCoherency.
From imm Require Import IordCoherency.
From imm Require Import TraversalOrder. 
Require Import TlsEventSets.
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
Require Import PlainStepBasic.
Require Import FencePlainStep.
Require Import ReadPlainStep.
Require Import WriteRlxCovPlainStep.
Require Import RMWRlxCovPlainStep.
Require Import ReservePlainStep.
Require Import IssuePlainStep.
Require Import IssueNextPlainStep.
Require Import IssueRelPlainStep.
Require Import IssueRelNextPlainStep.
Require Import IssueReservedPlainStep.
Require Import IssueReservedRelPlainStep.
Require Import IssueReservedRelNextPlainStep.
Require Import SimulationRelProperties.

Set Implicit Arguments.

Section PlainStep.
                        
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
Global Add Parametric Morphism : simrel_common with signature
       eq ==> same_relation ==> eq ==> set_equiv ==> eq ==> eq ==> eq
          ==> Basics.impl as simrel_common_more_impl. 
Proof using.
  unfold simrel_common. ins. red. ins. desc. splits; rewrite <- ?H0, <- ?H; eauto.
  { ins. etransitivity; [| etransitivity]; [| apply RMWCOV| ]; eauto.
    all: apply set_equiv_exp; by rewrite H0. }
  { ins. rewrite <- H0. eauto. }
  eapply reserved_time_more; [..| apply RESERVED_TIME]; eauto. by symmetry. 
Qed. 

(* TODO: move *)
Global Add Parametric Morphism : simrel_common with signature
       eq ==> same_relation ==> eq ==> set_equiv ==> eq ==> eq ==> eq
          ==> iff as simrel_common_more. 
Proof using.
  ins. split; eapply simrel_common_more_impl; eauto; by symmetry. 
Qed.  


(* TODO: move *)
Global Add Parametric Morphism : simrel_thread_local with signature
       eq ==> same_relation ==> eq ==> set_equiv ==> eq ==> eq ==> eq ==> eq
          ==> Basics.impl as simrel_thread_local_more_impl. 
Proof using.
  unfold simrel_thread_local. ins. red. ins. desc.
  do 2 eexists. splits; eauto.
  { eapply sim_prom_more; [..| apply SIM_PROM]; eauto; by symmetry. }
  { eapply sim_res_prom_more; [..| apply SIM_RPROM]; eauto; by symmetry. }
  { eapply sim_mem_more; [..| apply SIM_MEM]; eauto; by symmetry. }
  { eapply sim_res_mem_more; [..| apply SIM_RES_MEM]; eauto; by symmetry. }
  { eapply sim_tview_more; [..| apply SIM_TVIEW]; eauto.
    { by symmetry. }
    by rewrite <- H0. }
  eapply sim_state_more; [..| apply STATE]; eauto. by rewrite <- H0.
Qed.   
  
(* TODO: move *)
Global Add Parametric Morphism : simrel_thread_local with signature
       eq ==> same_relation ==> eq ==> set_equiv ==> eq ==> eq ==> eq ==> eq
          ==> iff as simrel_thread_local_more. 
Proof using.
  ins. split; eapply simrel_thread_local_more_impl; eauto; by symmetry. 
Qed. 

(* TODO: move *)
Global Add Parametric Morphism : simrel_thread with signature
       eq ==> same_relation ==> eq ==> set_equiv ==> eq ==> eq ==> eq ==> eq
          ==> iff as simrel_thread_more. 
Proof using. 
  ins. split; unfold simrel_thread; ins; desc.
  all: splits; [eapply simrel_common_more | eapply simrel_thread_local_more].
  17, 34: by apply LOCAL. 8, 24: by apply COMMON.
  all: eauto; by symmetry.
Qed. 
  
(* TODO: move *)
Global Add Parametric Morphism : simrel with signature
       eq ==> same_relation ==> eq ==> set_equiv ==> eq ==> eq
          ==> iff as simrel_more. 
Proof using. 
  ins. unfold simrel. split; ins; desc; splits.
  1, 3: eapply simrel_common_more; [..| apply COMMON]; eauto; by symmetry. 
  all: ins; eapply simrel_thread_local_more; [..| apply THREADS]; eauto; by symmetry. 
Qed. 

Lemma step_end_helper PC PC' t f_to f_from f_to' f_from' smode T0 T T' (EQUIV: T' ≡₁ T)
      (STEP: plain_step MachineEvent.silent t PC PC' \/ (plain_step MachineEvent.silent t)^+ PC PC')
      (ST: simrel_thread G sc PC' T f_to' f_from' t smode)
      (SR: smode = sim_normal ->
           simrel G sc PC T0 f_to f_from -> simrel G sc PC' T f_to' f_from'):
    (plain_step MachineEvent.silent t)＊ PC PC' /\
    simrel_thread G sc PC' T' f_to' f_from' t smode /\
    (smode = sim_normal ->
     simrel G sc PC T0 f_to f_from -> simrel G sc PC' T' f_to' f_from').
Proof using.
  splits.
  { des; [eapply inclusion_r_rt | eapply inclusion_t_rt]; eauto. done. }
  { rewrite EQUIV. eauto. }
  ins. rewrite EQUIV. eauto.
Qed.
  

Lemma plain_sim_step thread PC T f_to f_from T' smode
      (TCSTEP : ext_isim_trav_step G sc thread T T')
      (SIMREL_THREAD : simrel_thread G sc PC T f_to f_from thread smode)
      (FAIR: mem_fair G):
    exists PC' f_to' f_from',
      ⟪ PSTEP : (plain_step MachineEvent.silent thread)＊ PC PC' ⟫ /\
      ⟪ SIMREL_THREAD : simrel_thread G sc PC' T' f_to' f_from' thread smode ⟫ /\
      ⟪ SIMREL :
          smode = sim_normal -> simrel G sc PC T f_to f_from ->
          simrel G sc PC' T' f_to' f_from' ⟫.
Proof using WF CON.
  cdes SIMREL_THREAD. cdes COMMON. cdes LOCAL.
  set (TCSTEP' := TCSTEP).
  inv TCSTEP'.
  { (* Fence covering *)
    inversion TS. simpl in ets_upd.
    rewrite set_pair_alt, set_inter_empty_r, set_union_empty_r in ets_upd.     
    edestruct fence_step; eauto.
    { eapply ext_itrav_step_more; [..| apply TS]; eauto. by symmetry. }
    desc. edestruct step_end_helper; eauto. }
  { (* Read covering *)
    inversion TS. simpl in ets_upd.
    rewrite set_pair_alt, set_inter_empty_r, set_union_empty_r in ets_upd.     
    edestruct read_step; eauto.
    { eapply ext_itrav_step_more; [..| apply TS]; eauto. by symmetry. }
    desc. edestruct step_end_helper; eauto. }
  { (* Write reserving *)
    inversion TS. simpl in ets_upd.
    rewrite set_pair_alt, set_inter_empty_r, set_union_empty_r in ets_upd.
    edestruct reserve_step; eauto.
    { eapply ext_itrav_step_more; [..| apply TS]; eauto. by symmetry. }
    desc. edestruct step_end_helper; eauto. }
  { (* Relaxed write issuing *)
    inversion TS. simpl in ets_upd.

    destruct (classic (reserved T w)) as [SW|NSW].
    { destruct (classic (exists wnext, dom_sb_S_rfrmw G T rfi (eq w) wnext)) as [NEMP|EMP].
      2: { edestruct issue_rlx_reserved_step_no_next; eauto.
           { eapply ext_itrav_step_more; [..| apply TS]; eauto. by symmetry. }
           { generalize EMP. clear. basic_solver. }
           desc. edestruct step_end_helper; eauto. }

      desc. edestruct issue_rlx_reserved_step_with_next; eauto.
      { eapply ext_itrav_step_more; [..| apply TS]; eauto. by symmetry. }
      desc. edestruct step_end_helper; eauto. }

    destruct (classic (exists wnext, dom_sb_S_rfrmw G T rfi (eq w) wnext)) as [NEMP|EMP].
    2: { edestruct issue_rlx_step_no_next; eauto.
         { eapply ext_itrav_step_more; [..| apply TS]; eauto. by symmetry. }
         { intros WEX. destruct NSW. apply tls_set_alt.
           apply ets_issue_W_ex; vauto. }
         { generalize EMP. clear. basic_solver. }
         desc. edestruct step_end_helper; eauto. }
    desc. edestruct issue_rlx_step_next; eauto.
    { eapply ext_itrav_step_more; [..| apply TS]; eauto. by symmetry. }
    { intros WEX. destruct NSW. apply tls_set_alt.
      apply ets_issue_W_ex; vauto. }
    desc. edestruct step_end_helper; eauto. }

  { (* Relaxed write covering *)
    inversion TS. simpl in ets_upd.
    rewrite set_pair_alt, set_inter_empty_r, set_union_empty_r in ets_upd.
    edestruct rlx_write_cover_step; eauto.
    { eapply ext_itrav_step_more; [..| apply TS]; eauto. by symmetry. }
    desc. edestruct step_end_helper; eauto. } 

  { (* Release write covering *)
    inversion TS1. simpl in ets_upd.
    inversion TS2. simpl in ets_upd0. 
    rewrite set_pair_alt, set_inter_empty_r, set_union_empty_r in ets_upd0.

    destruct (classic (reserved T w)) as [SW|NSW].
    { exfalso. apply NRMW. apply RCOH. by split. }

    destruct (classic (exists wnext, dom_sb_S_rfrmw G T rfi (eq w) wnext)) as [NEMP|EMP].
    2: { edestruct issue_rel_step_no_next; eauto.
         { eapply ext_itrav_step_more; [..| apply TS1]; eauto. by symmetry. }  
         { eapply ext_itrav_step_more; [..| apply TS2]; eauto.
           { by symmetry. }
           rewrite ets_upd0, ets_upd. basic_solver. }
         { generalize EMP. clear. basic_solver. }
         desc. edestruct step_end_helper with (T' := T').
         3: by apply SIMREL_THREAD0.
         all: eauto. 
         rewrite ets_upd0, ets_upd. basic_solver. }
         
    desc. edestruct issue_rel_step_next; eauto.
    { eapply ext_itrav_step_more; [..| apply TS1]; eauto. by symmetry. }  
    { eapply ext_itrav_step_more; [..| apply TS2]; eauto.
      { by symmetry. }
      rewrite ets_upd0, ets_upd. basic_solver. }
    desc. edestruct step_end_helper with (T' := T').
    3: by apply SIMREL_THREAD0.
    all: eauto. 
    rewrite ets_upd0, ets_upd. basic_solver. }

  { (* Relaxed RMW covering *)
    assert (R r) as RR.
    { apply (dom_l (wf_rmwD WF)) in RMW. apply seq_eqv_l in RMW. desf. }
    inversion TS1. simpl in ets_upd.
    rewrite set_pair_alt, set_inter_empty_r, set_union_empty_r in ets_upd.
    inversion TS2. simpl in ets_upd0. 
    rewrite set_pair_alt, set_inter_empty_r, set_union_empty_r in ets_upd0.
    edestruct rlx_rmw_cover_step; eauto.
    { eapply ext_itrav_step_more; [..| apply TS1]; eauto. by symmetry. }  
    { eapply ext_itrav_step_more; [..| apply TS2]; eauto.
      { by symmetry. }
      rewrite ets_upd0, ets_upd. basic_solver. }
    desc. edestruct step_end_helper with (T' := T').
    3: by apply SIMREL_THREAD0.
    all: eauto. 
    rewrite ets_upd0, ets_upd. basic_solver. }

  (* Release RMW covering *)
  inversion TS1. simpl in ets_upd.
  inversion TS2. simpl in ets_upd0. 
  inversion TS3. simpl in ets_upd1. 
  rewrite set_pair_alt, set_inter_empty_r, set_union_empty_r in ets_upd1, ets_upd.
  assert (reserved T w) as SW.
  { apply tls_set_alt.
    specialize_full ets_issue_W_ex0; try by vauto.
    simpl in ets_issue_W_ex0. apply ets_upd in ets_issue_W_ex0.
    destruct ets_issue_W_ex0; vauto. }

  (* pose proof (set_equiv_refl2 T'') as T''_.  *)
  rewrite ets_upd in ets_upd0.  eapply set_equiv_trans in ets_upd0. specialize_full ets_upd0.
  { clear. rewrite dom_sb_S_rfrmw_union_P.
    unfold dom_sb_S_rfrmw at 2. simplify_tls_events.
    rewrite seq_false_r, dom_empty, set_inter_empty_l, set_union_empty_r.
    reflexivity. }
  rewrite ets_upd0 in ets_upd1.
  
  destruct (classic (exists wnext, dom_sb_S_rfrmw G T rfi (eq w) wnext)) as [NEMP|EMP].
  2: { edestruct issue_rel_reserved_step_no_next; eauto.
       { generalize EMP. clear. basic_solver. }
       { eapply ext_itrav_step_more; [..| apply TS1]; eauto. by symmetry. }  
       { eapply ext_itrav_step_more; [..| apply TS2]; eauto; by symmetry. }
       { eapply ext_itrav_step_more; [..| apply TS3]; eauto; try by symmetry.
         rewrite ets_upd1. basic_solver 10. }
       desc. edestruct step_end_helper with (T' := T').
       3: by apply SIMREL_THREAD0.
       all: eauto. 
       rewrite ets_upd1. basic_solver 10. }

  { desc. edestruct issue_rel_reserved_step_with_next; eauto.
    { eapply ext_itrav_step_more; [..| apply TS1]; eauto. by symmetry. }  
    { eapply ext_itrav_step_more; [..| apply TS2]; eauto; by symmetry. }
    { eapply ext_itrav_step_more; [..| apply TS3]; eauto.
      { by symmetry. }
      rewrite ets_upd1. basic_solver 10. }  
    
    desc. edestruct step_end_helper with (T' := T').
    3: by apply SIMREL_THREAD0.
    all: eauto. 
    rewrite ets_upd1. basic_solver 10. }

  { (* Propagation *)
    inversion TS. simpl in ets_upd.
    rewrite set_pair_alt, set_inter_empty_r, set_union_empty_r in ets_upd.
    admit. 
    
  } 

Admitted. 

End PlainStep.
