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
Require Import IssueStepHelper.

(* TODO: Neither of versions works with the intended set usage *)
(* Global Add Parametric Morphism A: (fun (S: A -> Prop) s => S s) with signature *)
(*        (@set_equiv A) ==> eq ==> iff as set_apply_more. *)
(* Proof using. ins. by apply AuxRel.set_equiv_exp_equiv. Qed. *)
(* Global Add Parametric Morphism A: (@Basics.apply A Prop) with signature *)
(*        (@set_equiv A) ==> eq ==> iff as apply_more. *)
(* Proof using. ins. by apply AuxRel.set_equiv_exp_equiv. Qed.  *)

Set Implicit Arguments.

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

Lemma issue_rlx_step_no_next PC T f_to f_from thread w smode
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
      (NONEXT : dom_sb_S_rfrmw G T rfi (eq w) ⊆₁ ∅)
      (WTID : thread = tid w)
      (FAIR: mem_fair G)
  :
  (* let T' := mkTC (covered T) (issued T ∪₁ eq w) in *)
  (* let S' := S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G (mkETC T S) rfi (eq w) in *)
  let T' := T ∪₁ eq (mkTL ta_issue w) ∪₁ (eq ta_reserve <*> (eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w))) in
  exists f_to' f_from' PC',
    ⟪ PCSTEP : (plain_step MachineEvent.silent thread)⁺ PC PC' ⟫ /\
    ⟪ SIMREL_THREAD : simrel_thread G sc PC' T' f_to' f_from' thread smode ⟫ /\
    ⟪ SIMREL :
        smode = sim_normal -> simrel G sc PC T f_to f_from ->
        simrel G sc PC' T' f_to' f_from' ⟫.
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
  
  edestruct issue_step_helper_no_next as [p_rel]; eauto. simpls; desf.
  2: { set (rel'' := TView.rel (Local.tview local) locw).
       set (rel' := (View.join (View.join rel'' (View.unwrap p_rel))
                               (View.singleton_ur locw (f_to' w)))).

       set (wsmsg:=Message.full wsv wsrel).
       set (pe :=
              ThreadEvent.promise
                locw (f_from' w) (f_to' w) (Message.full valw (Some rel'))
                (Memory.op_kind_split (f_to' ws) wsmsg)).
       
       assert (Memory.closed_message (Message.full valw (Some rel')) memory') as CLOS_MSG.
       { by do 2 constructor. }
       
       exists f_to', f_from'. eexists.
       apply and_assoc. apply pair_app; unnw.
       { split.
         { eapply t_step.
           set (pe' := MachineEvent.silent).
           arewrite (pe' = ThreadEvent.get_machine_event pe) by simpls.
           eapply plain_step_intro with (lang:=thread_lts (tid w)); eauto.
           2: by unfold pe; clear; desf.
           apply Thread.step_promise.
           constructor.
           2: by simpls.
           econstructor; eauto. }
         destruct (is_rel lab w) eqn:RELB; [by desf|].
         subst.
         red; splits; red; splits; eauto; simpls.
         1-3: by apply TSTEP. 
         all: try (rewrite IdentMap.add_add_eq; eauto).
         (* { generalize RELB RELCOV. clear. basic_solver. } *)
         { clear -RELB RELCOV. simplify_tls_events.
           generalize RELB RELCOV. basic_solver 10. }
         {
           ins. etransitivity; [etransitivity| ].
           2: { eapply RMWCOV; eauto. }
           all: apply set_equiv_exp; clear; simplify_tls_events; basic_solver. }
         { eapply f_to_coherent_more; [..| apply FCOH0]; eauto.
           clear. simplify_tls_events. basic_solver. }
         { ins. subst. clear -SC_COV. rewrite SC_COV; auto.
           simplify_tls_events. basic_solver. }
         { desc. splits.
           { rewrite <- FOR_SPLIT. clear. 
             by simplify_tls_events. }
           rewrite RMW_BEF_S. clear. by simplify_tls_events. }
         { eapply Memory.split_closed; eauto. }
         simpls.
         exists state; eexists.
         rewrite IdentMap.gss.
         splits; eauto.
         { eapply sim_prom_more; [..| apply SIM_PROM0]; eauto.
           clear. by simplify_tls_events. }
         { eapply sim_res_prom_more; [..| apply SIM_RES_PROM]; eauto.
           clear. by simplify_tls_events. }
         { eapply sim_mem_more; [..| apply SIM_MEM0]; eauto. 
           clear. by simplify_tls_events. }
         { eapply sim_res_mem_more; [..| apply SIM_RES_MEM0]; eauto.
           clear. by simplify_tls_events. }         
         { simpls. eapply sim_tview_more.
           3: { clear. by simplify_tls_events. }
           all: auto. 
           eapply sim_tview_f_issued with (f_to:=f_to); eauto. }         
         eapply tview_closedness_preserved_split; eauto.
         eapply sim_state_more.
         3: { clear. by simplify_tls_events. }
         all: auto. }
       intros [PCSTEP SIMREL_THREAD']; split; auto.
       intros SMODE SIMREL.
       subst. desc. red.
       inv SMODE. }

  set (rel'' := TView.rel (Local.tview local) locw).
  set (rel' := (View.join (View.join rel'' (View.unwrap p_rel))
                          (View.singleton_ur locw (f_to' w)))).

  set (pe :=
         ThreadEvent.promise
           locw (f_from' w) (f_to' w) (Message.full valw (Some rel'))
           Memory.op_kind_add).
  
  assert (Memory.closed_message (Message.full valw (Some rel')) memory') as CLOS_MSG.
  { by do 2 constructor. }
  
  exists f_to', f_from'. eexists.
  apply and_assoc. apply pair_app; unnw.
  { split.
    { eapply t_step.
      set (pe' := MachineEvent.silent).
      arewrite (pe' = ThreadEvent.get_machine_event pe) by simpls.
      eapply plain_step_intro with (lang:=thread_lts (tid w)); eauto.
      2: by unfold pe; clear; desf.
      apply Thread.step_promise.
      constructor.
      2: by simpls.
      econstructor; eauto. }
    destruct (is_rel lab w) eqn:RELB; [by desf|].
    subst.
    red; splits; red; splits; eauto; simpls.
    all: try (rewrite IdentMap.add_add_eq; eauto).
    1-3: by apply TSTEP. 
    { clear -RELB RELCOV. simplify_tls_events.
      rewrite set_inter_union_r, RELCOV. basic_solver. }
    { ins. etransitivity; [etransitivity| ].
      2: { eapply RMWCOV; eauto. }
      all: eapply set_equiv_exp; clear; by simplify_tls_events. }
    { eapply f_to_coherent_more; [..| apply FCOH0]; eauto.
      clear. simplify_tls_events. basic_solver. }
    { ins. clear -SC_COV H0. simplify_tls_events. auto. }
    { ins. generalize (SC_REQ0 H0 l).
      clear. by simplify_tls_events. }
    { eapply reserved_time_same_issued_reserved; eauto.
      all: clear; by simplify_tls_events. }
    { eapply Memory.add_closed; eauto. }
    simpls.
    exists state; eexists.
    rewrite IdentMap.gss.
    splits; eauto.
    { eapply sim_prom_more; [..| apply SIM_PROM0]; eauto.
      clear. by simplify_tls_events. }
    { eapply sim_res_prom_more; [..| apply SIM_RES_PROM]; eauto.
      clear. by simplify_tls_events. }
    { eapply sim_mem_more; [..| apply SIM_MEM0]; eauto. 
      clear. by simplify_tls_events. }
    { eapply sim_res_mem_more; [..| apply SIM_RES_MEM0]; eauto.
      clear. by simplify_tls_events. }         
    { simpls. eapply sim_tview_more.
      3: { clear. by simplify_tls_events. }
      all: auto. 
      eapply sim_tview_f_issued with (f_to:=f_to); eauto. }
    { eapply tview_closedness_preserved_add; eauto. }
    eapply sim_state_more; [..| apply STATE]; eauto.
    clear. by simplify_tls_events. }
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
  apply SIMREL in AA. cdes AA.
  eapply simrel_thread_local_step with (thread:=tid w) (PC:=PC) (T:=T); eauto.
  (* 10: { simpls. eapply msg_preserved_add; eauto. } *)
  11: { simpls. eapply msg_preserved_add; eauto. }
  10: { simpls. eapply closedness_preserved_add; eauto. }
  9: by eapply same_other_threads_steps; eauto.
  all: simpls; eauto.
  1-8: clear -TLSCOH EW WF NINIT; simplify_tls_events; try basic_solver. 
  { apply coveredE; eauto. }
  { rewrite issuedE; eauto. basic_solver. }
  { rewrite dom_sb_S_rfrmw_same_tid; auto. basic_solver. }
  { ins.
    etransitivity; [|by symmetry; apply IdentMap.Facts.add_in_iff].
    split.
    { ins; eauto. }
    intros [|HH]; subst; auto.
    apply SIMREL_THREAD; auto. }
  { apply IdentMap.Facts.add_in_iff in TP. destruct TP as [HH|]; auto; subst.
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
