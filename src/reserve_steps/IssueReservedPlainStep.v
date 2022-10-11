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
Require Import ExistsIssueReservedInterval.
Require Import IssueReservedStepHelper.
Require Import MemoryClosedness.
Require Import SimulationRelProperties.

Set Implicit Arguments.

Section IssueReservedPlainStep.

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

Lemma issue_rlx_reserved_step_no_next PC T f_to f_from thread w smode
      (SIMREL_THREAD : simrel_thread G sc PC T f_to f_from thread smode)
      (TSTEP : ext_itrav_step
                 G sc (mkTL ta_issue w) T
                 (* (mkETC *)
                 (*    (mkTC (covered T) (issued T ∪₁ eq w)) *)
                 (*    (S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G (mkETC T S) rfi (eq w))) *)
                 (T ∪₁ eq (mkTL ta_issue w) ∪₁ (eq ta_reserve <*> (eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w))))
      )
      (SW : reserved T w)
      (NREL : ~ Rel w)
      (NONEXT : dom_sb_S_rfrmw G T rfi (eq w) ⊆₁ ∅)
      (WTID : thread = tid w) :
  (* let T' := mkTC (covered T) (issued T ∪₁ eq w) in *)
  (* let S' := S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G (mkETC T S) rfi (eq w) in *)
  let T' := T ∪₁ eq (mkTL ta_issue w) ∪₁ (eq ta_reserve <*> (eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w))) in
  exists f_to' PC',
    ⟪ PCSTEP : (plain_step MachineEvent.silent thread)⁺ PC PC' ⟫ /\
    ⟪ SIMREL_THREAD : simrel_thread G sc PC' T' f_to' f_from thread smode ⟫ /\
    ⟪ SIMREL :
        smode = sim_normal -> simrel G sc PC T f_to f_from ->
        simrel G sc PC' T' f_to' f_from ⟫.
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
  assert (E w /\ W w) as [EW WW] by (by apply SEW).
  assert (~ is_init w) as NINIT.
  { intros AA. apply NISSB. eapply init_issued; eauto. by split. }

  assert (exists locw, loc lab w = Some locw) as [locw WLOC] by (by apply is_w_loc).
  assert (exists valw, val lab w = Some valw) as [valw WVAL] by (by apply is_w_val).
  
  assert (W_ex w) as [r RMW].
  { apply RCOH. by split. }
  
  edestruct issue_reserved_step_helper_no_next as [p_rel]; eauto. simpls; desc.

  set (f_to' := upd f_to w (Time.middle (f_from w) (f_to w))).
  assert (ISSEQ_TO : forall e : actid, issued T e -> f_to' e = f_to e).
  { ins. unfold f_to'. rewrite updo; auto. by intros HH; subst. }
  set (rel'' :=
        if is_rel lab w
        then (TView.cur (Local.tview local))
        else (TView.rel (Local.tview local) locw)).
  set (rel' := (View.join (View.join rel'' (View.unwrap p_rel))
                          (View.singleton_ur locw (f_to' w)))).

  set (pe_cancel :=
         ThreadEvent.promise
           locw (f_from w) (f_to w) Message.reserve
           Memory.op_kind_cancel).

  set (pe :=
         ThreadEvent.promise
           locw (f_from w) (f_to' w) (Message.full valw (Some rel'))
           Memory.op_kind_add).
  
  assert (Memory.closed_message (Message.full valw (Some rel')) memory_add) as CLOS_MSG.
  { by do 2 constructor. }
  
  exists f_to'. eexists.
  apply and_assoc. apply pair_app; unnw.
  { split.
    { eapply t_trans; apply t_step.
      { set (pe'' := MachineEvent.silent).
        arewrite (pe'' = ThreadEvent.get_machine_event pe_cancel) by simpls.
        econstructor; eauto.
        2: by unfold pe_cancel; desf.
        apply Thread.step_promise.
        constructor.
        2: by simpls.
        econstructor; eauto. }
      set (pe' := MachineEvent.silent).
      arewrite (pe' = ThreadEvent.get_machine_event pe) by simpls.
      eapply plain_step_intro with (lang:=thread_lts (tid w)); eauto.
      { simpls. rewrite IdentMap.gss; eauto. }
      2: by unfold pe; clear; desf.
      apply Thread.step_promise.
      constructor.
      2: by simpls.
      econstructor; eauto. }
    destruct (is_rel lab w) eqn:RELB.
    { desf. }
    subst.
    red; splits; red; splits; eauto; simpls.
    all: try (rewrite IdentMap.add_add_eq; eauto).
    1-3: by apply TSTEP. 
    { clear -RELB RELCOV. simplify_tls_events.
      generalize RELB RELCOV. basic_solver 10. }
    { ins. etransitivity; [etransitivity| ].
      2: { eapply RMWCOV; eauto. }
      all: apply set_equiv_exp; clear; simplify_tls_events; basic_solver. }
    { eapply f_to_coherent_more; [..| apply FCOH0]; eauto.
      clear. simplify_tls_events. basic_solver. }
    { ins. subst. clear -SC_COV. rewrite SC_COV; auto.
      simplify_tls_events. basic_solver. }
    { ins. eapply max_value_more; [.. | apply SC_REQ0]; eauto.
      clear. simplify_tls_events. apply S_tm_more; basic_solver. }
    { eapply reserved_time_more; [.. | apply RESERVED_TIME0]; eauto.
      clear. basic_solver. } 
    { eapply Memory.add_closed; eauto.
      eapply Memory.cancel_closed; eauto. }
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
    { eapply tview_closedness_preserved_add; eauto.
      eapply tview_closedness_preserved_cancel; eauto. }
    eapply sim_state_more; [.. | apply STATE]; auto.
    clear. simplify_tls_events. basic_solver. }
  intros [PCSTEP SIMREL_THREAD']; split; auto.
  intros SMODE SIMREL.
  subst. desc. red.
  splits; [by apply SIMREL_THREAD'|].
  simpls. ins.
  destruct (classic (thread = tid w)) as [|TNEQ]; subst.
  { apply SIMREL_THREAD'. }
  set (AA:=TP).
  apply IdentMap.Facts.add_in_iff in AA. desf.
  apply IdentMap.Facts.add_in_iff in AA. desf.
  apply SIMREL in AA. cdes AA.
  eapply simrel_thread_local_step with (thread:=tid w) (PC:=PC) (T:=T); eauto.

  1-8: clear -WF TLSCOH ISSUABLE NINIT; simplify_tls_events.
  1-8: try by basic_solver. 
  { by apply coveredE. }
  { apply issuableE, set_subset_eq in ISSUABLE. rewrite issuedE, ISSUABLE; basic_solver. }
  { rewrite dom_sb_S_rfrmw_same_tid; auto. basic_solver. }
  4: { ins. rewrite !IdentMap.Facts.add_in_iff.
        split; auto.
        intros [| [ | ]]; auto; subst.
        all: apply IdentMap.Facts.in_find_iff; by rewrite LLH. }
  3: { eapply msg_preserved_trans.
        { eapply msg_preserved_cancel; eauto. }
        eapply msg_preserved_add; eauto. }
  2: { eapply closedness_preserved_trans.
       { eapply closedness_preserved_cancel; eauto. }
       eapply closedness_preserved_add; eauto. }
  { by eapply same_other_threads_steps; eauto. }
  all: simpls; eauto.
  { repeat (apply IdentMap.Facts.add_in_iff in TP; desf). }
  { eapply sim_prom_f_issued; eauto. }
  { red. ins. apply SIM_RPROM0 in RES. desc.
    assert (b <> w) as BNW.
    { intros HH; desf. }
    exists b. splits; auto.
    unfold f_to'. rewrite updo; auto. }
  { eapply sim_mem_f_issued; eauto. }
  { ins.
    assert (b <> w) as BNW.
    { intros HH; desf. }
    unfold f_to'. rewrite updo; auto.
    apply SIM_RES_MEM1; auto. }
  eapply sim_tview_f_issued; eauto.
Qed.

Lemma issue_rlx_reserved_step_with_next PC T f_to f_from thread w wnext smode
      (SIMREL_THREAD : simrel_thread G sc PC T f_to f_from thread smode)
      (TSTEP : ext_itrav_step
                 G sc (mkTL ta_issue w) T
                 (T ∪₁ eq (mkTL ta_issue w) ∪₁ (eq ta_reserve <*> (eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w)))))
      (SW : reserved T w)
      (NREL : ~ Rel w)
      (WNEXT : dom_sb_S_rfrmw G T rfi (eq w) wnext)
      (WTID : thread = tid w) :
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
  assert (E w /\ W w) as [EW WW] by (by apply SEW).
  assert (~ is_init w) as NINIT.
  { intros AA. apply NISSB. eapply init_issued; eauto. by split. }

  assert (exists locw, loc lab w = Some locw) as [locw WLOC] by (by apply is_w_loc).
  assert (exists valw, val lab w = Some valw) as [valw WVAL] by (by apply is_w_val).
  
  assert (W_ex w) as [r RMW].
  { apply RCOH. by split. }
  
  edestruct issue_reserved_step_helper_with_next as [REQ_TO]; eauto. simpls; desc.

  set (n_to     := Time.middle (f_from w) (f_to w)).
  set (f_to'    := upd (upd f_to w n_to) wnext (f_to w)).
  set (f_from'  := upd f_from wnext n_to).

  set (rel'' :=
        if is_rel lab w
        then (TView.cur (Local.tview local))
        else (TView.rel (Local.tview local) locw)).
  set (rel' := (View.join (View.join rel'' (View.unwrap p_rel))
                          (View.singleton_ur locw (f_to' w)))).

  set (pe :=
         ThreadEvent.promise
           locw (f_from' w) (f_to' w) (Message.full valw (Some rel'))
           (Memory.op_kind_split (f_to' wnext) Message.reserve)).
  
  assert (Memory.closed_message (Message.full valw (Some rel')) memory_split) as CLOS_MSG.
  { by do 2 constructor. }
  
  exists f_to', f_from'. eexists.
  apply and_assoc. apply pair_app; unnw.
  { split.
    { apply t_step.
      set (pe'' := MachineEvent.silent).
      arewrite (pe'' = ThreadEvent.get_machine_event pe) by simpls.
      econstructor; eauto.
      2: by unfold pe; desf.
      apply Thread.step_promise.
      constructor.
      2: by simpls.
      econstructor; eauto. }
    destruct (is_rel lab w) eqn:RELB.
    { desf. }
    subst.
    (* TODO: very similar to the previous lemma *)
    red; splits; red; splits; eauto; simpls.
    all: try (rewrite IdentMap.add_add_eq; eauto).
    1-3: by apply TSTEP.     
    { clear -RELB RELCOV. simplify_tls_events.
      generalize RELB RELCOV. basic_solver 10. }
    { ins. etransitivity; [etransitivity| ].
      2: { eapply RMWCOV; eauto. }
      all: apply set_equiv_exp; clear; simplify_tls_events; basic_solver. }
    { eapply f_to_coherent_more; [..| apply FCOH0]; eauto.
      clear. simplify_tls_events. basic_solver. }
    { ins. subst. clear -SC_COV. rewrite SC_COV; auto.
      simplify_tls_events. basic_solver. }
    { ins. eapply max_value_more; [.. | apply SC_REQ0]; eauto.
      clear. simplify_tls_events. apply S_tm_more; basic_solver. }
    { eapply reserved_time_more; [.. | apply RESERVED_TIME0]; eauto.
      clear. basic_solver. } 
    { eapply Memory.split_closed; eauto. }
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
    { eapply tview_closedness_preserved_split; eauto. }
    eapply sim_state_more; [.. | apply STATE]; auto.
    clear. simplify_tls_events. basic_solver. }

  intros [PCSTEP SIMREL_THREAD']; split; auto.
  intros SMODE SIMREL.
  subst. desc. red.
  splits; [by apply SIMREL_THREAD'|].
  simpls. ins.
  destruct (classic (thread = tid w)) as [|TNEQ]; subst.
  { apply SIMREL_THREAD'. }
  set (AA:=TP).
  apply IdentMap.Facts.add_in_iff in AA. desf.
  apply SIMREL in AA. cdes AA.
  eapply simrel_thread_local_step with (thread:=tid w) (PC:=PC) (T:=T); eauto.

  1-8: clear -WF TLSCOH ISSUABLE NINIT; simplify_tls_events.
  1-8: try by basic_solver. 
  { by apply coveredE. }
  { apply issuableE, set_subset_eq in ISSUABLE. rewrite issuedE, ISSUABLE; basic_solver. }
  { rewrite dom_sb_S_rfrmw_same_tid; auto. basic_solver. }

  3: { eapply msg_preserved_split; eauto. }
  2: { eapply closedness_preserved_split; eauto. }
  { by eapply same_other_threads_steps; eauto. }
  all: simpls; eauto.
  { ins. etransitivity.
    2: { symmetry. apply IdentMap.Facts.add_in_iff. }
    split; [by ins; eauto|].
    intros [|HH]; subst; auto.
    apply SIMREL_THREAD; auto.
    split; auto. now apply WF. }
  { apply IdentMap.Facts.add_in_iff in TP. desf. }
  { eapply sim_prom_f_issued; eauto. }
  { (* TODO: generalize to a lemma? *)
    red. ins. apply SIM_RPROM0 in RES. desc.
    assert (b <> w) as BNW.
    { intros HH; desf. }
    exists b. splits; auto.
    { rewrite REQ_FROM; auto. }
    rewrite REQ_TO; auto. }
  { eapply sim_mem_f_issued; eauto. }
  { ins.
    assert (b <> w) as BNW.
    { intros HH; desf. }
    rewrite REQ_FROM; auto. rewrite REQ_TO; auto.
    apply SIM_RES_MEM1; auto. }
  eapply sim_tview_f_issued; eauto.
Qed.

End IssueReservedPlainStep.
