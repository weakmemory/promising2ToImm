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
From imm Require Import SimClosure.

From imm Require Import TraversalOrder.
From imm Require Import TLSCoherency.
From imm Require Import IordCoherency.
From imm Require Import AuxDef.
From imm Require Import TlsEventSets.
Require Import ExtTraversalConfig.
Require Import ExtTraversal.
Require Import MaxValue.
Require Import ViewRel.
From imm Require Import TlsViewRelHelpers.
Require Import SimulationRel.
Require Import SimulationPlainStepAux.
Require Import PlainStepBasic.
Require Import SimState.
Require Import SimStateHelper.
Require Import PromiseLTS.
Require Import MemoryAux.
Require Import FtoCoherent.
From imm Require Import AuxRel2.
Require Import ExistsReserveInterval.
Require Import ReserveStepHelper.
Require Import MemoryClosedness.
Require Import SimulationRelProperties.

Set Implicit Arguments.

Section ReservePlainStep.

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

Lemma reserve_step PC T f_to f_from thread w smode
      (SIMREL_THREAD : simrel_thread G sc PC T f_to f_from thread smode)
      (TSTEP : ext_itrav_step
                 G sc (mkTL ta_reserve w) T (T ∪₁ eq (mkTL ta_reserve w)))
      (WTID : thread = tid w)
      (FAIR: mem_fair G):
  let T' := T ∪₁ eq (mkTL ta_reserve w) in
  exists PC' f_to' f_from',
    ⟪ PCSTEP : plain_step MachineEvent.silent thread PC PC' ⟫ /\
    ⟪ SIMREL_THREAD : simrel_thread G sc PC' T' f_to' f_from' thread smode ⟫ /\
    ⟪ SIMREL :
        smode = sim_normal -> simrel G sc PC T f_to f_from ->
        simrel G sc PC' T' f_to' f_from' ⟫.
Proof using WF CON.
  cdes SIMREL_THREAD. cdes COMMON. cdes LOCAL.
  subst.
  
  assert (W w) as WW.
  { eapply ext_itrav_step_reserveW; eauto. }

  assert (E w) as EW.
  { eapply ext_itrav_stepE in TSTEP; eauto. }
  
  assert (exists locw, loc lab w = Some locw) as [locw WLOC] by (by apply is_w_loc).
  
  edestruct reserve_step_helper as [f_to']; eauto. simpls; desc.

  assert (forall e, issued T e -> f_to' e = f_to e) as ISSEQ_TO.
  { ins. apply REQ_TO. eapply rcoh_I_in_S; eauto. }

  assert (forall e, issued T e -> f_from' e = f_from e) as ISSEQ_FROM.
  { ins. apply REQ_FROM. eapply rcoh_I_in_S; eauto. }

  set (pe :=
         ThreadEvent.promise
           locw (f_from' w) (f_to' w) Message.reserve
           Memory.op_kind_add).

  eexists; exists f_to'; exists f_from'.
  apply and_assoc. apply pair_app; unnw.
  { split.
    { set (pe' := MachineEvent.silent).
      assert (pe' = ThreadEvent.get_machine_event pe) as H.
      { unfold pe. simpls. }
      rewrite H. clear H.
      econstructor; eauto.
      2: by unfold pe; desf.
      apply Thread.step_promise.
      constructor.
      2: by simpls.
      econstructor; eauto. }

    (* red; splits; red; splits. *)
    (* { eauto.  *)
    
    red; splits; red; splits; eauto.
    1-3: by apply TSTEP.
    { clear -RELCOV. by simplify_tls_events. }
    { ins. etransitivity; [etransitivity| ].
      2: { eapply RMWCOV; eauto. }
      all: apply set_equiv_exp; clear; simplify_tls_events; basic_solver. }
    { eapply f_to_coherent_more; [..| apply FCOH0]; eauto.
      clear. simplify_tls_events. basic_solver. }
    { ins. subst. clear -SC_COV. rewrite SC_COV; auto.
      simplify_tls_events. basic_solver. }
    { ins. eapply max_value_more; [.. | apply SC_REQ0]; eauto.
      clear. simplify_tls_events. apply S_tm_more; basic_solver. }
    { eapply Memory.add_inhabited; eauto. }
    { eapply Memory.add_closed; eauto. }

    simpls.
    exists state; eexists.
    rewrite IdentMap.gss.
    splits; eauto.

    { eapply sim_prom_same_covered_issued; [..| apply SIM_PROM0]; auto.
      all: clear; simplify_tls_events; basic_solver. }
    { eapply sim_mem_same_covered_issued; [..| apply SIM_MEM0]; auto.
      all: clear; simplify_tls_events; basic_solver. }
    { eapply sim_tview_more. 
      3: { by simplify_tls_events. }
      all: eauto. 
      eapply sim_tview_f_issued; eauto. }
    { eapply tview_closedness_preserved_add; eauto. }
    eapply sim_state_more; [.. | apply STATE]; auto.
    clear. simplify_tls_events. basic_solver. }
  intros [PCSTEP SIMREL_THREAD']; split; auto.
  intros SMODE SIMREL.
  eapply simrel_fS in SIMREL; eauto. 
  eapply full_simrel_step with (T := T); eauto.
  1-8: simplify_tls_events; auto using coveredE, issuedE with hahn.
  { basic_solver. }                                                 
  4: { ins. rewrite IdentMap.Facts.add_in_iff.
        split; auto. intros [|]; auto; subst.
        apply IdentMap.Facts.in_find_iff. by rewrite LLH. }
  3: by eapply msg_preserved_add; eauto.
  2: by eapply closedness_preserved_add; eauto.
  { by eapply same_other_threads_step; eauto. }
  subst. apply SIMREL_THREAD'. 
Qed.

End ReservePlainStep.
