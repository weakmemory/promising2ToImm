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

Require Import TraversalConfig.
Require Import ExtTraversalConfig.
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

Lemma reserve_step PC T S f_to f_from thread w smode
      (SIMREL_THREAD : simrel_thread G sc PC T S f_to f_from thread smode)
      (TSTEP : ext_itrav_step
                 G sc w (mkETC T S) (mkETC T (S ∪₁ eq w)))
      (WTID : thread = tid w) :
  let S' := S ∪₁ eq w in
  exists PC' f_to' f_from',
    ⟪ PCSTEP : plain_step MachineEvent.silent thread PC PC' ⟫ /\
    ⟪ SIMREL_THREAD : simrel_thread G sc PC' T S' f_to' f_from' thread smode ⟫ /\
    ⟪ SIMREL :
        smode = sim_normal -> simrel G sc PC T S f_to f_from ->
        simrel G sc PC' T S' f_to' f_from' ⟫.
Proof using WF CON.
  cdes SIMREL_THREAD. cdes COMMON. cdes LOCAL.
  subst.
  
  assert (tc_coherent G sc T) as TCCOHs by apply TCCOH.

  assert (W w) as WW.
  { eapply ext_itrav_step_reserveW with (T := mkETC T S); eauto. }

  assert (E w) as EW.
  { eapply ext_itrav_stepE with (T := mkETC T S); eauto. }
  
  assert (exists locw, loc lab w = Some locw) as [locw WLOC] by (by apply is_w_loc).
  
  edestruct reserve_step_helper as [f_to']; eauto. simpls; desc.

  assert (forall e, issued T e -> f_to' e = f_to e) as ISSEQ_TO.
  { ins. apply REQ_TO. by apply TCCOH.(etc_I_in_S). }

  assert (forall e, issued T e -> f_from' e = f_from e) as ISSEQ_FROM.
  { ins. apply REQ_FROM. by apply TCCOH.(etc_I_in_S). }

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
    subst.
    red; splits; red; splits; eauto.
    { apply TSTEP. }
    { eapply Memory.add_inhabited; eauto. }
    { eapply Memory.add_closed; eauto. }
    simpls.
    exists state; eexists.
    rewrite IdentMap.gss.
    splits; eauto.
    { eapply sim_tview_f_issued with (f_to:=f_to); eauto. }
    eapply tview_closedness_preserved_add; eauto. }
  intros [PCSTEP SIMREL_THREAD']; split; auto.
  intros SMODE SIMREL.
  eapply simrel_fS in SIMREL; eauto.
  eapply full_simrel_step.
  16: by apply SIMREL.
  14: { ins. rewrite IdentMap.Facts.add_in_iff.
        split; auto. intros [|]; auto; subst.
        apply IdentMap.Facts.in_find_iff.
          by rewrite LLH. }
  13: by eapply msg_preserved_add; eauto.
  12: by eapply closedness_preserved_add; eauto.
  10: by eapply same_other_threads_step; eauto.
  all: simpls; eauto.
  { eapply coveredE; eauto. }
  rewrite issuedE; eauto.
  all: basic_solver.
Qed.

End ReservePlainStep.
