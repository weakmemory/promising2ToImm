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

Set Implicit Arguments.

Section IssuePlainStep.

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

Lemma issue_rel_step_no_next PC T S f_to f_from thread w smode
      (SIMREL_THREAD : simrel_thread G sc PC T S f_to f_from thread smode)
      (TSTEP1 :
         ext_itrav_step
           G sc w (mkETC T S)
           (mkETC
              (mkTC (covered T) (issued T ∪₁ eq w))
              (S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G (mkETC T S) rfi (eq w))))
      (TSTEP2 :
         ext_itrav_step
           G sc w
           (mkETC
              (mkTC (covered T) (issued T ∪₁ eq w))
              (S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G (mkETC T S) rfi (eq w)))
           (mkETC
              (mkTC (covered T ∪₁ eq w) (issued T ∪₁ eq w))
              (S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G (mkETC T S) rfi (eq w))))
      (NWEX : ~ W_ex w)
      (REL : Rel w)
      (NONEXT : dom_sb_S_rfrmw G (mkETC T S) rfi (eq w) ⊆₁ ∅)
      (WTID : thread = tid w) :
  let T' := mkTC (covered T ∪₁ eq w) (issued T ∪₁ eq w) in
  let S' := S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G (mkETC T S) rfi (eq w) in
  exists f_to' f_from' PC',
    ⟪ PCSTEP : (plain_step MachineEvent.silent thread)⁺ PC PC' ⟫ /\
    ⟪ SIMREL_THREAD : simrel_thread G sc PC' T' S' f_to' f_from' thread smode ⟫ /\
    ⟪ SIMREL :
        smode = sim_normal -> simrel G sc PC T S f_to f_from ->
        simrel G sc PC' T' S' f_to' f_from' ⟫.
Proof using WF CON.
  cdes SIMREL_THREAD. cdes COMMON. cdes LOCAL.
  subst.

  assert (tc_coherent G sc T) as TCCOHs by apply TCCOH.
  
  (* assert (COV : coverable G sc T w). *)
  (* { eapply ext_itrav_step_cov_coverable with (T:=mkETC T S); eauto. } *)
  assert (NEXT : next G (covered T) w).
  { eapply ext_itrav_step_cov_next with
        (T:=mkETC (mkTC (covered T) (issued T ∪₁ eq w)) _); eauto.
    apply TSTEP1. }
  assert (~ issued T w) as NISSB.
  { eapply ext_itrav_step_iss_nI with (T:=mkETC T S); eauto. }
  assert (issuable G sc T w) as ISSUABLE.
  { eapply ext_itrav_step_iss_issuable with (T:=mkETC T S); eauto. }
  assert (S ⊆₁ E ∩₁ W) as SEW.
  { apply set_subset_inter_r. split; [by apply TCCOH|].
    apply (reservedW WF TCCOH). }
  assert (E w /\ W w) as [EW WW] by (by apply ISSUABLE).
  assert (~ is_init w) as NINIT.
  { intros AA. apply NISSB. eapply init_issued; eauto. by split. }

  assert (exists locw, loc lab w = Some locw) as [locw WLOC] by (by apply is_w_loc).
  assert (exists valw, val lab w = Some valw) as [valw WVAL] by (by apply is_w_val).
  
  assert (NSW : ~ S w).
  { intros HH. apply NWEX. apply TCCOH. by split. }
  
  edestruct issue_step_helper_no_next as [p_rel PREL]; eauto.
  simpls; desf.

  set (rel'' := TView.cur (Local.tview local)).
  set (rel' := (View.join (View.join rel'' p_rel.(View.unwrap))
                          (View.singleton_ur locw (f_to' w)))).

  assert (p_rel = None); subst.
  { red in PREL. destruct PREL; desf.
    exfalso. apply NWEX. red. generalize INRMW. clear. basic_solver. }

  assert (tc_coherent G sc T) as sTCCOH by apply TCCOH.

  assert (sc_per_loc G) as SC_PER_LOC.
  { by apply coherence_sc_per_loc; cdes CON. }

  assert (~ covered T w) as WNCOV.
  { apply NEXT. }

  cdes STATE.
  edestruct sim_state_to_events as [ev HH]; eauto.
  desc.

  apply clos_rt_rt1n in ESTEPS.
  eapply (rtc_lang_tau_step_rtc_thread_tau_step
            _ _ _ local PC.(Configuration.sc) PC.(Configuration.memory)) in ESTEPS.

  assert (exists ex ordw, lab w = Astore ex ordw locw valw) as PARAMS; desf.
  { unfold is_w in WW. unfold loc in WLOC. unfold val in WVAL.
    destruct (lab w); desf; eauto. }

  assert (~ dom_rel rmw w) as NNRMW.
  { intros [x RMW]. apply (dom_l WF.(wf_rmwD)) in RMW.
    apply seq_eqv_l in RMW. type_solver. }

  assert (Event_imm_promise.same_g_events lab (w :: nil) ev) as SAME.
  { by apply SAME_NRMW. }
  
  assert (ev = ProgramEvent.write locw valw (Event_imm_promise.wmod ordw)) as EV.
  { red in SAME; red in SAME; simpls.
    rewrite PARAMS in *; simpls.
    destruct ev; desf; vauto. }

  set (pe := ThreadEvent.write locw (f_from' w) (f_to' w)
                               valw (Some rel') (Event_imm_promise.wmod ordw)).
  assert (ev = ThreadEvent.get_program_event pe) as EV'.
  { done. }
  
  assert (forall y : actid, covered T y /\ tid y = tid w -> sb y w) as COVSB.
  { intros y [COVY TIDY].
    destruct (same_thread G w y) as [[ST|ST]|ST]; subst; auto.
    { apply TCCOH in COVY; apply COVY. }
    { done. }
    assert (covered T w) as CC.
    { apply TCCOH in COVY. apply COVY.
      eexists; apply seq_eqv_r; eauto. }
      by apply NEXT in CC. }
  
  assert (Rlx w) as WRLX.
  { apply ALLRLX. by split. }

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
  
  (* edestruct (Memory.remove_exists (Local.promises local) locw) *)
  (*   as [new_prom NPCH]. *)
  (* { edestruct (SIM_MEM locw w) as [rel' HH]; eauto. } *)
  
  (* destruct REL_REP as [p_rel]; desf. *)
  (* 2: { exfalso. apply NRMW. destruct INRMW as [z H]. *)
  (*      eexists. apply H; done. } *)

  assert (Memory.le (Local.promises local) promises') as LELCL'.
  { red. ins. erewrite Memory.remove_o; eauto.
    desf; simpls; desc; subst.
    { exfalso.
      assert (LHS' : Memory.get locw (f_to' w) (Local.promises local) = None).
      { eapply Memory.add_get0; eauto. }
      rewrite LHS' in LHS. inv LHS'. }
    erewrite Memory.add_o; eauto. rewrite loc_ts_eq_dec_neq; eauto. }
  assert (Memory.le promises' (Local.promises local)) as LELCL''.
  { red. ins. erewrite Memory.remove_o in LHS; eauto.
    desf; simpls; desc; subst.
    erewrite Memory.add_o in LHS; eauto. rewrite loc_ts_eq_dec_neq in LHS; eauto. }

  assert (Memory.le (Configuration.memory PC) memory') as LEMEM'.
  { eapply memory_add_le; eauto. }

  
  assert (Memory.get locw (f_to' w) memory' =
          Some (f_from' w, Message.full valw (Some rel'))) as MEMGET.
  { erewrite Memory.add_o; eauto. by rewrite loc_ts_eq_dec_eq. }

  cdes CON.
  exists f_to', f_from'. eexists.
  apply and_assoc. apply pair_app.
  { split.
    { eapply t_step.
      set (pe' := MachineEvent.silent).
      arewrite (pe' = ThreadEvent.get_machine_event pe) by simpls.
      eapply plain_step_intro with (lang:=thread_lts (tid w)); eauto.
      2: by unfold pe; clear; desf.
      apply Thread.step_program.
      constructor.
      { rewrite EV' in STEP; eauto. }
      unfold pe; eapply Local.step_write.
      econstructor; eauto.
      { unfold TView.write_released. unfold rel', rel''. simpls. desf.
        rewrite View.join_bot_l. rewrite view_join_bot_r.
        unfold LocFun.add. desf. }
      { by constructor. }
      intros _. by eapply nonsynch_loc_le; [|by eauto]. }
    unnw.
    red; splits; red; splits; simpls.
    all: try (rewrite IdentMap.add_add_eq; eauto).
    { apply TSTEP2. }
    { generalize REL RELCOV. clear. basic_solver 10. }
    { ins. set (AA:=RMW). apply RMWCOV in AA.
      ins; split; intros HH; left.
      all: destruct HH as [HH|HH]; (try by apply AA).
      all: subst; exfalso.
      2: { apply NWEX. do 2 red. eauto. }
      apply NNRMW. red. eauto. }
    { intros e' EE. 
      destruct (Ident.eq_dec (tid e') (tid w)) as [EQ|NEQ].
      { rewrite EQ. eexists.
        rewrite IdentMap.gss; eauto. }
      rewrite IdentMap.gso; auto. }
    { ins.
      destruct (Ident.eq_dec thread' (tid w)) as [EQ|NEQ].
      { subst. rewrite IdentMap.gss in TID.
        etransitivity.
        2: by apply NEW_PROM_IN_MEM.
        inv TID; simpls. }
      red; ins. rewrite IdentMap.gso in TID; auto.
      apply LEMEM'. eapply PROM_IN_MEM; eauto. }
    { ins. etransitivity; [apply SC_COV|]; auto.
      basic_solver. }
    { eapply Memory.add_closed; eauto. }
    rewrite IdentMap.gss.
 
    eexists; eexists; eexists; splits; eauto; simpls.
    { erewrite tau_steps_step_same_instrs; eauto. }
    { ins. rewrite IdentMap.gso in TID'; auto.
      edestruct (PROM_DISJOINT thread') as [HH|]; eauto.
      left. destruct (Memory.get loc to promises') eqn:AA; auto.
      destruct p. eapply LELCL'' in AA. by rewrite HH in AA. }
    { red; ins.
      destruct (Ordering.le Ordering.acqrel (Event_imm_promise.wmod ordw)); vauto.
      destruct (classic (b = w)) as [|NEQ].
      { subst.
        unfold loc in LOC; unfold val in VAL; rewrite PARAMS in *; inv LOC.
        eexists (Some _); splits; eauto.
        intros _ H. by exfalso; apply H; right. }
      destruct ISSB as [ISSB|]; [|by subst].
      edestruct SIM_MEM as [rel]; eauto.
      simpls; desc.
      rewrite ISSEQ_TO; auto. rewrite ISSEQ_FROM; auto.
      exists rel; splits; auto.
      { eapply sim_mem_helper_f_issued; eauto. }
      { eapply Memory.add_closed_timemap; eauto. }
      intros TT COVWB.
      destruct H1 as [PROM REL']; auto; unnw.
      { by intros H; apply COVWB; left. }
      split.
      { by apply LELCL'. }

      (* TODO: generalize! *)
      assert (l = locw -> Time.lt (f_to' w) (f_to b)) as FGT.
      { ins; subst. rewrite <- ISSEQ_TO; auto.
        eapply f_to_co_mon; eauto.
        assert (E b /\ W b) as [EB WB] by (by apply TCCOH).
        assert (co w b \/ co b w) as H; [|destruct H as [|H]; [done|exfalso]].
        { edestruct (@wf_co_total G WF (Some locw)); eauto.
          all: by red; split; [red; split|]; auto. }
        cdes CON.
        eapply Cint.
        eexists; split.
        2: { apply r_step. red. left; right.
             eexists; split; eauto. }
        apply sb_in_hb.
        edestruct (same_thread G b w) as [[HH|HH]|]; vauto.
        { intros IB. apply COVWB; left. by apply TCCOH. }
        exfalso.
        apply COVWB; left.
        apply NEXT. eexists; apply seq_eqv_r; eauto.
        2: by do 2 left; apply TCCOH.(etc_I_in_S).
        clear. basic_solver. }
      desc. exists p_rel.
      destruct (classic (l = locw)) as [|LL]; subst.
      { exfalso. apply LELCL' in PROM.
        apply NOWLOC in PROM; auto. inv PROM. }

      simpls.
      unfold LocFun.add. rewrite Loc.eq_dec_neq; auto.
      split; auto.
      destruct REL'0 as [AA|AA]; desc; [left|right].
      { split; auto. intros HH.
        unfolder in HH. desf.
        { apply AA. basic_solver 10. }
        exfalso.
        enough (Some locw = Some l) as HH.
        { inv HH. }
        rewrite <- LOC, <- WLOC.
        eapply WF.(wf_rfrmwl). eexists; eauto. }
      exists p. splits; eauto.
      { red; eauto. }
      exists p_v. split; auto. rewrite ISSEQ_TO; auto. rewrite ISSEQ_FROM; auto. }
    { eapply sim_tview_write_step; eauto.
      { etransitivity; [by apply TCCOH|].
        intros x H; apply H. }
      { intros x y H. apply seq_eqv_r in H; destruct H as [H1 H2].
        apply TCCOH in H2. apply H2. eexists; apply seq_eqv_r; eauto. }
      { eapply sim_tview_f_issued; eauto. }
      unfolder. ins. desf. apply NEXT. basic_solver 10. }
    { cdes PLN_RLX_EQ. 
      unfold TView.write_tview.
      red; splits; simpls.
      all: desf; simpls.
      all: try rewrite EQ_CUR.
      all: try rewrite EQ_ACQ.
      1-2: reflexivity.
      all: unfold LocFun.add, LocFun.find, View.join; intros l.
      all: desf; simpls.
      all: rewrite EQ_CUR; reflexivity. }
    { assert (Memory.closed_timemap (View.rlx (TView.cur (Local.tview local))) memory')
             as CURA.
      { eapply Memory.add_closed_timemap; eauto. apply MEM_CLOSE. }
      assert (Memory.closed_timemap (View.rlx (TView.acq (Local.tview local))) memory')
             as ACQA.
      { eapply Memory.add_closed_timemap; eauto. apply MEM_CLOSE. }
      assert (Memory.closed_timemap (TimeMap.singleton locw (f_to' w)) memory') as SINA.
      { eapply Memory.singleton_closed_timemap; eauto. }
      unfold TView.write_tview; simpls.
      red; splits; simpls.
      all: desf; ins.
      all: repeat (apply Memory.join_closed_timemap); auto.
      unfold LocFun.add, LocFun.find; desf.
      2: { eapply Memory.add_closed_timemap; eauto. apply MEM_CLOSE. }
      apply Memory.join_closed_timemap; auto. }
    red. splits; eauto.
    ins. rewrite INDEX_NRMW; auto.
    apply sim_state_cover_event; auto. }
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
  eapply simrel_thread_local_step with (thread:=tid w) (PC:=PC) (T:=T) (S:=S); eauto.
  11: { simpls. eapply msg_preserved_add; eauto. }
  10: { simpls. eapply closedness_preserved_add; eauto. }
  9: by eapply same_other_threads_steps; eauto.
  all: simpls; eauto.
  { rewrite coveredE; eauto. generalize EW. clear. basic_solver. }
  { rewrite issuedE; eauto. generalize EW. clear. basic_solver. }
  1-5: clear; basic_solver.
  { rewrite dom_sb_S_rfrmw_same_tid; auto. clear. basic_solver. }
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
