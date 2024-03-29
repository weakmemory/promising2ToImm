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
From imm Require Import SimClosure. 
From hahnExt Require Import HahnExt. 
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
From hahnExt Require Import HahnExt.
Require Import MemoryClosedness.
Require Import SimulationRelProperties.
Require Import ExistsIssueNextInterval.
Require Import IssueNextStepHelper.
From imm Require Import Next.
From imm Require Import EventsTraversalOrder.

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

Lemma issue_rel_step_next PC T f_to f_from thread w wnext smode
      (SIMREL_THREAD : simrel_thread G sc PC T f_to f_from thread smode)
      (TSTEP1:
         ext_itrav_step
           G sc (mkTL ta_issue w) T (T ∪₁ eq (mkTL ta_issue w) ∪₁ (eq ta_reserve <*> (eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w)))))
      (TSTEP2:
         ext_itrav_step
           G sc (mkTL ta_cover w)
           (T ∪₁ eq (mkTL ta_issue w) ∪₁ (eq ta_reserve <*> (eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w))))
           (T ∪₁ eq (mkTL ta_cover w) ∪₁ eq (mkTL ta_issue w) ∪₁ (eq ta_reserve <*> (eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w)))))
      (NWEX : ~ W_ex w)
      (REL : Rel w)
      (NEXT : dom_sb_S_rfrmw G T rfi (eq w) wnext)
      (WTID : thread = tid w)
      (FAIR: mem_fair G)
  :
  (* let T' := mkTC (covered T ∪₁ eq w) (issued T ∪₁ eq w) in *)
  (* let S' := S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G (mkETC T S) rfi (eq w) in *)
  let T' := (T ∪₁ eq (mkTL ta_cover w) ∪₁ eq (mkTL ta_issue w) ∪₁ (eq ta_reserve <*> (eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w)))) in
  exists f_to' f_from' PC',
    ⟪ PCSTEP : (plain_step MachineEvent.silent thread)⁺ PC PC' ⟫ /\
    ⟪ SIMREL_THREAD : simrel_thread G sc PC' T' f_to' f_from' thread smode ⟫ /\
    ⟪ SIMREL :
        smode = sim_normal -> simrel G sc PC T f_to f_from ->
        simrel G sc PC' T' f_to' f_from' ⟫.
Proof using WF CON.
  cdes SIMREL_THREAD. cdes COMMON. cdes LOCAL.
  subst.

  (* assert (COV : coverable G sc T w). *)
  (* { eapply ext_itrav_step_cov_coverable with (T:=mkETC T S); eauto. } *)
  assert (NEXTCOV : next G (covered T) w).
  { eapply next_more.
    3: { eapply ext_itrav_step_cov_next; [..| apply TSTEP2];eauto. apply TSTEP1. }
    all: eauto.
    clear. simplify_tls_events. basic_solver. }
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
  
  edestruct issue_step_helper_next as [p_rel PREL]; eauto.
  simpls; desf.

  set (rel'' := TView.cur (Local.tview local)).
  set (rel' := (View.join (View.join rel'' (View.unwrap p_rel))
                          (View.singleton_ur locw (f_to' w)))).

  assert (p_rel = None); subst.
  { red in PREL. destruct PREL; desf.
    exfalso. apply NWEX. red. generalize INRMW. clear. basic_solver. }

  assert (sc_per_loc G) as SC_PER_LOC.
  { by apply coherence_sc_per_loc; cdes CON. }

  assert (~ covered T w) as WNCOV.
  { apply NEXTCOV. }

  cdes STATE.
  edestruct sim_state_to_events as [ev HH]; eauto.
  desc.

  apply clos_rt_rt1n in ESTEPS.
  eapply (rtc_lang_tau_step_rtc_thread_tau_step
            _ _ _ local (Configuration.sc PC) (Configuration.memory PC)) in ESTEPS.

  assert (exists ex ordw, lab w = Astore ex ordw locw valw) as PARAMS; desf.
  { unfold is_w in WW. unfold loc in WLOC. unfold val in WVAL.
    destruct (lab w); desf; eauto. }

  assert (~ dom_rel rmw w) as NNRMW.
  { intros [x RMW]. apply (dom_l (wf_rmwD WF)) in RMW.
    apply seq_eqv_l in RMW. type_solver. }

  assert (Event_imm_promise.same_g_events lab (w :: nil) ev) as SAME.
  { by apply SAME_NRMW. }
  
  assert (ev = ProgramEvent.write locw valw (Event_imm_promise.wmod ordw)) as EV.
  { red in SAME; red in SAME; simpls.
    rewrite PARAMS in *; simpls.
    destruct ev; desf; vauto. }

  set (pe1 := ThreadEvent.write locw (f_from' w) (f_to' w)
                                valw (Some rel') (Event_imm_promise.wmod ordw)).
  assert (ev = ThreadEvent.get_program_event pe1) as EV'.
  { done. }
  set (pe2 :=
         ThreadEvent.promise
           locw (f_from' wnext) (f_to' wnext) Message.reserve
           Memory.op_kind_add).
  
  assert (forall y : actid, covered T y /\ tid y = tid w -> sb y w) as COVSB.
  { intros y [COVY TIDY].
    destruct (same_thread G w y) as [[ST|ST]|ST]; subst; auto.
    { eapply coveredE, COVY; eauto. }
    { done. }
    assert (covered T w) as CC.
    { eapply dom_sb_covered; eauto. eexists. basic_solver. }
    by apply NEXTCOV in CC. }
  
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

  assert (Memory.le (Configuration.memory PC) memory') as LEMEM'.
  { etransitivity; eapply memory_add_le; eauto. }

  assert (Memory.get locw (f_to' w) memory' =
          Some (f_from' w, Message.full valw (Some rel'))) as MEMGET.
  { erewrite Memory.add_o; eauto. rewrite loc_ts_eq_dec_neq; [|by right].
    erewrite Memory.add_o; eauto. by rewrite loc_ts_eq_dec_eq. }

  cdes CON.
  exists f_to', f_from'. eexists.
  apply and_assoc. apply pair_app.
  { split.
    { eapply t_trans; eapply t_step.
      { set (pe' := MachineEvent.silent).
        arewrite (pe' = ThreadEvent.get_machine_event pe1) by simpls.
        eapply plain_step_intro with (lang:=thread_lts (tid w)); eauto.
        2: by unfold pe1; clear; desf.
        apply Thread.step_program.
        constructor.
        { rewrite EV' in STEP; eauto. }
        unfold pe1; eapply Local.step_write.
        econstructor; eauto.
        { unfold TView.write_released. unfold rel', rel''. simpls. desf.
          rewrite View.join_bot_l. rewrite view_join_bot_r.
          unfold LocFun.add. desf. }
        { by constructor. }
        intros _. by eapply nonsynch_loc_le; [|by eauto]. }
      set (pe' := MachineEvent.silent).
      arewrite (pe' = ThreadEvent.get_machine_event pe2) by simpls.
      eapply plain_step_intro with (lang:=thread_lts (tid w)); eauto.
      { simpls. rewrite IdentMap.gss. eauto. }
      2: by unfold pe2; clear; desf.
      apply Thread.step_promise.
      constructor.
      2: by simpls.
      econstructor; eauto. }
    unnw.
    red; splits; red; splits; simpls.
    all: try (rewrite IdentMap.add_add_eq; eauto).
    { apply TSTEP2. }
    { apply TSTEP2. }
    { apply TSTEP2. }
    { clear -RELCOV. simplify_tls_events. relsf. rewrite RELCOV. basic_solver. }
    { ins. clear -RMW NWEX WW RMWCOV WF. 
      etransitivity; [etransitivity| ].
      2: { eapply RMWCOV; eauto. }
      { etransitivity.
        { apply set_equiv_exp. clear. simplify_tls_events. reflexivity. }
        unfolder. split; auto. intros [? | ->]; auto.
        apply wf_rmwD, seq_eqv_lr in RMW; auto. desc. type_solver. }
      etransitivity.
      2: { apply set_equiv_exp. clear. simplify_tls_events. reflexivity. }
      unfolder. split; auto. intros [? | ->]; auto.
      destruct NWEX. red. eexists. eauto. }
    { intros e' EE. 
      apply IdentMap.Facts.add_in_iff.
      destruct (Ident.eq_dec e' (tid w)) as [|NEQ]; subst; auto. }
    { ins.
      destruct (Ident.eq_dec thread' (tid w)) as [EQ|NEQ].
      { subst. rewrite IdentMap.gss in TID.
        etransitivity.
        2: by apply NEW_PROM_IN_MEM.
        inv TID; simpls. }
      red; ins. rewrite IdentMap.gso in TID; auto.
      apply LEMEM'. eapply PROM_IN_MEM; eauto. }
    { ins. etransitivity; [apply SC_COV|]; auto.
      clear. simplify_tls_events. basic_solver. }
    { do 2 (eapply Memory.add_closed; eauto). }
    rewrite IdentMap.gss.
 
    eexists; eexists; eexists; splits; eauto; simpls.
    { erewrite tau_steps_step_same_instrs; eauto. }
    { ins.
      eapply PROM_DISJOINT0; eauto.
      rewrite IdentMap.gso; auto. rewrite IdentMap.gso in TID'; eauto. }
    { red; ins.
      destruct (Ordering.le Ordering.acqrel (Event_imm_promise.wmod ordw)); vauto.
      destruct (classic (b = w)) as [|NEQ].
      { subst.
        unfold loc in LOC; unfold val in VAL; rewrite PARAMS in *; inv LOC.
        eexists (Some _); splits; eauto.
        { eapply Memory.add_closed_timemap; eauto. }
        intros _ H. destruct H. clear. find_event_set. }
      eapply set_equiv_exp in ISSB; [| by clear; simplify_tls_events]. 
      destruct ISSB as [ISSB|]; [|by subst].
      edestruct SIM_MEM as [rel]; eauto.
      simpls; desc.
      rewrite ISSEQ_TO; auto. rewrite ISSEQ_FROM; auto.
      exists rel; splits; auto.
      { eapply sim_mem_helper_f_issued; eauto. }
      { do 2 (eapply Memory.add_closed_timemap; eauto). }
      intros TT COVWB.
      destruct H1 as [PROM REL']; auto; unnw.
      { intros H; apply COVWB. clear -H. find_event_set. }
      split.
      { by apply OLD_PROM_IN_NEW_PROM. }

      (* TODO: generalize! *)
      assert (l = locw -> Time.lt (f_to' w) (f_to b)) as FGT.
      { ins; subst. rewrite <- ISSEQ_TO; auto.
        eapply f_to_co_mon; eauto.
        2: by clear; find_event_set.
        2: { clear -ISSB RCOH. eapply rcoh_I_in_S in ISSB; eauto.
             find_event_set. }
        assert (E b /\ W b) as [EB WB].
        { split; [eapply issuedE | eapply issuedW]; eauto. }
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
        { intros IB. apply COVWB.
          forward eapply init_covered with (x := b) as CB; eauto.
          { split; auto. }
          clear -CB. find_event_set. }
        exfalso. apply COVWB.
        enough (covered T b) as CB; [clear -CB; find_event_set| ]. 
        apply NEXTCOV. eexists. basic_solver. }
      desc. exists p_rel.
      destruct (classic (l = locw)) as [|LL]; subst.
      { exfalso. apply OLD_PROM_IN_NEW_PROM in PROM.
        apply NOWLOC in PROM; auto. inv PROM. }

      simpls.
      unfold LocFun.add. rewrite Loc.eq_dec_neq; auto.
      split; auto.
      destruct REL'0 as [AA|AA]; desc; [left|right].
      { split; auto. intros HH.
        eapply set_equiv_exp in HH; [| by clear; simplify_tls_events].
        eapply set_equiv_exp in HH; [| by rewrite id_union, !seq_union_l, codom_union].
        destruct HH as [ | HH]; [done| ].
        exfalso.
        enough (Some locw = Some l) as HH_.
        { inv HH. }
        rewrite <- LOC, <- WLOC.
        eapply (wf_rfrmwl WF). by destruct HH as [w_ [-> ?]%seq_eqv_l]. }
      exists p. splits; eauto.
      { clear -AA. find_event_set. }
      exists p_v. split; auto. rewrite ISSEQ_TO; auto. rewrite ISSEQ_FROM; auto. }
    { simplify_tls_events. eapply sim_tview_write_step; eauto.
      { by apply coveredE. }
      { apply doma_alt. eapply dom_sb_covered; eauto. }
      { eapply sim_tview_f_issued; eauto. }
      apply doma_alt. apply NEXTCOV. }
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
      { do 2 (eapply Memory.add_closed_timemap; eauto). apply MEM_CLOSE. }
      assert (Memory.closed_timemap (View.rlx (TView.acq (Local.tview local))) memory')
             as ACQA.
      { do 2 (eapply Memory.add_closed_timemap; eauto). apply MEM_CLOSE. }
      assert (Memory.closed_timemap (TimeMap.singleton locw (f_to' w)) memory') as SINA.
      { eapply Memory.singleton_closed_timemap; eauto. }
      unfold TView.write_tview; simpls.
      red; splits; simpls.
      all: desf; ins.
      all: repeat (apply Memory.join_closed_timemap); auto.
      unfold LocFun.add, LocFun.find; desf.
      2: { do 2 (eapply Memory.add_closed_timemap; eauto). apply MEM_CLOSE. }
      apply Memory.join_closed_timemap; auto. }
    red. splits; eauto.
    ins. rewrite INDEX_NRMW; auto.
    etransitivity.
    { apply set_equiv_exp. clear. simplify_tls_events. reflexivity. }
    apply sim_state_cover_event; auto. }

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
  11: { simpls. eapply msg_preserved_trans; eapply msg_preserved_add; eauto. }
  10: { simpls. eapply closedness_preserved_trans; eapply closedness_preserved_add; eauto. }
  9: by eapply same_other_threads_steps; eauto.
  all: simpls; eauto.
  { eapply coveredE; eauto. apply TSTEP2. }
  { eapply issuedE; eauto. apply TSTEP2. }
  1-6: clear -WF NINIT; simplify_tls_events; try basic_solver. 
  { rewrite dom_sb_S_rfrmw_same_tid; auto. basic_solver. }
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
