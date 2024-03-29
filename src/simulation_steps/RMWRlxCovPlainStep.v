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
From imm Require Import SimClosure.

From hahnExt Require Import HahnExt.
From hahnExt Require Import HahnExt.
From imm Require Import TraversalOrder. 
From imm Require Import TLSCoherency.
From imm Require Import IordCoherency.
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
Require Import ReadPlainStepHelper.
From imm Require Import Next.
From imm Require Import EventsTraversalOrder.
From hahnExt Require Import HahnExt.

Set Implicit Arguments.

Section RMWRlxCovPlainStep.

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

Lemma rlx_rmw_cover_step PC T f_to f_from thread r w smode
      (SIMREL_THREAD : simrel_thread G sc PC T f_to f_from thread smode)
      (TID : tid r = thread)
      (ISS : issued T w)
      (REL : ~ Rel w) (RMW : rmw r w)
      (TS1 : ext_itrav_step
               G sc (mkTL ta_cover r)
               T
               (* (mkETC (mkTC (covered T ∪₁ eq r) (issued T)) S) *)
               (T ∪₁ eq (mkTL ta_cover r))
      )
      (TS2 : ext_itrav_step
               G sc (mkTL ta_cover w)
               (T ∪₁ eq (mkTL ta_cover r))
               (* (mkETC (mkTC (covered T ∪₁ eq r ∪₁ eq w) (issued T)) S) *)
               (T ∪₁ eq (mkTL ta_cover r) ∪₁ eq (mkTL ta_cover w))
      ) :
  let T' := (T ∪₁ eq (mkTL ta_cover r) ∪₁ eq (mkTL ta_cover w)) in
  exists PC',
    ⟪ PCSTEP : plain_step MachineEvent.silent thread PC PC' ⟫ /\
    ⟪ SIMREL_THREAD : simrel_thread G sc PC' T' f_to f_from thread smode ⟫ /\
    ⟪ SIMREL :
        smode = sim_normal -> simrel G sc PC T f_to f_from ->
        simrel G sc PC' T' f_to f_from ⟫.
Proof using WF CON.
  cdes SIMREL_THREAD. cdes COMMON. cdes LOCAL.
  set (X := STATE).

  assert (COV : coverable G sc T r).
  { eapply ext_itrav_step_cov_coverable; eauto. }
  assert (NEXT : next G (covered T) r).
  { eapply ext_itrav_step_cov_next; eauto. }

  assert (sc_per_loc G) as SC_PER_LOC.
  { by apply coherence_sc_per_loc; cdes CON. }

  assert (~ covered T r) as RNCOV.
  { apply NEXT. }

  cdes STATE. rewrite <- TID in *.
  edestruct sim_state_to_events as [ev HH]; eauto.
  desc.

  apply clos_rt_rt1n in ESTEPS.
  eapply (rtc_lang_tau_step_rtc_thread_tau_step
            _ _ _ local (Configuration.sc PC) (Configuration.memory PC)) in ESTEPS.

  assert (E r /\ E w) as [RACT WACT].
  { apply (wf_rmwE WF) in RMW.
    apply seq_eqv_l in RMW; destruct RMW as [WW RMW].
    apply seq_eqv_r in RMW; desf. }

  assert (R r /\ W w) as [RREAD WWRITE].
  { apply (wf_rmwD WF) in RMW.
    apply seq_eqv_l in RMW; destruct RMW as [WW RMW].
    apply seq_eqv_r in RMW; desf. }

  assert (exists w', rf w' r) as [w' RF].
  { by cdes CON; eapply Comp; split. }

  assert (exists xrmw locr valr ordr, lab r = Aload xrmw ordr locr valr) as PARAMS; desf.
  { unfold is_r in RREAD.
    destruct (lab r); desf.
      by exists ex; exists l; exists v; exists o. }
  assert (exists xordw locw valw ordw, lab w = Astore xordw ordw locw valw) as WPARAMS; desf.
  { unfold is_w in WWRITE.
    destruct (lab w); desf.
      by exists s; exists l; exists v; exists o. }

  assert (locw = locr) as SAME_PARAMS; subst.
  { apply (wf_rmwl WF) in RMW.
    unfold same_loc, loc in *; desf. }

  assert (issued T w') as WISS.
  { eapply dom_rf_coverable; eauto. basic_solver 10. }

  assert (~ is_init r) as RNINIT.
  { intros H; apply (init_w WF) in H.
    type_solver. }
  assert (sb r w) as WRSB.
  { apply wf_rmwi in RMW; red in RMW; desf. }

  assert (~ covered T w) as WNCOV.
  { intros COVw. apply RNCOV. eapply dom_sb_covered; eauto. basic_solver 10. }
  assert (~ is_init w) as WNINIT.
  { intros H. apply WNCOV. eapply init_covered; basic_solver. }

  assert (loc lab r = Some locr) as RLOC.
  { unfold loc. by rewrite PARAMS. }
  assert (val lab r = Some valr) as RVAL.
  { unfold val. by rewrite PARAMS. }

  assert (loc lab w = Some locr) as WLOC.
  { unfold loc. by rewrite WPARAMS. }
  assert (val lab w = Some valw) as WVAL.
  { unfold val. by rewrite WPARAMS. }

  assert (W w') as WPWRITE.
  { apply (wf_rfD WF) in RF. apply seq_eqv_l in RF; desf. }
  assert (E w') as WPACT.
  { apply (wf_rfE WF) in RF. apply seq_eqv_l in RF; desf. }
  assert (loc lab w' = Some locr) as WPLOC.
  { assert (loc lab w' = loc lab r) as HH.
    { by apply (wf_rfl WF). }
    rewrite HH.
      by unfold loc; rewrite PARAMS. }
  assert (val lab w' = Some valr) as WPVAL.
  { assert (val lab w' = val lab r) as HH.
    { by apply wf_rfv. }
    rewrite HH.
      by unfold val; rewrite PARAMS. }

  assert (co w' w) as COWPW.
  { cdes CON.
    eapply rf_rmw_in_co; eauto.
    eexists; eauto. }

  assert (tid w = tid r) as TIDWR.
  { destruct (sb_tid_init WRSB); desf. }

  edestruct SIM_MEM with (b:=w) as [rel DOM].
  all: eauto.
  simpls. desc.

  edestruct SIM_MEM with (b:=w') as [rel' DOM'].
  all: eauto.
  simpls. desc.
  clear DOM'1.

  assert ((rf ⨾ rmw) w' w) as RFRMW.
  { exists r; split; auto. }
  
  destruct DOM1 as [WMEM [p_rel]]; eauto. desc.
  destruct H0; desc.
  { exfalso. apply NINRMW. exists w'. apply seq_eqv_l; split; auto. }
  assert (p = w'); subst.
  { eapply wf_rfrmwf; eauto. }
  rewrite INMEM0 in P_INMEM. inv P_INMEM. clear P_INMEM.
  rename p_v into valr. rename p_rel into rel'.
  
  destruct (SAME_RMW w RMW) as [SAME WREPR].
  assert (ev = ProgramEvent.update
                  locr valr valw
                  (Event_imm_promise.rmod ordr)
                  (Event_imm_promise.wmod ordw)) as EV.
  { red in SAME; red in SAME; simpls.
    rewrite PARAMS in *; simpls.
    rewrite WPARAMS in *; simpls.
    destruct ev; desf; vauto. }

  assert (Events.mod lab r = ordr) as RORD.
  { unfold Events.mod. by rewrite PARAMS. }
  assert (Events.mod lab w = ordw) as WORD.
  { unfold Events.mod. by rewrite WPARAMS. }

  set (pe := ThreadEvent.update locr (f_from w) (f_to w) valr valw
                                rel' (Some (View.join
                                              (View.join
                                                 (TView.rel (Local.tview local) locr)
                                                 (View.unwrap rel'))
                                     (View.singleton_ur locr (f_to w))))
                                (Event_imm_promise.rmod ordr) (Event_imm_promise.wmod ordw)).
  assert (ev = ThreadEvent.get_program_event pe) as EV'.
  { done. }

  assert (Rlx r /\ Rlx w) as [RRLX WRLX].
  { split. all: apply ALLRLX; by split. }

  assert (Ordering.le Ordering.relaxed (Event_imm_promise.rmod ordr)) as RLX_ORDR.
  { unfold is_rlx, mode_le, Events.mod in *; simpls.
    rewrite PARAMS in *.
    destruct ordr; simpls. }
  assert (Ordering.le Ordering.relaxed (Event_imm_promise.wmod ordw)) as RLX_ORDW.
  { unfold is_rlx, mode_le, Events.mod in *; simpls.
    rewrite WPARAMS in *.
    destruct ordw; simpls. }
  assert (~ Ordering.le Ordering.acqrel (Event_imm_promise.wmod ordw)) as NREL_ORDW.
  { unfold is_rel, mode_le, Events.mod in *; simpls.
    rewrite WPARAMS in *.
    destruct ordw; simpls. }
  assert (~ Ordering.le Ordering.strong_relaxed (Event_imm_promise.wmod ordw)) as NSRLX_ORDW.
  { unfold is_rel, mode_le, Events.mod in *; simpls.
    rewrite WPARAMS in *.
    destruct ordw; simpls. }

  assert (reserved T w) as WS.
  { eapply rcoh_I_in_S; eauto. }
  assert (reserved T w') as WS'.
  { eapply rcoh_I_in_S; eauto. }

  assert (Time.lt (f_from w) (f_to w)) as LTFF.
  { apply FCOH; auto. }
  
  assert (f_to w' = f_from w) as FF.
  { apply FCOH; auto. } 

  edestruct (Memory.remove_exists (Local.promises local) locr)
    as [new_prom NPCH].
  { eauto. }

  assert (reserved T ⊆₁ E ∩₁ W) as SEW.
  { generalize rcoh_S_in_E, reservedW. basic_solver. }

  assert (is_init ∩₁ E ⊆₁ reserved T) as IES.
  { rewrite <- rcoh_I_in_S; eauto. 
    eapply init_issued; eauto. }
  
  assert (Time.lt Time.bot (f_to w)) as LT_BOT.
  { eapply lt_init_ts with (I:=reserved T); eauto. }

  assert (forall y (TIDY : tid y = tid r) (COVY : covered T y), sb y r) as SBYR_gen.
  { ins.
    assert (E y) as EY.
    { eapply coveredE; eauto. }
    destruct (classic (is_init y)) as [II|II].
    { apply init_ninit_sb; auto.  }
    edestruct same_thread with (x:=y) (y:=r) as [[|SB]|SB]; eauto.
    { by subst. }
    destruct RNCOV. eapply dom_sb_covered; eauto. basic_solver 10. }

  assert (wf_sc G sc) as WFSC by apply CON. 
  
  assert (Time.lt (View.rlx (TView.cur (Local.tview local)) locr) (f_to w)) as CUR_LT.
  { cdes SIM_TVIEW. specialize (CUR locr).
    red in CUR. desc.
    destruct MAX as [[MM1 MM2]|[a_max MM]].
    { unfold LocFun.find in *. rewrite MM2; auto. }
    desc.
    eapply TimeFacts.le_lt_lt; eauto.
    assert (issued T a_max) as ISSA.
    { eapply t_cur_covered; eauto. }
    destruct INam as [y CCUR]. red in CCUR.
    apply seqA in CCUR.
    apply seq_eqv_r in CCUR. destruct CCUR as [CCUR COVY].
    apply seq_eqv_r in CCUR. destruct CCUR as [CCUR IIY].
    assert (E y) as EY.
    { eapply coveredE; eauto. }
    assert (sb y r) as SBYR.
    { destruct IIY as [TT|].
      { apply SBYR_gen; auto. }
      apply init_ninit_sb; auto.  }
    assert (sb y w) as SBYW.
    { eapply sb_trans; eauto. }
    destruct (classic (a_max = w)) as [AWEQ|AWNEQ].
    { rewrite AWEQ in *. clear a_max AWEQ.
      exfalso. eapply urr_hb_irr.
      6: { eexists. split; eauto. by apply sb_in_hb. }
      all: auto.
      all: apply CON. }
    assert (E a_max) as EA.
    { eapply issuedE; eauto. }
    assert (W a_max) as WA.
    { apply wf_urrD in CCUR; auto. 
      apply seq_eqv_l in CCUR. apply CCUR. }
    assert (loc lab a_max = Some locr) as LOCA.
    { apply wf_urrD in CCUR; auto. 
      apply seq_eqv_l in CCUR. apply CCUR. }
    eapply f_to_co_mon; eauto.
    edestruct (wf_co_total WF) as [|CO].
    3: by apply AWNEQ.
    1,2: split; [split|]; auto.
    { by rewrite LOCA. }
    { done. }
    exfalso. eapply eco_urr_irr.
    5: { eexists. split.
         { apply co_in_eco. apply CO. }
         apply urr_hb. exists y. split; eauto.
         apply r_step. by apply sb_in_hb. }
    { done. }
    all: try apply CON.
    eapply rcoh_I_in_S; eauto. }

  assert (Time.lt (View.rlx (View.unwrap rel') locr) (f_to w)) as REL_LT.
  { red in HELPER0. desc.
    specialize (SIMMSG locr).
    red in SIMMSG. desc.
    destruct MAX as [[MM1 MM2]|[a_max MM]].
    { unfold LocFun.find in *. rewrite MM2; auto. }
    desc.
    eapply TimeFacts.le_lt_lt; eauto.
    destruct INam as [INam|[_ INam]].
    2: { rewrite INam. eapply f_to_co_mon; eauto. }
    assert (issued T a_max) as ISSA.
    { eapply msg_rel_issued; eauto.      
      eexists. apply seq_eqv_r. eauto. }
    assert (E a_max) as EA.
    { eapply issuedE; eauto. }
    destruct INam as [y [CCUR RELES]].
    assert (W a_max) as WA.
    { apply wf_urrD in CCUR; auto. 
      apply seq_eqv_l in CCUR. apply CCUR. }
    assert (loc lab a_max = Some locr) as LOCA.
    { apply wf_urrD in CCUR; auto. 
      apply seq_eqv_l in CCUR. apply CCUR. }
    eapply f_to_co_mon; eauto.
    destruct (classic (a_max = w)) as [AWEQ|AWNEQ].
    { rewrite AWEQ in *. clear a_max AWEQ.
      exfalso. eapply release_co_urr_irr.
      6: { exists w'. split; eauto.
           exists w. split; eauto. }
      { done. }
      all: apply CON. }
    edestruct (wf_co_total WF) as [|CO].
    3: by apply AWNEQ.
    1,2: split; [split|]; auto.
    { by rewrite LOCA. }
    { done. }
    exfalso. eapply release_co_urr_irr.
    6: { eexists. split.
         2: { eexists. split; [by apply CO|].
              eauto. }
         assert (release G ⨾ (rf ⨾ rmw) ⊆ release G) as XX.
         { unfold release, rs. rewrite !seqA. by rewrite rt_unit. }
         apply XX. eexists. split; eauto. }
    { done. }
    all: try apply CON.
    eapply rcoh_I_in_S; eauto. }

  eexists.
  apply and_assoc. apply pair_app.
  { split.
    { set (pe' := MachineEvent.silent).
      assert (pe' = ThreadEvent.get_machine_event pe) as H.
      { unfold pe. simpls. }
      rewrite H. clear H.
      econstructor; eauto.
      apply Thread.step_program.
      constructor.
      { rewrite EV' in STEP; eauto. }
      unfold pe; eapply Local.step_update.
      { econstructor; eauto.
        { rewrite <- FF. eauto. }
        assert
          (Time.le (View.rlx (TView.cur (Local.tview local)) locr) (f_from w))
          as PP.
        2: constructor; auto.
        2: by cdes PLN_RLX_EQ; rewrite EQ_CUR.
        edestruct (max_event_cur) as [a_max]; eauto; desc.
        assert (E a_max) as EA.
        { apply (wf_urrE WF) in CCUR.
          revert CCUR; unfold seq; unfolder; ins; desf.
            by apply CON. }
        assert (issued T a_max) as AISS.
        { assert (A: (urr G sc locr ⨾ ⦗coverable G sc T⦘) a_max r).
            by basic_solver.
            apply (urr_coverable) in A; try done.
            revert A; unfold seq; unfolder; ins; desf. }
        rewrite <- FF.
        destruct (classic (a_max = w')) as [|AWNEQ]; [by desf|].
        edestruct (@wf_co_total G WF (Some locr) a_max) as [AWCO|AWCO].
        3: apply AWNEQ.
        2: basic_solver.
        apply set_interA; split; auto.
        hahn_rewrite (@wf_urrD G sc locr) in CCUR.
        revert CCUR; clear; basic_solver 12.
        { etransitivity; eauto.
          apply Time.le_lteq; left.
          eapply f_to_co_mon; eauto.
          eapply rcoh_I_in_S; eauto. }
        exfalso.
        eapply transp_rf_co_urr_irr; eauto.
        1-2: by apply CON.
        exists w'; split.
        { right; red; apply RF. }
        exists a_max; split; eauto. }
      econstructor; eauto.
      4: by desf.
      { unfold TView.write_released, TView.write_tview. simpls. rewrite RLX_ORDW.
        destruct (Ordering.le Ordering.acqrel (Event_imm_promise.wmod ordw)); simpls.
        unfold LocFun.add. rewrite Loc.eq_dec_eq.
        rewrite (View.join_comm (TView.rel (Local.tview local) locr)).
          by rewrite View.join_assoc. }
      { unfold TView.write_released, TView.read_tview. simpls.
        constructor. rewrite RLX_ORDR. unfold View.join, TimeMap.join. simpls.
        apply TimeFacts.join_spec_lt; [apply TimeFacts.join_spec_lt|]; auto.
        { unfold TimeMap.singleton, LocFun.add. rewrite Loc.eq_dec_eq.
          apply FCOH; auto. }
        destruct (Ordering.le Ordering.acqrel (Event_imm_promise.rmod ordr)); auto. }
      econstructor.
      2: by apply NPCH.
      apply Memory.promise_lower; eauto; simpls.
      4: done.
      1,2: apply Memory.lower_exists_same; auto.
      1,2: constructor.
      1,2: do 2 constructor; simpls.
      1,2: rewrite REL_PLN_RLX; reflexivity.
      constructor.
      simpls. unfold TimeMap.join.
      apply Time.join_spec.
      2: { unfold TimeMap.singleton, LocFun.add. 
           rewrite Loc.eq_dec_eq. apply DenseOrder_le_PreOrder. }
      apply Time.le_lteq. left. apply TimeFacts.join_spec_lt; auto.
      eapply TimeFacts.le_lt_lt.
      2: by apply CUR_LT.
      eapply rel_le_cur; eauto. }
    unnw.
    assert (covered (T ∪₁ eq (mkTL ta_cover r) ∪₁ eq (mkTL ta_cover w)) ≡₁ covered T ∪₁ eq r ∪₁ eq w) as COV'.
    { simplify_tls_events. basic_solver. }
    red; splits; red; splits; simpls.
    1-3: by apply TS2. 
    { clear -RELCOV. simplify_tls_events. rewrite RELCOV. basic_solver. }
    { ins. apply (wf_rmwD WF) in RMW0.
      apply seq_eqv_l in RMW0; destruct RMW0 as [RR RMW0].
      apply seq_eqv_r in RMW0; destruct RMW0 as [RMW0 WW].
      split; intros [[HH|HH]|HH]%COV'; apply COV'. 
      { left; left. erewrite <- RMWCOV; eauto. }
      { subst. right. eapply wf_rmwf; eauto. }
      { type_solver. }
      { left; left. erewrite RMWCOV; eauto. }
      { type_solver. }
      subst. left; right.
      eapply wf_rmw_invf; eauto. }
    { intros e' EE. 
      apply IdentMap.Facts.add_in_iff.
      destruct (Ident.eq_dec e' (tid r)) as [|NEQ]; subst; auto. }
    { ins.
      destruct (Ident.eq_dec thread' (tid r)) as [EQ|NEQ].
      { subst. rewrite IdentMap.gss in TID.
        inv TID. etransitivity; eauto.
        eapply memory_remove_le; eauto. }
      red; ins. rewrite IdentMap.gso in TID; auto.
      eapply PROM_IN_MEM; eauto. }
    { eapply f_to_coherent_more; [..| apply FCOH]; eauto.
      clear. by simplify_tls_events. }
    { ins. etransitivity; [by apply SC_COV|].
      clear. simplify_tls_events. basic_solver. }
    { intros NFSC l.
      eapply max_value_same_set.
      { by apply SC_REQ. } 
      apply s_tm_n_f_steps.
      { by apply init_covered. }
      { clear. simplify_tls_events. basic_solver. }
      intros a [[H|H]|H]%COV' HH AA.
      all: type_solver. }
    { eapply SimulationRelProperties.reserved_time_same_issued_reserved.
      { apply RESERVED_TIME. }
      all: clear; by simplify_tls_events. }
    rewrite IdentMap.gss.
    eexists; eexists; eexists; splits; eauto; simpls.
    { erewrite tau_steps_step_same_instrs; eauto. }
    { ins. rewrite IdentMap.gso in TID'; auto.
      edestruct (PROM_DISJOINT thread') as [H|]; eauto.
      left. erewrite Memory.remove_o; eauto. desf. }
    { red. ins.
      erewrite Memory.remove_o in PROM; eauto.
      destruct (loc_ts_eq_dec (l, to) (locr, f_to w)) as [[AA BB]|NEQ].
      { simpls. rewrite AA in *. rewrite BB in *.
        rewrite (loc_ts_eq_dec_eq locr (f_to w)) in PROM. desf. }
      rewrite (loc_ts_eq_dec_neq NEQ) in PROM.
      edestruct SIM_PROM as [w'']; eauto.
      desc.
      exists w''; splits; desc; auto.
      assert (W w'') as WW.
      { eapply issuedW; eauto. }
      { clear -ISS0. find_event_set. }
      intros [[H | -> ]|H]%COV'; [by desf |  | by desf].
      eapply issuedW in ISS0; eauto. type_solver. }
    { red; ins. move SIM_RPROM at bottom. red in SIM_RPROM.
      specialize (SIM_RPROM l to from). specialize_full SIM_RPROM.
      { erewrite Memory.remove_o in RES; eauto. desf. }
      desc. exists b. splits; eauto.
      { clear -RES0. find_event_set. }
      clear -NOISS; separate_set_event. }
    { red; splits; simpls.

      (* edestruct SIM_MEM as [rel'']; eauto. *)
      (* simpls; desc. *)
      simplify_tls_events' in ISSB.
      red in SIM_MEM. 
      edestruct (SIM_MEM l b) as [rel'']; eauto.
      simpls; desc. 
      
      exists rel''; splits; auto.
      
      intros TIDBF COVBF.
      assert (~ covered T b) as COVB.
      { intros B. apply COVBF. clear -B. find_event_set. }
      assert (b <> w) as NEQBW.
      { intros ->. apply COVBF. clear. find_event_set. }
      destruct H1 as [PROM REL']; auto; unnw; splits; auto.
      { erewrite Memory.remove_o; eauto.
        destruct (loc_ts_eq_dec (l, f_to b) (locr, f_to w)) as [EQ|NEQ].
        2: by rewrite loc_ts_eq_dec_neq.
        exfalso. simpls. destruct EQ as [EQ1 EQ2]. rewrite EQ1 in *. clear l EQ1.
        eapply f_to_eq with (I:=reserved T) in EQ2; eauto.
        { red. by rewrite LOC. }
        eapply rcoh_I_in_S; eauto. }
      desc. exists p_rel.
      split; auto.
      destruct (Ordering.le Ordering.acqrel (Event_imm_promise.wmod ordw)); [by desf|].
      unfold LocFun.add.
      destruct (Loc.eq_dec l locr) as [EQ|]; [|done].
      assert (View.join
                (View.join (TView.rel (Local.tview local) locr)
                           (View.singleton_ur locr (f_to w)))
                (View.unwrap p_rel) =
              View.join
                (View.join (TView.rel (Local.tview local) locr)
                           (View.unwrap p_rel))
                (View.singleton_ur locr (f_to w))) as HH.
      { rewrite View.join_assoc.
        rewrite View.join_comm with (lhs:=View.singleton_ur locr (f_to w)).
          by rewrite View.join_assoc. }
      rewrite HH. rewrite View.join_assoc.
      assert (View.join (View.singleton_ur locr (f_to w)) (View.singleton_ur l (f_to b)) =
              View.singleton_ur l (f_to b)) as YY.
      2: { rewrite YY. by rewrite EQ in *. }
      rewrite EQ in *. apply View.le_join_r.
      apply View.singleton_ur_spec.
      { apply View.singleton_ur_wf. }
      unfold View.singleton_ur, TimeMap.singleton, LocFun.init; simpls.
      unfold LocFun.add. rewrite Loc.eq_dec_eq.
      apply Time.le_lteq. left. eapply f_to_co_mon; eauto.
      assert (E b /\ W b) as [EB WB].
      { split; [eapply issuedE | eapply issuedW]; eauto. }
      2: { eapply rcoh_I_in_S; eauto. }
      2: { destruct REL'0 as [REL'0 | REL'0]; [left | right]; desc; splits; auto.
           { intros CIb. apply REL'0.
             eapply set_equiv_exp; [| apply CIb].
             clear. by simplify_tls_events. }
           eexists. splits; eauto.
           clear -REL'0. find_event_set. }             
      edestruct (wf_co_total WF) with (a:=w) (b:=b) as [CO|CO]; eauto.
      1,2: split; [split|]; eauto.
      exfalso.
      assert (sb w b) as SBWB.
      { edestruct same_thread with (x:=w) (y:=b) as [[SB|SB]|SB]; eauto.
        { by rewrite TIDWR. }
        { clear -SB NEQBW. desf. }
        exfalso. apply COVB.
        apply NEXT. eexists. apply seq_eqv_r. split; [|done].
        edestruct same_thread with (x:=r) (y:=b) as [[SB'|SB']|SB']; eauto.
        { subst. clear -WB RREAD. type_solver. }
        exfalso. eapply wf_rmwi; eauto. }
      cdes CON. eapply Cint. exists b. split.
      { apply sb_in_hb; eauto. }
      apply r_step. by apply co_in_eco. }
    { red. ins.
      simplify_tls_events' in RESB.
      assert (~ issued T b) as NISSB'.
      { intros NI. apply NISSB. clear -NI. find_event_set. }
      splits.
      { by apply SIM_RES_MEM. }
      ins. erewrite Memory.remove_o; eauto. desf.
      2: by apply SIM_RES_MEM.
      simpls. desf.
      exfalso.
      assert (b = (ThreadEvent (tid r) (Datatypes.S (eindex state)))); desf.
      eapply f_to_eq with (I:=reserved T); eauto.
      red. by rewrite LOC. }
    { assert (doma (sb ⨾ ⦗eq r⦘) (covered T)) as SBCOV.
      { red. ins. apply NEXT. eexists; eauto. }
      rewrite COV'. 
      eapply sim_tview_write_step; eauto.
      { by apply CON. }
      { rewrite coveredE; eauto. basic_solver. }
      { assert (covered T ∪₁ eq r ≡₁ covered (T ∪₁ eq (mkTL ta_cover r))) as ->.
        { clear. by simplify_tls_events. }
        apply doma_alt. eapply dom_sb_covered; eauto.
        all: by apply TS1. }
      1: rewrite <- FF; eapply sim_tview_read_step; eauto.
      { by apply CON. }
      { ins. destruct H as [COVY TIDY].
          by apply SBYR_gen. }
      { intros [COVW|]; [by desf|]. 
        clear WREPR.
        type_solver. }
      { intros y [[COVY|HH] TIDYW].
        { rewrite TIDWR in TIDYW.
          eapply sb_trans.
          2: by apply (rmw_in_sb WF); eauto.
          apply SBYR_gen; auto. }
        rewrite <- HH in *.
          by apply (rmw_in_sb WF). }
      red. ins. apply seq_eqv_r in REL0. destruct REL0 as [REL0 HH].
      rewrite <- HH in *. clear y HH.
      destruct (classic (x = r)) as [|NEQ].
      { by right. }
      edestruct sb_semi_total_r with (x:=w) (y:=x) (z:=r) as [AA|AA]; eauto.
      { left. apply NEXT. eexists. apply seq_eqv_r. eauto. }
      exfalso. eapply (wf_rmwi WF); eauto. }
    { cdes PLN_RLX_EQ. 
      unfold TView.write_tview, TView.read_tview; simpls.
      unfold View.singleton_ur_if.
      rewrite RLX_ORDR.
      destruct (Ordering.le Ordering.acqrel (Event_imm_promise.wmod ordw)); simpls.
      red; splits; simpls.
      all: desf; simpls.
      all: try rewrite REL_PLN_RLX0.
      all: try rewrite EQ_CUR.
      all: try rewrite EQ_ACQ.
      1-3: reflexivity.
      all: intros l; unfold LocFun.add.
      all: destruct (Loc.eq_dec l locr) as [|NEQ]; subst.
      2: by apply EQ_REL.
      unfold View.join; simpls. by rewrite EQ_REL. }
    { unfold TView.write_tview, TView.read_tview; simpls.
      red; splits; simpls.
      all: desf; ins.
      all: repeat (apply Memory.join_closed_timemap).
      all: try apply MEM_CLOSE.
      all: auto.
      all: try by apply Memory.closed_timemap_bot.
      all: try rewrite <- FF.
      all: try by eapply Memory.singleton_closed_timemap; eauto.
      unfold LocFun.add.
      destruct (Loc.eq_dec loc locr) as [LL|NLL].
      unfold View.join; simpls.
      apply Memory.join_closed_timemap.
      1,3: by apply MEM_CLOSE.
      eapply Memory.singleton_closed_timemap; eauto. }
    red. splits; eauto.
    ins. rewrite (INDEX_RMW w RMW); auto.
    etransitivity; [apply set_equiv_exp; clear; by simplify_tls_events| ]. 
    apply sim_state_cover_rmw_events; auto. }
  intros [PCSTEP SIMREL_THREAD']; split; auto.
  intros SMODE SIMREL.
  eapply full_simrel_step.
  17: by apply SIMREL.
  15: { ins. rewrite IdentMap.Facts.add_in_iff.
        split; auto. intros [|]; auto; subst.
        apply IdentMap.Facts.in_find_iff.
          by rewrite LLH. }
  14: by eapply msg_preserved_refl; eauto.
  11: by eapply same_other_threads_step; eauto.
  all: simpls; eauto.
  9: { subst. by apply SIMREL_THREAD'. }   
  all: clear -WF RACT WACT TLSCOH TIDWR; simplify_tls_events; try basic_solver.
  { rewrite coveredE; eauto. basic_solver. }
  eapply issuedE; eauto.
Qed.

End RMWRlxCovPlainStep.
