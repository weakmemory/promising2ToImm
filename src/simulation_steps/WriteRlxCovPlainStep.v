Require Import PArith Arith.
From hahn Require Import Hahn.
Require Import PromisingLib.
From Promising2 Require Import Configuration TView View Time Event Cell Thread Memory Local.
From imm Require Import Events.
From imm Require Import Execution.
From imm Require Import Execution_eco.
From imm Require Import imm_s_hb.
From imm Require Import imm_s.
From imm Require Import imm_common.
From imm Require Import CombRelations.
From imm Require Import CombRelationsMore.
From imm Require Import ProgToExecution.

Require Import TraversalConfig.
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
Require Import AuxRel2.

Set Implicit Arguments.

Section WriteRlxCovPlainStep.

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

Lemma rlx_write_cover_step PC T S f_to f_from thread w smode
      (SIMREL_THREAD : simrel_thread G sc PC T S f_to f_from thread smode)
      (TID : tid w = thread)
      (TSTEP : ext_itrav_step
                 G sc w (mkETC T S) (mkETC (mkTC (covered T ∪₁ eq w) (issued T)) S))
      (TYPE : W w)
      (NREL : ~ Rel w)
      (NRMW : ~ codom_rel rmw w):
  let T' := (mkTC (covered T ∪₁ eq w) (issued T)) in
  exists PC',
    ⟪ PCSTEP : plain_step MachineEvent.silent thread PC PC' ⟫ /\
    ⟪ SIMREL_THREAD : simrel_thread G sc PC' T' S f_to f_from thread smode ⟫ /\
    ⟪ SIMREL :
        smode = sim_normal -> simrel G sc PC T S f_to f_from ->
        simrel G sc PC' T' S f_to f_from ⟫.
Proof using WF CON.
  cdes SIMREL_THREAD. cdes COMMON. cdes LOCAL.
  
  assert (COV : coverable G sc T w).
  { eapply ext_itrav_step_cov_coverable with (T:=mkETC T S); eauto. }
  assert (NEXT : next G (covered T) w).
  { eapply ext_itrav_step_cov_next with (T:=mkETC T S); eauto. }

  assert (tc_coherent G sc T) as sTCCOH by apply TCCOH.

  assert (sc_per_loc G) as SC_PER_LOC.
  { by apply coherence_sc_per_loc; cdes CON. }

  assert (~ covered T w) as WNCOV.
  { apply NEXT. }

  cdes STATE. rewrite <- TID in *.
  edestruct sim_state_to_events as [ev HH]; eauto.
  desc.

  apply clos_rt_rt1n in ESTEPS.
  eapply (rtc_lang_tau_step_rtc_thread_tau_step
            _ _ _ local PC.(Configuration.sc) PC.(Configuration.memory)) in ESTEPS.

  assert (E w) as WACT.
  { apply NEXT. }

  assert (exists ex ordw locw valw, lab w = Astore ex ordw locw valw) as PARAMS; desf.
  { unfold is_w in TYPE.
    destruct (lab w); desf; eexists; eauto. }
  assert (loc lab w = Some locw) as WLOC.
  { by unfold loc; rewrite PARAMS. }

  assert (~ is_init w) as NINIT.
  { intros IIN. apply WNCOV. apply TCCOH. by split. }
  assert (issued T w) as WISS.
  { cdes COV; desf; type_solver. }
  assert (S w) as WS.
  { by apply TCCOH.(etc_I_in_S). }
  assert (val lab w = Some valw) as WPVAL.
  { by unfold val; rewrite PARAMS. }

  cdes SIM_MEM.
  edestruct SIM_MEM0 as [rel DOM']; eauto.
  desc.

  assert (~ dom_rel rmw w) as NNRMW.
  { intros [x RMW]. apply (dom_l WF.(wf_rmwD)) in RMW.
    apply seq_eqv_l in RMW. type_solver. }

  assert (Event_imm_promise.same_g_events lab (w :: nil) ev) as SAME.
  { by apply SAME_NRMW. }
  
  assert (ev = ProgramEvent.write locw valw (Event_imm_promise.wmod ordw)) as EV.
  { red in SAME; red in SAME; simpls.
    rewrite PARAMS in *; simpls.
    destruct ev; desf; vauto. }

  set (pe := ThreadEvent.write locw (f_from w) (f_to w)
                               valw rel (Event_imm_promise.wmod ordw)).
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

  assert (~ Ordering.le Ordering.strong_relaxed (Event_imm_promise.wmod ordw)) as NSRLX_PROM_W.
  { unfold Event_imm_promise.wmod, is_rel, is_rlx, mode_le, Events.mod in *.
    rewrite PARAMS in *.
    destruct ordw; simpls. }
  assert (~ Ordering.le Ordering.acqrel (Event_imm_promise.wmod ordw)) as NREL_PROM_W.
  { unfold Event_imm_promise.wmod, is_rel, is_rlx, mode_le, Events.mod in *.
    rewrite PARAMS in *.
    destruct ordw; simpls. }
  
  destruct DOM'1 as [INPROM REL_REP]; auto.

  assert (Time.lt (f_from w) (f_to w)) as LT_F_T.
  { by apply FCOH. }

  assert (View.opt_wf rel) as WFREL.
  { apply opt_wf_unwrap. constructor.
    rewrite REL_PLN_RLX. reflexivity. }

  (* TODO: check!!! *)
  assert (Time.le (View.rlx (View.unwrap rel) locw) (f_to w)) as WVREL.
  { subst. simpls.
    destruct REL_REP as [p_rel]; desc.
    rewrite REL in *.
    unfold View.join; simpls.
    unfold TimeMap.join, TimeMap.singleton, LocFun.add.
    rewrite Loc.eq_dec_eq.
    apply Time.join_spec.
    2: reflexivity.
    apply Time.join_spec.
    2: { destruct H0 as [H0|H0]; desc; subst; simpls.
         { unfold TimeMap.bot. apply Time.bot_spec. }
         exfalso. apply NRMW.
         destruct INRMW; desc. by eexists; eauto. }

    clear REL.
    cdes SIM_TVIEW.
    specialize (REL locw locw).
    rewrite Loc.eq_dec_eq in REL.
    unfold LocFun.find in REL.
    cdes REL.
    destruct MAX as [[_ MAX]|[a_max MAX]].
    { rewrite MAX. apply Time.bot_spec. }
    desc.
    destruct (classic (a_max = w)) as [AWEQ|AWNEQ].
    { desf. }

    assert (issued T a_max) as ISSA.
    { destruct INam as [IN|IN].
      { apply t_rel_covered in IN; auto. }
      destruct IN as [[[WA LOCA] TIDA] COVA].
      eapply w_covered_issued; eauto.
        by split. }
    assert (S a_max) as SA.
    { by apply TCCOH.(etc_I_in_S). }
    assert ((E ∩₁ W ∩₁ (fun x => loc lab a_max = Some locw)) a_max) as BB.
    { destruct INam as [IN|IN].
      { apply set_interA; split.
        { by apply TCCOH. }
        eapply t_rel_urr_doma; eauto. }
      destruct IN as [[[WA LOCA] TIDA] COVA].
      split; [split|]; auto.
      apply TCCOH in COVA. apply COVA. }
    edestruct (@wf_co_total G WF (Some locw) a_max) as [AWCO|AWCO]; eauto.
      by split; [|done]; split.
      { etransitivity; eauto.
        apply Time.le_lteq; left.
        eapply f_to_co_mon; eauto. }
      exfalso.
      assert (exists y, urr G sc locw a_max y /\ sb y w) as [y [URR SBY]].
      { destruct INam as [INam|INam].
        { destruct INam as [y IN].
          exists y.
          red in IN.
          repeat (hahn_rewrite <- seqA in IN).
          apply seq_eqv_r in IN; destruct IN as [IN COVY].
          apply seq_eqv_r in IN; destruct IN as [IN TID].
          repeat (apply seq_eqv_r in IN; destruct IN as [IN _]).
          split; auto.
          assert (E y) as EY.
          { eapply coveredE in COVY; eauto. }
          destruct TID.
          { destruct (same_thread G w y); auto. }
          apply init_ninit_sb; auto. }
        exists a_max.
        destruct INam as [[[WA LOCA] TIDA] COVA].
        split. 
        { apply urr_refl; basic_solver. }
        destruct (same_thread G w a_max); auto.
        apply BB. }
      eapply sb_transp_rf_co_urr_irr; eauto.
      1-3: by apply CON.
      eexists; split; eauto.
      eexists; split.
        by left.
        eexists; split; eauto. }

  edestruct (Memory.remove_exists (Local.promises local)  locw)
    as [new_prom NPCH].
  { edestruct (SIM_MEM locw w) as [rel' HH]; eauto. }
  
  destruct REL_REP as [p_rel]; desf.
  2: { exfalso. apply NRMW. destruct INRMW as [z H].
       eexists. apply H; done. }

  cdes CON.
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
      unfold pe; eapply Local.step_write.
      econstructor; eauto.
      { unfold TView.write_released.
        rewrite NRLX_PROM_W; simpls.
        rewrite View.join_bot_l.
        destruct (Ordering.le Ordering.acqrel (Event_imm_promise.wmod ordw)) eqn: HH.
        { subst; desf. }
        simpls; rewrite view_join_bot_r in *.
          by unfold LocFun.add; rewrite Loc.eq_dec_eq. }
      { constructor.
        edestruct (max_event_cur) as [a_max]; eauto; desc.
        assert (E a_max) as EA.
        { apply (wf_urrE WF) in CCUR; auto.
          revert CCUR; unfold seq; unfolder; ins; desf. }
        assert (issued T a_max) as AISS.
        { assert (A: (urr G sc locw ⨾ ⦗coverable G sc T⦘) a_max w).
          { basic_solver. }
          apply (urr_coverable) in A; try done.
          revert A; unfold seq; unfolder; ins; desf. }
        assert (S a_max) as SA.
        { by apply TCCOH.(etc_I_in_S). }
        edestruct (@wf_co_total G WF (Some locw) a_max) as [AWCO|AWCO].
        3: apply NEQ.
        2: basic_solver.
        1: apply set_interA; split; auto.
        hahn_rewrite (@wf_urrD G sc locw) in CCUR.
        revert CCUR; clear; basic_solver 12.
        { eapply TimeFacts.le_lt_lt; eauto; cdes FCOH.
          assert (DenseOrder.le (f_to a_max) (f_from w)) as LE.
          { apply TCO; auto. }
          eapply TimeFacts.le_lt_lt; eauto. }
        exfalso.
        eapply transp_rf_co_urr_irr; eauto.
        exists w; split.
        { by left. }
        eexists; eauto. }
      { econstructor.
        2: by apply NPCH.
        apply Memory.promise_lower; eauto.
        all: apply Memory.lower_exists_same; auto.
        all: by constructor. }
      { intros. exfalso.
        unfold Event_imm_promise.wmod, is_rel, mode_le, Events.mod in *.
        rewrite PARAMS in *.
        destruct ordw; simpls. }
      done. }
    unnw.
    red; splits; red; splits; simpls.
    { apply TSTEP. }
    { etransitivity; eauto. basic_solver. }
    { intros. apply WF.(wf_rmwD) in RMW.
      apply seq_eqv_l in RMW; destruct RMW as [RR RMW].
      apply seq_eqv_r in RMW; destruct RMW as [RMW WW].
      split; intros [HH|HH]; left; auto.
      { erewrite <- RMWCOV; eauto. }
      { type_solver. }
      { erewrite RMWCOV; eauto. }
      subst. exfalso. apply NRMW. eexists; eauto. }
    { intros e' EE. 
      destruct (Ident.eq_dec (tid e') (tid w)) as [EQ|NEQ].
      { rewrite EQ. eexists.
        rewrite IdentMap.gss; eauto. }
      rewrite IdentMap.gso; auto. }
    { ins.
      destruct (Ident.eq_dec thread' (tid w)) as [EQ|NEQ].
      { subst. rewrite IdentMap.gss in TID.
        etransitivity.
        2: by eapply PROM_IN_MEM; eauto.
        inv TID; simpls. clear TID.
        red; ins.
        erewrite Memory.remove_o in LHS; eauto.
        destruct (loc_ts_eq_dec (loc, to) (locw, f_to w)) as [|NEQ]; [by desf|].
          by erewrite loc_ts_eq_dec_neq in LHS. }
      red; ins. rewrite IdentMap.gso in TID; auto.
      eapply PROM_IN_MEM; eauto. }
    { ins. etransitivity; [apply SC_COV|]; auto.
      basic_solver. }
    { intros NFSC l.
      eapply max_value_same_set.
      { by apply SC_REQ. }
      rewrite s_tm_union.
      unfold CombRelations.S_tm.
      split; unionL; try basic_solver 3.
      rewrite (wf_S_tmrD); type_solver 21. }
    rewrite IdentMap.gss.
 
    eexists; eexists; eexists; splits; eauto; simpls.
    { ins. rewrite IdentMap.gso in TID'; auto.
      edestruct (PROM_DISJOINT thread') as [H|]; eauto.
      left. erewrite Memory.remove_o; eauto. desf. }
    { red; splits; simpls.
      erewrite Memory.remove_o in PROM; eauto. 
      destruct (loc_ts_eq_dec (l, to) (locw, f_to w)) as [[EQ1 EQ2]|NEQ]; simpls; subst.
      { rewrite (loc_ts_eq_dec_eq locw (f_to w)) in PROM.
        inv PROM. }
      rewrite (loc_ts_eq_dec_neq NEQ) in PROM.
      edestruct SIM_PROM as [b H]; eauto; desc.
      exists b; splits; auto.
      intros [H|H]; [done|subst].
      unfold loc in *; rewrite PARAMS in *; desf. }
    { red; ins. apply SIM_RPROM.
      erewrite Memory.remove_o in RES; eauto. desf. }
    { red; ins.
      destruct (Ordering.le Ordering.acqrel (Event_imm_promise.wmod ordw)); vauto.
      destruct (classic (b = w)) as [|NEQ].
      { subst.
        unfold loc in LOC; unfold val in VAL; rewrite PARAMS in *; inv LOC.
        eexists; splits; eauto.
        intros _ H.
          by exfalso; apply H; right. }
      edestruct SIM_MEM as [rel]; eauto.
      simpls; desc.
      exists rel; splits; auto.
      intros TT COVWB.
      destruct H1 as [PROM REL]; auto; unnw.
      { by intros H; apply COVWB; left. }
      erewrite Memory.remove_o; eauto.

      (* TODO: generalize! *)
      assert (l = locw -> Time.lt (f_to w) (f_to b)) as FGT.
      { ins; subst. eapply f_to_co_mon; eauto.
        assert (co w b \/ co b w) as H; [|destruct H as [|H]; [done|exfalso]].
        { assert (W b) as WB.
          { by apply TCCOH. }
          edestruct (@wf_co_total G WF (Some locw)).
          3: by eauto.
          1,2: by red; split; [red; split|]; auto.
            by right.
              by left. }
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
          by apply TCCOH.(etc_I_in_S). }

      destruct (loc_ts_eq_dec (l, f_to b) (locw, f_to w)) as [[A B]|LNEQ].
      { exfalso. simpls; subst; rewrite B in *.
          by apply DenseOrder.lt_strorder in FGT. }
      simpls. rewrite (loc_ts_eq_dec_neq LNEQ).
      splits; auto.
      unfold LocFun.add.
      destruct (classic (l = locw)) as [LL|LL].
      2: by rewrite Loc.eq_dec_neq.
      subst; rewrite Loc.eq_dec_eq.
      destruct REL as [p_rel [REL HH]]; exists p_rel; splits.
      2: by apply HH.
      rewrite View.join_assoc.
      rewrite (View.join_comm (View.unwrap p_rel)).
      rewrite <- View.join_assoc.
      rewrite (View.join_comm _ (View.singleton_ur locw (f_to b))).
      rewrite (View.join_comm _ (View.singleton_ur locw (f_to w))).
      rewrite <- View.join_assoc.
      rewrite (@View.le_join_l (View.singleton_ur locw (f_to b))); auto.
      { rewrite View.join_assoc. by rewrite View.join_comm. }
      unfold View.singleton_ur, TimeMap.singleton, LocFun.add, LocFun.find, LocFun.init.
      constructor; simpls; intros l.
      all: destruct (Loc.eq_dec l locw).
      2,4: by apply Time.bot_spec.
      all: by apply Time.le_lteq; left; apply FGT. }
    { red. ins. splits.
      { by apply SIM_RES_MEM. }
      ins. erewrite Memory.remove_o; eauto. desf.
      2: by apply SIM_RES_MEM.
      simpls. desf.
      exfalso.
      assert (b = w); desf.
      eapply f_to_eq with (I:=S); eauto.
      { generalize TCCOH.(etc_S_in_E), (reservedW WF TCCOH). basic_solver. }
      red. by rewrite LOC. }
    { eapply sim_tview_write_step; eauto.
      { etransitivity; [by apply TCCOH|].
        intros x H; apply H. }
      { intros x y H. apply seq_eqv_r in H; destruct H as [H1 H2].
        apply TCCOH in H2. apply H2. eexists; apply seq_eqv_r; eauto. }
      intros x y H. apply seq_eqv_r in H; destruct H as [H]; subst.
      apply COV. eexists; apply seq_eqv_r; eauto. }
    { cdes PLN_RLX_EQ. 
      unfold TView.write_tview.
      red; splits; simpls.
      all: desf; simpls.
      all: try rewrite EQ_CUR.
      all: try rewrite EQ_ACQ.
      1-2: reflexivity.
      all: unfold LocFun.add, LocFun.find, View.join; intros l.
      all: desf; simpls.
      all: rewrite EQ_REL; reflexivity. }
    { unfold TView.write_tview; simpls.
      red; splits; simpls.
      all: desf; ins.
      all: repeat (apply Memory.join_closed_timemap).
      all: try apply MEM_CLOSE.
      all: try by eapply Memory.singleton_closed_timemap; eauto.
      all: unfold LocFun.add, LocFun.find; desf.
      all: try by apply MEM_CLOSE.
      all: apply Memory.join_closed_timemap.
      all: try apply MEM_CLOSE.
      all: by eapply Memory.singleton_closed_timemap; eauto. }
    red. splits; eauto.
    ins. rewrite INDEX_NRMW; auto.
    apply sim_state_cover_event; auto. }
  intros [PCSTEP SIMREL_THREAD']; split; auto.
  intros SMODE SIMREL.
  eapply full_simrel_step.
  15: by apply SIMREL.
  13: { ins. rewrite IdentMap.Facts.add_in_iff.
        split; auto. intros [|]; auto; subst.
        apply IdentMap.Facts.in_find_iff.
          by rewrite LLH. }
  all: simpls; eauto.
  7: by apply msg_preserved_refl.
  rewrite coveredE; eauto.
  2: by eapply issuedE; eauto.
  all: basic_solver.
Qed.

End WriteRlxCovPlainStep.
