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
Require Import ExistsIssueReservedInterval.
Require Import IssueReservedStepHelper.
Require Import MemoryClosedness.
Require Import SimulationRelProperties.
Require Import ReadPlainStepHelper.

Set Implicit Arguments.

Section IssueReservedRelPlainStep.

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

Lemma issue_rel_reserved_step_no_next PC T (S : actid -> Prop) f_to f_from thread r w smode
      (TID : tid r = thread)
      (REL : Rel w) (RMW : rmw r w)
      (SW : S w)
      (NONEXT : dom_sb_S_rfrmw G (mkETC T S) rfi (eq w) ⊆₁ ∅)

      (TSTEP1 : ext_itrav_step
                 G sc r (mkETC T S)
                 (mkETC (mkTC (covered T ∪₁ eq r) (issued T)) S))
      (TSTEP2 : ext_itrav_step
                  G sc w (mkETC (mkTC (covered T ∪₁ eq r) (issued T)) S)
                  (mkETC
                     (mkTC (covered T ∪₁ eq r) (issued T ∪₁ eq w))
                     (S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G (mkETC T S) rfi (eq w))))

      (TSTEP3 : ext_itrav_step
                  G sc w
                  (mkETC
                     (mkTC (covered T ∪₁ eq r) (issued T ∪₁ eq w))
                     (S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G (mkETC T S) rfi (eq w)))
                  (mkETC
                     (mkTC (covered T ∪₁ eq r ∪₁ eq w) (issued T ∪₁ eq w))
                     (S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G (mkETC T S) rfi (eq w))))

      (SIMREL_THREAD : simrel_thread G sc PC T S f_to f_from thread smode) :

  let T' := mkTC (covered T ∪₁ eq r ∪₁ eq w) (issued T ∪₁ eq w) in
  let S' := S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G (mkETC T S) rfi (eq w) in
  exists PC',
    ⟪ PCSTEP : (plain_step MachineEvent.silent thread)^+ PC PC' ⟫ /\
    ⟪ SIMREL_THREAD : simrel_thread G sc PC' T' S' f_to f_from thread smode ⟫ /\
    ⟪ SIMREL :
        smode = sim_normal -> simrel G sc PC T S f_to f_from ->
        simrel G sc PC' T' S' f_to f_from ⟫.
Proof using WF CON.
  cdes SIMREL_THREAD. cdes COMMON. cdes LOCAL.

  assert (NEXT : next G (covered T) r).
  { eapply ext_itrav_step_cov_next with (T:=mkETC T S); eauto. }
  assert (COV : coverable G sc T r).
  { admit. }
 
  assert (WTID : thread = tid w).
  { rewrite <- TID. by apply WF.(wf_rmwt). }
  assert (ISS : ~ issued T w).
  { admit. }

  assert (S ⊆₁ E ∩₁ W) as SEW.
  { generalize TCCOH.(etc_S_in_E). generalize (reservedW WF TCCOH). clear. basic_solver. }
  
  assert (sc_per_loc G) as SC_PER_LOC.
  { by apply coherence_sc_per_loc; cdes CON. }
  assert (tc_coherent G sc T) as TCCOHs.
  { apply TCCOH. }

  assert (~ covered T r) as RNCOV.
  { apply NEXT. }

  cdes STATE. rewrite <- TID in *.
  edestruct sim_state_to_events as [ev HH]; eauto.
  desc.

  apply clos_rt_rt1n in ESTEPS.
  eapply (rtc_lang_tau_step_rtc_thread_tau_step
            _ _ _ local PC.(Configuration.sc) PC.(Configuration.memory)) in ESTEPS.

  assert (E r /\ E w) as [RACT WACT].
  { apply (wf_rmwE WF) in RMW.
    apply seq_eqv_l in RMW; destruct RMW as [WW RMW].
    apply seq_eqv_r in RMW; desf. }

  assert (R r /\ W w) as [RREAD WWRITE].
  { apply (wf_rmwD WF) in RMW.
    hahn_rewrite (R_ex_in_R) in RMW.
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
  { red in COV. destruct COV as [_ [[COV|COV]|COV]].
    1,3: type_solver.
    eapply COV.
    eexists. apply seq_eqv_r. eauto. }

  assert (S w') as SW'.
  { by apply TCCOH.(etc_I_in_S). }

  assert (~ is_init r) as RNINIT.
  { intros H; apply (init_w WF) in H.
    type_solver. }
  assert (sb r w) as WRSB.
  { apply wf_rmwi in RMW; red in RMW; desf. }

  assert (~ covered T w) as WNCOV.
  { intros H; apply NEXT.
    apply TCCOH in H. apply H.
    exists w. by apply seq_eqv_r; split. }
  assert (~ is_init w) as WNINIT.
  { intros H. apply WNCOV. by apply TCCOH. }

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

  edestruct SIM_MEM as [rel' DOM'].
  { apply WISS. }
  all: eauto.
  simpls. desc.
  clear DOM'1.

  assert ((rf ⨾ rmw) w' w) as RFRMW.
  { exists r; split; auto. }
  
  (* destruct DOM1 as [WMEM [p_rel]]; eauto. desc. *)
  (* destruct H0; desc. *)
  (* { exfalso. apply NINRMW. exists w'. apply seq_eqv_l; split; auto. } *)
  (* assert (p = w'); subst. *)
  (* { eapply wf_rfrmwf; eauto. } *)
  (* rewrite INMEM0 in P_INMEM. inv P_INMEM. clear P_INMEM. *)
  (* rename p_v into valr. rename p_rel into rel'. *)
 
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

  edestruct (@read_step_helper G WF sc CON) as [TCCOH' HH]; eauto.
  desc. rewrite <- TIDWR in *.

  assert (tc_coherent G sc (mkTC (covered T ∪₁ eq r) (issued T)))
    as TCCOH1.
  { apply TSTEP1. }

  assert (issuable G sc (mkTC (covered T ∪₁ eq r) (issued T)) w) as WNNISS.
  { eapply issuable_next_w; eauto.
    split; simpls.
    red; split; [split|]; auto.
    { red. intros x [y SBB]. apply seq_eqv_r in SBB. desc. rewrite <- SBB0 in *.
      clear y SBB0.
      destruct (classic (x = r)) as [EQ|NEQ].
      { by right. }
      left.
      edestruct sb_semi_total_r with (x:=w) (y:=x) (z:=r); eauto.
      { apply NEXT. eexists. apply seq_eqv_r. eauto. }
      exfalso. eapply WF.(wf_rmwi); eauto. }
    clear WREPR REPR.
    red; intros [H|H]; [by desf|].
    type_solver. }

  edestruct (fun w1 w2 x z k w3 w4 w5 =>
               @issue_reserved_step_helper_no_next
               G WF sc CON (mkTC (covered T ∪₁ eq r) (issued T)) S
               w1 w2 f_to f_from FCOH
               (Configuration.mk x PC.(Configuration.sc) PC.(Configuration.memory))
               w3 smode w4 w5 (Local.mk z k)
            ) with (w:=w) (valw:=valw) (ordw:=Events.mod lab w)
    as [p_rel H].
  all: simpls.
  2: by apply SIM_PROM0.
  5: by apply PLN_RLX_EQ0.
  all: eauto.
  { ins. rewrite IdentMap.gso in *; eauto. }
  { rewrite IdentMap.gss. eauto. }
  desc. red in H. desc.
  destruct H0 as [H|H]; desc.
  { exfalso. apply NINRMW. exists w'. apply seq_eqv_l. split; eauto. }
  assert (p = w') as PW.
  { eapply wf_rfrmwf; eauto. }
  rewrite PW in *; clear PW.
  simpls.
  assert (p_rel = rel') as PW.
  { rewrite INMEM in P_INMEM. clear -P_INMEM. inv P_INMEM. }
  rewrite PW in *; clear PW.
  (* destruct H1 as [H1|H1]; red in H1; desc. *)
  (* 2: done. *)
  destruct (is_rel lab w) eqn:RELVV; simpls.

  set (pe := ThreadEvent.update
               locr (f_from w) (f_to w) valr valw
               rel' (Some
                       (View.join
                          (View.join
                             (View.join
                                (View.join (TView.cur (Local.tview local))
                                           (View.singleton_ur_if
                                              (Ordering.le
                                                 Ordering.relaxed
                                                 (Event_imm_promise.rmod (Events.mod lab r))) locr
                                              (f_to w')))
                                (if
                                    Ordering.le Ordering.acqrel
                                                (Event_imm_promise.rmod (Events.mod lab r))
                                  then View.unwrap rel'
                                  else View.bot)) (View.unwrap rel'))
                          (View.singleton_ur locr (f_to w))))
               (Event_imm_promise.rmod ordr) (Event_imm_promise.wmod ordw)).

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
  assert (Ordering.le Ordering.acqrel (Event_imm_promise.wmod ordw)) as REL_ORDW.
  { unfold is_rel, mode_le, Events.mod in *; simpls.
    rewrite WPARAMS in *.
    destruct ordw; simpls. }
  assert (Ordering.le Ordering.strong_relaxed (Event_imm_promise.wmod ordw)) as SRLX_ORDW.
  { unfold is_rel, mode_le, Events.mod in *; simpls.
    rewrite WPARAMS in *.
    destruct ordw; simpls. }

  assert (f_to w' = f_from w) as FF.
  { apply FCOH0; auto.
    { by do 2 left. }
    clear. basic_solver. }

  assert (forall l to from msg 
                 (NEQ : l <> locr \/ to <> f_to w),
             Memory.get l to memory_add = Some (from, msg) <->
             Memory.get l to PC.(Configuration.memory) = Some (from, msg))
    as NOTNEWM.
  { ins. erewrite Memory.add_o; eauto.
    rewrite loc_ts_eq_dec_neq; auto.
    erewrite Memory.remove_o; eauto.
    rewrite loc_ts_eq_dec_neq; auto. }

  eexists (Configuration.mk _ _ memory_add).
  apply and_assoc. apply pair_app.
  { split.
    { set (pe' := MachineEvent.silent).
      assert (pe' = ThreadEvent.get_machine_event pe) as H.
      { unfold pe. simpls. }
      rewrite H. clear H.
      econstructor; eauto.
      econstructor; eauto.
      2: by unfold pe; clear; desf.
      apply Thread.step_program.
      constructor.
      { assert (ev = ThreadEvent.get_program_event pe) as EV' by done.
        rewrite EV' in STEP; eauto. }
      unfold pe; eapply Local.step_update.
      { econstructor; eauto.
        { rewrite <- FF; eauto. }
        (* TODO: generalize! *)
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
        assert (S a_max) as SA by (by apply TCCOH.(etc_I_in_S)).
        rewrite <- FF.
        destruct (classic (a_max = w')) as [|AWNEQ]; [by desf|].
        edestruct (@wf_co_total G WF (Some locr) a_max) as [AWCO|AWCO].
        3: by apply AWNEQ.
        2: basic_solver.
        apply set_interA; split; auto.
        hahn_rewrite (@wf_urrD G sc locr) in CCUR.
        revert CCUR; clear; basic_solver 12.
        { etransitivity; eauto.
          apply Time.le_lteq; left.
          eapply f_to_co_mon; eauto.
          all: generalize SA SW'; clear; basic_solver. }
        exfalso.
        eapply transp_rf_co_urr_irr; eauto.
        1-3: by apply CON.
        exists w'; split.
        { right; red; apply RF. }
        exists a_max; split; eauto. }
      econstructor; eauto.
      { unfold TView.write_released, TView.write_tview. simpls. rewrite RLX_ORDW.
        rewrite REL_ORDW.
        unfold View.singleton_ur_if. rewrite RORD.
        rewrite RLX_ORDR.
        unfold LocFun.add. rewrite Loc.eq_dec_eq.
        rewrite View.join_comm with (lhs:=View.unwrap rel').
        rewrite !View.join_assoc.
        rewrite View.join_comm with (lhs:=View.unwrap rel').
          by rewrite FF. }
      { unfold TView.write_released, TView.read_tview. simpls.
        constructor. unfold View.join. simpls.
        rewrite <- RORD. by rewrite <- FF. }
      (* 3: by econstructor; eauto.  *)
      admit. }
    unnw.
    red; splits; red; splits; simpls.
    { apply TSTEP3. }
    { rewrite set_inter_union_r.
      apply set_subset_union_l; split.
      etransitivity; eauto.
      all: clear; basic_solver. }
    { ins. apply WF.(wf_rmwD) in RMW0.
      apply seq_eqv_l in RMW0; destruct RMW0 as [RR RMW0].
      apply seq_eqv_r in RMW0; destruct RMW0 as [RMW0 WW].
      split; intros [[HH|HH]|HH].
      { left; left. erewrite <- RMWCOV; eauto. }
      { subst. right. eapply wf_rmwf; eauto. }
      { subst. clear -WWRITE RR. type_solver. }
      { left; left. erewrite RMWCOV; eauto. }
      { subst. clear -WW RREAD. type_solver. }
      subst. left; right.
      eapply wf_rmw_invf; eauto. }
    { intros e' EE. 
      destruct (Ident.eq_dec (tid e') (tid w)) as [EQ|NEQ].
      { rewrite EQ. eexists.
        rewrite IdentMap.gss. eauto. }
      rewrite IdentMap.gso; auto. }
    { admit. }
    (* { ins. destruct (Ident.eq_dec thread' (tid w)) as [EQ|NEQ]. *)
    (*   { subst. rewrite IdentMap.gss in TID. *)
    (*     inversion TID. eapply PROM_IN_MEM0.  *)
    (*     rewrite IdentMap.gss. rewrite FF. reflexivity. } *)
    (*   eapply PROM_IN_MEM1; eauto. rewrite IdentMap.gso in TID; auto. *)
    (*   rewrite IdentMap.gso; eauto. rewrite IdentMap.gso; eauto. } *)
    { intros NFSC. etransitivity; [by apply SC_COV|].
      clear. basic_solver. }
    { intros QQ l.
      eapply max_value_same_set.
      { by apply SC_REQ1. }
      apply s_tm_n_f_steps.
      { apply TCCOH'. }
      { clear. basic_solver. }
      intros a [[H|H]|H] HH AA.
      { apply HH. by left. }
      { subst. clear -RREAD AA. type_solver. }
      subst. clear -WWRITE AA. type_solver. }
    { eapply Memory.add_closed with (mem1:=memory_cancel); eauto.
      eapply Memory.cancel_closed; eauto. }
    rewrite IdentMap.gss.
    eexists; eexists; eexists; splits; eauto; simpls.
    { ins. eapply PROM_DISJOINT0; eauto.
      rewrite IdentMap.gso in *; eauto.
      rewrite IdentMap.gso in *; eauto. }
    { clear WREPR REPR. rewrite <- FF, <- RORD, <- WORD.
      apply SIM_MEM1. }
    { eapply sim_tview_write_step; eauto.
      1,2: by apply CON.
      3: rewrite <- FF; eapply sim_tview_read_step; eauto. 
      { apply set_subset_union_l; split.
        all: intros x H.
        { apply TCCOH in H; apply H. }
          by desf. }
      5: { red. ins. eapply NEXT. red. eauto. }
      2,3: by apply CON.
      { red. ins. left. apply seq_eqv_r in REL0.
        destruct REL0 as [SB [COVY|]]; subst.
        { apply TCCOH in COVY. apply COVY. eexists.
          apply seq_eqv_r. eauto. }
        apply NEXT. eexists. apply seq_eqv_r. eauto. }
      { intros y [COVY TIDY].
        edestruct same_thread with (x:=r) (y:=y) as [[|SB]|SB]; eauto.
        { apply TCCOH in COVY. apply COVY. }
        { exfalso. apply RNCOV. by subst. }
        exfalso. apply RNCOV. apply TCCOH in COVY.
        apply COVY. eexists. apply seq_eqv_r. eauto. }
      { intros [HH|HH]. 
        { by apply WNCOV. }
        clear -HH RREAD WWRITE.
        type_solver. }
      { intros y [[COVY|XX] TIDY].
        2: { subst. apply rmw_in_sb; auto. }
        eapply sb_trans.
        2: { apply rmw_in_sb; eauto. }
        edestruct same_thread with (x:=r) (y:=y) as [[SS|SB]|SB]; eauto.
        { apply TCCOH in COVY. apply COVY. }
        { by rewrite TIDY. }
        { by subst. }
        exfalso. apply RNCOV. apply TCCOH in COVY.
        apply COVY. eexists. apply seq_eqv_r. eauto. }
      { intros y z HH. apply seq_eqv_r in HH. destruct HH as [SB HH].
        rewrite <- HH in *. clear z HH.
        destruct (classic (y = r)) as [|NEQ].
        { by right. }
        edestruct sb_semi_total_r with (x:=w) (y:=y) (z:=r) as [AA|AA]; eauto.
        { left. apply NEXT. eexists. apply seq_eqv_r. eauto. }
        exfalso. eapply WF.(wf_rmwi); eauto. }
      { erewrite Memory.add_o; eauto.
          by rewrite loc_ts_eq_dec_eq. }
      done. }
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
      1-4: reflexivity.
      all: intros l; unfold LocFun.add.
      all: destruct (Loc.eq_dec l locr) as [|NEQ]; subst.
      2,4: by apply EQ_REL.
      all: unfold View.join; simpls.
      all: rewrite EQ_CUR.
      2: done.
        by rewrite REL_PLN_RLX. }
    { assert (Memory.closed_timemap (TimeMap.singleton locr (f_to w)) memory_add) as AA.
      { unfold TimeMap.singleton, LocFun.add; red; ins.
        destruct (Loc.eq_dec loc locr); subst; eauto.
        erewrite Memory.add_o; eauto. rewrite loc_ts_eq_dec_eq. eauto. }
      assert (Memory.closed_timemap (TimeMap.singleton locr (f_from w)) memory_add) as BB.
      { unfold TimeMap.singleton, LocFun.add; red; ins.
        destruct (Loc.eq_dec loc locr); subst; eauto.
        rewrite <- FF.
        assert (f_to w' <> f_to w) as DD.
        { intros HH.
          eapply f_to_eq with (I:=S) in HH; subst; eauto.
          red. by rewrite WLOC. }
        erewrite Memory.add_o; eauto. rewrite loc_ts_eq_dec_neq; auto.
        erewrite Memory.remove_o; eauto. rewrite loc_ts_eq_dec_neq; auto.
        eauto. }
      assert (forall tmap,
                 Memory.closed_timemap tmap PC.(Configuration.memory) ->
                 Memory.closed_timemap tmap memory_add) as HH.
      { intros tmap HH. red. ins.
        specialize (HH loc). desc.
        exists from, val, released. apply NOTNEWM; auto.
        destruct (classic (loc = locr)) as [|]; subst; auto.
        destruct (classic (tmap locr = f_to w)) as [EQ|]; subst; auto.
        rewrite EQ in HH. exfalso.
        edestruct SIM_RES_MEM with (b:=w) as [OO]; eauto.
        rewrite OO in HH. inv HH. }
      unfold TView.write_tview, TView.read_tview; simpls.
      red; splits; simpls.
      all: desf; ins.
      all: repeat (apply Memory.join_closed_timemap); auto.
      all: try by (apply HH; apply MEM_CLOSE).
      all: try by apply Memory.closed_timemap_bot.
      all: unfold LocFun.add; destruct (Loc.eq_dec loc locr); subst; eauto.
      2,4: by (apply HH; apply MEM_CLOSE).
      all: unfold View.join; simpls.
      all: repeat (apply Memory.join_closed_timemap); auto.
      all: try by (apply HH; apply MEM_CLOSE).
        by apply Memory.closed_timemap_bot. }
    red. splits; eauto.
    ins. rewrite (INDEX_RMW w RMW); auto.
    rewrite TIDWR in *.
    apply sim_state_cover_rmw_events; auto. }
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
  11: { simpls.
        eapply msg_preserved_trans.
        2: by eapply msg_preserved_add; eauto.
        eapply msg_preserved_cancel; eauto. }
  10: { simpls.
        eapply closedness_preserved_trans.
        2: by eapply closedness_preserved_add; eauto.
        eapply closedness_preserved_cancel; eauto. }
  9: by eapply same_other_threads_steps; eauto.
  all: simpls; eauto.
  { erewrite coveredE; eauto.
    clear -RACT WACT. basic_solver. }
  { rewrite issuedE; eauto. generalize WACT. clear. basic_solver. }
  1-5: clear; basic_solver.
  { rewrite dom_sb_S_rfrmw_same_tid; auto. clear. basic_solver. }
  { ins. etransitivity.
    2: { symmetry. apply IdentMap.Facts.add_in_iff. }
    split; [by ins; eauto|].
    intros [|HH]; subst; auto.
    apply SIMREL_THREAD; auto. }
  {apply IdentMap.Facts.add_in_iff in TP.
   destruct TP as [TP|]; auto; subst. clear -TNEQ. desf. }
  ins.
  assert (b <> w) as BNW.
  { intros HH. subst. clear -TNEQ. desf. }
  apply SIM_RES_MEM1; auto.
Admitted.

End IssueReservedRelPlainStep.
