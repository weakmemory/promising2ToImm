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

From imm Require Import TraversalOrder.
From imm Require Import TLSCoherency.
From imm Require Import IordCoherency.
From imm Require Import AuxDef.
From imm Require Import TlsEventSets.
From imm Require Import Next.
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
Require Import ExistsIssueReservedInterval.
Require Import IssueReservedStepHelper.
Require Import MemoryClosedness.
Require Import SimulationRelProperties.
Require Import ReadPlainStepHelper.
From imm Require Import EventsTraversalOrder.
Require Import ExtTraversalProperties. 

Set Implicit Arguments.

Section IssueReservedRelPlainStep.

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

Lemma issue_rel_reserved_step_no_next PC T f_to f_from thread r w smode
      (TID : tid r = thread)
      (REL : Rel w) (RMW : rmw r w)
      (SW : reserved T w)
      (NONEXT : dom_sb_S_rfrmw G T rfi (eq w) ⊆₁ ∅)

      (TSTEP1 : ext_itrav_step
                 G sc (mkTL ta_cover r) T
                 (* (mkETC (mkTC (covered T ∪₁ eq r) (issued T)) S) *)
                 (T ∪₁ eq (mkTL ta_cover r))
      )
      (TSTEP2 : ext_itrav_step
                  G sc (mkTL ta_issue w) (T ∪₁ eq (mkTL ta_cover r))
                  (* (mkETC *)
                  (*    (mkTC (covered T ∪₁ eq r) (issued T ∪₁ eq w)) *)
                  (*    (S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G (mkETC T S) rfi (eq w))) *)
                  (T ∪₁ eq (mkTL ta_cover r) ∪₁ eq (mkTL ta_issue w) ∪₁ (eq ta_reserve <*> (eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w))))
      )

      (TSTEP3 : ext_itrav_step
                  G sc (mkTL ta_cover w)
                  (* (mkETC *)
                  (*    (mkTC (covered T ∪₁ eq r) (issued T ∪₁ eq w)) *)
                  (*    (S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G (mkETC T S) rfi (eq w))) *)
                  (T ∪₁ eq (mkTL ta_cover r) ∪₁ eq (mkTL ta_issue w) ∪₁ (eq ta_reserve <*> (eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w))))
                  (* (mkETC *)
                  (*    (mkTC (covered T ∪₁ eq r ∪₁ eq w) (issued T ∪₁ eq w)) *)
                  (*    (S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G (mkETC T S) rfi (eq w))) *)
                  (T ∪₁ eq (mkTL ta_cover r) ∪₁ eq (mkTL ta_cover w) ∪₁ eq (mkTL ta_issue w) ∪₁ (eq ta_reserve <*> (eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w))))
      )

      (SIMREL_THREAD : simrel_thread G sc PC T f_to f_from thread smode) :

  (* let T' := mkTC (covered T ∪₁ eq r ∪₁ eq w) (issued T ∪₁ eq w) in *)
  (* let S' := S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G (mkETC T S) rfi (eq w) in *)
  let T' := T ∪₁ eq (mkTL ta_cover r) ∪₁ eq (mkTL ta_cover w) ∪₁ eq (mkTL ta_issue w) ∪₁ (eq ta_reserve <*> (eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w))) in 
  exists f_to' PC',
    ⟪ PCSTEP : (plain_step MachineEvent.silent thread)⁺ PC PC' ⟫ /\
    ⟪ SIMREL_THREAD : simrel_thread G sc PC' T' f_to' f_from thread smode ⟫ /\
    ⟪ SIMREL :
        smode = sim_normal -> simrel G sc PC T f_to f_from ->
        simrel G sc PC' T' f_to' f_from ⟫.
Proof using WF CON.
  cdes SIMREL_THREAD. cdes COMMON. cdes LOCAL.

  assert (coherence G) as COH by apply CON.
  assert (wf_sc G sc) as WF_sc by apply CON.
  assert (coh_sc G sc) as COH_sc by apply CON.

  assert (NEXT : next G (covered T) r).
  { eapply ext_itrav_step_cov_next; eauto. }
 
  assert (WTID : thread = tid w).
  { rewrite <- TID. by apply (wf_rmwt WF). }
  assert (ISS : ~ issued T w).
  { cdes TSTEP2. inversion TSTEP0. intros HH. apply ets_new_ta.
    left. destruct HH as [[a e] [[? [=]] [=]]]. vauto. }

  assert (reserved T ⊆₁ E ∩₁ W) as SEW.
  { apply set_subset_inter_r. split; [apply RCOH| apply reservedW]; eauto. }

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

  assert (COV : coverable G sc T r).
  { eapply ext_itrav_step_cov_coverable; eauto. } 

  assert (issued T w') as WISS.
  { eapply dom_rf_coverable; eauto. eexists. splits; vauto. } 

  assert (reserved T w') as SW'.
  { by eapply RCOH. }

  assert (~ is_init r) as RNINIT.
  { intros H; apply (init_w WF) in H.
    type_solver. }
  assert (sb r w) as WRSB.
  { apply wf_rmwi in RMW; red in RMW; desf. }

  assert (~ covered T w) as WNCOV.
  { intros H; apply NEXT.
    eapply dom_sb_covered; eauto. basic_solver 10. }
  assert (~ is_init w) as WNINIT.
  { intros H. apply WNCOV. eapply init_covered; vauto. }

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

  set (S' := reserved T ∪₁ eq w ∪₁
               dom_sb_S_rfrmw G (T ∪₁ eq (mkTL ta_cover r)) rfi (eq w)).
  assert (S' ⊆₁ E ∩₁ W) as SEW'.
  { unfold S'. rewrite SEW at 1. unionL; auto.
    { generalize WACT WWRITE. clear. basic_solver. }
    apply set_subset_inter_r. split; auto using ExtTraversalProperties.dom_sb_S_rfrmwE, ExtTraversalProperties.dom_sb_S_rfrmwD. }

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

  assert (issuable G sc (T ∪₁ eq (mkTL ta_cover r)) w) as WNNISS.
  { eapply issuable_next_w; eauto.
    split; simpls.
    red; split; [split|]; auto.
    { red. intros x [y SBB]. apply seq_eqv_r in SBB. desc. rewrite <- SBB0 in *.
      clear y SBB0.
      destruct (classic (x = r)) as [->|NEQ].
      { clear. find_event_set. }
      edestruct sb_semi_total_r with (x:=w) (y:=x) (z:=r); eauto.
      { eapply dom_sb_covered; eauto. exists r.
        apply seq_eqv_r. split; auto. clear. find_event_set. }
      exfalso. eapply (wf_rmwi WF); eauto. }
    clear WREPR REPR.
    assert (r <> w) as NEQ by (intros ->; type_solver). 
    clear -NEQ WNCOV. separate_set_event. }

  assert (reserve_coherent G (T ∪₁ eq (mkTL ta_cover r))) as RCOH'.
  { by apply reserve_coherent_add_cover. }


  (*****)
  (* forward eapply issue_reserved_step_helper_no_next with (T := T ∪₁ eq (mkTL ta_cover r)); eauto. *)
  (* { clear -FCOH. by simplify_tls_events. } *)
  (* { eapply sim_res_prom_issued_reserved_subset; [.. | apply SIM_RPROM]. *)
  (*   all: clear; by simplify_tls_events. } *)
  (* { eapply sim_res_mem_issued_reserved_subsets; [.. | apply SIM_RES_MEM]. *)
  (*   all: clear; by simplify_tls_events. } *)
  (* { simpl in SIM_TVIEW0. ins. simpls. *)
  (*   red. splits.  *)
  (*   { move SIM_TVIEW at bottom. red in SIM_TVIEW. desc. *)
  (*     red in CUR. red. *)
  (*     ins. specialize (CUR l). *)
  (*     simplify_tls_events. rewrite t_cur_union. *)
      

  edestruct (fun w1 w2 rcoh wri fcoh x z k w3 w4 w5 =>
               @issue_reserved_step_helper_no_next
               G WF sc CON (T ∪₁ eq (mkTL ta_cover r))
               w1 w2 rcoh wri f_to f_from fcoh
               (Configuration.mk x (Configuration.sc PC) (Configuration.memory PC))
               w3 smode w4 w5 (Local.mk z k)
            ) with (w:=w) (valw:=valw) (ordw:=Events.mod lab w)
    as [p_rel H].
  1-3: by apply TSTEP1.
  { clear -RELCOV. simplify_tls_events. rewrite RELCOV. basic_solver. }
  { clear -FCOH. by simplify_tls_events. }
  all: simpls.
  2: by apply SIM_PROM0.
  5: by apply PLN_RLX_EQ0.
  all: eauto.
  { eapply sim_res_prom_issued_reserved_subset; [.. | apply SIM_RPROM].
    all: clear; by simplify_tls_events. }
  { ins. rewrite IdentMap.gso in *; eauto. }
  { eapply sim_res_mem_issued_reserved_subsets; [.. | apply SIM_RES_MEM].
    all: clear; by simplify_tls_events. }
  { rewrite IdentMap.gss. eauto. }
  { clear -SW. find_event_set. }
  { clear -ISS. separate_set_event. }
  { clear -NONEXT. unfold dom_sb_S_rfrmw in *. by simplify_tls_events. }

  (*****)
  desc. red in H. desc.
  destruct H0 as [H|H]; desc.
  { exfalso. apply NINRMW. exists w'. apply seq_eqv_l. split; eauto.
    clear -WISS. find_event_set. }
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
  
  set (f_to' := upd f_to w (Time.middle (f_from w) (f_to w))).
  assert (ISSEQ_TO : forall e : actid, issued T e -> f_to' e = f_to e).
  { ins. unfold f_to'. rewrite updo; auto. by intros HH; subst. }

  set (pe := ThreadEvent.update
               locr (f_from w) (f_to' w) valr valw
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
                          (View.singleton_ur locr (f_to' w))))
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
  { rewrite <- ISSEQ_TO; auto.
    apply FCOH0; auto.
    { clear -SW'. find_event_set. }
    clear. find_event_set. }

  assert (forall l to from msg 
                 (NEQ  : l <> locr \/ to <> f_to  w)
                 (NEQ' : l <> locr \/ to <> f_to' w),
             Memory.get l to memory_add = Some (from, msg) <->
             Memory.get l to (Configuration.memory PC) = Some (from, msg))
    as NOTNEWM.
  { ins. erewrite Memory.add_o; eauto.
    rewrite loc_ts_eq_dec_neq; auto.
    erewrite Memory.remove_o; eauto.
    by rewrite loc_ts_eq_dec_neq. }

  set (pe_cancel :=
         ThreadEvent.promise
           locr (f_from w) (f_to w) Message.reserve
           Memory.op_kind_cancel).

  assert (f_to w' <> f_to w) as FWNEQ.
  { intros HH.
    eapply f_to_eq with (I:=reserved T) in HH; subst; eauto.
    red. by rewrite WLOC. }
  assert (f_to w' <> f_to' w) as FWNEQ'.
  { rewrite <- ISSEQ_TO; auto.
    intros HH.
    eapply f_to_eq in HH; (try by apply FCOH0); subst; eauto.
    { clear -TLSCOH RCOH WF WACT WWRITE. simplify_tls_events.
      apply set_subset_inter_r. split.
      { rewrite rcoh_S_in_E, dom_sb_S_rfrmwE; basic_solver. }
      rewrite reservedW, dom_sb_S_rfrmwD; basic_solver. }
    { red. by rewrite WLOC. }
    all: clear -SW'; find_event_set. }

  assert (forall y : actid, covered T y /\ tid y = tid r -> sb y r) as COVNR.
  { intros y [COVY TIDY].
    edestruct same_thread with (x:=r) (y:=y) as [[|SB]|SB]; eauto.
    { eapply coveredE with (T := T); eauto. }
    { exfalso. apply RNCOV. by subst. }
    exfalso. apply RNCOV.
    eapply dom_sb_covered; eauto. clear -COVY SB. basic_solver 10. }
  assert (doma (sb ⨾ ⦗eq r⦘) (covered T)) as DOMASBR.
  { red. ins. eapply NEXT. red. eauto. }

  exists f_to'.
  eexists (Configuration.mk _ _ memory_add).
  apply and_assoc. apply pair_app.
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
      apply Thread.step_program.
      constructor.
      { assert (ev = ThreadEvent.get_program_event pe) as EV' by done.
        rewrite EV' in STEP; eauto. }
      unfold pe; eapply Local.step_update.
      { econstructor; eauto.
        { simpls. rewrite <- FF.
          erewrite Memory.remove_o; eauto.
          rewrite loc_ts_eq_dec_neq; eauto. }
        (* TODO: generalize! *)
        assert
          (Time.le (View.rlx (TView.cur (Local.tview local)) locr) (f_from w))
          as PP.
        2: constructor; auto.
        2: by cdes PLN_RLX_EQ; simpls; rewrite EQ_CUR.
        edestruct (max_event_cur) as [a_max]; eauto; desc.
        assert (E a_max) as EA.
        { apply (wf_urrE WF) in CCUR.
          revert CCUR; unfold seq; unfolder; ins; desf.
            by apply CON. }
        assert (issued T a_max) as AISS.
        { assert (A: (urr G sc locr ⨾ ⦗coverable G sc T⦘) a_max r)by basic_solver.
          apply (urr_coverable) in A; try done.
          revert A; unfold seq; unfolder; ins; desf. }
        assert (reserved T a_max) as SA by (by apply (rcoh_I_in_S RCOH)).
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
      simpls. auto. intros HH.
      eapply nonsynch_loc_le with (mem2:=(Local.promises local)); auto.
      eapply memory_remove_le; eauto. }
    unnw.
    assert (  covered
                (T ∪₁ eq (mkTL ta_cover r) ∪₁ eq (mkTL ta_cover w) ∪₁ eq (mkTL ta_issue w)
                   ∪₁ eq ta_reserve <*> (eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w))) ≡₁ covered T ∪₁ eq r ∪₁ eq w) as COV'.
    { clear. by simplify_tls_events. }
    red; splits; red; splits; simpls.
    1-3: by apply TSTEP3. 
    { clear -RELCOV. simplify_tls_events. relsf. rewrite RELCOV. basic_solver. }
    { ins. apply (wf_rmwD WF) in RMW0.
      apply seq_eqv_l in RMW0; destruct RMW0 as [RR RMW0].
      apply seq_eqv_r in RMW0; destruct RMW0 as [RMW0 WW].
      split; intros [[HH|<-]|<-]%COV'.
      { pose proof (RMWCOV _ _ RMW0). clear -HH H. find_event_set. } 
      { apply COV'. right. eapply wf_rmwf; eauto. }
      { clear -WWRITE RR. type_solver. }
      { pose proof (RMWCOV _ _ RMW0). clear -HH H. find_event_set. }
      { clear -WW RREAD. type_solver. }
      apply COV'. left. right. eapply wf_rmw_invf; eauto. }
    { intros e' EE. 
      apply IdentMap.Facts.add_in_iff.
      destruct (Ident.eq_dec e' (tid w)) as [|NEQ]; subst; auto.
      right. apply IdentMap.Facts.add_in_iff. auto. }
    { ins. destruct (Ident.eq_dec thread' (tid w)) as [EQ|NEQ].
      { subst. rewrite IdentMap.gss in TID.
        inversion TID. simpls. }
      eapply PROM_IN_MEM1; eauto.
      do 2 (rewrite IdentMap.gso in TID; auto).
      do 2 (rewrite IdentMap.gso; eauto). }
    { eapply f_to_coherent_more; [..| apply FCOH0]; eauto.
      unfold dom_sb_S_rfrmw. clear. simplify_tls_events. basic_solver. }
    { intros NFSC. etransitivity; [by apply SC_COV|].
      clear. simplify_tls_events. basic_solver. }
    { intros QQ l.
      eapply max_value_same_set.
      { by apply SC_REQ1. }
      apply s_tm_n_f_steps.
      { etransitivity; [apply init_covered| ]; eauto. }
      { clear. simplify_tls_events. basic_solver. }      
      intros a [[H|H]|H]%COV' HH AA.
      { apply HH. clear -H. find_event_set. }
      { subst. clear -RREAD AA. type_solver. }
      subst. clear -WWRITE AA. type_solver. }
    { eapply reserved_time_same_issued_reserved; [apply RESERVED_TIME1| ..]; auto.
      all: clear; unfold dom_sb_S_rfrmw; simplify_tls_events; auto. }
    { eapply Memory.add_closed with (mem1:=memory_cancel); eauto.
      eapply Memory.cancel_closed; eauto. }
    rewrite IdentMap.gss.
    assert (dom_sb_S_rfrmw G (T ∪₁ eq (mkTL ta_cover r)) rfi (eq w) ≡₁ dom_sb_S_rfrmw G T rfi (eq w)) as DS' by (unfold dom_sb_S_rfrmw; clear; by simplify_tls_events).
    assert (tls_coherent G (T ∪₁ eq (mkTL ta_cover r))) as TCOH'.
    { eapply tls_coherent_ext; eauto.
      red. left. do 2 (split; eauto). }  
    assert (iord_coherent G sc (T ∪₁ eq (mkTL ta_cover r))) as ICOH'.
    { eapply iord_coherent_extend; eauto.
      eapply coverable_iord_dom_cond; eauto. }
    assert (covered T ∪₁ eq r ≡₁ covered (T ∪₁ eq (mkTL ta_cover r))) as COV'_. 
    { clear. by simplify_tls_events. }

    eexists; eexists; eexists; splits; eauto; simpls.
    { erewrite tau_steps_step_same_instrs; eauto. }
    { ins. edestruct PROM_DISJOINT0 as [HH|]; eauto.
      do 2 (rewrite IdentMap.gso in *; eauto). }
    { eapply sim_prom_more; [..| apply SIM_PROM1]; auto. rewrite DS'. auto. }
    { eapply sim_res_prom_more; [..| apply SIM_RES_PROM]; auto.
      rewrite DS'. auto. }
    (* { eapply sim_mem_more; [..| apply SIM_MEM1]; auto.
      { rewrite DS'. auto. }
      f_equal. ins. vauto.  *)
    (* } *)
    { clear WREPR REPR. rewrite <- FF, <- RORD, <- WORD.
      eapply sim_mem_more; [..| apply SIM_MEM1]; eauto.
      by rewrite DS'. }
    { clear WREPR REPR. rewrite <- FF, <- RORD, <- WORD.
      eapply sim_res_mem_more; [..| apply SIM_RES_MEM0]; eauto.
      by rewrite DS'. }
    { rewrite COV'. 
      eapply sim_tview_write_step; eauto. 
      3: { rewrite <- FF.
           rewrite COV'_. 
           eapply sim_tview_f_issued
                  with (T := T ∪₁ eq (mkTL ta_cover r)). 
           7: { rewrite covered_union, covered_singleton.  
                eapply sim_tview_read_step; eauto. }
           all: eauto.
           ins. apply ISSEQ_TO.
           clear -ISS0. eapply set_equiv_exp; [| apply ISS0].
           by simplify_tls_events. }
      { rewrite coveredE; eauto. clear -RACT. basic_solver. }
      { apply doma_alt. rewrite COV'_. eapply dom_sb_covered; eauto. }
      { clear -WNCOV WWRITE RREAD.
        assert (r <> w) by (intros ->; type_solver). 
        separate_set_event. }
      { intros y [[COVY|XX] TIDY].
        2: { subst. apply rmw_in_sb; auto. }
        eapply sb_trans.
        2: { apply rmw_in_sb; eauto. }
        edestruct same_thread with (x:=r) (y:=y) as [[SS|SB]|SB]; eauto.
        { eapply coveredE; [..| apply COVY]; eauto. }
        { by rewrite TIDY. }
        { by subst. }
        exfalso. apply RNCOV. eapply dom_sb_covered; eauto.
        clear -COVY SB. basic_solver 10. }
      { intros y z HH. apply seq_eqv_r in HH. destruct HH as [SB HH].
        rewrite <- HH in *. clear z HH.
        destruct (classic (y = r)) as [|NEQ].
        { by right. }
        edestruct sb_semi_total_r with (x:=w) (y:=y) (z:=r) as [AA|AA]; eauto.
        { left. apply NEXT. eexists. apply seq_eqv_r. eauto. }
        exfalso. eapply (wf_rmwi WF); eauto. }
      { erewrite Memory.add_o; eauto. by rewrite loc_ts_eq_dec_eq. }
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
    { assert (Memory.closed_timemap (TimeMap.singleton locr (f_to' w)) memory_add) as AA.
      { unfold TimeMap.singleton, LocFun.add; red; ins.
        destruct (Loc.eq_dec loc locr); subst; eauto.
        erewrite Memory.add_o; eauto. rewrite loc_ts_eq_dec_eq. eauto. }
      assert (Memory.closed_timemap (TimeMap.singleton locr (f_from w)) memory_add) as BB.
      { unfold TimeMap.singleton, LocFun.add; red; ins.
        destruct (Loc.eq_dec loc locr); subst; eauto.
        rewrite <- FF.
        erewrite Memory.add_o; eauto. rewrite loc_ts_eq_dec_neq; auto.
        erewrite Memory.remove_o; eauto. rewrite loc_ts_eq_dec_neq; auto.
        eauto. }
      assert (forall tmap,
                 Memory.closed_timemap tmap (Configuration.memory PC) ->
                 Memory.closed_timemap tmap memory_add) as HH.
      { intros tmap HH. red. ins.
        specialize (HH loc). desc.
        exists from, val, released.
        destruct (classic (loc = locr)) as [|]; subst; auto.
        2: by apply NOTNEWM; auto.
        apply NOTNEWM; auto.
        { destruct (classic (tmap locr = f_to w)) as [EQ|]; subst; auto.
          rewrite EQ in HH. exfalso.
          edestruct SIM_RES_MEM with (b:=w) as [OO]; eauto.
          rewrite OO in HH. inv HH. }
        destruct (classic (tmap locr = f_to' w)) as [EQ|]; subst; auto.
        rewrite EQ in HH. exfalso.
        unfold f_to' in HH. rewrite NINMEM in HH. inv HH. }
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
    etransitivity; [apply set_equiv_exp| ].
    { clear. simplify_tls_events. reflexivity. }    
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
  apply IdentMap.Facts.add_in_iff in AA.
  destruct AA as [AA|AA]; subst; auto.
  { clear -TNEQ. desf. }
  apply SIMREL in AA. cdes AA.
  eapply simrel_thread_local_step with (thread:=tid w) (PC:=PC) (T:=T); eauto.
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
  1-8: clear -TLSCOH WNINIT WACT RACT WF; simplify_tls_events; try basic_solver. 
  { erewrite coveredE; eauto. basic_solver. }
  { rewrite issuedE; eauto. basic_solver. }
  { rewrite dom_sb_S_rfrmw_same_tid; auto. basic_solver. }
  { ins.
    etransitivity; [|by symmetry; apply IdentMap.Facts.add_in_iff].
    split.
    { ins; eauto. right. apply IdentMap.Facts.add_in_iff. eauto. }
    intros [|HH]; subst; auto.
    { apply SIMREL_THREAD; auto.
      split; auto. now apply WF. }
    apply IdentMap.Facts.add_in_iff in HH.
    destruct HH as [|HH]; subst; auto.
    apply IdentMap.Facts.in_find_iff. rewrite LLH. clear. desf. }
  { apply IdentMap.Facts.in_find_iff. rewrite LLH0. clear. desf. }
  { eapply sim_prom_f_issued; eauto. }
  { (* TODO: generalize to a lemma? *)
    red. ins. apply SIM_RPROM0 in RES. desc.
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
Unshelve.
apply state.
Qed.

End IssueReservedRelPlainStep.
