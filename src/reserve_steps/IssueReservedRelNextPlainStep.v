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
From imm Require Import AuxDef.
From imm Require Import SimClosure.

From imm Require Import TraversalOrder.
From imm Require Import TLSCoherency.
From imm Require Import IordCoherency.
From imm Require Import TlsEventSets.
Require Import ExtTraversalConfig.
Require Import ExtTraversal.
Require Import ExtTraversalProperties.
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
From imm Require Import Next.
From imm Require Import EventsTraversalOrder.

Set Implicit Arguments.

Section IssueReservedRelNextPlainStep.

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

(* TODO: move*)
Lemma dom_sb_S_rfrmw_same_reserved T1 T2 rrf P
      (SAME_RES: reserved T1 ≡₁ reserved T2):
  dom_sb_S_rfrmw G T1 rrf P ≡₁ dom_sb_S_rfrmw G T2 rrf P. 
Proof using. unfold dom_sb_S_rfrmw. by rewrite SAME_RES. Qed.  


Lemma issue_rel_reserved_step_with_next PC T f_to f_from thread r w wnext smode
      (TID : tid r = thread)
      (REL : Rel w) (RMW : rmw r w)
      (SW : reserved T w)
      (WNEXT : dom_sb_S_rfrmw G T rfi (eq w) wnext)

      (TSTEP1 : ext_itrav_step
                 G sc (mkTL ta_cover r) T
                 (T ∪₁ eq (mkTL ta_cover r))
      )
      (TSTEP2 : ext_itrav_step
                  G sc (mkTL ta_issue w) (T ∪₁ eq (mkTL ta_cover r))
                  (T ∪₁ eq (mkTL ta_cover r) ∪₁ eq (mkTL ta_issue w) ∪₁ (eq ta_reserve <*> (eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w))))
      )
      (TSTEP3 : ext_itrav_step
                  G sc (mkTL ta_cover w)
                  (T ∪₁ eq (mkTL ta_cover r) ∪₁ eq (mkTL ta_issue w) ∪₁ (eq ta_reserve <*> (eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w))))
                  (T ∪₁ eq (mkTL ta_cover r) ∪₁ eq (mkTL ta_cover w) ∪₁ eq (mkTL ta_issue w) ∪₁ (eq ta_reserve <*> (eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w))))
      )
      (SIMREL_THREAD : simrel_thread G sc PC T f_to f_from thread smode) :

  (* let T' := mkTC (covered T ∪₁ eq r ∪₁ eq w) (issued T ∪₁ eq w) in *)
  (* let S' := S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G (mkETC T S) rfi (eq w) in *)
  let T' := (T ∪₁ eq (mkTL ta_cover r) ∪₁ eq (mkTL ta_cover w) ∪₁ eq (mkTL ta_issue w) ∪₁ (eq ta_reserve <*> (eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w)))) in
  exists f_to' f_from' PC',
    ⟪ PCSTEP : (plain_step MachineEvent.silent thread)⁺ PC PC' ⟫ /\
    ⟪ SIMREL_THREAD : simrel_thread G sc PC' T' f_to' f_from' thread smode ⟫ /\
    ⟪ SIMREL :
        smode = sim_normal -> simrel G sc PC T f_to f_from ->
        simrel G sc PC' T' f_to' f_from' ⟫.
Proof using WF CON.
  cdes SIMREL_THREAD. cdes COMMON. cdes LOCAL.

  assert (NEXT : next G (covered T) r).
  { eapply ext_itrav_step_cov_next; eauto. }
 
  assert (WTID : thread = tid w).
  { rewrite <- TID. by apply (wf_rmwt WF). }
  assert (ISS : ~ issued T w).
  { intros HH. inversion TSTEP2. apply ets_new_ta.
    left. by apply tls_set_alt. }

  assert (reserved T ⊆₁ E ∩₁ W) as SEW.
  { generalize (rcoh_S_in_E RCOH). generalize (reservedW WF TLSCOH RCOH). clear. basic_solver. }

  assert (sc_per_loc G) as SC_PER_LOC.
  { by apply coherence_sc_per_loc; cdes CON. }
  
  assert (E wnext /\ W wnext) as [ENEXT WWNEXT].
  { split.
    { eapply dom_sb_S_rfrmwE; eauto. }
    apply W_ex_in_W; auto. eapply dom_sb_S_rfrmw_in_W_ex; eauto. }
  
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
  { eapply EventsTraversalOrder.dom_rf_coverable; eauto. basic_solver 10. }

  assert (reserved T w') as SW'.
  { eapply rcoh_I_in_S; eauto. }

  assert (~ is_init r) as RNINIT.
  { intros H; apply (init_w WF) in H.
    type_solver. }
  assert (sb r w) as WRSB.
  { apply wf_rmwi in RMW; red in RMW; desf. }

  assert (~ covered T w) as WNCOV.
  { intros H; apply NEXT.
    eapply dom_sb_covered; eauto. basic_solver 10. }
  assert (~ is_init w) as WNINIT.
  { intros H. apply WNCOV. eapply init_covered; eauto. basic_solver. }

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

  assert (reserved T ∪₁ eq w ∪₁ dom_sb_S_rfrmw G
            (T ∪₁ eq (mkTL ta_cover r)) rfi (eq w)
            ⊆₁ E ∩₁ W) as SEW'.
  { rewrite SEW at 1. unionL; auto.
    { generalize WACT WWRITE. clear. basic_solver. }
    generalize dom_sb_S_rfrmwE, dom_sb_S_rfrmwD. basic_solver. }

  edestruct SIM_MEM as [rel' DOM'].
  { apply WISS. }
  all: eauto.
  simpls. desc.
  clear DOM'1.

  assert ((rf ⨾ rmw) w' w) as RFRMW.
  { exists r; split; auto. }

  assert (tid wnext = tid w) as TWNEXTEQ.
  { eapply dom_sb_S_rfrmw_same_tid; eauto. }
  
  assert (forall y : actid, covered T y /\ tid y = tid w -> sb y w) as COVSB.
  { intros y [COVY TIDY].
    destruct (same_thread G w y) as [[ST|ST]|ST]; subst; auto.
    { eapply coveredE, COVY; eauto. }
    { done. }
    assert (covered T w) as CC; [| by vauto]. 
    eapply dom_sb_covered; eauto. eexists. basic_solver. }

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

  (* assert (tc_coherent G sc (mkTC (covered T ∪₁ eq r) (issued T))) *)
  (*   as TCCOH1. *)
  (* { apply TSTEP1. } *)

  assert (issuable G sc (T ∪₁ eq (mkTL ta_cover r)) w) as WNNISS.
  { eapply issuable_next_w; eauto.
    split; simpls.
    red; split; [split|]; auto.
    { red. intros x [y SBB]. apply seq_eqv_r in SBB. desc. rewrite <- SBB0 in *.
      clear y SBB0.
      destruct (classic (x = r)) as [->|NEQ].
      { clear. find_event_set. }
      edestruct sb_semi_total_r with (x:=w) (y:=x) (z:=r); eauto.
      { apply covered_union. left.
        apply proj1, proj2 in NEXT. eapply NEXT. basic_solver 10. }
      exfalso. eapply (wf_rmwi WF); eauto. }
    assert (r <> w) as NEQ by (intros ->; type_solver).
    clear -WNCOV NEQ. separate_set_event. }

  edestruct (fun w1 w2 rcoh cov fcoh x z k w3 w4 w5 =>
               @issue_reserved_step_helper_with_next
               G WF sc CON (T ∪₁ eq (mkTL ta_cover r))
               w1 w2 rcoh cov f_to f_from fcoh
               (Configuration.mk x (Configuration.sc PC) (Configuration.memory PC))
               w3 smode w4 w5 (Local.mk z k)
            ) with (w:=w) (valw:=valw) (ordw:=Events.mod lab w) (wnext:=wnext)
    as [p_rel H].
  all: simpls.
  3: by apply SIM_PROM0.
  6: by apply PLN_RLX_EQ0.
  all: eauto.
  { clear -FCOH. by simplify_tls_events. }
  { eapply sim_res_prom_issued_reserved_subset; [..| apply SIM_RPROM].
    all: clear; simplify_tls_events; auto. }
  { ins. rewrite IdentMap.gso in *; eauto. }
  { eapply sim_res_mem_issued_reserved_subsets; [.. | apply SIM_RES_MEM].
    all: clear; by simplify_tls_events. } 
  { rewrite IdentMap.gss. eauto. }
  { clear -SW. find_event_set. }
  { clear -ISS. separate_set_event. }
  { clear -WNEXT. unfold dom_sb_S_rfrmw in *. by simplify_tls_events'. }
  desc. red in H0. desc.
  destruct H1 as [H1|H1]; desc.
  { exfalso. apply NINRMW. exists w'. apply seq_eqv_l. split; eauto.
    clear -WISS. find_event_set. }
  assert (p = w') as PW.
  { eapply wf_rfrmwf; eauto. }
  rewrite PW in *; clear PW.
  simpls.
  assert (p_rel0 = rel') as PW.
  { rewrite INMEM in P_INMEM. clear -P_INMEM. inv P_INMEM. }
  rewrite PW in *; clear PW.
  destruct (is_rel lab w) eqn:RELVV; simpls.

  set (f_to' := upd (upd f_to w (Time.middle (f_from w) (f_to w))) wnext (f_to w)).
  set (f_from' := upd f_from wnext (Time.middle (f_from w) (f_to w))).

  set (pe := ThreadEvent.update
               locr (f_from' w) (f_to' w) valr valw
               rel' (Some
                       (View.join
                          (View.join
                             (View.join
                                (View.join (TView.cur (Local.tview local))
                                           (View.singleton_ur_if
                                              (Ordering.le
                                                 Ordering.relaxed
                                                 (Event_imm_promise.rmod (Events.mod lab r))) locr
                                              (f_to' w')))
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

  assert ((rf ⨾ rmw) w wnext) as RFRMWNEXT.
  { (* TODO: generalize to a lemma. *)
    destruct WNEXT as [_ [y AA]]. destruct_seq_l AA as BB; subst.
    generalize AA. clear. unfold Execution.rfi. basic_solver 10. }
  assert (~ reserved T wnext) as NRESNEXT.
  { intros HH. apply ISS.
    eapply ExtTraversalProperties.dom_rf_rmw_S_in_I; eauto.
    exists wnext. apply seqA. apply seq_eqv_r. split; auto. }
  assert (~ issued T wnext) as NISSNEXT.
  { intros HH. apply NRESNEXT. eapply rcoh_I_in_S; eauto. }

  assert (w <> wnext) as WNEQNEXT.
  { intros HH; subst. eapply (wf_rfrmw_irr WF); eauto. }

  assert (f_to' w' = f_from' w) as FF'.
  { apply FCOH0; auto.
    all: clear -SW' SW; find_event_set. }
  
  assert (f_to w' = f_from' w) as FF.
  { rewrite <- ISSEQ_TO; auto. }

  (* assert (forall l to from msg  *)
  (*                (NEQ : l <> locr \/ to <> f_to w), *)
  (*            Memory.get l to memory_add = Some (from, msg) <-> *)
  (*            Memory.get l to (Configuration.memory PC) = Some (from, msg)) *)
  (*   as NOTNEWM. *)
  (* { ins. erewrite Memory.add_o; eauto. *)
  (*   rewrite loc_ts_eq_dec_neq; auto. *)
  (*   erewrite Memory.remove_o; eauto. *)
  (*   rewrite loc_ts_eq_dec_neq; auto. } *)

  (* set (pe_cancel := *)
  (*        ThreadEvent.promise *)
  (*          locr (f_from w) (f_to w) Message.reserve *)
  (*          Memory.op_kind_cancel). *)

  assert (reserved
    (T ∪₁ eq (mkTL ta_cover r) ∪₁ eq (mkTL ta_cover w) ∪₁ eq (mkTL ta_issue w)
     ∪₁ eq ta_reserve <*>
        (eq w ∪₁ dom_sb_S_rfrmw G (T ∪₁ eq (mkTL ta_cover r)) rfi (eq w)))
  ⊆₁ E ∩₁ W) as RES'_EW. 
  { clear -WF SEW WACT WWRITE. simplify_tls_events.
    rewrite SEW. generalize dom_sb_S_rfrmwD, dom_sb_S_rfrmwE.
    basic_solver 10. }

  assert (f_to' w' <> f_to' w) as FWNEQ.
  { intros HH.
    eapply f_to_eq in HH.
    5: by eauto.
    all: eauto.
    { subst. generalize ISS WISS. clear. desf. }     
    { red. by rewrite WLOC. }
    all: clear -SW' SW; find_event_set. }
  
  assert (loc lab wnext = Some locr) as LOCWNEXT.
  { rewrite <- WLOC. symmetry. by apply (wf_rfrmwl WF). }

  forward eapply (@dom_sb_S_rfrmw_same_reserved T (T ∪₁ eq (mkTL ta_cover r)) rfi (eq w))  as SAME_DSR.
  { clear. by simplify_tls_events. }  

  assert (f_to' w' <> f_to' wnext) as FWNEQ'.
  { intros HH.
    eapply f_to_eq in HH.
    5: by eauto.
    all: eauto.
    { subst. generalize NISSNEXT WISS. clear. desf. }
    { red. by rewrite WPLOC. }
    all: apply SAME_DSR in WNEXT; clear -SW' SW WNEXT; find_event_set. }

  assert (Memory.get locr (f_to w) (Configuration.memory PC) =
          Some (f_from w, Message.reserve)) as W_INMEM.
  { edestruct SIM_RES_MEM with (b:=w) as [OO]; eauto. }

  exists f_to', f_from'.
  eexists (Configuration.mk _ _ memory_split).
  apply and_assoc. apply pair_app.
  { split.
    { eapply t_step.
      set (pe' := MachineEvent.silent).
      arewrite (pe' = ThreadEvent.get_machine_event pe) by simpls.
      eapply plain_step_intro with (lang:=thread_lts (tid w)); eauto.
      2: by unfold pe; clear; desf.
      apply Thread.step_program.
      constructor.
      { assert (ev = ThreadEvent.get_program_event pe) as EV' by done.
        rewrite EV' in STEP; eauto. }
      unfold pe; eapply Local.step_update.
      { econstructor; eauto.
        { simpls. rewrite <- FF; eauto. }
        (* TODO: generalize! *)
        assert
          (Time.le (View.rlx (TView.cur (Local.tview local)) locr) (f_from' w))
          as PP.
        2: constructor; auto.
        2: by cdes PLN_RLX_EQ; simpls; rewrite EQ_CUR.
        edestruct (max_event_cur) as [a_max]; eauto; desc.
        assert (E a_max) as EA.
        { apply (wf_urrE WF) in CCUR; [|by apply CON].
          revert CCUR. clear -NEQ. basic_solver. }
        assert (issued T a_max) as AISS.
        { assert (A: (urr G sc locr ⨾ ⦗coverable G sc T⦘) a_max r).
          { basic_solver. }
          apply (urr_coverable) in A; try done.
          2: { apply CON. }
          revert A. clear. basic_solver. }
        assert (reserved T a_max) as SA by (eapply rcoh_I_in_S; eauto). 
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
        rewrite <- FF. rewrite ISSEQ_TO; auto. }
      { unfold TView.write_released, TView.read_tview. simpls.
        constructor. unfold View.join. simpls.
        rewrite <- RORD. by rewrite <- FF. }
      simpls. econstructor.
      eapply Memory.promise_split; eauto.
      all: by unfold f_to'; rewrite ISSEQ_TO with (e:=w'); eauto. }
    unnw.

    assert (  covered
                (T ∪₁ eq (mkTL ta_cover r) ∪₁ eq (mkTL ta_cover w) ∪₁ eq (mkTL ta_issue w)
                   ∪₁ eq ta_reserve <*> (eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w))) ≡₁ covered T ∪₁ eq r ∪₁ eq w) as COV'.
    { clear. by simplify_tls_events. }
    assert (covered T ∪₁ eq r ≡₁ covered (T ∪₁ eq (mkTL ta_cover r))) as COV'_. 
    { clear. by simplify_tls_events. }


    red; splits; red; splits; simpls.
    1-3: by apply TSTEP3.    
    { clear -RELCOV. simplify_tls_events. generalize RELCOV. basic_solver 10. }
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
      destruct (Ident.eq_dec e' (tid w)) as [|NEQ]; subst; auto. }
    { ins. destruct (Ident.eq_dec thread' (tid w)) as [EQ|NEQ].
      { subst. rewrite IdentMap.gss in TID.
        inversion TID. simpls. }
      eapply PROM_IN_MEM1; eauto.
      rewrite IdentMap.gso in TID; auto.
      do 2 (rewrite IdentMap.gso; eauto). }
    { eapply f_to_coherent_more; [..| apply FCOH0]; eauto.
      clear -SAME_DSR. simplify_tls_events. by rewrite SAME_DSR. }
    { intros NFSC. etransitivity; [by apply SC_COV|].
      clear. simplify_tls_events. basic_solver. }
    { intros QQ l.
      eapply max_value_same_set.
      { by apply SC_REQ1. }
      apply s_tm_n_f_steps.
      { erewrite (@init_covered G T); eauto.
        clear. simplify_tls_events. basic_solver. }
      { clear. simplify_tls_events. basic_solver. }
      intros a [[H|H]|H]%COV' HH AA.
      { apply HH. clear -H. find_event_set. }
      { subst. clear -RREAD AA. type_solver. }
      subst. clear -WWRITE AA. type_solver. }
    { eapply reserved_time_more;[..| apply RESERVED_TIME1]; eauto.
      by rewrite SAME_DSR. }
    { eapply Memory.split_closed; eauto. }
    rewrite IdentMap.gss.
    eexists; eexists; eexists; splits; eauto; simpls.
    { erewrite tau_steps_step_same_instrs; eauto. }
    { ins. edestruct PROM_DISJOINT0 as [HH|]; eauto.
      do 2 (rewrite IdentMap.gso in *; eauto). }
    { eapply sim_prom_more; [..| apply SIM_PROM1]; eauto.
      by rewrite SAME_DSR. }
    { eapply sim_res_prom_more; [..| apply SIM_RES_PROM]; eauto.
      by rewrite SAME_DSR. }
    (* { clear WREPR REPR. rewrite <- FF, <- RORD, <- WORD. *)
    (*   apply SIM_MEM1. } *)
    { clear WREPR REPR. rewrite <- FF, <- RORD, <- WORD.
      eapply sim_mem_more; [..| apply SIM_MEM1]; eauto.
      by rewrite SAME_DSR. }
    { clear WREPR REPR. rewrite <- FF, <- RORD, <- WORD.
      eapply sim_res_mem_more; [..| apply SIM_RES_MEM0]; eauto.
      by rewrite SAME_DSR. }
    { rewrite COV'. 
      eapply sim_tview_write_step; eauto.
      1,2: by apply CON.
      3: rewrite <- FF'; eapply sim_tview_read_step; eauto. 
      (* { apply set_subset_union_l; split. *)
      (*   all: intros x H. *)
      (*   { apply TCCOH in H; apply H. } *)
      (*     by desf. } *)
      { rewrite coveredE; eauto. generalize RACT. clear. basic_solver. }
      6: { red. ins. eapply NEXT. red. eauto. }
      2,3: by apply CON.
      {
        (* TODO: move upper *)
        assert (forall A (r: relation A) (S1 S2: A -> Prop),
                    (doma r S1 \/ doma r S2) -> doma r (S1 ∪₁ S2)) as doma_union2.
        { ins. red. ins. des; [left | right]; eapply H; eauto. }
        (* TODO: move upper *)
        assert (forall A (r1 r2: relation A) (S: A -> Prop),
                    (doma r1 S /\ doma r2 S) <-> doma (r1 ∪ r2) S) as doma_union1.
        { clear. ins. unfold doma. split; ins; desc.
          { destruct REL; [eapply H| eapply H0]; eauto. }
          split; ins; eapply H; basic_solver. }
        apply doma_union2. left.
        rewrite id_union, seq_union_r. apply doma_union1. split; apply doma_alt.
        { eapply dom_sb_covered; eauto. }
        apply NEXT. }
      { eapply sim_tview_f_issued; [..| apply SIM_TVIEW]; eauto.
        ins. apply ISSEQ_TO. clear -ISS0. find_event_set. }
      { intros y [COVY TIDY].
        edestruct same_thread with (x:=r) (y:=y) as [[|SB]|SB]; eauto.
        { eapply coveredE with (T := T); eauto. }
        { exfalso. apply RNCOV. by subst. }
        exfalso. apply RNCOV.        
        eapply dom_sb_covered; eauto. clear -COVY SB. basic_solver 10. }
      { rewrite ISSEQ_TO; eauto. }
      { eapply sim_mem_helper_f_issued; eauto. }
      { intros [HH|HH]. 
        { by apply WNCOV. }
        clear -HH RREAD WWRITE.
        type_solver. }
      { intros y [[COVY|XX] TIDY].
        2: { subst. apply rmw_in_sb; auto. }
        eapply sb_trans.
        2: { apply rmw_in_sb; eauto. }
        edestruct same_thread with (x:=r) (y:=y) as [[SS|SB]|SB]; eauto.
        { eapply coveredE with (T := T); eauto. }
        { by rewrite TIDY. }
        { by subst. }
        exfalso. apply RNCOV.
        eapply dom_sb_covered; eauto. clear -COVY SB. basic_solver 10. }
      { intros y z HH. apply seq_eqv_r in HH. destruct HH as [SB HH].
        rewrite <- HH in *. clear z HH.
        destruct (classic (y = r)) as [|NEQ].
        { by right. }
        edestruct sb_semi_total_r with (x:=w) (y:=y) (z:=r) as [AA|AA]; eauto.
        { left. apply NEXT. eexists. apply seq_eqv_r. eauto. }
        exfalso. eapply WF.(wf_rmwi); eauto. }
      { erewrite Memory.split_o; eauto. eby rewrite loc_ts_eq_dec_eq. }
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
    { assert (Memory.closed_timemap (TimeMap.singleton locr (f_to' w)) memory_split) as AA.
      { unfold TimeMap.singleton, LocFun.add; red; ins.
        destruct (Loc.eq_dec loc locr); subst; eauto.
        erewrite Memory.split_o; eauto. rewrite loc_ts_eq_dec_eq. eauto. }
      assert (Memory.closed_timemap (TimeMap.singleton locr (f_from' w)) memory_split) as BB.
      { unfold TimeMap.singleton, LocFun.add; red; ins.
        destruct (Loc.eq_dec loc locr); subst; eauto.
        rewrite <- FF'.
        erewrite Memory.split_o; eauto.
        rewrite loc_ts_eq_dec_neq; auto.
        rewrite loc_ts_eq_dec_neq; auto.
        rewrite ISSEQ_TO; eauto. }
      assert (forall tmap,
                 Memory.closed_timemap tmap (Configuration.memory PC) ->
                 Memory.closed_timemap tmap memory_split) as HH.
      { intros tmap HH. red. ins.
        specialize (HH loc). desc.
        exists from, val, released.
        erewrite Memory.split_o; eauto.
        destruct (classic (loc = locr)) as [|]; subst; auto.
        2: { do 2 (rewrite loc_ts_eq_dec_neq; auto). }
        destruct (classic (tmap locr = f_to' w)) as [EQ|]; subst; auto.
        2: { rewrite loc_ts_eq_dec_neq; auto.
             destruct (classic (tmap locr = f_to' wnext)) as [EQ|]; subst; auto.
             2: by rewrite loc_ts_eq_dec_neq; auto.
             rewrite EQ in *. exfalso.
             unfold f_to' in HH. rewrite upds in HH.
             rewrite W_INMEM in HH. inv HH. }
        rewrite EQ in *. rewrite loc_ts_eq_dec_eq. exfalso.
        edestruct Memory.split_get0 with (mem2:=memory_split) as [QQ _]; eauto.
        unfold f_to' in HH. rewrite QQ in HH. inv HH. }
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
    { by rewrite COV'. }
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
  eapply simrel_thread_local_step with (thread:=tid w) (PC:=PC) (T:=T); eauto.
  11: { simpls. eapply msg_preserved_split; eauto. }
  10: { simpls. eapply closedness_preserved_split; eauto. }
  9: by eapply same_other_threads_steps; eauto.
  all: simpls; eauto.
  { clear -WACT WWRITE TLSCOH WF RMW. simplify_tls_events.
    apply wf_rmwE, seq_eqv_l, proj1 in RMW; eauto.
    generalize RMW WACT. erewrite coveredE; eauto. basic_solver 10. }
  { clear -WACT WF TLSCOH. simplify_tls_events. 
    rewrite issuedE; eauto. generalize WACT. clear. basic_solver. }
  1-5: clear; simplify_tls_events; basic_solver.
  { rewrite dom_sb_S_rfrmw_same_tid; auto. clear.
    simplify_tls_events. basic_solver. }
  { ins.
    etransitivity; [|by symmetry; apply IdentMap.Facts.add_in_iff].
    split.
    { ins; eauto. }
    intros [|HH]; subst; auto.
    apply SIMREL_THREAD; auto.
    split; auto. now apply WF. }
  { apply IdentMap.Facts.add_in_iff in TP. destruct TP as [HH|]; auto; subst.
    clear -TNEQ. desf. }
  { eapply sim_prom_f_issued; [..| apply SIM_PROM2]; eauto.
    { ins. apply ISSEQ_TO. clear -ISS0. find_event_set. }
    ins. apply ISSEQ_FROM. clear -ISS0. find_event_set. }
  { red. ins. apply SIM_RPROM0 in RES. desc.
    assert (b <> w) as NBW.
    { intros HH; subst. clear -TNEQ. desf. }
    exists b. splits; auto.
    { rewrite REQ_FROM; auto. clear -RES. find_event_set. }
    unfold f_to'. rewrite updo.
    2: { intros HH; subst. clear -TNEQ TWNEXTEQ. desf. }
    rewrite updo; auto. }
  { eapply sim_mem_f_issued; [..| apply SIM_MEM2]; eauto.
    { ins. apply ISSEQ_TO. clear -ISS0. find_event_set. }
    ins. apply ISSEQ_FROM. clear -ISS0. find_event_set. }
  { ins.
    assert (b <> w) as BNW.
    { intros HH. subst. clear -TNEQ. desf. }
    unfold f_to'. rewrite updo.
    2: { intros HH; subst. clear -RESB NRESNEXT. desf. }
    rewrite updo; auto.
    rewrite REQ_FROM; auto.
    { apply SIM_RES_MEM1; auto. }
    clear -RESB. find_event_set. }
  eapply sim_tview_f_issued; [..| apply SIM_TVIEW2]; eauto.
  ins. apply ISSEQ_TO. clear -ISS0. find_event_set.
Unshelve.
apply state.
Qed.

End IssueReservedRelNextPlainStep.
