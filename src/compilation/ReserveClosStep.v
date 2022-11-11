Require Import Lia.
Require Import PromisingLib.
From Promising2 Require Import TView View Time Event Cell Thread Memory Configuration Local.
From imm Require Import Prog.
From imm Require Import ProgToExecution.
From imm Require Import Events.
From imm Require Import Execution.
From imm Require Import imm_s.
From imm Require Import imm_s_ppo.
From imm Require Import CombRelations.
From imm Require Import ProgToExecutionProperties.
From imm Require Import RMWinstrProps.
From imm Require Import AuxRel2.
From imm Require Import FairExecution.
From imm Require Import FinExecution.
From imm Require Import FinThreads.
From imm Require Import ReserveClos.

Require Import SimulationRel.
Require Import PlainStepBasic.
Require Import SimulationPlainStep.
Require Import MaxValue.
Require Import SimState.
Require Import Event_imm_promise.
Require Import PromiseOutcome.
Require Import CertGraphInit.
Require Import MemoryAux.
Require Import PromiseLTS.
Require Import ExtSimTraversal.
Require Import ExtSimTraversalProperties.
Require Import ExtTraversalConfig.
Require Import ExtTraversalProperties.
Require Import ExtTraversal.
Require Import ExtTraversalCounting.
Require Import SimulationPlainStepAux.
Require Import FtoCoherent.
Require Import AuxTime.
Require Import IndefiniteDescription.
From imm Require Import ImmFair. 
Require Import Coq.Program.Basics.
Require Import FinTravConfigs.
Require Import ChoiceFacts.
From imm Require Import AuxRel. 
Require Import ImmProperties. 
From hahn Require Import Hahn.

From imm Require Import SimTraversal.
From imm Require Import SimTraversalProperties.
(* From imm Require Import SimTravClosure. *)
From imm Require Import TraversalConfigAlt.
From imm Require Import SetSize.
From imm Require Import SimClosure.

From imm Require Import TLSCoherency.
From imm Require Import IordCoherency. 
From imm Require Import TlsEventSets.
From imm Require Import AuxDef.
From imm Require Import TraversalOrder.
From imm Require Import TlsAux2.
From imm Require Import SimIordTraversal.
From imm Require Import EventsTraversalOrder.

Set Implicit Arguments.

Section ReserveClos.

Variable G : execution.
Variable sc : relation actid.
Hypothesis WF : Wf G.
Hypothesis WFSC : wf_sc G sc.
Notation "'E'" := (acts_set G).
Notation "'W'" := (fun x => is_true (is_w (lab G) x)).

Lemma reserve_clos_tls_coherent tc
  (COH : tls_coherent G tc) :
  tls_coherent G (reserve_clos tc).
Proof using WF.
  unfold reserve_clos.
  apply tls_coherent_ext_union; auto.
  unfold exec_tls.
  arewrite (issued tc ≡₁ issued tc ∩₁ (is_init ∪₁ set_compl is_init)).
  { now rewrite <- set_full_split, set_inter_full_r. }
  rewrite issued_EW; eauto.
  rewrite !set_inter_union_r, set_pair_union_r.
  unionL.
  { transitivity (init_tls G); eauto with hahn.
    unfold init_tls. apply set_pair_mori; eauto with hahn.
    clear. basic_solver. }
  unionR right -> right.
  apply set_pair_mori; eauto with hahn.
  clear. basic_solver.
Qed.

Lemma reserve_clos_iord_coherent tc
  (ICOH : iord_coherent G sc tc) :
  iord_coherent G sc (reserve_clos tc).
Proof using.
  unfold reserve_clos.
  red. rewrite id_union, seq_union_r, dom_union.
  unionL.
  { now unionR left. }
  transitivity (@set_empty trav_label).
  2: clear; basic_solver.
  rewrite iord_no_reserve.
  unfold set_pair.
  unfolder. ins. do 2 desf.
Qed.

(* TODO: move *)
Lemma dom_sb_S_rfrmw_eq_reserved_issued r s tc
  (W_EX_IS_XACQ : W_ex G ⊆₁ W_ex G ∩₁ is_xacq (lab G))
  (TCOH : tls_coherent G tc)
  (ICOH : iord_coherent G sc tc)
  (RESEMPTC : reserved tc ≡₁ issued tc) :
  dom_sb_S_rfrmw G tc r s ⊆₁ issued tc.
Proof using WF.
  unfold dom_sb_S_rfrmw.
  rewrite RESEMPTC.
  transitivity (dom_rel (⦗W_ex G⦘ ⨾ sb G ⨾ ⦗issued tc⦘)).
  2: { rewrite W_EX_IS_XACQ.
       eapply dom_wex_sb_issued; eauto. }
  rewrite rmw_W_ex.
  clear. basic_solver.
Qed.

(* TODO: move to coq-imm/ReserveClos.v *)
Lemma dom_sb_S_rfrmw_reserve_clos r s tc
  (W_EX_IS_XACQ : W_ex G ⊆₁ W_ex G ∩₁ is_xacq (lab G))
  (TCOH : tls_coherent G tc)
  (ICOH : iord_coherent G sc tc)
  (RESEMPTC : reserved tc ≡₁ ∅) :
  dom_sb_S_rfrmw G (reserve_clos tc) r s ⊆₁ issued tc.
Proof using WF.
  etransitivity.
  apply dom_sb_S_rfrmw_eq_reserved_issued; eauto.
  all: try now rewrite issued_reserve_clos.
  { now apply reserve_clos_tls_coherent. }
  { now apply reserve_clos_iord_coherent. }
  unfold reserve_clos. rewrite reserved_union.
  rewrite RESEMPTC. rewrite set_union_empty_l.
  rewrite reserved_ta_reserve.
  rewrite issued_union. rewrite issued_ta_reserve.
  now rewrite set_union_empty_r.
Qed.

Local
Hint Rewrite issued_union reserved_union covered_union
  issued_ta_reserve reserved_ta_reserve covered_ta_reserve : tc_simpl.

Lemma reserve_clos_reserve_coherent tc
  (W_EX_IS_XACQ : W_ex G ⊆₁ W_ex G ∩₁ is_xacq (lab G))
  (IMMCONS : imm_consistent G sc)
  (TCOH : tls_coherent G tc)
  (ICOH : iord_coherent G sc tc)
  (NORES : reserved tc ≡₁ ∅) :
  reserve_coherent G (reserve_clos tc).
Proof using WF WFSC.
  assert (dom_rel (iord_simpl G sc ⨾ ⦗tc⦘) ⊆₁ tc) as ACOH.
  { apply iord_coh_implies_iord_simpl_coh; auto. }
  assert (⦗issued tc⦘ ⊆ ⦗W⦘ ;; ⦗issued tc⦘) as ISSW.
  { generalize (issuedW WF TCOH). clear. basic_solver. }
  unfold reserve_clos.
  constructor; unfold dom_sb_S_rfrmw; autorewrite with tc_simpl.
  all: repeat rewrite NORES.
  all: repeat rewrite set_union_empty_l.
  all: repeat rewrite set_union_empty_r.
  { now apply issuedE. }
  { eauto with hahn. }
  { unfolder. ins. desf. }
  { rewrite ISSW. 
    rewrite <- !seqA.
    match goal with
    | |- dom_rel (?r ;; ⦗ _ ⦘) ⊆₁ _ => arewrite (r ⊆ imm_bob.fwbob G)
    end.
    eapply fwbob_I_in_C; eauto. }
  { eapply dom_detour_rmwrfi_rfe_acq_sb_issued; eauto. }
  5: { unfolder. intros w [ISS [r RMW]].
       apply (dom_l (wf_rmwD WF)) in RMW. apply seq_eqv_l in RMW. destruct RMW as [RR RMW].
       apply (dom_l (wf_rmwE WF)) in RMW. apply seq_eqv_l in RMW. destruct RMW as [RE RMW].
       assert (codom_rel (rf G) r) as [w' RF].
       { apply IMMCONS. split; auto. }
       exists w'. splits; eauto.
       eapply rfrmw_I_in_I; eauto.
       basic_solver 10. }
  2: { unfolder. intros x [[w [SB WISS]] [y [YISS [z AA]]]].
       destruct AA as [RF [p [[QQ UU] PP]]]; subst.
       eapply dom_wex_sb_issued; eauto.
       assert (W_ex G x) as WEXX.
       { eexists; eauto. }
       unfolder. do 2 eexists. splits; eauto.
       now eapply W_EX_IS_XACQ. }
  all: rewrite <- !seqA.
  all: match goal with
       | |- dom_rel (?r ;; ⦗ issued _ ⦘) ⊆₁ issued _ =>
           rewrite ISSW;
           arewrite (r ⨾ ⦗W⦘ ⊆ ⦗W⦘ ⨾ (ar G sc)⁺); eauto using ar_ct_I_in_I
       end.
  { rewrite <- w_ex_acq_sb_w_in_ar, <- ct_step.
    generalize (W_ex_in_W WF). clear. basic_solver. }
  { rewrite (dom_l (wf_detourD WF)), (dom_l (wf_rfeD WF)).
    rewrite <- seq_union_r.
    hahn_frame.
    rewrite (dom_r (wf_detourD WF)), (dom_r (wf_rfeD WF)).
    rewrite <- !seq_union_l.
    hahn_frame.
    sin_rewrite data_rfi_rmw_rppo_in_ppo.
    arewrite_id ⦗W⦘. rewrite seq_id_r.
    rewrite detour_in_ar, rfe_in_ar, ppo_in_ar at 1.
    rewrite <- ct_unit, <- ct_step.
    apply seq_mori; eauto with hahn. }
  arewrite_id ⦗W⦘ at 1. rewrite seq_id_r.
  rewrite (dom_l (wf_detourD WF)).
  rewrite detour_in_ar, rmw_in_ar_int; auto.
  rewrite <- ct_unit, <- ct_step.
  hahn_frame; eauto with hahn.
Qed.

End ReserveClos.
  
Section ReserveClosSteps.

Variable prog : Prog.t.
Hypothesis TNONULL : ~ IdentMap.In tid_init prog.

Variable G : execution.
Variable final_memory : location -> value.

Hypothesis ALLRLX  : (acts_set G) \₁ is_init ⊆₁ (fun a => is_true (is_rlx (lab G) a)).
Hypothesis FRELACQ : (acts_set G) ∩₁ (fun a => is_true (is_f (lab G) a)) ⊆₁ (fun a => is_true (is_ra (lab G) a)).

Hypothesis PROG_EX : program_execution prog G.
Hypothesis RMWREX  : forall thread linstr
                            (IN : Some linstr = IdentMap.find thread prog),
    rmw_is_rex_instrs linstr.
Hypothesis WF : Wf G.
Variable sc : relation actid.
Hypothesis WFSC : wf_sc G sc.
Hypothesis IMMCON : imm_consistent G sc.

(* TODO: doesn't it follow from PROG_EX? *)
Hypothesis FIN_THREADS : fin_threads G.
Hypothesis GTHREADSPROG : forall t (IN : (threads_set G \₁ eq tid_init) t), IdentMap.In t prog.
Hypothesis THREADS_EXACT : forall t, threads_set G t <-> exists e, << ET : acts_set G e >> /\
                                                                   << TT : t = tid e >>.
Hypothesis EVENTS_NINIT : forall e (IN : acts_set G e) (TINIT : tid e = tid_init),
    is_init e.

Hypothesis w_ex_is_xacq : W_ex G ⊆₁ W_ex G ∩₁ is_xacq (lab G).

(* TODO: move *)
Definition ta_label2thread (a : trav_label) : thread_id :=
  match a with
  | (ta_propagate t, _) => t
  | (_, e) => tid e
  end.

#[local]
Hint Rewrite issued_eq_ta_cover issued_eq_ta_reserve issued_singleton
             covered_eq_ta_issue covered_eq_ta_reserve covered_singleton
             reserved_eq_ta_issue reserved_eq_ta_cover reserved_singleton
             covered_union issued_union reserved_union
             set_pair_empty_l set_pair_empty_r
             set_union_empty_l set_union_empty_r
             reserve_clos_eq_ta_cover reserve_clos_eq_ta_issue reserve_clos_eq_ta_reserve
             : cir_simplify.

(* TODO: move *)
Lemma reserve_coherent_ext_reserve tc tc' r w
  (RCRCOHTC1 : reserve_coherent G (reserve_clos tc))
  (RESEMPTC1 : reserved tc ≡₁ ∅)
  (EW : acts_set G w)
  (RMW : rmw G r w)
  (TCOH : tls_coherent G tc')
  (ISS' : issued tc' ≡₁ issued tc ∪₁ eq w)
  (IORD' : iord_coherent G sc tc')
  (RCOH' : reserve_coherent G (reserve_clos tc'))
  (DOMFRA : dom_rel (⦗is_f (lab G) ∩₁ is_ra (lab G)⦘ ⨾ sb G ⨾ ⦗eq w⦘) ⊆₁ covered tc)
  : reserve_coherent G (reserve_clos tc ∪₁ eq (ta_reserve, w)).
Proof using w_ex_is_xacq WFSC WF IMMCON.
  assert (COMP : complete G) by apply IMMCON.
  assert (WEX : W_ex G w) by (now exists r).
  assert (WW : is_w (lab G) w).
  { now apply W_ex_in_W. }
  assert (⦗eq w⦘ ⊆ ⦗is_w (lab G)⦘ ;; ⦗eq w⦘) as AW.
  { generalize WW. clear. basic_solver 10. }
  assert (dom_rel (⦗is_w (lab G)⦘ ⨾ (ar G sc ∪ rf G ⨾ ppo G ∩ same_loc (lab G))⁺ ⨾ ⦗eq w⦘) ⊆₁
            issued tc ∪₁ eq w) as IAW.
  { arewrite (eq w ⊆₁ issued tc ∪₁ eq w) at 1.
    rewrite <- ISS'. eapply ar_rf_ppo_loc_ct_I_in_I; auto. }
  assert (issued tc' w) as ISSW.
  { apply ISS'. by right. }
  constructor; autorewrite with cir_simplify; auto.
  { apply set_subset_union_l; split; try now apply RCRCOHTC1.
    now apply set_subset_single_l. }
  { unionR left. now apply RCRCOHTC1. }
  { rewrite set_minus_union_l.
    unionL; try now apply RCRCOHTC1.
    generalize WEX. clear. basic_solver 10. }
  all: try (rewrite id_union, !seq_union_r, dom_union;
            apply set_subset_union_l; split; [now apply RCRCOHTC1| ];
            rewrite ?issued_reserve_clos, ?covered_reserve_clos).
  { auto. }
  6: { rewrite set_inter_union_l.
       apply set_subset_union_l; split; try now apply RCRCOHTC1.
       rewrite issued_reserve_clos.
       apply (dom_l (wf_rmwD WF)) in RMW. apply seq_eqv_l in RMW. destruct RMW as [RR RMW].
       apply (dom_l (wf_rmwE WF)) in RMW. apply seq_eqv_l in RMW. destruct RMW as [ER RMW].
       set (AA:=COMP). edestruct AA as [q RF].
       { split; eauto. }
       intros x [BB _]; subst. exists q.
       unfolder. split; eauto.
       enough (issued tc' q) as BB.
       { apply ISS' in BB. destruct BB as [BB|BB]; auto; subst.
         exfalso. eapply wf_rfrmw_irr; eauto. eexists; eauto. }
       eapply rfrmw_I_in_I; eauto. exists x. unfolder. eexists. splits; eauto. }
  3: { unionR left. 
       rewrite dom_sb_S_rfrmw_union_P.
       unionL; try now apply RCRCOHTC1.
       unfold dom_sb_S_rfrmw. autorewrite with cir_simplify.
       rewrite issued_reserve_clos, reserved_reserve_clos.
       rewrite RESEMPTC1. rewrite set_union_empty_l.
       transitivity (dom_rel (<|W_ex G|> ;; sb G ⨾ ⦗eq w⦘)).
       { clear. rewrite rmw_W_ex. basic_solver 10. }
       rewrite <- !seqA. apply dom_rel_irr_seq_eq_no_eq.
       { arewrite_id ⦗W_ex G⦘. rewrite seq_id_l. apply sb_irr. }
       arewrite (eq w ⊆₁ issued tc ∪₁ eq w) at 1.
       rewrite <- ISS'. rewrite w_ex_is_xacq. eapply dom_wex_sb_issued; eauto. }
  { rewrite <- !seqA. apply dom_rel_irr_seq_eq_no_eq.
    2: { arewrite (eq w ⊆₁ issued tc ∪₁ eq w) at 1.
         rewrite <- ISS'.
         arewrite (issued tc' ⊆₁ reserved (reserve_clos tc')) at 1.
         { unfold reserve_clos. rewrite reserved_union.
           rewrite reserved_ta_reserve. eauto with hahn. }
         etransitivity.
         { apply rcoh_dr_R_acq_I; auto. }
         apply issued_reserve_clos. }
    arewrite_id ⦗(fun x : actid => is_r (lab G) x) ∩₁ (fun x : actid => is_acq (lab G) x)⦘.
    rewrite seq_id_l.
    rewrite rfi_in_sb, rmw_in_sb, detour_in_sb, sb_sb; auto.
    rewrite (rt_of_trans (@sb_trans G)).
    rewrite (rewrite_trans_seq_cr_l (@sb_trans G)).
    rewrite seq_union_l, sb_sb.
    apply irreflexive_union. split; [now apply sb_irr|].
    assert (imm_s_hb.coherence G) as AA by apply IMMCON.
    apply irreflexive_seqC.
    rewrite imm_s_hb.sb_in_hb, Execution_eco.rfe_in_eco.
    eapply irreflexive_mori; try by apply AA.
    red. eauto with hahn. }
  all: rewrite AW.
  all: rewrite <- !seqA.
  all: match goal with
       | |- dom_rel (?r ;; <| _ |>) ⊆₁ _ =>
           arewrite (r ⊆ <|is_w (lab G)|> ;; (ar G sc ∪ rf G ⨾ ppo G ∩ same_loc (lab G))⁺);
           [ | rewrite <- !seqA; apply dom_rel_irr_seq_eq_no_eq]
       end. 
  all: try now (rewrite inclusion_eqv_rel_true, seq_id_l;
                apply imm_s_rfppo.ar_rf_ppo_loc_acyclic; auto).
  all: try rewrite !seqA.
  all: auto.
  { arewrite (⦗W_ex G ∩₁ (fun a0 : actid => is_xacq (lab G) a0)⦘ ⊆
                <|is_w (lab G)|> ;; ⦗W_ex G ∩₁ (fun a0 : actid => is_xacq (lab G) a0)⦘).
    { generalize (W_ex_in_W WF). clear. basic_solver 10. }
    rewrite w_ex_acq_sb_w_in_ar. hahn_frame_l.
    rewrite <- ct_step. eauto with hahn. }
  all: arewrite_id ⦗fun a0 : actid => is_w (lab G) a0⦘ at 1; rewrite seq_id_r.
  { rewrite (dom_l (wf_detourD WF)), (dom_l (wf_rfeD WF)).
    rewrite <- seq_union_r. hahn_frame_l.
    rewrite detour_rfe_data_rfi_rmw_rppo_in_detour_rfe_ppo; auto.
    rewrite detour_in_ar, rfe_in_ar.
    rewrite ppo_in_ar at 1.
    rewrite <- ct_ct. rewrite <- !ct_step.
    eauto with hahn. }
  rewrite (dom_l (wf_detourD WF)). hahn_frame_l.
  rewrite detour_in_ar. rewrite rmw_in_ar_int, ar_int_in_ar; auto.
  rewrite <- ct_ct. rewrite <- !ct_step.
  eauto with hahn.
Qed.

Lemma isim_clos_step2ext_isim_trav_step tc1 tc2 thread tl
  (TCOH1 : tls_coherent  G tc1)
  (TCOH2 : tls_coherent  G tc2)
  (ICOH1 : iord_coherent G sc tc1)
  (ICOH2 : iord_coherent G sc tc2)
  (SCOH1 : sim_coherent G tc1)
  (SCOH2 : sim_coherent G tc2)
  (RESEMPTC1 : reserved tc1 ≡₁ ∅)
  (RESEMPTC2 : reserved tc2 ≡₁ ∅)
  (STEP : isim_clos_step G sc tl tc1 tc2)
  (TLTOTHREAD : match tl with
                | [] => False
                | a :: tl => thread = ta_label2thread a
                end) :
  (ext_isim_trav_step G sc thread)^* (reserve_clos tc1) (reserve_clos tc2).
Proof using w_ex_is_xacq WFSC WF IMMCON FRELACQ.
  assert (COMP : complete G) by apply IMMCON.
  assert (tls_coherent G (reserve_clos tc1)) as TLSCOHTC1.
  { apply reserve_clos_tls_coherent; auto. }
  assert (iord_coherent G sc (reserve_clos tc1)) as ICOHTC1.
  { apply reserve_clos_iord_coherent; auto. }
  assert (iord_coherent G sc (reserve_clos tc2)) as RCICOHTC2.
  { apply reserve_clos_iord_coherent; auto. }
  assert (reserve_coherent G (reserve_clos tc1)) as RCRCOHTC1.
  { eapply reserve_clos_reserve_coherent; eauto. }
  assert (reserve_coherent G (reserve_clos tc2)) as RCRCOHTC2.
  { eapply reserve_clos_reserve_coherent; eauto. }

  assert (tls_coherent G (reserve_clos tc2)) as TLSCOHN.
  { apply reserve_clos_tls_coherent; auto. }

  red in STEP; desf; subst; ins.
  { do 2 red in STEP. desf.
    apply seq_eqv_l in STEP. destruct STEP as [STEPA STEPRES].
    ins. apply rt_step.
    assert (reserve_clos tc2 ≡₁ reserve_clos tc1 ∪₁ eq (ta_cover, a)) as TC2ALT.
    { rewrite STEPRES. rewrite reserve_clos_union.
      apply set_union_more; try easy.
      unfold reserve_clos.
      split.
      2: { clear. eauto with hahn. }
      arewrite (issued (eq (ta_cover, a)) ⊆₁ ∅).
      { unfold issued. basic_solver 10. }
      unfold set_pair. clear. unfolder. ins. do 2 desf. }
    assert (acts_set G a) as EA.
    { rewrite STEPRES in TCOH2. 
      eapply coveredE; auto.
      { apply TCOH2. }
      apply covered_union. right.
      now apply covered_singleton. }
    assert (~ covered tc1 a) as NCOVA.
    { unfold covered. clear -STEPA.
      intros HH. apply STEPA. unfolder in HH. desf. destruct y; ins. desf. }
    assert ((acts_set G \₁ is_init) a) as ENINIT.
    { split; auto.
      intros HH. apply NCOVA.
      eapply init_covered; eauto.
      split; auto. }
    assert (~ reserve_clos tc1 (mkTL ta_cover a)) as NRCLS.
    { unfold reserve_clos. intros [QQ|QQ]; auto.
      red in QQ. do 2 desf. }
    assert (reserve_clos tc2 ≡₁
            reserve_clos tc1 ∪₁ eq (mkTL ta_cover a)
            ∪₁ eq ta_reserve <*> ∅) as ALT.
    { rewrite TC2ALT.
      rewrite set_pair_empty_l.
      now rewrite set_union_empty_r. }
    destruct (lab G a) eqn:HH;
      [apply ext_read_trav_step |
       apply ext_rlx_write_cover_step |
       apply ext_fence_trav_step ].
    all: try now (unfold is_r, is_w, is_f; rewrite HH; type_solver).
    all: try now constructor; auto; ins.
    { eapply sim_clos_cover_no_dom_rmw with (tc:=tc1); eauto.
      red. rewrite <- STEPRES. apply SCOH2. }
    { eapply sim_clos_cover_no_rel with (tc:=tc1) (tc':=tc2); eauto.
      { clear -HH. type_solver. }
      all: rewrite STEPRES.
      { now rewrite covered_union, covered_singleton. }
      rewrite issued_union, issued_eq_ta_cover.
      clear. basic_solver 10. }
    { eapply sim_clos_cover_no_codom_rmw with (tc:=tc1) (tc':=tc2); eauto.
      rewrite STEPRES. now rewrite covered_union, covered_singleton. }
    apply issued_union. left.
    assert (issued tc2 ⊆₁ issued tc1) as ISS.
    { rewrite STEPRES. rewrite issued_union.
      arewrite (issued (eq (ta_cover, a)) ⊆₁ ∅).
      all: unfold issued; clear; basic_solver. }
    apply ISS. eapply w_covered_issued; eauto.
    split.
    { clear -HH. type_solver. }
    unfold covered. generalize STEPRES. clear. basic_solver 10. }
  { rename a0 into w.
    destruct STEP as (RMW & tc' & STEP1 & STEP2).
    destruct STEP1 as [STEPA1 STEPRES1].
    apply seq_eqv_l in STEPA1. destruct STEPA1 as [NCOVTC1 TC'ALT].
    destruct STEP2 as [STEPA2 STEPRES2].
    apply seq_eqv_l in STEPA2. destruct STEPA2 as [NCOVTC' TC2ALT].
    rewrite TC'ALT in TC2ALT.
    desf.
    apply rt_step.
    assert (is_r (lab G) a /\ is_w (lab G) w) as (RR & WW).
    { apply wf_rmwD in RMW; auto. generalize RMW. clear. basic_solver. }
    assert (~ reserve_clos tc' (mkTL ta_cover w)) as NRESCLOSW.
    { intros [AA|AA]; auto.
      clear -AA. red in AA. do 2 desf. }
    assert (covered tc2 a) as COVA.
    { apply set_subset_single_l. rewrite TC2ALT.
      rewrite !covered_union, covered_singleton. eauto with hahn. }
    assert (covered (reserve_clos tc2) a) as COVCLOSA.
    { unfold reserve_clos. apply covered_union. now left. }
    assert (acts_set G a) as EA.
    { eapply coveredE; eauto. }
    assert (~ is_init a) as NINIT.
    { intros HH. apply NCOVTC1.
      enough (covered tc1 a) as AA.
      { red in AA. unfolder in AA. desf. destruct y; ins. desf. }
      eapply init_covered; eauto. split; auto. }
    assert (tls_coherent G tc') as TLSCOHTC'.
    { rewrite TC'ALT. apply tls_coherent_ext; auto.
      red. left. red. split.
      { basic_solver. }
      now split. }
    assert (reserved tc' ≡₁ ∅) as RESEMPTC'.
    { rewrite TC'ALT. rewrite reserved_union, RESEMPTC1.
      rewrite reserved_eq_ta_cover. clear. basic_solver. }
    assert (~ covered tc1 w) as NCOVW.
    { intros HH. apply NCOVTC'. apply TC'ALT. left. 
      red in HH. unfolder in HH. desf. destruct y; ins. desf. }
    assert (~ is_rel (lab G) w) as NORELW.
    { eapply sim_clos_cover_no_rel with (tc:=tc1) (tc':=tc2); eauto.
      all: rewrite TC2ALT.
      { rewrite !covered_union, !covered_singleton.
        clear. basic_solver 10. }
      rewrite !issued_union, !issued_eq_ta_cover.
      clear. basic_solver 10. }
    assert (issued (reserve_clos tc1) w) as ISSW.
    { apply issued_union. left.
      assert (issued tc2 ⊆₁ issued tc1) as ISS.
      { rewrite TC2ALT. rewrite !issued_union.
        arewrite (issued (eq (ta_cover, a)) ⊆₁ ∅).
        2: arewrite (issued (eq (ta_cover, w)) ⊆₁ ∅).
        all: unfold issued; clear; basic_solver. }
      apply ISS. eapply w_covered_issued; eauto.
      split; auto.
      unfold covered. generalize TC2ALT. clear. basic_solver 10. }
    eapply ext_rlx_rmw_cover_step with (T':=reserve_clos tc'); eauto.
    2: { constructor; auto; ins.
         rewrite TC2ALT, TC'ALT.
         rewrite !reserve_clos_union.
         rewrite set_pair_empty_l, set_union_empty_r.
         now rewrite !reserve_clos_eq_ta_cover. }
    constructor; auto; ins.
    { apply reserve_clos_tls_coherent; auto. }
    { now apply reserve_clos_iord_coherent. }
    { eapply reserve_clos_reserve_coherent; eauto. }
    { intros [AA|AA]; auto. generalize AA. unfold set_pair. clear. basic_solver. }
    rewrite set_pair_empty_l, set_union_empty_r.
    rewrite TC'ALT, reserve_clos_union.
    now rewrite reserve_clos_eq_ta_cover. }
  { destruct STEP as (AA & tc' & STEP1 & STEP2).
    destruct AA as (RMW & AA & REL); subst.
    destruct STEP2 as (tc'' & STEP2 & STEP3).
    destruct STEP1 as [STEPA1 STEPRES1].
    apply seq_eqv_l in STEPA1. destruct STEPA1 as [NCOVTC1 TC'ALT].
    destruct STEP2 as [STEPA2 STEPRES2].
    apply seq_eqv_l in STEPA2. destruct STEPA2 as [NCOVTC' TC''ALT].
    destruct STEP3 as [STEPA3 STEPRES3].
    apply seq_eqv_l in STEPA3. destruct STEPA3 as [NCOVTC'' TC2ALT].
    desf.
    rename a1 into w.
    rename a into r.
    rewrite TC'ALT in TC''ALT.
    rewrite TC''ALT in TC2ALT.

    assert (~ covered tc1 r) as NCOVR.
    { intros HH. apply NCOVTC1. red in HH. unfolder in HH. do 2 desf. destruct y; ins; desf. }
    assert (~ issued tc1 w) as NISS.
    { intros AA.
      assert (covered tc1 w) as BB.
      { apply set_subset_single_l. red in SCOH1. rewrite SCOH1.
        unfold sim_clos. rewrite covered_union. unionR right.
        rewrite covered_rel_clos.
        generalize REL AA. clear. basic_solver. }
      apply NCOVR.
      eapply dom_sb_covered; eauto. exists w.
      apply seq_eqv_r. split; auto. apply rmw_in_sb; auto. }
    assert (~ issued (reserve_clos tc1) w) as NISSRS.
    { intros HH. apply NISS. now apply issued_reserve_clos. }
    assert (issued tc2 ≡₁ issued tc1 ∪₁ eq w) as YY.
    { rewrite TC2ALT. now autorewrite with cir_simplify. }
    assert (covered tc2 ≡₁ covered tc1 ∪₁ eq r ∪₁ eq w) as YYC.
    { rewrite TC2ALT. now autorewrite with cir_simplify. }
    assert (reserved tc' ≡₁ ∅) as RESEMPTC'.
    { rewrite TC'ALT. now autorewrite with cir_simplify. }
    assert (reserved tc'' ≡₁ ∅) as RESEMPTC''.
    { rewrite TC''ALT. now autorewrite with cir_simplify. }

    assert (issued (reserve_clos tc2) w) as ISS2A.
    { apply issued_union. left.
      apply YY. now right. }
    assert (is_r (lab G) r /\ is_w (lab G) w) as (RR & WW).
    { apply wf_rmwD in RMW; auto. generalize RMW. clear. basic_solver. }
    assert (acts_set G w) as EW.
    { eapply issuedE; eauto. }
    assert (~ is_init w) as NINIT.
    { intros INIT. apply NISS. eapply init_issued; eauto.
      split; auto. }
    assert (acts_set G r) as ER.
    { eapply coveredE; eauto. apply covered_reserve_clos.
      apply YYC. clear. basic_solver. }
    assert (~ is_init r) as NINITR.
    { intros HH. eapply init_w in HH; eauto. type_solver 10. }
    assert (~ issued (reserve_clos tc1) w) as NISSW.
    { unfold reserve_clos. intros AA. apply issued_union in AA.
      destruct AA as [AA|AA]; auto.
      eapply issued_ta_reserve; eauto. }
    assert (~ reserve_clos tc'' (mkTL ta_cover w)) as NRCTC''.
    { unfold reserve_clos. intros [AA|AA]; auto.
      clear -AA. red in AA. do 2 desf. }
    (* assert (~ reserve_clos tc' (mkTL ta_cover w)) as NRCTC'. *)
    (* { unfold reserve_clos. intros [AA|AA]; auto. *)
    (*   clear -AA. red in AA. do 2 desf. } *)
    (* assert (~ covered tc1 w) as NCOVW. *)
    (* { intros HH. apply NISS. eapply w_covered_issued; eauto. *)
    (*   split; auto. } *)
    (* TODO: make a lemma? *)
    assert (tls_coherent G tc' ) as TCOH'.
    { rewrite TC'ALT. apply tls_coherent_ext; auto.
      red. left. repeat (split; auto). }
    assert (tls_coherent G tc'') as TCOH''.
    { rewrite TC''ALT. rewrite <- TC'ALT. apply tls_coherent_ext; auto.
      red. right. split.
      { clear. basic_solver. }
      repeat (split; auto). }
    assert (exec_tls G (ta_reserve, w)) as ETLS.
    { red. right. split.
      { clear. basic_solver. }
      repeat (split; auto). }
    assert (tls_coherent G (tc' ∪₁ eq (ta_reserve, w))) as TCCOH''A.
    { apply tls_coherent_ext; auto. }
    assert (iord_coherent G sc (tc' ∪₁ eq (ta_reserve, w))) as ICOH''A.
    { eapply iord_coherent_equiv_wo_reserved with (T1:=tc'); auto.
      clear. basic_solver. }
    
    assert (~ issued (reserve_clos tc1 ∪₁ eq (ta_reserve, w)) w) as NISSTC1'.
    { intros HH. apply issued_union in HH. destruct HH as [HH|HH]; auto.
      apply issued_eq_ta_reserve in HH. apply HH. }
    
    assert (W_ex G w)  as WEXW.
    { now exists r. }
    assert (reserve_coherent G (reserve_clos tc1 ∪₁ eq (ta_reserve, w))) as RCOH1.
    { eapply reserve_coherent_ext_reserve with (tc':=tc2); eauto.
      match goal with
      | |- ?X ⊆₁ _ => assert (X ⊆₁ covered tc1 ∪₁ eq r ∪₁ eq w) as AA
      end.
      { rewrite <- YYC.
        arewrite (eq w ⊆₁ issued tc2).
        { rewrite YY. clear. basic_solver. }
        eapply dom_F_sb_I_in_C; eauto. }
      intros x HH. destruct HH as [y HH].
      assert ((covered tc1 ∪₁ eq r ∪₁ eq w) x) as [[BB | BB] | BB]; auto; subst.
      { apply AA. eexists; eauto. }
      all: exfalso.
      all: apply seq_eqv_l in HH; desf.
      all: type_solver. }
    assert (reserve_coherent G (reserve_clos (tc' ∪₁ eq (ta_reserve, w)))) as RCOHAA.
    { rewrite TC'ALT. rewrite !reserve_clos_union. autorewrite with cir_simplify.
      eapply reserve_coherent_more.
      { reflexivity. }
      2: { eapply reserve_coherent_add_cover.
           now apply RCOH1. }
      clear. basic_solver 10. }

    eapply rt_trans with (y:=reserve_clos tc1 ∪₁ eq (ta_reserve, w)).
    all: apply rt_step.
    2: { eapply ext_rel_rmw_step with (T':=reserve_clos (tc' ∪₁ eq (ta_reserve, w)))
                                      (T'':=reserve_clos tc''); eauto.
         all: constructor; auto; ins.
         all: try now apply reserve_clos_tls_coherent; auto.
         all: try now apply reserve_clos_iord_coherent; auto.
         all: try now eapply reserve_clos_reserve_coherent; eauto.
         all: try now intros [AA|AA]; eauto; red in AA; do 2 desf.
         { intros [AA|AA].
           { destruct AA as [AA|AA]; eauto; red in AA; do 2 desf. }
           inv AA. }
         { rewrite TC'ALT. rewrite !reserve_clos_union.
           autorewrite with cir_simplify.
           clear. basic_solver. }
         { unfold reserve_clos. clear. basic_solver 10. }
         2: { rewrite TC2ALT, TC''ALT.
              rewrite !reserve_clos_union.
              now autorewrite with cir_simplify. }
         rewrite TC'ALT, TC''ALT.
         rewrite !reserve_clos_union.
         autorewrite with cir_simplify.
         rewrite !set_pair_union_r, set_pair_exact.
         split.
         all: repeat (apply set_subset_union_l; split; eauto 10 with hahn).
         transitivity (eq ta_reserve <*> issued tc1).
         2: { unfold reserve_clos. eauto 10 with hahn. }
         apply set_pair_mori; eauto with hahn.
         rewrite !dom_sb_S_rfrmw_union_P.
         unionL; eauto 10 using dom_sb_S_rfrmw_reserve_clos.
         { unfold dom_sb_S_rfrmw. autorewrite with cir_simplify. clear. basic_solver 10. }
         unfold dom_sb_S_rfrmw. autorewrite with cir_simplify.
         rewrite rmw_in_sb, rfi_in_sb; auto. rewrite sb_sb.
         unfolder. ins. desf. exfalso.
         eapply (@sb_irr G). eapply sb_sb. eexists; eauto. }
    arewrite (tid r = tid w).
    { eapply wf_rmwt; eauto. }
    eapply ext_reserve_trav_step.
    constructor; auto; ins.
    { apply tls_coherent_ext; auto. }
    { eapply iord_coherent_equiv_wo_reserved with (T1:=reserve_clos tc1); auto.
      clear. basic_solver. }
    { intros [AA|AA]; eauto.
      { eapply  RESEMPTC1. red. unfolder. exists (ta_reserve, w). eauto. }
      destruct AA as [_ BB]; auto. }
    now autorewrite with cir_simplify. }
  { destruct STEP as [STEPA [IA IB]].
    apply seq_eqv_l in STEPA. destruct STEPA as [NCOVTC1 TCALT].
    assert (issued tc2 ≡₁ issued tc1 ∪₁ eq a) as YY.
    { rewrite TCALT. now rewrite issued_union, issued_singleton. }
    assert (covered tc2 ≡₁ covered tc1) as YYC.
    { rewrite TCALT. rewrite covered_union. clear. unfold covered.
      clear. basic_solver 10. }
    assert (issued (reserve_clos tc2) a) as ISS2A.
    { apply issued_union. left.
      apply YY. now right. }
    assert (is_w (lab G) a) as WW.
    { eapply issuedW; eauto. }
    assert (acts_set G a) as EA.
    { eapply issuedE; eauto. }
    assert (~ is_init a) as NINIT.
    { intros HH. apply NCOVTC1.
      enough (issued tc1 a) as AA.
      { red in AA. unfolder in AA. desf. destruct y; ins. desf. }
      eapply init_issued; eauto. split; auto. }
    assert (~ is_rel (lab G) a) as NWREL.
    { intros REL.
      enough (issued  tc1 a) as AA.
      { apply NCOVTC1.
        red in AA. unfolder in AA. desf. destruct y; ins. desf. }
      eapply w_covered_issued; eauto.
      split; auto.
      red in SCOH2. rewrite SCOH2 in YYC.
      apply YYC. unfold sim_clos.
      apply covered_union. right.
      unfold rel_clos.
      red. unfolder. eexists (_, _). splits; ins; eauto.
      splits; eauto. apply YY. clear. basic_solver. }
    assert (~ issued tc1 a) as NISST.
    { intros AA. apply NCOVTC1.
      red in AA. unfolder in AA. desf.
      destruct y; ins; desf. }
    assert (~ issued (reserve_clos tc1) a) as NISS.
    { intros AA. apply issued_union in AA. 
      destruct AA as [AA|AA]; auto.
      apply issued_ta_reserve in AA. now red in AA. }
    assert (~ reserve_clos tc1 (mkTL ta_issue a)) as NRESCLOSW.
    { intros [AA|AA]; auto.
      clear -AA. red in AA. do 2 desf. }
    (* TODO: make a lemma? *)
    destruct (classic (W_ex G a)) as [WEX|NWEX].
    2: { apply rt_step.
         eapply ext_rlx_write_promise_step; auto.
         constructor; auto; ins.
         rewrite TCALT. rewrite reserve_clos_union, set_unionA.
         unfold reserve_clos at 2; ins.
         rewrite issued_singleton. rewrite set_pair_union_r.
         split.
         all: do 2 (apply set_subset_union_l; split; eauto with hahn).
         { clear. unfold set_pair. unfolder. ins. do 2 desf; ins. eauto. }
         apply set_subset_union_l; split; eauto with hahn.
         transitivity (reserve_clos tc1); eauto with hahn.
         unfold reserve_clos at 2.
         unionR right.
         apply set_pair_mori; eauto using dom_sb_S_rfrmw_reserve_clos with hahn. }
    set (QQ:=WEX). destruct QQ as [r RMW].
    eapply rt_trans with (y := reserve_clos tc1 ∪₁ eq (mkTL ta_reserve a)).
    all: apply rt_step.
    2: { eapply ext_rlx_write_promise_step; auto.
         { intros AA. apply issued_union in AA. destruct AA as [AA|AA]; ins.
           red in AA. unfolder in AA. desf. }
         constructor; auto.
         { ins. intros [AA|AA].
           2: now inv AA.
           apply NISS. red. unfolder. ins. }
         { clear. basic_solver. }
         rewrite TCALT. rewrite reserve_clos_union.
         unfold reserve_clos at 2.
         rewrite issued_singleton.
         assert (eq ta_reserve <*> eq a ≡₁ eq (mkTL ta_reserve a)) as AA.
         { clear. unfold set_pair. split.
           all: unfolder; ins; do 2 desf. }
         rewrite AA.
         split.
         all: repeat (apply set_subset_union_l; split; eauto 10 with hahn).
         unfold ets_upd_reserve; ins.
         rewrite set_pair_union_r. rewrite AA.
         apply set_subset_union_l; split; eauto 10 with hahn.
         rewrite dom_sb_S_rfrmw_union_P.
         rewrite dom_sb_S_rfrmw_reserve_clos; eauto.
         rewrite set_pair_union_r.
         apply set_subset_union_l; split; eauto 10 with hahn.
         unfold dom_sb_S_rfrmw. rewrite reserved_singleton.
         arewrite (dom_rel (sb G ⨾ ⦗eq a⦘) ∩₁ codom_rel (⦗eq a⦘ ⨾ rfi G ⨾ rmw G) ⊆₁ ∅).
         2: { rewrite set_pair_empty_l. clear. basic_solver. }
         rewrite rmw_in_sb, rfi_in_sb; auto.
         rewrite sb_sb. generalize (@sb_irr G) (@sb_trans G). clear. basic_solver 10. }
    apply ext_reserve_trav_step.
    assert (eq a ⊆₁ issued tc2) as AISS.
    { rewrite YY. clear. basic_solver. }
    
    assert (⦗eq a⦘ ⊆ ⦗is_w (lab G)⦘ ;; ⦗eq a⦘) as AW.
    { generalize WW. clear. basic_solver 10. }
    assert (reserve_coherent G (reserve_clos tc1 ∪₁ eq (mkTL ta_reserve a))) as RCOHNEW.
    { eapply reserve_coherent_ext_reserve with (tc':=tc2); eauto.
      rewrite <- YYC. rewrite AISS. eapply dom_F_sb_I_in_C; eauto. }
    constructor; ins.
    { apply tls_coherent_ext; auto.
      red. right. red; ins. split.
      { clear. basic_solver. }
      do 2 (split; auto). }
    { red. rewrite id_union, seq_union_r, dom_union.
      red in ICOHTC1. rewrite ICOHTC1.
      unionL; eauto with hahn.
      rewrite iord_no_reserve.
      clear. basic_solver 10. }
    { unfold reserve_clos. intros [AA|[AA BB]]; auto.
      eapply RESEMPTC1. red. unfolder; ins; eauto. }
    rewrite set_pair_empty_l.
    now rewrite set_union_empty_r. }
  { rename a0 into w.
    destruct STEP as (REL & tc' & STEP1 & STEP2).
    destruct STEP1 as [STEPA1 STEPRES1].
    apply seq_eqv_l in STEPA1. destruct STEPA1 as [NCOVTC1 TC'ALT].
    destruct STEP2 as [STEPA2 STEPRES2].
    apply seq_eqv_l in STEPA2. destruct STEPA2 as [NCOVTC' TC2ALT].
    rewrite TC'ALT in TC2ALT.
    desf.
    assert (~ issued tc1 w) as NISS.
    { intros AA. apply NCOVTC1. unfold issued in AA.
      clear -AA. unfolder in AA. do 2 desf. destruct y; ins; desf. }

    assert (issued tc2 ≡₁ issued tc1 ∪₁ eq w) as YY.
    { rewrite TC2ALT. rewrite !issued_union, issued_singleton.
      rewrite issued_eq_ta_cover. now rewrite set_union_empty_r. }
    assert (covered tc2 ≡₁ covered tc1 ∪₁ eq w) as YYC.
    { rewrite TC2ALT. rewrite !covered_union, covered_singleton.
      rewrite covered_eq_ta_issue. now rewrite set_union_empty_r. }
    assert (reserved tc' ≡₁ ∅) as RESEMPTC'.
    { rewrite TC'ALT. rewrite reserved_union, RESEMPTC1.
      rewrite reserved_eq_ta_issue. clear. basic_solver. }

    assert (issued (reserve_clos tc2) w) as ISS2A.
    { apply issued_union. left.
      apply YY. now right. }
    assert (is_w (lab G) w) as WW.
    { eapply issuedW; eauto. }
    assert (acts_set G w) as EW.
    { eapply issuedE; eauto. }
    assert (~ is_init w) as NINIT.
    { intros INIT. apply NISS. eapply init_issued; eauto.
      split; auto. }
    assert (~ issued (reserve_clos tc1) w) as NISSW.
    { unfold reserve_clos. intros AA. apply issued_union in AA.
      destruct AA as [AA|AA]; auto.
      eapply issued_ta_reserve; eauto. }
    assert (~ reserve_clos tc' (mkTL ta_cover w)) as NRCTC'.
    { unfold reserve_clos. intros [AA|AA]; auto.
      clear -AA. red in AA. do 2 desf. }
    assert (~ covered tc1 w) as NCOVW.
    { intros HH. apply NISS. eapply w_covered_issued; eauto.
      split; auto. }
    assert (~ codom_rel (rmw G) w) as NWEX.
    { eapply sim_clos_cover_no_codom_rmw; eauto. }
    apply rt_step.
    eapply ext_rel_write_step with (T':=reserve_clos tc'); eauto.
    2: { constructor; auto; ins.
         rewrite set_pair_empty_l, set_union_empty_r.
         rewrite TC2ALT, TC'ALT.
         rewrite !reserve_clos_union.
         apply set_union_more; try easy.
         unfold reserve_clos. rewrite issued_eq_ta_cover.
         now rewrite set_pair_empty_l, set_union_empty_r. }
    assert (tls_coherent G tc') as TLSCOHTC'.
    { rewrite TC'ALT. apply tls_coherent_ext; auto.
      red. right. red. split.
      { basic_solver. }
      repeat (split; auto). }
    constructor; auto; ins.
    { apply reserve_clos_tls_coherent; auto. }
    { apply reserve_clos_iord_coherent; auto. }
    { eapply reserve_clos_reserve_coherent; eauto. }
    { intros [AA|AA]; eauto.
      red in AA. do 2 desf. }
    rewrite TC'ALT. rewrite reserve_clos_union.
    unfold reserve_clos at 2.
    rewrite issued_singleton. rewrite set_pair_union_r.
    split.
    all: repeat (apply set_subset_union_l; split; eauto with hahn).
    transitivity (reserve_clos tc1); eauto with hahn.
    unfold reserve_clos.
    transitivity (eq ta_reserve <*> issued tc1); eauto with hahn.
    apply set_pair_mori; eauto with hahn.
    eapply dom_sb_S_rfrmw_reserve_clos; eauto. }
  { destruct STEP as [STEPA [IA IB]].
    apply seq_eqv_l in STEPA. destruct STEPA as [NCOVTC1 TCALT].
    apply rt_step.
    eapply ext_propagation_trav_step with (e:=a).
    constructor; auto; ins.
    { intros [AA|AA]; auto.
      clear -AA. red in AA. do 2 desf. }
    rewrite TCALT. rewrite reserve_clos_union, set_unionA.
    do 2 (apply set_union_more; auto).
    arewrite (issued (eq (ta_propagate tid, a)) ≡₁ ∅); try easy.
    unfold issued. clear. basic_solver. }
  exfalso.
  destruct STEP as [STEPA [IA IB]].
  apply seq_eqv_l in STEPA. destruct STEPA as [NCOVTC1 TCALT].
  rewrite TCALT in RESEMPTC2.
  eapply RESEMPTC2. apply reserved_union.
  right. red. clear. basic_solver.
Qed.

(* TODO: get rid of FRELACQ *)
Lemma sim_clos_step2ext_sim_trav_step tc1 tc2
      (* (COH1: tc_coherent G sc tc1) *)
      (STEP: sim_clos_step G sc tc1 tc2) :
  (ext_sim_trav_step G sc)^* (reserve_clos tc1) (reserve_clos tc2).
Proof using WF IMMCON FRELACQ.
  red in STEP. desc. 
  apply isim_trav_step2ext_isim_trav_step in STEP; auto.
  induction STEP.
  { apply rt_step. red. eauto. }
  { apply rt_refl. }
  eapply rt_trans; eauto. 
Qed. 


Lemma tc_coh2etc_coh tc (COH: tc_coherent G sc tc)
      (w_ex_is_xacq : W_ex G ⊆₁ W_ex G ∩₁ is_xacq (lab G)):
  etc_coherent G sc (mkETC tc (issued tc)).
Proof using WF IMMCON.
  forward eapply tc_coherent_implies_tc_coherent_alt as COH_ALT; eauto.
  { apply IMMCON. }
  inversion COH_ALT.
  destruct tc as [C I]. simpl in *.
  split; auto; unfold ecovered, eissued; simpl.
  { basic_solver. }
  { etransitivity; [| by apply tc_fwbob_I]. apply dom_rel_mori.
    rewrite <- !seqA. hahn_frame. apply imm_bob.sb_from_f_in_fwbob. }
  { forward eapply dom_detour_rmwrfi_rfe_acq_sb_issued as IN; eauto. }
  { forward eapply dom_wex_sb_issued as IN; eauto. }
  { unfold dom_sb_S_rfrmw. simpl.
    rewrite rmw_W_ex. repeat rewrite codom_seq. rewrite codom_eqv.
    rewrite set_interC, <- dom_eqv1.
    rewrite w_ex_is_xacq. forward eapply dom_wex_sb_issued as IN; eauto. }
  { sin_rewrite detour_rfe_data_rfi_rmw_rppo_in_detour_rfe_ppo; auto.
    rewrite seqA. forward eapply dom_detour_rfe_ppo_issued as IN; eauto. }
  { rewrite (dom_l (wf_detourD WF)); auto.
    rewrite detour_in_ar, imm_s_ppo.rmw_in_ar_int, ar_int_in_ar; eauto.
    etransitivity; [| by apply tc_I_ar_rf_ppo_loc_I]. apply dom_rel_mori.
    hahn_frame. rewrite <- ct_unit, <- ct_step. apply seq_mori; basic_solver 10. }
  forward eapply TraversalProperties.issuable_W_ex_in_codom_I_rfrmw as IN; eauto.
  rewrite <- IN, <- issued_in_issuable; auto.
Qed.

Lemma itrav_step2ext_itrav_step_cover (C I: actid -> Prop) (e: actid)
      (COH: tc_coherent G sc (mkTC C I))
      (w_ex_is_xacq : W_ex G ⊆₁ W_ex G ∩₁ is_xacq (lab G))
      (STEP: itrav_step G sc e (mkTC C I) (mkTC (C ∪₁ eq e) I)):
  ext_itrav_step G sc e (mkETC (mkTC C I) I) (mkETC (mkTC (C ∪₁ eq e) I) I).
Proof.
  forward eapply trav_step_coherence as COH2; [by red; eauto| done |].
  inversion STEP.
  2: { red in H. desc. simpl in *. destruct NISS. apply ISSEQ. basic_solver. }
  red in H. desc. red. splits; unfold ecovered, eissued; simpl in *; eauto.
  by apply tc_coh2etc_coh.
Qed.

Lemma etc_coh_extend_reserved tc w
      (w_ex_is_xacq : W_ex G ⊆₁ W_ex G ∩₁ is_xacq (lab G))
      (WEXw: W_ex G w)
      (NISS: ~ issued tc w)
      (ISS'w: issuable G sc tc w)
      (TCOH: etc_coherent G sc (mkETC tc (issued tc))):
  etc_coherent G sc (mkETC tc (issued tc ∪₁ eq w)). 
Proof using WF IMMCON.
  pose proof COH as COH'. destruct COH'.
  destruct tc as [C I] eqn:TC. 
  split; auto; unfold ecovered, eissued in *; simpl in *.
  { apply W_ex_in_E in WEXw; auto. basic_solver. }
  { basic_solver. }
  { basic_solver. }
  { rewrite id_union. repeat rewrite seq_union_r. rewrite dom_union. 
    apply set_subset_union_l. split; auto.
    etransitivity; [| by apply ISS'w]. apply dom_rel_mori. hahn_frame.
    apply imm_bob.sb_from_f_in_fwbob. }
  { rewrite id_union. repeat rewrite seq_union_r. rewrite dom_union. 
    apply set_subset_union_l. split; auto.
    replace I with (issued tc) by vauto.
    etransitivity; [| by eapply dom_detour_rmwrfi_rfe_acq_sb_issuable; eauto].
    apply dom_rel_mori. repeat hahn_frame_l. basic_solver. }
  { rewrite id_union. repeat rewrite seq_union_r. rewrite dom_union. 
    apply set_subset_union_l. split; auto.
    replace I with (issued tc) by vauto.
    etransitivity; [| by eapply dom_wex_sb_issuable; eauto].
    apply dom_rel_mori. repeat hahn_frame_l. basic_solver. }
  { rewrite dom_sb_S_rfrmw_issuable; auto.
    { simpl. basic_solver. }
    simpl. replace I with (issued tc) by vauto.
    rewrite issued_in_issuable at 1; vauto. basic_solver. }
  { rewrite id_union. repeat rewrite seq_union_r. rewrite dom_union.
    apply set_subset_union_l. split; auto.
    sin_rewrite detour_rfe_data_rfi_rmw_rppo_in_detour_rfe_ppo; auto.
    replace I with (issued tc) by vauto.
    etransitivity; [| by apply dom_detour_rfe_ppo_issuable; eauto].
    apply dom_rel_mori. hahn_frame. basic_solver. }
  { rewrite id_union. repeat rewrite seq_union_r. rewrite dom_union.
    apply set_subset_union_l. split; auto.
    rewrite (dom_l (wf_detourD WF)); auto. 
    rewrite detour_in_ar, imm_s_ppo.rmw_in_ar_int, ar_int_in_ar; eauto.
    etransitivity; [| by apply ISS'w]. apply dom_rel_mori.
    hahn_frame. rewrite <- ct_unit, <- ct_step. apply seq_mori; basic_solver. }
  rewrite set_inter_union_l. apply set_subset_union_l. split; auto.
  replace I with (issued tc) by vauto.
  rewrite <- TraversalProperties.issuable_W_ex_in_codom_I_rfrmw; try by vauto.
  basic_solver. 
Qed.

Lemma etc_coh_extend_reserved_rmw tc r w
      (w_ex_is_xacq : W_ex G ⊆₁ W_ex G ∩₁ is_xacq (lab G))
      (WEXw: W_ex G w)
      (COV'r: coverable G sc tc r)
      (RMW: rmw G r w)
      (COH: etc_coherent G sc (mkETC tc (issued tc))):
  etc_coherent G sc (mkETC tc (issued tc ∪₁ eq w)). 
Proof using WF IMMCON.
  clear FRELACQ. 
  apply wf_rmwD, seq_eqv_lr in RMW as (Rr & RMW & Ww); eauto. 
  destruct (classic (issued tc w)) as [ISSw | NISSw].
  { eapply etc_coherent_more; eauto. red. splits; basic_solver. }

  assert (sb G ⨾ ⦗eq w⦘ ⊆ ⦗coverable G sc tc⦘  ⨾ (sb G)^? ⨾ rmw G ⨾ ⦗eq w⦘) as DOM_SBw.
  { assert (⦗eq r⦘ ⨾ rmw G ⨾ ⦗eq w⦘ ⊆ rmw G ⨾ ⦗eq w⦘) as <- by basic_solver.
    rewrite sb_rmw_split; eauto. do 2 hahn_frame_r. 
    rewrite crE. repeat case_union _ _. apply union_mori; [basic_solver 10| ].
    red in COV'r. apply proj1, proj2 in COV'r. red in COV'r.
    apply dom_rel_helper_in in COV'r. rewrite COV'r at 1.
    hahn_frame. apply eqv_rel_mori. apply covered_in_coverable. apply COH. }

  pose proof COH as COH'. destruct COH'.
  destruct tc as [C I] eqn:TC. unfold ecovered, eissued in *; simpl in *.

  assert (dom_rel (⦗is_w (lab G)⦘ ⨾ sb G ⨾ ⦗eq r⦘ ⨾ rmw G ⨾ ⦗eq w⦘) ⊆₁ I) as SB_R_HELPER. 
  { rewrite <- !seqA. do 2 rewrite dom_seq. rewrite seqA.  
    red in COV'r. apply proj1, proj2 in COV'r. red in COV'r.
    apply dom_rel_helper_in in COV'r. rewrite COV'r at 1.
    seq_rewrite <- id_inter. repeat rewrite dom_seq. rewrite dom_eqv.
    rewrite w_covered_issued; eauto using COH. } 

  assert (dom_rel ((detour G ∪ rfe G) ⨾ sb G ⨾ ⦗eq w⦘) ⊆₁ I) as DET_RFE_ISS. 
  { rewrite DOM_SBw. rewrite <- !seqA. do 3 rewrite dom_seq.
    rewrite seq_union_l, dom_union. apply set_subset_union_l. split.
    { rewrite (dom_l (wf_detourD WF)). rewrite detour_in_sb, seqA, dom_eqv1. 
      rewrite dom_sb_coverable. rewrite w_covered_issued; eauto. }
    rewrite rfe_in_rf. apply dom_rf_coverable; auto. }


  split; auto; unfold ecovered, eissued in *; simpl in *.
  { apply W_ex_in_E in WEXw; auto. basic_solver. }
  { basic_solver. }
  { basic_solver. }
  { rewrite id_union. repeat rewrite seq_union_r. rewrite dom_union. 
    apply set_subset_union_l. split; auto.
    erewrite sb_rmw_split_disj; eauto.
    2: { unfolder. intros ?. desc. subst. type_solver. }
    etransitivity; [| apply COV'r]. basic_solver. }
  { rewrite id_union. repeat rewrite seq_union_r. rewrite dom_union. 
    apply set_subset_union_l. split; auto.
    rewrite inclusion_seq_eqv_l.
    rewrite rmw_in_sb, rfi_in_sb, sb_sb; auto.
    seq_rewrite <- ct_end. rewrite ct_of_trans; [| by apply sb_trans]. auto. }
  { rewrite id_union. repeat rewrite seq_union_r. rewrite dom_union. 
    apply set_subset_union_l. split; auto.
    rewrite W_ex_in_W; auto. erewrite eqv_rel_mori; [| red; intro; apply proj1].
    rewrite sb_rmw_split_disj; eauto.
    unfolder. intros ?. desc. subst x. type_solver. }
  { unfold dom_sb_S_rfrmw. simpl.
    rewrite id_union, seq_union_r, dom_union. rewrite set_inter_union_l.
    apply set_subset_union_l. split.
    { rewrite etc_sb_S. basic_solver. }
    rewrite wf_rmwD; auto. repeat rewrite codom_seq. rewrite codom_eqv.
    rewrite set_interC, <- dom_eqv1.
    rewrite sb_rmw_split_disj; eauto.
    2: { unfolder. intro. type_solver 10. }
    rewrite SB_R_HELPER. basic_solver. }
  { rewrite id_union. repeat rewrite seq_union_r. rewrite dom_union.
    apply set_subset_union_l. split; auto.
    rewrite rppo_in_sb, data_in_sb, rfi_in_sb, rmw_in_sb; auto. rewrite !unionK.
    seq_rewrite <- ct_end. rewrite ct_of_trans; [| by apply sb_trans]. auto. }
  { rewrite id_union. repeat rewrite seq_union_r. rewrite dom_union.
    apply set_subset_union_l. split; auto.
    rewrite <- DET_RFE_ISS. apply dom_rel_mori.
    rewrite rmw_in_sb; auto. basic_solver 10. }
  rewrite set_inter_union_l. apply set_subset_union_l. split; auto.
  red. intros ? [<- _].
  cdes IMMCON. destruct (Comp r) as [w' RF].
  { apply wf_rmwE in RMW; auto. generalize RMW, Rr. basic_solver 10. }
  exists w'. forward eapply dom_rf_coverable with (x := w'); eauto; basic_solver 10. 
Qed. 

(* Notation "'[' C '#' I '#' R ']'" := (mkETC (mkTC C I) R).  *)
  
Lemma itrav_step2ext_itrav_step_issue (C I: actid -> Prop) (e: actid)
      (w_ex_is_xacq : W_ex G ⊆₁ W_ex G ∩₁ is_xacq (lab G))
      (COH: tc_coherent G sc (mkTC C I))
      (STEP: itrav_step G sc e (mkTC C I) (mkTC C (I ∪₁ eq e))):
  ((ext_itrav_step G sc e ⨾ ⦗eq [C # I # I ∪₁ eq e]⦘)^? ⨾ 
                  ⦗etc_coherent G sc⦘ ⨾ (ext_itrav_step G sc e))
                         [C # I # I]
                         [C # I ∪₁ eq e # I ∪₁ eq e].
Proof.
  forward eapply trav_step_coherence as COH2; [by red; eauto| done |]. 
  inversion STEP.
  { red in H. desc. simpl in *. destruct NEXT. apply COVEQ. basic_solver. }
  red in H. desc. unfold ecovered, eissued; simpl in *.
  destruct (classic (W_ex G e)) as [WEXe | NWEXe].
  2: { eexists. splits; [by apply r_refl| ].
       apply seq_eqv_l. split; [by apply tc_coh2etc_coh| ]. 
       red. splits.
       2: { apply tc_coh2etc_coh; eauto. }
       right. left. unfold ecovered, eissued; simpl in *. splits; eauto.
       { tauto. }
       rewrite set_unionA, set_unionC with (s := eq e), <- set_unionA.
       rewrite set_union_absorb_r with (s := dom_sb_S_rfrmw _ _ _ _); auto.
       rewrite dom_sb_S_rfrmw_issuable; auto.
       rewrite <- issued_in_issuable; auto. }
  forward eapply (@etc_coh_extend_reserved (mkTC C I) e) as COH'; eauto.
  { apply tc_coh2etc_coh; auto. }
  simpl in COH'. remember [C # I # I ∪₁ eq e] as tc'.
  exists tc'. split.
  { apply r_step, seq_eqv_r. split; auto. 
    red. splits; auto. 
    do 2 right. subst tc'. splits; eauto. }
  apply seq_eqv_l. split; auto. 
  red. splits; [| subst tc'; vauto]. 
  2: { apply tc_coh2etc_coh; auto. }
  right. left. splits; vauto. simpl. split; [basic_solver| ]. 
  rewrite dom_sb_S_rfrmw_issuable; auto.
  { basic_solver. }
  apply set_subset_union_l. split; [| basic_solver].
  rewrite <- issued_in_issuable; auto.
Qed.

Lemma ext_isim_trav_step_more_helper:
  forall (y : thread_id) x y0,
  same_ext_trav_config x y0 ->
  forall x0 y1 : ext_trav_config,
  same_ext_trav_config x0 y1 ->
  ext_isim_trav_step G sc y x x0 -> ext_isim_trav_step G sc y y0 y1. 
Proof.
  intros t tc1 tc2 SAME tc1' tc2' SAME' STEP.
  apply same_etc_extensionality in SAME, SAME'. congruence. 
Qed.

Global Add Parametric Morphism : (ext_isim_trav_step G sc) with signature
    eq ==> same_ext_trav_config ==> same_ext_trav_config ==> iff as
        ext_isim_trav_step_more.
Proof using.
  ins; split; apply ext_isim_trav_step_more_helper.
  3, 4: symmetry. all: done. 
Qed. 

Lemma eis_add_res_rmw (C I C' I': actid -> Prop)
      (e: actid) (r w: actid)
      (RMWrw: rmw G r w)
      (w_ex_is_xacq : W_ex G ⊆₁ W_ex G ∩₁ is_xacq (lab G))
      (COV'r: C' r)
      (Erw: ⟪Erw: e = r \/ e = w⟫)
      (STEP: ext_itrav_step G sc e [C # I # I] [C' # I' # I'])
      (COH: tc_coherent G sc (mkTC C I)):
  ext_itrav_step G sc e [C # I # I ∪₁ eq w] [C' # I' # I' ∪₁ eq w].
Proof.
  assert (etc_coherent G sc [C # I # I]) as COH1. 
  { apply tc_coh2etc_coh; auto. }
  destruct STEP as [STEP COH2]. red in COH2. 

  red. splits.
  2: { eapply etc_coh_extend_reserved_rmw; eauto.
       { eexists. eauto. }
       eapply covered_in_coverable; eauto. apply COH2. }
  unfold ecovered, eissued in *. simpl in *. desf.
  { left. splits; try by vauto. by rewrite ISSEQ. }
  { right. left. splits; try by vauto.
    { intuition. }
    red in Erw. des; subst e. 
    { destruct COH2. apply issuedW in etc_tccoh.
      simpl in etc_tccoh. rewrite ISSEQ in etc_tccoh.
      apply set_subset_union_l in etc_tccoh. desc.
      apply wf_rmwD, seq_eqv_lr in RMWrw; auto. desc. 
      exfalso. generalize RMWrw, etc_tccoh0. unfolder. ins.
      specialize (etc_tccoh1 r eq_refl). type_solver. }
    rewrite ISSEQ. 
    split; [basic_solver| ]. 
    arewrite (dom_sb_S_rfrmw G [C # I # I ∪₁ eq w] (rfi G) (eq w) ≡₁ dom_sb_S_rfrmw G [C' # I' # I'] (rfi G) (eq w)).
    { unfold dom_sb_S_rfrmw. simpl. rewrite <- ISSEQ. basic_solver. }
    rewrite dom_sb_S_rfrmw_issuable; try by vauto.
    { unfold eissued. simpl. rewrite ISSEQ. basic_solver. }
    simpl. rewrite <- issued_in_issuable; auto. apply COH2. }
  right. right.
  destruct NISS. apply ISSEQ, RESEQ. basic_solver. 
Qed. 

End ReserveClosSteps.
