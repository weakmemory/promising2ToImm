From hahn Require Import Hahn.

From imm Require Import Events.
From imm Require Import Execution.
From imm Require Import Execution_eco.
From imm Require Import imm_bob imm_s_ppo.
From imm Require Import imm_s_hb.
From imm Require Import imm_s.
From imm Require Import imm_common_more.
From imm Require Import CertCOhelper.
From imm Require Import CombRelations.
From imm Require Import FairExecution.

From imm Require Import AuxDef.
Require Import ExtTraversalConfig.
From imm Require Import TraversalOrder.
From imm Require Import TLSCoherency.
From imm Require Import IordCoherency.
From imm Require Import SimClosure. 
Require Import TlsEventSets.
From imm Require Import FinExecution. 

From imm Require Import TraversalOrder.
From imm Require Import TLSCoherency.
From imm Require Import IordCoherency.
Require Import TlsEventSets.
Require Import EventsTraversalOrder.

Require Import ExtTraversalConfig.

Require Import Cert_co.
Require Import Cert_D.
Require Import Cert_rf.
Require Import Cert_ar.
Require Import Cert_atomicity.
Require Import Cert_coherence.
Require Import CertExecution2.
Require Import TLSCoherencyAltOld. 

Set Implicit Arguments.

Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'NTid_' t" := (fun x => tid x <> t) (at level 1).

Section CertExec_tc.

Variable G : execution.
Variable sc : relation actid.

Notation "'Init'" := (fun a => is_true (is_init a)).

Notation "'E'" := (acts_set G).
(* Notation "'Gacts'" := (acts G). *)
Notation "'Glab'" := (lab G).
Notation "'Gsb'" := (sb G).
Notation "'Grf'" := (rf G).
Notation "'Gco'" := (co G).
Notation "'Grmw'" := (rmw G).
Notation "'Gdata'" := (data G).
Notation "'Gaddr'" := (addr G).
Notation "'Gctrl'" := (ctrl G).
Notation "'Gdeps'" := (deps G).
Notation "'Grmw_dep'" := (rmw_dep G).

Notation "'Gfre'" := (fre G).
Notation "'Grfe'" := (rfe G).
Notation "'Gcoe'" := (coe G).
Notation "'Grfi'" := (rfi G).
Notation "'Gfri'" := (fri G).
Notation "'Gcoi'" := (coi G).
Notation "'Gfr'" := (fr G).
Notation "'Geco'" := (eco G).
Notation "'Gdetour'" := (detour G).
Notation "'Gsw'" := (sw G).
Notation "'Grelease'" := (release G).
Notation "'Grs'" := (rs G).
Notation "'Ghb'" := (hb G).
Notation "'Gppo'" := (ppo G).
Notation "'Grppo'" := (rppo G).
Notation "'Gbob'" := (bob G).
Notation "'Gfwbob'" := (fwbob G).
Notation "'Gar'" := ((ar G) sc).
Notation "'Gar_int'" := ((ar_int G)).
Notation "'Gurr'" := ((urr G) sc).
Notation "'Gfurr'" := ((furr G) sc).
Notation "'Gmsg_rel'" := ((msg_rel G) sc).

Notation "'Gloc'" := (loc Glab).
Notation "'Gval'" := (val Glab).
Notation "'Gsame_loc'" := (same_loc Glab).

Notation "'R'" := (fun a => is_true (is_r Glab a)).
Notation "'W'" := (fun a => is_true (is_w Glab a)).
Notation "'F'" := (fun a => is_true (is_f Glab a)).
Notation "'GR_ex'" := (fun a => is_true (R_ex Glab a)).
Notation "'GW_ex'" := (W_ex G).
Notation "'GW_ex_acq'" := (GW_ex ∩₁ (fun a => is_true (is_xacq Glab a))).

Notation "'Loc_' l" := (fun x => Gloc x = Some l) (at level 1).
Notation "'W_' l" := (W ∩₁ Loc_ l) (at level 1).
Notation "'R_' l" := (R ∩₁ Loc_ l) (at level 1).

Notation "'Pln'" := (fun a => is_true (is_only_pln Glab a)).
Notation "'Rlx'" := (fun a => is_true (is_rlx Glab a)).
Notation "'Rel'" := (fun a => is_true (is_rel Glab a)).
Notation "'Acq'" := (fun a => is_true (is_acq Glab a)).
Notation "'Acqrel'" := (fun a => is_true (is_acqrel Glab a)).
Notation "'Acq/Rel'" := (fun a => is_true (is_ra Glab a)).
Notation "'Sc'" := (fun a => is_true (is_sc Glab a)).
Notation "'xacq'" := (fun a => is_true (is_xacq Glab a)).

Variable T : trav_label -> Prop.

Notation "'I'" := (issued T).
Notation "'C'" := (covered T).
Notation "'S'" := (reserved T).

Variable thread : BinNums.positive.

Notation "'cert_co'" := (cert_co G T thread).

Notation "'D'" := (D G T thread).

Notation "'new_rf'" := (new_rf G sc T thread).
Notation "'cert_rf'" := (cert_rf G sc T thread).
Notation "'cert_rfi'" := (cert_rfi G sc T thread).
Notation "'cert_rfe'" := (cert_rfe G sc T thread).

Hypothesis WF : Wf G.
Hypothesis WF_SC : wf_sc G sc.
Hypothesis RELCOV : W ∩₁ Rel ∩₁ I ⊆₁ C.
Hypothesis TCOH : tls_coherent G T.
Hypothesis ICOH : iord_coherent G sc T.
Hypothesis RCOH : reserve_coherent G T.
Hypothesis ACYC_EXT : acyc_ext G sc.
Hypothesis CSC : coh_sc G sc.
Hypothesis COH : coherence G.
Hypothesis AT : rmw_atomicity G.
Hypothesis FIN : fin_exec G. 

Hypothesis IT_new_co: I ∪₁ E ∩₁ W ∩₁ Tid_ thread ≡₁ E ∩₁ W.
Hypothesis E_to_S: E ⊆₁ C ∪₁ dom_rel (Gsb^? ⨾ ⦗S⦘).
Hypothesis Grfe_E : dom_rel Grfe ⊆₁ I.
Hypothesis E_F_AcqRel_in_C: E ∩₁ F ∩₁ Acq/Rel ⊆₁ C.
Hypothesis COMP_ACQ: forall r (IN: (E ∩₁ R ∩₁ Acq) r), exists w, Grf w r.
Hypothesis urr_helper: dom_rel ((Ghb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ sc^? ⨾ Ghb^? ⨾ Grelease ⨾ ⦗I⦘) ⊆₁ C.
Hypothesis urr_helper_C: dom_rel ((Ghb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ sc^? ⨾ Ghb^? ⨾ (Grelease ⨾ Grf)^? ⨾ ⦗C⦘) ⊆₁ C.
Hypothesis W_hb_sc_hb_to_I_NTid: dom_rel (⦗W⦘ ⨾ Ghb ⨾ (sc ⨾ Ghb)^? ⨾ ⦗I ∩₁ NTid_ thread⦘) ⊆₁ I.
Hypothesis detour_E : dom_rel (Gdetour ⨾ ⦗E ∩₁ NTid_ thread⦘) ⊆₁ I.
Hypothesis detour_Acq_E : dom_rel (Gdetour ⨾ ⦗E ∩₁ R ∩₁ Acq⦘) ⊆₁ I.
Hypothesis hb_sc_hb_de : ⦗(E \₁ C) ∩₁ (E \₁ I)⦘ ⨾ Ghb ⨾ (sc ⨾ Ghb)^? ⊆ Gsb.
Hypothesis COMP_C : C ∩₁ R ⊆₁ codom_rel Grf.
Hypothesis COMP_NTID : E ∩₁ NTid_ thread ∩₁ R ⊆₁ codom_rel Grf.
Hypothesis COMP_PPO : dom_rel (Gppo ⨾ ⦗I⦘) ⊆₁ codom_rel Grf.
Hypothesis COMP_RPPO : dom_rel (⦗R⦘ ⨾ (Gdata ∪ Grfi ∪ Grmw)＊ ⨾ Grppo ⨾ ⦗S⦘) ⊆₁ codom_rel Grf.
Hypothesis TCCOH_rst_new_T : tls_coherent G (T ∪₁ eq ta_cover <*> (E ∩₁ NTid_ thread)).
(* Hypothesis TCOH_rst_new_T_restr : tls_coherent G ((T ∪₁ eq ta_cover <*> (E ∩₁ NTid_ thread)) \₁ action ↓₁ eq ta_reserve). *)
Hypothesis ICOH_rst_new_T : iord_coherent G sc (T ∪₁ eq ta_cover <*> (E ∩₁ NTid_ thread)).

Hypothesis S_in_W : S ⊆₁ W.
Hypothesis RPPO_S : dom_rel ((Gdetour ∪ Grfe) ⨾ (Gdata ∪ Grfi ∪ Grmw)＊ ⨾ Grppo ⨾ ⦗S⦘) ⊆₁ I.
Hypothesis RMW_S : dom_rel ((Gdetour ∪ Grfe) ⨾ Grmw ⨾ ⦗S⦘) ⊆₁ I.
Hypothesis ST_in_E : S ∩₁ Tid_ thread ⊆₁ E.
Hypothesis I_in_S : I ⊆₁ S.
Hypothesis W_ex_sb_I : dom_rel (⦗GW_ex_acq⦘ ⨾ Gsb ⨾ ⦗S⦘) ⊆₁ I.

Hypothesis F_in_C : E ∩₁ F ∩₁ Acq/Rel ⊆₁ C.

Hypothesis S_I_in_W_ex : (S ∩₁ Tid_ thread) \₁ I ⊆₁ W_ex G.

Hypothesis ETC_DR_R_ACQ_I : dom_rel ((Gdetour ∪ Grfe) ⨾ (Grmw ⨾ Grfi)＊ ⨾ ⦗R∩₁Acq⦘ ⨾ Gsb ⨾ ⦗S⦘) ⊆₁ I.

Hypothesis COMP_R_ACQ_SB : dom_rel ((Grmw ⨾ Grfi)＊ ⨾ ⦗E ∩₁ R ∩₁ Acq⦘) ⊆₁ codom_rel Grf.

Variable lab' : actid -> label.
Hypothesis SAME : same_lab_u2v lab' Glab.

Hypothesis NEW_VAL : forall r w (RF: cert_rf w r), val lab' w = val lab' r.
Hypothesis OLD_VAL : forall a (NIN: ~ (E \₁ D) a), val lab' a = Gval a.

Hypothesis ETC_DETOUR_RMW_S : dom_rel (Gdetour ⨾ Grmw ⨾ ⦗ S ⦘) ⊆₁ I.

Hypothesis SB_S          : dom_sb_S_rfrmw G T (Grf ⨾ ⦗GR_ex⦘) I ⊆₁ S.
Hypothesis RMWREX        : dom_rel Grmw ⊆₁ GR_ex.
Hypothesis FACQREL       : E ∩₁ F ⊆₁ Acq/Rel.

Notation "'certG'" := (certG G sc T thread lab').

Hypothesis WF_cert    : Wf certG.
Hypothesis WF_SC_cert : wf_sc certG sc.

(* Notation "'CE'" := (acts_set certG). *)
(* Notation "'Cacts'" := (acts certG). *)
(* Notation "'Clab'" := (lab certG). *)
(* Notation "'Csb'" := (sb certG). *)
Notation "'Crf'" := (rf certG).
Notation "'Cco'" := (co certG).
Notation "'Crmw'" := (rmw certG).
(* Notation "'Cdata'" := (data certG). *)
(* Notation "'Caddr'" := (addr certG). *)
(* Notation "'Cctrl'" := (ctrl certG). *)
Notation "'Cdeps'" := (deps certG).
(* Notation "'Crmw_dep'" := (rmw_dep certG). *)

Notation "'Cfre'" := (fre certG).
(* Notation "'Crfe'" := (rfe certG). *)
Notation "'Ccoe'" := (coe certG).
Notation "'Crfi'" := (rfi certG).
Notation "'Cfri'" := (fri certG).
Notation "'Ccoi'" := (coi certG).
Notation "'Cfr'" := (fr certG).
Notation "'Ceco'" := (eco certG).
Notation "'Cdetour'" := (detour certG).
Notation "'Csw'" := (sw certG).
Notation "'Crelease'" := (release certG).
Notation "'Crs'" := (rs certG).
Notation "'Chb'" := (hb certG).
Notation "'Cppo'" := (ppo certG).
(* Notation "'Cbob'" := (bob certG). *)
(* Notation "'Cfwbob'" := (fwbob certG). *)
Notation "'Car'" := ((ar certG) sc).
Notation "'Car_int'" := ((ar_int certG)).
Notation "'Curr'" := ((urr certG) sc).
Notation "'Cmsg_rel'" := ((msg_rel certG) sc).

(* Notation "'E'" := (acts_set G). *)
(* Notation "'Gacts'" := (acts G). *)
Notation "'Clab'" := (lab certG).
Notation "'Csb'" := (sb certG).
(* Notation "'Grf'" := (rf G). *)
(* Notation "'Gco'" := (co G). *)
(* Notation "'Gdata'" := (data G). *)
(* Notation "'Gaddr'" := (addr G). *)
(* Notation "'Gctrl'" := (ctrl G). *)
(* Notation "'Gdeps'" := (deps G). *)
(* Notation "'Grmw_dep'" := (rmw_dep G). *)

(* Notation "'Gfre'" := (fre G). *)
Notation "'Crfe'" := (rfe certG).
(* Notation "'Gcoe'" := (coe G). *)
Notation "'Crfi'" := (rfi certG).
(* Notation "'Gfri'" := (fri G). *)
(* Notation "'Gcoi'" := (coi G). *)
(* Notation "'Gfr'" := (fr G). *)
(* Notation "'Geco'" := (eco G). *)
(* Notation "'Gdetour'" := (detour G). *)
(* Notation "'Gsw'" := (sw G). *)
Notation "'Crelease'" := (release certG).
(* Notation "'Grs'" := (rs G). *)
(* Notation "'Ghb'" := (hb G). *)
(* Notation "'Gppo'" := (ppo G). *)
(* Notation "'Grppo'" := (rppo G). *)
(* Notation "'Gbob'" := (bob G). *)
(* Notation "'Gfwbob'" := (fwbob G). *)
(* Notation "'Gar'" := ((ar G) sc). *)
(* Notation "'Gar_int'" := ((ar_int G)). *)
(* Notation "'Gurr'" := ((urr G) sc). *)
(* Notation "'Gfurr'" := ((furr G) sc). *)
(* Notation "'Gmsg_rel'" := ((msg_rel G) sc). *)

(* Notation "'Gloc'" := (loc Glab). *)
(* Notation "'Gval'" := (val Glab). *)
Notation "'Csame_loc'" := (same_loc Clab).

Notation "'CR'" := (fun a => is_true (is_r Clab a)).
Notation "'CW'" := (fun a => is_true (is_w Clab a)).
Notation "'CF'" := (fun a => is_true (is_f Clab a)).
(* Notation "'GR_ex'" := (fun a => is_true (R_ex Glab a)). *)
(* Notation "'GW_ex'" := (W_ex G). *)
(* Notation "'GW_ex_acq'" := (GW_ex ∩₁ (fun a => is_true (is_xacq Glab a))). *)

Notation "'CPln'" := (fun a => is_true (is_only_pln Clab a)).
Notation "'CRlx'" := (fun a => is_true (is_rlx Clab a)).
Notation "'CRel'" := (fun a => is_true (is_rel Clab a)).
Notation "'CAcq'" := (fun a => is_true (is_acq Clab a)).
Notation "'CAcqrel'" := (fun a => is_true (is_acqrel Clab a)).
Notation "'CAcq/Rel'" := (fun a => is_true (is_ra Clab a)).
Notation "'CSc'" := (fun a => is_true (is_sc Clab a)).


Definition certT :=
  (T ∪₁ eq ta_cover <*> (E ∩₁ NTid_ thread)) \₁ action ↓₁ eq ta_reserve ∪₁
  eq ta_reserve <*> (issued T ∪₁ reserved T ∩₁ Tid_ thread). 

Lemma tls_cover_certT:
  certT ∩₁ action ↓₁ eq ta_cover ≡₁
  (T ∪₁ event ↓₁ (E ∩₁ NTid_ thread)) ∩₁ action ↓₁ eq ta_cover. 
Proof using. 
  unfold certT. rewrite !set_pair_alt. fold action event.
  rewrite set_minus_union_l, !set_inter_union_l.
  rewrite set_equiv_union with (t' := ∅); [| reflexivity| ].  
  2: { split; [| basic_solver]. iord_dom_solver. }
  rewrite set_union_empty_r. apply set_equiv_union.
  all: split; [basic_solver| iord_dom_solver]. 
Qed. 

Lemma covered_certT:
  covered certT ≡₁ C ∪₁ E ∩₁ NTid_ thread. 
Proof using.
  (* it's just easier to prove it separately without appealing to tls_cover_certT *)
  clear. 
  unfold certT. simplify_tls_events. basic_solver 10.
Qed. 
  
Lemma tls_issue_certT:
  certT ∩₁ action ↓₁ eq ta_issue ≡₁ T ∩₁ action ↓₁ eq ta_issue. 
Proof using. 
  unfold certT. rewrite !set_pair_alt. fold action event.
  rewrite set_minus_union_l, !set_inter_union_l.
  rewrite set_equiv_union with (t' := ∅); [rewrite set_union_empty_r| reflexivity| ].
  2: { split; [| basic_solver]. iord_dom_solver. }
  rewrite set_equiv_union with (t' := ∅); [rewrite set_union_empty_r| reflexivity| ]. 
  2: { split; [| basic_solver]. iord_dom_solver. }
  split; [basic_solver| iord_dom_solver]. 
Qed. 

Lemma issued_certT:
  issued certT ≡₁ I. 
Proof using.
  clear. 
  unfold certT. simplify_tls_events. basic_solver 10. 
Qed. 
  
Lemma reserved_certT:
  reserved certT ≡₁ issued T ∪₁ reserved T ∩₁ Tid_ thread. 
Proof using.
  clear. 
  unfold certT. simplify_tls_events.
  rewrite set_minus_absorb_l; [basic_solver| ]. 
  unfold reserved. unfolder. ins. desc. vauto.   
Qed. 

Lemma T_propagations_certT_thread t:
  certT ∩₁ action ↓₁ (eq (ta_propagate t)) ≡₁
  T ∩₁ action ↓₁ (eq (ta_propagate t)).
Proof using.
  clear. 
  unfold certT. simplify_tls_events.
  rewrite !set_pair_alt. fold action event. 
  rewrite set_minus_union_l, !set_inter_union_l.
  rewrite set_unionA, set_equiv_union with (t' := ∅). 
  2: { rewrite set_minusE, set_interA.
       rewrite set_interC with (s := set_compl _).
       rewrite set_inter_absorb_r with (s := action ↓₁ _); [reflexivity| ].
       unfolder. by intros ? <-. }
  2: { split; [| basic_solver].
       unfolder. ins; des; vauto; congruence. }
  basic_solver.
Qed.  


Lemma T_propagations_certT:
  certT ∩₁ action ↓₁ (is_ta_propagate_to_G G) ≡₁
  T ∩₁ action ↓₁ (is_ta_propagate_to_G G).
Proof using.
  unfold is_ta_propagate_to_G.
  rewrite set_map_bunion, <- !set_bunion_inter_compat_l.
  apply set_equiv_bunion; [done| ].
  ins. apply T_propagations_certT_thread. 
Qed. 

Lemma propagated_thread_certT t:
  propagated_thread certT t ≡₁ propagated_thread T t.
Proof using. 
  unfold propagated_thread. by rewrite T_propagations_certT_thread. 
Qed. 

Lemma propagated_certT: propagated G certT ≡₁ propagated G T.
Proof using.
  unfold propagated. by rewrite T_propagations_certT. 
Qed. 

Lemma certG_same_props:
  is_ta_propagate_to_G certG ≡₁ is_ta_propagate_to_G G. 
Proof using. auto. Qed. 

Lemma cert_E:
  acts_set certG ≡₁ acts_set G.
Proof using. basic_solver. Qed. 

Lemma cert_sb:
  Csb ≡ Gsb.
Proof using. basic_solver. Qed. 

Lemma init_tls_cert: 
  init_tls certG ≡₁ init_tls G.
Proof using. 
  unfold init_tls. rewrite cert_E. auto. 
Qed.  

Lemma exec_tls_cert: 
  exec_tls certG ≡₁ exec_tls G.
Proof using SAME. 
  unfold exec_tls. rewrite cert_E. erewrite cert_W; eauto. 
Qed.  

Lemma certT_alt:
  certT ≡₁ T ∩₁ action ↓₁ (eq ta_cover ∪₁ eq ta_issue ∪₁
                     is_ta_propagate) ∪₁
    (eq ta_reserve <*> (I ∪₁ S ∩₁ Tid_ thread)) ∪₁
    ((eq ta_cover) <*> (E ∩₁ NTid_ thread)). 
Proof using.
  clear. 
  unfold certT. rewrite !set_pair_alt. apply AuxRel.set_equiv_exp_equiv.
  unfolder. intros [t a]. split; ins; des; destruct t; ins; splits. 
  all: try (by vauto || tauto).
  all: try by (repeat left; vauto). 
  { left. right. vauto. }
  right. vauto.
Qed.  
  
Lemma cert_imm_consistent (FAIR: mem_fair G):
  imm_consistent certG sc.
Proof using All.
  red; splits.
  all: eauto 20 using WF_SC_cert, cert_acyc_ext, cert_coh_sc, cert_complete, cert_coherence, cert_rmw_atomicity.
Qed.

Lemma dom_fwbob_I : dom_rel (Gfwbob ⨾ ⦗C ∪₁ I⦘) ⊆₁ C ∪₁ I.
Proof using E_F_AcqRel_in_C E_to_S F_in_C RELCOV S_in_W WF TCOH ICOH.
  unfold fwbob; relsf; unionL; splits.
  { rewrite sb_W_rel_CI; eauto. basic_solver. }
  { rewrite W_rel_sb_loc_W_CI; eauto. basic_solver. }
  { rewrite (dom_r (@wf_sbE G)).
    generalize dom_sb_F_AcqRel_in_C. basic_solver 12. }
  rewrite (dom_l (@wf_sbE G)).
  generalize E_F_AcqRel_in_C; basic_solver 12.
Qed.  
  
 

Lemma TCOH_cert:
  tls_coherent certG certT.
Proof using TCOH SAME RCOH WF.
  clear -TCOH SAME RCOH WF. 
  pose proof TCOH as TCOH_. destruct TCOH_. split.
  { simpl. rewrite init_tls_cert.
    unfold init_tls.
    rewrite !set_pair_alt. fold event action.
    rewrite !set_map_union, !set_inter_union_l.
    repeat (apply set_subset_union_l; split).
    { red. intros [a e] [[=] [?]]. ins. subst.
      apply tls_set_alt. apply covered_certT. left.
      eapply init_covered; eauto. basic_solver. }
    { red. intros [a e] [[=] [?]]. ins. subst.
      apply tls_set_alt. apply issued_certT.
      eapply init_issued; eauto. basic_solver. }
    { red. intros [a e] [[=] [?]]. ins. subst.
      apply tls_set_alt. apply reserved_certT. left.
      eapply init_issued; eauto. basic_solver. }
    transitivity (certT ∩₁ action ↓₁ is_ta_propagate_to_G G); [| basic_solver].
    rewrite T_propagations_certT. 
    rewrite <- tls_coh_init. unfold init_tls.
    rewrite set_pair_alt. basic_solver. }
  rewrite init_tls_cert, exec_tls_cert. unfold certT. rewrite set_minus_union_l.
  repeat (apply set_subset_union_l; split).
  { rewrite <- tls_coh_exec. basic_solver. }
  { rewrite set_pair_alt. fold action event.
    rewrite set_minusE. rewrite set_inter_absorb_r; [| iord_dom_solver].
    rewrite AuxRel2.set_split_complete with (s := Init).
    rewrite set_map_union, set_inter_union_r. apply set_subset_union.
    { unfold init_tls. rewrite set_pair_alt. basic_solver. }
    unfold exec_tls. rewrite set_pair_alt. basic_solver. }
  rewrite rcoh_I_in_S; eauto.
  arewrite (S ∪₁ S ∩₁ Tid_ thread ⊆₁ E ∩₁ W).
  { forward eapply reservedW; eauto. forward eapply rcoh_S_in_E; basic_solver. }
  rewrite AuxRel2.set_split_complete with (s := Init).
  rewrite set_pair_alt. fold action event. 
  rewrite set_map_union, set_inter_union_r. apply set_subset_union.
  { unfold init_tls. rewrite set_pair_alt. basic_solver. }
  unfold exec_tls. rewrite !set_pair_alt. unionR right. basic_solver. 
Qed.  

Lemma TICOH_cert_old:
  tls_iord_coherent_alt_old certG sc certT.
Proof using All.
  assert (dom_rel Crfe ⊆₁ I) as AA.
  { rewrite cert_rfe_eq. eapply dom_cert_rfe_in_I with (G:=G); eauto. }

  assert (dom_rel ((⦗GW_ex⦘ ⨾ Grfi ⨾ ⦗R ∩₁ Acq⦘) ⨾ (Cppo ∪ bob certG) ⨾ ⦗I⦘) ⊆₁ I) as BB.
  { arewrite (⦗I⦘ ⊆ ⦗D⦘ ⨾ ⦗I⦘).
    { generalize I_in_D. clear. basic_solver. }
    arewrite ((Cppo ∪ bob certG) ⨾ ⦗D⦘ ⊆ Gar_int).
    { rewrite seq_union_l. unionL.
      2: { rewrite cert_bob; eauto. rewrite bob_in_ar_int. clear. basic_solver. }
      rewrite <- ppo_in_ar_int.
      eapply cert_ppo_D; eauto. }
    arewrite (⦗GW_ex⦘ ⊆ ⦗W⦘ ⨾ ⦗GW_ex⦘).
    { generalize (W_ex_in_W WF). clear. basic_solver. }
    arewrite (⦗GW_ex⦘ ⨾ Grfi ⨾ ⦗R ∩₁ Acq⦘ ⊆ Gar_int).
    arewrite (Gar_int ⨾ Gar_int ⊆ Gar_int⁺).
    { by rewrite <- ct_ct, <- ct_step. }
    rewrite (@issued_in_issuable G) at 1; eauto.
    eapply ar_int_ct_issuable_in_I; eauto. }

  assert ((C ∪₁ E ∩₁ NTid_ thread) ∩₁ CW ⊆₁ I) as CNI.
  { erewrite same_lab_u2v_is_w; eauto.
    rewrite set_inter_union_l. apply set_subset_union_l. split.
    { rewrite set_interC. eapply w_covered_issued; eauto. }
    rewrite set_interA, set_interC with (s' := W), <- set_interA.
    rewrite <- IT_new_co. basic_solver. }
  assert (dom_rel (Csb ⨾ ⦗C ∪₁ E ∩₁ NTid_ thread⦘) ⊆₁ C ∪₁ E ∩₁ NTid_ thread) as SBCN.
  { rewrite ?cert_E, ?cert_sb. 
    rewrite id_union, seq_union_r, dom_union.
    apply set_subset_union_l. split.
    { erewrite dom_sb_covered; eauto. basic_solver. }
    (* TODO: generalize this approach? *)
    rewrite AuxRel2.set_split_complete with (s' := dom_rel _) (s := is_init).
    apply set_subset_union_l. split.
    { unionR left. rewrite <- init_covered; eauto.
      rewrite wf_sbE; eauto. basic_solver. }
    rewrite set_interC, <- dom_eqv1.
    unionR right. apply E_ntid_sb_prcl. }  
  
  constructor.
  (* all: try by ins. *)
  all: rewrite ?covered_certT, ?issued_certT, ?reserved_certT, ?propagated_certT; simplify_tls_events.
  all: rewrite ?cert_E, ?cert_sb.
  { erewrite (init_covered _ _ TCOH); eauto. basic_solver. }
  { erewrite (@coveredE G); eauto. basic_solver. }
  { auto. }
  (* { ins; rewrite cert_W; edone. } *)
  { auto. }
  { rewrite rfi_union_rfe; relsf; unionL; splits; ins.
    { rewrite (dom_l (wf_rfiD WF_cert)), cert_W; eauto.
      arewrite (Crfi ⊆ Gsb).
      rewrite <- CNI. rewrite cert_W with (lab' := lab'); eauto.
      generalize SBCN. basic_solver 10. }
    rewrite (dom_rel_helper AA). basic_solver 21. }
  (* { ins; rewrite cert_W; edone. } *)
  { rewrite (dom_r (wf_scD WF_SC)).
    rewrite seqA, <- id_inter, set_inter_union_r.
    erewrite eqv_rel_mori with (y := C). 
    2: { apply set_subset_union_l. split; [basic_solver| ].
         rewrite <- E_F_AcqRel_in_C.
         mode_solver.  }
    rewrite (@dom_sc_covered G) with (T := T); eauto. basic_solver. }
  { eapply (@issuedE G); eauto. }
  { rewrite cert_W; eauto. eapply (@issuedW G); eauto. }
  { ins; rewrite cert_fwbob; eauto.
    rewrite fwbob_I_in_C; eauto. basic_solver. }
  { rewrite cert_W_ex, cert_R, cert_Acq; eauto.
    arewrite (⦗GW_ex⦘ ⨾ Crfi ⨾ ⦗R ∩₁ Acq⦘ ⊆ ⦗GW_ex⦘ ⨾ Grfi ⨾ ⦗R ∩₁ Acq⦘).
    { arewrite (⦗R ∩₁ Acq⦘ ⊆ ⦗Acq⦘ ⨾ ⦗R ∩₁ Acq⦘).
      { clear. basic_solver. }
      arewrite (Crfi ⨾ ⦗Acq⦘ ⊆ Grfi); try done.
      rewrite cert_rfi_eq. eapply cert_rfi_to_Acq_in_Grfi; eauto. }
    remember (Cppo ∪ bob certG) as X.
    rewrite !seq_union_l, !dom_union.
    unionL.
    3: { subst X. apply BB. }
    2: { rewrite (dom_rel_helper AA); basic_solver. }
    subst X. rewrite !seq_union_l, !seq_union_r, !dom_union. unionL; simpls.
    { rewrite I_in_D at 1.
      arewrite (⦗D⦘ ⊆ ⦗D⦘ ⨾ ⦗D⦘) by basic_solver.
      forward (eapply cert_ppo_D with (G:=G)); eauto.
      intros HH. sin_rewrite HH.
      forward (eapply dom_ppo_D with (G:=G)); try edone.
      forward (eapply cert_detour_D with (G:=G)); try edone.
      clear. unfolder; ins; desf. eapply H; basic_solver 42. }
    unfold bob; relsf; unionL; splits; simpls.
    { arewrite (⦗I⦘ ⊆ ⦗C ∪₁ I⦘) at 1.
      rewrite cert_fwbob; auto.
      rewrite (dom_rel_helper dom_fwbob_I).
      rewrite C_in_D, I_in_D at 1; relsf.
      forward (eapply cert_detour_D with (G:=G)); eauto.
      intros HH. sin_rewrite HH.
      basic_solver 20. }
    rewrite I_in_D at 1.
    rewrite !seqA.
    rewrite cert_sb.
    rewrite cert_R, cert_Acq; eauto.
    forward (eapply cert_detour_R_Acq with (G:=G)); eauto.
    intros HH. sin_rewrite HH. basic_solver. }
  { ins; rewrite cert_W_ex_acq; eauto.
    eapply dom_wex_sb_issued; eauto. }
  simpls.
  rewrite same_lab_u2v_same_loc; eauto.
  arewrite (Cppo ∩ Gsame_loc ⨾ ⦗I⦘ ⊆ (Cppo ⨾ ⦗I⦘) ∩ Gsame_loc ⨾ ⦗I⦘).
  { basic_solver. }
  arewrite (Cppo ⨾ ⦗I⦘ ⊆ Gppo).
  { rewrite I_in_D. eapply cert_ppo_D; eauto. }
  arewrite (Gppo ∩ Gsame_loc ⨾ ⦗I⦘ ⊆ ⦗D⦘ ⨾ Gppo ∩ Gsame_loc ⨾ ⦗I⦘).
  { apply dom_rel_helper.
    arewrite (Gppo ∩ Gsame_loc ⊆ Gppo).
    rewrite I_in_D. eapply dom_ppo_D; edone. }
  rewrite cert_rfi_eq.
  forward (eapply cert_rfi_D with (G:=G) (T:=T) (thread:=thread)); eauto.
  intros HH. sin_rewrite HH.
  arewrite_id ⦗D⦘. rewrite !seq_id_l.
  arewrite (Grfi ⊆ Grf).
  eapply rf_ppo_loc_I_in_I; eauto.
Unshelve.
all:auto.
Qed. 

Lemma dom_prop_cert:
  dom_rel (PROP certG sc ⨾ ⦗certT⦘) ⊆₁ certT. 
Proof using. 
  unfold PROP.
  transitivity (T ∩₁ action ↓₁ eq ta_cover ∪₁ eq ta_cover <*> (E ∩₁ NTid_ thread)).
  2: { clear.
       unfold certT. unionR left.
       unionL.
       all: iord_dom_unfolder; vauto. }
  match goal with
  | |- ?X ⊆₁ ?Y => remember X as A
  end.
  transitivity ((A ∩₁ event ↓₁ Tid_ thread) ∪₁ (A ∩₁ event ↓₁ NTid_ thread)).
  { clear. unfolder. ins. tauto. }
  unionL; [unionR left | unionR right].
  2: { arewrite (A ⊆₁ eq ta_cover <*> E); eauto.
       2: { clear. rewrite !set_pair_alt. basic_solver 1. }
       admit. }
  subst A.
  rewrite !seqA.
  arewrite (⦗action ↓₁ is_ta_propagate_to_G certG⦘ ⨾ ⦗certT⦘ ⊆
            ⦗action ↓₁ is_ta_propagate_to_G G⦘ ⨾ ⦗T⦘).
  { clear. unfold certT. iord_dom_unfolder; eauto 10. }
  intros [t1 e1] [HH E1T].
  red in E1T; ins.
  destruct HH as [[t2 e2] HH].
  apply seq_eqv_l in HH. destruct HH as [AA HH].
  red in AA; ins; subst t1.
  split.
  2: { clear. red; ins. }
  destruct HH as [[t3 e3] [[AA BB] HH]].
  apply seq_eqv_r in HH. destruct HH as [HH CT2].
  assert (t3 = t2 /\ e3 = e2) as [A1 A2].
  { clear - HH. inv HH. }
  subst t3. subst e3.
  destruct HH as [_ HH]. red in HH; ins.
  red in HH. destruct HH as [thread' [[HH DD] CC]].
  red in AA. ins.
  do 3 (apply seqA in AA).
  apply seq_eqv_r in AA. destruct AA as [AA _].
  assert (I e2) as IE2.
  { admit. (* since it is propagated *) }
  destruct AA as [e3 [AA CC23]].
  assert (Gco^? e3 e2) as CO32.
  { (* cert_co_I *) admit. }

  (* might be wrong... *)
  assert (T (ta_cover, e3)) as CT3.
  { (* via ICOH *) admit. }

  (* red in HH. desc. clear HH. red in HH0; ins. *)
  (* apply seq_eqv_l in HH. destruct HH as [_ HH]. *)
  (* apply seq_eqv_r in HH. destruct HH as [HH E2T]. *)
  (* red in E2T; ins. *)

  (* unfolder. ins. desc. *)


  (* rewrite !seqA. *)
  (* arewrite () *)

  (* rewrite !seqA. *)
  (* rewrite seq_eqvC, <- id_inter. *)
  (* rewrite inclusion_inter_l1. *)
  (* rewrite certG_same_props. *)
  (* arewrite (certT ∩₁ action ↓₁ is_ta_propagate_to_G G ⊆₁ *)
  (*               T ∩₁ action ↓₁ is_ta_propagate_to_G G). *)
  (* { clear. unfold certT. iord_dom_unfolder; eauto 10. } *)
  (* rewrite dom_rel_collect_event2. *)
  (* 2: { clear. unionL; iord_dom_unfolder. } *)
  (* rewrite set_collect_union. *)
  (* rewrite set_pair_cancel_action. *)
  (* transitivity (C ∪₁ E ∩₁ NTid_ thread); [|reflexivity]. *)
  (* arewrite (event ↑₁ (T ∩₁ action ↓₁ is_ta_propagate_to_G G) ⊆₁ propagated G T). *)
  (* rewrite propagated_in_issued; eauto. *)
  (* arewrite_id ⦗CW⦘. rewrite seq_id_l. *)

  (* arewrite (Cco^? ⨾ ⦗I⦘ ⊆ Gco^? ⨾ ⦗I⦘). *)
  (* { (* cert_co_I *) admit. } *)

Admitted. 

(* Lemma dom_prop_cert: *)
(*   dom_rel (PROP certG sc ⨾ ⦗certT⦘) ⊆₁ certT.  *)
(* Proof using.  *)
(*   unfold PROP. *)
(*   transitivity (T ∩₁ action ↓₁ eq ta_cover ∪₁ eq ta_cover <*> (E ∩₁ NTid_ thread)). *)
(*   2: { clear. *)
(*        unfold certT. unionR left. *)
(*        unionL. *)
(*        all: iord_dom_unfolder; vauto. } *)
(*   rewrite !seqA. *)
(*   rewrite seq_eqvC, <- id_inter. *)
(*   rewrite inclusion_inter_l1. *)
(*   rewrite certG_same_props. *)
(*   arewrite (certT ∩₁ action ↓₁ is_ta_propagate_to_G G ⊆₁ *)
(*                 T ∩₁ action ↓₁ is_ta_propagate_to_G G). *)
(*   { clear. unfold certT. iord_dom_unfolder; eauto 10. } *)
(*   rewrite dom_rel_collect_event2. *)
(*   2: { clear. unionL; iord_dom_unfolder. } *)
(*   rewrite set_collect_union. *)
(*   rewrite set_pair_cancel_action. *)
(*   transitivity (C ∪₁ E ∩₁ NTid_ thread); [|reflexivity]. *)
(*   arewrite (event ↑₁ (T ∩₁ action ↓₁ is_ta_propagate_to_G G) ⊆₁ propagated G T). *)
(*   rewrite propagated_in_issued; eauto. *)
(*   arewrite_id ⦗CW⦘. rewrite seq_id_l. *)
(*   match goal with *)
(*   | |- ?X ⊆₁ ?Y => remember X as A *)
(*   end. *)
(*   transitivity (A ∩₁ (Tid_ thread ∪₁ NTid_ thread)). *)
(*   { clear. rewrite tid_set_dec. basic_solver. } *)
(*   rewrite set_inter_union_r. *)
(*   unionL; [unionR left | unionR right]. *)
(*   2: { arewrite (A ⊆₁ E); eauto. *)
(*        admit. } *)
(*   arewrite (Cco^? ⨾ ⦗I⦘ ⊆ Gco^? ⨾ ⦗I⦘). *)
(*   { (* cert_co_I *) admit. } *)

(* Admitted.  *)

Lemma ICOH_cert (FAIR: mem_fair G):
  iord_coherent certG sc certT. 
Proof using All. 
  apply tls_iord_coherent_alt_old_implies_iord_coherent; auto.
  { by apply cert_imm_consistent. }
  { apply TICOH_cert_old. }
  { arewrite (IPROP certG ≡ IPROP G).
    { unfold IPROP. erewrite certG_same_props, cert_W; eauto. }
    transitivity (certT ∩₁ action ↓₁ eq ta_issue); [| basic_solver].
    assert (dom_rel (IPROP G ⨾ ⦗T⦘) ⊆₁ T ∩₁ action ↓₁ eq ta_issue) as DOM'.
    { apply iord_coh_implies_iord_simpl_coh' in ICOH; eauto.
      2: { by apply coherence_sc_per_loc. }
      rewrite <- ICOH at 2. assert (IPROP G ⊆ iord_simpl G sc) as <-. 
      { unfold iord_simpl. basic_solver. }
      unfold IPROP. basic_solver 10. } 
    etransitivity; [| etransitivity]; [| by apply DOM'| ].
    2: { rewrite tls_issue_certT. basic_solver. }
    unfold IPROP. rewrite !seqA, <- !id_inter.
    rewrite set_interC with (s' := certT), T_propagations_certT.
    basic_solver 10. }
  apply dom_prop_cert. 
Qed. 


Lemma cert_detour_rfe_D : (Cdetour ∪ (rfe certG)) ⨾ ⦗D⦘ ⊆ ⦗I⦘ ⨾ (Gdetour ∪ Grfe).
Proof using All.
  rewrite seq_union_l.
  forward (eapply cert_detour_D with (G:=G)); eauto. intros HH. rewrite HH.
  forward (eapply cert_rfe_D with (G:=G)); eauto. intros AA. rewrite AA. 
    by rewrite seq_union_r.
Qed.

Lemma dom_cert_detour_rfe_D : dom_rel ((Cdetour ∪ (rfe certG)) ⨾ ⦗D⦘) ⊆₁ I.
Proof using All.
  rewrite cert_detour_rfe_D.
  basic_solver.
Qed.

Lemma Crppo_in_rppo : rppo certG ⊆ Grppo.
Proof using SAME.
  unfold rppo.
  rewrite cert_sb, cert_R_ex, cert_W; eauto.
  unfold CertExecution2.certG. simpls.
Qed.

Lemma dom_data_Crfi_rmw_D_in_D : dom_rel ((Gdata ∪ Crfi ∪ Grmw)＊ ⨾ ⦗D⦘) ⊆₁ D.
Proof using Grfe_E WF WF_SC TCOH ICOH.
  cut ((Gdata ∪ Crfi ∪ Grmw)＊ ⨾ ⦗D⦘ ⊆ ⦗D⦘ ⨾ (fun _ _ => True)).
  { unfolder; intros HH; ins; desf. eapply HH; eauto. }
  apply rt_ind_right with (P:= fun r => r ⨾ ⦗D⦘).
  { eauto with hahn. }
  { basic_solver. }
  intros h HH; rewrite !seqA.
  arewrite ((Gdata ∪ Crfi ∪ Grmw) ⨾ ⦗D⦘ ⊆ ⦗D⦘ ⨾ (fun _ _ : actid => True)).
  2: { sin_rewrite HH. clear. basic_solver. }
  transitivity (⦗D⦘ ⨾ (Gdata ∪ Crfi ∪ Grmw) ⨾ ⦗D⦘).
  2: { clear. basic_solver. }
  apply dom_rel_helper. rewrite !seq_union_l, !dom_union. unionL.
  { eby eapply dom_data_D. }
  { rewrite cert_rfi_eq. erewrite cert_rfi_D; eauto. clear. basic_solver. }
  eby eapply dom_rmw_D.
Qed.

Lemma RCOH_cert
      (COMP_RMW_S : dom_rel (Grmw ⨾ ⦗S⦘) ⊆₁ codom_rel Grf)
      (ST_in_W_ex : S ∩₁ Tid_ thread \₁ I ⊆₁ GW_ex)
      (ISTex_rf_I : (I ∪₁ S ∩₁ Tid_ thread) ∩₁ GW_ex ⊆₁ codom_rel (⦗I⦘ ⨾ Grf ⨾ Grmw))
      (DOM_SB_S_rf_I :
         dom_rel (Gsb ⨾ ⦗I ∪₁ S ∩₁ Tid_ thread⦘) ∩₁ codom_rel (⦗I⦘ ⨾ Grf ⨾ ⦗GR_ex⦘ ⨾ Grmw)
                 ⊆₁ I ∪₁ S ∩₁ Tid_ thread)
      (FAIR: mem_fair G)
  :
  (* etc_coherent certG sc (mkETC (mkTC (C ∪₁ (E ∩₁ NTid_ thread)) I) *)
  (*                              (I ∪₁ S ∩₁ Tid_ thread)). *)
  reserve_coherent certG certT. 
Proof using All.
  assert (I ∪₁ S ∩₁ Tid_ thread ⊆₁ S) as IST_in_S.
  { rewrite I_in_S. basic_solver. }

(*  assert ((Grf ⨾ ⦗D⦘ ∪ new_rf) ⨾ Grmw ≡ Grf ⨾ Grmw) as QQ.
  { rewrite (dom_rel_helper dom_rmw_in_D).
    rewrite wf_new_rfE. clear. basic_solver 10. }*)
  constructor.
  (* all: unfold eissued, ecovered; simpls. *)
  all: rewrite ?covered_certT, ?issued_certT, ?reserved_certT. 
  { rewrite cert_E, (@issuedE G), ST_in_E; eauto. basic_solver.  }
  (* { arewrite (I ∪₁ S ∩₁ Tid_ thread ⊆₁ E ∩₁ W). *)
  (*   2: { unfold CertExecution2.certG. unfold acts_set. basic_solver. } *)
  (*   rewrite <- IST_new_co; try edone. *)
  (*   rewrite IST_in_cert_co_base; try edone. *)
  (*   basic_solver 10. } *)
  { eauto with hahn. }
  { rewrite cert_W_ex. generalize ST_in_W_ex.
    basic_solver. }
  { rewrite cert_F, cert_AcqRel, cert_sb, IST_in_S; eauto.
    rewrite <- F_in_C. rewrite wf_sbE. clear. basic_solver. }
  { rewrite cert_sb, cert_Acq, cert_R; eauto.


rewrite seq_union_l, dom_union; unionL.
2: by rewrite cert_rfe_eq, cert_rfe_alt; eauto; clear; basic_solver. 


arewrite (⦗R ∩₁ Acq⦘ ⊆ ⦗C⦘ ∪ ⦗Acq \₁ C⦘) at 1.
    { unfolder. ins. desf. destruct (classic (C y)); eauto. }

rewrite seq_union_l.
rewrite !seq_union_r, dom_union; unionL.
{ 
rewrite (wf_detourD); eauto.
rewrite cert_W; eauto.
arewrite_id ⦗CR⦘.
rewrite rmw_in_sb, rfi_in_sb, detour_in_sb; eauto.

rewrite cert_sb.
generalize (@sb_trans G); ins; relsf.
rewrite <- w_covered_issued at 2; eauto.
seq_rewrite sb_covered; eauto.
clear; basic_solver 12.
}

rewrite rtE, ct_end.
seq_rewrite rt_seq_swap.
rewrite !seqA.


arewrite ((⦗fun _ : actid => True⦘ ∪ Grmw ⨾ (Crfi ⨾ Grmw)＊ ⨾ Crfi)
     ⨾ ⦗Acq \₁ C⦘ ⊆ (⦗fun _ : actid => True⦘ ∪ Grmw ⨾ (Crfi ⨾ Grmw)＊ ⨾ Crfi ⨾ ⦗Acq⦘ ⨾ ⦗Acq \₁ C⦘)
     ⨾ ⦗Acq \₁ C⦘).
basic_solver 21.

rewrite cert_rfi_eq.

forward (eapply cert_rfi_to_Acq_in_Grfi with (G:=G)); eauto.
intro AA; sin_rewrite AA; clear AA.


forward (eapply cert_rfi_Grmw_rt_in_Grfi_Grmw with (G:=G)); eauto.
intro AA; sin_rewrite AA; clear AA.

    assert (BB: Grmw ⨾ (Grfi ⨾ Grmw)＊ ⨾ Grfi ⊆ (Grmw ⨾ Grfi)⁺).
    { seq_rewrite <- rt_seq_swap.
      rewrite !seqA.
      remember (Grmw ⨾ Grfi) as Y.
      apply ct_end. }

rewrite BB; clear BB.

rewrite <- rtE.

forward (eapply cert_detour_R_Acq' with (G:=G)); eauto.
basic_solver 12.
}
  { rewrite cert_W_ex, cert_xacq, cert_sb, IST_in_S; eauto. }
  { unfold dom_sb_S_rfrmw. simpls.
    rewrite cert_sb, cert_R_ex; eauto.
    rewrite !seqA.
    arewrite (cert_rf ⨾ ⦗GR_ex⦘ ⨾ Grmw ⊆ Grf ⨾ ⦗GR_ex⦘ ⨾ Grmw); auto.
    2: { rewrite reserved_certT. auto. }
    arewrite (⦗GR_ex⦘ ⊆ ⦗GR_ex⦘ ⨾ ⦗GR_ex⦘) at 1.
    { clear. basic_solver. }
    rewrite (dom_l (wf_rmwE WF)) at 1.
    seq_rewrite <- (@id_inter _ _ E).
    rewrite Rex_in_D; eauto.
    seq_rewrite seq_eqvC. rewrite !seqA.
    arewrite (cert_rf ⨾ ⦗D⦘ ⊆ Grf ⨾ ⦗D⦘); [|clear; basic_solver].
    eapply cert_rf_D; eauto. }
  { rewrite Crppo_in_rppo.
    arewrite (Grppo ⨾ ⦗I ∪₁ S ∩₁ Tid_ thread⦘ ⊆
              ⦗D⦘ ⨾ Grppo ⨾ ⦗I ∪₁ S ∩₁ Tid_ thread⦘).
    { apply dom_rel_helper.
      rewrite IST_in_S.
      apply dom_rppo_S_in_D. }
    arewrite ((Gdata ∪ Crfi ∪ Grmw)＊ ⨾ ⦗D⦘ ⊆ ⦗D⦘ ⨾ (Gdata ∪ Crfi ∪ Grmw)＊ ⨾ ⦗D⦘).
    { apply dom_rel_helper.
      eapply dom_data_Crfi_rmw_D_in_D. }
    rewrite <- !seqA.
    do 4 rewrite AuxRel.dom_seq.
    apply dom_cert_detour_rfe_D. }
  { rewrite IST_in_S.
    rewrite (dom_rel_helper COMP_RMW_S).
    rewrite rfi_union_rfe, codom_union, id_union.
    rewrite !seq_union_l, !seq_union_r. rewrite dom_union.
    unionL.
    2: { rewrite <- dom_rel_eqv_dom_rel.
         arewrite (dom_rel (⦗codom_rel Grfe⦘ ⨾ Grmw ⨾ ⦗S⦘) ⊆₁ D).
         2: { rewrite <- dom_cert_detour_rfe_D.
              clear. basic_solver 10. }
         rewrite dom_eqv1. unfold Cert_D.D. by unionR right. }
    unfold detour.
    rewrite cert_rfe_eq. rewrite Grfi_in_cert_rfi; eauto.
    unfold Cert_rf.cert_rfe, Cert_rf.cert_rfi.
    unfolder. ins. desf.
    exfalso. assert (z0 = x0); subst; auto.
    eapply cert_rff with (G:=G); eauto. }
  transitivity (codom_rel (⦗I⦘ ⨾ cert_rf ⨾ Grmw ⨾ ⦗S⦘)).
  2: { clear. basic_solver 10. }
  rewrite cert_rmw_S_in_rf_rmw_S; auto.
  rewrite cert_W_ex.
  rewrite <- !seqA. rewrite codom_eqv1.
  apply set_subset_inter_r. split.
  2: { rewrite IST_in_S. clear. basic_solver. }
  rewrite ISTex_rf_I. by rewrite !seqA.
Qed.

End CertExec_tc.
