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

From hahnExt Require Import HahnExt.
(* From imm Require Import TraversalConfig. *)
(* From imm Require Import TraversalConfigAlt. *)
(* From imm Require Import TraversalConfigAltOld. *)
Require Import ExtTraversalConfig.
From imm Require Import TraversalOrder.
From imm Require Import TLSCoherency.
From imm Require Import IordCoherency.
From imm Require Import SimClosure. 
From imm Require Import TlsEventSets.
From hahnExt Require Import HahnExt.
From imm Require Import EventsTraversalOrder.
Require Import CertT.

Set Implicit Arguments.

Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'NTid_' t" := (fun x => tid x <> t) (at level 1).

Section CertExec_D.

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

Hypothesis WF : Wf G.
Hypothesis WF_SC : wf_sc G sc.
Hypothesis RELCOV : W ∩₁ Rel ∩₁ I ⊆₁ C.

(* Hypothesis TCCOH : tc_coherent G sc T. *)
(* Hypothesis TCOH : tls_coherent G T. *)
(* Hypothesis ICOH : iord_coherent G sc T. *)

Hypothesis ACYC_EXT : acyc_ext G sc.
Hypothesis CSC : coh_sc G sc.
Hypothesis COH : coherence G.
Hypothesis AT : rmw_atomicity G.

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

(* Hypothesis TCCOH_rst_new_T : tc_coherent G sc (mkTC (C ∪₁ (E ∩₁ NTid_ thread)) I). *)
Hypothesis TCOH_rst_new_T : tls_coherent G (certT G T thread).
Hypothesis ICOH_rst_new_T : iord_coherent G sc (certT G T thread).

Hypothesis S_in_W : S ⊆₁ W.
Hypothesis RPPO_S : dom_rel ((Gdetour ∪ Grfe) ⨾ (Gdata ∪ Grfi ∪ Grmw)＊ ⨾ Grppo ⨾ ⦗S⦘) ⊆₁ I.
Hypothesis RMW_S : dom_rel ((Gdetour ∪ Grfe) ⨾ Grmw ⨾ ⦗S⦘) ⊆₁ I.
Hypothesis ST_in_E : S ∩₁ Tid_ thread ⊆₁ E.
Hypothesis I_in_S : I ⊆₁ S.
Hypothesis C_in_E : C ⊆₁ E. 
Hypothesis I_in_E : I ⊆₁ E. 

Hypothesis F_in_C : E ∩₁ F ∩₁ Acq/Rel ⊆₁ C.

Hypothesis S_I_in_W_ex : (S ∩₁ Tid_ thread) \₁ I ⊆₁ W_ex G.

Hypothesis ETC_DR_R_ACQ_I : dom_rel ((Gdetour ∪ Grfe) ⨾ (Grmw ⨾ Grfi)＊ ⨾ ⦗R∩₁Acq⦘ ⨾ Gsb ⨾ ⦗S⦘) ⊆₁ I.

(******************************************************************************)
(**  the set D   *)
(******************************************************************************)

Definition D := C ∪₁ I ∪₁ (E ∩₁ NTid_ thread) ∪₁
  dom_rel (Grfi^? ⨾ Gppo ⨾ ⦗ I ⦘) ∪₁ 
  dom_rel ((Gdata ∪ Grfi ∪ Grmw)＊ ⨾ Grppo ⨾ ⦗ S ⦘) ∪₁ 
  codom_rel (⦗I⦘ ⨾ Grfi) ∪₁ codom_rel (Grfe ⨾ ⦗ R ∩₁ Acq ⦘)
  ∪₁ codom_rel Grfe ∩₁ dom_rel (Grmw ⨾ ⦗ S ⦘).

Lemma C_in_D : C ⊆₁ D.
Proof using. unfold D; basic_solver 12. Qed.
Lemma I_in_D : I ⊆₁ D.
Proof using. unfold D; basic_solver 12. Qed.
Lemma D_in_E : D ⊆₁ E.
Proof using WF I_in_E C_in_E. 
  unfold D.
  arewrite ((Gdata ∪ Grfi ∪ Grmw)＊ ⨾ Grppo ⊆ ⦗E⦘ ⨾ (Gdata ∪ Grfi ∪ Grmw)＊ ⨾ Grppo ⨾ ⦗E⦘).
  { rewrite (wf_rppoE WF) at 1.
    rewrite rtE. rewrite !seq_union_l, !seq_union_r, !seq_id_l.
    apply union_mori; [done|].
    rewrite (dom_l (wf_dataE WF)) at 1.
    rewrite (dom_l (wf_rfiE WF)) at 1.
    rewrite (dom_l (wf_rmwE WF)) at 1.
    rewrite <- !seq_union_r.
    rewrite inclusion_ct_seq_eqv_l.
    basic_solver. }

  rewrite (wf_ppoE WF), (wf_rfiE WF), (wf_rfeE WF), C_in_E, I_in_E; eauto.
  basic_solver.
Qed. 

Local Lemma S_W_S : ⦗S⦘ ⊆ ⦗W⦘ ⨾ ⦗S⦘.
Proof using S_in_W.
  generalize S_in_W. basic_solver.
Qed.

Lemma E_ntid_in_D : E ∩₁ NTid_ thread ⊆₁ D.
Proof using. unfold D. basic_solver 10. Qed.

Lemma D_init : E ∩₁ is_init ⊆₁ D.
Proof using TCOH_rst_new_T.
  rewrite set_interC, init_covered; eauto.
  rewrite covered_certT. rewrite C_in_D.
  apply set_subset_union_l. split; [done| ]. unfold D. basic_solver 10. 
Qed.


Lemma dom_rppo_S_in_D : dom_rel (Grppo ⨾ ⦗S⦘) ⊆₁ D.
Proof using.
  unfold D. basic_solver 21.
Qed.

Lemma dom_data_rfi_rppo_S_in_D :
  dom_rel ((Gdata ∪ Grfi ∪ Grmw)＊ ⨾ Grppo ⨾ ⦗S⦘) ⊆₁ D.
Proof using.
  unfold D. basic_solver 21.
Qed.

Lemma E_minus_D_in_tid : E \₁ D ⊆₁ Tid_ thread.
Proof using. 
arewrite (E ⊆₁ E ∩₁ Tid_ thread ∪₁ E ∩₁ NTid_ thread).
{ clear; unfolder; ins; desf; tauto. }
rewrite E_ntid_in_D.
clear; basic_solver.
Qed.

(* Lemma ICOH':  *)
(*   iord_coherent G sc T.  *)
(* Proof using.  *)
(*   clear -ICOH_rst_new_T. red. red in ICOH_rst_new_T. *)
(*   iord_dom_unfolder. *)
(*   { unfold G at ICOH_rst_new_T.  *)
(*   unfolder. ins. destruct H as [[a e] [IORD Tae]]. *)
(*   destruct a. *)
(*   { revert IORD.   *)

(* TODO: move*)
Lemma C_in_certC:
  C ⊆₁ covered (certT G T thread). 
Proof using. rewrite covered_certT. basic_solver. Qed. 

(* TODO: move*)
Lemma ENT_D:
  E ∩₁ NTid_ thread ⊆₁ D. 
Proof using. unfold D. basic_solver 10. Qed. 

(* TODO: move*)
Lemma covered_cert_D: covered (certT G T thread) ⊆₁ D. 
Proof using.
  rewrite covered_certT.
  rewrite C_in_D, ENT_D. basic_solver. 
Qed. 

Lemma dom_sb_C_in_D:
  dom_rel (Gsb ⨾ ⦗C⦘) ⊆₁ D. 
Proof using WF TCOH_rst_new_T ICOH_rst_new_T. 
  rewrite C_in_certC.
  rewrite dom_sb_covered; eauto.
  apply covered_cert_D. 
Qed. 

Lemma dom_addr_in_D : dom_rel Gaddr ⊆₁ D.
Proof using WF E_to_S S_in_W TCOH_rst_new_T ICOH_rst_new_T.
  rewrite (dom_r (wf_addrE WF)).
  rewrite E_to_S.
  rewrite id_union; relsf; unionL; splits.
  { rewrite (addr_in_sb WF). apply dom_sb_C_in_D. }
  rewrite dom_rel_eqv_dom_rel.
  rewrite S_W_S.
  sin_rewrite addr_sb_W_in_rppo.
  apply dom_rppo_S_in_D.
Qed.

Lemma dom_ctrl_in_D : dom_rel Gctrl ⊆₁ D.
Proof using WF E_to_S S_in_W TCOH_rst_new_T ICOH_rst_new_T.
  rewrite (dom_r (wf_ctrlE WF)).
  rewrite E_to_S.
  rewrite id_union; relsf; unionL; splits.
  { rewrite (ctrl_in_sb WF). apply dom_sb_C_in_D. }
  rewrite dom_rel_eqv_dom_rel.
  rewrite S_W_S.
  arewrite (Gctrl ⨾ Gsb^? ⊆ Gctrl).
  { generalize (ctrl_sb WF). basic_solver 21. }
  sin_rewrite ctrl_W_in_rppo.
  apply dom_rppo_S_in_D.
Qed.

Lemma dom_frmw_in_D : dom_rel Grmw_dep ⊆₁ D.
Proof using WF E_to_S S_in_W TCOH_rst_new_T ICOH_rst_new_T.
  rewrite (dom_r (wf_rmw_depE WF)).
  rewrite E_to_S.
  rewrite id_union; relsf; unionL; splits.
  { rewrite (rmw_dep_in_sb WF). apply dom_sb_C_in_D. }
  rewrite dom_rel_eqv_dom_rel.
  rewrite S_W_S.
  rewrite (dom_r (wf_rmw_depD WF)), !seqA.
  arewrite (⦗GR_ex⦘ ⨾ Gsb^? ⨾ ⦗W⦘ ⊆ Gsb ⨾ ⦗W⦘).
  { clear. type_solver. }
  sin_rewrite (rmw_dep_sb_W_in_rppo WF).
  apply dom_rppo_S_in_D.
Qed.

Lemma dom_rmw_D : dom_rel (Grmw ⨾ ⦗D⦘) ⊆₁ D.
Proof using sc WF TCOH_rst_new_T ICOH_rst_new_T.
  unfold D at 1. 
  rewrite !id_union; relsf; unionL; splits.
  { rewrite (rmw_in_sb WF) at 1. apply dom_sb_C_in_D. }
  { rewrite (rmw_in_ppo WF) at 1.
    unfold D. clear. basic_solver 12. }
  { unfold D. unionR left -> left -> left -> left.
    unionR left -> right.
    rewrite (dom_l (wf_rmwE WF)) at 1. 
    rewrite (wf_rmwt WF) at 1.
    clear. unfold same_tid. unfolder. intros. desf. split; congruence. }
  { rewrite dom_rel_eqv_dom_rel.
    rewrite (rmw_in_ppo WF) at 1.
    rewrite (dom_r (@wf_ppoD G)) at 1.
    rewrite (dom_l (@wf_ppoD G)) at 2.
    unionR left -> left -> left -> left. 
    unionR right.
    generalize (@ppo_rfi_ppo G).
    clear; type_solver 21. }
  { unionR left -> left -> left -> right.
    rewrite dom_rel_eqv_dom_rel.
    rewrite <- inclusion_t_rt at 2.
    rewrite ct_begin.
    clear; basic_solver 21. }
  { rewrite (dom_r (wf_rmwD WF)).
    rewrite (dom_r (wf_rfiD WF)).
    clear; type_solver. }
  { rewrite (dom_r (wf_rmwD WF)).
    clear; type_solver. }
  rewrite (wf_rmwD WF).
  clear; type_solver.
Qed.

Lemma Rex_in_D : GR_ex ∩₁ E ⊆₁ D.
Proof using urr_helper_C urr_helper detour_Acq_E W_hb_sc_hb_to_I_NTid
S_in_W RELCOV IT_new_co F_in_C E_to_S E_F_AcqRel_in_C
ETC_DR_R_ACQ_I COMP_RPPO COMP_NTID COMP_C
COMP_ACQ.
  rewrite E_to_S.
  rewrite set_inter_union_r. unionL.
  { rewrite <- C_in_D. clear. basic_solver. }
  rewrite <- dom_eqv1.
  arewrite (⦗S⦘ ⊆ ⦗W⦘ ⨾ ⦗S⦘).
  { rewrite <- S_in_W. clear. basic_solver. }
  rewrite crE. rewrite seq_union_l, seq_union_r, dom_union. unionL.
  { type_solver. }
  sin_rewrite R_ex_sb_W_in_rppo.
  unfold D. rewrite rtE.
  clear. basic_solver 20.
Qed.

Lemma dom_R_ex_sb_D : 
  dom_rel (⦗GR_ex⦘ ⨾ Gsb ⨾ ⦗W⦘ ⨾ ⦗D⦘) ⊆₁ D.
Proof using All.
  unfold D at 1. 
  rewrite !id_union, !seq_union_r, !dom_union. unionL; splits.
  { rewrite <- dom_sb_C_in_D. basic_solver. }
  { rewrite I_in_S at 1. unfold D. unfold rppo.
    unionR left -> left -> left -> right.
    rewrite rtE.
    basic_solver 21. }
  { unionR left -> left -> left -> left.
    unionR left -> right.
    rewrite (dom_l (@wf_sbE G)) at 1.
    arewrite ((GR_ex) ⊆₁ set_compl Init).
    { rewrite (init_w WF), R_ex_in_R; type_solver. }
    generalize (@ninit_sb_same_tid G).
    unfold same_tid; unfolder; ins; desf; splits; eauto.
    erewrite H; eauto. }
  { unionR left -> left -> left -> right.
    arewrite (Grfi ⊆ Gsb) at 1.
    rewrite (ppo_in_sb WF) at 1.
    rewrite I_in_S.
    arewrite (⦗S⦘ ⊆ ⦗S⦘ ⨾ ⦗W⦘) at 1.
    by generalize S_in_W; basic_solver.
    unfold rppo.
    generalize (@sb_trans G); basic_solver 21. }
  { unionR left -> left -> left -> right.
    arewrite (Grfi ⊆ Gsb) at 1.
    rewrite (data_in_sb WF) at 1.
    rewrite (rmw_in_sb WF) at 1.
    rewrite (rppo_in_sb WF) at 1.
    arewrite (⦗S⦘ ⊆ ⦗S⦘ ⨾ ⦗W⦘) at 1.
    by generalize S_in_W; basic_solver.
    unfold rppo.
    arewrite ((Gsb ∪ Gsb ∪ Gsb)＊ ⊆ Gsb^?).
    by generalize (@sb_trans G); ins; relsf.
    rewrite rtE.
    generalize (@sb_trans G); basic_solver 32. }
  { rewrite (dom_r (wf_rfiD WF)).
    type_solver. }
  { unfold D. rewrite (dom_r (wf_rmwD WF)).
    type_solver. }
  rewrite (wf_rmwD WF).
  clear; type_solver.
Qed.

Lemma dom_R_ex_fail_sb_D : 
  dom_rel (⦗GR_ex \₁ dom_rel Grmw⦘ ⨾ Gsb ⨾ ⦗W⦘ ⨾ ⦗D⦘) ⊆₁ D.
Proof using All. rewrite <- dom_R_ex_sb_D at 2. basic_solver 10. Qed.

Lemma dom_detour_D : dom_rel (Gdetour ⨾ ⦗D⦘) ⊆₁ I.
Proof using WF WF_SC  detour_Acq_E detour_E RPPO_S RMW_S CSC COH AT ACYC_EXT TCOH_rst_new_T ICOH_rst_new_T.
  unfold D.
  rewrite !id_union; relsf; unionL; splits.
  { rewrite (dom_l (wf_detourD WF)).
    rewrite detour_in_sb.
    rewrite <- issued_certT, C_in_certC.
    rewrite seqA, dom_eqv1.
    rewrite dom_sb_covered; eauto.
    eapply w_covered_issued; eauto. }
  { rewrite (dom_r (wf_detourD WF)).
    rewrite <- issued_certT. erewrite issuedW at 1; eauto. clear. type_solver. }
  { apply detour_E. }
  { rewrite dom_rel_eqv_dom_rel.
    rewrite crE; relsf; unionL; splits.
    2: by rewrite (dom_r (wf_detourD WF)), (dom_l (wf_rfiD WF)); clear; type_solver.
    rewrite <- issued_certT. 
    erewrite <- dom_detour_rfe_ppo_issued at 2; eauto.
    apply dom_rel_mori. repeat (apply seq_mori; try basic_solver). }
  { rewrite dom_rel_eqv_dom_rel.
    etransitivity.
    2: by apply RPPO_S.
    clear. basic_solver 15. }
  { rewrite dom_rel_eqv_codom_rel, transp_seq; relsf.
    sin_rewrite (detour_transp_rfi WF); rels. }
  { rewrite (dom_r (wf_rfeE WF)).
    relsf.
    transitivity (dom_rel (Gdetour ⨾ ⦗R ∩₁ Acq⦘ ⨾ ⦗E⦘)).
    { clear. basic_solver 21. }
    generalize detour_Acq_E. clear. basic_solver 21. }
  etransitivity.
  2: by apply RMW_S.
  clear. basic_solver 15.
Qed.

Lemma dom_data_D: dom_rel (Gdata ⨾ ⦗D⦘) ⊆₁ D.
Proof using WF TCOH_rst_new_T ICOH_rst_new_T. 
  unfold D at 1. 
  rewrite !id_union; relsf; unionL; splits.
  { rewrite (data_in_sb WF) at 1. apply dom_sb_C_in_D. }
  { rewrite data_in_ppo; auto.
    unfold D. clear. basic_solver 12. }
  { rewrite (data_in_sb WF) at 1.
    rewrite (dom_l (@wf_sbE G)) at 1.
    rewrite sb_tid_init' at 1; relsf; unionL; split.
    { unionR left -> left -> left -> left.
      unionR left -> right.
      unfold same_tid; unfolder; ins; desf; intuition auto with *. }
    arewrite (⦗E⦘ ⨾ ⦗fun a : actid => is_init a⦘ ⊆ ⦗D⦘).
    { generalize D_init. clear. basic_solver. }
    arewrite (dom_rel (⦗D⦘ ⨾ Gsb ⨾ ⦗E ∩₁ NTid_ thread⦘) ⊆₁ D) by basic_solver. }
  { rewrite dom_rel_eqv_dom_rel.
    rewrite crE at 1; relsf; unionL; splits.
    { rewrite (dom_r (wf_dataD WF)), (dom_l (@wf_ppoD G)).
      clear. type_solver. }
    rewrite (data_in_ppo WF) at 1.
    sin_rewrite ppo_rfi_ppo. unfold D. clear. basic_solver 21. }
  { rewrite dom_rel_eqv_dom_rel.
    arewrite (Gdata ⨾ (Gdata ∪ Grfi ∪ Grmw)＊ ⊆ (Gdata ∪ Grfi ∪ Grmw)＊).
    2: by eauto 10 with hahn.
    arewrite (Gdata ⊆ Gdata ∪ Grfi ∪ Grmw).
    rewrite <- ct_begin.
    apply inclusion_t_rt. }
  { rewrite (dom_r (wf_dataD WF)), (dom_r (wf_rfiD WF)). clear. type_solver. }
  { rewrite (dom_r (wf_dataD WF)), (dom_r (wf_rfeD WF)). clear. type_solver. }
  rewrite (dom_r (wf_dataD WF)), (dom_r (wf_rfeD WF)). clear. type_solver.
Qed.

(* Lemma dom_sb_F_AcqRel_in_C : dom_rel (Gsb ⨾ ⦗F ∩₁ Acq/Rel⦘) ⊆₁ C. *)
(* Proof using  F_in_C WF . *)
(*   rewrite (dom_r (@wf_sbE G)), !seqA. dom_sb *)

(*     covered_certT *)
(*   arewrite (⦗E⦘ ⨾ ⦗F ∩₁ Acq/Rel⦘ ⊆ ⦗C⦘). *)
(*   { revert F_in_C; clear; basic_solver. } *)
(*   generalize (dom_sb_covered WF TCOH ICOH). clear. basic_solver 21. *)
(* Qed. *)

Lemma dom_sb_F_AcqRel_in_D : dom_rel (Gsb ⨾ ⦗F ∩₁ Acq/Rel⦘) ⊆₁ D.
Proof using WF F_in_C TCOH_rst_new_T ICOH_rst_new_T.
  rewrite <- dom_sb_C_in_D. rewrite (dom_r (@wf_sbE G)).
  generalize F_in_C. basic_solver 10.
Qed.

Lemma dom_sb_F_Acq_in_D : dom_rel (Gsb ⨾ ⦗F ∩₁ Acq⦘) ⊆₁ D.
Proof using WF F_in_C TCOH_rst_new_T ICOH_rst_new_T.
  arewrite (Acq ⊆₁ Acq/Rel) by (clear; mode_solver).
  apply dom_sb_F_AcqRel_in_D.
Qed.

Lemma dom_sb_F_Rel_in_D : dom_rel (Gsb ⨾ ⦗F ∩₁ Rel⦘) ⊆₁ D.
Proof using  WF F_in_C TCOH_rst_new_T ICOH_rst_new_T.
  arewrite (Rel ⊆₁ Acq/Rel) by (clear; mode_solver).
  apply dom_sb_F_AcqRel_in_D.
Qed.

Lemma R_Acq_codom_rfe : (R ∩₁ Acq ∩₁ codom_rel (Grfe)) ⊆₁ D.
Proof using.
  unfold D. clear. basic_solver 21.
Qed.

(* It doesn't hold anymore since W_ex are
   neither necessarily issued, nor necessarily have the same value as in
   the original graph. *)
(* Lemma R_Acq_codom_W_ex_rfi : (R ∩₁ Acq ∩₁ codom_rel (⦗GW_ex⦘ ⨾ Grfi)) ⊆₁ D. *)
(* Proof using. *)
(*   rewrite (dom_l (wf_rfiE WF)). *)
(*   arewrite (⦗GW_ex⦘ ⨾ ⦗E⦘ ⊆ ⦗GW_ex ∩₁ E⦘) by basic_solver. *)
(*   rewrite W_ex_E. *)
(*   unfold D. *)
(*   basic_solver 21. *)
(* Qed. *)

Lemma dom_rfi_D : dom_rel (Grfi ⨾ ⦗D⦘) ⊆₁ D.
Proof using WF TCOH_rst_new_T ICOH_rst_new_T.
  unfold D at 1.
  rewrite !id_union, !seq_union_r, !dom_union.
  unionL.
  { arewrite (Grfi ⊆ Grf). rewrite <- I_in_D.
    rewrite <- issued_certT, C_in_certC. 
    eapply dom_rf_covered; eauto. }
  { rewrite <- issued_certT. 
    erewrite (dom_r (wf_rfiD WF)), issuedW at 1; eauto. clear. type_solver. }
  { arewrite (Grfi ⊆ Gsb).
    rewrite (dom_l (@wf_sbE G)).
    rewrite sb_tid_init'; relsf; unionL; splits.
    { unfold D.
      unionR left -> left -> left -> left.
      unionR left -> right.
      unfold same_tid. clear. unfolder. intros. desc. split; congruence. }
    transitivity D; [|unfold D; clear; basic_solver 21].
    rewrite <- D_init; clear; basic_solver. }
  { rewrite dom_rel_eqv_dom_rel.
    rewrite crE at 1; relsf; unionL; splits.
    { unfold D. clear. basic_solver 12. }
    rewrite (dom_r (wf_rfiD WF)), (dom_l (wf_rfiD WF)). clear. type_solver. }
  { rewrite dom_rel_eqv_dom_rel.
    arewrite (Grfi ⨾ (Gdata ∪ Grfi ∪ Grmw)＊ ⊆ (Gdata ∪ Grfi ∪ Grmw)＊).
    2: by apply dom_data_rfi_rppo_S_in_D.
    rewrite rt_begin at 2. unionR right.
    clear. basic_solver 10. }
  { unfold D. ie_unfolder; unfolder; ins; desf.
    assert (x=z); subst; eauto 15.
    eapply WF; clear; basic_solver. }
  { ie_unfolder; unfolder; ins; desc.
    assert (x=x0); subst.
    eapply WF; clear; basic_solver.
    exfalso; auto. }
  ie_unfolder; unfolder; ins; desc.
  assert (x=x0); subst.
  eapply WF; clear; basic_solver.
  exfalso; auto.
Qed.

Lemma dom_rf_D : dom_rel (Grf ⨾ ⦗D⦘) ⊆₁ D.
Proof using WF Grfe_E  TCOH_rst_new_T ICOH_rst_new_T.
  rewrite rfi_union_rfe at 1.
  relsf; unionL; splits.
  { apply dom_rfi_D. }
  revert Grfe_E. generalize I_in_D. clear. basic_solver.
Qed.

Lemma dom_Grfi_nD_in_thread :
  dom_rel (Grfi ⨾ ⦗set_compl D⦘) ⊆₁ Tid_ thread.
Proof using WF TCOH_rst_new_T.
  unfolder. intros x [y [RFI ND]].
  destruct (classic (I x)) as [IX|NIX].
  { exfalso. apply ND.
    do 2 red. left. left. right. basic_solver 10. }
  destruct RFI as [RF SB].
  apply (wf_rfE WF) in RF.
  unfolder in RF. desf.
  assert (~ is_init x) as NINX.
  { intros II. apply NIX. eapply issued_certT.  
    eapply init_issued; eauto. by split. }
  apply sb_tid_init in SB. desf.
  apply NNPP. intros NTX.
  assert (tid y <> thread) as NTY.
  { intros HH. apply NTX. by rewrite <- HH. }
  apply ND. red. do 5 left. right. by split.
Qed.

Lemma complete_D : D ∩₁ R  ⊆₁ codom_rel Grf.
Proof using All. 
  unfold D.
  rewrite !set_inter_union_l.
  unionL.
  { apply COMP_C. }
  { erewrite <- issued_certT. erewrite (issuedW ); eauto. type_solver. }
  { apply COMP_NTID. }
  { rewrite crE; relsf; unionL; splits.
    { rewrite COMP_PPO. clear. basic_solver. }
    rewrite (dom_l (wf_rfiD WF)). clear. type_solver. }
  { rewrite set_interC.
    rewrite <- dom_eqv1.
    apply COMP_RPPO. }
  all: ie_unfolder; clear; basic_solver.
Qed.

Lemma dom_ppo_D_helper : 
  dom_rel ((Gdata ∪ Gctrl ∪ Gaddr ⨾ Gsb^? ∪ Grfi ∪ Grmw ∪ Grmw_dep ⨾ Gsb^?)⁺ ⨾ ⦗D⦘) ⊆₁ D.
Proof using All.
cut ((Gdata ∪ Gctrl ∪ Gaddr ⨾ Gsb^? ∪ Grfi ∪ Grmw ∪ Grmw_dep ⨾ Gsb^?)⁺ ⨾ ⦗D⦘ ⊆ ⦗D⦘ ⨾ (fun _ _ => True)).
by unfolder; ins; desf; eapply H; eauto.
rewrite (inclusion_t_rt).
apply rt_ind_right with (P:= fun r =>  r ⨾ ⦗D⦘).
by eauto with hahn.
basic_solver.
intros k H; rewrite !seqA.
relsf; unionL.
- rewrite (dom_rel_helper dom_data_D); sin_rewrite H; basic_solver.
- rewrite (dom_rel_helper dom_ctrl_in_D); rewrite !seqA; sin_rewrite H; basic_solver.
- rewrite (dom_rel_helper dom_addr_in_D); rewrite !seqA; sin_rewrite H; basic_solver.
- rewrite (dom_rel_helper dom_rfi_D); sin_rewrite H; basic_solver.
- rewrite (dom_rel_helper dom_rmw_D); sin_rewrite H; basic_solver.
- rewrite (dom_rel_helper dom_frmw_in_D); rewrite !seqA; sin_rewrite H; basic_solver.
Qed.

Lemma dom_ppo_D : dom_rel (Gppo ⨾ ⦗D⦘) ⊆₁ D.
Proof using All.
cut (Gppo ⨾ ⦗D⦘ ⊆ ⦗D⦘ ⨾ (fun _ _ => True)).
by unfolder; ins; desf; eapply H; eauto.
unfold ppo.
arewrite_id ⦗R⦘.
rels.
rewrite path_ut_first.
rewrite !seqA.
arewrite (Gsb ⨾ (Gdata ∪ Gctrl ∪ Gaddr ⨾ Gsb^? ∪ Grfi ∪ Grmw
        ∪ Grmw_dep ⨾ Gsb^? ∪ ⦗GR_ex⦘ ⨾ Gsb)＊ ⊆ Gsb).
{ arewrite_id ⦗GR_ex⦘.
  rewrite (data_in_sb WF), (addr_in_sb WF), (ctrl_in_sb WF).
  rewrite (rmw_dep_in_sb WF), (rmw_in_sb WF).
  arewrite (Grfi ⊆ Gsb).
  generalize (@sb_trans G); ins; relsf. }
relsf; unionL.
{ arewrite_id ⦗W⦘.
rels.
rewrite (dom_rel_helper dom_ppo_D_helper).
basic_solver. }

rewrite !seqA.
rewrite (dom_rel_helper dom_R_ex_sb_D).
rewrite rtE; relsf.
seq_rewrite (dom_rel_helper dom_ppo_D_helper).
basic_solver 12.
Qed.

Lemma dom_ppo_CI : dom_rel (Gppo ⨾ ⦗C ∪₁ I⦘) ⊆₁ D.
Proof using All.
  rewrite C_in_D, I_in_D; relsf.
  apply dom_ppo_D.
Qed.

Lemma dom_ar_int_D_helper : dom_rel (⦗R ∩₁ set_compl Acq⦘ ⨾ Gar_int ⨾ ⦗I⦘) ⊆₁ D.
Proof using All.
  unfold ar_int. rewrite (wf_detourD WF). rewrite (W_ex_in_W WF).
  rewrite !seq_union_l, !seq_union_r. rewrite !dom_union. unionL.
  3-5: clear; type_solver 10.
  2: { unfold D. clear. basic_solver 20. }
  unfold bob, fwbob.
  rewrite !seq_union_l, !seq_union_r. rewrite !dom_union. unionL.
  3: rewrite <- issued_certT; erewrite issuedW; eauto. 
  2-5: clear; type_solver 10.
  rewrite !seqA, <- id_inter. rewrite RELCOV.
  rewrite <- dom_sb_C_in_D. basic_solver. 
Qed.

Hypothesis FACQREL : E ∩₁ F ⊆₁ Acq/Rel.

Lemma dom_ar_int_D:
  dom_rel (Gar_int⁺ ⨾ ⦗I⦘) ⊆₁ D ∪₁ R ∩₁ Acq.
Proof using All.
  rewrite (dom_l (wf_ar_intE WF)).
  rewrite inclusion_ct_seq_eqv_l.
  rewrite E_in_RW_F_AcqRel; auto. rewrite !seqA.
  rewrite !id_union, !seq_union_l, !dom_union. unionL.
  3: { rewrite (ar_int_in_sb WF). rewrite ct_of_trans; [|by apply sb_trans].
       rewrite <- C_in_D. rewrite wf_sbE. generalize E_F_AcqRel_in_C.
       clear. basic_solver 10. }
  2: { rewrite ar_int_in_ar.
       rewrite <- issued_certT. rewrite ar_ct_I_in_I; eauto.
       rewrite issued_certT. rewrite I_in_D. eauto with hahn. }
  arewrite (R ⊆₁ R ∩₁ Acq ∪₁ R ∩₁ set_compl Acq) at 1.
  { clear. unfolder. ins. tauto. }
  rewrite !id_union, !seq_union_l, !dom_union. unionL.
  { clear. basic_solver. }
  rewrite (dom_r (wf_ar_intE WF)).
  rewrite E_in_RW_F_AcqRel; auto.
  rewrite id_union. rewrite seq_union_r. 
  rewrite path_ut_first. rewrite seq_union_l, seq_union_r, dom_union.
  unionL.
  2: { rewrite !seqA. rewrite (ar_int_in_sb WF).
       arewrite_id ⦗R ∪₁ W⦘. rewrite seq_id_r.
       generalize (@sb_trans G). ins. relsf.
       do 2 rewrite <- seqA. do 2 rewrite dom_seq.
       rewrite dom_sb_F_AcqRel_in_D. basic_solver. }
  rewrite id_union, seq_union_r.
  rewrite path_ut_first. rewrite seq_union_l, seq_union_r, dom_union.
  unionL.
  { rewrite ct_end.
    rewrite <- issued_certT. rewrite issuedW; eauto.
    clear. type_solver. }
  arewrite (Gar_int ⨾ ⦗R⦘ ∪ Gar_int ⨾ ⦗W⦘ ⊆ Gar_int).
  arewrite (⦗W⦘ ⨾ Gar_int＊ ⨾ ⦗I⦘ ⊆ ⦗I⦘ ⨾ ⦗W⦘ ⨾ Gar_int＊ ⨾ ⦗I⦘).
  { apply dom_rel_helper.
    rewrite <- issued_certT. 
    rewrite ar_int_in_ar. eby apply ar_rt_I_in_I. }
  rewrite <- !seqA. do 3 rewrite dom_seq. rewrite !seqA.
  rewrite rtE, !seq_union_l, !seq_union_r, dom_union, seq_id_l.
  unionL.
  { rewrite dom_ar_int_D_helper. clear. eauto with hahn. }
  rewrite ct_begin, !seqA.
  arewrite (⦗R ∩₁ set_compl Acq⦘ ⨾ Gar_int ⨾ ⦗R⦘ ⊆ ∅₂).
  2: { clear. basic_solver. }
  unfold ar_int.
  rewrite wf_ppoD. rewrite (wf_detourD WF). rewrite (W_ex_in_W WF).
  rewrite !seq_union_l, !seq_union_r. unionL.
  2-5: clear; type_solver 10.
  unfold bob, fwbob. clear. type_solver 10.
Qed.

Lemma dom_ar_int_rt_CI_D:
  dom_rel (Gar_int＊ ⨾ ⦗C ∪₁ I⦘) ⊆₁ D ∪₁ R ∩₁ Acq.
Proof using All.
  rewrite id_union, seq_union_r, dom_union. unionL.
  2: { rewrite rtE. generalize I_in_D, dom_ar_int_D. clear. 
       basic_solver. }
  rewrite ar_int_in_sb; auto.
  rewrite rt_of_trans; [|by apply sb_trans].
  rewrite crE. relsf. rewrite dom_sb_C_in_D, C_in_D. basic_solver. 
Qed.

(*
Lemma dom_W_ex_acq_sb_W_D_in_CI :
  dom_rel (⦗GW_ex_acq⦘ ⨾ Gsb ⨾ ⦗W⦘ ⨾ ⦗D⦘) ⊆₁ C ∪₁ I.
Proof using All.
  assert (dom_rel (⦗GW_ex_acq⦘ ⨾ Gsb ⨾ ⦗I⦘) ⊆₁ I) as AA.
  { arewrite (⦗I⦘ ⊆ ⦗W⦘ ⨾ ⦗I⦘).
    { generalize (issuedW ). basic_solver. }
    arewrite (⦗GW_ex_acq⦘ ⨾ Gsb ⨾ ⦗W⦘ ⊆ ⦗W⦘ ⨾ Gar).
    2: by apply ar_I_in_I.
    arewrite (⦗GW_ex_acq⦘ ⊆ ⦗W⦘ ⨾ ⦗GW_ex_acq⦘).
    { generalize (W_ex_in_W WF). basic_solver. }
      by rewrite w_ex_acq_sb_w_in_ar. }
  unfold D at 1. rewrite !id_union, !seq_union_r, !dom_union.
  unionL.
  { unionR left.
    generalize (dom_sb_covered ). basic_solver. }
  { unionR right. arewrite_id ⦗W⦘. by rewrite seq_id_l. }
  { arewrite (⦗GW_ex_acq⦘ ⊆ ⦗GW_ex_acq⦘ ⨾ ⦗set_compl is_init⦘).
    { generalize W_ex_acq_not_init. basic_solver. }
    arewrite_id ⦗W⦘. rewrite seq_id_l.
    rewrite (dom_rel_helper (@E_ntid_sb_prcl G thread)).
    arewrite (GW_ex_acq ⊆₁ W).
    { generalize (W_ex_in_W WF). basic_solver. }
    rewrite !dom_eqv1. unionR right.
    rewrite <- !set_interA.
    arewrite (W ∩₁ E ⊆₁ E ∩₁ W) by basic_solver.
    rewrite <- IT_new_co. basic_solver. }
  { rewrite <- !seqA. rewrite dom_rel_eqv_dom_rel.
    rewrite !seqA.
    arewrite (Gsb ⨾ ⦗W⦘ ⨾ Grfi^? ⨾ Gppo ⊆ Gsb).
    2: by unionR right. 
    arewrite (Grfi ⊆ Gsb).
    rewrite (ppo_in_sb WF).
    generalize (@sb_trans G). basic_solver. }
  { unionR right. 
    rewrite <- !seqA. rewrite dom_rel_eqv_dom_rel.
    rewrite !seqA.
    arewrite (Gsb ⨾ ⦗W⦘ ⨾ (Gdata ∪ Grfi ∪ Grmw)＊ ⨾ Grppo ⊆ Gsb).
    2: rewrite W_ex_acq_in_I; basic_solver.
    arewrite (Grfi ⊆ Gsb).
    rewrite (data_in_sb WF).
    rewrite (rppo_in_sb WF).
    rewrite (rmw_in_sb WF).
    rewrite unionK.
    rewrite rt_of_trans.
    all: generalize (@sb_trans G); basic_solver. }
  { rewrite (dom_r (wf_rfiD WF)).
    rewrite <- !seqA. rewrite codom_eqv1.
    clear. type_solver 20. }
  clear. type_solver 20.
Qed.
*)

End CertExec_D.
