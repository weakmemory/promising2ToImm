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

From imm Require Import AuxDef.
Require Import ExtTraversalConfig.
From imm Require Import TraversalOrder.
From imm Require Import TLSCoherency.
From imm Require Import IordCoherency.
From imm Require Import SimClosure. 
Require Import TlsEventSets.
(* From imm Require Import FairExecution. *)
(* Require Import ImmFair. *)
From imm Require Import FinExecution.

Require Import Cert_co.
Require Import Cert_D.
Require Import Cert_rf.
Require Import CertExecution2.
Require Import Cert_hb.

Set Implicit Arguments.

Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'NTid_' t" := (fun x => tid x <> t) (at level 1).

Section CertExec_coh.

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
Hypothesis ACYC_EXT : acyc_ext G sc.
Hypothesis CSC : coh_sc G sc.
Hypothesis COH : coherence G.
Hypothesis AT : rmw_atomicity G.
Hypothesis FIN: fin_exec G. 

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
Hypothesis TCOH_rst_new_T : tls_coherent G (T ∪₁ eq ta_cover <*> (E ∩₁ NTid_ thread)).
Hypothesis ICOH_rst_new_T : iord_coherent G sc (T ∪₁ eq ta_cover <*> (E ∩₁ NTid_ thread)).

Hypothesis S_in_W : S ⊆₁ W.
Hypothesis RPPO_S : dom_rel ((Gdetour ∪ Grfe) ⨾ (Gdata ∪ Grfi ∪ Grmw)＊ ⨾ Grppo ⨾ ⦗S⦘) ⊆₁ I.
Hypothesis RMW_S : dom_rel ((Gdetour ∪ Grfe) ⨾ Grmw ⨾ ⦗S⦘) ⊆₁ I.
Hypothesis ST_in_E : S ∩₁ Tid_ thread ⊆₁ E.
Hypothesis I_in_S : I ⊆₁ S.

Hypothesis F_in_C : E ∩₁ F ∩₁ Acq/Rel ⊆₁ C.

Hypothesis S_I_in_W_ex : (S ∩₁ Tid_ thread) \₁ I ⊆₁ W_ex G.

Hypothesis ETC_DR_R_ACQ_I : dom_rel ((Gdetour ∪ Grfe) ⨾ (Grmw ⨾ Grfi)＊ ⨾ ⦗R∩₁Acq⦘ ⨾ Gsb ⨾ ⦗S⦘) ⊆₁ I.

Hypothesis COMP_R_ACQ_SB : dom_rel ((Grmw ⨾ Grfi)＊ ⨾ ⦗E ∩₁ R ∩₁ Acq⦘) ⊆₁ codom_rel Grf.
Hypothesis RMWREX        : dom_rel Grmw ⊆₁ GR_ex.
Hypothesis FACQREL       : E ∩₁ F ⊆₁ Acq/Rel.

Variable lab' : actid -> label.
Hypothesis SAME : same_lab_u2v lab' Glab.

Notation "'certG'" := (certG G sc T thread lab').

Hypothesis WF_cert : Wf certG.

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


Lemma cert_coherece_detour_helper :
  irreflexive (Ghb ⨾ (sc ⨾ Ghb)^? ⨾ ⦗D⦘ ⨾ Grf⁻¹⨾ 
  ⦗I ∩₁ NTid_ thread⦘ ⨾ cert_co ⨾ ⦗E ∩₁ W ∩₁ Tid_ thread \₁ I⦘).
Proof using All.
assert (A: dom_rel (Gdetour ⨾ ⦗D⦘) ⊆₁ I).
by eapply dom_detour_D; try edone.

rewrite wf_cert_col; try edone.
unfold same_loc; unfolder; ins; desc; splits; eauto.
assert (CO: Gco x z1).
{ eapply tot_ex.
  apply WF.
  unfolder; splits; eauto.
  hahn_rewrite (wf_rfE WF) in H2; unfolder in H2; desc; done.
  hahn_rewrite (wf_rfD WF) in H2; unfolder in H2; desc; done.
  unfolder; splits; eauto.
  intro; generalize COH CSC; unfold coherence, coh_sc, eco, fr.
  desf; try subst z0; basic_solver 21.
  intro; subst x; auto. }
assert (SB: Gsb x z0).
{ apply hb_sc_hb_de; generalize w_covered_issued; basic_solver 21. }
assert (RFE: Grfe z1 z0).
{ ie_unfolder; unfolder; ins; desc; splits; eauto.
  intro K.
  apply sb_tid_init in SB.
  apply sb_tid_init in K.
  destruct SB, K.
  congruence.
  hahn_rewrite (no_co_to_init WF (coherence_sc_per_loc COH)) in CO.
  unfolder in CO; desc; done.
  all: generalize init_issued; basic_solver. }
assert (COE: Gcoe x z1).
{ ie_unfolder; unfolder; ins; desc; splits; eauto.
  intro K.
  apply sb_tid_init in K.
  destruct K.
  congruence.
  generalize init_issued; basic_solver. }
assert (DETOURE: Gdetour x z0).
  by unfold detour; basic_solver.
apply H6, A; unfolder; ins; desf; splits; eauto.
Qed.

Lemma hb_sc_irr : irreflexive (Ghb ⨾ sc^?).
Proof using ACYC_EXT WF COH WF_SC.
case_refl sc; [by apply hb_irr|].
rewrite (wf_scD WF_SC); rotate 1.
sin_rewrite (f_sc_hb_f_sc_in_ar WF).
unfolder; ins; desc.
eapply ACYC_EXT.
eapply t_trans; [edone| apply t_step].
by apply sc_in_ar.
Qed.

Lemma set_compl_D_helper : ⦗set_compl D⦘ ⨾ Ghb ⨾ (sc ⨾ Ghb)^? ⊆ Gsb.
Proof using WF hb_sc_hb_de.
rewrite <- hb_sc_hb_de.
rewrite (dom_l (wf_hbE WF)) at 1.
rewrite !seqA.
forward (eapply C_in_D with (G:=G) (T:=T) (thread:=thread)); eauto.
forward (eapply I_in_D with (G:=G) (T:=T) (thread:=thread)); eauto.
basic_solver 21.
Qed.


Lemma hb_rfe_irr : irreflexive (Ghb ⨾ (sc ⨾ Ghb)^? ⨾ Crfe).
Proof using ACYC_EXT COH COMP_ACQ COMP_C COMP_NTID COMP_RPPO CSC ETC_DR_R_ACQ_I E_to_S
F_in_C G Grfe_E IT_new_co I_in_S RELCOV RMWREX ST_in_E S_I_in_W_ex S_in_W T
WF WF_SC W_hb_sc_hb_to_I_NTid detour_Acq_E lab' sc thread urr_helper
urr_helper_C TCOH_rst_new_T.
rewrite cert_rfe_eq. rewrite cert_rfe_alt; eauto.
relsf; unionL.
{ revert COH CSC; unfold coherence, coh_sc, eco.
  ie_unfolder. clear; basic_solver 21. }
{ forward (eapply new_rf_hb with (G:=G)); try edone. 
  clear; basic_solver 12. }
arewrite (Grmw ≡ <|GR_ex ∩₁ E|> ;; Grmw).
2: { rewrite Rex_in_D; eauto. clear. basic_solver. }
apply dom_rel_helper.
rewrite (dom_l (wf_rmwE WF)).
rewrite (dom_rel_helper RMWREX).
clear. basic_solver.
Qed.

Lemma hb_rf_irr : irreflexive (Ghb ⨾ (sc ⨾ Ghb)^? ⨾ Crf).
Proof using ACYC_EXT COH COMP_ACQ COMP_C COMP_NTID COMP_RPPO CSC ETC_DR_R_ACQ_I E_to_S
F_in_C G Grfe_E IT_new_co I_in_S RELCOV RMWREX ST_in_E S_I_in_W_ex S_in_W T WF WF_SC W_hb_sc_hb_to_I_NTid detour_Acq_E lab' sc thread urr_helper
urr_helper_C TCOH_rst_new_T.
rewrite cert_rf_eq.
rewrite cert_rfi_union_cert_rfe.
relsf; unionL.
{ arewrite (cert_rfi ⊆ Gsb).
  rotate 2.
rewrite sb_in_hb.
generalize (@hb_trans G).
generalize (hb_sc_irr).
clear.
 basic_solver 12. }
apply hb_rfe_irr.
Qed.

Lemma hb_co_irr : irreflexive (Ghb ⨾ (sc ⨾ Ghb)^? ⨾ Cco).
Proof using All.
ins; rewrite cert_co_alt'; try edone; relsf; unionL.
{ revert COH CSC. unfold coherence, coh_sc, eco. basic_solver 21. }
revert W_hb_sc_hb_to_I_NTid. basic_solver 21.
Qed.

Lemma hb_co_irr' : irreflexive (Ghb ⨾ (sc ⨾ Ghb)^? ⨾ Cco^?).
Proof using All.
rewrite (crE cert_co); relsf; unionL; splits.
generalize hb_sc_irr (@hb_trans G); basic_solver 21.
apply hb_co_irr.
Qed.

Lemma hb_co_irr'' : irreflexive (Ghb ⨾ (sc ⨾ Ghb)^? ⨾ ⦗set_compl D⦘ ⨾ Grmw ⨾ Cco^?).
Proof using All.
      rewrite (rmw_in_sb WF).
      rewrite sb_in_hb.
      arewrite_id ⦗set_compl D⦘; rels.
      arewrite (Ghb ⨾ (sc ⨾ Ghb)^? ⨾ Ghb ⊆ Ghb ⨾ (sc ⨾ Ghb)^?).
      { generalize (@hb_trans G). basic_solver 21. }
      apply hb_co_irr'.
Qed.


Lemma hb_co_rfe_irr : irreflexive (Ghb ⨾ (sc ⨾ Ghb)^? ⨾ Cco ⨾ Crfe).
Proof using All.
  rewrite cert_rfe_eq. rewrite cert_rfe_alt; eauto.
  relsf; unionL.
  { rewrite (dom_rel_helper Grfe_E).
    unfold CertExecution2.certG; ins; rewrite !seqA.
    rewrite (I_in_cert_co_base G thread) at 1.
    arewrite (cert_co ⨾ ⦗cert_co_base G T thread⦘ ⊆ co G ⨾ ⦗cert_co_base G T thread⦘).
    eby eapply cert_co_I.
    revert COH CSC. unfold coherence, coh_sc, eco.
    ie_unfolder. basic_solver 21. }
  ins; rewrite cert_co_alt'; try edone; relsf; unionL.
  2: { generalize non_I_new_rf. basic_solver 16. }
  { arewrite_id ⦗set_compl (dom_rel Grmw)⦘. rewrite seq_id_r.
    rewrite new_rf_in_furr.
    rotate 1.
    arewrite (Gfurr \ Gsb ⊆ Gfurr).
    arewrite (Gfurr ⨾ Ghb ⨾ (sc ⨾ Ghb)^? ⊆ Gfurr).
    { generalize (furr_hb_sc_hb WF WF_SC ACYC_EXT). basic_solver 21. }
    generalize (eco_furr_irr WF WF_SC CSC COH).
    unfold eco. basic_solver 21. }
  arewrite (Grmw ≡ <|GR_ex ∩₁ E|> ;; Grmw).
  2: { rewrite Rex_in_D; eauto. clear. basic_solver. }
  apply dom_rel_helper.
  rewrite (dom_l (wf_rmwE WF)).
  rewrite (dom_rel_helper RMWREX).
  clear. basic_solver.
Qed.
(* rewrite rmw_W_ex, transp_seq, transp_eqv_rel, W_ex_in_cert_co_base. *)
(* forward (eapply cert_co_I with (G:=G)); eauto; intro AA. *)
(* sin_rewrite AA. *)
(* arewrite_id ⦗cert_co_base G T⦘; rels. *)

(* rotate 1. *)
(* sin_rewrite (transp_rmw_sb WF). *)


(*       revert COH. unfold coherence, coh_sc, eco, fr. *)
(* rewrite sb_in_hb. *)
(* generalize (co_irr WF). *)
(*       basic_solver 21. *)
(* Qed. *)

Lemma hb_co_rfe_irr' : irreflexive (Ghb ⨾ (sc ⨾ Ghb)^? ⨾ Cco^? ⨾ Crfe).
Proof using All.
rewrite (crE cert_co); relsf; unionL; splits.
generalize hb_rfe_irr (@hb_trans G); basic_solver 21.
apply hb_co_rfe_irr.
Qed.

(* irreflexive
  (Ghb
   ⨾ (sc ⨾ Ghb)^?
     ⨾ ⦗set_compl D⦘ ⨾ Grmw ⨾ cert_co^? ⨾ ⦗I⦘ ⨾ Grfe ⨾ ⦗D⦘)

irreflexive
  (Ghb
   ⨾ (sc ⨾ Ghb)^?
     ⨾ ⦗set_compl D⦘
       ⨾ Grmw
         ⨾ cert_co^?
           ⨾ ⦗I⦘ ⨾ (new_rf \ Gsb) ⨾ ⦗set_compl (dom_rel Grmw)⦘)


 *)
Lemma hb_fr_irr : irreflexive (Ghb ⨾ (sc ⨾ Ghb)^? ⨾ Cfr).
Proof using All.
unfold fr; ins; rewrite cert_co_alt'; try edone; unfold CertExecution2.certG; ins.
    unfold Cert_rf.cert_rf.
    do 2 rewrite transp_union.
    rewrite transp_seq; relsf; unionL.
    { revert COH CSC. unfold coherence, coh_sc, eco, fr. ie_unfolder. basic_solver 21. }
    { rotate 1.
      arewrite (Gco ∩ cert_co ⊆ cert_co).
      rewrite (dom_r (wf_coD WF_cert)), !seqA, cert_W; eauto.
      arewrite (⦗W⦘ ⨾ Ghb ⨾ (sc ⨾ Ghb)^? ⊆ Gfurr).
      { rewrite (furr_alt WF_SC). basic_solver 21. }
      unfold Cert_rf.new_rf. basic_solver 21. }
    { rewrite !transp_seq. relsf. rewrite !seqA.
      arewrite ((immediate cert_co)⁻¹ ⨾ Gco ∩ cert_co ⊆ cert_co^?).
      { forward (eapply transp_cert_co_imm_cert_co with (G:=G)); eauto.
        basic_solver 12. }
      apply hb_co_irr''. }
    { rewrite !seqA. eapply cert_coherece_detour_helper. }
    { rotate 1.
      arewrite (⦗E ∩₁ W ∩₁ Tid_ thread \₁ I⦘ ⊆ ⦗W⦘) by basic_solver.
      arewrite (⦗W⦘ ⨾ Ghb ⨾ (sc ⨾ Ghb)^? ⊆ Gfurr).
      { rewrite (furr_alt WF_SC). basic_solver 21. }
      unfold Cert_rf.new_rf. basic_solver 21. }
    rewrite !transp_seq. relsf. rewrite !seqA.
    arewrite ((immediate cert_co)⁻¹
             ⨾ ⦗I ∩₁ NTid_ thread⦘ ⨾ cert_co ⨾ ⦗E ∩₁ W ∩₁ Tid_ thread \₁ I⦘ ⊆ cert_co^?).
      { forward (eapply transp_cert_co_imm_cert_co with (G:=G)); eauto.
        basic_solver 12. }
    apply hb_co_irr''.
Qed.

Lemma hb_fr_rfe : irreflexive (Ghb ⨾ (sc ⨾ Ghb)^? ⨾ Cfr ⨾ Crfe).
Proof using All.
rewrite cert_rfe_eq. rewrite cert_rfe_alt; eauto. relsf; unionL.
  { unfold fr. unfold CertExecution2.certG. ins. unfold Cert_rf.cert_rf.
    rewrite !transp_union, transp_seq; relsf; unionL.
    { rewrite (dom_rel_helper Grfe_E), !seqA.
      rewrite (I_in_cert_co_base G thread) at 1.
      arewrite (cert_co ⨾ ⦗cert_co_base G T thread⦘ ⊆ co G ⨾ ⦗cert_co_base G T thread⦘).
      eby eapply cert_co_I.
      revert COH CSC. unfold coherence, coh_sc, eco, fr. ie_unfolder.
      basic_solver 21. }
    { arewrite (Grfe ⨾ ⦗D⦘ ⊆ Grf) by ie_unfolder; basic_solver.
      rotate 1.
      arewrite (Grf ⨾ Ghb ⨾ (sc ⨾ Ghb)^? ⊆ Gfurr).
      { rewrite (furr_alt WF_SC). rewrite (dom_l (wf_rfD WF)). basic_solver 21. }
      unfold Cert_rf.new_rf. basic_solver 21. }
    rewrite !transp_seq. relsf. rewrite !seqA.
    arewrite ((immediate cert_co)⁻¹ ⨾ cert_co ⊆ cert_co^?).
    { forward (eapply transp_cert_co_imm_cert_co with (G:=G)); eauto. }

    arewrite (cert_co^? ⨾ ⦗I⦘ ⊆ Gco^? ⨾ ⦗I⦘).
    { cut (cert_co ⨾ ⦗I⦘ ⊆ Gco).
basic_solver.
      rewrite (I_in_cert_co_base G thread) at 1.

      forward (eapply cert_co_I with (G:=G)); eauto; intro AA.
rewrite AA; basic_solver. }

      rewrite (rmw_in_sb WF).
      rewrite sb_in_hb.
      arewrite_id ⦗set_compl D⦘; rels.
      arewrite (Ghb ⨾ (sc ⨾ Ghb)^? ⨾ Ghb ⊆ Ghb ⨾ (sc ⨾ Ghb)^?).
      { generalize (@hb_trans G). basic_solver 21. }
      arewrite_id ⦗I⦘; rels.

      revert COH CSC. 
unfold coherence, coh_sc, eco, rfe.

      basic_solver 21. }
  { unfold fr; unfold CertExecution2.certG; ins. unfold Cert_rf.cert_rf.
    rewrite !transp_union, !transp_seq; relsf; unionL.
    1-2: rewrite cert_co_alt'; try edone; relsf; unionL.
    2,4: generalize non_I_new_rf; basic_solver 16.
    { arewrite_id ⦗set_compl (dom_rel Grmw)⦘. rewrite seq_id_r.
      rewrite new_rf_in_furr.
      rotate 1.
      arewrite (Gfurr \ Gsb ⊆ Gfurr).
      arewrite (Gfurr ⨾ Ghb ⨾ (sc ⨾ Ghb)^? ⊆ Gfurr).
      { generalize (furr_hb_sc_hb WF WF_SC ACYC_EXT). basic_solver 21. }
      generalize (eco_furr_irr WF WF_SC CSC COH).
      unfold eco, fr. basic_solver 21. }
    { arewrite_id ⦗set_compl (dom_rel Grmw)⦘. rewrite !seq_id_r.
      rewrite new_rf_in_furr at 2.
      rotate 1.
      arewrite (Gfurr \ Gsb ⊆ Gfurr).
      arewrite (Gfurr ⨾ Ghb ⨾ (sc ⨾ Ghb)^? ⊆ Gfurr).
      { generalize (furr_hb_sc_hb WF WF_SC ACYC_EXT). basic_solver 21. }
      unfold Cert_rf.new_rf. basic_solver 21. }
    rewrite !seqA.
    arewrite ((immediate cert_co)⁻¹ ⨾ cert_co ⊆ cert_co^?).
      { forward (eapply transp_cert_co_imm_cert_co with (G:=G)); eauto. }

      rewrite (rmw_in_sb WF) at 1.
      rewrite sb_in_hb at 1.
      arewrite_id ⦗set_compl D⦘; rels.
      arewrite (Ghb ⨾ (sc ⨾ Ghb)^? ⨾ Ghb ⊆ Ghb ⨾ (sc ⨾ Ghb)^?).
      { generalize (@hb_trans G). basic_solver 21. }
      arewrite_id ⦗I⦘; rels.


generalize hb_co_rfe_irr'.
unfold rfe.
rewrite cert_rf_eq.
unfold Cert_rf.cert_rf.
basic_solver 21. }

  rotate 1.
  sin_rewrite set_compl_D_helper.
  unfold fr. rewrite !seqA.
  rewrite AuxRel.immediate_in.
  arewrite (cert_co ⨾ Grmw⁻¹ \ Gsb ⊆ cert_co ⨾ Grmw⁻¹).
rotate 1.
sin_rewrite (transp_rmw_sb WF).
arewrite_id ⦗I⦘; rels.
forward (eapply cert_co_trans with (G:=G)); eauto.
ins; relsf. 
generalize hb_fr_irr.
rewrite sb_in_hb.

generalize (fr_irr WF_cert).
unfold fr.
basic_solver 21.
Qed.

Lemma coh_helper : irreflexive (Chb ⨾ (sc ⨾ Chb)^? ⨾ Ceco^?).
Proof using All.
  apply coh_helper_alt; rewrite cert_hb; eauto.
  generalize hb_sc_irr, hb_rfe_irr, hb_co_irr, 
             hb_co_rfe_irr, hb_fr_irr, hb_fr_rfe.
  basic_solver 21.
Qed.

Lemma cert_coherence : coherence certG.
Proof using All.
  red. generalize coh_helper; basic_solver 12.
Qed.

Lemma cert_coh_sc : coh_sc certG sc.
Proof using All.
  red; case_refl _.
  2: generalize coh_helper; basic_solver 21.
  rewrite cert_hb; auto.
  rewrite (wf_scD WF_SC); rotate 2.
  sin_rewrite (f_sc_hb_f_sc_in_ar WF).
  unfolder; ins; desc.
  eapply ACYC_EXT.
  eapply t_trans; [edone| apply t_step].
    by apply sc_in_ar.
Qed.

End CertExec_coh.
