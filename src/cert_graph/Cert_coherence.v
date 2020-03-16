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

From imm Require Import AuxRel2.
Require Import TraversalConfig.
Require Import TraversalConfigAlt.
Require Import TraversalConfigAltOld.
Require Import ExtTraversalConfig.

Require Import Cert_co.
Require Import Cert_D.
Require Import Cert_rf.
Require Import CertExecution2.
Require Import Cert_hb.

Set Implicit Arguments.
Remove Hints plus_n_O.

Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'NTid_' t" := (fun x => tid x <> t) (at level 1).

Section CertExec_coh.

Variable G : execution.
Variable sc : relation actid.

Notation "'Init'" := (fun a => is_true (is_init a)).

Notation "'E'" := G.(acts_set).
Notation "'Gacts'" := G.(acts).
Notation "'Glab'" := G.(lab).
Notation "'Gsb'" := G.(sb).
Notation "'Grf'" := G.(rf).
Notation "'Gco'" := G.(co).
Notation "'Grmw'" := G.(rmw).
Notation "'Gdata'" := G.(data).
Notation "'Gaddr'" := G.(addr).
Notation "'Gctrl'" := G.(ctrl).
Notation "'Gdeps'" := G.(deps).
Notation "'Grmw_dep'" := G.(rmw_dep).

Notation "'Gfre'" := G.(fre).
Notation "'Grfe'" := G.(rfe).
Notation "'Gcoe'" := G.(coe).
Notation "'Grfi'" := G.(rfi).
Notation "'Gfri'" := G.(fri).
Notation "'Gcoi'" := G.(coi).
Notation "'Gfr'" := G.(fr).
Notation "'Geco'" := G.(eco).
Notation "'Gdetour'" := G.(detour).
Notation "'Gsw'" := G.(sw).
Notation "'Grelease'" := G.(release).
Notation "'Grs'" := G.(rs).
Notation "'Ghb'" := G.(hb).
Notation "'Gppo'" := G.(ppo).
Notation "'Grppo'" := G.(rppo).
Notation "'Gbob'" := G.(bob).
Notation "'Gfwbob'" := G.(fwbob).
Notation "'Gar'" := (G.(ar) sc).
Notation "'Gar_int'" := (G.(ar_int)).
Notation "'Gurr'" := (G.(urr) sc).
Notation "'Gfurr'" := (G.(furr) sc).
Notation "'Gmsg_rel'" := (G.(msg_rel) sc).

Notation "'Gloc'" := (loc Glab).
Notation "'Gval'" := (val Glab).
Notation "'Gsame_loc'" := (same_loc Glab).

Notation "'R'" := (fun a => is_true (is_r Glab a)).
Notation "'W'" := (fun a => is_true (is_w Glab a)).
Notation "'F'" := (fun a => is_true (is_f Glab a)).
Notation "'GR_ex'" := (fun a => is_true (R_ex Glab a)).
Notation "'GW_ex'" := G.(W_ex).
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


Variable T : trav_config.
Variable S : actid -> Prop.

Notation "'I'" := (issued T).
Notation "'C'" := (covered T).

Variable thread : BinNums.positive.

Notation "'cert_co'" := (cert_co G T S thread).

Notation "'D'" := (D G T S thread).

Notation "'new_rf'" := (new_rf G sc T S thread).
Notation "'cert_rf'" := (cert_rf G sc T S thread).
Notation "'cert_rfi'" := (cert_rfi G sc T S thread).
Notation "'cert_rfe'" := (cert_rfe G sc T S thread).

Hypothesis WF : Wf G.
Hypothesis WF_SC : wf_sc G sc.
Hypothesis RELCOV : W ∩₁ Rel ∩₁ I ⊆₁ C.
Hypothesis TCCOH : tc_coherent G sc T.
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
Hypothesis TCCOH_rst_new_T : tc_coherent G sc (mkTC (C ∪₁ (E ∩₁ NTid_ thread)) I).

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

Notation "'certG'" := (certG G sc T S thread lab').

Hypothesis WF_cert : Wf certG.

(* Notation "'CE'" := certG.(acts_set). *)
(* Notation "'Cacts'" := certG.(acts). *)
(* Notation "'Clab'" := certG.(lab). *)
(* Notation "'Csb'" := certG.(sb). *)
Notation "'Crf'" := certG.(rf).
Notation "'Cco'" := certG.(co).
Notation "'Crmw'" := certG.(rmw).
(* Notation "'Cdata'" := certG.(data). *)
(* Notation "'Caddr'" := certG.(addr). *)
(* Notation "'Cctrl'" := certG.(ctrl). *)
Notation "'Cdeps'" := certG.(deps).
(* Notation "'Crmw_dep'" := certG.(rmw_dep). *)

Notation "'Cfre'" := certG.(fre).
(* Notation "'Crfe'" := certG.(rfe). *)
Notation "'Ccoe'" := certG.(coe).
Notation "'Crfi'" := certG.(rfi).
Notation "'Cfri'" := certG.(fri).
Notation "'Ccoi'" := certG.(coi).
Notation "'Cfr'" := certG.(fr).
Notation "'Ceco'" := certG.(eco).
Notation "'Cdetour'" := certG.(detour).
Notation "'Csw'" := certG.(sw).
Notation "'Crelease'" := certG.(release).
Notation "'Crs'" := certG.(rs).
Notation "'Chb'" := certG.(hb).
Notation "'Cppo'" := certG.(ppo).
(* Notation "'Cbob'" := certG.(bob). *)
(* Notation "'Cfwbob'" := certG.(fwbob). *)
Notation "'Car'" := (certG.(ar) sc).
Notation "'Car_int'" := (certG.(ar_int)).
Notation "'Curr'" := (certG.(urr) sc).
Notation "'Cmsg_rel'" := (certG.(msg_rel) sc).

(* Notation "'E'" := G.(acts_set). *)
(* Notation "'Gacts'" := G.(acts). *)
Notation "'Clab'" := certG.(lab).
Notation "'Csb'" := certG.(sb).
(* Notation "'Grf'" := G.(rf). *)
(* Notation "'Gco'" := G.(co). *)
(* Notation "'Gdata'" := G.(data). *)
(* Notation "'Gaddr'" := G.(addr). *)
(* Notation "'Gctrl'" := G.(ctrl). *)
(* Notation "'Gdeps'" := G.(deps). *)
(* Notation "'Grmw_dep'" := G.(rmw_dep). *)

(* Notation "'Gfre'" := G.(fre). *)
Notation "'Crfe'" := certG.(rfe).
(* Notation "'Gcoe'" := G.(coe). *)
Notation "'Crfi'" := certG.(rfi).
(* Notation "'Gfri'" := G.(fri). *)
(* Notation "'Gcoi'" := G.(coi). *)
(* Notation "'Gfr'" := G.(fr). *)
(* Notation "'Geco'" := G.(eco). *)
(* Notation "'Gdetour'" := G.(detour). *)
(* Notation "'Gsw'" := G.(sw). *)
Notation "'Crelease'" := certG.(release).
(* Notation "'Grs'" := G.(rs). *)
(* Notation "'Ghb'" := G.(hb). *)
(* Notation "'Gppo'" := G.(ppo). *)
(* Notation "'Grppo'" := G.(rppo). *)
(* Notation "'Gbob'" := G.(bob). *)
(* Notation "'Gfwbob'" := G.(fwbob). *)
(* Notation "'Gar'" := (G.(ar) sc). *)
(* Notation "'Gar_int'" := (G.(ar_int)). *)
(* Notation "'Gurr'" := (G.(urr) sc). *)
(* Notation "'Gfurr'" := (G.(furr) sc). *)
(* Notation "'Gmsg_rel'" := (G.(msg_rel) sc). *)

(* Notation "'Gloc'" := (loc Glab). *)
(* Notation "'Gval'" := (val Glab). *)
Notation "'Csame_loc'" := (same_loc Clab).

Notation "'CR'" := (fun a => is_true (is_r Clab a)).
Notation "'CW'" := (fun a => is_true (is_w Clab a)).
Notation "'CF'" := (fun a => is_true (is_f Clab a)).
(* Notation "'GR_ex'" := (fun a => is_true (R_ex Glab a)). *)
(* Notation "'GW_ex'" := G.(W_ex). *)
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
  by apply hb_sc_hb_de; generalize (w_covered_issued TCCOH); basic_solver 21.
assert (RFE: Grfe z1 z0).
{ ie_unfolder; unfolder; ins; desc; splits; eauto.
  intro K.
  apply sb_tid_init in SB.
  apply sb_tid_init in K.
  destruct SB, K.
  congruence.
  hahn_rewrite (no_co_to_init WF (coherence_sc_per_loc COH)) in CO.
  unfolder in CO; desc; done.
  generalize (init_issued WF TCCOH); basic_solver.
  generalize (init_issued WF TCCOH); basic_solver. }
assert (COE: Gcoe x z1).
{ ie_unfolder; unfolder; ins; desc; splits; eauto.
  intro K.
  apply sb_tid_init in K.
  destruct K.
  congruence.
  generalize (init_issued WF TCCOH); basic_solver. }
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
rewrite (dom_l WF.(wf_hbE)) at 1.
rewrite !seqA.
forward (eapply C_in_D with (G:=G) (T:=T) (S:=S) (thread:=thread)); eauto.
forward (eapply I_in_D with (G:=G) (T:=T) (S:=S) (thread:=thread)); eauto.
basic_solver 21.
Qed.


Lemma hb_rfe_irr : irreflexive (Ghb ⨾ (sc ⨾ Ghb)^? ⨾ Crfe).
Proof using ACYC_EXT COH COMP_ACQ COMP_C COMP_NTID COMP_RPPO CSC ETC_DR_R_ACQ_I E_to_S
F_in_C G Grfe_E IT_new_co I_in_S RELCOV RMWREX S ST_in_E S_I_in_W_ex S_in_W T
TCCOH_rst_new_T WF WF_SC W_hb_sc_hb_to_I_NTid detour_Acq_E lab' sc thread urr_helper
urr_helper_C.
rewrite cert_rfe_eq. rewrite cert_rfe_alt; eauto.
relsf; unionL.
{ revert COH CSC; unfold coherence, coh_sc, eco.
  ie_unfolder. clear; basic_solver 21. }
{ forward (eapply new_rf_hb with (G:=G)); try edone. 
  clear; basic_solver 12. }
arewrite (Grmw ≡ <|GR_ex ∩₁ E|> ;; Grmw).
2: { rewrite Rex_in_D; eauto. clear. basic_solver. }
apply dom_rel_helper.
rewrite (dom_l WF.(wf_rmwE)).
rewrite (dom_rel_helper RMWREX).
clear. basic_solver.
Qed.

Lemma hb_rf_irr : irreflexive (Ghb ⨾ (sc ⨾ Ghb)^? ⨾ Crf).
Proof using ACYC_EXT COH COMP_ACQ COMP_C COMP_NTID COMP_RPPO CSC ETC_DR_R_ACQ_I E_to_S
F_in_C G Grfe_E IT_new_co I_in_S RELCOV RMWREX S ST_in_E S_I_in_W_ex S_in_W T
TCCOH_rst_new_T WF WF_SC W_hb_sc_hb_to_I_NTid detour_Acq_E lab' sc thread urr_helper
urr_helper_C.
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
      rewrite WF.(rmw_in_sb).
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
    rewrite (I_in_cert_co_base G T S thread) at 1.
    arewrite (cert_co ⨾ ⦗cert_co_base G T S thread⦘ ⊆ co G ⨾ ⦗cert_co_base G T S thread⦘).
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
  rewrite (dom_l WF.(wf_rmwE)).
  rewrite (dom_rel_helper RMWREX).
  clear. basic_solver.
Qed.
(* rewrite rmw_W_ex, transp_seq, transp_eqv_rel, W_ex_in_cert_co_base. *)
(* forward (eapply cert_co_I with (G:=G)); eauto; intro AA. *)
(* sin_rewrite AA. *)
(* arewrite_id ⦗cert_co_base G T⦘; rels. *)

(* rotate 1. *)
(* sin_rewrite WF.(transp_rmw_sb). *)


(*       revert COH. unfold coherence, coh_sc, eco, fr. *)
(* rewrite sb_in_hb. *)
(* generalize WF.(co_irr). *)
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
      rewrite (dom_r WF_cert.(wf_coD)), !seqA, cert_W; eauto.
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
      rewrite (I_in_cert_co_base G T S thread) at 1.
      arewrite (cert_co ⨾ ⦗cert_co_base G T S thread⦘ ⊆ co G ⨾ ⦗cert_co_base G T S thread⦘).
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
      rewrite (I_in_cert_co_base G T S thread) at 1.

      forward (eapply cert_co_I with (G:=G)); eauto; intro AA.
rewrite AA; basic_solver. }

      rewrite WF.(rmw_in_sb).
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

      rewrite WF.(rmw_in_sb) at 1.
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
sin_rewrite WF.(transp_rmw_sb).
arewrite_id ⦗I⦘; rels.
forward (eapply cert_co_trans with (G:=G)); eauto.
ins; relsf. 
generalize hb_fr_irr.
rewrite sb_in_hb.

generalize WF_cert.(fr_irr).
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
