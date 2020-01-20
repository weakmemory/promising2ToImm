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

Require Import AuxRel2.
Require Import TraversalConfig.
Require Import TraversalConfigAlt.
Require Import TraversalConfigAltOld.
Require Import ExtTraversalConfig.

Require Import ImmProperties.

Require Import Cert_co.
Require Import Cert_D.
Require Import Cert_rf.
Require Import Cert_ar.
Require Import Cert_atomicity.
Require Import Cert_coherence.
Require Import CertExecution2.

Set Implicit Arguments.
Remove Hints plus_n_O.

Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'NTid_' t" := (fun x => tid x <> t) (at level 1).

Section CertExec_tc.

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

Notation "'cert_co'" := (cert_co G T thread).

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
Hypothesis RMW_S : dom_rel ((Gdetour ∪ Grfe) ;; Grmw ;; <|S|>) ⊆₁ I.
Hypothesis ST_in_E : S ∩₁ Tid_ thread ⊆₁ E.
Hypothesis I_in_S : I ⊆₁ S.
Hypothesis W_ex_acq_in_I :GW_ex_acq ⊆₁ I.

Hypothesis F_in_C : E ∩₁ F ∩₁ Acq/Rel ⊆₁ C.

Hypothesis S_I_in_W_ex : (S ∩₁ Tid_ thread) \₁ I ⊆₁ W_ex G.

Hypothesis ETC_DR_R_ACQ_I : dom_rel ((Gdetour ∪ Grfe) ⨾ (Grmw ⨾ Grfi)^* ⨾ ⦗R∩₁Acq⦘ ⨾ Gsb ⨾ ⦗S⦘) ⊆₁ I.

Hypothesis COMP_R_ACQ_SB : dom_rel ((Grmw ⨾ Grfi)＊ ⨾ ⦗E ∩₁ R ∩₁ Acq⦘) ⊆₁ codom_rel Grf.

Variable lab' : actid -> label.
Hypothesis SAME : same_lab_u2v lab' Glab.

Hypothesis NEW_VAL : forall r w (RF: cert_rf w r), val lab' w = val lab' r.
Hypothesis OLD_VAL : forall a (NIN: ~ (E \₁ D) a), val lab' a = Gval a.

Hypothesis ETC_DETOUR_RMW_S : dom_rel (Gdetour ⨾ Grmw ⨾ ⦗ S ⦘) ⊆₁ I.

Notation "'certG'" := (certG G sc T S thread lab').

Hypothesis WF_cert    : Wf certG.
Hypothesis WF_SC_cert : wf_sc certG sc.

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

Lemma cert_imm_consistent : imm_consistent certG sc.
Proof using All.
red; splits; eauto using WF_SC_cert, cert_acyc_ext, cert_coh_sc, cert_complete, cert_coherence, cert_rmw_atomicity.
Qed.

Lemma dom_fwbob_I : dom_rel (Gfwbob ⨾ ⦗C ∪₁ I⦘) ⊆₁ C ∪₁ I.
Proof using E_F_AcqRel_in_C E_to_S F_in_C RELCOV S_in_W TCCOH.
  unfold fwbob; relsf; unionL; splits.
  { rewrite sb_W_rel_CI; eauto. basic_solver. }
  { rewrite W_rel_sb_loc_W_CI; eauto. basic_solver. }
  { rewrite (dom_r (@wf_sbE G)).
    generalize dom_sb_F_AcqRel_in_C. basic_solver 12. }
  rewrite (dom_l (@wf_sbE G)).
  generalize E_F_AcqRel_in_C; basic_solver 12.
Qed.

Lemma TCCOH_cert_old : tc_coherent_alt_old certG sc (mkTC (C ∪₁ (E ∩₁ NTid_ thread)) I).
Proof using All.
  assert (dom_rel Crfe ⊆₁ I) as AA.
  { rewrite cert_rfe_eq. eapply dom_cert_rfe_in_I with (G:=G); eauto. }

  assert (TCCOH1:= TCCOH_rst_new_T).
  apply (tc_coherent_implies_tc_coherent_alt WF WF_SC) in TCCOH1.
  destruct TCCOH1.

  assert (dom_rel ((⦗GW_ex⦘ ⨾ Grfi ⨾ ⦗R ∩₁ Acq⦘) ⨾ (Cppo ∪ bob certG) ⨾ ⦗I⦘) ⊆₁ I) as BB.
  { arewrite (⦗I⦘ ⊆ ⦗D⦘ ;; ⦗I⦘).
    { generalize I_in_D. clear. basic_solver. }
    arewrite ((Cppo ∪ bob certG) ⨾ ⦗D⦘ ⊆ Gar_int).
    { rewrite seq_union_l. unionL.
      2: { rewrite cert_bob; eauto. rewrite bob_in_ar_int. clear. basic_solver. }
      rewrite <- ppo_in_ar_int.
      eapply cert_ppo_D; eauto. }
    arewrite (⦗GW_ex⦘ ⊆ ⦗W⦘ ;; ⦗GW_ex⦘).
    { generalize WF.(W_ex_in_W). clear. basic_solver. }
    arewrite (⦗GW_ex⦘ ⨾ Grfi ⨾ ⦗R ∩₁ Acq⦘ ⊆ Gar_int).
    arewrite (Gar_int ⨾ Gar_int ⊆ Gar_int⁺).
    { by rewrite <- ct_ct, <- ct_step. }
    arewrite (Gar_int ⊆ Gar ∪ Grf ⨾ Grmw); auto. }

  constructor.
  all: try by ins.
  { ins; rewrite cert_W; edone. }
  { rewrite rfi_union_rfe; relsf; unionL; splits; ins.
    { rewrite (dom_l (wf_rfiD WF_cert)), cert_W; eauto.
      arewrite (Crfi ⊆ Gsb).
      generalize tc_sb_C, tc_W_C_in_I. basic_solver 21. }
    rewrite (dom_rel_helper AA).
    basic_solver 21. }
  { ins; rewrite cert_W; edone. }
  { ins; rewrite cert_fwbob; edone. }
  { rewrite cert_W_ex, cert_R, cert_Acq; eauto.
    arewrite (⦗GW_ex⦘ ⨾ Crfi ⨾ ⦗R ∩₁ Acq⦘ ⊆ ⦗GW_ex⦘ ⨾ Grfi ⨾ ⦗R ∩₁ Acq⦘).
    { arewrite (⦗R ∩₁ Acq⦘ ⊆ ⦗Acq⦘ ;; ⦗R ∩₁ Acq⦘).
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
    rewrite cert_sb. eapply tc_W_ex_sb_I; eauto.
    apply tc_coherent_implies_tc_coherent_alt; eauto. }
  simpls.
  arewrite (Grmw ⨾ ⦗I⦘ ⊆ ⦗D⦘ ⨾ Grmw ⨾ ⦗I⦘).
  { apply dom_rel_helper.
    rewrite rmw_in_ppo; auto.
    rewrite I_in_D.
    eapply dom_ppo_D; edone. }
  rewrite cert_rfi_eq.
  forward (eapply cert_rfi_D with (G:=G) (T:=T) (S:=S) (thread:=thread)); eauto.
  intros HH. sin_rewrite HH.
  arewrite_id ⦗D⦘. rewrite !seq_id_l.
  arewrite (Grfi ⊆ Grf).
  eapply rfrmw_I_in_I; eauto.
Unshelve.
all:auto.
Qed.

Lemma dom_cert_ar_rfrmw_I : dom_rel (⦗is_w certG.(lab)⦘ ⨾ (Car ∪ Crf ⨾ rmw certG)⁺ ⨾ ⦗I⦘) ⊆₁ I.
Proof using All.
  eapply otc_I_ar_rfrmw_I_implied_helper_2 with (T:=mkTC (C ∪₁ (E ∩₁ NTid_ thread)) I).
  { apply WF_cert. }
  { apply cert_imm_consistent. }
  apply TCCOH_cert_old.
Qed.

Lemma TCCOH_cert : tc_coherent certG sc (mkTC (C ∪₁ (E ∩₁ NTid_ thread)) I).
Proof using All.
  assert (TCCOH1:= TCCOH_rst_new_T).
  apply (tc_coherent_implies_tc_coherent_alt WF WF_SC) in TCCOH1.
  destruct TCCOH1.
  apply tc_coherent_alt_implies_tc_coherent; constructor.
  all: try by ins.
  { ins; rewrite cert_W; edone. }
  { rewrite rfi_union_rfe; relsf; unionL; splits; ins.
    2: { rewrite cert_rfe_eq.
         arewrite_id ⦗C ∪₁ E ∩₁ NTid_ thread⦘. rewrite seq_id_r.
         eapply dom_cert_rfe_in_I with (G:=G); eauto. }
    rewrite (dom_l (wf_rfiD WF_cert)), cert_W; eauto.
    arewrite (Crfi ⊆ Gsb).
    generalize tc_sb_C, tc_W_C_in_I; basic_solver 21. }
  { ins; rewrite cert_W; edone. }
  { ins; rewrite cert_fwbob; edone. }
  ins. apply dom_cert_ar_rfrmw_I.
Qed.

Lemma cert_detour_rfe_D : (Cdetour ∪ certG.(rfe)) ⨾ ⦗D⦘ ⊆ ⦗I⦘ ⨾ (Gdetour ∪ Grfe).
Proof using All.
  rewrite seq_union_l.
  forward (eapply cert_detour_D with (G:=G)); eauto. intros HH. rewrite HH.
  forward (eapply cert_rfe_D with (G:=G)); eauto. intros AA. rewrite AA. 
    by rewrite seq_union_r.
Qed.

Lemma dom_cert_detour_rfe_D : dom_rel ((Cdetour ∪ certG.(rfe)) ⨾ ⦗D⦘) ⊆₁ I.
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
Proof using Grfe_E TCCOH WF WF_SC.
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

Lemma ETCCOH_cert (ST_in_W_ex : S ∩₁ Tid_ thread \₁ I ⊆₁ GW_ex)
      (ISTex_rf_I : (I ∪₁ S ∩₁ Tid_ thread) ∩₁ GW_ex ⊆₁ codom_rel (⦗I⦘ ⨾ Grf ⨾ Grmw))
      (DOM_SB_S_rf_I :
         dom_rel (⦗GW_ex⦘ ⨾ Gsb ⨾ ⦗I ∪₁ S ∩₁ Tid_ thread⦘) ∩₁ codom_rel (⦗I⦘ ⨾ Grf ⨾ ⦗GR_ex⦘ ⨾ Grmw)
                 ⊆₁ I ∪₁ S ∩₁ Tid_ thread) :
  etc_coherent certG sc (mkETC (mkTC (C ∪₁ (E ∩₁ NTid_ thread)) I)
                               (I ∪₁ S ∩₁ Tid_ thread)).
Proof using All.
  assert (I ∪₁ S ∩₁ Tid_ thread ⊆₁ S) as IST_in_S.
  { rewrite I_in_S. basic_solver. }

(*  assert ((Grf ⨾ ⦗D⦘ ∪ new_rf) ⨾ Grmw ≡ Grf ⨾ Grmw) as QQ.
  { rewrite (dom_rel_helper dom_rmw_in_D).
    rewrite wf_new_rfE. clear. basic_solver 10. }*)
  constructor.
  all: unfold eissued, ecovered; simpls.
  { apply TCCOH_cert. }
  { arewrite (I ∪₁ S ∩₁ Tid_ thread ⊆₁ E ∩₁ W).
    2: { unfold CertExecution2.certG. unfold acts_set. basic_solver. }
    rewrite <- IST_new_co; try edone.
    rewrite IST_in_cert_co_base; try edone.
    basic_solver 10. }
  { eauto with hahn. }
  { rewrite cert_W_ex. generalize ST_in_W_ex.
    basic_solver. }
  { rewrite cert_F, cert_AcqRel, cert_sb, IST_in_S; eauto. admit. }
  { rewrite cert_sb, cert_Acq, cert_R; eauto.
  admit.
(*    unfolder. intros x [y [z [DRF [[RZ ACQZ] [SB SS]]]]].
    assert (exists w, rfe certG w z) as [w CRFE].
    { destruct DRF as [DRF|]; eauto.
      clear -DRF.
      red in DRF. unfolder in DRF. desf.
      eauto. }
    set (AA:=CRFE).
    apply cert_rfe in AA.
    destruct AA as [RFE|NRFE].
    2: { exfalso. eapply new_rfe_Acq.
         apply seq_eqv_r. split; [|split]; eauto.
         apply seq_eqv_l in NRFE. apply NRFE. }
    apply seq_eqv_lr in RFE. destruct RFE as [IW [RFE DZ]].
    eapply dom_cert_detour_rfe_D. basic_solver 10. *)
    }
  { rewrite cert_W_ex, cert_xacq, cert_sb, IST_in_S, W_ex_acq_in_I; basic_solver. }
  { unfold dom_sb_S_rfrmw. simpls.
    rewrite cert_sb, cert_W_ex.
    rewrite !seqA.
    arewrite (cert_rf ⨾ ⦗R_ex lab'⦘ ⨾ Grmw ⊆ Grf ⨾ ⦗GR_ex⦘ ⨾ Grmw); auto.
    admit. }
    (* arewrite (Gctrl ⊆ <|D|> ;; Gctrl) at 1. *)
    (* { apply dom_rel_helper. eapply dom_ctrl_in_D; eauto. } *)
    (* arewrite (Grmw ∩ (⦗D⦘ ⨾ Gctrl) ⊆ ⦗D⦘ ⨾ (Grmw ∩ Gctrl)). *)
    (* { clear. basic_solver. } *)
    (* arewrite (cert_rf ⨾ ⦗D⦘ ⊆ Grf ⨾ ⦗D⦘); [|clear; basic_solver]. *)
    (* eapply cert_rf_D; eauto. } *)
  { rewrite Crppo_in_rppo.
    admit. }
    (* arewrite (Grppo ⨾ ⦗I ∪₁ S ∩₁ Tid_ thread⦘ ⊆ *)
    (*               ⦗D⦘ ⨾ Grppo ⨾ ⦗I ∪₁ S ∩₁ Tid_ thread⦘). *)
    (* { apply dom_rel_helper. *)
    (*   rewrite IST_in_S. *)
    (*   apply dom_rppo_S_in_D. } *)
    (* arewrite ((Gdata ∪ Crfi ∪ Grmw)＊ ⨾ ⦗D⦘ ⊆ ⦗D⦘ ⨾ (Gdata ∪ Crfi ∪ Grmw)＊ ⨾ ⦗D⦘). *)
    (* { apply dom_rel_helper. *)
    (*   eapply dom_data_Crfi_rmw_D_in_D. } *)
    (* rewrite <- !seqA. *)
    (* do 4 rewrite AuxRel.dom_seq. *)
    (* apply dom_cert_detour_rfe_D. } *)
  admit.
  admit.
Admitted.

End CertExec_tc.
