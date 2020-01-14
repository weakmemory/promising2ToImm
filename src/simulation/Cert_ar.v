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
Require Import CertExecution2.

Set Implicit Arguments.
Remove Hints plus_n_O.

Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'NTid_' t" := (fun x => tid x <> t) (at level 1).

Section CertExec_ar.

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
Hypothesis ST_in_E : S ∩₁ Tid_ thread ⊆₁ E.
Hypothesis I_in_S : I ⊆₁ S.
Hypothesis W_ex_acq_in_I :GW_ex_acq ⊆₁ I.

Hypothesis F_in_C : E ∩₁ F ∩₁ Acq/Rel ⊆₁ C.

Hypothesis S_I_in_W_ex : (S ∩₁ Tid_ thread) \₁ I ⊆₁ W_ex G.

Hypothesis ETC_DR_R_ACQ_I : dom_rel ((Gdetour ∪ Grfe) ⨾ (Grmw ⨾ Grfi)^* ⨾ ⦗R∩₁Acq⦘ ⨾ Gsb ⨾ ⦗S⦘) ⊆₁ I.

Hypothesis COMP_R_ACQ_SB : dom_rel ((Grmw ⨾ Grfi)＊ ⨾ ⦗E ∩₁ R ∩₁ Acq⦘) ⊆₁ codom_rel Grf.

Variable lab' : actid -> label.
Hypothesis SAME : same_lab_u2v lab' Glab.

Notation "'certG'" := (certG G sc T S thread lab').


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

(* TODO: move *)
Lemma ppo_helper : Cppo ⊆
 ⦗CR⦘ ⨾ (certG.(data) ∪ certG.(ctrl) ∪ certG.(addr) ⨾ Csb^? ∪ Crfi ∪ Crmw ∪ certG.(rmw_dep) ⨾ Csb^?)^+ ⨾  
   (⦗(R_ex certG.(lab)) \₁ dom_rel Crmw⦘ ⨾ Csb)^?⨾ ⦗CW⦘.
Proof.
Admitted.

Lemma Cppo_in_Gar_int_ct : Cppo ;; <| dom_rel (Gar_int^+ ;; <| I |>) |> ⊆ Gar_int^+.
Proof.
unfold ppo.
Admitted.

Lemma Cppo_in_Gar_int_ct : Cppo ;; <| dom_rel (Car_int^+ ;; <| I |>) |> ⊆ Gar_int^+.
Proof.
unfold ppo.
Admitted.

Lemma Cppo_in_Gar_int_ct : Car_int^+ ;; <| I |> ⊆ Gar_int^+.
Proof.
unfold ppo.
Admitted.


Lemma cert_ppo_D : Cppo ⨾ ⦗ D ⦘ ⊆ Gppo.
Proof using All.
rewrite ppo_helper.
unfold ppo; ins.

rewrite cert_R, cert_W, cert_sb, cert_R_ex, !seqA.

arewrite ((⦗GR_ex \₁ dom_rel Grmw⦘ ⨾ Gsb)^? ⨾ ⦗W⦘ ⨾ ⦗D⦘ ⊆ ⦗D⦘ ;; (⦗GR_ex \₁ dom_rel Grmw⦘ ⨾ Gsb)^? ⨾ ⦗W⦘).
{ rewrite crE, !seq_union_l, !seqA.
  forward (eapply dom_R_ex_fail_sb_D); try edone.
  clear; basic_solver 12. }

rewrite <- ct_cr with (r:=(Gdata ∪ Gctrl ∪ Gaddr ⨾ Gsb^? ∪ Grfi ∪ Grmw ∪ Grmw_dep ⨾ Gsb^? ∪ ⦗GR_ex \₁ dom_rel Grmw⦘ ⨾ Gsb)).
hahn_frame_r.
rewrite <- !seqA.
apply seq_mori; [|clear; basic_solver 12].



remember (Gdata ∪ Gctrl ∪ Gaddr ⨾ Gsb^? ∪ Grmw ∪ Grmw_dep ⨾ Gsb^?) as X.

arewrite (Gdata ∪ Gctrl ∪ Gaddr ⨾ Gsb^? ∪ Crfi ∪ Grmw ∪ Grmw_dep ⨾ Gsb^? ⊆ X ∪ Crfi).
{ subst X; clear; basic_solver 12. }

assert (XX: X ∪ Grfi ⊆ Gdata ∪ Gctrl ∪ Gaddr ⨾ Gsb^? ∪ Grfi ∪ Grmw ∪ Grmw_dep ⨾ Gsb^? ∪ ⦗GR_ex \₁ dom_rel Grmw⦘ ⨾ Gsb).
{ subst X; clear; basic_solver 12. }
rewrite <- XX.
(* arewrite (⦗W⦘ ⨾ ⦗D⦘ ⊆ ⦗D⦘ ⨾ ⦗W⦘) by basic_solver. *)
(* hahn_frame. *)
rewrite path_union; relsf; unionL.
generalize inclusion_t_t; basic_solver.
rewrite !seqA.

assert (X_D_helper: dom_rel (X ⨾ ⦗D⦘) ⊆₁ D).
{ rewrite HeqX.
  relsf; unionL; splits.
  eby eapply dom_data_D.
  etransitivity; [|eby eapply dom_ctrl_in_D]; basic_solver.
  etransitivity; [|eby eapply dom_addr_in_D]; basic_solver.
  etransitivity; [|eby eapply dom_rmw_D]; basic_solver.
  etransitivity; [|eby eapply dom_frmw_in_D]; basic_solver. }

assert (X_D: dom_rel (X＊ ⨾ ⦗D⦘) ⊆₁ D).
{ cut (X＊ ⨾ ⦗D⦘ ⊆ ⦗D⦘ ⨾ (fun _ _ => True)).
by unfolder; ins; desf; eapply H; eauto.
apply rt_ind_right with (P:= fun r =>  r ⨾ ⦗D⦘).
- by eauto with hahn.
- basic_solver.
- intros h H; rewrite !seqA.
rewrite (dom_rel_helper X_D_helper); sin_rewrite H.
basic_solver. }


rewrite (dom_rel_helper X_D).
enough ((X＊ ⨾ Crfi)⁺ ⨾ ⦗D⦘ ⊆ (X ∪ Grfi)⁺).
sin_rewrite H; arewrite (X ⊆ (X ∪ Grfi)⁺) at 2; relsf; basic_solver.


apply ct_ind_right with (P:= fun r =>  r ⨾ ⦗D⦘).
- by eauto with hahn.
- rewrite !seqA, ct_end. 

arewrite (X ⊆ X ∪ Grfi) at 1.
rewrite cert_rfi_D.
basic_solver 12.

- intros k H.
rewrite !seqA.
rewrite cert_rfi_D.

seq_rewrite (dom_rel_helper X_D).
rewrite !seqA.
sin_rewrite H.
arewrite_id ⦗D⦘.
arewrite (X ⊆ X ∪ Grfi) at 2.
arewrite (Grfi ⊆ (X ∪ Grfi)＊) at 3.
relsf.
Qed.

Lemma cert_ppo_CI : Cppo ⨾ ⦗ C ∪₁ I ⦘ ⊆ Gppo.
Proof using All.
rewrite C_in_D, I_in_D; relsf.
apply cert_ppo_D.
Qed.

Lemma cert_detour_D : Cdetour ⨾ ⦗ D ⦘ ⊆ ⦗ I ⦘ ⨾ Gdetour.
Proof using ACYC_EXT COH CSC Grfe_E IT_new_co RPPO_S ST_in_E S_in_W TCCOH WF WF_SC
      detour_Acq_E detour_E.
  enough (Cdetour ⨾ ⦗ D ⦘ ⊆ Gdetour).
  { arewrite (⦗D⦘ ⊆ ⦗D⦘ ⨾ ⦗D⦘) by basic_solver.
    sin_rewrite H.
    forward (eapply dom_detour_D with (T:=T)); try edone.
    clear. basic_solver. }
  unfold detour, Execution.coe.
  rewrite cert_sb.
  rewrite <- seq_eqv_inter_lr, !seqA.
  rewrite cert_rfe_D.
  rewrite I_in_cert_co_base with (G:=G).
  seq_rewrite <- seq_eqv_minus_lr.
  ins; rewrite cert_co_I; try edone.
  clear. basic_solver 21.
Qed.

Lemma cert_detour_R_Acq_sb_D : Cdetour ⨾ ⦗R∩₁Acq⦘ ⨾ Gsb ⨾ ⦗ D ⦘ ⊆ 
  ⦗ I ⦘ ⨾ Gdetour ⨾ ⦗R∩₁Acq⦘ ⨾ Gsb.
Proof using All.
  rewrite (detour_to_codom_rfe WF_cert), !seqA.
  rewrite cert_rfe.
  rewrite codom_union, id_union; relsf; unionL.
  arewrite (⦗codom_rel (⦗I⦘ ⨾ Grfe ⨾ ⦗D⦘)⦘ ⊆ ⦗D⦘) by basic_solver.
  sin_rewrite cert_detour_D; basic_solver 40.
  unfolder; ins; desf; exfalso.
  generalize new_rfe_Acq. basic_solver 21.
Qed.





Lemma cert_ar_int_I : Car_int⁺ ⨾ ⦗ C ∪₁ I ⦘ ⊆ ⦗ D ∪₁ R ∩₁ Acq ⦘ ⨾ Gar_int⁺.
Proof.

rewrite (ct_ar_int_alt WF_cert).
2: by apply (coherence_sc_per_loc cert_coherence).
rewrite cert_R, cert_Acq, cert_sb, cert_W_ex_acq, cert_W.
rewrite cert_same_loc, cert_Rel, cert_AcqRel, cert_F, cert_W_ex.
  arewrite (⦗R ∩₁ Acq⦘ ⊆ ⦗Acq⦘ ;; ⦗R ∩₁ Acq⦘) at 3.
  { clear; basic_solver. }
  sin_rewrite Crfi_to_Acq_in_Grf.

relsf; unionL.
- unfold ar_int, bob, fwbob.
case_refl Gsb.
rewrite (dom_l (@wf_sbE G)) at 1.
generalize E_F_AcqRel_in_C, C_in_D.
rewrite <- ct_step; basic_solver 12.
rewrite (dom_l (@wf_sbE G)) at 2.
generalize E_F_AcqRel_in_C, (dom_sb_covered TCCOH), C_in_D.
rewrite ct_begin, <- inclusion_t_rt, <- ct_step; basic_solver 32.
- unfold ar_int, bob.
rewrite <- ct_step; basic_solver 12.
- unfold ar_int, bob, fwbob.
case_refl Gsb.
rewrite (dom_r (@wf_sbE G)) at 1.
generalize E_F_AcqRel_in_C, (dom_sb_covered TCCOH), C_in_D.
rewrite <- ct_step; basic_solver 21.
rewrite (dom_r (@wf_sbE G)) at 1.
generalize E_F_AcqRel_in_C, (dom_sb_covered TCCOH), C_in_D.
rewrite ct_begin, <- inclusion_t_rt, <- ct_step; basic_solver 32.
- unfold ar_int, bob, fwbob.
rewrite W_rel_sb_loc_W_CI.
generalize C_in_D, I_in_D.
rewrite <- ct_step; basic_solver 21.
- unfold ar_int, bob, fwbob.
rewrite !seqA.
rewrite (cr_helper W_rel_sb_loc_W_CI).
rewrite <- seqA.
sin_rewrite sb_W_rel_CI.
generalize C_in_D, I_in_D.
rewrite <- ct_cr, <- ct_step; basic_solver 32.

- rewrite !seqA.
rewrite (cr_helper W_rel_sb_loc_W_CI).

arewrite ((⦗W ∩₁ Rel⦘ ⨾ Gsb ∩ Gsame_loc ⨾ ⦗W⦘)^?  ⊆ Gar_int^?) at 1.
unfold ar_int, bob, fwbob; basic_solver 21.

rewrite <- (ct_cr Gar_int).
hahn_frame_r.

arewrite (Cppo ⨾ ⦗C ∪₁ I⦘ ⊆ Gppo⨾ ⦗C ∪₁ I⦘).
generalize cert_ppo_CI; basic_solver 12.

arewrite (Gppo ⨾ ⦗C ∪₁ I⦘ ⊆ ⦗D⦘ ⨾ Gppo).
rewrite C_in_D, I_in_D; generalize dom_ppo_D; basic_solver.


rewrite <-ct_step.

unfold ar_int; basic_solver 12.

- rewrite !seqA.
rewrite (cr_helper W_rel_sb_loc_W_CI).


arewrite ((⦗W ∩₁ Rel⦘ ⨾ Gsb ∩ Gsame_loc ⨾ ⦗W⦘)^?  ⊆ Gar_int^?) at 3.
unfold ar_int, bob, fwbob; basic_solver 21.

rewrite <- (ct_cr Gar_int).
hahn_frame_r.


arewrite (Cppo^? ⨾ ⦗C ∪₁ I⦘ ⊆ Gppo^?⨾ ⦗C ∪₁ I⦘).
generalize cert_ppo_CI; basic_solver 12.

arewrite (Gppo^? ⨾ ⦗C ∪₁ I⦘ ⊆ ⦗D⦘ ⨾ Gppo^?).
rewrite C_in_D, I_in_D; generalize dom_ppo_D; basic_solver.

arewrite (Gppo^?  ⊆ Gar_int^?).
unfold ar_int; basic_solver 12.

rewrite <- (ct_cr Gar_int).
hahn_frame_r.

apply ct_inclusion_from_rt_inclusion1.

{ rewrite detour_in_sb, !(ppo_in_sb WF_cert).
arewrite_id ⦗W⦘ at 1.
arewrite_id ⦗W⦘ at 1.
arewrite_id ⦗R ∩₁ Acq⦘ at 1.
arewrite_id  ⦗W ∩₁ Rel⦘ at 1.
arewrite_id  ⦗W ∩₁ Rel⦘ at 1.
arewrite_id  ⦗W ∩₁ Rel⦘ at 1.
arewrite_id  ⦗GW_ex_acq⦘ at 1.
arewrite (Gsb ∩ Gsame_loc ⊆ Gsb) at 1.
arewrite_id  ⦗W ∩₁ Rel⦘ at 1.
arewrite_id  ⦗GW_ex⦘ at 1.
arewrite (Gsb ∩ Gsame_loc ⊆ Gsb) at 1.
arewrite_id ⦗R ∩₁ Acq⦘ at 1.
arewrite (Grfi ⊆ Gsb) at 1.

rewrite cert_sb.
arewrite_id  ⦗W ∩₁ Rel⦘ at 1.
arewrite_id ⦗W⦘ at 1.
generalize (@sb_trans G); ins; relsf.
apply sb_acyclic. }



apply rt_ind_right with (P:= fun r =>  r ⨾ ⦗D⦘).
by auto with hahn.
by basic_solver.

intros k H; rewrite !seqA.

 relsf; unionL.
* case_refl (⦗R ∩₁ Acq⦘ ⨾ Gsb).
+
rewrite cert_detour_D.

arewrite (Gdetour  ⊆ Gar_int).
rewrite (rt_end Gar_int); relsf; unionR right.
hahn_frame_r.

arewrite (⦗I⦘ ⊆ ⦗C ∪₁ I⦘).


rewrite (cr_helper sb_W_rel_CI).

arewrite ((Gsb ⨾ ⦗W ∩₁ Rel⦘)^?  ⊆ Gar_int^?).
unfold ar_int, bob, fwbob; basic_solver 21.
rewrite <- (rt_cr Gar_int).
hahn_frame_r.

arewrite (Cppo^? ⨾ ⦗C ∪₁ I⦘ ⊆ Gppo^? ⨾ ⦗C ∪₁ I⦘).
generalize cert_ppo_CI; basic_solver 12.

arewrite (Gppo^? ⨾ ⦗C ∪₁ I⦘ ⊆ ⦗D⦘ ⨾ Gppo^?  ).
rewrite C_in_D, I_in_D; generalize dom_ppo_D; basic_solver.

arewrite (Gppo ⊆ Gar_int).
rewrite <- (rt_cr Gar_int).
hahn_frame_r.

done.

+
rewrite !seqA, cert_detour_R_Acq_sb_D.
arewrite (⦗R ∩₁ Acq⦘ ⨾ Gsb  ⊆ Gar_int).
by unfold ar_int, bob, fwbob; basic_solver 21.

rewrite (rt_end Gar_int); relsf; unionR right.
hahn_frame_r.

arewrite (Gdetour  ⊆ Gar_int^?).
rewrite <- (rt_cr Gar_int).
hahn_frame_r.
arewrite (⦗I⦘ ⊆ ⦗C ∪₁ I⦘).
rewrite (cr_helper sb_W_rel_CI).

arewrite ((Gsb ⨾ ⦗W ∩₁ Rel⦘)^?  ⊆ Gar_int^?).
unfold ar_int, bob, fwbob; basic_solver 21.
rewrite <- (rt_cr Gar_int).
hahn_frame_r.


arewrite (Cppo^? ⨾ ⦗C ∪₁ I⦘ ⊆ Gppo^? ⨾ ⦗C ∪₁ I⦘).
generalize cert_ppo_CI; basic_solver 12.

arewrite (Gppo^? ⨾ ⦗C ∪₁ I⦘ ⊆ ⦗D⦘ ⨾ Gppo^?  ).
rewrite C_in_D, I_in_D; generalize dom_ppo_D; basic_solver.

arewrite (Gppo ⊆ Gar_int).
rewrite <- (rt_cr Gar_int).
hahn_frame_r.

done.
* 

rewrite (dom_l (@wf_sbE G)) at 3; rewrite !seqA.

arewrite (⦗GW_ex_acq⦘ ⨾ ⦗E⦘ ⊆ ⦗C ∪₁ I⦘ ⨾ ⦗GW_ex_acq⦘ ⨾ ⦗E⦘).
generalize W_ex_acq_sb_S1; basic_solver 21.

arewrite (⦗GW_ex_acq⦘ ⨾ ⦗E⦘ ⨾ Gsb ⨾ ⦗W⦘  ⊆ Gar_int^?).
by unfold ar_int, bob, fwbob; basic_solver 21.
arewrite_id ⦗D⦘; rels.
rewrite <- (rt_cr Gar_int).
hahn_frame_r.
rewrite (cr_helper W_rel_sb_loc_W_CI).

arewrite ((⦗W ∩₁ Rel⦘ ⨾ Gsb ∩ Gsame_loc ⨾ ⦗W⦘)^?  ⊆ Gar_int^?) at 1.
unfold ar_int, bob, fwbob; basic_solver 21.

rewrite <- (rt_cr Gar_int).
hahn_frame_r.

rewrite (cr_helper sb_W_rel_CI).

arewrite ((Gsb ⨾ ⦗W ∩₁ Rel⦘)^?  ⊆ Gar_int^?).
unfold ar_int, bob, fwbob; basic_solver 21.
rewrite <- (rt_cr Gar_int).
hahn_frame_r.

arewrite (Cppo^? ⨾ ⦗C ∪₁ I⦘ ⊆ Gppo^? ⨾ ⦗C ∪₁ I⦘).
generalize cert_ppo_CI; basic_solver 12.

arewrite (Gppo^? ⨾ ⦗C ∪₁ I⦘ ⊆ ⦗D⦘ ⨾ Gppo^?  ).
rewrite C_in_D, I_in_D; generalize dom_ppo_D; basic_solver.

arewrite (Gppo ⊆ Gar_int).
rewrite <- (rt_cr Gar_int).
hahn_frame_r.

done.

*
SearchAbout Grf Acq.
Print ar_int.
Print D.
SearchAbout sb D.
rewrite (dom_l WF.(wf_rfiE)).

rewrite !seqA.

arewrite (⦗GW_ex⦘ ⨾ ⦗E⦘ ⊆ ⦗C ∪₁ I⦘ ⨾ ⦗GW_ex⦘).
generalize W_ex_E; basic_solver 21.

arewrite (⦗GW_ex⦘ ⊆ ⦗GW_ex⦘ ;; ⦗set_compl Init⦘).
by generalize (W_ex_not_init WF); basic_solver.
sin_rewrite cert_rfi_Acq.
rewrite !seqA.

arewrite (⦗R ∩₁ Acq⦘ ⊆ ⦗R ∩₁ Acq⦘ ;; ⦗R ∩₁ Acq⦘).
basic_solver.
arewrite (⦗R ∩₁ Acq⦘ ⨾ Gsb^? ⊆ Gar_int^?).
unfold ar_int, bob, fwbob; basic_solver 21.
arewrite (⦗GW_ex⦘ ⨾ Grfi ⨾ ⦗R ∩₁ Acq⦘ ⊆ Gar_int^* ).
rels.

arewrite_id ⦗D⦘; rels.
rewrite <- (rt_rt Gar_int) at 2.
hahn_frame_r.
rewrite (cr_helper W_rel_sb_loc_W_CI).

arewrite ((⦗W ∩₁ Rel⦘ ⨾ Gsb ∩ Gsame_loc ⨾ ⦗W⦘)^?  ⊆ Gar_int^?) at 1.
unfold ar_int, bob, fwbob; basic_solver 21.

rewrite <- (rt_cr Gar_int).
hahn_frame_r.

rewrite (cr_helper sb_W_rel_CI).

arewrite ((Gsb ⨾ ⦗W ∩₁ Rel⦘)^?  ⊆ Gar_int^?).
unfold ar_int, bob, fwbob; basic_solver 21.
rewrite <- (rt_cr Gar_int).
hahn_frame_r.

arewrite (Cppo^? ⨾ ⦗C ∪₁ I⦘ ⊆ Gppo^? ⨾ ⦗C ∪₁ I⦘).
generalize cert_ppo_CI; basic_solver 12.

arewrite (Gppo^? ⨾ ⦗C ∪₁ I⦘ ⊆ ⦗D⦘ ⨾ Gppo^?  ).
rewrite C_in_D, I_in_D; generalize dom_ppo_D; basic_solver.

arewrite (Gppo ⊆ Gar_int).
rewrite <- (rt_cr Gar_int).
hahn_frame_r.

done.
Qed.

*)

(*
Lemma cert_ar_int_I : Car_int⁺ ⨾ ⦗ C ∪₁ I ⦘ ⊆ ⦗ D ∪₁ R ∩₁ Acq ⦘ ⨾ Gar_int⁺.
Proof using All.
  rewrite (ct_ar_int_alt WF_cert).
  2: by apply (coherence_sc_per_loc cert_coherence).
  rewrite cert_R, cert_Acq, cert_sb, cert_W_ex_acq, cert_W.
  rewrite cert_same_loc, cert_Rel, cert_AcqRel, cert_F, cert_W_ex.
  arewrite (⦗R ∩₁ Acq⦘ ⊆ ⦗Acq⦘ ;; ⦗R ∩₁ Acq⦘) at 3.
  { clear; basic_solver. }
  sin_rewrite Crfi_to_Acq_in_Grf.

  relsf; unionL.
  { unfold ar_int, bob, fwbob.
    case_refl Gsb.
    { rewrite (dom_l (@wf_sbE G)) at 1.
      generalize E_F_AcqRel_in_C, C_in_D.
      rewrite <- ct_step. basic_solver 12. }
    rewrite (dom_l (@wf_sbE G)) at 2.
    generalize E_F_AcqRel_in_C, (dom_sb_covered TCCOH), C_in_D.
    rewrite ct_begin, <- inclusion_t_rt, <- ct_step.
    basic_solver 32. }
  { unfold ar_int, bob.
    rewrite <- ct_step. basic_solver 12. }
  { unfold ar_int, bob, fwbob.
    case_refl Gsb.
    { rewrite (dom_r (@wf_sbE G)) at 1.
      generalize E_F_AcqRel_in_C, (dom_sb_covered TCCOH), C_in_D.
      rewrite <- ct_step. basic_solver 21. }
    rewrite (dom_r (@wf_sbE G)) at 1.
    generalize E_F_AcqRel_in_C, (dom_sb_covered TCCOH), C_in_D.
    rewrite ct_begin, <- inclusion_t_rt, <- ct_step.
    basic_solver 32. }
  { unfold ar_int, bob, fwbob.
    rewrite W_rel_sb_loc_W_CI.
    generalize C_in_D, I_in_D.
    rewrite <- ct_step.
    basic_solver 21. }
  { unfold ar_int, bob, fwbob.
    rewrite !seqA.
    rewrite (cr_helper W_rel_sb_loc_W_CI).
    rewrite <- seqA.
    sin_rewrite sb_W_rel_CI.
    generalize C_in_D, I_in_D.
    rewrite <- ct_cr, <- ct_step.
    basic_solver 32. }
  { rewrite !seqA.
    rewrite (cr_helper W_rel_sb_loc_W_CI).

    arewrite ((⦗W ∩₁ Rel⦘ ⨾ Gsb ∩ Gsame_loc ⨾ ⦗W⦘)^?  ⊆ Gar_int^?) at 1.
    { unfold ar_int, bob, fwbob. basic_solver 21. }
    rewrite <- (ct_cr Gar_int).
    hahn_frame_r.
    arewrite (Cppo ⨾ ⦗C ∪₁ I⦘ ⊆ Gppo⨾ ⦗C ∪₁ I⦘).
    { generalize cert_ppo_CI; basic_solver 12. }
    arewrite (Gppo ⨾ ⦗C ∪₁ I⦘ ⊆ ⦗D⦘ ⨾ Gppo).
    { rewrite C_in_D, I_in_D; generalize dom_ppo_D; basic_solver. }
    rewrite <- ct_step.
    unfold ar_int. basic_solver 12. }
  rewrite !seqA.
  rewrite (cr_helper W_rel_sb_loc_W_CI).
  arewrite ((⦗W ∩₁ Rel⦘ ⨾ Gsb ∩ Gsame_loc ⨾ ⦗W⦘)^?  ⊆ Gar_int^?) at 2.
  { unfold ar_int, bob, fwbob. basic_solver 21. }
  
  SearchAbout 
  arewrite (⦗GW_ex⦘ ⨾ Grfi ⨾ ⦗R ∩₁ Acq⦘ ⨾ Gsb^?  ⊆ Gar_int^?) at 2.
  { unfold ar_int, bob, fwbob. basic_solver 21. }

  
  
  
  rewrite <- (ct_cr Gar_int).
  hahn_frame_r.
  arewrite (Cppo^? ⨾ ⦗C ∪₁ I⦘ ⊆ Gppo^?⨾ ⦗C ∪₁ I⦘).
  { generalize cert_ppo_CI. basic_solver 12. }
  arewrite (Gppo^? ⨾ ⦗C ∪₁ I⦘ ⊆ ⦗D⦘ ⨾ Gppo^?).
  { rewrite C_in_D, I_in_D. generalize dom_ppo_D. basic_solver. }
  arewrite (Gppo^? ⊆ Gar_int^?).
  rewrite <- (ct_cr Gar_int).
  hahn_frame_r.
  apply ct_inclusion_from_rt_inclusion1.
  { rewrite detour_in_sb, !(ppo_in_sb WF_cert).
    arewrite_id ⦗W⦘ at 1.
    arewrite_id ⦗W⦘ at 1.
    arewrite_id ⦗R ∩₁ Acq⦘ at 1.
    arewrite_id  ⦗W ∩₁ Rel⦘ at 1.
    arewrite_id  ⦗W ∩₁ Rel⦘ at 1.
    arewrite_id  ⦗W ∩₁ Rel⦘ at 1.
    arewrite_id  ⦗GW_ex_acq⦘ at 1.
    arewrite (Gsb ∩ Gsame_loc ⊆ Gsb) at 1.
    rewrite cert_sb.
    generalize (@sb_trans G); ins; relsf.
    apply sb_acyclic. }

  apply rt_ind_right with (P:= fun r =>  r ⨾ ⦗D⦘).
  { auto with hahn. }
  { basic_solver. }
  intros k H; rewrite !seqA.
  relsf; unionL.
  { case_refl (⦗R ∩₁ Acq⦘ ⨾ Gsb).
    { rewrite cert_detour_D.
      arewrite (Gdetour  ⊆ Gar_int).
      rewrite (rt_end Gar_int); relsf; unionR right.
      hahn_frame_r.
      arewrite (⦗I⦘ ⊆ ⦗C ∪₁ I⦘).
      rewrite (cr_helper sb_W_rel_CI).
      arewrite ((Gsb ⨾ ⦗W ∩₁ Rel⦘)^?  ⊆ Gar_int^?).
      { unfold ar_int, bob, fwbob. basic_solver 21. }
      rewrite <- (rt_cr Gar_int).
      hahn_frame_r.
      arewrite (Cppo^? ⨾ ⦗C ∪₁ I⦘ ⊆ Gppo^? ⨾ ⦗C ∪₁ I⦘).
      { generalize cert_ppo_CI. basic_solver 12. }
      arewrite (Gppo^? ⨾ ⦗C ∪₁ I⦘ ⊆ ⦗D⦘ ⨾ Gppo^?  ).
      { rewrite C_in_D, I_in_D. generalize dom_ppo_D. basic_solver. }
      arewrite (Gppo ⊆ Gar_int).
      rewrite <- (rt_cr Gar_int). by hahn_frame_r. }
    rewrite !seqA, cert_detour_R_Acq_sb_D.
    arewrite (⦗R ∩₁ Acq⦘ ⨾ Gsb  ⊆ Gar_int).
    rewrite (rt_end Gar_int); relsf; unionR right.
    hahn_frame_r.
    arewrite (Gdetour  ⊆ Gar_int^?).
    rewrite <- (rt_cr Gar_int).
    hahn_frame_r.
    arewrite (⦗I⦘ ⊆ ⦗C ∪₁ I⦘).
    rewrite (cr_helper sb_W_rel_CI).
    arewrite ((Gsb ⨾ ⦗W ∩₁ Rel⦘)^?  ⊆ Gar_int^?).
    { unfold ar_int, bob, fwbob. basic_solver 21. }
    rewrite <- (rt_cr Gar_int).
    hahn_frame_r.
    arewrite (Cppo^? ⨾ ⦗C ∪₁ I⦘ ⊆ Gppo^? ⨾ ⦗C ∪₁ I⦘).
    { generalize cert_ppo_CI. basic_solver 12. }
    arewrite (Gppo^? ⨾ ⦗C ∪₁ I⦘ ⊆ ⦗D⦘ ⨾ Gppo^?).
    { rewrite C_in_D, I_in_D. generalize dom_ppo_D. basic_solver. }
    arewrite (Gppo ⊆ Gar_int).
    rewrite <- (rt_cr Gar_int). by hahn_frame_r. }
  rewrite !seqA.
  rewrite (dom_rel_helper dom_W_ex_acq_sb_W_D_in_CI).
  rewrite (dom_l (@wf_sbE G)) at 3; rewrite !seqA.

  arewrite (⦗GW_ex_acq⦘ ⨾ ⦗E⦘ ⨾ Gsb ⨾ ⦗W⦘  ⊆ Gar_int^?).
  arewrite_id ⦗D⦘; rels.
  rewrite <- (rt_cr Gar_int).
  hahn_frame_r.
  rewrite (cr_helper W_rel_sb_loc_W_CI).

  arewrite ((⦗W ∩₁ Rel⦘ ⨾ Gsb ∩ Gsame_loc ⨾ ⦗W⦘)^?  ⊆ Gar_int^?) at 1.
  unfold ar_int, bob, fwbob; basic_solver 21.

  rewrite <- (rt_cr Gar_int).
  hahn_frame_r.

  rewrite (cr_helper sb_W_rel_CI).

  arewrite ((Gsb ⨾ ⦗W ∩₁ Rel⦘)^?  ⊆ Gar_int^?).
  unfold ar_int, bob, fwbob; basic_solver 21.
  rewrite <- (rt_cr Gar_int).
  hahn_frame_r.

  arewrite (Cppo^? ⨾ ⦗C ∪₁ I⦘ ⊆ Gppo^? ⨾ ⦗C ∪₁ I⦘).
  generalize cert_ppo_CI; basic_solver 12.

  arewrite (Gppo^? ⨾ ⦗C ∪₁ I⦘ ⊆ ⦗D⦘ ⨾ Gppo^?  ).
  rewrite C_in_D, I_in_D; generalize dom_ppo_D; basic_solver.

  arewrite (Gppo ⊆ Gar_int).
  rewrite <- (rt_cr Gar_int).
  hahn_frame_r.

  done.
Qed.
*)

Lemma cert_acyc_ext : acyc_ext certG sc.
Proof using All.
red; unfold imm_s.ar.
rewrite unionC.
apply acyclic_union1.
- rewrite (ar_int_in_sb WF_cert); apply sb_acyclic.
- red; rewrite sc_rfe_ct_in_sc_rfe; unionL.
  apply WF_SC.
  arewrite (certG.(rfe) ⊆ certG.(rf)).
  apply rf_irr, WF_cert.
- rewrite sc_rfe_ct_in_sc_rfe.
  arewrite ((sc ∪ rfe certG) ⊆ ⦗ C ∪₁ I ⦘ ⨾ (sc ∪ rfe certG)).
  { unionL.
    - rewrite (dom_l (wf_scD WF_SC)) at 1.
      rewrite (dom_l (wf_scE WF_SC)) at 1.
      arewrite (Sc ⊆₁ Acq/Rel) by mode_solver.
      generalize E_F_AcqRel_in_C; basic_solver 12.
      - rewrite cert_rfe; basic_solver 12. }
Print ar_int.
sin_rewrite cert_ar_int_I.

rotate 1.
rewrite <- seqA.
rewrite (seq_union_l).
arewrite_id  ⦗D ∪₁ R ∩₁ Acq⦘ at 1; rels.

arewrite (rfe certG ⨾ ⦗D ∪₁ R ∩₁ Acq⦘ ⊆ Grfe).
{ rewrite cert_rfe; relsf; unionL; [basic_solver 12|].

rewrite wf_new_rfE.
generalize new_rfe_Acq.
unfolder; ins; desf; exfalso; basic_solver 21. }

arewrite (sc ⊆ Gar＊).
arewrite (Grfe ⊆ Gar＊).
arewrite (Gar_int ⊆ Gar).
relsf.
red; relsf.
Qed.


(******************************************************************************)
(** **   *)
(******************************************************************************)

(* TODO: move to another file , CertExcutionInit ?*)
Lemma cert_imm_consistent : imm_consistent certG sc.
Proof using All.
red; splits; eauto using WF_SC_cert, cert_acyc_ext, cert_coh_sc, cert_complete, cert_coherence, cert_rmw_atomicity.
Qed.

End CertExec.
