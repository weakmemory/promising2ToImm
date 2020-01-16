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
Hypothesis RPPO_RMW_S : dom_rel ((Gdetour ∪ Grfe) ⨾ (Gdata ∪ Grfi ∪ Grmw)＊ ⨾ (Grppo ∪ Grmw) ⨾ ⦗S⦘) ⊆₁ I.
Hypothesis ST_in_E : S ∩₁ Tid_ thread ⊆₁ E.
Hypothesis I_in_S : I ⊆₁ S.
Hypothesis W_ex_acq_in_I :GW_ex_acq ⊆₁ I.

Hypothesis F_in_C : E ∩₁ F ∩₁ Acq/Rel ⊆₁ C.

Hypothesis S_I_in_W_ex : (S ∩₁ Tid_ thread) \₁ I ⊆₁ W_ex G.

Hypothesis ETC_DR_R_ACQ_I : dom_rel ((Gdetour ∪ Grfe) ⨾ (Grmw ⨾ Grfi)^* ⨾ ⦗R∩₁Acq⦘ ⨾ Gsb ⨾ ⦗S⦘) ⊆₁ I.

Hypothesis COMP_R_ACQ_SB : dom_rel ((Grmw ⨾ Grfi)＊ ⨾ ⦗E ∩₁ R ∩₁ Acq⦘) ⊆₁ codom_rel Grf.

Hypothesis ETC_DETOUR_RMW_S : dom_rel (Gdetour ⨾ Grmw ⨾ ⦗ S ⦘) ⊆₁ I.

Variable lab' : actid -> label.
Hypothesis SAME : same_lab_u2v lab' Glab.

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



Lemma cert_ppo_D : Cppo ⨾ ⦗ D ⦘ ⊆ Gppo.
Proof using All.
rewrite ppo_helper; auto.
rewrite (cert_R _ SAME).
rewrite (cert_W _ SAME).
rewrite cert_sb.
rewrite (cert_R_ex _ SAME).
rewrite !seqA.


rewrite rtE.
rewrite !seq_union_l, !seq_union_r.
unionL.
{ relsf.
  unfold ppo.
  rewrite <- ct_step.
  rewrite crE.
  type_solver 21. }

unfold ppo; ins.


arewrite ((⦗GR_ex \₁ dom_rel Grmw⦘ ⨾ Gsb)^? ⨾ ⦗W⦘ ⨾ ⦗D⦘ ⊆ ⦗D⦘ ;; (⦗GR_ex \₁ dom_rel Grmw⦘ ⨾ Gsb)^? ⨾ ⦗W⦘).
{ rewrite crE, !seq_union_l, !seqA.
  forward (eapply dom_R_ex_fail_sb_D with (G:=G)); try edone.
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
rewrite cert_rfi_eq.
rewrite cert_rfi_D; auto.
basic_solver 12.

- intros k H.
rewrite !seqA.
rewrite cert_rfi_eq.
rewrite cert_rfi_D; auto.

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
Proof using All.
  enough (Cdetour ⨾ ⦗ D ⦘ ⊆ Gdetour).
  { arewrite (⦗D⦘ ⊆ ⦗D⦘ ⨾ ⦗D⦘) by basic_solver.
    sin_rewrite H.
    forward (eapply dom_detour_D with (T:=T) (G:=G)); try edone.
    clear. basic_solver. }
  unfold detour, Execution.coe.
  rewrite cert_sb.
  rewrite <- seq_eqv_inter_lr, !seqA.
  rewrite cert_rfe_eq.
  rewrite cert_rfe_D; auto.
  rewrite I_in_cert_co_base with (G:=G).
  seq_rewrite <- seq_eqv_minus_lr.
  ins; rewrite cert_co_I; try edone.
  clear. basic_solver 21.
Qed.


Lemma cert_detour_R_Acq : Cdetour ⨾ ⦗R∩₁Acq⦘ ⊆ ⦗ I ⦘ ⨾ Gdetour ⨾ ⦗R∩₁Acq⦘.
Proof using All.
  cut (Cdetour ⨾ ⦗R∩₁Acq⦘ ⊆ Gdetour ⨾ ⦗R∩₁Acq⦘).
  { intros HH. rewrite HH. apply dom_rel_helper.
    rewrite <- detour_Acq_E. rewrite (dom_r WF.(wf_detourE)) at 1.
    clear. basic_solver 10. }
  unfold detour.
  rewrite cert_sb.
  arewrite ((Ccoe ⨾ Crfe) ∩ Gsb ⨾ ⦗R ∩₁ Acq⦘ ⊆
            (Ccoe ⨾ Crfe ⨾ ⦗Acq⦘) ∩ Gsb ⨾ ⦗R ∩₁ Acq⦘).
  { clear. basic_solver 10. }
  rewrite cert_rfe_eq. rewrite cert_rfe_to_Acq_in_Grfe; auto.
  rewrite (dom_rel_helper Grfe_E) at 1.
  arewrite (Ccoe ⨾ ⦗I⦘ ⊆ Gcoe).
  2: done.
  erewrite I_in_cert_co_base with (G:=G).
  forward (eapply cert_co_I with (G:=G)); eauto.
  unfold coe. rewrite cert_sb. unfold CertExecution2.certG.
  clear. simpls.
  unfolder. intros HH; ins; desf. splits; auto. apply HH. by split.
Qed.

Lemma cert_ar_int_CI : Car_int ⨾ ⦗dom_rel (Gar_int＊ ⨾ ⦗C ∪₁ I⦘)⦘ ⊆ Gar_int⁺.
Proof using All.
  unfold ar_int at 1.
  rewrite cert_bob; auto.
  rewrite cert_W_ex_acq; auto.
  rewrite cert_sb; auto.
  rewrite cert_W; eauto.
  rewrite cert_W_ex; auto.
  rewrite cert_R; eauto.
  rewrite cert_Acq; eauto.
  arewrite (Crfi ⨾ ⦗R ∩₁ Acq⦘ ⊆ Crfi ⨾ ⦗Acq⦘ ⨾ ⦗R ∩₁ Acq⦘).
  { clear. basic_solver. }
  arewrite (Crfi ⨾ ⦗Acq⦘ ⊆ Grfi).
  { rewrite cert_rfi_eq.
    eapply cert_rfi_to_Acq_in_Grfi; eauto. }
  rewrite bob_in_ar_int, w_ex_acq_sb_w_in_ar_int.
  arewrite (⦗GW_ex⦘ ⨾ Grfi ⨾ ⦗R ∩₁ Acq⦘ ⊆ Gar_int).
  arewrite (Gar_int ∪ Cppo ∪ Cdetour ∪ Gar_int ∪ Gar_int ⊆ Cppo ∪ Cdetour ∪ Gar_int⁺).
  { clear. rewrite <- ct_step. basic_solver. }
  rewrite seq_union_l. unionL.
  2: { clear. basic_solver. }
  rewrite seq_union_l. unionL.
  2: { rewrite <- ct_step. rewrite <- detour_in_ar_int at 2.
       rewrite dom_ar_int_rt_CI_D; eauto.
       rewrite id_union. rewrite seq_union_r. unionL.
       { sin_rewrite cert_detour_D. clear. basic_solver. }
       rewrite cert_detour_R_Acq. clear. basic_solver. }
  rewrite dom_ar_int_rt_CI_D; eauto.
  rewrite id_union. rewrite seq_union_r. unionL.
  { rewrite cert_ppo_D. rewrite ppo_in_ar_int. apply ct_step. }
  rewrite wf_ppoD. rewrite cert_W; eauto.
  clear. type_solver.
Qed.

Lemma cert_ar_int_ct_CI : Car_int⁺ ⨾ ⦗ C ∪₁ I ⦘ ⊆ Gar_int⁺.
Proof using All.
  arewrite (C ∪₁ I ⊆₁ dom_rel (Gar_int^* ;; ⦗ C ∪₁ I ⦘)).
  { rewrite rtE. clear. basic_solver 10. }
  apply ct_ind_left with (P:= fun r => r ⨾ ⦗dom_rel (Gar_int^* ;; ⦗ C ∪₁ I ⦘)⦘); auto.
  { by auto with hahn. }
  { apply cert_ar_int_CI. }
  intros k H; rewrite !seqA.
  arewrite (k ⨾ ⦗dom_rel (Gar_int＊ ⨾ ⦗C ∪₁ I⦘)⦘ ⊆ ⦗dom_rel (Gar_int＊ ⨾ ⦗C ∪₁ I⦘)⦘ ⨾ Gar_int⁺).
  2: by sin_rewrite cert_ar_int_CI; apply ct_ct.
  clear -H.
  intros x y AA. apply seq_eqv_l. split; auto.
  apply seq_eqv_r in AA. destruct AA as [BB [z AA]].
  apply seq_eqv_r in AA. destruct AA as [AA CC].
  exists z. apply seq_eqv_r. split; auto.
  apply inclusion_t_rt. eapply ct_rt. eexists. splits; eauto.
  apply H. apply seq_eqv_r. split; auto. basic_solver 10.
Qed.

Lemma cert_ar_int_I : Car_int⁺ ⨾ ⦗ C ∪₁ I ⦘ ⊆ ⦗ D ∪₁ R ∩₁ Acq ⦘ ⨾ Gar_int⁺.
Proof.
  arewrite (⦗ C ∪₁ I ⦘ ⊆ ⦗ C ∪₁ I ⦘ ⨾ ⦗ C ∪₁ I ⦘).
  { clear. basic_solver. }
  rewrite <- !seqA.
  rewrite cert_ar_int_ct_CI.
  forward (eapply dom_ar_int_rt_CI_D with (G:=G)); eauto.
  rewrite rtE. clear. basic_solver 20.
Qed.

Lemma cert_acyc_ext : acyc_ext certG sc.
Proof using All.
  red; unfold imm_s.ar.
  rewrite unionC.
  apply acyclic_union1.
  { rewrite (ar_int_in_sb WF_cert); apply sb_acyclic. }
  { red; rewrite sc_rfe_ct_in_sc_rfe; unionL; auto.
    { apply WF_SC. }
    arewrite (certG.(rfe) ⊆ certG.(rf)).
    apply rf_irr, WF_cert. }
  rewrite sc_rfe_ct_in_sc_rfe; auto.
  arewrite ((sc ∪ rfe certG) ⊆ ⦗ C ∪₁ I ⦘ ⨾ (sc ∪ rfe certG)).
  { unionL.
    2: { rewrite cert_rfe_eq. rewrite cert_rfe_alt; auto. basic_solver 12. }
    rewrite (dom_l (wf_scD WF_SC)) at 1.
    rewrite (dom_l (wf_scE WF_SC)) at 1.
    arewrite (Sc ⊆₁ Acq/Rel) by mode_solver.
    generalize E_F_AcqRel_in_C; basic_solver 12. }

  sin_rewrite cert_ar_int_I.
  rotate 1.
  rewrite <- seqA.
  rewrite (seq_union_l).
  arewrite_id  ⦗D ∪₁ R ∩₁ Acq⦘ at 1; rels.
  arewrite (rfe certG ⨾ ⦗D ∪₁ R ∩₁ Acq⦘ ⊆ Grfe).
  { arewrite (R ∩₁ Acq ⊆₁ Acq) by basic_solver.
    rewrite id_union, seq_union_r. 
    rewrite cert_rfe_eq.
    rewrite cert_rfe_to_Acq_in_Grfe; auto.
    unionL; [|done].
    rewrite cert_rfe_D; auto.
    basic_solver 21. }

  arewrite (sc ⊆ Gar＊).
  arewrite (Grfe ⊆ Gar＊).
  arewrite (Gar_int ⊆ Gar).
  relsf.
  red; relsf.
Qed.

End CertExec_ar.
