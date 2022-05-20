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
From imm Require Import AuxDef. 
From imm Require Import TraversalOrder.
From imm Require Import TLSCoherency.
From imm Require Import IordCoherency.
From imm Require Import SimClosure. 
Require Import TlsAux.
Require Import Next. 
Require Import ExtTraversalConfig ExtTraversalProperties.
From imm Require Import FinExecution. 
Require Import ExtTraversalConfig.

Require Import Cert_co.
Require Import Cert_D.
Require Import Cert_rf.
Require Import CertExecution2.

Set Implicit Arguments.

Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'NTid_' t" := (fun x => tid x <> t) (at level 1).

Section CertExec_hb.

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

Hypothesis RMWREX : dom_rel Grmw ⊆₁ GR_ex.

Variable lab' : actid -> label.
Hypothesis SAME : same_lab_u2v lab' Glab.

Notation "'certG'" := (certG G sc T thread lab').


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


(******************************************************************************)
(** **   *)
(******************************************************************************)

Lemma dom_rf_D_helper: Grf ⨾ ⦗D⦘ ≡ ⦗D⦘ ⨾ Grf ⨾ ⦗D⦘.
Proof.
forward (eapply dom_rf_D with (T:=T) (thread:=thread)); try edone.
basic_solver 12.
Qed.

Lemma Grelease_D_in_Crelease : Grelease ⨾ ⦗ D ⦘ ⊆ Crelease.
Proof using All.
  unfold release, rs; ins.
  rewrite (cert_F _ SAME).
  rewrite (cert_Rel _ SAME).
  rewrite (cert_W _ SAME).
  rewrite (cert_same_loc _ SAME).
  rewrite (cert_sb).
  hahn_frame.
  transitivity ((Grf ⨾ ⦗D⦘ ⨾ Grmw)＊).
  2: unfold Cert_rf.cert_rf; apply clos_refl_trans_mori; basic_solver 12.
  eapply rt_ind_right with (P:=fun r=> r ⨾ ⦗D⦘); eauto with hahn.
  basic_solver 12.
  intros k H.
  rewrite !seqA.
  arewrite (Grmw ⨾ ⦗D⦘ ⊆ ⦗D⦘ ⨾ Grmw) at 1.
  { forward (eapply dom_rmw_D with (T:=T)); try edone; basic_solver. }
  remember ((Grf ⨾ ⦗D⦘ ⨾ Grmw)＊) as X.
  seq_rewrite dom_rf_D_helper.
  subst X.
  rewrite !seqA.
  sin_rewrite H.
  rewrite rtE at 2.
  rewrite ct_end.
  basic_solver 21.
Qed.

Lemma Crelease_D_in_Grelease : Crelease ⨾ ⦗ D ⦘ ⊆ Grelease.
Proof using All.
  unfold release, rs; ins.
  rewrite (cert_F _ SAME).
  rewrite (cert_Rel _ SAME).
  rewrite (cert_W _ SAME).
  rewrite (cert_same_loc _ SAME).
  rewrite (cert_sb).
  hahn_frame.
  transitivity ((Grf ⨾ ⦗D⦘ ⨾ Grmw)＊).
  2: apply clos_refl_trans_mori; basic_solver 12.
  eapply rt_ind_right with (P:=fun r=> r ⨾ ⦗D⦘); eauto with hahn.
  basic_solver 12.
  intros k H.
  rewrite !seqA.
  arewrite (Grmw ⨾ ⦗D⦘ ⊆ ⦗D⦘ ⨾ Grmw) at 1.
  { forward (eapply dom_rmw_D with (T:=T)); try edone; basic_solver. }
  arewrite (cert_rf ⨾ ⦗D⦘ ⊆ Grf ⨾ ⦗D⦘) by (by apply cert_rf_D).
  remember ((Grf ⨾ ⦗D⦘ ⨾ Grmw)＊) as X.
  seq_rewrite dom_rf_D_helper.
  subst X.
  rewrite !seqA.
  sin_rewrite H.
  rewrite rtE at 2.
  rewrite ct_end.
  basic_solver 21.
Qed.

Lemma Crelease_D_eq_Grelease_D : Crelease ⨾ ⦗ D ⦘ ≡ Grelease ⨾ ⦗ D ⦘.
Proof using All.
  generalize Crelease_D_in_Grelease, Grelease_D_in_Crelease.
  clear. basic_solver.
Qed.

(*Lemma rt_rf_rmw : (rf ⨾ rmw)＊ ⊆ (rfi ⨾ rmw)＊ ⨾ (rfe ⨾ rmw ⨾ (rfi ⨾ rmw)＊)＊.
Proof.
eapply rt_ind_left with (P:=fun r=> r); eauto with hahn.
basic_solver 12.
intros k H.
rewrite !seqA, H.
rewrite rfi_union_rfe; relsf; unionL.
- rewrite rt_begin at 3.
  basic_solver 21.
- rewrite (rt_begin (rfe ⨾ rmw ⨾ (rfi ⨾ rmw)＊)) at 2.
  basic_solver 21.
Qed.
*)
Lemma cert_sb_sw_helper : Gsb ∪ Gsw ⊆ Gsb ∪ Csw.
Proof using All.
  unionL; [basic_solver|].
  unfold imm_s_hb.sw; ins.
  remember (Grf ⨾ ⦗D⦘ ∪ new_rf) as X.
  rewrite (cert_F _ SAME).
  rewrite (cert_Acq _ SAME).
  rewrite (cert_sb).
  rewrite !crE, !seq_union_l, !seq_union_r, !seq_id_l, !seqA.
  unionL.
  { arewrite (⦗Acq⦘ ⊆ (⦗D⦘ ∪ ⦗set_compl D⦘) ⨾ ⦗Acq⦘) at 1.
    { unfolder. ins. desf. destruct (classic (D y)); eauto. }
    rewrite !seq_union_l, !seq_union_r.
    unionL.
    { seq_rewrite dom_rf_D_helper.
      rewrite !seqA.
      sin_rewrite Grelease_D_in_Crelease.
      unfold Cert_rf.cert_rf.
      subst X; basic_solver 21. }
    rewrite rfi_union_rfe at 1.
    rewrite !seq_union_l, !seq_union_r.
    unionL; cycle 1.
    { transitivity (fun _ _ : actid => False); [|basic_solver].
      rewrite (dom_r (wf_rfeD WF)).
      unfold Cert_D.D; basic_solver 21. }
    rewrite (dom_r (wf_rfiE WF)) at 1.
    rewrite E_to_S.
    rewrite C_in_D with (G:=G) (T:=T) (thread:=thread). 
    rewrite id_union, !seq_union_r, !seq_union_l, !seq_union_r, !seqA.
    unionL; [basic_solver|].
    unfold release at 1, rs at 1.
    rewrite rt_rf_rmw.
    rewrite rtE with (r:= Grfe ⨾ Grmw ⨾ (Grfi ⨾ Grmw)＊).
    rewrite !seq_union_r, !seq_union_l; unionL.
    { arewrite (Grfi ⊆ Gsb).
      rewrite (rmw_in_sb WF).
      generalize (@sb_trans G); ins; relsf.
      revert H; basic_solver 21. }
    rewrite ct_end, <- !seqA.
    arewrite (((((((⦗Rel⦘ ⨾ (⦗F⦘ ⨾ Gsb)^?) ⨾ ⦗W⦘) ⨾ (Gsb ∩ Gsame_loc)^?) ⨾ ⦗W⦘) ⨾ 
      (Grfi ⨾ Grmw)＊) ⨾ ((Grfe ⨾ Grmw) ⨾ (Grfi ⨾ Grmw)＊)＊) ⊆ Grelease).
    { arewrite (Grfi ⊆ Grf).
      arewrite (Grfe ⊆ Grf).
      rewrite <- !seqA.
      rewrite <- !ct_begin.
      rewrite !seqA; relsf. }
    assert (BB: Grmw ⨾ (Grfi ⨾ Grmw)＊ ⨾ Grfi ⊆ (Grmw ⨾ Grfi)⁺).
    { seq_rewrite <- rt_seq_swap.
      rewrite !seqA.
      remember (Grmw ⨾ Grfi) as Y.
      apply ct_end. }
    sin_rewrite BB.
    assert (AA: dom_rel (Grfe ⨾ (Grmw ⨾ Grfi)⁺ ⨾ ⦗dom_rel (Gsb^? ⨾ ⦗S⦘)⦘ ⨾ ⦗Acq⦘) ⊆₁ I).
    { rewrite (dom_r (wf_rfiD WF)) at 1.
      rewrite seq_eqvC.
      rewrite <- !seqA.
      rewrite dom_rel_eqv_dom_rel, seqA. rewrite inclusion_ct_seq_eqv_r, !seqA.
      arewrite (⦗R⦘ ⨾ ⦗Acq⦘ ⨾ Gsb^? ⨾ ⦗S⦘ ⊆ ⦗R ∩₁ Acq⦘ ⨾ Gsb ⨾ ⦗S⦘).
      { rewrite crE; relsf. rewrite S_in_W at 1. type_solver 32. }
      arewrite (Grfe ⊆ Gdetour ∪ Grfe). 
      by rewrite inclusion_t_rt. }
    rewrite seq_eqvC.
    seq_rewrite (dom_rel_helper AA).
    rewrite !seqA.
    arewrite ((Grmw ⨾ Grfi)⁺ ⨾ ⦗dom_rel (Gsb^? ⨾ ⦗S⦘)⦘ ⨾ ⦗Acq⦘ ⊆ 
              ⦗dom_rel ((Grmw ⨾ Grfi)＊ ⨾ ⦗R ∩₁ Acq⦘ ⨾ Gsb ⨾ ⦗S⦘)⦘ ⨾ 
              (Grmw ⨾ Grfi)⁺ ⨾ ⦗dom_rel (Gsb^? ⨾ ⦗S⦘)⦘ ⨾ ⦗Acq⦘).
    { apply dom_rel_helper.
    rewrite seq_eqvC, <- seqA.
    
    rewrite dom_rel_eqv_dom_rel.
    rewrite (dom_r (wf_rfiD WF)) at 1. 
    rewrite <- !seqA.
    rewrite inclusion_ct_seq_eqv_r, !seqA.
    arewrite (⦗S⦘ ⊆ ⦗S⦘ ⨾ ⦗W⦘) at 1.
    { generalize S_in_W; clear; basic_solver. }
    arewrite (⦗R⦘ ⨾ ⦗Acq⦘ ⨾ Gsb^? ⨾ ⦗S⦘ ⨾ ⦗W⦘ ⊆ ⦗R ∩₁ Acq⦘ ⨾ Gsb ⨾ ⦗S⦘).
    {  type_solver 21. }
    rewrite rtE. basic_solver 21. }
    arewrite (Grfe ⊆ Grf).
    arewrite (Grf ⨾ ⦗dom_rel ((Grmw ⨾ Grfi)＊ ⨾ ⦗R ∩₁ Acq⦘ ⨾ Gsb ⨾ ⦗S⦘)⦘ ⊆ Crf).
    { apply Grf_to_Acq_S_in_cert_rf; eauto. }

    rewrite Grfi_in_cert_rfi at 1; try edone.
    arewrite_id ⦗dom_rel (Gsb^? ⨾ ⦗S⦘)⦘.
    arewrite_id ⦗set_compl D⦘.
    arewrite (Crfi ⊆ Crf).
    seq_rewrite <- ct_seq_swap.
    rewrite !seqA.
    arewrite (Grelease ⨾ ⦗I⦘ ⊆ release certG).
    { rewrite I_in_D; apply Grelease_D_in_Crelease. }
  rels.
  rewrite inclusion_t_rt.
  rewrite <- cert_rmw.
  sin_rewrite release_rf_rmw_steps.
  subst X; ins; basic_solver 12. }
  
arewrite (⦗F⦘ ⨾ ⦗Acq⦘ ⊆ ⦗F ∩₁ Acq/Rel⦘ ⨾ ⦗Acq⦘) at 1.
by mode_solver 21.

arewrite (Gsb ⨾ ⦗F ∩₁ Acq/Rel⦘ ⊆ ⦗D⦘ ⨾ Gsb ⨾ ⦗F ∩₁ Acq/Rel⦘).
{ forward (eapply dom_sb_F_AcqRel_in_D with (T:=T) (thread:=thread)); try edone.
  basic_solver 12. }

  seq_rewrite dom_rf_D_helper.
  rewrite !seqA.

arewrite ( Grf ⨾ ⦗D⦘ ⊆ cert_rf).

sin_rewrite Grelease_D_in_Crelease.
unionR right -> right.
basic_solver 21.
Qed.

Lemma cert_sb_sw : Gsb ∪ Csw ≡ Gsb ∪ Gsw.
Proof using All.
  split; [|by apply cert_sb_sw_helper].
  unionL; [by eauto with hahn|].
  unfold imm_s_hb.sw; ins.
  rewrite (cert_F _ SAME).
  rewrite (cert_Acq _ SAME).
  rewrite (cert_sb).
  rewrite !crE, !seq_union_l, !seq_union_r, !seq_id_l.
  unionL.
  2: { rewrite !seqA.
       arewrite (Gsb ⨾ ⦗F⦘ ⨾ ⦗Acq⦘ ≡ ⦗D⦘ ⨾ Gsb ⨾ ⦗F⦘ ⨾ ⦗Acq⦘).
       { rewrite (dom_r (@wf_sbE G)). generalize dom_sb_F_Acq_in_D. basic_solver 12. }
       arewrite (cert_rf ⨾ ⦗D⦘ ⊆ Grf ⨾ ⦗D⦘) by (by apply cert_rf_D).
       seq_rewrite dom_rf_D_helper.
       rewrite !seqA.
       seq_rewrite Crelease_D_eq_Grelease_D.
       rewrite !seqA. eauto with hahn. }
  arewrite (cert_rf ⊆ cert_rf ⨾ ⦗D⦘ ∪ cert_rf ⨾ ⦗set_compl D⦘).
  { clear. unfolder. ins. desf. tauto. }
  rewrite !seq_union_l, !seq_union_r.
  unionL.
  { arewrite (cert_rf ⨾ ⦗D⦘ ⊆ Grf ⨾ ⦗D⦘) by (by apply cert_rf_D).
    seq_rewrite dom_rf_D_helper.
    rewrite !seqA.
    seq_rewrite Crelease_D_eq_Grelease_D.
    basic_solver 20. }
  rewrite cert_rfD; try edone.
  rewrite cert_rfE; try edone.
  rewrite !seqA.
  rewrite <- !id_inter. rewrite <- set_interA.
  arewrite (E ∩₁ R ∩₁ (set_compl D ∩₁ Acq) ⊆₁
            codom_rel Grf ∩₁ set_compl D ∩₁ (E ∩₁ R ∩₁ Acq)).
  { generalize COMP_ACQ. clear. basic_solver 10. }
  rewrite rfi_union_rfe at 1. rewrite codom_union.
  rewrite set_inter_union_l. rewrite set_inter_union_l, id_union, !seq_union_r.
  unionL.
  2: { arewrite (codom_rel Grfe ∩₁ set_compl D ∩₁ (E ∩₁ R ∩₁ Acq) ⊆₁ ∅).
       { unfold Cert_D.D. basic_solver 20. }
       basic_solver. }
  rewrite !id_inter. rewrite !seqA.
  arewrite (cert_rf ⨾ ⦗codom_rel Grfi⦘ ⨾ ⦗set_compl D⦘ ⊆ Grfi ⨾ ⦗set_compl D⦘).
  { rewrite <- id_inter.
    intros x y HH.
    apply seq_eqv_r in HH. destruct HH as [HH [[x' AA] BB]].
    assert (x' = x); subst; auto.
    { eapply cert_rff; eauto.
      apply Grfi_in_cert_rfi; auto. }
    basic_solver. }
  unfold release at 1, rs at 1.
  rewrite rt_rf_rmw.
  rewrite rtE with (r:= rfe certG ⨾ Crmw ⨾ (rfi certG ⨾ Crmw)＊).
  rewrite !seq_union_r, !seq_union_l; unionL.
  { unionR left.
    arewrite (Crfi ⊆ Gsb). arewrite (Grfi ⊆ Gsb).
    rewrite (rmw_in_sb WF).
    generalize (@sb_trans G); ins; relsf.
    revert H; basic_solver 21. }
  unionR right -> left.
  rewrite ct_end, <- !seqA.
  arewrite (((((((⦗CRel⦘ ⨾ (⦗CF⦘ ⨾ Csb)^?) ⨾ ⦗CW⦘) ⨾ (Csb ∩ Csame_loc)^?) ⨾ ⦗CW⦘) ⨾ 
               (Crfi ⨾ Crmw)＊) ⨾ ((Crfe ⨾ Crmw) ⨾ (Crfi ⨾ Crmw)＊)＊) ⊆ Crelease).
  { arewrite (Crfi ⊆ Crf).
    arewrite (Crfe ⊆ Crf).
    rewrite <- !seqA.
    rewrite <- !ct_begin.
    rewrite !seqA; relsf. }
  arewrite (⦗set_compl D⦘ ⨾ ⦗E⦘ ⨾ ⦗R⦘ ⨾ ⦗Acq⦘ ⊆ ⦗Acq \₁ C⦘ ⨾ ⦗E ∩₁ R ∩₁ Acq \₁ C⦘).
  { rewrite <- C_in_D. clear. basic_solver. }
  rewrite cert_rmw.
  arewrite_id (⦗W⦘ ⨾ ⦗E⦘). by basic_solver. 
  rels.
  arewrite ((Crfi ⨾ Grmw)＊ ⨾ Grfi ⨾ ⦗Acq \₁ C⦘  ⊆ (Grfi ⨾ Grmw)＊ ⨾ Grfi).
  { rewrite cert_rfi_eq.
    eapply cert_rfi_Grmw_rt_in_Grfi_Grmw; edone. }

  arewrite (Crfe ⊆ ⦗ I ⦘ ⨾ Crfe).
  { rewrite cert_rfe_eq.
    eapply dom_rel_helper with (r:=cert_rfe).
    eapply dom_cert_rfe_in_I; edone. }

  rewrite I_in_D.
  seq_rewrite Crelease_D_eq_Grelease_D.
  rewrite !seqA.
  arewrite (Crfe ⊆ Crf).
  arewrite (Grmw ⨾ (Grfi ⨾ Grmw)＊ ⨾ Grfi ⊆ (Grmw ⨾ Grfi)＊).
  { rewrite rt_seq_swap. rewrite <- seqA, <- ct_begin. apply inclusion_t_rt. }
  rewrite r_to_dom_rel_r_r with (r:=(Grmw ⨾ Grfi)＊ ⨾ ⦗E ∩₁ R ∩₁ Acq \₁ C⦘).

  arewrite (Crf ⨾ ⦗ dom_rel ((Grmw ⨾ Grfi)＊ ⨾ ⦗E∩₁R∩₁Acq \₁ C⦘) ⦘ ⊆ Grf).
  { rewrite cert_rf_eq.
    eapply cert_rf_to_Acq_nC_in_Grf; edone. }

  arewrite_id ⦗D⦘. rewrite seq_id_l.
  arewrite (Grfi ⊆ Grf).
  seq_rewrite <- rt_seq_swap. rewrite !seqA.
  sin_rewrite release_rf_rmw_steps.
  clear. basic_solver.
Qed.

Lemma cert_hb : Chb ≡ Ghb.
Proof using All. by unfold imm_s_hb.hb; rewrite cert_sb_sw. Qed.


End CertExec_hb.
