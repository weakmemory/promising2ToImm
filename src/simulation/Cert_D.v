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

Set Implicit Arguments.
Remove Hints plus_n_O.

Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'NTid_' t" := (fun x => tid x <> t) (at level 1).

Section CertExec_D.

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

(******************************************************************************)
(**  the set D   *)
(******************************************************************************)

Definition D := C ∪₁ I ∪₁ (E ∩₁ NTid_ thread) ∪₁
  dom_rel (Grfi^? ⨾ Gppo ⨾ ⦗ I ⦘) ∪₁ 
  dom_rel ((Gdata ∪ Grfi ∪ Grmw)＊ ⨾ Grppo ⨾ ⦗ S ⦘) ∪₁ 
  codom_rel (⦗I⦘ ⨾ Grfi) ∪₁ codom_rel (Grfe ⨾ ⦗ R ∩₁ Acq ⦘).

Lemma C_in_D : C ⊆₁ D.
Proof using. unfold D; basic_solver 12. Qed.
Lemma I_in_D : I ⊆₁ D.
Proof using. unfold D; basic_solver 12. Qed.
Lemma D_in_E : D ⊆₁ E.
Proof using WF TCCOH. 
  unfold D.
  (* TODO: introduce a lemma? *)
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
  rewrite (wf_ppoE WF), (wf_rfiE WF), (wf_rfeE WF), (coveredE TCCOH).
  rewrite (issuedE TCCOH) at 1.
  basic_solver.
Qed.

Local Lemma S_W_S : ⦗S⦘ ⊆ ⦗W⦘ ⨾ ⦗S⦘.
Proof using S_in_W.
  generalize S_in_W. basic_solver.
Qed.

Lemma D_init : E ∩₁ is_init ⊆₁ D.
Proof using TCCOH.
  cdes TCCOH; generalize ICOV; unfold D; basic_solver 12.
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

Lemma dom_addr_in_D : dom_rel Gaddr ⊆₁ D.
Proof using WF TCCOH E_to_S S_in_W.
  rewrite (dom_r (wf_addrE WF)).
  rewrite E_to_S.
  rewrite id_union; relsf; unionL; splits.
  { rewrite (addr_in_sb WF).
    generalize (dom_sb_covered TCCOH).
    unfold D; basic_solver 21. }
  rewrite dom_rel_eqv_dom_rel.
  rewrite S_W_S.
  sin_rewrite addr_sb_W_in_rppo.
  apply dom_rppo_S_in_D.
Qed.

Lemma dom_ctrl_in_D : dom_rel Gctrl ⊆₁ D.
Proof using WF TCCOH E_to_S S_in_W.
  rewrite (dom_r (wf_ctrlE WF)).
  rewrite E_to_S.
  rewrite id_union; relsf; unionL; splits.
  { rewrite (ctrl_in_sb WF).
    generalize (dom_sb_covered TCCOH).
    unfold D. basic_solver 12. }
  rewrite dom_rel_eqv_dom_rel.
  rewrite S_W_S.
  arewrite (Gctrl ⨾ Gsb^? ⊆ Gctrl).
  { generalize (ctrl_sb WF). basic_solver 21. }
  sin_rewrite ctrl_W_in_rppo.
  apply dom_rppo_S_in_D.
Qed.

Lemma dom_frmw_in_D : dom_rel Grmw_dep ⊆₁ D.
Proof using WF TCCOH E_to_S S_in_W.
  rewrite (dom_r (wf_rmw_depE WF)).
  rewrite E_to_S.
  rewrite id_union; relsf; unionL; splits.
  { rewrite (rmw_dep_in_sb WF).
    generalize (dom_sb_covered TCCOH).
    unfold D. clear.
    basic_solver 12. }
  rewrite dom_rel_eqv_dom_rel.
  rewrite S_W_S.
  rewrite (dom_r (wf_rmw_depD WF)), !seqA.
  arewrite (⦗GR_ex⦘ ⨾ Gsb^? ⨾ ⦗W⦘ ⊆ Gsb ⨾ ⦗W⦘).
  { clear. type_solver. }
  sin_rewrite WF.(rmw_dep_sb_W_in_rppo).
  apply dom_rppo_S_in_D.
Qed.

Lemma dom_rmw_D : dom_rel (Grmw ⨾ ⦗D⦘) ⊆₁ D.
Proof using sc WF TCCOH.
  unfold D.
  rewrite !id_union; relsf; unionL; splits.
  { rewrite (dom_l (wf_rmwD WF)).
    rewrite WF.(rmw_in_sb) at 1.
    generalize (dom_sb_covered TCCOH), (w_covered_issued TCCOH).
    clear; basic_solver 21. }
  { rewrite WF.(rmw_in_ppo) at 1.
    clear. basic_solver 12. }
  { unionR left -> left -> left -> left.
    unionR right.
    rewrite (dom_l WF.(wf_rmwE)) at 1. 
    rewrite WF.(wf_rmwt) at 1.
    clear; unfold same_tid; basic_solver 12. }
  { rewrite dom_rel_eqv_dom_rel.
    rewrite WF.(rmw_in_ppo) at 1.
    rewrite (dom_r (@wf_ppoD G)) at 1.
    rewrite (dom_l (@wf_ppoD G)) at 2.
    unionR left -> left -> left -> right.
    generalize (@ppo_rfi_ppo G).
    clear; type_solver 21. }
  { unionR left -> left -> right.
    rewrite dom_rel_eqv_dom_rel.
    rewrite <- inclusion_t_rt at 2.
    rewrite ct_begin.
    clear; basic_solver 21. }
  { rewrite (dom_r (wf_rmwD WF)).
    rewrite (dom_r (wf_rfiD WF)).
    clear; type_solver. }
  { rewrite (dom_r (wf_rmwD WF)).
    clear; type_solver. }
Qed.

Lemma dom_R_ex_fail_sb_D : 
  dom_rel (⦗GR_ex \₁ dom_rel Grmw⦘ ⨾ Gsb ⨾ ⦗W⦘ ⨾ ⦗D⦘) ⊆₁ D.
Proof.
  unfold D.
  rewrite !id_union; relsf; unionL; splits.
  { generalize (dom_sb_covered TCCOH), (w_covered_issued TCCOH).
    clear.
    basic_solver 21. }
  { rewrite I_in_S at 1. unfold rppo.
    unionR left -> left -> right.
    rewrite rtE.
    basic_solver 21. }
  { unionR left -> left -> left -> left.
    unionR right.
    rewrite (dom_l (@wf_sbE G)) at 1.
    arewrite ((GR_ex \₁ dom_rel Grmw) ⊆₁ set_compl Init).
    by rewrite WF.(init_w), R_ex_in_R; type_solver.
    generalize (@ninit_sb_same_tid G).
    unfold same_tid; unfolder; ins; desf; splits; eauto.
    erewrite H; eauto. }
  { unionR left -> left -> right.
    arewrite (Grfi ⊆ Gsb) at 1.
    rewrite WF.(ppo_in_sb) at 1.
    rewrite I_in_S.
    arewrite (⦗S⦘ ⊆ ⦗S⦘ ;; ⦗W⦘) at 1.
    by generalize S_in_W; basic_solver.
    unfold rppo.
    generalize (@sb_trans G); basic_solver 21. }
  { unionR left -> left -> right.
    arewrite (Grfi ⊆ Gsb) at 1.
    rewrite WF.(data_in_sb) at 1.
    rewrite WF.(rmw_in_sb) at 2.
    rewrite WF.(rppo_in_sb) at 1.
    arewrite (⦗S⦘ ⊆ ⦗S⦘ ;; ⦗W⦘) at 1.
    by generalize S_in_W; basic_solver.
    unfold rppo.
    arewrite ((Gsb ∪ Gsb ∪ Gsb)＊ ⊆ Gsb^?).
    by generalize (@sb_trans G); ins; relsf.
    rewrite rtE.
    generalize (@sb_trans G); basic_solver 32. }
  { rewrite (dom_r (wf_rfiD WF)).
    type_solver. }
  rewrite (dom_r (wf_rmwD WF)).
  type_solver.
Qed.

Lemma dom_detour_D : dom_rel (Gdetour ⨾ ⦗D⦘) ⊆₁ I.
Proof using WF WF_SC TCCOH RPPO_S detour_Acq_E detour_E.
  unfold D.
  rewrite !id_union; relsf; unionL; splits.
  { rewrite (dom_l (wf_detourD WF)).
    rewrite detour_in_sb.
    generalize (dom_sb_covered TCCOH), (w_covered_issued TCCOH).
    clear.
    basic_solver 21. }
  { rewrite (dom_r (wf_detourD WF)).
    rewrite (issuedW TCCOH) at 1.
    clear. type_solver. }
  { apply detour_E. }
  { rewrite dom_rel_eqv_dom_rel.
    rewrite crE; relsf; unionL; splits.
    2: by rewrite (dom_r (wf_detourD WF)), (dom_l (wf_rfiD WF)); clear; type_solver.
    etransitivity.
    2: eapply tc_dr_pb_I; eauto; apply tc_coherent_implies_tc_coherent_alt; eauto.
    clear.
    basic_solver 10. }
  { rewrite dom_rel_eqv_dom_rel.
    etransitivity.
    2: by apply RPPO_S.
    clear.
    basic_solver 10. }
  { rewrite dom_rel_eqv_codom_rel, transp_seq; relsf.
    sin_rewrite (detour_transp_rfi WF); rels. }
  rewrite (dom_r (wf_rfeE WF)).
  relsf.
  transitivity (dom_rel (Gdetour ⨾ ⦗R ∩₁ Acq⦘ ⨾ ⦗E⦘)).
  { clear. basic_solver 21. }
  generalize detour_Acq_E. clear. basic_solver 21.
Qed.

Lemma dom_data_D: dom_rel (Gdata ⨾ ⦗D⦘) ⊆₁ D.
Proof using WF TCCOH.
  unfold D.
  rewrite !id_union; relsf; unionL; splits.
  { rewrite (data_in_sb WF) at 1.
    generalize (dom_sb_covered TCCOH). clear. basic_solver 21. }
  { rewrite (data_in_ppo WF) at 1. clear.
    basic_solver 12. }
  { rewrite (data_in_sb WF) at 1.
    rewrite (dom_l (@wf_sbE G)) at 1.
    rewrite sb_tid_init' at 1; relsf; unionL; split.
    { unionR left -> left -> left -> left.
      unionR right.
      unfold same_tid; unfolder; ins; desf; eauto 20. }
    arewrite (⦗E⦘ ⨾ ⦗fun a : actid => is_init a⦘ ⊆ ⦗D⦘).
    { generalize D_init. clear. basic_solver. }
    arewrite (dom_rel (⦗D⦘ ⨾ Gsb ⨾ ⦗E ∩₁ NTid_ thread⦘) ⊆₁ D) by basic_solver.
    unfold D. clear. basic_solver 12. }
  { rewrite dom_rel_eqv_dom_rel.
    rewrite crE at 1; relsf; unionL; splits.
    { rewrite (dom_r (wf_dataD WF)), (dom_l (@wf_ppoD G)).
      clear. type_solver. }
    rewrite (data_in_ppo WF) at 1.
    sin_rewrite ppo_rfi_ppo. clear. basic_solver 21. }
  { rewrite dom_rel_eqv_dom_rel.
    arewrite (Gdata ⨾ (Gdata ∪ Grfi ∪ Grmw)＊ ⊆ (Gdata ∪ Grfi ∪ Grmw)＊).
    2: by eauto 10 with hahn.
    arewrite (Gdata ⊆ Gdata ∪ Grfi ∪ Grmw).
    rewrite <- ct_begin.
    apply inclusion_t_rt. }
  { rewrite (dom_r (wf_dataD WF)), (dom_r (wf_rfiD WF)). clear. type_solver. }
  rewrite (dom_r (wf_dataD WF)), (dom_r (wf_rfeD WF)). clear. type_solver.
Qed.

Lemma dom_sb_F_AcqRel_in_CI : dom_rel (Gsb ⨾ ⦗F ∩₁ Acq/Rel⦘) ⊆₁ C ∪₁ I.
Proof using TCCOH F_in_C.
  rewrite (dom_r (@wf_sbE G)), !seqA.
  arewrite (⦗E⦘ ⨾ ⦗F ∩₁ Acq/Rel⦘ ⊆ ⦗C⦘).
  revert F_in_C; clear; basic_solver.
  generalize (dom_sb_covered TCCOH). clear. basic_solver 21.
Qed.

Lemma dom_sb_F_AcqRel_in_D : dom_rel (Gsb ⨾ ⦗F ∩₁ Acq/Rel⦘) ⊆₁ D.
Proof using TCCOH F_in_C.
  rewrite dom_sb_F_AcqRel_in_CI, C_in_D, I_in_D. basic_solver.
Qed.

Lemma dom_sb_F_Acq_in_D : dom_rel (Gsb ⨾ ⦗F ∩₁ Acq⦘) ⊆₁ D.
Proof using TCCOH F_in_C.
  arewrite (Acq ⊆₁ Acq/Rel) by (clear; mode_solver).
  apply dom_sb_F_AcqRel_in_D.
Qed.

Lemma dom_sb_F_Rel_in_D : dom_rel (Gsb ⨾ ⦗F ∩₁ Rel⦘) ⊆₁ D.
Proof using TCCOH F_in_C.
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
Proof using WF TCCOH.
  unfold D at 1.
  rewrite !id_union, !seq_union_r, !dom_union.
  unionL.
  { arewrite (Grfi ⊆ Grf). rewrite <- I_in_D.
    eapply dom_rf_covered; eauto. }
  { rewrite (dom_r (wf_rfiD WF)), (issuedW TCCOH) at 1. clear. type_solver. }
  { arewrite (Grfi ⊆ Gsb).
    rewrite (dom_l (@wf_sbE G)).
    rewrite sb_tid_init'; relsf; unionL; splits.
    { unfold D.
      unionR left -> left -> left -> left.
      unionR right.
      unfold same_tid. clear. basic_solver. }
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
  ie_unfolder; unfolder; ins; desc.
  assert (x=x0); subst.
  eapply WF; clear; basic_solver.
  exfalso; auto.
Qed.

Lemma dom_rf_D : dom_rel (Grf ⨾ ⦗D⦘) ⊆₁ D.
Proof using WF TCCOH Grfe_E.
  rewrite rfi_union_rfe at 1.
  relsf; unionL; splits.
  { apply dom_rfi_D. }
  revert Grfe_E. generalize I_in_D. clear. basic_solver.
Qed.

Lemma complete_D : D ∩₁ R  ⊆₁ codom_rel Grf.
Proof using WF TCCOH COMP_C COMP_NTID COMP_PPO COMP_RPPO.
  unfold D.
  rewrite !set_inter_union_l.
  unionL.
  { apply COMP_C. }
  { rewrite (issuedW TCCOH). clear. type_solver. }
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
        ∪ Grmw_dep ⨾ Gsb^? ∪ ⦗GR_ex \₁ dom_rel Grmw⦘ ⨾ Gsb)＊ ⊆ Gsb).
{ arewrite_id ⦗GR_ex \₁ dom_rel Grmw⦘.
  rewrite WF.(data_in_sb), WF.(addr_in_sb), WF.(ctrl_in_sb).
  rewrite WF.(rmw_dep_in_sb), WF.(rmw_in_sb).
  arewrite (Grfi ⊆ Gsb).
  generalize (@sb_trans G); ins; relsf. }
relsf; unionL.
{ arewrite_id ⦗W⦘.
rels.
rewrite (dom_rel_helper dom_ppo_D_helper).
basic_solver. }

rewrite !seqA.
rewrite (dom_rel_helper dom_R_ex_fail_sb_D).
rewrite rtE; relsf.
seq_rewrite (dom_rel_helper dom_ppo_D_helper).
basic_solver 12.
Qed.

Lemma dom_ppo_CI : dom_rel (Gppo ⨾ ⦗C ∪₁ I⦘) ⊆₁ D.
Proof using All.
  rewrite C_in_D, I_in_D; relsf.
  apply dom_ppo_D.
Qed.

End CertExec_D.