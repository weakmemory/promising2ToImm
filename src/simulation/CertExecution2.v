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

Set Implicit Arguments.
Remove Hints plus_n_O.

Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'NTid_' t" := (fun x => tid x <> t) (at level 1).

(* TODO: move to more appropriate place. *)
Lemma tid_set_dec thread : Tid_ thread ∪₁ NTid_ thread ≡₁ (fun x => True).
Proof using. unfolder; split; ins; desf; tauto. Qed.

Section CertExec.

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
Hypothesis F_SB_S : dom_rel (⦗F∩₁Acq/Rel⦘ ⨾ sb G ⨾ ⦗S⦘) ⊆₁ C.
Hypothesis ST_in_E : S ∩₁ Tid_ thread ⊆₁ E.
Hypothesis I_in_S : I ⊆₁ S.
Hypothesis W_ex_acq_sb_S : dom_rel (⦗GW_ex_acq⦘ ⨾ Gsb ⨾ ⦗S⦘) ⊆₁ I.

Hypothesis F_sb_S_in_C : dom_rel (⦗F ∩₁ Acq/Rel⦘ ⨾ Gsb ⨾ ⦗S⦘) ⊆₁ C.

(* Lemma W_ex_E : GW_ex ⊆₁ S. *)
(* Proof using W_ex_IST I_in_S. *)
(*   rewrite W_ex_IST. rewrite I_in_S. clear. basic_solver. *)
(* Qed. *)

(******************************************************************************)
(**  the set D   *)
(******************************************************************************)

Definition D := C ∪₁ I ∪₁ (E ∩₁ NTid_ thread) ∪₁
  dom_rel (Grfi^? ⨾ Gppo ⨾ ⦗ I ⦘) ∪₁ 
  dom_rel ((Gdata ∪ Grfi ∪ Grmw)＊ ⨾ Grppo ⨾ ⦗ S ⦘) ∪₁ 
  codom_rel (⦗I⦘ ⨾ Grfi) ∪₁ codom_rel (Grfe ⨾ ⦗ R ∩₁ Acq ⦘).

(*   (E ∩₁ R ∩₁ Acq ∩₁ codom_rel (⦗I⦘ ⨾ Grfi)). *)

(* Definition determined :=
  dom_rel (rmw ⨾ ⦗ NTid_ thread ∩₁ issued T ⦘) \ codom_rel (⦗ set_compl W_ex⦘⨾ rfi).
 *)

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
Proof using WF TCCOH E_to_S S_in_W.
  unfold D.
Admitted.

(*
Lemma Rex_in_D : GR_ex ∩₁ E ⊆₁ D.
Proof using S_in_W E_to_S.
  rewrite E_to_S.
  rewrite S_W_S.
  rewrite set_inter_union_r.
  unionL.
  { rewrite C_in_D. clear. basic_solver. }
  rewrite <- dom_eqv1.
  arewrite (⦗GR_ex⦘ ⨾ Gsb^? ⨾ ⦗W⦘ ⊆ ⦗GR_ex⦘ ⨾ Gsb ⨾ ⦗W⦘).
  { clear. type_solver. }
  sin_rewrite R_ex_sb_W_in_rppo.
  apply dom_rppo_S_in_D.
Qed.
*)

Lemma dom_R_ex_fail_sb_D : 
  dom_rel (⦗GR_ex \₁ dom_rel Grmw⦘ ⨾ Gsb ⨾ ⦗W⦘ ⨾ ⦗D⦘) ⊆₁ D.
Proof.
unfold D.
(* easy *)
Admitted.

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

Lemma dom_sb_F_AcqRel_in_CI : dom_rel (Gsb ⨾ ⦗E ∩₁ F ∩₁ Acq/Rel⦘) ⊆₁ C ∪₁ I.
Proof using TCCOH E_to_S F_SB_S S_in_W.
  rewrite E_to_S.
  unfold D.
  rewrite !set_inter_union_l.
  rewrite !id_union; relsf; unionL; splits.
  { generalize (dom_sb_covered TCCOH). clear. basic_solver 21. }
  arewrite (⦗dom_rel (Gsb^? ⨾ ⦗S⦘) ∩₁ F ∩₁ Acq/Rel⦘ ⊆
            ⦗dom_rel (⦗F ∩₁ Acq/Rel⦘ ⨾ Gsb^? ⨾ ⦗S⦘)⦘).
  { clear. basic_solver 12. }
  rewrite dom_rel_eqv_dom_rel.
  arewrite (⦗F ∩₁ Acq/Rel⦘ ⨾ Gsb^? ⨾ ⦗S⦘ ⊆ ⦗C⦘ ⨾ Gsb).
  2: { generalize (dom_sb_covered TCCOH). clear. basic_solver 21. }
  case_refl _.
  { rewrite S_in_W. clear. type_solver. }
  generalize F_SB_S.
  clear. basic_solver 10.
Qed.

Lemma dom_sb_F_AcqRel_in_D : dom_rel (Gsb ⨾ ⦗E ∩₁ F ∩₁ Acq/Rel⦘) ⊆₁ D.
Proof using TCCOH E_to_S F_SB_S S_in_W.
 rewrite dom_sb_F_AcqRel_in_CI, C_in_D, I_in_D. clear. relsf.
Qed.

Lemma dom_sb_F_Acq_in_D : dom_rel (Gsb ⨾ ⦗E ∩₁ F ∩₁ Acq⦘) ⊆₁ D.
Proof using TCCOH E_to_S F_SB_S S_in_W.
  arewrite (Acq ⊆₁ Acq/Rel) by (clear; mode_solver).
  apply dom_sb_F_AcqRel_in_D.
Qed.

Lemma dom_sb_F_Rel_in_D : dom_rel (Gsb ⨾ ⦗E ∩₁ F ∩₁ Rel⦘) ⊆₁ D.
Proof using TCCOH E_to_S F_SB_S S_in_W.
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
Proof using WF TCCOH E_to_S S_in_W.
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
Proof using WF TCCOH E_to_S S_in_W.
  rewrite C_in_D, I_in_D; relsf.
  apply dom_ppo_D.
Qed.

(******************************************************************************)
(**  new co relation  *)
(******************************************************************************)

(* TODO: move to ImmProperties.v *)
Lemma W_ex_eq_EW_W_ex : GW_ex ≡₁ E ∩₁ W ∩₁ GW_ex.
Proof using WF.
  generalize WF.(ImmProperties.W_ex_in_E).
  generalize WF.(W_ex_in_W). clear. basic_solver 10.
Qed.

(* TODO: move up. *)
Hypothesis S_I_in_W_ex : (S ∩₁ Tid_ thread) \₁ I ⊆₁ W_ex G.

Definition cert_co_base := I ∪₁ W_ex G.
Lemma cert_co_base_alt : cert_co_base ≡₁ I ∪₁ W_ex G ∩₁ Tid_ thread.
Proof using WF IT_new_co.
  clear -WF IT_new_co.
  unfold cert_co_base.
  split; [|basic_solver].
  unionL; [basic_solver|].
  rewrite W_ex_eq_EW_W_ex at 1.
  rewrite <- IT_new_co. basic_solver.
Qed.

Lemma I_in_cert_co_base : I ⊆₁ cert_co_base.
Proof using. unfold cert_co_base. basic_solver. Qed.
Lemma IST_in_cert_co_base : I ∪₁ S ∩₁ Tid_ thread ⊆₁ cert_co_base.
Proof using S_I_in_W_ex.
  rewrite AuxRel.set_subset_union_minus with (s:=S ∩₁ Tid_ thread) (s':=I).
  rewrite S_I_in_W_ex.
  unfold cert_co_base. clear. basic_solver.
Qed.

Definition cert_co := new_co G cert_co_base (E ∩₁ W ∩₁ Tid_ thread).

Lemma IST_new_co : cert_co_base ∪₁ E ∩₁ W ∩₁ Tid_ thread ≡₁ E ∩₁ W.
Proof using WF S_in_W ST_in_E IT_new_co.
  rewrite <- IT_new_co at 2.
  rewrite cert_co_base_alt.
  rewrite W_ex_eq_EW_W_ex at 1.
  clear. basic_solver.
Qed.

Lemma wf_cert_coE : cert_co ≡ ⦗E⦘ ⨾ cert_co ⨾ ⦗E⦘.
Proof using WF S_in_W ST_in_E IT_new_co.
  apply wf_new_coE; [apply IST_new_co|apply (wf_coE WF)].
Qed.

Lemma wf_cert_coD : cert_co ≡ ⦗W⦘ ⨾ cert_co ⨾ ⦗W⦘.
Proof using WF S_in_W ST_in_E IT_new_co.
  apply wf_new_coD; [apply IST_new_co|apply (wf_coD WF)].
Qed.

Lemma wf_cert_col : cert_co ⊆ Gsame_loc.
Proof using WF S_in_W ST_in_E IT_new_co.
  apply wf_new_col; [apply IST_new_co|apply (wf_coD WF)].
Qed.

Lemma cert_co_trans : transitive cert_co.
Proof using WF S_in_W ST_in_E IT_new_co.
  apply new_co_trans; try apply WF; apply IST_new_co.
Qed.

Lemma wf_cert_co_total : forall ol, is_total (E ∩₁ W ∩₁ (fun x => Gloc x = ol)) cert_co.
Proof using WF S_in_W ST_in_E IT_new_co.
  intros.
  apply wf_new_co_total.
  apply IST_new_co.
  all: apply WF.
Qed.

Lemma cert_co_irr : irreflexive cert_co.
Proof using WF S_in_W ST_in_E IT_new_co.
  apply new_co_irr. 
  apply IST_new_co.
  all: apply WF.
Qed.

Lemma cert_co_I : cert_co ⨾ ⦗ cert_co_base ⦘ ⊆ Gco ⨾ ⦗ cert_co_base ⦘.
Proof using WF S_in_W ST_in_E IT_new_co.
  apply new_co_I.
  apply IST_new_co.
  all: apply WF.
Qed.

Lemma I_co_in_cert_co : ⦗ cert_co_base ⦘ ⨾ Gco ⊆ cert_co.
Proof using WF S_in_W ST_in_E IT_new_co.
  apply I_co_in_new_co.
  apply IST_new_co.
  all: apply WF.
Qed.

Lemma cert_co_for_split_helper : ⦗set_compl cert_co_base⦘ ⨾ (immediate cert_co) ⊆ Gsb.
Proof using All.
(* Proof using WF S_in_W ST_in_E IT_new_co. *)
  unfold cert_co.
  red; intros x y H.
  assert (A: (E ∩₁ W ∩₁ Tid_ thread) y).
  { apply (co_for_split IST_new_co (wf_coE WF) (wf_coD WF)).
    red. eauto. }
  unfolder in H; desf.
  assert (B: (E ∩₁ W) x).
  { hahn_rewrite (wf_new_coE IST_new_co (wf_coE WF)) in H0.
    hahn_rewrite (wf_new_coD IST_new_co (wf_coD WF)) in H0.
    unfolder in H0. clear -H0. basic_solver. }
  apply IST_new_co in B; unfolder in B.
  destruct B as [B|[[B1 B2] B3]].
  { intuition. }
  unfolder in A.
  assert (D: (⦗ E ∩₁ W ∩₁ Tid_ (tid x) ⦘ ⨾ Gco) x y).
  { rewrite B3.
    eapply T_new_co.
    { apply IST_new_co. }
    all: try edone; try apply WF.
    clear -H0 A B1 B2 B3.
    basic_solver. }
  desf.
  eapply same_thread in A0; try edone.
  { desf.
    exfalso.
    unfolder in D; desf.
    destruct A0.
    { rewrite H2 in D0. eapply (co_irr WF); edone. }
    eapply COH.
    hahn_rewrite <- (@sb_in_hb G).
    hahn_rewrite <- (@co_in_eco G).
    clear -H2 D0.
    basic_solver. }
  hahn_rewrite (no_co_to_init WF (coherence_sc_per_loc COH)) in D.
  unfolder in D. apply D.
Qed.

Lemma cert_co_for_split :
  ⦗set_compl (GW_ex ∪₁ (I ∪₁ S ∩₁ Tid_ thread))⦘ ⨾ (immediate cert_co) ⊆ Gsb.
Proof using All.
  arewrite (immediate cert_co ⊆
            <|cert_co_base ∪₁ set_compl cert_co_base|> ;; immediate cert_co).
  { rewrite AuxRel.set_compl_union_id. unfold set_full. by rewrite seq_id_l. }
  rewrite id_union, seq_union_l, seq_union_r. unionL.
  2: { rewrite cert_co_for_split_helper. clear. basic_solver. }
  rewrite <- seqA. rewrite <- id_inter.
  rewrite set_interC. rewrite <- set_minusE.
  arewrite (cert_co_base \₁ (GW_ex ∪₁ (I ∪₁ S ∩₁ Tid_ thread)) ⊆₁ ∅).
  2: clear; basic_solver.
  unfold cert_co_base. clear. basic_solver.
Qed.

(* TODO: move to ImmProperties.v *)
Lemma I_eq_EW_I : I ≡₁ E ∩₁ W ∩₁ I.
Proof using TCCOH.
  clear -TCCOH.
  split; [|clear; basic_solver].
  generalize (issuedW TCCOH), (issuedE TCCOH).
  basic_solver.
Qed.

Lemma cert_co_alt :
  cert_co  ⊆ Gco ∩ cert_co ⨾ ⦗ cert_co_base ⦘ ∪ ⦗ Tid_ thread ⦘ ⨾ Gco ∩ cert_co ∪ 
           ⦗ I ∩₁ NTid_ thread ⦘ ⨾ cert_co ⨾ ⦗ (E ∩₁ W ∩₁ Tid_ thread) \₁
                                              cert_co_base ⦘.
Proof using All.
  arewrite (I ∩₁ NTid_ thread ≡₁ cert_co_base \₁ E ∩₁ W ∩₁ Tid_ thread).
  { rewrite cert_co_base_alt.
    split.
    2: { rewrite W_ex_eq_EW_W_ex, I_eq_EW_I at 1.
         rewrite set_minus_union_l. unionL.
         2: { clear. intros x [HH BB]. exfalso. apply BB.
              generalize HH. basic_solver. }
         clear. intros x [HH BB]. split; [by apply HH|].
         generalize HH, BB. basic_solver 10. }
    clear. intros x [HH BB]. split; [basic_solver|].
    unfolder. intros AA. desf. }
  arewrite (cert_co ⊆ cert_co ∩ cert_co) at 1.
  unfold cert_co at 1.
  rewrite new_co_in at 1.
  all: try by apply WF.
  { clear. basic_solver 40. }
  apply IST_new_co.
Qed.

Lemma cert_co_alt' : cert_co  ⊆ Gco ∩ cert_co ∪ 
  ⦗ I ∩₁ NTid_ thread ⦘ ⨾ cert_co ⨾ ⦗ (E ∩₁ W ∩₁ Tid_ thread) \₁ I ⦘.
Proof using All.
  rewrite cert_co_alt at 1.
  clear.
  unionL.
  3: rewrite <- I_in_cert_co_base at 1.
  all: basic_solver 12.
Qed.

(******************************************************************************)
(** Definition of the new rf edges   *)
(******************************************************************************)

(*Definition viewed l := Gurr l. *)
Definition new_rf := Gfurr ∩ Gsame_loc ⨾ ⦗(E \₁ D) ∩₁ R⦘ \ cert_co ⨾ Gfurr.
(* Definition new_rf_loc l := max_co' (viewed l) ⨾ ⦗(E \₁ D) ∩₁ Tid_ thread ∩₁ R_ l⦘. *)
(* Definition new_rf x y := exists l, new_rfl l x y.  *)
Print furr.
Print urr.
(* Definition new_rf := 
(((⦗W⦘ ⨾ Gsb \ (Gco ⨾ Gsb ∪ (Gco ⨾ ⦗I ∩₁ Tid_ thread⦘ ⨾ Gco ⨾ ⦗I⦘ ⨾ Gfurr)))
∪ ((⦗I⦘ ⨾ Gco^{-1} ⨾ ⦗I⦘ ⨾ Gsb) ∩ Gfurr \ (Gco ⨾ ⦗I⦘ ⨾ Gfurr))) ⨾
⦗(E \₁ D) ∩₁ Tid_ thread ∩₁ R⦘)
∩ Gsame_loc.
 *)

Lemma wf_new_rfE : new_rf ≡ ⦗E⦘ ⨾ new_rf ⨾ ⦗E \₁ D⦘.
Proof using WF WF_SC.
apply dom_helper_3.
unfold new_rf.
rewrite (wf_furrE WF WF_SC); basic_solver 21.
Qed.

Lemma wf_new_rfD : new_rf ≡ ⦗W⦘ ⨾ new_rf ⨾ ⦗R⦘.
Proof using.
apply dom_helper_3.
unfold new_rf.
unfold furr, urr; basic_solver.
Qed.

Lemma wf_new_rfl : new_rf ⊆ Gsame_loc.
Proof using.
unfold new_rf; basic_solver.
(* unfold new_rf, new_rf_loc, max_co', viewed, Events.same_loc.
red; ins; desc.
hahn_rewrite (@wf_urrD G) in H.
unfold seq, eqv_rel in H; desf.
unfolder in *; ins; desf; congruence.
 *)
Qed.

Lemma wf_new_rff : functional new_rf⁻¹.
Proof using WF WF_SC IT_new_co ST_in_E S_in_W.
  rewrite wf_new_rfD, wf_new_rfE.
  red; ins.
  assert (exists l, Gloc y = Some l).
  { generalize (is_w_loc Glab). generalize H. basic_solver 12. }
  desc.

  assert (Gloc z = Some l).
  { hahn_rewrite wf_new_rfl in H; hahn_rewrite wf_new_rfl in H0.
    generalize H H0. unfolder. ins. desf. congruence. }
  unfolder in H. unfolder in H0.
  destruct (classic (y=z)) as [|X]; eauto; desf.
  exfalso. eapply wf_cert_co_total in X.
  3: basic_solver 22.
  2: unfolder; splits; eauto; congruence.
  unfold new_rf in *. desf.
  all: unfolder in H12; unfolder in H5.
  all: basic_solver 40.
Qed.

Lemma new_rf_comp : forall b (IN: ((E \₁ D) ∩₁ R) b) , exists a, new_rf a b.
Proof using WF WF_SC IT_new_co ST_in_E S_in_W.
  ins; unfolder in IN; desf.
  assert (exists l, Gloc b = Some l); desc.
  { generalize (is_r_loc Glab). basic_solver 12. }
  assert (E (InitEvent l)).
  { apply WF; eauto. }
  assert (Glab (InitEvent l) = Astore Xpln Opln l 0) by apply WF. 
  assert (Gloc (InitEvent l) = Some l).
  { unfold loc. by rewrite (wf_init_lab WF). }
  assert (W_ l (InitEvent l)).
  { unfolder. unfold is_w, loc; desf; eauto. }
  assert (Gsb (InitEvent l) b).
  { apply init_ninit_sb; eauto. eapply read_or_fence_is_not_init; eauto. }
  assert (Gurr l (InitEvent l) b).
  { exists (InitEvent l); splits.
    unfold eqv_rel; eauto.
    hahn_rewrite <- sb_in_hb.
    basic_solver 12. }

  forward (eapply last_exists with (s:=cert_co ⨾ ⦗fun x=> Gfurr x b⦘) 
                                   (dom:= filterP (W_ l) G.(acts)) (a:=(InitEvent l))).
  { eapply acyclic_mon.
    apply trans_irr_acyclic; [apply cert_co_irr| apply cert_co_trans].
    basic_solver. }
  { ins.
    assert (A: (cert_co ⨾ ⦗fun x : actid => Gfurr x b⦘)^? (InitEvent l) c).
    { apply rt_of_trans; try done.
      apply transitiveI; unfolder; ins; desf; splits; eauto.
      eapply cert_co_trans; eauto. }
    unfolder in A; desf.
    { apply in_filterP_iff; split; auto. }
    apply in_filterP_iff.
    hahn_rewrite wf_cert_coE in A.
    hahn_rewrite wf_cert_coD in A.
    hahn_rewrite wf_cert_col in A.
    unfold same_loc in *.
    unfolder in A.
    desf; splits; eauto. red. splits; auto.
    congruence. }
  ins; desf.
  assert (A: (cert_co ⨾ ⦗fun x : actid => Gfurr x b⦘)^? (InitEvent l) b0).
  { apply rt_of_trans; try done.
    apply transitiveI; unfolder; ins; desf; splits; eauto.
    eapply cert_co_trans; eauto. }
  assert (Gloc b0 = Some l).
  { unfolder in A; desf.
    hahn_rewrite wf_cert_col in A.
    unfold same_loc in *; desf. unfolder in H7; congruence. }
  exists b0; red; split.
  { unfold furr, same_loc.
    unfolder in A; desf.
    all: unfolder; ins; desf.
    all: splits; try congruence.
    all: basic_solver 21. }
  unfold max_elt in *.
  unfolder in H7; ins; desf; intro; desf.
  unfolder in H9. desf.
  eapply H7. eauto.
Qed.

Lemma new_rf_mod: (E \₁ D) ∩₁ is_r Glab ≡₁ codom_rel new_rf.
Proof using WF WF_SC IT_new_co ST_in_E S_in_W.
  split.
  unfolder; ins; desf.
  apply new_rf_comp; basic_solver.
  unfold new_rf; basic_solver.
Qed.

Lemma new_rf_in_furr: new_rf ⊆ Gfurr.
Proof using.
unfold new_rf; basic_solver.
Qed.

Lemma new_rf_hb: irreflexive (new_rf ⨾ Ghb ⨾ (sc ⨾ Ghb)^?).
Proof using WF WF_SC CSC COH ACYC_EXT.
rewrite new_rf_in_furr.
apply furr_hb_sc_hb_irr; done.
Qed.

Lemma non_I_new_rf: ⦗E \₁ I⦘ ⨾ new_rf ⊆ Gsb.
Proof using WF WF_SC CSC COH ACYC_EXT IT_new_co.
  assert (new_rf_hb: irreflexive (new_rf ⨾ Ghb ⨾ (sc ⨾ Ghb)^?)).
  { by apply new_rf_hb. (* Coq bug ?! *) }

  rewrite wf_new_rfD.
  arewrite (⦗E \₁ I⦘ ⨾ ⦗W⦘ ⊆ ⦗E \₁ I⦘ ⨾ ⦗Tid_ thread⦘ ⨾ ⦗W⦘).
  { rewrite <- id_inter at 1.
    rewrite set_inter_minus_l.
    rewrite <- IT_new_co.
    clear.
    basic_solver. }
  rewrite wf_new_rfE.
  arewrite (E \₁ D ⊆₁ E ∩₁ Tid_ thread).
  { unfold D. clear. unfolder. ins. desf; tauto. }
  clear -new_rf_hb WF.
  unfolder; ins; desf.
  eapply (@same_thread G) in H3; desf.
  destruct H3; [subst x; type_solver|].
  2: intro K; apply (init_w WF) in K; type_solver.
  exfalso. generalize new_rf_hb.
  generalize (@sb_in_hb G).
  basic_solver 12.
Qed.

Lemma non_S_new_rf: ⦗E \₁ S⦘ ⨾ new_rf ⊆ Gsb.
Proof using WF WF_SC CSC COH ACYC_EXT IT_new_co I_in_S.
  rewrite <- I_in_S.
  apply non_I_new_rf.
Qed.

Lemma new_rfe_Acq : (new_rf \ Gsb) ⨾ ⦗R∩₁Acq⦘ ⊆ ∅₂.
Proof using WF WF_SC ACYC_EXT COH COMP_ACQ CSC IT_new_co S ST_in_E S_in_W.
rewrite wf_new_rfE.
arewrite (⦗E⦘ ⊆ ⦗E \₁ I⦘ ∪ ⦗E ∩₁ I⦘).
unfolder; ins; desf; tauto.
relsf.
rewrite minus_union_l.
relsf; unionL.
sin_rewrite non_I_new_rf.
basic_solver.
rewrite wf_new_rfD.
arewrite (new_rf ⊆ new_rf ∩ Gsame_loc).
generalize (wf_new_rfl); basic_solver.

unfolder; ins; desf.

assert (Lx:exists l, Gloc x = Some l); desc.
by apply is_w_loc.

assert (Ly:Gloc y = Some l).
unfold same_loc in *; congruence.

forward (apply COMP_ACQ).
by basic_solver.

ins; desc.

apply rfi_union_rfe in H10; unfolder in H10; desf; cycle 1.
by generalize R_Acq_codom_rfe; basic_solver 12.

ie_unfolder; unfolder in H10; desf.

hahn_rewrite (wf_rfD WF) in H10.
hahn_rewrite (wf_rfE WF) in H10.

unfolder in H10; desf.

assert (Lz:Gloc z = Some l).
by apply (wf_rfl WF) in H14; unfold same_loc in *; congruence.

forward (apply ((wf_co_total WF) (Some l) z)).
basic_solver.
instantiate (1 := x).
basic_solver.

intro; desf.

intro; desf.

-
eapply eco_furr_irr; try edone.
eexists; splits; [|eby apply new_rf_in_furr].
unfold eco, fr.
basic_solver 12.
- eapply H3.
exists z; split; [| apply furr_alt; basic_solver 12].
apply I_co_in_cert_co.
apply seq_eqv_l. split; auto.
red. basic_solver.
Qed.

(******************************************************************************)
(** The new label function   *)
(******************************************************************************)

Variable lab' : actid -> label.
Hypothesis SAME : same_lab_u2v lab' Glab.
Hypothesis NEW_VAL : forall r w (RF: new_rf w r), val lab' w = val lab' r.
Hypothesis OLD_VAL : forall a (NIN: ~ (E \₁ D) a), val lab' a = Gval a.

Lemma cert_R : is_r lab' ≡₁ R.
Proof using SAME. ins; erewrite same_lab_u2v_is_r; eauto. Qed.
Lemma cert_W : is_w lab' ≡₁ W.
Proof using SAME. ins; erewrite same_lab_u2v_is_w; eauto. Qed.
Lemma cert_F : is_f lab' ≡₁ F.
Proof using SAME. ins; erewrite same_lab_u2v_is_f; eauto. Qed.
Lemma cert_Rel : is_rel lab' ≡₁ Rel.
Proof using SAME. ins; erewrite same_lab_u2v_is_rel; eauto. Qed.
Lemma cert_Acq : is_acq lab' ≡₁ Acq.
Proof using SAME. ins; erewrite same_lab_u2v_is_acq; eauto. Qed.
Lemma cert_AcqRel : is_ra lab' ≡₁ Acq/Rel.
Proof using SAME. ins; erewrite same_lab_u2v_is_ra; eauto. Qed.
Lemma cert_Sc : is_sc lab' ≡₁ Sc.
Proof using SAME. ins; erewrite same_lab_u2v_is_sc; eauto. Qed.
Lemma cert_R_ex : R_ex lab' ≡₁ R_ex Glab.
Proof using SAME. ins; erewrite same_lab_u2v_R_ex; eauto. Qed.
Lemma cert_xacq : is_xacq lab' ≡₁ is_xacq Glab.
Proof using SAME. ins; erewrite same_lab_u2v_is_xacq; eauto. Qed.
Lemma cert_loc : loc lab' = Gloc.
Proof using SAME. ins; erewrite same_lab_u2v_loc; eauto. Qed.
Lemma cert_W_ l : (is_w lab') ∩₁ (fun x => loc lab' x = Some l) ≡₁ W_ l.
Proof using SAME. ins; erewrite same_lab_u2v_is_w, same_lab_u2v_loc; eauto. Qed.
Lemma cert_same_loc : same_loc lab' ≡ Gsame_loc.
Proof using SAME. ins; erewrite same_lab_u2v_same_loc; eauto. Qed.

(******************************************************************************)
(** Construction of the certification graph   *)
(******************************************************************************)

Definition certG :=
    {| acts := G.(acts);
       lab := lab' ;
       rmw := Grmw ;
       data := Gdata ;
       addr := Gaddr ;
       ctrl := Gctrl ;
       rmw_dep := Grmw_dep ;
       rf := Grf ⨾ ⦗D⦘ ∪ new_rf ;
       co := cert_co ;
    |}.

(* Notation "'CE'" := certG.(acts_set). *)
(* Notation "'Cacts'" := certG.(acts). *)
(* Notation "'Clab'" := certG.(lab). *)
(* Notation "'Csb'" := certG.(sb). *)
Notation "'Crf'" := certG.(rf).
Notation "'Cco'" := certG.(co).
(* Notation "'Crmw'" := certG.(rmw). *)
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
(* Notation "'Crelease'" := certG.(release). *)
Notation "'Crs'" := certG.(rs).
Notation "'Chb'" := certG.(hb).
Notation "'Cppo'" := certG.(ppo).
(* Notation "'Cbob'" := certG.(bob). *)
(* Notation "'Cfwbob'" := certG.(fwbob). *)
Notation "'Car'" := (certG.(ar) sc).
Notation "'Car_int'" := (certG.(ar_int)).
Notation "'Curr'" := (certG.(urr) sc).
Notation "'Cmsg_rel'" := (certG.(msg_rel) sc).

(******************************************************************************)
(** properties of the ceritifcation execution   *)
(******************************************************************************)

Lemma cert_lab_init : forall a (IN: is_init a), lab' a = Glab a.
Proof using TCCOH SAME OLD_VAL.
ins; cut (val lab' a = Gval a).
- assert (same_label_u2v (lab' a) (Glab a)) as SS by (by apply SAME).
  unfold same_label_u2v in *. unfold val; desf; desf.
  all: intros HH; inv HH.
- apply OLD_VAL.
  unfolder; desf.
  generalize (D_init); unfolder; ins; desf; intro; desf; eauto 20.
Qed.

Lemma cert_E : certG.(acts_set) ≡₁ E.
Proof using. unfold certG; vauto. Qed.
Lemma cert_sb : certG.(sb) ≡ Gsb.
Proof using. by unfold Execution.sb; rewrite cert_E. Qed.
Lemma cert_W_ex : certG.(W_ex) ≡₁ GW_ex.
Proof using. unfold Execution.W_ex; ins. Qed.


Lemma cert_fwbob : certG.(fwbob) ≡ Gfwbob.
Proof using SAME. 
unfold imm_bob.fwbob.
rewrite cert_W, cert_F, cert_Rel, cert_AcqRel.
by rewrite cert_sb, cert_same_loc.
Qed.

Lemma cert_bob : certG.(bob) ≡ Gbob.
Proof using SAME. 
unfold imm_bob.bob.
by rewrite cert_R, cert_Acq, cert_fwbob, cert_sb.
Qed.

Lemma cert_W_ex_acq : certG.(W_ex) ∩₁ is_xacq lab' ≡₁ GW_ex ∩₁ xacq.
Proof using SAME.
unfold Execution.W_ex.
by rewrite cert_xacq; ins.
Qed.

Lemma cert_rfe : certG.(rfe) ≡ ⦗I⦘ ⨾ Grfe ⨾ ⦗D⦘ ∪ ⦗I⦘ ⨾ (new_rf \ Gsb).
Proof using WF WF_SC ACYC_EXT COH CSC IT_new_co Grfe_E.
unfold Execution.rfe; ins.
rewrite cert_sb.
split; [|basic_solver 12].
rewrite minus_union_l; unionL.
generalize Grfe_E; ie_unfolder; basic_solver 21.
rewrite (dom_l wf_new_rfE) at 1.
  arewrite (⦗E⦘ ⊆ ⦗E ∩₁ I⦘ ∪ ⦗E \₁ I⦘) at 1.
  by unfolder; ins; desf; tauto.
relsf; rewrite minus_union_l; unionL.
basic_solver 21.
rewrite (non_I_new_rf).
basic_solver 21.
Qed.

Lemma cert_rfe_D : certG.(rfe) ⨾ ⦗D⦘ ⊆ ⦗I⦘ ⨾ Grfe.
Proof using WF WF_SC ACYC_EXT COH CSC IT_new_co Grfe_E.
rewrite cert_rfe.
rewrite (dom_r wf_new_rfE).
basic_solver 12.
Qed.

Lemma cert_rf_D : Crf ⨾ ⦗D⦘ ≡ Grf ⨾ ⦗D⦘.
Proof using WF WF_SC.
  ins; split; [rewrite wf_new_rfE|].
  all: clear; basic_solver 20.
Qed.

Lemma cert_rfi_D : Crfi ⨾ ⦗D⦘ ⊆ ⦗D⦘ ⨾ Grfi ⨾ ⦗D⦘.
Proof using  WF WF_SC TCCOH Grfe_E.
ie_unfolder; rewrite cert_sb.
rewrite <- seq_eqv_inter_lr.
rewrite cert_rf_D.
rewrite (dom_rel_helper dom_rf_D).
clear.
basic_solver.
Qed.

Lemma dom_Grfi_nD_in_thread :
  dom_rel (Grfi ⨾ ⦗set_compl D⦘) ⊆₁ Tid_ thread.
Proof using WF TCCOH.
  unfolder. intros x [y [RFI ND]].
  destruct (classic (I x)) as [IX|NIX].
  { exfalso. apply ND.
    do 2 red. left. right. basic_solver 10. }
  destruct RFI as [RF SB].
  apply WF.(wf_rfE) in RF.
  unfolder in RF. desf.
  assert (~ is_init x) as NINX.
  { intros II. apply NIX. 
    eapply init_issued; eauto. by split. }
  apply sb_tid_init in SB. desf.
  apply NNPP. intros NTX.
  assert (tid y <> thread) as NTY.
  { intros HH. apply NTX. by rewrite <- HH. }
  apply ND. red. do 4 left. right. by split.
Qed.

Lemma Grfi_nD_in_new_rf : Grfi ⨾ ⦗set_compl D⦘ ⊆ new_rf.
Proof using All.
  unfold new_rf.
  rewrite AuxRel.minus_inter_compl.
  apply inclusion_inter_r.
  { rewrite furr_alt; [|done].
    arewrite (Grfi ⊆ Grf).
    rewrite (dom_r WF.(wf_rfE)) at 1.
    rewrite (WF.(wf_rfD)) at 1.
    arewrite (Grf ⊆ Grf ∩ Grf) at 1.
    rewrite (WF.(wf_rfl)) at 1.
    clear.
    basic_solver 21. }
  rewrite (dom_rel_helper dom_Grfi_nD_in_thread).
  arewrite (Grfi ⊆ Grf).
  rewrite cert_co_alt'.
  unfolder; ins; desf.
  intro; desf.
  eapply eco_furr_irr; try edone.
  exists z; splits; eauto.
  red; right. unfolder; ins; desf.
  exists z; splits; eauto; red.
  basic_solver.
Qed.

Lemma Grfi_in_Crfi : Grfi ⊆ Crfi.
Proof using All.
arewrite (Grfi ⊆ Grfi ⨾ ⦗D ∪₁ set_compl D⦘).
by clear; unfolder; ins; desf; tauto.
rewrite id_union; rewrite seq_union_r; unionL.
{ unfold rfi.
  rewrite cert_sb.
  generalize cert_rf_D.
  by clear; unfolder; ins; desf; unfolder; eauto 12. }
arewrite (Grfi ⨾ ⦗set_compl D⦘ ⊆ Gsb ∩ (Grfi ⨾ ⦗set_compl D⦘)).
by clear; unfold rfi; basic_solver.
rewrite Grfi_nD_in_new_rf. 
unfold rfi. rewrite cert_sb.
clear; unfold certG; simpl; basic_solver.
Qed.

Lemma Crf_in_furr : Crf ⊆ Gfurr.
Proof using All.
unfold certG; ins.
rewrite new_rf_in_furr.
Admitted.

Lemma Grfe_in_inv_Gco_cr_Crf : Grfe ⊆ (Gco^{-1})^? ;; Crf.
Proof using All.
arewrite (Grfe ⊆ ((Gco ∪ Gco^{-1})^? ;; Crf) ∩ Grfe).
{ admit. }
rewrite crE at 1; relsf.
rewrite !inter_union_l; unionL.
1,3: basic_solver.
transitivity (fun _ _ : actid => False); [|basic_solver].
rewrite Crf_in_furr.
clear - COH WF WF_SC CSC.
unfold rfe.
unfolder; ins; desf.
eapply eco_furr_irr; eauto.
eexists; splits; eauto.
apply fr_in_eco; eexists; splits; eauto.
Admitted.

Lemma I_Grfe_in_inv_Gco_cr_Crf : <| I |> ;; Grfe ⊆ (cert_co ∩ Gco^{-1})^? ;; Crf.
Proof.
arewrite (Grfe ⊆ Grfe ⨾ ⦗D ∪₁ set_compl D⦘).
by clear; unfolder; ins; desf; tauto.
rewrite id_union; rewrite !seq_union_r; unionL.
by clear; unfold certG, rfe; simpl; basic_solver 12.
arewrite (Grfe ⊆ Grfe ∩ Grfe).
rewrite Grfe_in_inv_Gco_cr_Crf at 1.
rewrite !crE; relsf.
rewrite !inter_union_l, seq_union_l, seq_union_r; unionL.
by basic_solver.
unionR right.
rewrite WF.(wf_coE).
rewrite WF.(wf_coD).
arewrite (Gco ⊆ Gco ∩ Gsame_loc) at 1.
{ generalize WF.(wf_col); basic_solver. }
unfolder; ins; desf.
edestruct is_w_loc; eauto.
exists z0; splits; eauto 10.
eapply tot_ex.
{ apply wf_new_co_total. 
  apply IST_new_co.
  all: apply WF. }
{ unfolder; eauto. }
{ unfolder; eauto. }
2: by intro; subst; eapply WF.(co_irr); eauto.
unfolder in H3; desf.
intro HH.
apply H3.
eexists; splits; eauto.
admit.
Admitted.


 (* TODO: move this up *)
Hypothesis ETC_DR_R_ACQ_I : dom_rel ((Gdetour ∪ Grfe) ⨾ (Grmw ⨾ Grfi)^* ⨾ ⦗R∩₁Acq⦘ ⨾ Gsb ⨾ ⦗S⦘) ⊆₁ I.


Lemma Grfe_to_Acq_S_in_Crf : <| I |> ;; Grfe ;; <| dom_rel ((Grmw ⨾ Grfi)^* ⨾ ⦗R∩₁Acq⦘ ⨾ Gsb ⨾ ⦗S⦘) |> ⊆ Crf.
Proof using All.
arewrite (Grfe ⊆ Grfe ⨾ ⦗D ∪₁ set_compl D⦘).
by clear; unfolder; ins; desf; tauto.
rewrite id_union; rewrite !seq_union_l, !seq_union_r; unionL.
by clear; unfold certG, rfe; simpl; basic_solver 12.
unfold certG; simpl; unionR right.
arewrite (Grfe ⨾ ⦗set_compl D⦘ ⊆ ((Gco ∪ Gco^{-1})^? ;; new_rf) ∩ Grfe).
admit.
rewrite crE.
SearchAbout furr.
sn_rewrite inter_union_l.
rewrite seq_union_l, !seq_union_r; unionL; [basic_solver 14|].
SearchAbouit 

(******************************************************************************)
(** **   *)
(******************************************************************************)

(*
Lemma cert_release : certG.(release) ≡ Grelease.
Proof using WF WF_SC TCCOH E_to_S SAME S_in_W.
unfold imm_s_hb.release, imm_s_hb.rs; ins.
rewrite cert_F, cert_Rel, cert_W, cert_same_loc, cert_sb.
rewrite (dom_rel_helper dom_rmw_in_D) at 1.
seq_rewrite cert_rf_D.
rewrite (dom_rel_helper dom_rmw_in_D) at 2.
by rewrite !seqA.
Qed.
*)

Lemma sw_helper_S :
  Grelease ⨾ ⦗E ∩₁ S⦘ ⨾ new_rf ⨾ ⦗Acq⦘ ⊆ 
  Gsb ∪ (Grelease ⨾ Grf ⨾ ⦗Acq⦘ ∪ Grelease ⨾ Grf ⨾ Gsb ⨾ ⦗F⦘ ⨾ ⦗Acq⦘).
Proof using All.
  unfold new_rf.
  unfolder; ins; desf.
  assert (A: exists w : actid, Grf w y); desc.
  { eapply COMP_ACQ. basic_solver. }
  destruct (classic (w=z)); subst; [eauto 20|].
  exfalso.
  unfold furr in *; desf; eauto.
  assert (Gloc z = Some l).
  { hahn_rewrite (@wf_urrD G) in H1. unfolder in H1. desf. }
  eapply (transp_rf_co_urr_irr WF WF_SC CSC COH).
  assert (W w).
  { hahn_rewrite (wf_rfD WF) in A; unfolder in A; desf. }
  assert (Loc_ l w).
  { hahn_rewrite (wf_rfl WF) in A; unfold same_loc in *.
    unfolder in A; desf; congruence. }
  exists w; splits.
  { basic_solver. }
  assert (W z) as WZ.
  { match goal with
    | H : Grelease _ _ |- _ => rename H into REL
    end.
    apply (dom_r WF.(wf_releaseD)) in REL.
    clear -REL. unfolder in REL. desf. }
  assert (E w) as EW.
  { hahn_rewrite (wf_rfE WF) in A; unfolder in A; desf. }
  exists z; split; eauto.
  exploit (new_co_I IST_new_co); try apply WF; [| basic_solver].
  unfolder; splits; eauto.
  { eapply tot_ex.
    { by eapply (wf_new_co_total IST_new_co); try apply WF. }
    { unfolder; splits; eauto. }
    { basic_solver 10. }
    { intro.
      eapply H3. exists w. splits; eauto.
      exists l; unfold urr.
      apply (wf_urrE WF WF_SC) in H1.
      basic_solver 12. }
    intro; subst; eauto. }
  apply IST_in_cert_co_base.
  assert ((E ∩₁ W) z) as AA. 
  { split; auto. }
  apply IT_new_co in AA. unfolder in AA.
  unfolder.
  desf; eauto.
Qed.

Lemma sw_helper :
  Grelease ⨾ ⦗E ∩₁ I⦘ ⨾ new_rf ⨾ ⦗Acq⦘ ⊆ 
  Gsb ∪ (Grelease ⨾ Grf ⨾ ⦗Acq⦘ ∪ Grelease ⨾ Grf ⨾ Gsb ⨾ ⦗F⦘ ⨾ ⦗Acq⦘).
Proof using All.
  rewrite I_in_S.
  apply sw_helper_S.
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
  rewrite cert_F, cert_Acq, cert_sb.
  rewrite !crE, !seq_union_l, !seq_union_r, !seq_id_l, !seqA.
  unionL.
  { arewrite (⦗Acq⦘ ⊆ (⦗D⦘ ∪ ⦗set_compl D⦘) ⨾ ⦗Acq⦘) at 1.
    { unfolder. ins. desf. destruct (classic (D y)); eauto. }
    rewrite !seq_union_l, !seq_union_r.
    unionL.
    { seq_rewrite (dom_rel_helper dom_rf_D). admit. }
    rewrite rfi_union_rfe.
    rewrite !seq_union_l, !seq_union_r.
    unionL; cycle 1.
    { transitivity (fun _ _ : actid => False); [|basic_solver].
      rewrite (dom_r WF.(wf_rfeD)).
      unfold D; basic_solver 21. }
    rewrite (dom_r WF.(wf_rfiE)) at 1.
    rewrite E_to_S.
    rewrite C_in_D; rewrite id_union, !seq_union_r, !seq_union_l, !seq_union_r, !seqA.
    unionL; [basic_solver|].
    unfold release at 1, rs at 1.
    rewrite rt_rf_rmw.
    rewrite rtE with (r:= Grfe ⨾ Grmw ⨾ (Grfi ⨾ Grmw)＊).
    rewrite !seq_union_r, !seq_union_l; unionL.
    { (* SB! *) admit. }
    rewrite ct_end, <- !seqA.
    arewrite (((((((⦗Rel⦘ ⨾ (⦗F⦘ ⨾ Gsb)^?) ⨾ ⦗W⦘) ⨾ (Gsb ∩ Gsame_loc)^?) ⨾ ⦗W⦘) ⨾ 
      (Grfi ⨾ Grmw)＊) ⨾ ((Grfe ⨾ Grmw) ⨾ (Grfi ⨾ Grmw)＊)＊) ⊆ Grelease).
    { admit. }
    
    assert (BB: Grmw ⨾ (Grfi ⨾ Grmw)＊ ⨾ Grfi ⊆ (Grmw ⨾ Grfi)^+).
    { seq_rewrite <- rt_seq_swap.
      rewrite !seqA.
      remember (Grmw ⨾ Grfi) as X.
      apply ct_end. }
    sin_rewrite BB.
    assert (AA: dom_rel (Grfe ⨾ (Grmw ⨾ Grfi)⁺ ⨾ ⦗dom_rel (Gsb^? ⨾ ⦗S⦘)⦘ ⨾ ⦗Acq⦘) ⊆₁ I).
    { rewrite (dom_r WF.(wf_rfiD)) at 1.
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
    SearchAbout Grfi.
    
    Grmw ⨾ (Grfi ⨾ Grmw)＊ ⨾ Grfi_nD_in_new_rf
    Print D.
    SearchAbout new_rf.
     SearchAbout new_rf.
      SearchAbout (dom_rel ( _ ;; <| dom_rel _ |>)).
    SearchAbout (_ (_ ;; _ )^*).
    re
    
    

unfold release at 1.
    SearchAbout release.
    Print D.
    SearchAbout E.
    
     sin_rewrite Grfi_nD_in_new_rf.

  2: { rewrite <- R_Acq_codom_rfe at 2.
       rewrite (dom_r (wf_rfeD WF)) at 1.
       basic_solver 21. }
  arewrite (⦗Acq⦘ ⊆ (⦗D⦘ ∪ ⦗set_compl D⦘) ⨾ ⦗Acq⦘) at 1.
  { unfolder. ins. desf. destruct (classic (D y)); eauto. }
  rewrite !seq_union_l, !seq_union_r.
  unionL.
  { eauto with hahn. }
  sin_rewrite Grfi_nD_in_new_rf.
  eauto with hahn.



  admit.
(*   { eauto 6 with hahn hahn_full. }
 *)  arewrite (Gsb ⨾ ⦗F⦘ ⨾ ⦗Acq⦘ ≡ ⦗D⦘ ⨾ Gsb ⨾ ⦗F⦘ ⨾ ⦗Acq⦘) at 1.
       2: basic_solver 12.
       rewrite (dom_r (@wf_sbE G)). generalize dom_sb_F_Acq_in_D.
       basic_solver 12. }
  rewrite rfi_union_rfe.
  rewrite !seq_union_l, !seq_union_r.
  unionL.
  2: { rewrite <- R_Acq_codom_rfe at 2.
       rewrite (dom_r (wf_rfeD WF)) at 1.
       basic_solver 21. }
  arewrite (⦗Acq⦘ ⊆ (⦗D⦘ ∪ ⦗set_compl D⦘) ⨾ ⦗Acq⦘) at 1.
  { unfolder. ins. desf. destruct (classic (D y)); eauto. }
  rewrite !seq_union_l, !seq_union_r.
  unionL.
  { eauto with hahn. }
  sin_rewrite Grfi_nD_in_new_rf.
  eauto with hahn.
Qed.

Lemma cert_sb_sw : Gsb ∪ Csw ≡ Gsb ∪ Gsw.
Proof using All.
  split; [|by apply cert_sb_sw_helper].
  unionL; [by eauto with hahn|].
  unfold imm_s_hb.sw; ins.
  rewrite cert_F, cert_Acq, cert_release, cert_sb.
  rewrite !crE, !seq_union_l, !seq_union_r, !seq_id_l, !seqA.
  unionL.
  all: eauto 6 with hahn hahn_full.
  2: { arewrite (Gsb ⨾ ⦗F⦘ ⨾ ⦗Acq⦘ ≡ ⦗D⦘ ⨾ Gsb ⨾ ⦗F⦘ ⨾ ⦗Acq⦘).
       { rewrite (dom_r (@wf_sbE G)). generalize dom_sb_F_Acq_in_D. basic_solver 12. }
       rewrite (dom_r wf_new_rfE). basic_solver. }
  rewrite (dom_r wf_new_rfD).
  rewrite (dom_r wf_new_rfE).
  rewrite !seqA.
  rewrite <- !id_inter. rewrite set_inter_minus_l. rewrite <- set_interA.
  arewrite (E ∩₁ R ∩₁ Acq ⊆₁ codom_rel Grf ∩₁ (E ∩₁ R ∩₁ Acq)).
  { generalize COMP_ACQ. clear. basic_solver 10. }
  rewrite rfi_union_rfe at 1. rewrite codom_union.
  rewrite set_inter_union_l. rewrite set_minus_union_l, id_union, !seq_union_r.
  unionL.
  { unionR right -> left.
    hahn_frame.
    intros x y HH. apply seq_eqv_r in HH. destruct HH as [HH [[[x' CC] [BB ACQ]] ND]].
    apply seq_eqv_r. split; auto.
    assert (x' = x); [|by subst; apply CC].
    eapply wf_new_rff; eauto.
    apply Grfi_nD_in_new_rf. apply seq_eqv_r. split; auto. }
  arewrite (codom_rel Grfe ∩₁ (E ∩₁ R ∩₁ Acq) ⊆₁ D).
  { unfold D. unionR right. basic_solver. }
  basic_solver.
Qed.

Lemma cert_hb : Chb ≡ Ghb.
Proof using All.
by unfold imm_s_hb.hb; rewrite cert_sb_sw.
Qed.

Lemma cert_msg_rel l : Cmsg_rel l ⨾ ⦗I⦘ ≡ Gmsg_rel l ⨾ ⦗I⦘.
Proof using All.
unfold CombRelations.msg_rel, urr.
rewrite cert_W_, cert_F, cert_Sc, cert_release, cert_hb, !seqA.
arewrite ((Ghb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ sc^? ⨾ Ghb^? ⨾ Grelease ⨾ ⦗I⦘ ≡ ⦗C⦘ ⨾ (Ghb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ sc^? ⨾ Ghb^? ⨾ Grelease ⨾ ⦗I⦘).
split; [|basic_solver 21].
by rewrite (dom_rel_helper (urr_helper)) at 1.

arewrite (Crf^? ⨾ ⦗C⦘ ≡ Grf^? ⨾ ⦗C⦘).
rewrite !crE; relsf.
arewrite (⦗C⦘ ≡ ⦗C⦘ ⨾ ⦗C⦘) at 2.
by basic_solver.
arewrite (⦗C⦘ ≡ ⦗C⦘ ⨾ ⦗C⦘) at 5.
by basic_solver.
split; unionL; try basic_solver.
rewrite C_in_D at 1. 
seq_rewrite cert_rf_D; basic_solver.
rewrite C_in_D at 1. 
seq_rewrite <- cert_rf_D; basic_solver.

done.
Qed.



Lemma cert_t_cur_thread l : t_cur certG sc thread l
  (covered T ∪₁ E ∩₁ NTid_ thread) ≡₁ t_cur G sc thread l (covered T).
Proof using All.
unfold t_cur, c_cur, urr.
rewrite cert_W_, cert_F, cert_Sc, cert_hb, !seqA.

arewrite  (⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C ∪₁ E ∩₁ NTid_ thread⦘ ≡  ⦗C⦘ ⨾ ⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C⦘).
unfolder; splits; ins; desf; splits; eauto.
by apply (init_covered TCCOH); split; eauto; apply (sub_E_in SUB).
by apply (init_covered TCCOH); split; eauto; apply (sub_E_in SUB).

arewrite (⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C⦘ ≡ ⦗C⦘ ⨾ ⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C⦘) at 2.
basic_solver 12.


arewrite ((Ghb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ sc^? ⨾ Ghb^? ⨾ ⦗C⦘ ≡ ⦗C⦘ ⨾ (Ghb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ sc^? ⨾ Ghb^? ⨾ ⦗C⦘).
split; [generalize (urr_helper_C)|]; basic_solver 21.

remember (dom_rel
  (⦗W_ l⦘
   ⨾ Crf^?
     ⨾ ⦗C⦘
       ⨾ (Ghb ⨾ ⦗F ∩₁ Sc⦘)^?
         ⨾ sc^? ⨾ Ghb^? ⨾ ⦗C⦘ ⨾ ⦗C⦘ ⨾ ⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C⦘)) as X.

arewrite ((Ghb ⨾ ⦗F ∩₁ Sc⦘)^?
          ⨾ sc^? ⨾ Ghb^? ⨾ ⦗C⦘ ≡ ⦗C⦘ ⨾ (Ghb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ sc^? ⨾ Ghb^? ⨾ ⦗C⦘).
split; [generalize (urr_helper_C)|]; basic_solver 21.


subst.

arewrite (Crf^? ⨾ ⦗C⦘ ≡ Grf^? ⨾ ⦗C⦘).
{ arewrite (⦗C⦘ ≡ ⦗D⦘ ⨾ ⦗C⦘).
split.
generalize C_in_D; basic_solver.
basic_solver. 
rewrite !crE; relsf. 
seq_rewrite cert_rf_D.
rewrite !seqA.
done.
}
done.
Qed.


Lemma cert_t_rel_thread l l' : t_rel certG sc thread l l'
  (covered T ∪₁ E ∩₁ NTid_ thread) ≡₁ t_rel G sc thread l l' (covered T).
Proof using All.
unfold t_rel, c_rel, urr.
rewrite !cert_W_, cert_F, cert_Sc, cert_hb, cert_Rel, !seqA.

arewrite  (⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C ∪₁ E ∩₁ NTid_ thread⦘ ≡  ⦗C⦘ ⨾ ⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C⦘).
unfolder; splits; ins; desf; splits; eauto.
by apply (init_covered TCCOH); split; eauto; apply (sub_E_in SUB).
by apply (init_covered TCCOH); split; eauto; apply (sub_E_in SUB).

arewrite (⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C⦘ ≡ ⦗C⦘ ⨾ ⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C⦘) at 2.
basic_solver 12.

arewrite (⦗Rel⦘ ⨾ ⦗W_ l' ∪₁ F⦘ ⨾ ⦗C⦘ ≡ ⦗C⦘ ⨾ ⦗Rel⦘ ⨾ ⦗W_ l' ∪₁ F⦘).
basic_solver 12.


arewrite ((Ghb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ sc^? ⨾ Ghb^? ⨾ ⦗C⦘ ≡ ⦗C⦘ ⨾ (Ghb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ sc^? ⨾ Ghb^? ⨾ ⦗C⦘).
split; [generalize (urr_helper_C)|]; basic_solver 21.


remember (dom_rel
  (⦗W_ l⦘
   ⨾ Crf^?
     ⨾ ⦗C⦘
       ⨾ (Ghb ⨾ ⦗F ∩₁ Sc⦘)^?
         ⨾ sc^? ⨾ Ghb^? ⨾ ⦗C⦘ ⨾ ⦗C⦘ ⨾ ⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C⦘)) as X.

arewrite ((Ghb ⨾ ⦗F ∩₁ Sc⦘)^?
          ⨾ sc^? ⨾ Ghb^? ⨾ ⦗C⦘ ≡ ⦗C⦘ ⨾ (Ghb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ sc^? ⨾ Ghb^? ⨾ ⦗C⦘).
split; [generalize (urr_helper_C)|]; basic_solver 21.


subst.

arewrite (Crf^? ⨾ ⦗C⦘ ≡ Grf^? ⨾ ⦗C⦘).
{ arewrite (⦗C⦘ ≡ ⦗D⦘ ⨾ ⦗C⦘).
split.
generalize C_in_D; basic_solver.
basic_solver. 
rewrite !crE; relsf. 
seq_rewrite cert_rf_D.
rewrite !seqA.
done.
}
done.
Qed.


Lemma cert_t_acq_thread l : t_acq certG sc thread l
  (covered T ∪₁ E ∩₁ NTid_ thread) ≡₁ t_acq G sc thread l (covered T).
Proof using All.
unfold t_acq, c_acq, urr.
rewrite !cert_W_, cert_F, cert_Sc, cert_hb, cert_release, !seqA.

arewrite  (⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C ∪₁ E ∩₁ NTid_ thread⦘ ≡  ⦗C⦘ ⨾ ⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C⦘).
unfolder; splits; ins; desf; splits; eauto.
by apply (init_covered TCCOH); split; eauto; apply (sub_E_in SUB).
by apply (init_covered TCCOH); split; eauto; apply (sub_E_in SUB).

arewrite (⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C⦘ ≡ ⦗C⦘ ⨾ ⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C⦘) at 2.
basic_solver 12.

arewrite ((Grelease ⨾ Crf)^? ⨾ ⦗C⦘ ≡ (Grelease ⨾ Grf)^? ⨾ ⦗C⦘).
{ arewrite (⦗C⦘ ≡ ⦗D⦘ ⨾ ⦗C⦘).
split.
generalize C_in_D; basic_solver.
basic_solver. 
rewrite !crE; relsf.
rewrite !seqA.
seq_rewrite cert_rf_D.
rewrite !seqA.
done.
}

arewrite ((Ghb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ sc^? ⨾ Ghb^? ⨾ (Grelease ⨾ Grf)^? ⨾  ⦗C⦘ ≡ ⦗C⦘ ⨾ (Ghb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ sc^? ⨾ Ghb^? ⨾ (Grelease ⨾ Grf)^? ⨾ ⦗C⦘).
split; [generalize (urr_helper_C)|]; basic_solver 21.


remember (dom_rel
  (⦗W_ l⦘
   ⨾ Crf^?
     ⨾ ⦗C⦘
       ⨾ (Ghb ⨾ ⦗F ∩₁ Sc⦘)^?
         ⨾ sc^? ⨾ Ghb^? ⨾ (Grelease ⨾ Grf)^? ⨾ ⦗C⦘ ⨾ ⦗C⦘ ⨾ ⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C⦘)) as X.

arewrite ((Ghb ⨾ ⦗F ∩₁ Sc⦘)^?
          ⨾ sc^? ⨾ Ghb^? ⨾ (Grelease ⨾ Grf)^? ⨾ ⦗C⦘ ≡ ⦗C⦘ ⨾ (Ghb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ sc^? ⨾ Ghb^? ⨾ (Grelease ⨾ Grf)^? ⨾ ⦗C⦘).
split; [generalize (urr_helper_C)|]; basic_solver 21.


subst.

arewrite (Crf^? ⨾ ⦗C⦘ ≡ Grf^? ⨾ ⦗C⦘).
{ arewrite (⦗C⦘ ≡ ⦗D⦘ ⨾ ⦗C⦘).
split.
generalize C_in_D; basic_solver.
basic_solver. 
rewrite !crE; relsf. 
seq_rewrite cert_rf_D.
rewrite !seqA.
done.
}
done.
Qed.




(******************************************************************************)
(** **   *)
(******************************************************************************)



Lemma WF_cert : Wf certG.
Proof using WF WF_SC TCCOH Grfe_E IT_new_co NEW_VAL OLD_VAL SAME ST_in_E S_in_W.
constructor; ins.
all: rewrite ?cert_sb, ?cert_R, ?cert_W, ?cert_same_loc, ?cert_E, ?cert_rf, ?cert_co, ?cert_R_ex.
all: try by apply WF.
- apply dom_helper_3; rewrite (wf_rfE WF), wf_new_rfE; basic_solver.
- apply dom_helper_3; rewrite (wf_rfD WF), wf_new_rfD; basic_solver.
- rewrite (wf_rfl WF), wf_new_rfl; basic_solver.
- ins; unfolder; ins; desf; eauto.
  unfold funeq; ins.
  hahn_rewrite (wf_rfE WF) in H; unfolder in H; desc.
  rewrite !OLD_VAL.
  by apply wf_rfv; eauto.
  by intro B; eapply B; eauto.
  by intro A; eapply A; generalize dom_rf_D; basic_solver.
- rewrite transp_union; apply functional_union.
  by unfolder; ins; eapply (wf_rff WF); basic_solver.
  by apply wf_new_rff.
  by unfolder; ins; desf; apply wf_new_rfE in H0; unfolder in H0; basic_solver.
- apply wf_new_coE; [apply IST_new_co|apply (wf_coE WF)].
- apply wf_new_coD; [apply IST_new_co|apply (wf_coD WF)].
- apply wf_new_col; [apply IST_new_co|apply (wf_coD WF)].
- apply new_co_trans.
  apply IST_new_co.
  all: apply WF.
- intros. erewrite same_lab_u2v_loc; try edone.
  apply wf_new_co_total. 
  apply IST_new_co.
  all: apply WF.
- apply new_co_irr. 
  apply IST_new_co.
  all: apply WF.
- ins; desf; apply cert_E.
  by apply (wf_init WF); exists b; splits; [apply cert_E| rewrite <- cert_loc].
- ins; rewrite cert_lab_init.
  apply (wf_init_lab WF).
  by unfold is_init.
Qed.

Lemma WF_SC_cert : wf_sc certG sc.
Proof using WF_SC SAME.
constructor.
- rewrite cert_E; apply WF_SC.
- rewrite cert_F, cert_Sc; apply WF_SC.
- apply WF_SC.
- rewrite cert_E, cert_F, cert_Sc; apply WF_SC.
- apply WF_SC.
Qed.

(******************************************************************************)
(** **   *)
(******************************************************************************)


Lemma cert_complete : complete certG.
Proof using TCCOH WF WF_SC IT_new_co SAME ST_in_E S_in_W COMP_C COMP_NTID COMP_PPO COMP_RPPO.
red; unfolder; ins; desf.
destruct (classic (D x)).
- forward (apply (complete_D)).
  unfolder; ins; desf; eauto 20.
  apply cert_R in H0.
  forward (apply H2); splits; try edone; desf; eexists; eauto.
- forward (apply new_rf_comp).
  by unfolder; ins; desf; splits; eauto; apply cert_R; ins.
  ins; desf; basic_solver 12.
Qed.

Lemma cert_coherece_detour_helper :
  irreflexive (Ghb ⨾ (sc ⨾ Ghb)^? ⨾ ⦗D⦘ ⨾ Grf⁻¹⨾ ⦗I ∩₁ NTid_ thread⦘ ⨾ cert_co ⨾ ⦗E ∩₁ W ∩₁ Tid_ thread \₁ I⦘).
Proof using All.
assert (A: dom_rel (Gdetour ⨾ ⦗D⦘) ⊆₁ I).
by apply dom_detour_D. (* Ori: weird Coq behavior? *)

rewrite wf_cert_col.
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

Lemma coh_helper : irreflexive (Chb ⨾ (sc ⨾ Chb)^? ⨾ Ceco^?).
Proof using All.
  apply coh_helper_alt; rewrite cert_hb; relsf; unionL.
  { case_refl sc; [by apply hb_irr|].
    rewrite (wf_scD WF_SC); rotate 1.
    sin_rewrite (f_sc_hb_f_sc_in_ar sc WF).
    unfolder; ins; desc.
    eapply ACYC_EXT.
    eapply t_trans; [edone| apply t_step].
      by apply sc_in_ar. }
  { rewrite cert_rfe; relsf; unionL.
    { revert COH CSC; unfold coherence, coh_sc, eco.
      ie_unfolder. basic_solver 21. }
    generalize new_rf_hb. basic_solver 12. }
  { rewrite cert_co_alt'; relsf; unionL.
    { revert COH CSC. unfold coherence, coh_sc, eco. basic_solver 21. }
    revert W_hb_sc_hb_to_I_NTid. basic_solver 21. }
  { rewrite cert_rfe; relsf; unionL.
    { rewrite (dom_rel_helper Grfe_E).
      unfold certG; ins; rewrite !seqA.
      rewrite I_in_cert_co_base at 1.
      sin_rewrite cert_co_I.
      revert COH CSC. unfold coherence, coh_sc, eco.
      ie_unfolder. basic_solver 21. }
    rewrite cert_co_alt'; relsf; unionL.
    2: { generalize non_I_new_rf. basic_solver 16. }
    rewrite new_rf_in_furr.
    rotate 1.
    arewrite (Gfurr \ Gsb ⊆ Gfurr).
    arewrite (Gfurr ⨾ Ghb ⨾ (sc ⨾ Ghb)^? ⊆ Gfurr).
    { generalize (furr_hb_sc_hb WF WF_SC ACYC_EXT). basic_solver 21. }
    generalize (eco_furr_irr WF WF_SC CSC COH).
    unfold eco. basic_solver 21. }
  { unfold fr; rewrite cert_co_alt'; unfold certG; ins.
    rewrite transp_union, transp_seq; relsf; unionL.
    { revert COH CSC. unfold coherence, coh_sc, eco, fr. ie_unfolder. basic_solver 21. }
    { rotate 1.
      arewrite (Gco ∩ cert_co ⊆ cert_co).
      rewrite (dom_r (wf_cert_coD)), !seqA.
      arewrite (⦗W⦘ ⨾ Ghb ⨾ (sc ⨾ Ghb)^? ⊆ Gfurr).
      { rewrite (furr_alt WF_SC). basic_solver 21. }
      unfold new_rf. basic_solver 21. }
    { rewrite !seqA. eapply cert_coherece_detour_helper. }
    rotate 1.
    arewrite (⦗E ∩₁ W ∩₁ Tid_ thread \₁ I⦘ ⊆ ⦗W⦘) by basic_solver.
    arewrite (⦗W⦘ ⨾ Ghb ⨾ (sc ⨾ Ghb)^? ⊆ Gfurr).
    { rewrite (furr_alt WF_SC). basic_solver 21. }
    unfold new_rf. basic_solver 21. }
  rewrite cert_rfe; relsf; unionL.
  { unfold fr; unfold certG; ins.
    rewrite transp_union, transp_seq; relsf; unionL.
    { rewrite (dom_rel_helper Grfe_E), !seqA.
      rewrite I_in_cert_co_base at 1.
      sin_rewrite cert_co_I.
      revert COH CSC. unfold coherence, coh_sc, eco, fr. ie_unfolder.
      basic_solver 21. }
    arewrite (Grfe ⨾ ⦗D⦘ ⊆ Grf) by ie_unfolder; basic_solver.
    rotate 1.
    arewrite (Grf ⨾ Ghb ⨾ (sc ⨾ Ghb)^? ⊆ Gfurr).
    { rewrite (furr_alt WF_SC). rewrite (dom_l (wf_rfD WF)). basic_solver 21. }
    unfold new_rf. basic_solver 21. }
  unfold fr; unfold certG; ins.
  rewrite transp_union, transp_seq; relsf; unionL.
  all: rewrite cert_co_alt'; relsf; unionL.
  2,4: generalize non_I_new_rf; basic_solver 16.
  { rewrite new_rf_in_furr.
    rotate 1.
    arewrite (Gfurr \ Gsb ⊆ Gfurr).
    arewrite (Gfurr ⨾ Ghb ⨾ (sc ⨾ Ghb)^? ⊆ Gfurr).
    { generalize (furr_hb_sc_hb WF WF_SC ACYC_EXT). basic_solver 21. }
    generalize (eco_furr_irr WF WF_SC CSC COH).
    unfold eco, fr. basic_solver 21. }
  rewrite new_rf_in_furr at 2.
  rotate 1.
  arewrite (Gfurr \ Gsb ⊆ Gfurr).
  arewrite (Gfurr ⨾ Ghb ⨾ (sc ⨾ Ghb)^? ⊆ Gfurr).
  { generalize (furr_hb_sc_hb WF WF_SC ACYC_EXT). basic_solver 21. }
  unfold new_rf. basic_solver 21.
Qed.

Lemma cert_coherence : coherence certG.
Proof using All.
red; generalize coh_helper; basic_solver 12.
Qed.

Lemma cert_coh_sc : coh_sc certG sc.
Proof using All.
red; case_refl _.
- rewrite cert_hb.
  rewrite (wf_scD WF_SC); rotate 2.
  sin_rewrite (f_sc_hb_f_sc_in_ar sc WF).
  unfolder; ins; desc.
  eapply ACYC_EXT.
  eapply t_trans; [edone| apply t_step].
  by apply sc_in_ar.
- generalize coh_helper; basic_solver 21.
Qed.

(* TODO: move up *)
Lemma W_ex_in_cert_co_base : GW_ex ⊆₁ cert_co_base.
Proof using. unfold cert_co_base. clear. basic_solver. Qed.

Lemma cert_rmw_atomicity : rmw_atomicity certG.
Proof using WF WF_SC TCCOH AT COH COMP_NTID E_to_S G IT_new_co I_in_S S ST_in_E S_in_W 
      TCCOH_rst_new_T W_hb_sc_hb_to_I_NTid detour_E S_I_in_W_ex.
  clear OLD_VAL NEW_VAL SAME ACYC_EXT CSC COMP_ACQ.
  generalize (atomicity_alt WF (coherence_sc_per_loc COH) AT).
  intro AT'; clear AT.

  red; ins; cut (irreflexive (Cfr ⨾ (cert_co \ Gsb) ⨾ Grmw^{-1})).
  { basic_solver 12. }
  rewrite (rmw_W_ex), !transp_seq, !transp_eqv_rel.
  unfold cert_co.
  rotate 1.
  unfold fr; ins; rewrite transp_union.
  rewrite (dom_rel_helper (dom_rmw_in_D)).
  rewrite (dom_r (wf_new_rfE)).
  rewrite !transp_seq, !transp_eqv_rel, !seqA.
  relsf; unionL; [| basic_solver].
  unfold cert_co.

  arewrite ((new_co G cert_co_base 
                    (E ∩₁ W ∩₁ Tid_ thread) \ Gsb) ⨾ ⦗GW_ex⦘ ⊆
            (new_co G cert_co_base
                    (E ∩₁ W ∩₁ Tid_ thread) ∩ Gco \ Gsb) ⨾ ⦗GW_ex⦘).
  { cut (new_co G cert_co_base (E ∩₁ W ∩₁ Tid_ thread) ⨾ ⦗GW_ex⦘ ⊆ Gco).
    { basic_solver 21. }
    rewrite W_ex_in_cert_co_base.
    rewrite (new_co_I IST_new_co); try apply WF.
    clear. basic_solver. }

  rewrite (new_co_in IST_new_co) at 1; try apply WF.
  relsf; unionL.
  1,2: generalize (co_trans WF); revert AT'; unfold fr; basic_solver 12.

  assert (cert_co_base \₁ E ∩₁ W ∩₁ Tid_ thread ⊆₁ I \₁ Tid_ thread) as ISTN.
  { rewrite cert_co_base_alt.
    rewrite I_eq_EW_I at 1.
    rewrite W_ex_eq_EW_W_ex at 1.
    intros x [[AA|AA] BB].
    { split; [by apply AA|].
      intros HH. apply BB. split; auto. by apply AA. }
    exfalso. apply BB. generalize AA. clear. basic_solver. }

  remember (new_co G cert_co_base (E ∩₁ W ∩₁ Tid_ thread)) as new.
  rewrite !seqA.
  arewrite (⦗E ∩₁ W ∩₁ Tid_ thread \₁ cert_co_base⦘
              ⨾ (new ∩ Gco \ Gsb) ⨾ ⦗GW_ex⦘ ⊆
            ⦗E ∩₁ W ∩₁ Tid_ thread \₁ cert_co_base⦘
              ⨾ new ⨾ ⦗GW_ex \₁ E ∩₁ W ∩₁ Tid_ thread⦘).
  { unfolder; ins; desf; splits; eauto.
    intros [[EY WY] TT].
    eapply same_thread in TT; desf; eauto.
    2: { hahn_rewrite (no_co_to_init WF (coherence_sc_per_loc COH)) in H3.
         unfolder in H3; desf. }
    destruct TT; desf; try subst z2; eauto.
    { apply co_irr in H3; auto. }
    eapply COH. eexists. splits; [apply sb_in_hb | right; apply co_in_eco]; edone. }

  rewrite W_ex_in_cert_co_base.
  subst new.

  rewrite (inter_inclusion
             (@T_I_new_co_I_T G cert_co_base 
                              (E ∩₁ W ∩₁ Tid_ thread) (co_trans WF))).

  rewrite (inter_eq (wf_rfD WF)), (inter_eq (wf_rfE WF)),
  (inter_inclusion (wf_rfl WF)), (inter_inclusion (wf_rmwl WF)),
  (inter_inclusion (wf_col WF)).
  unfolder; ins; desc. subst z0 z3.
  assert (Gsame_loc z1 z4) by (unfold same_loc in *; congruence).
  assert (K: Gco z4 z1 \/ Gco z1 z4).
  { eapply WF; try basic_solver 2.
    intro; subst z1; eauto. }
  destruct K.
  2: revert AT'; unfold fr; basic_solver 12.
  eapply (new_co_irr IST_new_co); try apply WF.
  eapply (new_co_trans IST_new_co); try apply WF.
  apply H3.
  apply new_co_helper; [apply WF| apply WF| basic_solver 12].
Qed.

(******************************************************************************)
(** **   *)
(******************************************************************************)


Lemma cert_ppo_D : Cppo ⨾ ⦗ D ⦘ ⊆ Gppo.
Proof using E_to_S Grfe_E SAME S_in_W TCCOH WF WF_SC.
remember (Gdata ∪ Gctrl ∪ Gaddr ⨾ Gsb^? ∪ ⦗GR_ex⦘ ⨾ Gsb ∪ Grmw_dep) as X.

unfold ppo; ins.
arewrite (Cppo ⊆ ⦗R⦘ ⨾ (X ∪ Crfi)⁺ ⨾ ⦗W⦘).
{ unfold ppo; rewrite cert_R, cert_W, cert_sb, cert_R_ex.
rewrite HeqX; hahn_frame; apply inclusion_t_t; basic_solver 12. }
arewrite (Gppo ≡ ⦗R⦘ ⨾ (X ∪ Grfi)⁺ ⨾ ⦗W⦘).
by unfold ppo; rewrite HeqX; split; hahn_frame; apply inclusion_t_t; basic_solver 12.
arewrite (⦗W⦘ ⨾ ⦗D⦘ ⊆ ⦗D⦘ ⨾ ⦗W⦘) by basic_solver.
hahn_frame.
rewrite path_union; relsf; unionL.
generalize inclusion_t_t; basic_solver.
rewrite !seqA.

assert (X_D_helper: dom_rel (X ⨾ ⦗D⦘) ⊆₁ D).
{ rewrite HeqX.
  relsf; unionL; splits.
  apply dom_data_D.
  rewrite (dom_rel_helper dom_ctrl_in_D); basic_solver.
  rewrite (dom_rel_helper dom_addr_in_D); basic_solver.
  rewrite (dom_l (@wf_sbE G)); generalize (Rex_in_D); basic_solver.
  rewrite (dom_rel_helper dom_frmw_in_D); basic_solver. }

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
Proof using E_to_S Grfe_E SAME S_in_W TCCOH WF WF_SC.
rewrite C_in_D, I_in_D; relsf.
apply cert_ppo_D.
Qed.

Lemma cert_detour_D : Cdetour ⨾ ⦗ D ⦘ ⊆ ⦗ I ⦘ ⨾ Gdetour.
Proof using ACYC_EXT COH CSC Grfe_E IT_new_co RPPO_S ST_in_E S_in_W TCCOH WF WF_SC
      detour_Acq_E detour_E.
  enough (Cdetour ⨾ ⦗ D ⦘ ⊆ Gdetour).
  { arewrite (⦗D⦘ ⊆ ⦗D⦘ ⨾ ⦗D⦘) by basic_solver.
    sin_rewrite H.
    rewrite (dom_rel_helper dom_detour_D).
    clear. basic_solver. }
  unfold detour, Execution.coe.
  rewrite cert_sb.
  rewrite <- seq_eqv_inter_lr, !seqA.
  rewrite cert_rfe_D.
  rewrite I_in_cert_co_base.
  seq_rewrite <- seq_eqv_minus_lr.
  rewrite cert_co_I.
  clear. basic_solver 21.
Qed.

Lemma cert_detour_R_Acq_sb_D : Cdetour ⨾ ⦗R∩₁Acq⦘ ⨾ Gsb ⨾ ⦗ D ⦘ ⊆ 
  ⦗ I ⦘ ⨾ Gdetour ⨾ ⦗R∩₁Acq⦘ ⨾ Gsb.
Proof using ACYC_EXT COH COMP_ACQ CSC Grfe_E IT_new_co NEW_VAL OLD_VAL RPPO_S SAME
      ST_in_E S_in_W TCCOH WF WF_SC detour_Acq_E detour_E.
  rewrite (detour_to_codom_rfe WF_cert), !seqA.
  rewrite cert_rfe.
  rewrite codom_union, id_union; relsf; unionL.
  arewrite (⦗codom_rel (⦗I⦘ ⨾ Grfe ⨾ ⦗D⦘)⦘ ⊆ ⦗D⦘) by basic_solver.
  sin_rewrite cert_detour_D; basic_solver 40.
  unfolder; ins; desf; exfalso.
  generalize new_rfe_Acq. basic_solver 21.
Qed.

(* TODO: move *)
Lemma W_rel_sb_loc_W_CI :
 (⦗W ∩₁ Rel⦘ ⨾ Gsb ∩ Gsame_loc ⨾ ⦗W⦘) ⨾ ⦗C ∪₁ I⦘ ⊆
⦗C ∪₁ I⦘ ⨾ (⦗W ∩₁ Rel⦘ ⨾ Gsb ∩ Gsame_loc ⨾ ⦗W⦘).
Proof using TCCOH.
  (* case_refl _; [basic_solver|]. *)
  rewrite !seqA.
  arewrite (⦗W⦘ ⨾ ⦗C ∪₁ I⦘ ⊆ ⦗W⦘ ⨾ ⦗I⦘).
  { generalize (w_covered_issued TCCOH). basic_solver. }
  generalize (dom_W_Rel_sb_loc_I_in_C TCCOH). basic_solver 12.
Qed.

(* TODO: move *)
Lemma sb_W_rel_CI :
 (Gsb ⨾ ⦗W ∩₁ Rel⦘) ⨾ ⦗C ∪₁ I⦘ ⊆ ⦗C ∪₁ I⦘ ⨾ (Gsb ⨾ ⦗W ∩₁ Rel⦘).
Proof using TCCOH RELCOV.
  generalize RELCOV, (dom_sb_covered TCCOH).
  basic_solver 12.
Qed.

Lemma E_ntid_in_D : E ∩₁ NTid_ thread ⊆₁ D.
Proof using. unfold D. basic_solver 10. Qed.

(* TODO: introduce a separate file w/ definition of D and its properties. *)
Lemma dom_W_ex_acq_sb_W_D_in_CI :
  dom_rel (⦗GW_ex_acq⦘ ⨾ Gsb ⨾ ⦗W⦘ ⨾ ⦗D⦘) ⊆₁ C ∪₁ I.
Proof using All.
  assert (dom_rel (⦗GW_ex_acq⦘ ⨾ Gsb ⨾ ⦗I⦘) ⊆₁ I) as AA.
  { arewrite (⦗I⦘ ⊆ ⦗W⦘ ⨾ ⦗I⦘).
    { generalize (issuedW TCCOH). basic_solver. }
    arewrite (⦗GW_ex_acq⦘ ⨾ Gsb ⨾ ⦗W⦘ ⊆ ⦗W⦘ ⨾ Gar).
    2: by apply ar_I_in_I.
    arewrite (⦗GW_ex_acq⦘ ⊆ ⦗W⦘ ⨾ ⦗GW_ex_acq⦘).
    { generalize (W_ex_in_W WF). basic_solver. }
      by rewrite w_ex_acq_sb_w_in_ar. }
  unfold D at 1. rewrite !id_union, !seq_union_r, !dom_union.
  unionL.
  { unionR left.
    generalize (dom_sb_covered TCCOH). basic_solver. }
  { unionR right. arewrite_id ⦗W⦘. by rewrite seq_id_l. }
  { arewrite (⦗GW_ex_acq⦘ ⊆ ⦗GW_ex_acq⦘ ⨾ ⦗set_compl is_init⦘).
    { generalize W_ex_acq_not_init. basic_solver. }
    arewrite_id ⦗W⦘. rewrite seq_id_l.
    rewrite (dom_rel_helper (@E_ntid_sb_prcl G thread)).
    arewrite (GW_ex_acq ⊆₁ W).
    { generalize WF.(W_ex_in_W). basic_solver. }
    rewrite !dom_eqv1. unionR right.
    rewrite <- !set_interA.
    arewrite (W ∩₁ E ⊆₁ E ∩₁ W) by basic_solver.
    rewrite <- IT_new_co. basic_solver. }
  { rewrite <- !seqA. rewrite dom_rel_eqv_dom_rel.
    rewrite !seqA.
    arewrite (Gsb ⨾ ⦗W⦘ ⨾ Grfi^? ⨾ Gppo ⊆ Gsb).
    2: by unionR right. 
    arewrite (Grfi ⊆ Gsb).
    rewrite WF.(ppo_in_sb).
    generalize (@sb_trans G). basic_solver. }
  { unionR right. 
    rewrite <- !seqA. rewrite dom_rel_eqv_dom_rel.
    rewrite !seqA.
    arewrite (Gsb ⨾ ⦗W⦘ ⨾ (Gdata ∪ Grfi)＊ ⨾ Grppo ⊆ Gsb).
    2: by apply W_ex_acq_sb_S.
    arewrite (Grfi ⊆ Gsb).
    rewrite WF.(data_in_sb).
    rewrite WF.(rppo_in_sb).
    rewrite unionK.
    rewrite rt_of_trans.
    all: generalize (@sb_trans G); basic_solver. }
  { rewrite (dom_r WF.(wf_rfiD)).
    rewrite <- !seqA. rewrite codom_eqv1.
    clear. type_solver 20. }
  clear. type_solver 20.
Qed.

Lemma cert_ar_int_I : Car_int⁺ ⨾ ⦗ C ∪₁ I ⦘ ⊆ ⦗ D ∪₁ R ∩₁ Acq ⦘ ⨾ Gar_int⁺.
Proof using All.
  rewrite (ct_ar_int_alt WF_cert).
  2: by apply (coherence_sc_per_loc cert_coherence).
  rewrite cert_R, cert_Acq, cert_sb, cert_W_ex_acq, cert_W.
  rewrite cert_same_loc, cert_Rel, cert_AcqRel, cert_F.
  relsf; unionL.
  { unfold ar_int, bob, fwbob.
    case_refl Gsb.
    { rewrite (dom_l (@wf_sbE G)) at 1.
      generalize E_F_AcqRel_in_C, C_in_D.
      rewrite <- ct_step. basic_solver 12. }
    rewrite (dom_l (@wf_sbE G)) at 2.
    generalize E_F_AcqRel_in_C, (dom_sb_covered TCCOH), C_in_D.
    rewrite ct_begin, <- inclusion_t_rt, <- ct_step.
    basic_solver 21. }
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
    basic_solver 21. }
  { unfold ar_int, bob, fwbob.
    rewrite W_rel_sb_loc_W_CI.
    generalize C_in_D, I_in_D.
    rewrite <- ct_step.
    basic_solver 12. }
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
    unfold ar_int. basic_solver. }
  rewrite !seqA.
  rewrite (cr_helper W_rel_sb_loc_W_CI).
  arewrite ((⦗W ∩₁ Rel⦘ ⨾ Gsb ∩ Gsame_loc ⨾ ⦗W⦘)^?  ⊆ Gar_int^?) at 2.
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

Lemma  cert_acyc_ext_helper : (sc ∪ certG.(rfe))⁺ ⊆ sc ∪ certG.(rfe).
Proof using All.
rewrite path_union.
generalize (sc_trans WF_SC); ins; relsf; unionL; [basic_solver|].
rewrite crE at 2; relsf; unionL.
-
arewrite (sc^? ⨾ rfe certG ⊆ rfe certG ).
rewrite crE; relsf; unionL; [basic_solver|].
rewrite (dom_l (wf_rfeD WF_cert)), cert_W.
rewrite (dom_r (wf_scD WF_SC)) at 1.
type_solver.

rewrite ct_begin, rtE; relsf; unionL; [basic_solver|].
rewrite ct_begin.
rewrite (dom_l (wf_rfeD WF_cert)).
rewrite (dom_r (wf_rfeD WF_cert)).
type_solver.

-
rewrite (dom_r (wf_rfeD WF_cert)), cert_R.
rewrite <- !seqA.
rewrite inclusion_ct_seq_eqv_r, !seqA.
rewrite (dom_l (wf_scD WF_SC)) at 2.
type_solver.

Qed.


Lemma cert_acyc_ext : acyc_ext certG sc.
Proof using All.
red; unfold imm_s.ar.
rewrite unionC.
apply acyclic_union1.
- rewrite (ar_int_in_sb WF_cert); apply sb_acyclic.
- red; rewrite cert_acyc_ext_helper; unionL.
apply WF_SC.
arewrite (certG.(rfe) ⊆ certG.(rf)).
apply rf_irr, WF_cert.
- 
rewrite cert_acyc_ext_helper.
arewrite ((sc ∪ rfe certG) ⊆ ⦗ C ∪₁ I ⦘ ⨾ (sc ∪ rfe certG)).
{ unionL.
- rewrite (dom_l (wf_scD WF_SC)) at 1.
rewrite (dom_l (wf_scE WF_SC)) at 1.
arewrite (Sc ⊆₁ Acq/Rel) by mode_solver.
generalize E_F_AcqRel_in_C; basic_solver 12.
- rewrite cert_rfe; basic_solver 12.
}
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


Lemma cert_imm_consistent : imm_consistent certG sc.
Proof using All.
red; splits; eauto using WF_SC_cert, cert_acyc_ext, cert_coh_sc, cert_complete, cert_coherence, cert_rmw_atomicity.
Qed.

(******************************************************************************)
(** **   *)
(******************************************************************************)

Lemma dom_fwbob_I : dom_rel (Gfwbob ⨾ ⦗C ∪₁ I⦘) ⊆₁ C ∪₁ I.
Proof using E_F_AcqRel_in_C E_to_S F_SB_S RELCOV S_in_W TCCOH.
unfold fwbob; relsf; unionL; splits.
- rewrite sb_W_rel_CI; basic_solver.
- rewrite W_rel_sb_loc_W_CI; basic_solver.
- rewrite (dom_r (@wf_sbE G)).
generalize dom_sb_F_AcqRel_in_CI. basic_solver 12.
- rewrite (dom_l (@wf_sbE G)).
generalize E_F_AcqRel_in_C; basic_solver 12.
Qed.

Lemma TCCOH_cert_old : tc_coherent_alt_old certG sc (mkTC (C ∪₁ (E ∩₁ NTid_ thread)) I).
Proof using All.
  assert (TCCOH1:= TCCOH_rst_new_T).
  apply (tc_coherent_implies_tc_coherent_alt WF WF_SC) in TCCOH1.
  destruct TCCOH1.
  constructor.
  all: try by ins.
  { ins; rewrite cert_W; done. }
  { rewrite rfi_union_rfe; relsf; unionL; splits; ins.
    rewrite (dom_l (wf_rfiD WF_cert)), cert_W.
    arewrite (Crfi ⊆ Gsb).
    generalize tc_sb_C, tc_W_C_in_I; basic_solver 21.
    rewrite cert_rfe; basic_solver 21. }
  { ins; rewrite cert_W; done. }
  { ins; rewrite cert_fwbob; done. }
  { relsf; unionL; splits; simpls.
    3,4: rewrite cert_rfe; basic_solver.
    { rewrite I_in_D at 1.
      arewrite (⦗D⦘ ⊆ ⦗D⦘ ⨾ ⦗D⦘) by basic_solver.
      sin_rewrite cert_ppo_D.
      rewrite (dom_rel_helper dom_ppo_D).
      sin_rewrite cert_detour_D.
      basic_solver. }
    unfold bob; relsf; unionL; splits; simpls.
    { arewrite (⦗I⦘ ⊆ ⦗C ∪₁ I⦘) at 1.
      rewrite cert_fwbob.
      rewrite (dom_rel_helper dom_fwbob_I).
      rewrite C_in_D, I_in_D at 1; relsf.
      sin_rewrite cert_detour_D.
      basic_solver. }
    rewrite I_in_D at 1.
    rewrite !seqA.
    rewrite cert_sb.
    rewrite cert_R, cert_Acq.
    rewrite cert_detour_R_Acq_sb_D.
    basic_solver. }
  { ins; rewrite cert_W_ex_acq.
    rewrite cert_sb. eapply tc_W_ex_sb_I; eauto.
    apply tc_coherent_implies_tc_coherent_alt; eauto. }
  simpls.
  arewrite (Grmw ⨾ ⦗I⦘ ⊆ ⦗D⦘ ⨾ Grmw ⨾ ⦗I⦘).
  { apply dom_rel_helper.
    rewrite rmw_in_ppo; auto.
    rewrite I_in_D.
    apply dom_ppo_D. }
  sin_rewrite cert_rfi_D. rewrite !seqA.
  arewrite_id ⦗D⦘. rewrite !seq_id_l.
  arewrite (Grfi ⊆ Grf).
  eapply rfrmw_I_in_I; eauto.
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
  { ins; rewrite cert_W; done. }
  { rewrite rfi_union_rfe; relsf; unionL; splits; ins.
    rewrite (dom_l (wf_rfiD WF_cert)), cert_W.
    arewrite (Crfi ⊆ Gsb).
    generalize tc_sb_C, tc_W_C_in_I; basic_solver 21.
    rewrite cert_rfe; basic_solver 21. }
  { ins; rewrite cert_W; done. }
  { ins; rewrite cert_fwbob; done. }
  ins. apply dom_cert_ar_rfrmw_I.
Qed.

Lemma cert_detour_rfe_D : (Cdetour ∪ certG.(rfe)) ⨾ ⦗D⦘ ⊆ ⦗I⦘ ⨾ (Gdetour ∪ Grfe).
Proof using ACYC_EXT COH CSC Grfe_E IT_new_co RPPO_S ST_in_E S_in_W TCCOH WF WF_SC
      detour_Acq_E detour_E.
  rewrite seq_union_l.
  rewrite cert_detour_D, cert_rfe_D.
    by rewrite seq_union_r.
Qed.

Lemma dom_cert_detour_rfe_D : dom_rel ((Cdetour ∪ certG.(rfe)) ⨾ ⦗D⦘) ⊆₁ I.
Proof using ACYC_EXT COH CSC Grfe_E IT_new_co RPPO_S ST_in_E S_in_W TCCOH WF WF_SC
      detour_Acq_E detour_E.
  rewrite cert_detour_rfe_D.
  basic_solver.
Qed.

Lemma Crppo_in_rppo : rppo certG ⊆ Grppo.
Proof using SAME.
  unfold rppo.
  rewrite cert_sb, cert_R_ex, cert_W.
  unfold certG. simpls.
Qed.

Lemma dom_data_Crfi_D_in_D : dom_rel ((Gdata ∪ Crfi)＊ ⨾ ⦗D⦘) ⊆₁ D.
Proof using Grfe_E TCCOH WF WF_SC.
  unfolder. ins. desf.
  induction H.
  3: intuition.
  2: basic_solver.
  desf.
  { apply dom_data_D. basic_solver 10. }
  assert ((Crfi ⨾ ⦗D⦘) x y) as AA.
  { basic_solver 10. }
  apply cert_rfi_D in AA. unfolder in AA. desf.
Qed.

Lemma ETCCOH_cert (ST_in_W_ex : S ∩₁ Tid_ thread \₁ I ⊆₁ GW_ex)
      (ISTex_rf_I : (I ∪₁ S ∩₁ Tid_ thread) ∩₁ GW_ex ⊆₁ codom_rel (⦗I⦘ ⨾ Grf ⨾ Grmw))
      (DOM_SB_S_rf_I :
         dom_rel (⦗GW_ex⦘ ⨾ Gsb ⨾ ⦗I ∪₁ S ∩₁ Tid_ thread⦘) ∩₁ codom_rel (⦗I⦘ ⨾ Grf ⨾ Grmw)
                 ⊆₁ I ∪₁ S ∩₁ Tid_ thread) :
  etc_coherent certG sc (mkETC (mkTC (C ∪₁ (E ∩₁ NTid_ thread)) I)
                               (I ∪₁ S ∩₁ Tid_ thread)).
Proof using All.
  assert (I ∪₁ S ∩₁ Tid_ thread ⊆₁ S) as IST_in_S.
  { rewrite I_in_S. basic_solver. }
  assert ((Grf ⨾ ⦗D⦘ ∪ new_rf) ⨾ Grmw ≡ Grf ⨾ Grmw) as QQ.
  { rewrite (dom_rel_helper dom_rmw_in_D).
    rewrite wf_new_rfE. clear. basic_solver 10. }
  constructor.
  all: unfold eissued, ecovered; simpls.
  { apply TCCOH_cert. }
  { arewrite (I ∪₁ S ∩₁ Tid_ thread ⊆₁ E ∩₁ W).
    2: { unfold certG. unfold acts_set. basic_solver. }
    rewrite <- IST_new_co.
    rewrite IST_in_cert_co_base.
    basic_solver 10. }
  { eauto with hahn. }
  { rewrite cert_W_ex. generalize ST_in_W_ex.
    basic_solver. }
  { rewrite cert_F, cert_AcqRel, cert_sb, IST_in_S. by unionR left. }
  { rewrite cert_sb, cert_Acq, cert_R.
    unfolder. intros x [y [z [DRF [[RZ ACQZ] [SB SS]]]]].
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
    eapply dom_cert_detour_rfe_D. basic_solver 10. }
  { by rewrite cert_W_ex, cert_xacq, cert_sb, IST_in_S. }
  { unfold dom_sb_S_rfrmw. simpls. by rewrite QQ, cert_sb, cert_W_ex. }
  2: by rewrite QQ, cert_W_ex.
  rewrite Crppo_in_rppo.
  arewrite (Grppo ⨾ ⦗I ∪₁ S ∩₁ Tid_ thread⦘ ⊆
                  ⦗D⦘ ⨾ Grppo ⨾ ⦗I ∪₁ S ∩₁ Tid_ thread⦘).
  { apply dom_rel_helper.
    rewrite IST_in_S.
    apply dom_rppo_S_in_D. }
  arewrite ((Gdata ∪ Crfi)＊ ⨾ ⦗D⦘ ⊆ ⦗D⦘ ⨾ (Gdata ∪ Crfi)＊ ⨾ ⦗D⦘).
  { apply dom_rel_helper.
    apply dom_data_Crfi_D_in_D. }
  rewrite <- !seqA.
  do 4 rewrite AuxRel.dom_seq.
  apply dom_cert_detour_rfe_D.
Qed.

End CertExec.
