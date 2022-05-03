From hahn Require Import Hahn.

From imm Require Import Events.
From imm Require Import Execution.
From imm Require Import Execution_eco.
From imm Require Import imm_bob imm_s_ppo imm_s_hb imm_s.
From imm Require Import SubExecution.
From imm Require Import CombRelations.
From imm Require Import AuxRel2.

From imm Require Import TraversalConfig.
From imm Require Import TraversalConfigAlt.
Require Import ExtTraversalConfig ExtTraversalProperties.
Require Import AuxRel.

Set Implicit Arguments.
Remove Hints plus_n_O.

Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'NTid_' t" := (fun x => tid x <> t) (at level 1).

Section RestExec.

Variable Gf : execution.
Variable sc : relation actid.

Notation "'Init'" := (fun a => is_true (is_init a)).

Notation "'FE'" := (acts_set Gf).
(* Notation "'Facts'" := (acts Gf). *)
Notation "'Flab'" := (lab Gf).
Notation "'Fsb'" := (sb Gf).
Notation "'Frf'" := (rf Gf).
Notation "'Fco'" := (co Gf).
Notation "'Frmw'" := (rmw Gf).
Notation "'Fdata'" := (data Gf).
Notation "'Faddr'" := (addr Gf).
Notation "'Fctrl'" := (ctrl Gf).
Notation "'Fdeps'" := (deps Gf).
Notation "'Frmw_dep'" := (rmw_dep Gf).

Notation "'Ffre'" := (fre Gf).
Notation "'Frfe'" := (rfe Gf).
Notation "'Fcoe'" := (coe Gf).
Notation "'Frfi'" := (rfi Gf).
Notation "'Ffri'" := (fri Gf).
Notation "'Fcoi'" := (coi Gf).
Notation "'Ffr'" := (fr Gf).
Notation "'Feco'" := (eco Gf).
Notation "'Fdetour'" := (detour Gf).
Notation "'Fsw'" := (sw Gf).
Notation "'Frelease'" := (release Gf).
Notation "'Frs'" := (rs Gf).
Notation "'Fhb'" := (hb Gf).
Notation "'Fppo'" := (ppo Gf).
Notation "'Fbob'" := (bob Gf).
Notation "'Ffwbob'" := (fwbob Gf).
Notation "'Far'" := ((ar Gf) sc).
Notation "'Furr'" := ((urr Gf) sc).
Notation "'Fmsg_rel'" := ((msg_rel Gf) sc).

Notation "'Floc'" := (loc Flab).
Notation "'Fval'" := (val Flab).
Notation "'Fsame_loc'" := (same_loc Flab).

Notation "'FR'" := (fun a => is_true (is_r Flab a)).
Notation "'FW'" := (fun a => is_true (is_w Flab a)).
Notation "'FF'" := (fun a => is_true (is_f Flab a)).
Notation "'FR_ex'" := (fun a => is_true (R_ex Flab a)).
Notation "'FW_ex'" := (W_ex Gf).
Notation "'FW_ex_acq'" := (FW_ex ∩₁ (fun a => is_true (is_xacq Flab a))).

Notation "'FLoc_' l" := (fun x => Floc x = Some l) (at level 1).
Notation "'FW_' l" := (FW ∩₁ FLoc_ l) (at level 1).
Notation "'FR_' l" := (FR ∩₁ FLoc_ l) (at level 1).

Notation "'FPln'" := (fun a => is_true (is_only_pln Flab a)).
Notation "'FRlx'" := (fun a => is_true (is_rlx Flab a)).
Notation "'FRel'" := (fun a => is_true (is_rel Flab a)).
Notation "'FAcq'" := (fun a => is_true (is_acq Flab a)).
Notation "'FAcqrel'" := (fun a => is_true (is_acqrel Flab a)).
Notation "'FAcq/Rel'" := (fun a => is_true (is_ra Flab a)).
Notation "'FSc'" := (fun a => is_true (is_sc Flab a)).
Notation "'Fxacq'" := (fun a => is_true (is_xacq Flab a)).

Variable T : trav_config.
Variable S : actid -> Prop.

Notation "'I'" := (issued T).
Notation "'C'" := (covered T).

Variable thread : BinNums.positive.

Hypothesis WF : Wf Gf.
Hypothesis WF_SC : wf_sc Gf sc.
Hypothesis IMMCON : imm_consistent Gf sc.
Hypothesis RELCOV : FW ∩₁ FRel ∩₁ I ⊆₁ C.
Hypothesis RMWCOV : forall r w (RMW : Frmw r w), C r <-> C w.
Hypothesis ETCCOH : etc_coherent Gf sc (mkETC T S).

Local Lemma TCCOH : tc_coherent Gf sc T.
Proof using ETCCOH. apply ETCCOH. Qed.

Definition E0 :=  C ∪₁ I ∪₁ dom_rel (Fsb^? ⨾ ⦗Tid_ thread ∩₁ S⦘)
  ∪₁ dom_rel (Frmw ⨾ ⦗ NTid_ thread ∩₁ I ⦘).

Definition rstG := restrict Gf E0.
Definition rst_sc := ⦗ E0 ⦘ ⨾ sc ⨾ ⦗ E0 ⦘.

Notation "'E'" := (acts_set rstG).
(* Notation "'Gacts'" := (acts rstG). *)
Notation "'Glab'" := (lab rstG).
Notation "'Gsb'" := (sb rstG).
Notation "'Grf'" := (rf rstG).
Notation "'Gco'" := (co rstG).
Notation "'Grmw'" := (rmw rstG).
Notation "'Gdata'" := (data rstG).
Notation "'Gaddr'" := (addr rstG).
Notation "'Gctrl'" := (ctrl rstG).
Notation "'Gdeps'" := (deps rstG).
Notation "'Grmw_dep'" := (rmw_dep rstG).

Notation "'Gfre'" := (fre rstG).
Notation "'Grfe'" := (rfe rstG).
Notation "'Gcoe'" := (coe rstG).
Notation "'Grfi'" := (rfi rstG).
Notation "'Gfri'" := (fri rstG).
Notation "'Gcoi'" := (coi rstG).
Notation "'Gfr'" := (fr rstG).
Notation "'Geco'" := (eco rstG).
Notation "'Gdetour'" := (detour rstG).
Notation "'Gsw'" := (sw rstG).
Notation "'Grelease'" := (release rstG).
Notation "'Grs'" := (rs rstG).
Notation "'Ghb'" := (hb rstG).
Notation "'Gppo'" := (ppo rstG).
Notation "'Gbob'" := (bob rstG).
Notation "'Gfwbob'" := (fwbob rstG).
Notation "'Gar'" := ((ar rstG) rst_sc).
Notation "'Gurr'" := ((urr rstG) rst_sc).
Notation "'Gmsg_rel'" := ((msg_rel rstG) rst_sc).

Notation "'Gloc'" := (loc Glab).
Notation "'Gval'" := (val Glab).
Notation "'Gsame_loc'" := (same_loc Glab).

Notation "'R'" := (fun a => is_true (is_r Glab a)).
Notation "'W'" := (fun a => is_true (is_w Glab a)).
Notation "'F'" := (fun a => is_true (is_f Glab a)).
Notation "'GR_ex'" := (fun a => is_true (R_ex Glab a)).
Notation "'GW_ex'" := (W_ex rstG).
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

Lemma E0_in_Gf : E0 ⊆₁ FE.
Proof using WF ETCCOH.
  unfold E0.
  rewrite coveredE, issuedE; try apply TCCOH.
  rewrite (etc_S_in_E ETCCOH).
  rewrite (dom_l (@wf_sbE Gf)).
  rewrite (dom_l (wf_rmwE WF)).
  basic_solver.
Qed.

Lemma E_E0 : E ≡₁ E0.
Proof using WF ETCCOH. by apply restrict_E, E0_in_Gf. Qed.

Lemma tid_S_in_E : Tid_ thread ∩₁ S ⊆₁ E.
Proof using WF ETCCOH.
  rewrite E_E0; unfold E0. basic_solver 10.
Qed.

Lemma I_in_E : I ⊆₁ E.
Proof using WF ETCCOH.
  rewrite E_E0; unfold E0; basic_solver.
Qed.

Lemma C_in_E : C ⊆₁ E.
Proof using WF ETCCOH.
  rewrite E_E0; unfold E0; basic_solver.
Qed.

Lemma dom_sb_TS_in_E : dom_rel (Fsb^? ⨾ ⦗Tid_ thread ∩₁ S⦘) ⊆₁ E.
Proof using WF ETCCOH.
  rewrite E_E0; unfold E0. basic_solver 10.
Qed.

Lemma ST_in_E : S ∩₁ Tid_ thread ⊆₁ E.
Proof using WF ETCCOH.
  rewrite E_E0; unfold E0. basic_solver 10.
Qed.

Lemma SUB: sub_execution Gf rstG sc rst_sc.
Proof using WF ETCCOH.
  eapply restrict_sub. done. eapply E0_in_Gf.
Qed.

Lemma INIT : Init ∩₁ FE ⊆₁ E.
Proof using WF ETCCOH.
  rewrite (init_issued WF TCCOH); rewrite E_E0; unfold E0; basic_solver.
Qed.

Lemma rstWF : Wf rstG.
Proof using WF ETCCOH.
apply (sub_WF INIT WF SUB).
Qed.

(* Lemma Wex_rfi_rmw_E :  dom_rel (⦗FW_ex⦘ ⨾ Frfi ⨾ Frmw ⨾ ⦗E⦘) ⊆₁ S. *)
(* Proof using WF ETCCOH. *)
(*   assert (FW_ex ∩₁ dom_rel (Fsb ⨾ ⦗S⦘) ⊆₁ S) as SS. *)
(*   { rewrite <- dom_eqv1. *)
(*     eapply etc_po_S with (T:=mkETC T S); eauto. } *)
(*   assert (FW_ex ∩₁ dom_rel (Fsb^? ⨾ ⦗S⦘) ⊆₁ S) as SS'. *)
(*   { rewrite crE, seq_union_l, seq_id_l, dom_union, set_inter_union_r.  *)
(*     unionL; auto. basic_solver. } *)
(*   assert (FW_ex ∩₁ dom_rel (Fsb ⨾ ⦗I⦘) ⊆₁ S) as IS. *)
(*   { rewrite etc_I_in_S with (T:=mkETC T S); eauto; simpls. } *)

(*   rewrite E_E0; unfold E0. *)
(*   rewrite !id_union; relsf; unionL; splits. *)
(*   { rewrite (rmw_in_sb WF) at 1. *)
(*     rewrite <- etc_I_in_S with (T:=mkETC T S); eauto. *)
(*     unfold eissued; simpls. *)
(*     generalize TCCOH, dom_sb_covered, dom_rf_covered; ie_unfolder; basic_solver 21. } *)
(*   { rewrite (rmw_in_sb WF) at 1 2. *)
(*     arewrite (Frfi ⊆ Fsb) at 1. *)
(*     generalize (@sb_trans Gf); ins; relsf. } *)
(*   { arewrite (dom_rel (Frfi ⨾ Frmw ⨾ ⦗dom_rel (Fsb^? ⨾ ⦗Tid_ thread ∩₁ S⦘)⦘) ⊆₁ *)
(*               dom_rel (Fsb^? ⨾ ⦗S⦘)); [|done]. *)
(*     rewrite (rmw_in_sb WF) at 1. *)
(*     arewrite (Frfi ⊆ Fsb) at 1. *)
(*     generalize (@sb_trans Gf). *)
(*     basic_solver 40. } *)
(*   sin_rewrite set_minus_remove_l. *)
(*   2: reflexivity. *)
(*   arewrite (dom_rel (Frfi ⨾ Frmw ⨾ ⦗dom_rel (Frmw ⨾ ⦗NTid_ thread ∩₁ I⦘)⦘) ⊆₁ *)
(*             dom_rel (Fsb ⨾ ⦗I⦘)); [|done]. *)
(*   rewrite (rmw_in_sb WF) at 1 2. *)
(*   arewrite (Frfi ⊆ Fsb) at 1. *)
(*   generalize (@sb_trans Gf). *)
(*   basic_solver 40. *)
(* Qed. *)

Lemma rfe_rmw_I :dom_rel (Frfe ⨾ Frmw ⨾ ⦗I⦘) ⊆₁ I.
Proof using WF ETCCOH.
  arewrite (Frfe ⊆ Frf).
  eapply rfrmw_I_in_I; eauto. apply TCCOH.
Qed.

Lemma rmw_E_rfe :  dom_rel (Frmw ⨾ ⦗E⦘) ∩₁ codom_rel Frfe ⊆₁ E.
Proof using WF ETCCOH.
  rewrite E_E0; unfold E0.
  rewrite !id_union; relsf; unionL; splits.
  { rewrite (rmw_in_sb WF) at 1.
    generalize TCCOH, dom_sb_covered, dom_rf_covered.
    ie_unfolder; basic_solver 21. }
  { arewrite (⦗I⦘ ⊆ ⦗Tid_ thread ∩₁ I⦘ ∪ ⦗NTid_ thread ∩₁ I⦘).
    { by unfolder; ins; desf; tauto. }
    relsf; unionL; splits.
    { rewrite (rmw_in_sb WF) at 1. rewrite (etc_I_in_S ETCCOH) at 1. basic_solver 20. }
    unionR right.
    unfolder; ins; desf; splits; eauto. }
  { rewrite dom_rel_eqv_dom_rel.
    rewrite (rmw_in_sb WF) at 1.
    generalize (@sb_trans Gf); ins; relsf.
    basic_solver 12. }
  rewrite (dom_r (wf_rmwD WF)) at 1.
  rewrite (dom_l (wf_rmwD WF)) at 2.
  clear. type_solver.
Qed.

(* Lemma rfe_rmw_E : dom_rel (Frfe ⨾ Frmw ⨾ ⦗E⦘) ⊆₁ E. *)
(* Proof using WF ETCCOH. *)
(*   rewrite E_E0 at 1; unfold E0. *)
(*   rewrite !id_union; relsf; unionL; splits. *)
(*   4: { rewrite (dom_r (wf_rmwD WF)) at 1. *)
(*        rewrite (dom_l (wf_rmwD WF)) at 2. *)
(*        clear. type_solver. } *)
(*   { rewrite <- I_in_E. *)
(*     rewrite (rmw_in_sb WF) at 1. *)
(*     rewrite (dom_rel_helper (dom_sb_covered TCCOH)). *)
(*     arewrite (Frfe ⊆ Frf). rewrite <- !seqA. *)
(*     rewrite (dom_rel_helper (dom_rf_covered WF TCCOH)). *)
(*     clear. basic_solver. } *)
(*   { rewrite <- I_in_E. *)
(*     arewrite (Frfe ⊆ Frf). *)
(*     eapply rfrmw_I_in_I; eauto. apply TCCOH. } *)
(*   rewrite <- I_in_E. *)
(*   rewrite <- seqA, dom_rel_eqv_dom_rel, !seqA. *)
(*   arewrite (⦗Tid_ thread ∩₁ S⦘ ⊆ ⦗FW⦘ ⨾ ⦗S⦘). *)
(*   { arewrite (S ⊆₁ FW ∩₁ S) at 1. *)
(*     2: clear; basic_solver. *)
(*     apply set_subset_inter_r. split; [|done]. apply (reservedW WF ETCCOH). } *)
(*   sin_rewrite (rmw_sb_cr_W_in_rppo WF). *)
(*   etransitivity. *)
(*   2: by apply (etc_rppo_S ETCCOH). *)
(*   rewrite <- inclusion_id_rt. clear. basic_solver 20. *)
(* Qed. *)

Lemma rmw_E_rfi :  dom_rel (Frmw ⨾ ⦗E⦘) ∩₁ codom_rel Frfi ⊆₁ E.
Proof using WF ETCCOH.
rewrite E_E0; unfold E0.
rewrite !id_union; relsf; unionL; splits.
- rewrite (rmw_in_sb WF) at 1.
  generalize TCCOH, dom_sb_covered, dom_rf_covered; ie_unfolder; basic_solver 21.
- arewrite (⦗I⦘ ⊆ ⦗Tid_ thread ∩₁ I⦘ ∪ ⦗NTid_ thread ∩₁ I⦘).
  by unfolder; ins; desf; tauto.
  relsf; unionL; splits.
  { rewrite (rmw_in_sb WF) at 1. rewrite (etc_I_in_S ETCCOH) at 1. basic_solver 20. }
  unionR right.
  unfolder; ins; desf; splits; eauto.
- rewrite dom_rel_eqv_dom_rel.
  rewrite (rmw_in_sb WF) at 1.
  generalize (@sb_trans Gf); ins; relsf.
  basic_solver 12.
- rewrite (dom_r (wf_rmwD WF)) at 1.
  rewrite (dom_l (wf_rmwD WF)) at 2.
  clear. type_solver.
Qed.

Lemma dom_Frmw_I_in_E : dom_rel (Frmw ⨾ ⦗I⦘) ⊆₁ E.
Proof using WF ETCCOH.
  rewrite E_E0. unfold E0.
  arewrite (I ⊆₁ I ∩₁ (Tid_ thread ∪₁ NTid_ thread)) at 1.
  { unfolder. ins. tauto. }
  rewrite set_inter_union_r, id_union.
  rewrite !seq_union_r, dom_union.
  unionL.
  { unionR left -> right.
    rewrite <- (etc_I_in_S ETCCOH). unfold eissued; simpls.
    rewrite (rmw_in_sb WF). basic_solver 10. }
  unionR right.
  unfolder. ins. desf. splits; eauto.
Qed.

Lemma rt_rf_rmw_I :
  (Frf ⨾ Frmw)＊ ⨾ ⦗I⦘ ⊆ (Frfi ⨾  Frmw)^? ⨾ ⦗I⦘ ⨾ (⦗E⦘ ⨾ Frf ⨾ ⦗E⦘ ⨾ Frmw ⨾ ⦗E⦘)＊ ⨾ ⦗E⦘ ⨾ ⦗I⦘.
Proof using WF ETCCOH.
  rewrite rt_begin, !seqA.
  rewrite !seq_union_l, seq_id_l.
  unionL.
  { generalize I_in_E. basic_solver 12. }
  rewrite rmw_W_ex at 1 2; rewrite !seqA.
  rewrite <- !(seqA Frf Frmw).
  seq_rewrite <- rt_seq_swap.
  arewrite_id ⦗FW_ex⦘ at 2; rewrite seq_id_l.
  apply rt_ind_left with (P:= fun r => Frf ⨾ Frmw ⨾ r ⨾ ⦗I⦘).
  { eauto with hahn. }
  { rewrite seq_id_l.
    rewrite rfi_union_rfe at 1. rewrite !seq_union_l.
    unionL.
    { rewrite <- inclusion_id_rt, seq_id_l.
      arewrite (⦗I⦘ ⊆ ⦗I⦘ ⨾ ⦗E⦘ ⨾ ⦗I⦘) at 1.
      { generalize I_in_E. basic_solver. }
      do 3 hahn_frame_r.
      basic_solver. }
    rewrite <- inclusion_t_rt, <- ct_step.
    rewrite <- inclusion_id_cr. rewrite seq_id_l, !seqA.
    rewrite (dom_rel_helper_in rfe_rmw_I).
    generalize I_in_E rfe_rmw_I rmw_E_rfe; ie_unfolder; basic_solver 80. }
  intros k H.
  rewrite !seqA, H.
  arewrite (⦗FW_ex⦘ ⨾ (Frfi ⨾ Frmw)^? ⨾ ⦗I⦘ ⊆ ⦗I⦘ ⨾ ⦗FW_ex⦘ ⨾ (Frfi ⨾ Frmw)^? ⨾ ⦗I⦘).
  { eapply dom_rel_helper_in.
    rewrite crE; relsf; unionL; splits; [basic_solver 12|].
    arewrite (Frfi ⊆ Frf).
    rewrite rfrmw_I_in_I; eauto.
    { basic_solver. }
      by apply ETCCOH. }

  arewrite (⦗I⦘ ⊆ ⦗I⦘ ⨾ ⦗I⦘) at 2.
  { basic_solver. }
  rewrite I_in_E at 2.
  arewrite (⦗I⦘ ⨾ ⦗FW_ex⦘ ⨾ (Frfi ⨾ Frmw)^? ⨾ ⦗E⦘ ⊆ ⦗I⦘ ⨾ ⦗E⦘ ⨾ (⦗E⦘ ⨾ Frf ⨾ ⦗E⦘ ⨾ Frmw ⨾ ⦗E⦘ )^?).
  { generalize I_in_E rmw_E_rfi; ie_unfolder; basic_solver 80. }
  relsf; rewrite rfi_union_rfe at 1; relsf.
  remember (⦗E⦘ ⨾ Frf ⨾ ⦗E⦘ ⨾ Frmw ⨾ ⦗E⦘) as X.

  arewrite_id ⦗I⦘ at 5. arewrite_id ⦗I⦘ at 2. rewrite !seq_id_l.
  relsf.
  unionL; [basic_solver 40|].

  arewrite (Frfe ⨾ Frmw ⨾ ⦗I⦘ ⊆ ⦗I⦘ ⨾ Frfe ⨾ Frmw ⨾ ⦗I⦘).
  { generalize rfe_rmw_I; basic_solver 12. }
  arewrite (Frfe ⨾ Frmw ⨾ ⦗I⦘ ⨾ ⦗E⦘ ⊆ ⦗E⦘ ⨾ (⦗E⦘ ⨾ Frf ⨾ ⦗E⦘ ⨾ Frmw ⨾ ⦗E⦘)^?).
  2:{ subst. relsf. remember (⦗E⦘ ⨾ Frf ⨾ ⦗E⦘ ⨾ Frmw ⨾ ⦗E⦘) as X. basic_solver 21. }
  rewrite crE. rewrite seq_union_r. unionR right. 
  hahn_frame_r. rewrite (dom_rel_helper rfe_rmw_I).
  rewrite I_in_E at 1.
  unfold rfe.
  unfolder. ins. desf. splits; auto.
  eexists. splits; eauto. eexists.
  splits; eauto.
  apply rmw_E_rfe. unfold rfe. unfolder. splits; eauto.
  do 2 eexists. splits; eauto. by apply I_in_E.
Qed.

Lemma release_I : Frelease ⨾ ⦗I⦘ ⊆ ⦗C⦘ ⨾ Grelease.
Proof using WF ETCCOH RELCOV.
  unfold imm_s_hb.release.
  rewrite (sub_F SUB), (sub_Rel SUB).
  rewrite !seqA; unfold imm_s_hb.rs.
  rewrite (sub_W SUB), (sub_same_loc SUB).
  rewrite !seqA.
  rewrite rt_rf_rmw_I.
  arewrite (⦗E⦘ ⊆  ⦗E⦘ ⨾ ⦗E⦘) at 2.
  basic_solver.
  seq_rewrite <- (sub_rf SUB).
  seq_rewrite <- (sub_rmw SUB).
  arewrite ((Fsb ∩ Fsame_loc)^? ⨾ ⦗W⦘ ⨾ (Frfi ⨾ Frmw)^? ⊆ (Fsb ∩ Fsame_loc)^? ⨾ ⦗W⦘).
  { case_refl (Frfi ⨾ Frmw); [done|].
    arewrite_id  ⦗W⦘.
    rewrite (dom_r (wf_rmwD WF)).
    rewrite (rfi_in_sbloc' WF).
    rewrite (rmw_in_sb_loc WF) at 1.
    generalize (@sb_same_loc_trans Gf); ins; relsf. }
  case_refl (⦗F⦘ ⨾ Fsb).
  { arewrite (⦗Rel⦘ ⨾ ⦗W⦘ ⨾ (Fsb ∩ Fsame_loc)^? ⨾ ⦗W⦘ ⨾ ⦗I⦘ ⊆ ⦗I⦘ ⨾ ⦗Rel⦘ ⨾ ⦗W⦘ ⨾ ((⦗E⦘ ⨾ Fsb ⨾ ⦗E⦘) ∩ Fsame_loc)^? ⨾ ⦗W⦘ ⨾ ⦗I⦘).
    { generalize (W_Rel_sb_loc_I TCCOH) I_in_E. basic_solver 21. }
    seq_rewrite <- (sub_sb SUB); revert RELCOV; basic_solver 40. }
  arewrite ((Fsb ∩ Fsame_loc)^? ⊆ Fsb^?) at 1.
  arewrite_id ⦗FW⦘ at 1.
  generalize (@sb_trans Gf); ins; relsf.
  arewrite (⦗Rel⦘ ⨾ ⦗F⦘ ⨾ Fsb ⨾ ⦗W⦘ ⨾ ⦗I⦘ ⊆ ⦗C⦘ ⨾ ⦗Rel⦘ ⨾ ⦗F⦘ ⨾ ⦗E⦘ ⨾ Fsb ⨾ ⦗E⦘ ⨾ ⦗W⦘ ⨾ ⦗E⦘).
  { generalize (dom_F_Rel_sb_I_in_C TCCOH), C_in_E, I_in_E; basic_solver 21. }
  remember (⦗E0⦘ ⨾ Frf ⨾ ⦗E0⦘ ⨾ ⦗E0⦘ ⨾ Frmw ⨾ ⦗E0⦘) as X.
  ins; seq_rewrite <- (sub_sb SUB); basic_solver 21.
Qed.


Lemma release_S : Frelease ⨾ ⦗S⦘ ⊆ ⦗C⦘ ⨾ (fun _ _ => True) +++ Fsb^?.
Proof using thread WF ETCCOH RELCOV.
  unfold imm_s_hb.release at 1, imm_s_hb.rs at 1.
  rewrite !seqA.
  rewrite (rt_rf_rmw_S' WF ETCCOH).
  rewrite (crE (⦗I⦘ ⨾ (Frf ⨾ Frmw)⁺)); relsf; unionL.
  { arewrite (Frfi ⊆ Fsb).
    rewrite (rmw_in_sb WF).
    generalize (@sb_trans Gf). intros AA. relsf.
    clear -AA. basic_solver 12. }
  arewrite (Frfi ⊆ Frf).
  arewrite (⦗FRel⦘ ⨾ (⦗FF⦘ ⨾ Fsb)^? ⨾ ⦗FW⦘ ⨾ (Fsb ∩ Fsame_loc)^? ⨾ ⦗FW⦘ ⨾ (Frf ⨾ Frmw)＊ ⊆ Frelease).
  sin_rewrite release_I.
  clear. basic_solver 21.
Qed.

Lemma sb_F_E : dom_rel (Fsb ⨾ ⦗FF ∩₁ FAcq/Rel ∩₁ E⦘) ⊆₁ C ∪₁ I.
Proof using thread WF ETCCOH RELCOV.
  rewrite E_E0; unfold E0.
  rewrite !set_inter_union_r.
  rewrite !id_union; relsf; unionL; splits.
  { generalize (dom_sb_covered TCCOH); ie_unfolder; basic_solver 21. }
  { rewrite (issuedW TCCOH) at 1; type_solver. }
  2: { rewrite (dom_l (wf_rmwD WF)) at 1. type_solver. }
  rewrite crE. rewrite !seq_union_l, !seq_id_l, dom_union, set_inter_union_r.
  rewrite id_union, seq_union_r, dom_union.
  unionL.
  { rewrite (reservedW WF ETCCOH). type_solver. }
  generalize (etc_F_sb_S ETCCOH), (dom_sb_covered TCCOH). unfold ecovered; simpls.
  basic_solver 21.
Qed.

Lemma rfe_E :  dom_rel (Frfe ⨾ ⦗E ∩₁ NTid_ thread⦘) ⊆₁ I.
Proof using WF ETCCOH.
  clear RELCOV.
  rewrite E_E0; unfold E0.
  rewrite !set_inter_union_l.
  rewrite !id_union; relsf; unionL; splits.
  { generalize (dom_rf_covered WF TCCOH). ie_unfolder. basic_solver 21. }
  { rewrite (dom_r (wf_rfeD WF)) at 1; rewrite (issuedW TCCOH) at 1.
    type_solver. }
  { arewrite (Frfe ⊆ Frfe  ⨾  ⦗set_compl Init⦘).
    { rewrite (dom_r (wf_rfeD WF)).
      rewrite (init_w WF).
      unfolder; ins; desf; splits; eauto.
      intro; type_solver. }
    unfolder; ins; desf.
    apply sb_tid_init in H1; desf. }
  arewrite (Frfe ⊆ Frf).
  unfolder. ins. desf. eapply rfrmw_I_in_I; eauto.
  { apply ETCCOH. }
  basic_solver 10.
Qed.

Lemma Grfe_E :  dom_rel (Grfe) ⊆₁ I.
Proof using WF ETCCOH IMMCON.
  rewrite (dom_l (wf_rfeE rstWF)).
  rewrite E_E0; unfold E0.
  rewrite !id_union; relsf; unionL; splits.
  { rewrite (dom_l (wf_rfeD rstWF)).
    generalize (w_covered_issued TCCOH).
    basic_solver. }
  { basic_solver. }
  { rewrite (dom_r (wf_rfeE rstWF)).
    arewrite (⦗E⦘ ⊆ ⦗E ∩₁ NTid_ thread⦘ ∪ ⦗E ∩₁ Tid_ thread⦘).
    unfolder; ins; desf; tauto.
    relsf; splits.
    { rewrite (sub_rfe_in SUB), rfe_E. basic_solver. }
    rewrite (sub_rfe_in SUB).
    unfolder; ins; desf; exfalso.
    { eapply rfe_n_same_tid; eauto.
      { apply IMMCON. }
      split; eauto. congruence. }
    cdes IMMCON.
    eapply (thread_rfe_sb WF (coherence_sc_per_loc Cint)).
    unfold same_tid. unfolder. split; eauto. congruence. }
  rewrite (dom_l (wf_rmwD WF)).
  rewrite (dom_l (wf_rfeD rstWF)).
  clear. type_solver.
Qed.

Lemma rfi_E : dom_rel (Frfi ⨾ ⦗E⦘) ⊆₁ E.
Proof using WF ETCCOH.
  clear RELCOV.
  rewrite E_E0; unfold E0.
  rewrite !id_union; relsf; unionL; splits.
  { generalize (dom_sb_covered TCCOH); ie_unfolder. basic_solver 21. }
  { rewrite (dom_r (wf_rfiD WF)) at 1; rewrite (issuedW TCCOH) at 1. type_solver. }
  { generalize (@sb_trans Gf); ie_unfolder. basic_solver 21. }
  rewrite (dom_l (wf_rfiD WF)) at 1.
  unionR left -> left -> right.
  unfolder. ins. desf.
  eapply rfrmw_I_in_I; eauto.
  { apply ETCCOH. }
  eexists. apply seqA. apply seq_eqv_r. split; eauto.
  eexists. splits; eauto.
  match goal with
  | H: Frfi _ _ |- _ => apply H
  end.
Qed.

Lemma rfe_rmwrfi_rt_Acq_E :
  dom_rel (Frfe ⨾ (Frmw ⨾ Frfi)＊ ⨾ ⦗E ∩₁ FAcq⦘) ⊆₁ I.
Proof using WF ETCCOH.
  clear RELCOV.
  arewrite (Frfe ⨾ (Frmw ⨾ Frfi)＊ ⊆ (Frfe ⨾ (Frmw ⨾ Frfi)＊) ⨾ ⦗R⦘).
  { apply codom_rel_helper.
    rewrite (dom_r (wf_rfiD WF)), (dom_r (wf_rfeD WF)).
    rewrite rtE. rewrite <- !seqA.
    rewrite inclusion_ct_seq_eqv_r.
    basic_solver. }
  rewrite E_E0; unfold E0.
  rewrite !set_inter_union_l.
  rewrite !id_union; relsf; unionL; splits.
  { arewrite ((Frmw ⨾ Frfi)＊ ⊆ Fsb^?).
    { rewrite rmw_in_sb, rfi_in_sb; auto.
      generalize (@sb_trans Gf). intros HH.
        by rewrite rewrite_trans, rt_of_trans. }
    arewrite (Fsb^? ⨾ ⦗R⦘ ⨾ ⦗C ∩₁ FAcq⦘ ⊆ ⦗C⦘ ⨾ Fsb^?).
    { generalize (dom_sb_covered TCCOH). basic_solver 20. }
    generalize (dom_rf_covered WF TCCOH). ie_unfolder. basic_solver 21. }
  { rewrite (issuedW TCCOH) at 1. type_solver. }
  2: { arewrite_id ⦗R⦘. rewrite seq_id_l.
       arewrite (dom_rel (Frmw ⨾ ⦗NTid_ thread ∩₁ I⦘) ∩₁ FAcq ⊆₁
                 dom_rel (Frmw ⨾ ⦗I⦘)).
       { basic_solver. }
       rewrite <- !seqA. rewrite dom_rel_eqv_dom_rel.
       rewrite rfe_in_rf, rfi_in_rf. rewrite !seqA.
       rewrite (dom_l (wf_rfD WF)) at 1. rewrite !seqA.
       seq_rewrite <- clos_trans_rotl.
       arewrite (Frf ⨾ Frmw ⊆ Far ∪ Frf ⨾ Frmw).
       apply (ar_rfrmw_ct_I_in_I WF TCCOH). }
  rewrite crE. rewrite seq_union_l, seq_id_l, dom_union.
  rewrite set_inter_union_l. rewrite id_union.
  rewrite !seq_union_r, dom_union.
  rewrite (dom_r (wf_rfeD WF)).
  unionL.
  { rewrite (reservedW WF ETCCOH). type_solver. }
  rewrite set_interC.
  rewrite id_inter. rewrite <- !seqA.
  rewrite dom_rel_eqv_dom_rel.
  generalize (etc_dr_R_acq_I ETCCOH).
  unfold eissued. simpls.
  basic_solver 40.
Qed.

Lemma rfe_Grmwrfi_rt_Acq_E :
  dom_rel (Frfe ⨾ (Grmw ⨾ Grfi)＊ ⨾ ⦗E ∩₁ FAcq⦘) ⊆₁ I.
Proof using WF ETCCOH.
  rewrite (sub_rfi_in SUB).
  rewrite (sub_rmw_in SUB).
  apply rfe_rmwrfi_rt_Acq_E.
Qed.

Lemma rfe_Acq_E : dom_rel (Frfe ⨾ ⦗E ∩₁ FAcq⦘) ⊆₁ I.
Proof using WF ETCCOH.
  rewrite <- rfe_rmwrfi_rt_Acq_E.
  rewrite rtE. basic_solver 10.
Qed.

Lemma rfe_sb_F_E : dom_rel (Frfe ⨾ Fsb ⨾ ⦗E ∩₁ FF ∩₁ FAcq/Rel⦘) ⊆₁ I.
Proof using WF ETCCOH.
  clear RELCOV.
  rewrite E_E0; unfold E0.
  rewrite !set_inter_union_l.
  rewrite !id_union; relsf; unionL; splits.
  { generalize (dom_rf_covered WF TCCOH) (dom_sb_covered TCCOH).
    ie_unfolder; basic_solver 21. }
  { rewrite (issuedW TCCOH) at 1. type_solver. }
  2: { rewrite (dom_l (wf_rmwD WF)) at 1. type_solver. }
  rewrite set_interA. rewrite set_interC. rewrite id_inter.
  rewrite <- !seqA. rewrite dom_rel_eqv_dom_rel.
  rewrite crE. rewrite seq_union_l, seq_id_l.
  rewrite !seq_union_r, dom_union.
  unionL.
  { rewrite (reservedW WF ETCCOH). type_solver. }
  arewrite (Tid_ thread ∩₁ S ⊆₁ S) by basic_solver.
  sin_rewrite (dom_rel_helper (etc_F_sb_S ETCCOH)).
  unfold ecovered. simpls.
  generalize (dom_rf_covered WF TCCOH) (dom_sb_covered TCCOH).
  ie_unfolder; basic_solver 21.
Qed.

Lemma rfe_sb_F_Acq_E   :  dom_rel (Frfe ⨾ Fsb ⨾ ⦗E ∩₁ FF ∩₁ FAcq⦘) ⊆₁ I.
Proof using WF ETCCOH.
etransitivity; [|apply rfe_sb_F_E].
unfolder; ins; desf; eexists; eexists; splits; eauto; mode_solver 21. 
Qed.

Lemma rfe_sb_F_Rel_E   :  dom_rel (Frfe ⨾  Fsb ⨾ ⦗E ∩₁ FF ∩₁ FRel⦘) ⊆₁ I.
Proof using WF ETCCOH.
  clear RELCOV.
  etransitivity; [|apply rfe_sb_F_E].
  unfolder; ins; desf; eexists; eexists; splits; eauto; mode_solver 21. 
Qed.

Lemma rf_C : Frf ⨾ ⦗C⦘ ⊆ ⦗I⦘ ⨾ Grf.
Proof using WF ETCCOH.
rewrite (sub_rf SUB).
rewrite <- I_in_E at 1.
rewrite <- C_in_E at 1.
generalize (dom_rf_covered WF TCCOH); basic_solver 21.
Qed.

Lemma sw_C : Fsw ⨾ ⦗C⦘ ⊆ ⦗C⦘ ⨾ Gsw.
Proof using WF ETCCOH RELCOV.
unfold sw; rewrite !seqA.
arewrite ((Fsb ⨾ ⦗FF⦘)^? ⨾ ⦗FAcq⦘ ⨾ ⦗C⦘ ⊆ ⦗C⦘ ⨾ (⦗E⦘ ⨾ Fsb ⨾ ⦗E⦘ ⨾ ⦗FF⦘)^? ⨾ ⦗FAcq⦘).
by generalize (dom_sb_covered TCCOH) C_in_E; basic_solver 21.
sin_rewrite rf_C.
rewrite !seqA.
sin_rewrite release_I.
seq_rewrite <- (sub_sb SUB). 
by rewrite !seqA.
Qed.


Lemma sb_C : Fsb ⨾ ⦗C⦘ ⊆ ⦗C⦘ ⨾ Gsb.
Proof using WF ETCCOH.
rewrite (sub_sb SUB).
rewrite <- C_in_E.
generalize (dom_sb_covered TCCOH); basic_solver 21.
Qed.

Lemma hb_C : Fhb ⨾ ⦗C⦘ ⊆ ⦗C⦘ ⨾ Ghb.
Proof using WF ETCCOH RELCOV.
unfold hb.
apply ct_ind_left with (P:= fun r => r ⨾ ⦗C⦘).
- eauto with hahn.
- rewrite <- ct_step.
by relsf; rewrite sb_C, sw_C.
- intros k H; rewrite !seqA; sin_rewrite H.
relsf; sin_rewrite sb_C; sin_rewrite sw_C.
rewrite !seqA.
arewrite (Gsb ⊆ (Gsb ∪ Gsw)＊) at 1.
arewrite (Gsw ⊆ (Gsb ∪ Gsw)＊) at 3.
relsf.
Qed.

Lemma sc_C : sc ⨾ ⦗C⦘ ⊆ ⦗C⦘ ⨾ rst_sc.
Proof using WF WF_SC ETCCOH.
  clear RELCOV.
  unfold rst_sc.
  rewrite <- E_E0.
  rewrite <- C_in_E.
  cut (dom_rel (sc ⨾ ⦗C⦘) ⊆₁ C).
  { basic_solver 21. }
  rewrite (covered_in_coverable TCCOH) at 1.
  rewrite (dom_r (wf_scD WF_SC)) at 1.
  unfold coverable, dom_cond; type_solver 21.
Qed.

Lemma urr_C l : Furr l  ⨾ ⦗C⦘ ⊆ ⦗I⦘ ⨾ Gurr l.
Proof using WF WF_SC ETCCOH RELCOV.
  unfold CombRelations.urr.
  rewrite !seqA, (sub_W_ SUB), (sub_F SUB), (sub_Sc SUB).
  rewrite (cr_helper hb_C).
  sin_rewrite (cr_helper sc_C).
  rewrite !seqA.
  arewrite ((Fhb ⨾ ⦗FF ∩₁ FSc⦘)^? ⨾ ⦗C⦘ ⊆ ⦗C⦘ ⨾ (Ghb ⨾ ⦗FF ∩₁ FSc⦘)^?).
  { generalize hb_C.
    unfolder; ins; desf; splits; eauto 20.
    eapply H; eauto.
    right; eexists; splits; eauto.
    eapply H; eauto. }
  arewrite (⦗FW_ l⦘ ⨾ Frf^? ⨾ ⦗C⦘ ⊆ ⦗I⦘ ⨾ ⦗FW_ l⦘ ⨾ Grf^?).
  2: done.
  rewrite crE; relsf; unionL.
  { generalize (w_covered_issued TCCOH). basic_solver 21. }
  sin_rewrite rf_C; basic_solver 21.
Qed.

Lemma msg_rel_I l : Gmsg_rel l ⨾ ⦗ I ⦘ ≡ Fmsg_rel l ⨾ ⦗ I ⦘.
Proof using All.
unfold CombRelations.msg_rel.
split.
by rewrite (sub_urr_in SUB), (sub_release_in SUB).
arewrite (⦗I⦘ ⊆ ⦗I⦘ ⨾ ⦗I⦘) at 1.
by basic_solver.
sin_rewrite release_I.
rewrite !seqA.
sin_rewrite urr_C.
basic_solver.
Qed.


Lemma t_cur_thread l : t_cur rstG rst_sc thread l
  (covered T) ≡₁ t_cur Gf sc thread l (covered T).
Proof using All.
unfold t_cur, c_cur.
split.
rewrite (sub_urr_in SUB); basic_solver 12.
arewrite (⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C⦘ ⊆ ⦗C⦘ ⨾ ⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C⦘).
basic_solver.
sin_rewrite (@urr_C l).
basic_solver 21.
Qed.

Lemma t_rel_thread l l' : t_rel rstG rst_sc thread l l'
  (covered T) ≡₁ t_rel Gf sc thread l l' (covered T).
Proof using All.
unfold t_rel, c_rel.
split.
rewrite (sub_urr_in SUB); basic_solver 12.
arewrite (⦗FRel⦘ ⨾ ⦗FW_ l' ∪₁ FF⦘ ⨾ ⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C⦘ ⊆ ⦗C⦘ ⨾ 
⦗FRel⦘ ⨾ ⦗FW_ l' ∪₁ FF⦘ ⨾ ⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C⦘).
basic_solver.
sin_rewrite (@urr_C l).
basic_solver 21.
Qed.

Lemma t_acq_thread l : t_acq rstG rst_sc thread l
  (covered T) ≡₁ t_acq Gf sc thread l (covered T).
Proof using All.
unfold t_acq, c_acq.
split.
rewrite (sub_urr_in SUB), (sub_release_in SUB), (sub_rf_in SUB) ; basic_solver 12.
arewrite (⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C⦘ ⊆ ⦗C⦘ ⨾ ⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C⦘).
basic_solver.
arewrite ((Frelease ⨾ Frf)^? ⨾ ⦗C⦘ ⊆ ⦗C⦘ ⨾ (Grelease ⨾ Grf)^? ).
{ case_refl _; [basic_solver|].
  rewrite !seqA.
  sin_rewrite rf_C.
  sin_rewrite release_I. 
  basic_solver 12. }
  sin_rewrite (@urr_C l).
basic_solver 21.
Qed.

Lemma WF_rst : Wf rstG.
Proof using WF ETCCOH. eapply sub_WF; eauto. apply INIT. apply SUB. Qed.

Lemma WF_SC_rst : wf_sc rstG rst_sc.
Proof using WF WF_SC ETCCOH.
  unfold rstG; eapply sub_WF_SC; eauto; apply SUB.
Qed.

Lemma coh_sc_rst : coh_sc rstG rst_sc.
Proof using WF ETCCOH IMMCON.
  eapply sub_coh_sc; eauto; [eapply SUB| eapply IMMCON].
Qed.

Lemma coherence_rst : coherence rstG .
Proof using WF ETCCOH IMMCON.
  eapply sub_coherence; eauto; [eapply SUB| eapply IMMCON].
Qed.

Lemma Frmw_E_prefix_clos : codom_rel (⦗E⦘ ⨾ Frmw) ⊆₁ E.
Proof using WF ETCCOH RELCOV RMWCOV.
  rewrite E_E0 at 1.
  unfold E0. rewrite !id_union, !seq_union_l. rewrite !codom_union.
  unionL.
  { rewrite <- C_in_E. unfolder. ins. desf.
    eapply RMWCOV with (r:=x0); eauto. }
  { rewrite (issuedW TCCOH).
    rewrite (wf_rmwD WF). type_solver. }
  { rewrite (dom_l (wf_rmwD WF)).
    unfolder. ins. desf.
    { subst. 
      match goal with
      | H : S _ |- _ => eapply (reservedW WF ETCCOH) in H
      end.
      type_solver. }
    subst.
    assert (Fsb^? x y) as [|SB]; try subst x.
    { apply (transp_rmw_sb WF). eexists; eauto. }
    { apply tid_S_in_E. by split. }
    apply dom_sb_TS_in_E. basic_solver 10. }
  unfolder. ins. desf.
  assert (y = x); subst.
  2: by apply I_in_E.
  eapply wf_rmwf; eauto.
Qed.

Lemma acyc_ext_rst : acyc_ext rstG rst_sc.
Proof using WF ETCCOH IMMCON RELCOV RMWCOV.
  eapply sub_acyc_ext; eauto; [eapply SUB |eapply IMMCON].
Qed.

Lemma rmw_atomicity_rst : rmw_atomicity rstG.
Proof using WF ETCCOH IMMCON.
  eapply sub_rmw_atomicity; eauto; [eapply INIT| eapply SUB| eapply IMMCON].
Qed.

(******************************************************************************)
(******************************************************************************)

Lemma sb_total_W : (W ∩₁ (E \₁ I)) × (W ∩₁ (E \₁ I)) ⊆ Gsb^? ∪ Gsb⁻¹.
Proof using WF ETCCOH.  
  clear RELCOV.
  unfolder; ins; desf.
  cut ((x = y \/ Fsb x y) \/ Fsb y x).
  { intro; desf; eauto.
    left.
    all: right; apply (sub_sb SUB); basic_solver. }
  set (AA:=H3). apply E_E0 in AA.
  set (BB:=H1). apply E_E0 in BB.
  set (CC:=AA). apply E0_in_Gf in CC.
  set (DD:=BB). apply E0_in_Gf in DD.
  assert (~ is_init x) as NIX.
  { intros II. apply H4. eapply init_issued; eauto.
    { apply TCCOH. }
    split; auto. }
  assert (~ is_init y) as NIY.
  { intros II. apply H2. eapply init_issued; eauto.
    { apply TCCOH. }
    split; auto. }
  clear H3 H1. 
  unfold E0 in *; unfolder in *; ins; desf.
  all: try by exfalso; generalize (w_covered_issued TCCOH); basic_solver 4.
  all: try (apply (dom_l (wf_rmwD WF)) in AA; unfolder in AA; type_solver).
  all: try (apply (dom_l (wf_rmwD WF)) in BB; unfolder in BB; type_solver).
  all: eapply tid_n_init_sb; apply seq_eqv_l; split; auto;
    apply seqA;
    do 2 (apply seq_eqv_r; split; auto); red; auto.
  { apply sb_tid_init' in AA. unfold same_tid in *.
    unfolder in AA. desf. rewrite AA0. congruence. }
  { apply sb_tid_init' in BB. unfold same_tid in *.
    unfolder in BB. desf. rewrite BB0. desf. }
  apply sb_tid_init' in AA. unfold same_tid in *.
  unfolder in AA. desf. rewrite AA0. desf.
  apply sb_tid_init' in BB. unfold same_tid in *.
  unfolder in BB. desf. rewrite BB0. desf.
Qed.

Lemma IT_new_co: I ∪₁ E ∩₁ W ∩₁ Tid_ thread ≡₁ E ∩₁ W.
Proof using WF ETCCOH.
  clear RELCOV.
split.
- arewrite (I  ⊆₁ W ∩₁ E).
  generalize I_in_E (issuedW TCCOH); basic_solver.
  basic_solver.
- unfolder; ins; desf.
  destruct (classic (tid x = thread)); eauto.
  apply E_E0 in H.
  unfold E0 in *.
  unfolder in *; desf; eauto.
  * generalize (w_covered_issued TCCOH); basic_solver.
  * apply (dom_l (@wf_sbE Gf)) in H; unfolder in H; desf.
    apply sb_tid_init in H2; desf.
    left.
    apply (w_covered_issued TCCOH).
    cdes TCCOH.
    unfolder in ICOV; basic_solver 21.
  * apply (dom_l (wf_rmwD WF)) in H; unfolder in H; type_solver.
Qed.

Lemma CT_F: C ∩₁ F ∪₁ E ∩₁ F ∩₁ Tid_ thread ≡₁ E ∩₁ F.
Proof using WF ETCCOH.
  clear RELCOV.
split.
- rewrite C_in_E; basic_solver.
- unfolder; ins; desf.
  destruct (classic (tid x = thread)); eauto. left. 
  apply E_E0 in H.
  unfold E0 in *. 
  unfolder in *; desf; eauto.
  * apply (issuedW TCCOH) in H; type_solver.
  * apply (dom_l (@wf_sbE Gf)) in H; unfolder in H; desf.
    apply sb_tid_init in H2; desf.
    apply (init_w WF) in H2; type_solver.
  * apply (dom_l (wf_rmwD WF)) in H; unfolder in H; type_solver.
Qed.

Lemma dom_sb_S_tid_in_E : dom_rel (Fsb^? ⨾ ⦗Tid_ thread ∩₁ S⦘) ⊆₁ E.
Proof using WF ETCCOH.
  rewrite E_E0. unfold E0. by unionR left -> right.
Qed.

Lemma dom_rmw_ntid_I_in_E :
  dom_rel (Frmw ⨾ ⦗NTid_ thread ∩₁ I⦘) ⊆₁ E.
Proof using WF ETCCOH.
  rewrite E_E0. unfold E0. basic_solver 10.
Qed.

Lemma E_to_S: E ⊆₁ C ∪₁ dom_rel (Gsb^? ⨾ ⦗S⦘).
Proof using WF ETCCOH.
  rewrite E_E0. unfold E0. unionL.
  { basic_solver. }
  { rewrite (etc_I_in_S ETCCOH); simpls.
    basic_solver 10. }
  all: unionR right; rewrite (sub_sb SUB).
  { rewrite <- dom_sb_S_tid_in_E.
    unfolder. ins. desf; eauto 20. }
  erewrite <- inclusion_step_cr; [|reflexivity].
  rewrite <- I_in_E at 2.
  rewrite <- (etc_I_in_S ETCCOH). unfold eissued; simpls.
  rewrite <- dom_rmw_ntid_I_in_E.
  unfolder. ins. desf. eexists. splits; eauto 10.
    by apply (rmw_in_sb WF).
Qed.

Lemma E_F_AcqRel_in_C: E ∩₁ F ∩₁ Acq/Rel ⊆₁ C.
Proof using WF ETCCOH.
  clear RELCOV.
  rewrite E_to_S.
  rewrite (sub_sb_in SUB).
  unfolder; ins; desf.
  { apply (reservedW WF ETCCOH) in H2. type_solver. }
  generalize (etc_F_sb_S ETCCOH). unfold ecovered. simpls.
  basic_solver 21.
Qed.

Lemma E_F_Sc_in_C: E ∩₁ F ∩₁ Sc ⊆₁ C.
Proof using WF ETCCOH.
  clear RELCOV.
  arewrite (Sc ⊆₁ Acq/Rel) by mode_solver.
  apply E_F_AcqRel_in_C.
Qed.

Lemma COMP_RMWRFI_ACQ :
  dom_rel ((Grmw ⨾ Grfi)＊ ⨾ ⦗E ∩₁ R ∩₁ Acq⦘) ⊆₁ codom_rel Grf.
Proof using WF ETCCOH IMMCON.
  assert (dom_rel ((Grmw ⨾ Grfi)＊ ⨾ ⦗E ∩₁ R ∩₁ Acq⦘) ⊆₁ E ∩₁ R) as AA.
  { rewrite rtE. rewrite (dom_l (wf_rmwE rstWF)), (dom_l (wf_rmwD rstWF)).
    rewrite !seqA. clear. rewrite !inclusion_ct_seq_eqv_l. basic_solver 10. }
  rewrite (dom_rel_helper AA).
  intros r IN.
  cdes IMMCON.
  unfolder in IN; desf.
  edestruct (Comp z) as [x FR].
  { split; auto. apply (sub_E SUB); basic_solver. }
  unfolder; ins ;desf.
  cut (E0 x /\ E0 z).
  { basic_solver 12. }
  split; apply E_E0.
  2: { by apply IN5. }
  hahn_rewrite rfi_union_rfe in FR; unfolder in FR; desf.
  { eapply rfi_E. basic_solver 21. }
  eapply I_in_E.
  eapply rfe_Grmwrfi_rt_Acq_E.
  basic_solver 21.
Qed.

Lemma COMP_ACQ: forall r (IN: (E ∩₁ R ∩₁ Acq) r), exists w, Grf w r.
Proof using WF ETCCOH IMMCON.
  assert (dom_rel (⦗E ∩₁ R ∩₁ Acq⦘) ⊆₁ codom_rel Grf) as AA.
  { rewrite <- COMP_RMWRFI_ACQ. rewrite rtE. clear. basic_solver 10. }
  ins. eapply AA. generalize IN. clear. basic_solver 10.
Qed.

Lemma COMP_C : C ∩₁ R ⊆₁ codom_rel Grf.
Proof using WF ETCCOH IMMCON.
unfolder; ins; desf.
cdes IMMCON.
edestruct (Comp x) as [y FR].
- split; [by apply (coveredE TCCOH)| done].
- unfolder; ins ;desf.
cut (E0 y /\ E0 x).
basic_solver 12.
unfold E0; split; [|basic_solver].
generalize (dom_rf_covered WF TCCOH).
basic_solver 12.
Qed.

Lemma COMP_NTID : E ∩₁ NTid_ thread ∩₁ R ⊆₁ codom_rel Grf.
Proof using WF ETCCOH IMMCON.
unfolder; ins; desf.
cdes IMMCON.
edestruct (Comp x) as [x0 x1].
- split.
apply (sub_E SUB); basic_solver.
apply (sub_R SUB); basic_solver.
- unfolder; ins ;desf.
cut (E0 x0 /\ E0 x).
basic_solver 12.
split; apply E_E0.
2: { by apply H. }
hahn_rewrite rfi_union_rfe in x1; unfolder in x1; desf.
eapply rfi_E.
 basic_solver 21.
eapply I_in_E.
eapply rfe_E.
basic_solver 21.
Qed.

Lemma COMP_PPO : dom_rel (Gppo ⨾ ⦗I⦘) ∩₁ R ⊆₁ codom_rel Grf.
Proof using WF ETCCOH IMMCON RELCOV RMWCOV.
  rewrite (dom_l (wf_ppoE rstWF)).
  unfolder; ins; desf.
  cdes IMMCON.
  edestruct (Comp x) as [x0 x1].
  { split.
    apply (sub_E SUB); basic_solver.
    apply (sub_R SUB); basic_solver. }
  unfolder; ins ;desf.
  cut (E0 x0 /\ E0 x).
  { basic_solver 12. }
  split; apply E_E0.
  2: { by apply H. }
  hahn_rewrite rfi_union_rfe in x1; unfolder in x1; desf.
  { eapply rfi_E. basic_solver 21. }
  eapply I_in_E.
  generalize (dom_rfe_ppo_issued WF TCCOH).
  apply (sub_ppo_in SUB) in H1.
  basic_solver 21.
Qed.

Lemma COMP_RPPO : dom_rel (⦗R⦘ ⨾ (Gdata ∪ Grfi ∪ Grmw)＊ ⨾ rppo rstG ⨾ ⦗S⦘) ⊆₁ codom_rel Grf.
Proof using WF ETCCOH IMMCON RELCOV RMWCOV.
  arewrite ((Gdata ∪ Grfi ∪ Grmw)＊ ⨾ rppo rstG ⊆ ⦗E⦘ ⨾ (Gdata ∪ Grfi ∪ Grmw)＊ ⨾ rppo rstG).
  { apply dom_rel_helper.
    rewrite rtE, seq_union_l, seq_id_l, dom_union. unionL.
    { rewrite (dom_l (wf_rppoE rstWF)). basic_solver. }
    rewrite (dom_l (wf_dataE rstWF)).
    rewrite (dom_l (wf_rfiE rstWF)).
    rewrite (dom_l (wf_rmwE rstWF)).
    rewrite <- !seq_union_r.
    rewrite inclusion_ct_seq_eqv_l. basic_solver. }
  rewrite (sub_data_in SUB).
  rewrite (sub_rfi_in SUB).
  rewrite (sub_rmw_in SUB).
  rewrite (sub_rppo_in SUB).
  2: by apply Frmw_E_prefix_clos.
  unfolder. ins. desf.
  cdes IMMCON.
  edestruct (Comp x) as [x0 x1].
  { split.
    { apply (sub_E SUB). basic_solver. }
    apply (sub_R SUB); basic_solver. }
  unfolder; ins ;desf.
  cut (E0 x0 /\ E0 x).
  { basic_solver 12. }
  split; apply E_E0.
  2: { by apply H3. }
  hahn_rewrite rfi_union_rfe in x1; unfolder in x1; desf.
  { eapply rfi_E. basic_solver 21. }
  eapply I_in_E.
  apply (etc_rppo_S ETCCOH). simpls.
  basic_solver 21.
Qed.

Lemma COMP_RMW_S :
  dom_rel (Grmw ⨾ ⦗S⦘) ⊆₁ codom_rel Grf.
Proof using WF ETCCOH IMMCON.
  rewrite (dom_l (wf_rmwE rstWF)).
  rewrite (dom_l (wf_rmwD rstWF)).
  unfolder; ins; desf.
  cdes IMMCON.
  edestruct (Comp x) as [x0 x1].
  { split.
    { apply (sub_E SUB); basic_solver. }
    apply (sub_R SUB); basic_solver. }
  unfolder; ins ;desf.
  cut (E0 x0 /\ E0 x).
  { basic_solver 12. }
  split; apply E_E0.
  2: { by apply H. }
  hahn_rewrite rfi_union_rfe in x1; unfolder in x1; desf.
  { eapply rfi_E. basic_solver 21. }
  eapply I_in_E. eapply rfe_rmw_S with (T:=mkETC T S); eauto.
  do 2 eexists. split; eauto.
  apply seq_eqv_r. split; eauto.
  generalize H0. basic_solver 21.
Qed.

Lemma urr_helper: 
  dom_rel ((Ghb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ rst_sc^? ⨾ Ghb^? ⨾ Grelease ⨾ ⦗I⦘) ⊆₁ C.
Proof using All.
  rewrite (sub_hb_in SUB), (sub_release_in SUB), (sub_F SUB), (sub_Sc SUB).
  arewrite (rst_sc ⊆ sc) by unfold rst_sc; basic_solver.
  rewrite release_I.
  sin_rewrite (cr_helper hb_C).
  rewrite !seqA.
  sin_rewrite (cr_helper sc_C).
  rewrite !seqA.
  arewrite ((Fhb ⨾ ⦗FF ∩₁ FSc⦘)^? ⨾ ⦗C⦘ ⊆ ⦗C⦘ ⨾ (Ghb ⨾ ⦗FF ∩₁ FSc⦘)^?).
  { generalize hb_C.
    unfolder; ins; desf; splits; eauto 20.
    eapply H; eauto.
    right; eexists; splits; eauto.
    eapply H; eauto. }
  basic_solver.
Qed.


Lemma urr_helper_C: 
  dom_rel ((Ghb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ rst_sc^? ⨾ Ghb^? ⨾ (Grelease ⨾ Grf)^? ⨾ ⦗C⦘) ⊆₁ C.
Proof using All.
rewrite (sub_hb_in SUB), (sub_release_in SUB), (sub_F SUB), (sub_Sc SUB).
rewrite (sub_rf_in SUB).
arewrite (rst_sc ⊆ sc) by unfold rst_sc; basic_solver.

arewrite ((Frelease ⨾ Frf)^? ⨾ ⦗C⦘ ⊆ ⦗C⦘ ⨾ (Grelease ⨾ Grf)^?).
{ case_refl _; [basic_solver 12|].
rewrite !seqA.
rewrite rf_C.
sin_rewrite release_I.
basic_solver 12. }


sin_rewrite (cr_helper hb_C).
rewrite !seqA.
sin_rewrite (cr_helper sc_C).
rewrite !seqA.
arewrite ((Fhb ⨾ ⦗FF ∩₁ FSc⦘)^? ⨾ ⦗C⦘ ⊆ ⦗C⦘ ⨾ (Ghb ⨾ ⦗FF ∩₁ FSc⦘)^?).
{ generalize hb_C.
unfolder; ins; desf; splits; eauto 20.
eapply H; eauto.
right; eexists; splits; eauto.
eapply H; eauto. }
basic_solver.
Qed.

Lemma release_CI_de :
  ⦗(E \₁ C) ∩₁ (E \₁ I)⦘ ⨾ Grelease ⨾ ⦗C ∪₁ I⦘ ⊆ ∅₂.
Proof using All.
  rewrite !id_union; relsf; unionL.
  { rewrite (dom_r (wf_releaseD rstWF)), !seqA.
    arewrite (⦗W⦘ ⨾ ⦗C⦘ ⊆ ⦗W ∩₁ C⦘).
    { basic_solver 12. }
    rewrite (w_covered_issued TCCOH).
    rewrite (sub_release_in SUB).
    rels; sin_rewrite (release_I); basic_solver. }
  rewrite (sub_release_in SUB).
  rels; sin_rewrite (release_I); basic_solver.
Qed.

Lemma dom_rfe_rmw_ct_rfi_Acq_in_I :
  dom_rel (Grfe ⨾ Grmw ⨾ (Grfi ⨾ Grmw)＊ ⨾ Grfi ⨾ ⦗Acq⦘) ⊆₁ I.
Proof using All.
  rewrite (dom_r (wf_rfiE rstWF)) at 2. rewrite !seqA. rewrite seq_eqvC.
  rewrite E_E0. unfold E0.
  rewrite !id_union, !seq_union_r, !dom_union. unionL.
  { rewrite (rmw_in_sb rstWF). arewrite (Grfi ⊆ Gsb).
    arewrite (Gsb ⨾ (Gsb ⨾ Gsb)＊ ⨾ Gsb ⨾ ⦗Acq⦘ ⊆ Gsb).
    { generalize (@sb_trans rstG). ins. relsf. basic_solver. }
    rewrite (sub_rfe_in SUB).
    rewrite (sub_sb_in SUB).
    rewrite (dom_rel_helper (dom_sb_covered TCCOH)).
    arewrite (Frfe ⊆ Frf).
    rewrite <- !seqA.
    sin_rewrite (dom_rel_helper (dom_rf_covered WF TCCOH)).
    basic_solver. }
  { rewrite (issuedW TCCOH) at 1. 
    rewrite (wf_rfiD rstWF) at 2. rewrite (sub_R SUB).
    type_solver. }
  { rewrite <- !seqA. rewrite dom_rel_eqv_dom_rel. rewrite !seqA.
    rewrite (sub_rfe_in SUB).
    rewrite (sub_rfi_in SUB).
    rewrite (sub_rmw_in SUB).
    rewrite (sub_Acq SUB).
    arewrite (Tid_ thread ∩₁ S ⊆₁ S) by basic_solver.
    forward (eapply dom_rfe_rmw_ct_rfi_Acq_sb_S_in_I); eauto. }
  rewrite <- !seqA. rewrite dom_rel_eqv_dom_rel. rewrite !seqA.
  rewrite (sub_rfe_in SUB).
  rewrite (sub_rfi_in SUB).
  rewrite (sub_rmw_in SUB).
  rewrite (sub_Acq SUB).
  arewrite (NTid_ thread ∩₁ I ⊆₁ I) by basic_solver. 
  arewrite (Frmw ⨾ (Frfi ⨾ Frmw)＊ ⊆ Frmw ⨾ (Frfi ⨾ Frmw)＊ ⨾ ⦗FW_ex⦘).
  { rewrite <- !seqA. apply codom_rel_helper.
    rewrite rmw_W_ex. rewrite rtE. rewrite <- !seqA.
    rewrite inclusion_ct_seq_eqv_r. basic_solver. }
  arewrite (⦗FW_ex⦘ ⊆ ⦗FW⦘ ⨾ ⦗FW_ex⦘).
  { generalize (W_ex_in_W WF). basic_solver. }
  arewrite (Frmw ⨾ (Frfi ⨾ Frmw)＊ ⨾ ⦗W⦘ ⊆ Fppo).
  { rewrite (dom_l (wf_rmwD WF)) at 1.
    rewrite seqA. unfold ppo. hahn_frame.
    rewrite ct_begin. apply seq_mori; [eauto with hahn|].
    rewrite <- rt_of_ct with
        (r:= Fdata ∪ Fctrl ∪ Faddr ⨾ Fsb^? ∪ Frfi ∪ Frmw ∪ Frmw_dep ⨾ Fsb^?
                   ∪ ⦗FR_ex⦘ ⨾ Fsb).
    apply clos_refl_trans_mori.
    rewrite <- ct_ct, <- ct_step.
    apply seq_mori; eauto with hahn. }
  arewrite (⦗FW_ex⦘ ⨾ Frfi ⨾ ⦗FAcq⦘ ⊆ ar_int Gf).
  { unfold ar_int. unionR right. rewrite (wf_rfiD WF) at 1. basic_solver 10. }
  rewrite (rmw_in_ppo WF).
  rewrite ppo_in_ar_int.
  rewrite (dom_l (wf_rfeD WF)).
  rewrite rfe_in_ar with (sc:=sc).
  arewrite (ar_int Gf ⊆ Far).
  arewrite (Far ⨾ Far ⨾ Far ⨾ Far ⊆ Far⁺).
  { rewrite ct_step with (r:=Far) at 1 2 3 4. by rewrite !ct_ct. }
  apply ar_ct_I_in_I; auto. apply ETCCOH.
Qed.

Lemma sw_de : ⦗(E \₁ C) ∩₁ (E \₁ I)⦘ ⨾ Gsw ⊆ Gsb.
Proof using All.
  unfold sw.
  rewrite crE, !seq_union_l, !seq_union_r, seq_id_l, !seqA.
  unionL.
  2: { arewrite (Gsb ⨾ ⦗F⦘ ⨾ ⦗Acq⦘ ⊆ ⦗C⦘ ⨾ Gsb ⨾ ⦗F⦘ ⨾ ⦗Acq⦘).
       { apply dom_rel_helper. rewrite (dom_r (@wf_sbE rstG)), !seqA.
         rewrite <- !id_inter.
         arewrite (E ∩₁ (F ∩₁ Acq) ⊆₁ E ∩₁ F ∩₁ Acq/Rel) by mode_solver.
         rewrite E_F_AcqRel_in_C. rewrite (sub_sb_in SUB).
         eapply dom_sb_covered. apply ETCCOH. }
       rewrite (sub_rf_in SUB). sin_rewrite rf_C. rewrite !seqA.
       arewrite (I ⊆₁ C ∪₁ I) at 2.
       sin_rewrite release_CI_de. basic_solver. }
  rewrite rfi_union_rfe. rewrite !seq_union_l, !seq_union_r.
  unionL.
  2: { rewrite (sub_rfe SUB), !seqA. rewrite (sub_Acq SUB).
       rewrite <- id_inter. rewrite (dom_rel_helper rfe_Acq_E).
       arewrite_id ⦗E⦘. rewrite seq_id_l.
       arewrite (I ⊆₁ C ∪₁ I) at 2.
       sin_rewrite release_CI_de. basic_solver. }
  unfold imm_s_hb.release, imm_s_hb.rs.
  rewrite rt_rf_rmw, !seqA.
  rewrite (rtE (Grfe ⨾ Grmw ⨾ (Grfi ⨾ Grmw)＊)).
  relsf; unionL.
  { arewrite (Grfi ⊆ Gsb).
    rewrite (rmw_in_sb rstWF).
    arewrite_id ⦗FW⦘.
    arewrite_id ⦗FF⦘.
    arewrite ((Gsb ∩ Fsame_loc)^? ⊆ Gsb^?) by basic_solver.
    generalize (@sb_trans rstG); ins; relsf.
    basic_solver. }
  transitivity (fun (x y : actid) => False); [|basic_solver].
  rewrite ct_end, !seqA.
  arewrite (⦗Rel⦘ ⨾ (⦗F⦘ ⨾ Gsb)^? ⨾ ⦗W⦘ ⨾ (Gsb ∩ Gsame_loc)^? ⨾ ⦗W⦘ ⨾ (Grfi ⨾ Grmw)＊ ⊆ Grelease).
  { arewrite (Grfi ⊆ Grf). by unfold imm_s_hb.release, imm_s_hb.rs. }
  arewrite (Grelease ⨾ (Grfe ⨾ Grmw ⨾ (Grfi ⨾ Grmw)＊)＊ ⊆ Grelease).
  { unfold imm_s_hb.release, imm_s_hb.rs.
    arewrite (Grfe ⊆ Grf). arewrite (Grfi ⊆ Grf).
    rewrite <- !seqA. rewrite <- ct_begin. rewrite rt_of_ct.
    rewrite !seqA. by rewrite rt_rt. }
  rewrite (dom_rel_helper dom_rfe_rmw_ct_rfi_Acq_in_I).
  arewrite (I ⊆₁ C ∪₁ I) at 2.
  sin_rewrite release_CI_de. basic_solver.
Qed.
     
Lemma sb_sw_de : ⦗(E \₁ C) ∩₁ (E \₁ I)⦘ ⨾ Gsb^? ⨾ Gsw ⊆ Gsb.
Proof using All.
case_refl _; [by apply sw_de|].
rewrite (dom_l (wf_swE rstWF)).
rewrite (dom_l (wf_swD rstWF)).

arewrite (⦗(FF ∪₁ FW) ∩₁ FRel⦘ ⊆ ⦗FF ∩₁ FRel⦘ ∪ ⦗FW ∩₁ FRel⦘) by basic_solver.
relsf; unionL.
-
rewrite (sub_sb_in SUB) at 1.
 arewrite (FRel ⊆₁ FAcq/Rel) by mode_solver.
generalize sb_F_E; unfolder; ins; desf; exfalso.
assert (~ (C x \/ I x)) by tauto.
basic_solver 12.
- 


arewrite (⦗E⦘ ⊆ ⦗(E \₁ C) ∩₁ (E \₁ I)⦘ ∪ ⦗C ∪₁ I⦘).
by unfolder; ins; desf; tauto.
relsf; unionL.
* generalize sw_de, (@sb_trans rstG); basic_solver 21.
* rewrite (sub_sb_in SUB) at 1.
generalize RELCOV (dom_sb_covered TCCOH); unfolder; ins; desf; exfalso; basic_solver 21.
Qed.

Lemma hb_de : ⦗(E \₁ C) ∩₁ (E \₁ I)⦘ ⨾ Ghb ⊆ Gsb.
Proof using All.
unfold hb.
rewrite path_union.
generalize (@sb_trans rstG); ins; relsf; unionL.
basic_solver 12.
apply ct_ind_right with (P:= fun r => ⦗(E \₁ C) ∩₁ (E \₁ I)⦘ ⨾ r ⨾ Gsb^?).
- eauto with hahn.
- rewrite !seqA; sin_rewrite sb_sw_de.
generalize (@sb_trans rstG); ins; relsf.
- intros k H1.
arewrite (⦗(E \₁ C) ∩₁ (E \₁ I)⦘ ⊆ ⦗(E \₁ C) ∩₁ (E \₁ I)⦘ ⨾ ⦗(E \₁ C) ∩₁ (E \₁ I)⦘).
basic_solver.
sin_rewrite H1.
arewrite (Gsb ⊆ Gsb^?) at 1.
sin_rewrite sb_sw_de.
generalize (@sb_trans rstG); ins; relsf.
Qed.

Lemma hb_sc_hb_de : ⦗(E \₁ C) ∩₁ (E \₁ I)⦘ ⨾ Ghb ⨾ (rst_sc ⨾ Ghb)^? ⊆ Gsb.
Proof using All.
arewrite (⦗(E \₁ C) ∩₁ (E \₁ I)⦘ ⊆ ⦗(E \₁ C) ∩₁ (E \₁ I)⦘ ⨾ ⦗(E \₁ C) ∩₁ (E \₁ I)⦘).
basic_solver.
sin_rewrite hb_de.
case_refl _; [basic_solver|].
rewrite (dom_l (wf_scD WF_SC_rst)).
rewrite (dom_l (wf_scE WF_SC_rst)).
rewrite !seqA.
arewrite (⦗F ∩₁ Sc⦘ ⨾ ⦗E⦘ ⊆ ⦗C⦘).
generalize E_F_Sc_in_C; basic_solver.
rewrite (sub_sb_in SUB) at 1.
generalize (dom_sb_covered TCCOH).
unfolder; ins; desf.
exfalso; eauto 21.
Qed. 

Lemma W_hb_to_I_NTid: 
  dom_rel (⦗W⦘ ⨾ Ghb ⨾  ⦗I ∩₁ NTid_ thread⦘) ⊆₁ I.
Proof using All.
  rewrite (dom_l (wf_hbE rstWF)) at 1; rewrite !seqA.
  arewrite (⦗E⦘ ⊆ ⦗(E \₁ C) ∩₁ (E \₁ I)⦘ ∪ ⦗E ∩₁ C ∪₁ E ∩₁ I⦘).
  { unfolder. ins. desf. tauto. }
  relsf; unionL; splits; [|generalize (w_covered_issued TCCOH); basic_solver| basic_solver].
  rewrite <- !dom_eqv1.
  sin_rewrite hb_de.
  rewrite (dom_l (@wf_sbE rstG)), !seqA.
  rewrite sb_tid_init'; relsf; unionL; splits.
  { rewrite <- set_interA, (set_interC W).
    seq_rewrite <- IT_new_co.
    unfold same_tid in *.
    unfolder; ins; desf; congruence. }
  unfolder; ins.
  eapply init_issued; eauto.
  { apply TCCOH. }
  desf. split; auto. by apply (sub_E_in SUB).
Qed.

Lemma F_hb_to_I_NTid: 
  dom_rel (⦗F⦘ ⨾ Ghb ⨾  ⦗I ∩₁ NTid_ thread⦘) ⊆₁ C.
Proof using All.
rewrite (dom_l (wf_hbE rstWF)) at 1; rewrite !seqA.
arewrite (⦗E⦘ ⊆ ⦗(E \₁ C) ∩₁ (E \₁ I)⦘ ∪ ⦗E ∩₁ C ∪₁ E ∩₁ I⦘).
by unfolder; ins; desf; tauto.
relsf; unionL; splits.
2: basic_solver.
2: rewrite (issuedW TCCOH); type_solver.
rewrite <- !dom_eqv1.
sin_rewrite hb_de.
rewrite (dom_l (@wf_sbE rstG)), !seqA.
rewrite sb_tid_init'; relsf; unionL; splits.
- rewrite <- set_interA, (set_interC F).
seq_rewrite <- CT_F.

unfold same_tid in *.
unfolder; ins; desf; congruence.
- 
unfolder; ins; desf.
apply (init_w WF) in H1; type_solver.
Qed.


Lemma W_hb_sc_hb_to_I_NTid: 
  dom_rel (⦗W⦘ ⨾ Ghb ⨾ (rst_sc ⨾ Ghb)^? ⨾ ⦗I ∩₁ NTid_ thread⦘) ⊆₁ I.
Proof using All.
rewrite crE; relsf; split.
generalize W_hb_to_I_NTid; basic_solver 21.
rewrite !seqA.
rewrite (dom_l (wf_scD WF_SC_rst)).
rewrite (dom_l (wf_scE WF_SC_rst)).
rewrite !seqA.
arewrite (⦗F ∩₁ Sc⦘ ⨾ ⦗E⦘ ⊆ ⦗C⦘).
generalize E_F_Sc_in_C; basic_solver.
rewrite (sub_hb_in SUB).
sin_rewrite hb_C.
generalize (w_covered_issued TCCOH); basic_solver 21.
Qed.

Lemma detour_E : dom_rel (Gdetour ⨾ ⦗E ∩₁ NTid_ thread⦘) ⊆₁ I.
Proof using WF ETCCOH.
  clear RELCOV.
  rewrite (sub_detour_in SUB).
  rewrite E_E0; unfold E0.
  rewrite !set_inter_union_l.
  rewrite !id_union; relsf; unionL; splits.
  { rewrite (dom_l (wf_detourD WF)), detour_in_sb. 
    generalize (w_covered_issued TCCOH), (dom_sb_covered TCCOH).
    ie_unfolder. basic_solver 21. }
  { rewrite (dom_r (wf_detourD WF)) at 1. rewrite (issuedW TCCOH) at 1. type_solver. }
  { arewrite (Fdetour ⊆ Fdetour  ⨾  ⦗set_compl Init⦘).
    { rewrite (dom_r (wf_detourD WF)).
      rewrite (init_w WF).
      unfolder; ins; desf; splits; eauto.
      intro; type_solver. }
    unfolder; ins; desf.
    apply sb_tid_init in H1; desf. }
  rewrite (rmw_in_ppo WF).
  arewrite
    (dom_rel (Fppo ⨾ ⦗NTid_ thread ∩₁ I⦘)
        ∩₁ NTid_ thread ⊆₁ dom_rel (Fppo ⨾ ⦗I⦘)).
  { basic_solver. }
  rewrite dom_rel_eqv_dom_rel.
  rewrite <- dom_detour_rfe_ppo_issued at 2; eauto.
  2: by apply ETCCOH.
  basic_solver 10.
Qed.

Lemma detour_Acq_E : dom_rel (Gdetour ⨾ ⦗E ∩₁ R ∩₁ Acq⦘) ⊆₁ I.
Proof using WF ETCCOH.
  clear RELCOV.
  rewrite (sub_detour_in SUB).
  rewrite E_E0; unfold E0.
  rewrite !set_inter_union_l.
  rewrite !id_union; relsf; unionL; splits.
  { rewrite (dom_l (wf_detourD WF)), detour_in_sb. 
    generalize (w_covered_issued TCCOH), (dom_sb_covered TCCOH).
    ie_unfolder. basic_solver 21. }
  { rewrite (dom_r (wf_detourD WF)) at 1. rewrite (issuedW TCCOH) at 1. type_solver. }
  { rewrite set_interA. rewrite set_interC. rewrite id_inter.
    rewrite <- !seqA. rewrite dom_rel_eqv_dom_rel.
    rewrite crE. rewrite seq_union_l, seq_id_l.
    rewrite !seq_union_r, dom_union.
    unionL.
    { rewrite (reservedW WF ETCCOH). type_solver. }
    rewrite <- (etc_dr_R_acq_I ETCCOH).
    rewrite rtE.
    basic_solver 20. }
  rewrite (rmw_in_ppo WF).
  arewrite
    (dom_rel (Fppo ⨾ ⦗NTid_ thread ∩₁ I⦘)
       ∩₁ R ∩₁ Acq ⊆₁ dom_rel (Fppo ⨾ ⦗I⦘)).
  { basic_solver. }
  rewrite dom_rel_eqv_dom_rel.
  rewrite <- (dom_detour_rfe_ppo_issued WF TCCOH) at 2.
  basic_solver 10.
Qed.

Lemma TCCOH_rst : tc_coherent rstG rst_sc T.
Proof using WF ETCCOH RELCOV RMWCOV.
  cdes TCCOH.
  red; splits.
  { rewrite (sub_E_in SUB). apply TCCOH. }
  { unfold coverable in *; repeat (splits; try apply set_subset_inter_r).
    { unfold E0. basic_solver. }
    { rewrite CC. basic_solver. } 
    { rewrite (sub_sb_in SUB). rewrite CC at 1. basic_solver 12. }
    rewrite (sub_rf_in SUB), (sub_W SUB), (sub_R SUB), (sub_F SUB).
    arewrite (rst_sc ⊆ sc) by (unfold rst_sc; basic_solver).
    rewrite CC at 1. basic_solver 21. }
  unfold issuable in *; repeat (splits; try apply set_subset_inter_r).
  { rewrite <- E_E0. apply I_in_E. }
  { rewrite II. basic_solver. }
  { rewrite (sub_W SUB). rewrite II at 1. basic_solver 12. }
  { rewrite (sub_fwbob_in SUB). rewrite II at 1. basic_solver 12. }
  rewrite (sub_ar_in SUB), (sub_rf_in SUB), (sub_ppo_in SUB).
  rewrite (sub_same_loc_in SUB).
  rewrite II at 1. basic_solver 12.
Qed.

Lemma C_E_NTid : C ∪₁ (E ∩₁ NTid_ thread) ≡₁
C ∪₁ (I ∩₁ NTid_ thread) ∪₁ 
dom_rel (Frmw ⨾ ⦗ NTid_ thread ∩₁ I ⦘)
.
Proof using WF WF_SC ETCCOH.
  assert (TCCOH1:= TCCOH).
  apply (tc_coherent_implies_tc_coherent_alt WF WF_SC) in TCCOH1.
  destruct TCCOH1.
  rewrite E_E0; unfold E0; split; relsf; unionL; splits.
  1-3,5-7: basic_solver 12.
  { rewrite sb_tid_init'.
    relsf; splits.
    rewrite (dom_l (@wf_sbE Gf)).
    revert tc_init; basic_solver 12. }
  unionR right -> right.
  apply set_subset_inter_r; splits.
  basic_solver.
  rewrite (rmw_from_non_init WF).
  rewrite (rmw_in_sb WF).
  rewrite sb_tid_init'.
  unfolder. ins. desf. congruence.
Qed.

Lemma TCCOH_rst_new_T : tc_coherent rstG rst_sc (mkTC (C ∪₁ (E ∩₁ NTid_ thread)) I).
Proof using All.
  assert (TCCOH1:= TCCOH).
  apply (tc_coherent_implies_tc_coherent_alt WF WF_SC) in TCCOH1.
  destruct TCCOH1.
  apply tc_coherent_alt_implies_tc_coherent; constructor; ins.
  { rewrite (sub_E_in SUB) at 1. rewrite tc_init. basic_solver. }
  { unionL; [by rewrite C_in_E|basic_solver]. }
  { rewrite C_E_NTid at 1.
    rewrite !id_union; relsf; unionL; splits.
    { rewrite (sub_sb_in SUB). rewrite tc_sb_C. basic_solver. }
    { rewrite sb_tid_init'.
      relsf; splits.
      { rewrite (dom_l (@wf_sbE rstG)).
        unfolder. ins. desf. red in H4, H2.
        right. splits; try basic_solver. congruence. }
      rewrite (dom_l (@wf_sbE rstG)); rewrite (sub_E_in SUB) at 1. 
      revert tc_init. basic_solver. }
    rewrite dom_rel_eqv_dom_rel.

    rewrite (rmw_in_sb WF).
    rewrite (dom_l (@wf_sbE rstG)), !seqA.
    rewrite (sub_sb_in SUB) at 1.
    generalize (@sb_trans Gf); ins; relsf.


    rewrite sb_tid_init'.
    relsf; splits.
    { unfolder. ins. desf. red in H4. intuition. }
    rewrite (sub_E_in SUB) at 1. 
    revert tc_init. basic_solver. }
  { rewrite C_E_NTid.
    rewrite !set_inter_union_l.
    unionL; [done| basic_solver| rewrite (dom_l (wf_rmwD WF)); type_solver]. }
  { arewrite (⦗E0⦘ ⨾ Frf ⨾ ⦗E0⦘ ⊆ Grf).
    rewrite rfi_union_rfe; relsf; splits.
    { rewrite C_E_NTid.
      rewrite !id_union; relsf; unionL; splits.
      { rewrite (dom_l (wf_rfiD WF_rst)).
        arewrite (Grfi ⊆ Gsb).
        rewrite (sub_W SUB), (sub_sb_in SUB).
        generalize tc_W_C_in_I tc_sb_C. basic_solver 21. }
      { rewrite (dom_r (wf_rfiD WF_rst)); rewrite tc_I_in_W at 1.
        type_solver. }
      rewrite (sub_rfi_in SUB).
      unfolder; ins; desc; subst.
      eapply rfrmw_I_in_I; eauto.
      { apply TCCOH. }
      unfolder. do 2 eexists. split.
      { match goal with
        | H : Frfi _ _ |- _ => apply H
        end. }
      eauto. }
    rewrite (dom_r (wf_rfeE WF_rst)), !seqA.
    sin_rewrite (dom_rel_helper_in Grfe_E).
    basic_solver. }
  { rewrite (dom_r (wf_scE WF_SC_rst)), (dom_r (wf_scD WF_SC_rst)), !seqA.
    arewrite (⦗F ∩₁ Sc⦘ ⨾ ⦗E⦘ ⨾ ⦗C ∪₁ E ∩₁ NTid_ thread⦘ ⊆ ⦗C⦘).
    { generalize E_F_Sc_in_C. basic_solver. }
    rewrite (sub_sc_in SUB).
    rewrite tc_sc_C. basic_solver. }
  { apply I_in_E. }
  { rewrite (sub_fwbob_in SUB), tc_fwbob_I. basic_solver. }
  rewrite (sub_ar_in SUB), (sub_rf_in SUB), (sub_ppo_in SUB); auto.
Qed.

(* There was a commented out lemma for finite case. See commit history for it *)
(* Lemma GW_ex_in_IST *)
(*       (RMWREX : dom_rel Frmw ⊆₁ FR_ex) : *)
(*   GW_ex ⊆₁ issued T ∪₁ S ∩₁ Tid_ thread. *)

End RestExec.
