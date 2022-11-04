From hahn Require Import Hahn.

From imm Require Import Events.
From imm Require Import Execution.
From imm Require Import Execution_eco.
From imm Require Import imm_bob imm_s_ppo imm_s_hb imm_s.
From imm Require Import SubExecution.
From imm Require Import CombRelations.
From imm Require Import AuxRel2.

(* From imm Require Import TraversalConfig. *)
(* From imm Require Import TraversalConfigAlt. *)
From imm Require Import TraversalOrder.
From imm Require Import TLSCoherency.
From imm Require Import IordCoherency.
From imm Require Import SimClosure. 
From imm Require Import AuxDef. 
From imm Require Import TlsEventSets.
From imm Require Import EventsTraversalOrder.
Require Import ExtTraversalConfig ExtTraversalProperties.
From imm Require Import AuxRel.
Require Import CertT.

Set Implicit Arguments.

Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'NTid_' t" := (fun x => tid x <> t) (at level 1).


(* TODO: move to Eventstraversalorder *)
Section Tmp.
  Variable (G: execution) (sc: relation actid).
  Variable (T: trav_label -> Prop). 
  Hypothesis RELCOV : is_w (lab G) ∩₁ is_rel (lab G) ∩₁ issued T ⊆₁ covered T.
  (* Hypothesis RMWCOV : forall r w (RMW : Frmw r w), C r <-> C w. *)
  Hypotheses
    (TCOH: tls_coherent G T)
    (ICOH: iord_coherent G sc T)
    (RCOH: reserve_coherent G T).
  Hypotheses (WF: Wf G) (WF_SC: wf_sc G sc). 

  Lemma urr_helper_impl:
    dom_rel ((hb G ⨾ ⦗is_f (lab G) ∩₁ is_sc (lab G)⦘)^? ⨾ sc^? ⨾ (hb G)^? ⨾ ⦗covered T⦘) ⊆₁ covered T.
  Proof using WF_SC WF TCOH RELCOV ICOH.
    rewrite <- !seqA. 
    rewrite seqA. erewrite cr_helper.
    2: { apply dom_rel_helper_in. eapply dom_hb_covered; eauto. }
    rewrite <- seqA, dom_seq. rewrite seqA. erewrite cr_helper.
    2: { apply dom_rel_helper_in. eapply dom_sc_covered; eauto. }
    rewrite <- seqA, dom_seq. erewrite cr_helper.
    2: { apply dom_rel_helper_in.
         rewrite <- dom_hb_covered at 2; eauto. basic_solver. }
    basic_solver.
  Qed.

  Lemma urr_helper: 
    dom_rel ((hb G ⨾ ⦗is_f (lab G) ∩₁ is_sc (lab G)⦘)^? ⨾ sc^? ⨾ (hb G)^? ⨾ release G ⨾ ⦗issued T⦘) ⊆₁ covered T.
  Proof using WF_SC WF TCOH RELCOV ICOH. 
    rewrite <- !seqA. 
    rewrite seqA. forward eapply dom_release_issued as ->%dom_rel_helper_in; eauto.
    rewrite <- seqA, dom_seq.
    rewrite !seqA. apply urr_helper_impl. 
  Qed.

  Lemma urr_helper_C:
    dom_rel ((hb G ⨾ ⦗is_f (lab G) ∩₁ is_sc (lab G)⦘)^? ⨾ sc^? ⨾ (hb G)^? ⨾ (release G ⨾ rf G)^? ⨾ ⦗covered T⦘) ⊆₁ covered T.
  Proof using WF_SC WF TCOH RELCOV ICOH.
    rewrite <- !seqA. 
    rewrite seqA. erewrite cr_helper.
    2: { apply dom_rel_helper_in.
         rewrite seqA. eapply dom_release_rf_covered; eauto. }
    rewrite <- seqA, dom_seq.
    rewrite !seqA. apply urr_helper_impl. 
  Qed. 

  Lemma rfe_rmw_I: dom_rel (rfe G ⨾ rmw G ⨾ ⦗issued T⦘) ⊆₁ issued T.
  Proof using WF TCOH ICOH.
    arewrite (rfe G ⊆ rf G).
    eapply rfrmw_I_in_I; eauto. 
  Qed.

  Lemma release_S : release G ⨾ ⦗reserved T⦘ ⊆ ⦗covered T⦘ ⨾ (fun _ _ => True) +++ (sb G)^?.
  Proof using WF TCOH RELCOV RCOH ICOH. 
    unfold imm_s_hb.release at 1, imm_s_hb.rs at 1.
    rewrite !seqA.
    rewrite (rt_rf_rmw_S' WF ); eauto. 
    rewrite (crE (⦗issued T⦘ ⨾ (rf G ⨾ rmw G)⁺)); relsf; unionL.
    { arewrite (rfi G ⊆ sb G).
      rewrite (rmw_in_sb WF).
      generalize (@sb_trans G). intros AA. relsf.
      clear -AA. basic_solver 12. }
    arewrite (rfi G ⊆ rf G).
    arewrite (⦗is_rel (lab G)⦘ ⨾ (⦗is_f (lab G)⦘ ⨾ sb G)^? ⨾ ⦗is_w (lab G)⦘ ⨾ (sb G ∩ same_loc (lab G))^? ⨾ ⦗is_w (lab G)⦘ ⨾ (rf G ⨾ rmw G)＊ ⊆ release G).
    rewrite <- seqA. 
    forward eapply dom_release_issued as ->%dom_rel_helper_in; eauto.
    basic_solver. 
  Qed.


End Tmp. 

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

Variable T : trav_label -> Prop. 

Notation "'C'" := (covered T).
Notation "'I'" := (issued T).
Notation "'S'" := (reserved T).

Variable thread : BinNums.positive.

Hypothesis WF : Wf Gf.
Hypothesis WF_SC : wf_sc Gf sc.
Hypothesis IMMCON : imm_consistent Gf sc.
Hypothesis RELCOV : FW ∩₁ FRel ∩₁ I ⊆₁ C.
Hypothesis RMWCOV : forall r w (RMW : Frmw r w), C r <-> C w.
(* Hypothesis ETCCOH : etc_coherent Gf sc (mkETC T S). *)
Hypotheses
  (TCOH: tls_coherent Gf T)
  (ICOH: iord_coherent Gf sc T)
  (RCOH: reserve_coherent Gf T).

(* Local Lemma TCCOH : tc_coherent Gf sc T. *)
(* Proof using ETCCOH. apply ETCCOH. Qed. *)

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
Proof using WF TCOH RCOH. 
  unfold E0.
  rewrite coveredE, issuedE; eauto; try apply TCCOH.
  erewrite rcoh_S_in_E; eauto.
  rewrite (dom_l (@wf_sbE Gf)).
  rewrite (dom_l (wf_rmwE WF)).
  basic_solver.
Qed.

Lemma E_E0 : E ≡₁ E0.
Proof using WF TCOH RCOH. by apply restrict_E, E0_in_Gf. Qed.

Lemma tid_S_in_E : Tid_ thread ∩₁ S ⊆₁ E.
Proof using WF TCOH RCOH.
  rewrite E_E0; unfold E0. basic_solver 10.
Qed.

Lemma I_in_E : I ⊆₁ E.
Proof using WF TCOH RCOH.
  rewrite E_E0; unfold E0; basic_solver.
Qed.

Lemma C_in_E : C ⊆₁ E.
Proof using WF TCOH RCOH.
  rewrite E_E0; unfold E0; basic_solver.
Qed.

Lemma dom_sb_TS_in_E : dom_rel (Fsb^? ⨾ ⦗Tid_ thread ∩₁ S⦘) ⊆₁ E.
Proof using WF TCOH RCOH.
  rewrite E_E0; unfold E0. basic_solver 10.
Qed.

Lemma ST_in_E : S ∩₁ Tid_ thread ⊆₁ E.
Proof using WF TCOH RCOH.
  rewrite E_E0; unfold E0. basic_solver 10.
Qed.

Lemma SUB: sub_execution Gf rstG sc rst_sc.
Proof using WF TCOH RCOH. 
  eapply restrict_sub. done. eapply E0_in_Gf.
Qed.

Lemma INIT : Init ∩₁ FE ⊆₁ E.
Proof using WF TCOH RCOH. 
  erewrite init_issued; eauto; rewrite E_E0; unfold E0; basic_solver.
Qed.

Lemma rstWF : Wf rstG.
Proof using sc WF TCOH RCOH.
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

Lemma rmw_E_rfe :  dom_rel (Frmw ⨾ ⦗E⦘) ∩₁ codom_rel Frfe ⊆₁ E.
Proof using WF TCOH RCOH ICOH.
  rewrite E_E0; unfold E0.
  rewrite !id_union; relsf; unionL; splits.
  { rewrite (rmw_in_sb WF) at 1.
    generalize TCOH, dom_sb_covered, dom_rf_covered.
    ie_unfolder; basic_solver 21. }
  { arewrite (⦗I⦘ ⊆ ⦗Tid_ thread ∩₁ I⦘ ∪ ⦗NTid_ thread ∩₁ I⦘).
    { by unfolder; ins; desf; tauto. }
    relsf; unionL; splits.
    { rewrite (rmw_in_sb WF) at 1. rewrite (rcoh_I_in_S ) at 1; eauto.
      basic_solver 20. }
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
(* Proof using WF . *)
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
(*     apply set_subset_inter_r. split; [|done]. apply (reservedW WF ). } *)
(*   sin_rewrite (rmw_sb_cr_W_in_rppo WF). *)
(*   etransitivity. *)
(*   2: by apply (etc_rppo_S ). *)
(*   rewrite <- inclusion_id_rt. clear. basic_solver 20. *)
(* Qed. *)

Lemma rmw_E_rfi :  dom_rel (Frmw ⨾ ⦗E⦘) ∩₁ codom_rel Frfi ⊆₁ E.
Proof using WF TCOH RCOH ICOH.
rewrite E_E0; unfold E0.
rewrite !id_union; relsf; unionL; splits.
- rewrite (rmw_in_sb WF) at 1.
  generalize TCOH, dom_sb_covered, dom_rf_covered; ie_unfolder; basic_solver 21.
- arewrite (⦗I⦘ ⊆ ⦗Tid_ thread ∩₁ I⦘ ∪ ⦗NTid_ thread ∩₁ I⦘).
  by unfolder; ins; desf; tauto.
  relsf; unionL; splits.
  { rewrite (rmw_in_sb WF) at 1. rewrite (rcoh_I_in_S ) at 1; eauto.
    basic_solver 20. }
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
Proof using WF TCOH RCOH.
  rewrite E_E0. unfold E0.
  arewrite (I ⊆₁ I ∩₁ (Tid_ thread ∪₁ NTid_ thread)) at 1.
  { unfolder. ins. tauto. }
  rewrite set_inter_union_r, id_union.
  rewrite !seq_union_r, dom_union.
  unionL.
  { unionR left -> right.
    rewrite <- rcoh_I_in_S; eauto. unfold issued; simpls.
    rewrite (rmw_in_sb WF). basic_solver 10. }
  unionR right.
  unfolder. ins. desf. splits; eauto.
Qed.

Lemma rt_rf_rmw_I :
  (Frf ⨾ Frmw)＊ ⨾ ⦗I⦘ ⊆ (Frfi ⨾  Frmw)^? ⨾ ⦗I⦘ ⨾ (⦗E⦘ ⨾ Frf ⨾ ⦗E⦘ ⨾ Frmw ⨾ ⦗E⦘)＊ ⨾ ⦗E⦘ ⨾ ⦗I⦘.
Proof using WF TCOH RCOH ICOH.
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
    forward eapply rfe_rmw_I as ->%dom_rel_helper_in; eauto.  
    generalize I_in_E rfe_rmw_I rmw_E_rfe; ie_unfolder; basic_solver 80. }
  intros k H.
  rewrite !seqA, H.
  arewrite (⦗FW_ex⦘ ⨾ (Frfi ⨾ Frmw)^? ⨾ ⦗I⦘ ⊆ ⦗I⦘ ⨾ ⦗FW_ex⦘ ⨾ (Frfi ⨾ Frmw)^? ⨾ ⦗I⦘).
  { eapply dom_rel_helper_in.
    rewrite crE; relsf; unionL; splits; [basic_solver 12|].
    arewrite (Frfi ⊆ Frf).
    rewrite rfrmw_I_in_I; eauto.
    basic_solver. }
  
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
  hahn_frame_r.
  forward eapply rfe_rmw_I as ->%dom_rel_helper; eauto. 
  rewrite I_in_E at 1.
  unfold rfe.
  unfolder. ins. desf. splits; auto.
  eexists. splits; eauto. eexists.
  splits; eauto.
  apply rmw_E_rfe. unfold rfe. unfolder. splits; eauto.
  do 2 eexists. splits; eauto. by apply I_in_E.
Qed.

Lemma release_I : Frelease ⨾ ⦗I⦘ ⊆ ⦗C⦘ ⨾ Grelease.
Proof using WF RELCOV TCOH RCOH ICOH.
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
  {
    arewrite (⦗Rel⦘ ⨾ ⦗W⦘ ⨾ (Fsb ∩ Fsame_loc)^? ⨾ ⦗W⦘ ⨾ ⦗I⦘ ⊆ ⦗I⦘ ⨾ ⦗Rel⦘ ⨾ ⦗W⦘ ⨾ ((⦗E⦘ ⨾ Fsb ⨾ ⦗E⦘) ∩ Fsame_loc)^? ⨾ ⦗W⦘ ⨾ ⦗I⦘).
    { generalize (W_Rel_sb_loc_I WF TCOH ICOH) I_in_E. basic_solver 21. }
    seq_rewrite <- ?(sub_sb SUB); revert RELCOV; basic_solver 40. }
  arewrite ((Fsb ∩ Fsame_loc)^? ⊆ Fsb^?) at 1.
  arewrite_id ⦗FW⦘ at 1.
  generalize (@sb_trans Gf); ins; relsf.
  arewrite (⦗Rel⦘ ⨾ ⦗F⦘ ⨾ Fsb ⨾ ⦗W⦘ ⨾ ⦗I⦘ ⊆ ⦗C⦘ ⨾ ⦗Rel⦘ ⨾ ⦗F⦘ ⨾ ⦗E⦘ ⨾ Fsb ⨾ ⦗E⦘ ⨾ ⦗W⦘ ⨾ ⦗E⦘).
  { generalize dom_F_Rel_sb_I_in_C, C_in_E, I_in_E; basic_solver 21. }
  remember (⦗E0⦘ ⨾ Frf ⨾ ⦗E0⦘ ⨾ ⦗E0⦘ ⨾ Frmw ⨾ ⦗E0⦘) as X.
  ins; seq_rewrite <- (sub_sb SUB); basic_solver 21.
Qed.


Lemma sb_F_E : dom_rel (Fsb ⨾ ⦗FF ∩₁ FAcq/Rel ∩₁ E⦘) ⊆₁ C ∪₁ I.
Proof using thread WF RELCOV  TCOH RCOH ICOH.
  rewrite E_E0; unfold E0.
  rewrite !set_inter_union_r.
  rewrite !id_union; relsf; unionL; splits.
  { generalize (dom_sb_covered WF TCOH ICOH ); ie_unfolder; basic_solver 21. }
  { erewrite issuedW at 1; eauto; type_solver. }
  2: { rewrite (dom_l (wf_rmwD WF)) at 1; eauto. type_solver. }
  rewrite crE. rewrite !seq_union_l, !seq_id_l, dom_union, set_inter_union_r.
  rewrite id_union, seq_union_r, dom_union.
  unionL.
  { erewrite (reservedW WF ); type_solver. }
  generalize (rcoh_F_sb_S RCOH), (dom_sb_covered WF TCOH ICOH). unfold covered; simpls.
  basic_solver 21.
Qed.

Lemma rfe_E :  dom_rel (Frfe ⨾ ⦗E ∩₁ NTid_ thread⦘) ⊆₁ I.
Proof using WF TCOH RCOH ICOH.
  clear RELCOV.
  rewrite E_E0; unfold E0.
  rewrite !set_inter_union_l.
  rewrite !id_union; relsf; unionL; splits.
  { generalize (dom_rf_covered WF TCOH ICOH). ie_unfolder. basic_solver 21. }
  { rewrite (dom_r (wf_rfeD WF)) at 1; rewrite issuedW at 1; eauto. type_solver. }
  { arewrite (Frfe ⊆ Frfe  ⨾  ⦗set_compl Init⦘).
    { rewrite (dom_r (wf_rfeD WF)).
      erewrite init_w; eauto.
      unfolder; ins; desf; splits; eauto.
      intro; type_solver. }
    unfolder; ins; desf.
    apply sb_tid_init in H1; desf. }
  arewrite (Frfe ⊆ Frf).
  unfolder. ins. desf. eapply rfrmw_I_in_I; eauto.
  basic_solver 10.
Qed.

Lemma Grfe_E:  dom_rel (Grfe) ⊆₁ I.
Proof using WF IMMCON TCOH RCOH ICOH.
  rewrite (dom_l (wf_rfeE rstWF)).
  rewrite E_E0; unfold E0.
  rewrite !id_union; relsf; unionL; splits.
  { rewrite (dom_l (wf_rfeD rstWF)).
    generalize w_covered_issued. basic_solver. }
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
Proof using WF TCOH RCOH ICOH.
  clear RELCOV.
  rewrite E_E0; unfold E0.
  rewrite !id_union; relsf; unionL; splits.
  { generalize dom_sb_covered; ie_unfolder. basic_solver 21. }
  { rewrite (dom_r (wf_rfiD WF)) at 1; erewrite issuedW at 1; eauto. type_solver. }
  { generalize (@sb_trans Gf); ie_unfolder. basic_solver 21. }
  rewrite (dom_l (wf_rfiD WF)) at 1.
  unionR left -> left -> right.
  unfolder. ins. desf.
  eapply rfrmw_I_in_I; eauto.
  eexists. apply seqA. apply seq_eqv_r. split; eauto.
  eexists. splits; eauto.
  match goal with
  | H: Frfi _ _ |- _ => apply H
  end.
Qed.

Lemma rfe_rmwrfi_rt_Acq_E :
  dom_rel (Frfe ⨾ (Frmw ⨾ Frfi)＊ ⨾ ⦗E ∩₁ FAcq⦘) ⊆₁ I.
Proof using WF WF_SC TCOH RCOH ICOH.
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
    { generalize dom_sb_covered. basic_solver 20. }
    generalize dom_rf_covered. ie_unfolder. basic_solver 21. }
  { erewrite issuedW at 1; eauto. type_solver. }
  2: { arewrite_id ⦗R⦘. rewrite seq_id_l.
       arewrite (dom_rel (Frmw ⨾ ⦗NTid_ thread ∩₁ I⦘) ∩₁ FAcq ⊆₁
                 dom_rel (Frmw ⨾ ⦗I⦘)).
       { basic_solver. }
       rewrite <- !seqA. rewrite dom_rel_eqv_dom_rel.
       rewrite rfe_in_rf, rfi_in_rf. rewrite !seqA.
       rewrite (dom_l (wf_rfD WF)) at 1. rewrite !seqA.
       seq_rewrite <- clos_trans_rotl.
       arewrite (Frf ⨾ Frmw ⊆ Far ∪ Frf ⨾ Frmw).
       eapply ar_rfrmw_ct_I_in_I; eauto. }
  rewrite crE. rewrite seq_union_l, seq_id_l, dom_union.
  rewrite set_inter_union_l. rewrite id_union.
  rewrite !seq_union_r, dom_union.
  rewrite (dom_r (wf_rfeD WF)).
  unionL.
  { rewrite (reservedW WF ); eauto. type_solver. }
  rewrite set_interC.
  rewrite id_inter. rewrite <- !seqA.
  rewrite dom_rel_eqv_dom_rel.
  generalize (rcoh_dr_R_acq_I RCOH).
  unfold issued. simpls.
  basic_solver 40.
Qed.

Lemma rfe_Grmwrfi_rt_Acq_E :
  dom_rel (Frfe ⨾ (Grmw ⨾ Grfi)＊ ⨾ ⦗E ∩₁ FAcq⦘) ⊆₁ I.
Proof using WF WF_SC TCOH RCOH ICOH .
  rewrite (sub_rfi_in SUB).
  rewrite (sub_rmw_in SUB).
  apply rfe_rmwrfi_rt_Acq_E.
Qed.

Lemma rfe_Acq_E : dom_rel (Frfe ⨾ ⦗E ∩₁ FAcq⦘) ⊆₁ I.
Proof using WF WF_SC TCOH RCOH ICOH.
  rewrite <- rfe_rmwrfi_rt_Acq_E.
  rewrite rtE. basic_solver 10.
Qed.

Lemma rfe_sb_F_E : dom_rel (Frfe ⨾ Fsb ⨾ ⦗E ∩₁ FF ∩₁ FAcq/Rel⦘) ⊆₁ I.
Proof using WF TCOH RCOH ICOH.
  clear RELCOV.
  rewrite E_E0; unfold E0.
  rewrite !set_inter_union_l.
  rewrite !id_union; relsf; unionL; splits.
  { generalize (dom_rf_covered WF TCOH ICOH) (dom_sb_covered WF TCOH ICOH).
    ie_unfolder; basic_solver 21. }
  { erewrite issuedW at 1; eauto. type_solver. }
  2: { rewrite (dom_l (wf_rmwD WF)) at 1. type_solver. }
  rewrite set_interA. rewrite set_interC. rewrite id_inter.
  rewrite <- !seqA. rewrite dom_rel_eqv_dom_rel.
  rewrite crE. rewrite seq_union_l, seq_id_l.
  rewrite !seq_union_r, dom_union.
  unionL.
  { erewrite reservedW; eauto. type_solver. }
  arewrite (Tid_ thread ∩₁ S ⊆₁ S) by basic_solver.
  sin_rewrite (dom_rel_helper (rcoh_F_sb_S RCOH)).
  (* unfold covered. *)
  simpls.
  generalize (dom_rf_covered WF TCOH ICOH) (dom_sb_covered WF TCOH ICOH).
  ie_unfolder; basic_solver 40.
Qed.

Lemma rfe_sb_F_Acq_E   :  dom_rel (Frfe ⨾ Fsb ⨾ ⦗E ∩₁ FF ∩₁ FAcq⦘) ⊆₁ I.
Proof using WF TCOH RCOH ICOH.
etransitivity; [|apply rfe_sb_F_E].
unfolder; ins; desf; eexists; eexists; splits; eauto; mode_solver 21. 
Qed.

Lemma rfe_sb_F_Rel_E   :  dom_rel (Frfe ⨾  Fsb ⨾ ⦗E ∩₁ FF ∩₁ FRel⦘) ⊆₁ I.
Proof using WF TCOH RCOH ICOH.
  clear RELCOV.
  etransitivity; [|apply rfe_sb_F_E].
  unfolder; ins; desf; eexists; eexists; splits; eauto; mode_solver 21. 
Qed.

Lemma rf_C : Frf ⨾ ⦗C⦘ ⊆ ⦗I⦘ ⨾ Grf.
Proof using WF TCOH RCOH ICOH.
rewrite (sub_rf SUB).
rewrite <- I_in_E at 1.
rewrite <- C_in_E at 1.
generalize (dom_rf_covered WF TCOH ICOH); basic_solver 21.
Qed.

Lemma sw_C : Fsw ⨾ ⦗C⦘ ⊆ ⦗C⦘ ⨾ Gsw.
Proof using WF  RELCOV TCOH RCOH ICOH.
unfold sw; rewrite !seqA.
arewrite ((Fsb ⨾ ⦗FF⦘)^? ⨾ ⦗FAcq⦘ ⨾ ⦗C⦘ ⊆ ⦗C⦘ ⨾ (⦗E⦘ ⨾ Fsb ⨾ ⦗E⦘ ⨾ ⦗FF⦘)^? ⨾ ⦗FAcq⦘).
by generalize (dom_sb_covered WF TCOH ICOH) C_in_E; basic_solver 21.
sin_rewrite rf_C.
rewrite !seqA.
sin_rewrite release_I.
seq_rewrite <- (sub_sb SUB). 
by rewrite !seqA.
Qed.


Lemma sb_C : Fsb ⨾ ⦗C⦘ ⊆ ⦗C⦘ ⨾ Gsb.
Proof using WF TCOH RCOH ICOH .
rewrite (sub_sb SUB).
rewrite <- C_in_E.
generalize (dom_sb_covered WF TCOH ICOH); basic_solver 21.
Qed.

Lemma hb_C : Fhb ⨾ ⦗C⦘ ⊆ ⦗C⦘ ⨾ Ghb.
Proof using WF  RELCOV TCOH RCOH ICOH.
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
Proof using WF WF_SC TCOH RCOH ICOH.
  clear RELCOV.
  unfold rst_sc.
  rewrite <- E_E0.
  rewrite <- C_in_E.
  cut (dom_rel (sc ⨾ ⦗C⦘) ⊆₁ C).
  { basic_solver 21. }
  eapply dom_sc_covered; eauto. 
Qed.

Lemma urr_C l : Furr l  ⨾ ⦗C⦘ ⊆ ⦗I⦘ ⨾ Gurr l.
Proof using WF WF_SC RELCOV TCOH RCOH IMMCON ICOH.
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
  { generalize w_covered_issued. basic_solver 21. }
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
Proof using WF sc TCOH RCOH. eapply sub_WF; eauto. apply INIT. apply SUB. Qed.

Lemma WF_SC_rst : wf_sc rstG rst_sc.
Proof using WF WF_SC TCOH RCOH.
  unfold rstG; eapply sub_WF_SC; eauto; apply SUB.
Qed.

Lemma coh_sc_rst : coh_sc rstG rst_sc.
Proof using WF IMMCON TCOH RCOH.
  eapply sub_coh_sc; eauto; [eapply SUB| eapply IMMCON].
Qed.

Lemma coherence_rst : coherence rstG .
Proof using WF TCOH RCOH IMMCON.
  eapply sub_coherence; eauto; [eapply SUB| eapply IMMCON].
Qed.

Lemma Frmw_E_prefix_clos : codom_rel (⦗E⦘ ⨾ Frmw) ⊆₁ E.
Proof using WF RELCOV RMWCOV TCOH RCOH.
  rewrite E_E0 at 1.
  unfold E0. rewrite !id_union, !seq_union_l. rewrite !codom_union.
  unionL.
  { rewrite <- C_in_E. unfolder. ins. desf.
    eapply RMWCOV with (r:=x0); eauto. }
  { erewrite issuedW, wf_rmwD; eauto. type_solver. }
  { rewrite (dom_l (wf_rmwD WF)).
    unfolder. ins. desf.
    { subst. 
      match goal with
      | H : S _ |- _ => eapply (reservedW WF ) in H; eauto
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
Proof using WF TCOH RCOH IMMCON RELCOV RMWCOV.
  eapply sub_acyc_ext; eauto; [eapply SUB |eapply IMMCON].
Qed.

Lemma rmw_atomicity_rst : rmw_atomicity rstG.
Proof using WF TCOH RCOH IMMCON.
  eapply sub_rmw_atomicity; eauto; [eapply INIT| eapply SUB| eapply IMMCON].
Qed.

(******************************************************************************)
(******************************************************************************)

(* TODO: seems incorrect, not used *)

(* Lemma sb_total_W : (W ∩₁ (E \₁ I)) × (W ∩₁ (E \₁ I)) ⊆ Gsb^? ∪ Gsb⁻¹. *)
(* Proof using WF .   *)
(*   clear RELCOV. *)
(*   unfolder; ins; desf. *)
(*   cut ((x = y \/ Fsb x y) \/ Fsb y x). *)
(*   { intro; desf; eauto. *)
(*     left. *)
(*     all: right; apply (sub_sb SUB); basic_solver. } *)
(*   set (AA:=H3). apply E_E0 in AA. *)
(*   set (BB:=H1). apply E_E0 in BB. *)
(*   set (CC:=AA). apply E0_in_Gf in CC. *)
(*   set (DD:=BB). apply E0_in_Gf in DD. *)
(*   assert (~ is_init x) as NIX. *)
(*   { intros II. apply H4. eapply init_issued; eauto. *)
(*     split; auto. } *)
(*   assert (~ is_init y) as NIY. *)
(*   { intros II. apply H2. eapply init_issued; eauto. *)
(*     split; auto. } *)

(*   clear H3 H1.  *)
(*   unfold E0 in *; unfolder in *; ins; desf. *)
(*   all: try by exfalso; generalize (w_covered_issued TCOH); basic_solver 4. *)
(*   all: try by (apply (dom_l (wf_rmwD WF)) in AA; unfolder in AA; type_solver). *)
(*   all: try by (apply (dom_l (wf_rmwD WF)) in BB; unfolder in BB; type_solver). *)
(*   all: eapply tid_n_init_sb; apply seq_eqv_l; split; auto; *)
(*     apply seqA; *)
(*     do 2 (apply seq_eqv_r; split; auto); red; auto. *)
(*   { eapply sb_tid_init' in AA; eauto. unfold same_tid in *. *)
(*     unfolder in AA. desf. rewrite AA0. congruence. } *)
(*   { apply sb_tid_init' in BB. unfold same_tid in *. *)
(*     unfolder in BB. desf. rewrite BB0. desf. } *)
(*   apply sb_tid_init' in AA. unfold same_tid in *. *)
(*   unfolder in AA. desf. rewrite AA0. desf. *)
(*   apply sb_tid_init' in BB. unfold same_tid in *. *)
(*   unfolder in BB. desf. rewrite BB0. desf. *)
(* Qed. *)

Lemma IT_new_co: I ∪₁ E ∩₁ W ∩₁ Tid_ thread ≡₁ E ∩₁ W.
Proof using WF TCOH RCOH ICOH.
  clear RELCOV.
split.
- arewrite (I  ⊆₁ W ∩₁ E); [| basic_solver]. 
  generalize I_in_E issuedW; basic_solver.
- unfolder; ins; desf.
  destruct (classic (tid x = thread)); eauto.
  apply E_E0 in H.
  unfold E0 in *.
  unfolder in *; desf; eauto.
  * generalize w_covered_issued; basic_solver.
  * apply (dom_l (@wf_sbE Gf)) in H; unfolder in H; desf.
    apply sb_tid_init in H2; desf.
    left.
    eapply w_covered_issued; eauto. 
    (* cdes TCOH. *)
    unfolder. splits; eauto. eapply init_covered; vauto. 
  * apply (dom_l (wf_rmwD WF)) in H; unfolder in H; type_solver.
Qed.

Lemma CT_F: C ∩₁ F ∪₁ E ∩₁ F ∩₁ Tid_ thread ≡₁ E ∩₁ F.
Proof using WF TCOH RCOH.
  clear RELCOV.
split.
- rewrite C_in_E; basic_solver.
- unfolder; ins; desf.
  destruct (classic (tid x = thread)); eauto. left. 
  apply E_E0 in H.
  unfold E0 in *. 
  unfolder in *; desf; eauto.
  * eapply issuedW in H; eauto; type_solver.
  * apply (dom_l (@wf_sbE Gf)) in H; unfolder in H; desf.
    apply sb_tid_init in H2; desf.
    apply (init_w WF) in H2; type_solver.
  * apply (dom_l (wf_rmwD WF)) in H; unfolder in H; type_solver.
Qed.

Lemma dom_sb_S_tid_in_E : dom_rel (Fsb^? ⨾ ⦗Tid_ thread ∩₁ S⦘) ⊆₁ E.
Proof using WF TCOH RCOH.
  rewrite E_E0. unfold E0. by unionR left -> right.
Qed.

Lemma dom_rmw_ntid_I_in_E :
  dom_rel (Frmw ⨾ ⦗NTid_ thread ∩₁ I⦘) ⊆₁ E.
Proof using WF TCOH RCOH.
  rewrite E_E0. unfold E0. basic_solver 10.
Qed.

Lemma E_to_S: E ⊆₁ C ∪₁ dom_rel (Gsb^? ⨾ ⦗S⦘).
Proof using WF sc RCOH TCOH.
  rewrite E_E0. unfold E0. unionL.
  { unfolder. ins. vauto. }
  { erewrite <- rcoh_I_in_S; eauto.
    unfolder. ins. right. exists (event x). vauto. } 
  all: unionR right; rewrite (sub_sb SUB).
  { rewrite <- dom_sb_S_tid_in_E.
    unfolder. ins. desf; eauto 20. }
  erewrite <- inclusion_step_cr; [|reflexivity].
  rewrite <- I_in_E at 2.
  rewrite <- (rcoh_I_in_S ); eauto. unfold issued; simpls.
  rewrite <- dom_rmw_ntid_I_in_E.
  unfolder. ins. desf. eexists. splits; eauto 10.
  2: { by apply (rmw_in_sb WF). }
  do 2 eexists. splits; eauto. exists y0. vauto.  
Qed.

Lemma E_F_AcqRel_in_C: E ∩₁ F ∩₁ Acq/Rel ⊆₁ C.
Proof using WF sc TCOH RCOH.
  clear RELCOV.
  rewrite E_to_S.
  rewrite (sub_sb_in SUB).
  unfolder; ins; desf.
  { eapply reservedW in H2; eauto. type_solver. }
  generalize (rcoh_F_sb_S ). unfold covered. simpls.
  basic_solver 21.
Qed.

Lemma E_F_Sc_in_C: E ∩₁ F ∩₁ Sc ⊆₁ C.
Proof using WF sc TCOH RCOH.
  clear RELCOV.
  arewrite (Sc ⊆₁ Acq/Rel) by mode_solver.
  apply E_F_AcqRel_in_C.
Qed.

Lemma COMP_RMWRFI_ACQ :
  dom_rel ((Grmw ⨾ Grfi)＊ ⨾ ⦗E ∩₁ R ∩₁ Acq⦘) ⊆₁ codom_rel Grf.
Proof using WF WF_SC IMMCON TCOH RCOH ICOH.
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
Proof using WF WF_SC IMMCON TCOH RCOH ICOH.
  assert (dom_rel (⦗E ∩₁ R ∩₁ Acq⦘) ⊆₁ codom_rel Grf) as AA.
  { rewrite <- COMP_RMWRFI_ACQ. rewrite rtE. clear. basic_solver 10. }
  ins. eapply AA. generalize IN. clear. basic_solver 10.
Qed.

Lemma COMP_C : C ∩₁ R ⊆₁ codom_rel Grf.
Proof using WF IMMCON TCOH ICOH.
unfolder; ins; desf.
cdes IMMCON.
edestruct (Comp x) as [y FR].
- split; [eapply coveredE; eauto| done].
- unfolder; ins ;desf.
cut (E0 y /\ E0 x).
basic_solver 12.
unfold E0; split; [|basic_solver].
generalize (dom_rf_covered WF TCOH ICOH).
basic_solver 12.
Qed.

Lemma COMP_NTID : E ∩₁ NTid_ thread ∩₁ R ⊆₁ codom_rel Grf.
Proof using WF IMMCON TCOH ICOH RCOH.
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
Proof using WF  IMMCON RELCOV RMWCOV TCOH RCOH ICOH.
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
  generalize (dom_rfe_ppo_issued WF TCOH ICOH).
  apply (sub_ppo_in SUB) in H1.
  basic_solver 21.
Qed.

Lemma COMP_RPPO : dom_rel (⦗R⦘ ⨾ (Gdata ∪ Grfi ∪ Grmw)＊ ⨾ rppo rstG ⨾ ⦗S⦘) ⊆₁ codom_rel Grf.
Proof using WF  IMMCON RELCOV RMWCOV TCOH RCOH ICOH.
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
  eapply rcoh_rppo_S; eauto. 
  basic_solver 21.
Qed.

Lemma COMP_RMW_S :
  dom_rel (Grmw ⨾ ⦗S⦘) ⊆₁ codom_rel Grf.
Proof using WF IMMCON TCOH RCOH ICOH.
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
  eapply I_in_E. eapply rfe_rmw_S; eauto.
  do 2 eexists. split; eauto.
  apply seq_eqv_r. split; eauto.
  generalize H0. basic_solver 21.
Qed.

Lemma urr_helper_rst: 
  dom_rel ((Ghb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ rst_sc^? ⨾ Ghb^? ⨾ Grelease ⨾ ⦗I⦘) ⊆₁ C.
Proof using All.
  rewrite (sub_hb_in SUB), (sub_release_in SUB), (sub_F SUB), (sub_Sc SUB).
  arewrite (rst_sc ⊆ sc) by unfold rst_sc; basic_solver.
  apply urr_helper; eauto. 
Qed.


Lemma urr_helper_C_rst: 
  dom_rel ((Ghb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ rst_sc^? ⨾ Ghb^? ⨾ (Grelease ⨾ Grf)^? ⨾ ⦗C⦘) ⊆₁ C.
Proof using All.
  rewrite (sub_hb_in SUB), (sub_release_in SUB), (sub_F SUB), (sub_Sc SUB).
  rewrite (sub_rf_in SUB).
  arewrite (rst_sc ⊆ sc) by unfold rst_sc; basic_solver.
  apply urr_helper_C; eauto. 
Qed.

Lemma release_CI_de :
  ⦗(E \₁ C) ∩₁ (E \₁ I)⦘ ⨾ Grelease ⨾ ⦗C ∪₁ I⦘ ⊆ ∅₂.
Proof using All.
  rewrite !id_union; relsf; unionL.
  { rewrite (dom_r (wf_releaseD rstWF)), !seqA.
    arewrite (⦗W⦘ ⨾ ⦗C⦘ ⊆ ⦗W ∩₁ C⦘).
    { basic_solver 12. }
    erewrite (@w_covered_issued Gf); eauto. 
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
    rewrite (dom_rel_helper (dom_sb_covered WF TCOH ICOH)).
    arewrite (Frfe ⊆ Frf).
    rewrite <- !seqA.
    sin_rewrite (dom_rel_helper (dom_rf_covered WF TCOH ICOH)).
    basic_solver. }
  { erewrite issuedW at 1; eauto.
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
  apply ar_ct_I_in_I; auto.
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
         eapply dom_sb_covered; eauto. }
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
generalize RELCOV (dom_sb_covered WF TCOH ICOH); unfolder; ins; desf; exfalso; basic_solver 21.
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
generalize (dom_sb_covered WF TCOH ICOH).
unfolder; ins; desf.
exfalso; eauto 21.
Qed. 

Lemma W_hb_to_I_NTid: 
  dom_rel (⦗W⦘ ⨾ Ghb ⨾  ⦗I ∩₁ NTid_ thread⦘) ⊆₁ I.
Proof using All.
  rewrite (dom_l (wf_hbE rstWF)) at 1; rewrite !seqA.
  arewrite (⦗E⦘ ⊆ ⦗(E \₁ C) ∩₁ (E \₁ I)⦘ ∪ ⦗E ∩₁ C ∪₁ E ∩₁ I⦘).
  { unfolder. ins. desf. tauto. }
  relsf; unionL; splits; [|generalize w_covered_issued; basic_solver| basic_solver].
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
2: erewrite issuedW; eauto; type_solver.
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
generalize w_covered_issued; basic_solver 21.
Qed.

Lemma detour_E : dom_rel (Gdetour ⨾ ⦗E ∩₁ NTid_ thread⦘) ⊆₁ I.
Proof using WF TCOH RCOH ICOH.
  clear RELCOV.
  rewrite (sub_detour_in SUB).
  rewrite E_E0; unfold E0.
  rewrite !set_inter_union_l.
  rewrite !id_union; relsf; unionL; splits.
  { rewrite (dom_l (wf_detourD WF)), detour_in_sb. 
    generalize w_covered_issued, dom_sb_covered.
    ie_unfolder. basic_solver 21. }
  { rewrite (dom_r (wf_detourD WF)) at 1. erewrite issuedW at 1; eauto. type_solver. }
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
  basic_solver 10.
Qed.

Lemma detour_Acq_E : dom_rel (Gdetour ⨾ ⦗E ∩₁ R ∩₁ Acq⦘) ⊆₁ I.
Proof using WF TCOH RCOH ICOH.
  clear RELCOV.
  rewrite (sub_detour_in SUB).
  rewrite E_E0; unfold E0.
  rewrite !set_inter_union_l.
  rewrite !id_union; relsf; unionL; splits.
  { rewrite (dom_l (wf_detourD WF)), detour_in_sb. 
    generalize w_covered_issued, dom_sb_covered.
    ie_unfolder. basic_solver 21. }
  { rewrite (dom_r (wf_detourD WF)) at 1. erewrite issuedW at 1; eauto. type_solver. }
  { rewrite set_interA. rewrite set_interC. rewrite id_inter.
    rewrite <- !seqA. rewrite dom_rel_eqv_dom_rel.
    rewrite crE. rewrite seq_union_l, seq_id_l.
    rewrite !seq_union_r, dom_union.
    unionL.
    { erewrite reservedW; eauto. type_solver. }
    rewrite <- (rcoh_dr_R_acq_I ); eauto. 
    rewrite rtE.
    basic_solver 20. }
  rewrite (rmw_in_ppo WF).
  arewrite
    (dom_rel (Fppo ⨾ ⦗NTid_ thread ∩₁ I⦘)
       ∩₁ R ∩₁ Acq ⊆₁ dom_rel (Fppo ⨾ ⦗I⦘)).
  { basic_solver. }
  rewrite dom_rel_eqv_dom_rel.
  erewrite <- dom_detour_rfe_ppo_issued at 2; eauto. 
  basic_solver 10.
Qed.

Lemma ICOH_rst : iord_coherent rstG rst_sc T.
Proof using WF_SC WF TCOH RMWCOV RELCOV RCOH ICOH.
  red. etransitivity; [|now apply ICOH].
  apply dom_rel_mori. hahn_frame_r.
  apply sub_iord; eauto using SUB.
Qed.

Lemma Gsb_Fsb_restr:
  restr_rel E0 Fsb ≡ Gsb. 
Proof using WF TCOH RCOH. 
  unfold sb. rewrite <- !restr_relE, restr_restr.
  rewrite set_inter_absorb_l; [| apply E0_in_Gf].
  rewrite E_E0. done. 
Qed. 
  

Lemma ICOH_rst_certT: iord_coherent rstG rst_sc (certT rstG T thread).
Proof using WF_SC WF TCOH RMWCOV RELCOV RCOH ICOH.
  forward eapply ICOH_rst as ICOH'. red in ICOH'. red.
  unfold certT.
  assert (forall e (NIe: ~ is_init e),
             dom_rel (Fsb^? ⨾ ⦗Tid_ thread ∩₁ S⦘) e -> tid e = thread) as DOM_THREAD.
  { intros e NIe DOM.
    destruct DOM as [s [SB_ [Ts Ss]]%seq_eqv_r].
    destruct SB_ as [-> | SB]; [done| ].
    rewrite <- Ts. 
    eapply (@ninit_sb_same_tid Gf); eauto.
    apply seq_eqv_l. split; auto. }
 
  relsf. rewrite !id_union. relsf. splits.
  { unionR left -> left.
    rewrite iord_no_reserve. rewrite iord_no_reserve in ICOH'.
    generalize ICOH'. basic_solver 10. }
  2: { rewrite iord_no_reserve. rewrite set_pair_alt. basic_solver 10. }
  unfold iord. rewrite restr_relE, !seqA. 
  iord_dom_unfolder.
  { apply path_ut_first in d6. red in d6.
    rename b into e1, a0 into e2. 
    des.
    { left. right. splits; vauto.
      replace (tid e1) with (tid e2); [congruence| ].
      apply clos_trans_of_transitiveD in d6; [| apply sb_trans].
      symmetry. eapply (@ninit_sb_same_tid Gf).
      apply Gsb_Fsb_restr in d6. red in d6. desc. basic_solver. }
    destruct d6 as [c [SB_ [c' [SC REL]]]].
    enough (covered T c) as Cc.
    { apply clos_refl_trans_of_transitive in SB_; [| apply sb_trans]. 
      do 2 left. split; auto. apply tls_set_alt.
      destruct SB_ as [-> | SB]; [done | ].
      eapply dom_sb_covered; eauto.
      apply Gsb_Fsb_restr in SB. red in SB. desc. basic_solver 10. }
    red in SC. apply seq_eqv_lr in SC. desc.
    eapply wf_scD, seq_eqv_lr in SC0; eauto. desc. 
    red in SC. unfold set_union in SC. des; auto.
    { eapply issuedW in SC; eauto.
      type_solver. }
    { destruct SC as [s [SB__ [Ts Ss]]%seq_eqv_r].
      destruct SB__ as [-> | SB].
      { eapply reservedW in Ss; eauto. type_solver. }
      eapply rcoh_F_sb_S; eauto.
      eexists. apply seq_eqv_lr. splits; eauto. mode_solver. }
    destruct SC as [? [? [RMW%wf_rmwD%seq_eqv_lr _]]]; auto.
    type_solver. }
  { do 2 left. split; vauto. apply tls_set_alt. 
    do 2 (red in d; desc). unfold set_union in d. des; auto. 
    { eapply w_covered_issued; vauto. }
    { destruct d6. apply DOM_THREAD; basic_solver. }
    destruct d as [? [? [RMW%wf_rmwD%seq_eqv_lr _]]]; auto.
    type_solver. }
  do 2 left. split; vauto. apply tls_set_alt. 
  apply seq_eqv_lr in d9. desc.
  do 2 (red in d7; desc). unfold set_union in d7. des.
  { eapply dom_rf_covered; basic_solver 10. }
  { apply wf_rfD, seq_eqv_lr in d2; eauto. 
    eapply issuedW in d7; eauto. type_solver. }
  { destruct d6. apply DOM_THREAD; basic_solver. }
  eapply rfrmw_I_in_I; eauto. 
  destruct d7 as [? [RMW%wf_rmwD%seq_eqv_lr [NT II]]%seq_eqv_r]; auto.
  basic_solver 10. 
Qed. 
  
Lemma init_tls_eq_rstG : init_tls Gf ≡₁ init_tls rstG.
Proof using sc WF TCOH RCOH.
  split.
  2: { unfold init_tls.
       rewrite sub_is_ta_propagate_to_G; eauto using SUB.
       now rewrite E_E0, E0_in_Gf. }
  unfold init_tls.
  rewrite sub_is_ta_propagate_to_G with (G':=rstG); eauto using SUB.
  apply set_pair_mori; eauto with hahn.
  arewrite (FE ∩₁ Init ⊆₁ (Init ∩₁ FE) ∩₁ Init).
  { clear; basic_solver. }
  now rewrite INIT.
Qed.

(* TODO: move*)
Lemma init_tls_in_certT:
  init_tls Gf ⊆₁ certT rstG T thread.
Proof using TCOH.
  unfold init_tls. rewrite set_pair_alt. fold action event.
  rewrite !set_map_union, !set_inter_union_l.
  repeat (apply set_subset_union_l; split).
  1-3: red; intros [? e] [[=<-] [Ie]]; apply tls_set_alt.
  { apply covered_certT. left. eapply init_covered; vauto. }
  { apply issued_certT. eapply init_issued; vauto. }
  { apply reserved_certT. left. eapply init_issued; vauto. }
  red. intros [? e] [[t_ [TS [=<-]]] [Ie]]. apply tls_set_alt.
  eapply propagated_thread_certT.
  eapply init_propagated_thread; vauto.
Qed.


(* TODO: rename *)
Lemma TCOH_rst_certT: tls_coherent rstG (certT rstG T thread).
Proof using WF TCOH RCOH ICOH.
  assert (I ⊆₁ E ∩₁ W) as IEW.
  { generalize I_in_E issuedW. basic_solver 10. }
  assert (I ∪₁ S ∩₁ Tid_ thread ⊆₁ E ∩₁ W) as ISTEW.
  { apply set_subset_union_l. splits; auto.
    apply set_subset_inter_r. splits; auto.
    { rewrite <- tid_S_in_E. clear. basic_solver. }
    rewrite reservedW; eauto. clear. basic_solver. }
  split.
  { rewrite <- init_tls_eq_rstG.
    now apply init_tls_in_certT. }
  arewrite (certT rstG T thread ⊆₁ (event ↓₁ (is_init ∪₁ set_compl is_init)) ∩₁ certT rstG T thread).
  { clear. unfolder; ins; desf; tauto. }
  rewrite set_map_union.
  rewrite set_inter_union_l.
  apply set_union_mori.
  {
    (* unfold certT. *)
    rewrite certT_alt. 
    
    rewrite !set_inter_union_r.
    unionL.
    3: { unfold init_tls.
         clear. unfold set_pair. unfolder. ins. do 2 desf.
         splits; auto. }
    2: { unfold init_tls. rewrite ISTEW.
         clear. unfold set_pair. unfolder. ins. do 2 desf.
         splits; auto. }
    rewrite (tls_coh_exec TCOH).
    rewrite set_inter_union_l.
    rewrite set_inter_union_r.
    unionL.
    { rewrite init_tls_eq_rstG. clear. basic_solver 10. }
    transitivity (event ↓₁ Init ∩₁ exec_tls Gf).
    { clear. basic_solver 10. }
    arewrite (event ↓₁ Init ∩₁ exec_tls Gf ⊆₁ ∅).
    { rewrite exec_tls_ENI. clear. basic_solver 10. }
    clear; basic_solver. }
  (* unfold certT. *)
  rewrite certT_alt. 

  unfold exec_tls.
  rewrite !set_unionA.
  rewrite !set_map_union.
  rewrite !set_inter_union_r.
  rewrite !set_unionA.
  rewrite !set_pair_union_l.
  unionL.
  { arewrite (T ∩₁ action ↓₁ eq ta_cover ⊆₁ eq ta_cover <*> (event ↑₁ (T ∩₁ action ↓₁ eq ta_cover))).
    { clear. unfold set_pair. basic_solver 10. }
    rewrite C_in_E.
    clear. unfold set_pair. unfolder. ins. do 2 desf. eauto. }
  { unionR right -> left.
    arewrite (T ∩₁ action ↓₁ eq ta_issue ⊆₁ eq ta_issue <*> (event ↑₁ (T ∩₁ action ↓₁ eq ta_issue))).
    { clear. unfold set_pair. basic_solver 10. }
    rewrite IEW.
    clear. unfold set_pair. unfolder. ins. do 2 desf. }
  { unionR right -> right -> right.
    unfolder. intros [a e] [NINIT [TAE BB]]; ins.
    assert (is_ta_propagate_to_G Gf a) as PGF.
    { apply TCOH in TAE.
      unfold init_tls, exec_tls, set_pair in TAE.
      unfolder in TAE. desf. }
    assert (propagated Gf T e) as PP.
    { red. unfolder. exists (a, e).
      splits; auto; ins. }
    enough (E0 e) as E0E.
    { unfolder; splits; auto using E0_in_Gf.
      eapply propagatedW; eauto. }
    enough (issued T e) as ITE.
    { apply I_in_E in ITE. now apply E_E0 in ITE. }
    eapply propagated_in_issued; eauto. }
  { unionR right -> right -> left.
    rewrite ISTEW.
    unfold set_pair. unfolder. ins. do 2 desf. }
  unionR left.
  clear. unfold set_pair. unfolder. ins. do 2 desf.
Qed.

Lemma C_E_NTid : C ∪₁ (E ∩₁ NTid_ thread) ≡₁
                 C ∪₁ (I ∩₁ NTid_ thread) ∪₁ 
                   dom_rel (Frmw ⨾ ⦗ NTid_ thread ∩₁ I ⦘)
.
Proof using WF TCOH RCOH.
  rewrite E_E0; unfold E0; split; relsf; unionL; splits.
  1-3,5-7: basic_solver 12.
  { rewrite sb_tid_init'.
    rewrite unionC. rewrite cr_union_r.
    relsf; splits.
    2: { clear. basic_solver. }
    rewrite (dom_l (@wf_sbE Gf)).
    transitivity C; eauto with hahn.
    rewrite <- init_covered; eauto.
    basic_solver 12. }
  unionR right -> right.
  apply set_subset_inter_r; splits.
  { clear. basic_solver. }
  rewrite (rmw_from_non_init WF).
  rewrite (rmw_in_sb WF).
  rewrite sb_tid_init'.
  clear. unfolder. ins. desf. congruence.
Qed.

(* Lemma TCOH_rst_new_T : tc_coherent rstG rst_sc (mkTC (C ∪₁ (E ∩₁ NTid_ thread)) I). *)
(* Proof using All. *)
(*   assert (TCOH1:= TCOH). *)
(*   apply (tc_coherent_implies_tc_coherent_alt WF WF_SC) in TCOH1. *)
(*   destruct TCOH1. *)
(*   apply tc_coherent_alt_implies_tc_coherent; constructor; ins. *)
(*   { rewrite (sub_E_in SUB) at 1. rewrite tc_init. basic_solver. } *)
(*   { unionL; [by rewrite C_in_E|basic_solver]. } *)
(*   { rewrite C_E_NTid at 1. *)
(*     rewrite !id_union; relsf; unionL; splits. *)
(*     { rewrite (sub_sb_in SUB). rewrite tc_sb_C. basic_solver. } *)
(*     { rewrite sb_tid_init'. *)
(*       relsf; splits. *)
(*       { rewrite (dom_l (@wf_sbE rstG)). *)
(*         unfolder. ins. desf. red in H4, H2. *)
(*         right. splits; try basic_solver. congruence. } *)
(*       rewrite (dom_l (@wf_sbE rstG)); rewrite (sub_E_in SUB) at 1.  *)
(*       revert tc_init. basic_solver. } *)
(*     rewrite dom_rel_eqv_dom_rel. *)

(*     rewrite (rmw_in_sb WF). *)
(*     rewrite (dom_l (@wf_sbE rstG)), !seqA. *)
(*     rewrite (sub_sb_in SUB) at 1. *)
(*     generalize (@sb_trans Gf); ins; relsf. *)


(*     rewrite sb_tid_init'. *)
(*     relsf; splits. *)
(*     { unfolder. ins. desf. red in H4. intuition. } *)
(*     rewrite (sub_E_in SUB) at 1.  *)
(*     revert tc_init. basic_solver. } *)
(*   { rewrite C_E_NTid. *)
(*     rewrite !set_inter_union_l. *)
(*     unionL; [done| basic_solver| rewrite (dom_l (wf_rmwD WF)); type_solver]. } *)
(*   { arewrite (⦗E0⦘ ⨾ Frf ⨾ ⦗E0⦘ ⊆ Grf). *)
(*     rewrite rfi_union_rfe; relsf; splits. *)
(*     { rewrite C_E_NTid. *)
(*       rewrite !id_union; relsf; unionL; splits. *)
(*       { rewrite (dom_l (wf_rfiD WF_rst)). *)
(*         arewrite (Grfi ⊆ Gsb). *)
(*         rewrite (sub_W SUB), (sub_sb_in SUB). *)
(*         generalize tc_W_C_in_I tc_sb_C. basic_solver 21. } *)
(*       { rewrite (dom_r (wf_rfiD WF_rst)); rewrite tc_I_in_W at 1. *)
(*         type_solver. } *)
(*       rewrite (sub_rfi_in SUB). *)
(*       unfolder; ins; desc; subst. *)
(*       eapply rfrmw_I_in_I; eauto. *)
(*       { apply TCOH. } *)
(*       unfolder. do 2 eexists. split. *)
(*       { match goal with *)
(*         | H : Frfi _ _ |- _ => apply H *)
(*         end. } *)
(*       eauto. } *)
(*     rewrite (dom_r (wf_rfeE WF_rst)), !seqA. *)
(*     sin_rewrite (dom_rel_helper_in Grfe_E). *)
(*     basic_solver. } *)
(*   { rewrite (dom_r (wf_scE WF_SC_rst)), (dom_r (wf_scD WF_SC_rst)), !seqA. *)
(*     arewrite (⦗F ∩₁ Sc⦘ ⨾ ⦗E⦘ ⨾ ⦗C ∪₁ E ∩₁ NTid_ thread⦘ ⊆ ⦗C⦘). *)
(*     { generalize E_F_Sc_in_C. basic_solver. } *)
(*     rewrite (sub_sc_in SUB). *)
(*     rewrite tc_sc_C. basic_solver. } *)
(*   { apply I_in_E. } *)
(*   { rewrite (sub_fwbob_in SUB), tc_fwbob_I. basic_solver. } *)
(*   rewrite (sub_ar_in SUB), (sub_rf_in SUB), (sub_ppo_in SUB); auto. *)
(* Qed. *)

(* There was a commented out lemma for finite case. See commit history for it *)
(* Lemma GW_ex_in_IST *)
(*       (RMWREX : dom_rel Frmw ⊆₁ FR_ex) : *)
(*   GW_ex ⊆₁ issued T ∪₁ S ∩₁ Tid_ thread. *)

End RestExec.
