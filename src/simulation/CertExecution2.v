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

Notation "'cert_co'" := (cert_co G T thread).

Notation "'D'" := (D G T S thread).

Notation "'new_rf'" := (new_rf G sc T S thread).
Notation "'cert_rf'" := (Crf G sc T S thread).
(* Notation "'cert_rfi'" := (Crfi G sc T S thread). *)
(* Notation "'cert_rfe'" := (Crfe G sc T S thread). *)

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
       rf := cert_rf ;
       co := cert_co ;
    |}.

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
Lemma cert_rmw : Crmw ≡ Grmw.
Proof using. by unfold certG; ins. Qed.
Lemma cert_rf_eq : Crf ≡ cert_rf.
Proof using. by unfold certG; ins. Qed.
(* Lemma cert_rfi_eq : Crfi ≡ cert_rfi.
Proof using. by unfold certG; ins. Qed.
Lemma cert_rfe_eq : Crfe ≡ cert_rfe.
Proof using. by unfold certG; ins. Qed.
 *)
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



(******************************************************************************)
(** **   *)
(******************************************************************************)

Lemma dom_rf_D_helper': Grf ⨾ ⦗D⦘ ≡ ⦗D⦘ ;; Grf ⨾ ⦗D⦘.
Proof.
forward (eapply dom_rf_D with (T:=T) (S:=S) (thread:=thread)); try edone.
basic_solver 12.
Qed.

Lemma Grelease_D_in_Crelease : Grelease ;; <| D |> ⊆ Crelease.
Proof using All.
  unfold release, rs; ins.
  rewrite cert_F, cert_Rel, cert_W, cert_same_loc, cert_sb.
  hahn_frame.
  transitivity ((Grf ⨾ ⦗D⦘ ⨾ Grmw)＊).
  2: unfold Cert_rf.Crf; apply clos_refl_trans_mori; basic_solver 12.
  eapply rt_ind_right with (P:=fun r=> r ;; ⦗D⦘); eauto with hahn.
  basic_solver 12.
  intros k H.
  rewrite !seqA.
  arewrite (Grmw ⨾ ⦗D⦘ ⊆ ⦗D⦘ ;; Grmw) at 1.
  { forward (eapply dom_rmw_D with (T:=T)); try edone; basic_solver. }
  remember ((Grf ⨾ ⦗D⦘ ⨾ Grmw)＊) as X.
  seq_rewrite dom_rf_D_helper'.
  subst X.
  rewrite !seqA.
  sin_rewrite H.
  rewrite rtE at 2.
  rewrite ct_end.
  basic_solver 21.
Qed.

Lemma Crelease_D_in_Grelease : Crelease ;; <| D |> ⊆ Grelease.
Proof using All.
  unfold release, rs; ins.
  rewrite cert_F, cert_Rel, cert_W, cert_same_loc, cert_sb.
  hahn_frame.
  transitivity ((Grf ⨾ ⦗D⦘ ⨾ Grmw)＊).
  2: apply clos_refl_trans_mori; basic_solver 12.
  eapply rt_ind_right with (P:=fun r=> r ;; ⦗D⦘); eauto with hahn.
  basic_solver 12.
  intros k H.
  rewrite !seqA.
  arewrite (Grmw ⨾ ⦗D⦘ ⊆ ⦗D⦘ ;; Grmw) at 1.
  { forward (eapply dom_rmw_D with (T:=T)); try edone; basic_solver. }
  arewrite ((Grf ⨾ ⦗D⦘ ∪ new_rf) ⨾ ⦗D⦘ ⊆ Grf ⨾ ⦗D⦘).
  { rewrite wf_new_rfE; try edone. basic_solver 12. }
  remember ((Grf ⨾ ⦗D⦘ ⨾ Grmw)＊) as X.
  seq_rewrite dom_rf_D_helper'.
  subst X.
  rewrite !seqA.
  sin_rewrite H.
  rewrite rtE at 2.
  rewrite ct_end.
  basic_solver 21.
Qed.

Lemma Crelease_D_eq_Grelease_D : Crelease ;; <| D |> ≡ Grelease ;; <| D |>.
Proof using All.
  generalize Crelease_D_in_Grelease, Grelease_D_in_Crelease.
  clear. basic_solver.
Qed.

Lemma sw_helper_S :
  Grelease ⨾ ⦗E ∩₁ S⦘ ⨾ new_rf ⨾ ⦗Acq⦘ ⊆ 
  Gsb ∪ (Grelease ⨾ Grf ⨾ ⦗Acq⦘ ∪ Grelease ⨾ Grf ⨾ Gsb ⨾ ⦗F⦘ ⨾ ⦗Acq⦘).
Proof using All.
  unfold Cert_rf.new_rf.
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
  cut ((co G ⨾ ⦗cert_co_base G T⦘) w z).
  basic_solver.
  eapply new_co_I; try eapply IST_new_co; try apply WF; eauto.
  unfolder; splits; eauto.
  { eapply tot_ex.
    { eapply wf_new_co_total; try eapply IST_new_co; try apply WF; eauto. }
    { unfolder; splits; eauto. }
    { basic_solver 10. }
    { intro.
      eapply H3. exists w. splits; eauto.
      exists l; unfold urr.
      apply (wf_urrE WF WF_SC) in H1.
      basic_solver 12. }
    intro; subst; eauto. }
  eapply IST_in_cert_co_base; try edone.
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
  remember (Grf ⨾ ⦗D⦘ ∪ new_rf) as X.
  rewrite cert_F, cert_Acq, cert_sb.
  rewrite !crE, !seq_union_l, !seq_union_r, !seq_id_l, !seqA.
  unionL.
  { arewrite (⦗Acq⦘ ⊆ (⦗D⦘ ∪ ⦗set_compl D⦘) ⨾ ⦗Acq⦘) at 1.
    { unfolder. ins. desf. destruct (classic (D y)); eauto. }
    rewrite !seq_union_l, !seq_union_r.
    unionL.
    { seq_rewrite dom_rf_D_helper'.
      rewrite !seqA.
      sin_rewrite Grelease_D_in_Crelease.
      unfold Cert_rf.Crf.
      subst X; basic_solver 12. }
    rewrite rfi_union_rfe at 1.
    rewrite !seq_union_l, !seq_union_r.
    unionL; cycle 1.
    { transitivity (fun _ _ : actid => False); [|basic_solver].
      rewrite (dom_r WF.(wf_rfeD)).
      unfold Cert_D.D; basic_solver 21. }
    rewrite (dom_r WF.(wf_rfiE)) at 1.
    rewrite E_to_S.
    rewrite C_in_D with (G:=G) (T:=T) (S:=S) (thread:=thread). 
    rewrite id_union, !seq_union_r, !seq_union_l, !seq_union_r, !seqA.
    unionL; [basic_solver|].
    unfold release at 1, rs at 1.
    rewrite rt_rf_rmw.
    rewrite rtE with (r:= Grfe ⨾ Grmw ⨾ (Grfi ⨾ Grmw)＊).
    rewrite !seq_union_r, !seq_union_l; unionL.
    { arewrite (Grfi ⊆ Gsb).
      rewrite WF.(rmw_in_sb).
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
    assert (BB: Grmw ⨾ (Grfi ⨾ Grmw)＊ ⨾ Grfi ⊆ (Grmw ⨾ Grfi)^+).
    { seq_rewrite <- rt_seq_swap.
      rewrite !seqA.
      remember (Grmw ⨾ Grfi) as Y.
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
    arewrite ((Grmw ⨾ Grfi)⁺ ⨾ ⦗dom_rel (Gsb^? ⨾ ⦗S⦘)⦘ ⨾ ⦗Acq⦘ ⊆ 
              ⦗dom_rel ((Grmw ⨾ Grfi)＊ ⨾ ⦗R ∩₁ Acq⦘ ⨾ Gsb ⨾ ⦗S⦘)⦘ ⨾ 
              (Grmw ⨾ Grfi)⁺ ⨾ ⦗dom_rel (Gsb^? ⨾ ⦗S⦘)⦘ ⨾ ⦗Acq⦘).
    { apply dom_rel_helper.
    rewrite seq_eqvC, <- seqA.
    
    rewrite dom_rel_eqv_dom_rel.
    rewrite (dom_r WF.(wf_rfiD)) at 1. 
    rewrite <- !seqA.
    rewrite inclusion_ct_seq_eqv_r, !seqA.
    arewrite (⦗S⦘ ⊆ ⦗S⦘ ;; ⦗W⦘) at 1.
    { generalize S_in_W; clear; basic_solver. }
    arewrite (⦗R⦘ ⨾ ⦗Acq⦘ ⨾ Gsb^? ⨾ ⦗S⦘ ;; ⦗W⦘ ⊆ ⦗R ∩₁ Acq⦘ ⨾ Gsb ⨾ ⦗S⦘).
    {  type_solver 21. }
    rewrite rtE. basic_solver 21. }
    arewrite (Grfe ⊆ Grf).
arewrite (Grf
    ⨾ ⦗dom_rel ((Grmw ⨾ Grfi)＊ ⨾ ⦗R ∩₁ Acq⦘ ⨾ Gsb ⨾ ⦗S⦘)⦘  ⊆ Crf).
apply Grf_to_Acq_S_in_Crf; edone.

    rewrite Grfi_in_Crfi at 1; try edone.
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

arewrite (Gsb ⨾ ⦗F ∩₁ Acq/Rel⦘ ⊆ ⦗D⦘ ;; Gsb ⨾ ⦗F ∩₁ Acq/Rel⦘).
{ forward (eapply dom_sb_F_AcqRel_in_D with (T:=T) (S:=S) (thread:=thread)); try edone.
  basic_solver 12. }

  seq_rewrite dom_rf_D_helper'.
  rewrite !seqA.

arewrite ( Grf ⨾ ⦗D⦘ ⊆ cert_rf).

sin_rewrite Grelease_D_in_Crelease.
unionR right -> right.
basic_solver 21.
Qed.



(* TODO: move to AuxRel.v *) 
Lemma r_to_dom_rel_r_r {A} (r: relation A) : r ≡ <|dom_rel r|> ;; r.
Proof using. basic_solver. Qed.

Lemma cert_sb_sw : Gsb ∪ Csw ≡ Gsb ∪ Gsw.
Proof using All.
  split; [|by apply cert_sb_sw_helper].
  unionL; [by eauto with hahn|].
  unfold imm_s_hb.sw; ins.
  rewrite cert_F, cert_Acq, cert_sb.
  unfold Cert_rf.Crf.
  rewrite !seq_union_l, !seq_union_r.
  unionL.
  { seq_rewrite dom_rf_D_helper; try edone.
    rewrite !seqA.
    seq_rewrite Crelease_D_eq_Grelease_D.
    basic_solver 20. }
  rewrite !crE, !seq_union_l, !seq_union_r, !seq_id_l.
  unionL.
  2: { rewrite !seqA.
       arewrite (Gsb ⨾ ⦗F⦘ ⨾ ⦗Acq⦘ ≡ ⦗D⦘ ⨾ Gsb ⨾ ⦗F⦘ ⨾ ⦗Acq⦘).
       { rewrite (dom_r (@wf_sbE G)). generalize dom_sb_F_Acq_in_D. basic_solver 12. }
       seq_rewrite dom_rf_D_helper'.
       rewrite !seqA.
       rewrite wf_new_rfE; try edone. basic_solver. }
  rewrite wf_new_rfD; try edone.
  rewrite wf_new_rfE; try edone.
  rewrite !seqA.
  rewrite <- !id_inter. rewrite set_inter_minus_l. rewrite <- set_interA.
  arewrite (E ∩₁ R ∩₁ Acq ⊆₁ codom_rel Grf ∩₁ (E ∩₁ R ∩₁ Acq)).
  { generalize COMP_ACQ. clear. basic_solver 10. }
  rewrite rfi_union_rfe at 1. rewrite codom_union.
  rewrite set_inter_union_l. rewrite set_minus_union_l, id_union, !seq_union_r.
  unionL.
  2: { arewrite (codom_rel Grfe ∩₁ (E ∩₁ R ∩₁ Acq) ⊆₁ D).
       { unfold Cert_D.D. unionR left -> right. basic_solver. }
       basic_solver. }
  rewrite set_minus_inter_l, id_inter.
  arewrite (new_rf ⨾ ⦗codom_rel Grfi \₁ D⦘ ⊆ Grfi).
  { intros x y HH.
    apply seq_eqv_r in HH. destruct HH as [HH [[x' AA] BB]].
    assert (x' = x); subst; auto.
    eapply wf_new_rff; eauto.
    apply Grfi_nD_in_new_rf; try edone. apply seq_eqv_r. split; auto. }
  unfold release at 1, rs at 1.
  rewrite rt_rf_rmw.
  rewrite rtE with (r:= rfe certG ⨾ Crmw ⨾ (rfi certG ⨾ Crmw)＊).
  rewrite !seq_union_r, !seq_union_l; unionL.
  { unionR left.
    arewrite (Crfi ⊆ Gsb). arewrite (Grfi ⊆ Gsb).
    rewrite WF.(rmw_in_sb).
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
  arewrite (⦗E ∩₁ R ∩₁ Acq \₁ D⦘ ⊆ ⦗Acq \₁ C⦘ ;; ⦗E ∩₁ R ∩₁ Acq \₁ C⦘).
  { rewrite <- C_in_D. clear. basic_solver. }
  rewrite cert_rmw.
  arewrite_id (⦗W⦘ ⨾ ⦗E⦘). by basic_solver. 
  rels.
  arewrite ((Crfi ⨾ Grmw)＊ ⨾ Grfi ⨾ ⦗Acq \₁ C⦘  ⊆ (Grfi ⨾ Grmw)＊ ⨾ Grfi).
{ rewrite cert_rfi_eq.
  eapply Crfi_Grmw_rt_in_Grfi_Grmw; edone. }

arewrite (Crfe ⊆ <| I |> ;; Crfe).
{ rewrite cert_rfe_eq.
eapply dom_rel_helper with (r:=cert_rfe).
eapply dom_Crfe_in_I; edone. }

  rewrite I_in_D.
  seq_rewrite Crelease_D_eq_Grelease_D.
  rewrite !seqA.
  arewrite (Crfe ⊆ Crf).
  arewrite (Grmw ⨾ (Grfi ⨾ Grmw)＊ ⨾ Grfi ⊆ (Grmw ⨾ Grfi)＊).
  { rewrite rt_seq_swap. rewrite <- seqA, <- ct_begin. apply inclusion_t_rt. }
  rewrite r_to_dom_rel_r_r with (r:=(Grmw ⨾ Grfi)＊ ⨾ ⦗E ∩₁ R ∩₁ Acq \₁ C⦘).

arewrite (Crf ;; <| dom_rel ((Grmw ⨾ Grfi)^* ⨾ ⦗E∩₁R∩₁Acq \₁ C⦘) |> ⊆ Grf).
{ rewrite cert_rf_eq.
eapply Crf_to_Acq_nC_in_Grf; edone. }

  arewrite_id ⦗D⦘. rewrite seq_id_l.
  arewrite (Grfi ⊆ Grf).
  seq_rewrite <- rt_seq_swap. rewrite !seqA.
  sin_rewrite release_rf_rmw_steps.
  clear. basic_solver.
Qed.

Lemma cert_hb : Chb ≡ Ghb.
Proof using All.
by unfold imm_s_hb.hb; rewrite cert_sb_sw.
Qed.

Lemma cert_msg_rel l : Cmsg_rel l ⨾ ⦗I⦘ ≡ Gmsg_rel l ⨾ ⦗I⦘.
Proof using All.
unfold CombRelations.msg_rel, urr.
rewrite cert_W_, cert_F, cert_Sc, cert_hb, !seqA.
arewrite (Crelease ⨾ ⦗I⦘ ≡ Grelease ⨾ ⦗I⦘).
{ arewrite (⦗I⦘ ≡ ⦗D⦘ ;; ⦗I⦘).
  by generalize I_in_D; clear; basic_solver.
  seq_rewrite Crelease_D_eq_Grelease_D.
  by rewrite seqA. }
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
rewrite C_in_D with (G:=G) (T:=T) (S:=S) (thread:= thread) at 1.
arewrite (Crf ⨾ ⦗D⦘ ⊆ Grf ;; <| D |>).
by apply cert_rf_D; basic_solver.
basic_solver.
rewrite C_in_D with (G:=G) (T:=T) (S:=S) (thread:= thread) at 1.
arewrite (Grf ⨾ ⦗D⦘ ⊆ Crf ;; <| D |>).
by apply cert_rf_D; basic_solver.
basic_solver.
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
arewrite (Crf ⨾ ⦗D⦘ ≡ Grf ;; <| D |>).
by apply cert_rf_D; basic_solver.
basic_solver.

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
arewrite (Crf ⨾ ⦗D⦘ ≡ Grf ;; <| D |>).
by apply cert_rf_D; basic_solver.
basic_solver.

}
done.
Qed.


Lemma cert_t_acq_thread l : t_acq certG sc thread l
  (covered T ∪₁ E ∩₁ NTid_ thread) ≡₁ t_acq G sc thread l (covered T).
Proof using All.
unfold t_acq, c_acq, urr.
rewrite !cert_W_, cert_F, cert_Sc, cert_hb, !seqA.

arewrite  (⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C ∪₁ E ∩₁ NTid_ thread⦘ ≡  ⦗C⦘ ⨾ ⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C⦘).
{ unfolder; splits; ins; desf; splits; eauto.
  by apply (init_covered TCCOH); split; eauto; apply (sub_E_in SUB).
  by apply (init_covered TCCOH); split; eauto; apply (sub_E_in SUB). }

arewrite (⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C⦘ ≡ ⦗C⦘ ⨾ ⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C⦘) at 2.
basic_solver 12.

arewrite ((Crelease ⨾ Crf)^? ⨾ ⦗C⦘ ≡ (Grelease ⨾ Grf)^? ⨾ ⦗C⦘).
{ arewrite (⦗C⦘ ≡ ⦗D⦘ ⨾ ⦗C⦘).
  { split.
    generalize C_in_D; basic_solver.
    basic_solver. }
  rewrite !crE; relsf.
  rewrite !seqA.
arewrite (Crf ⨾ ⦗D⦘ ≡ Grf ;; <| D |>).
by apply cert_rf_D; basic_solver.
  apply union_more; [done|].
  rewrite seq_eqvC at 1 2.
  seq_rewrite rf_covered; eauto. rewrite !seqA.
  arewrite (⦗I⦘ ≡ ⦗D⦘ ;; ⦗I⦘).
  { generalize I_in_D. clear. basic_solver. }
  seq_rewrite Crelease_D_eq_Grelease_D. by rewrite !seqA. }

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
arewrite (Crf ⨾ ⦗D⦘ ≡ Grf ;; <| D |>).
by apply cert_rf_D; basic_solver.
basic_solver.
}
done.
Qed.




(******************************************************************************)
(** **   *)
(******************************************************************************)



Lemma WF_cert : Wf certG.
Proof using All.
(* Proof using WF WF_SC TCCOH Grfe_E IT_new_co NEW_VAL OLD_VAL SAME ST_in_E S_in_W. *)
constructor; ins.
all: rewrite ?cert_sb, ?cert_R, ?cert_W, ?cert_same_loc, ?cert_E, ?cert_rf, ?cert_co, ?cert_R_ex.
all: try by apply WF.
- apply dom_helper_3. 
unfold Cert_rf.Crf.
rewrite (wf_new_rfE); try done.
rewrite (wf_rfE WF); try done. 
basic_solver.
- apply dom_helper_3. 
unfold Cert_rf.Crf.
rewrite (wf_new_rfD); try done.
rewrite (wf_rfD WF); try done. 
basic_solver.
- unfold Cert_rf.Crf.
rewrite (wf_new_rfl); try done.
rewrite (wf_rfl WF); try done. 
basic_solver.
- unfold Cert_rf.Crf.
rewrite dom_rf_D_helper; try edone.
  rewrite (wf_rfE WF).
  ins; unfolder; ins; desf; eauto.
  unfold funeq; ins.
  rewrite !OLD_VAL.
  by apply wf_rfv; eauto.
  by intro B; eapply B; eauto.
  by intro A; eapply A.
- apply Crff; try edone.
- apply wf_new_coE; [eapply IST_new_co|apply (wf_coE WF)]; edone.
- apply wf_new_coD; [eapply IST_new_co|apply (wf_coD WF)]; edone.
- apply wf_new_col; [eapply IST_new_co|apply (wf_coD WF)]; edone.
- apply new_co_trans.
  eapply IST_new_co; try edone.
  all: apply WF.
- intros. erewrite same_lab_u2v_loc; try edone.
  apply wf_new_co_total. 
  eapply IST_new_co; try edone.
  all: apply WF.
- apply new_co_irr. 
  eapply IST_new_co; try edone.
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
unfold complete; ins.
rewrite cert_R, cert_E.
unfolder; ins; desf.
destruct (classic (D x)).
- forward (eapply (complete_D) with (T:=T) (x:=x)); try edone.
  unfold Cert_rf.Crf.
  unfolder; ins; desf; eauto 20.
- forward (apply new_rf_comp); try edone.
  unfold Cert_rf.Crf; basic_solver 12.
Qed.

Lemma cert_coherece_detour_helper :
  irreflexive (Ghb ⨾ (sc ⨾ Ghb)^? ⨾ ⦗D⦘ ⨾ Grf⁻¹⨾ ⦗I ∩₁ NTid_ thread⦘ ⨾ cert_co ⨾ ⦗E ∩₁ W ∩₁ Tid_ thread \₁ I⦘).
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

Lemma coh_helper : irreflexive (Chb ⨾ (sc ⨾ Chb)^? ⨾ Ceco^?).
Proof using All.
  apply coh_helper_alt; rewrite cert_hb; relsf; unionL.
  { case_refl sc; [by apply hb_irr|].
    rewrite (wf_scD WF_SC); rotate 1.
    sin_rewrite (f_sc_hb_f_sc_in_ar WF).
    unfolder; ins; desc.
    eapply ACYC_EXT.
    eapply t_trans; [edone| apply t_step].
      by apply sc_in_ar. }
  { rewrite cert_rfe; relsf; unionL.
    { revert COH CSC; unfold coherence, coh_sc, eco.
      ie_unfolder. basic_solver 21. }
    generalize new_rf_hb. basic_solver 12. }
  { ins; rewrite cert_co_alt'; try edone; relsf; unionL.
    { revert COH CSC. unfold coherence, coh_sc, eco. basic_solver 21. }
    revert W_hb_sc_hb_to_I_NTid. basic_solver 21. }
  { rewrite cert_rfe; relsf; unionL.
    { rewrite (dom_rel_helper Grfe_E).
      unfold certG; ins; rewrite !seqA.
      rewrite (I_in_cert_co_base G T) at 1.
      arewrite (cert_co ⨾ ⦗cert_co_base G T⦘ ⊆ co G ⨾ ⦗cert_co_base G T⦘).
      eby eapply cert_co_I.
      revert COH CSC. unfold coherence, coh_sc, eco.
      ie_unfolder. basic_solver 21. }
    ins; rewrite cert_co_alt'; try edone; relsf; unionL.
    2: { generalize non_I_new_rf. basic_solver 16. }
    rewrite new_rf_in_furr.
    rotate 1.
    arewrite (Gfurr \ Gsb ⊆ Gfurr).
    arewrite (Gfurr ⨾ Ghb ⨾ (sc ⨾ Ghb)^? ⊆ Gfurr).
    { generalize (furr_hb_sc_hb WF WF_SC ACYC_EXT). basic_solver 21. }
    generalize (eco_furr_irr WF WF_SC CSC COH).
    unfold eco. basic_solver 21. }
  { unfold fr; ins; rewrite cert_co_alt'; try edone; unfold certG; ins.
    rewrite transp_union, transp_seq; relsf; unionL.
    { revert COH CSC. unfold coherence, coh_sc, eco, fr. ie_unfolder. basic_solver 21. }
    { rotate 1.
      arewrite (Gco ∩ cert_co ⊆ cert_co).
      rewrite (dom_r WF_cert.(wf_coD)), !seqA, cert_W.
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
      rewrite (I_in_cert_co_base G T) at 1.
      arewrite (cert_co ⨾ ⦗cert_co_base G T⦘ ⊆ co G ⨾ ⦗cert_co_base G T⦘).
      eby eapply cert_co_I.
      revert COH CSC. unfold coherence, coh_sc, eco, fr. ie_unfolder.
      basic_solver 21. }
    arewrite (Grfe ⨾ ⦗D⦘ ⊆ Grf) by ie_unfolder; basic_solver.
    rotate 1.
    arewrite (Grf ⨾ Ghb ⨾ (sc ⨾ Ghb)^? ⊆ Gfurr).
    { rewrite (furr_alt WF_SC). rewrite (dom_l (wf_rfD WF)). basic_solver 21. }
    unfold new_rf. basic_solver 21. }
  unfold fr; unfold certG; ins.
  rewrite transp_union, transp_seq; relsf; unionL.
  all: rewrite cert_co_alt'; try edone; relsf; unionL.
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
  sin_rewrite (f_sc_hb_f_sc_in_ar WF).
  unfolder; ins; desc.
  eapply ACYC_EXT.
  eapply t_trans; [edone| apply t_step].
  by apply sc_in_ar.
- generalize coh_helper; basic_solver 21.
Qed.

(*
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
*)

(******************************************************************************)
(** **   *)
(******************************************************************************)
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
(* TODO: move and improve hypothesis! *)
assert (W_ex_acq_sb_S1 : GW_ex_acq ⊆₁ I).
admit.

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
sin_rewrite Crfi_Acq.
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

(* TODO: move to ImmPropoerties.v *)
Lemma  cert_acyc_ext_helper : (sc ∪ certG.(rfe))⁺ ⊆ sc ∪ certG.(rfe).
Proof using All.
rewrite path_union.
generalize (sc_trans WF_SC); ins; relsf; unionL; [basic_solver|].
rewrite crE at 2; relsf; unionL.
- arewrite (sc^? ⨾ rfe certG ⊆ rfe certG ).
  rewrite crE; relsf; unionL; [basic_solver|].
  rewrite (dom_l (wf_rfeD WF_cert)), cert_W.
  rewrite (dom_r (wf_scD WF_SC)) at 1.
  type_solver.
  rewrite ct_begin, rtE; relsf; unionL; [basic_solver|].
  rewrite ct_begin.
  rewrite (dom_l (wf_rfeD WF_cert)).
  rewrite (dom_r (wf_rfeD WF_cert)).
  type_solver.
- rewrite (dom_r (wf_rfeD WF_cert)), cert_R.
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
- rewrite cert_acyc_ext_helper.
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


Lemma cert_imm_consistent : imm_consistent certG sc.
Proof using All.
red; splits; eauto using WF_SC_cert, cert_acyc_ext, cert_coh_sc, cert_complete, cert_coherence, cert_rmw_atomicity.
Qed.

(******************************************************************************)
(** **   *)
(******************************************************************************)

Lemma dom_fwbob_I : dom_rel (Gfwbob ⨾ ⦗C ∪₁ I⦘) ⊆₁ C ∪₁ I.
Proof using E_F_AcqRel_in_C E_to_S F_in_C RELCOV S_in_W TCCOH.
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
      forward (eapply dom_ppo_D); try edone.
      forward (eapply cert_detour_D); try edone.
      clear. unfolder; ins; desf. eapply H; basic_solver 42. }
    { unfold bob; relsf; unionL; splits; simpls.
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
    { rewrite cert_W_ex, cert_R, cert_Acq.
      admit. }
    rewrite cert_W_ex, cert_R, cert_Acq, cert_bob.
    admit. }
  { ins; rewrite cert_W_ex_acq.
    rewrite cert_sb. eapply tc_W_ex_sb_I; eauto.
    apply tc_coherent_implies_tc_coherent_alt; eauto. }
  simpls.
  arewrite (Grmw ⨾ ⦗I⦘ ⊆ ⦗D⦘ ⨾ Grmw ⨾ ⦗I⦘).
  { apply dom_rel_helper.
    rewrite rmw_in_ppo; auto.
    rewrite I_in_D.
    eapply dom_ppo_D; edone. }
  sin_rewrite cert_rfi_D. rewrite !seqA.
  arewrite_id ⦗D⦘. rewrite !seq_id_l.
  arewrite (Grfi ⊆ Grf).
  eapply rfrmw_I_in_I; eauto.
Admitted.

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

Lemma dom_data_Crfi_rmw_D_in_D : dom_rel ((Gdata ∪ Crfi ∪ Grmw)＊ ⨾ ⦗D⦘) ⊆₁ D.
Proof using Grfe_E TCCOH WF WF_SC.
  unfolder. ins. desf.
  induction H.
  3: intuition.
  2: basic_solver.
  desf.
  { eapply dom_data_D; try edone. basic_solver 10. }
  { assert ((Crfi ⨾ ⦗D⦘) x y) as AA.
    { basic_solver 10. }
    apply cert_rfi_D in AA. unfolder in AA. desf. } 
  eapply dom_rmw_D; try edone. basic_solver 10.
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

(*  assert ((Grf ⨾ ⦗D⦘ ∪ new_rf) ⨾ Grmw ≡ Grf ⨾ Grmw) as QQ.
  { rewrite (dom_rel_helper dom_rmw_in_D).
    rewrite wf_new_rfE. clear. basic_solver 10. }*)
  constructor.
  all: unfold eissued, ecovered; simpls.
  { apply TCCOH_cert. }
  { arewrite (I ∪₁ S ∩₁ Tid_ thread ⊆₁ E ∩₁ W).
    2: { unfold certG. unfold acts_set. basic_solver. }
    rewrite <- IST_new_co; try edone.
    rewrite IST_in_cert_co_base; try edone.
    basic_solver 10. }
  { eauto with hahn. }
  { rewrite cert_W_ex. generalize ST_in_W_ex.
    basic_solver. }
  { rewrite cert_F, cert_AcqRel, cert_sb, IST_in_S. admit. }
  { rewrite cert_sb, cert_Acq, cert_R.
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
(*   2: by rewrite QQ, cert_W_ex. *)
admit.
     }
  { rewrite Crppo_in_rppo.
    arewrite (Grppo ⨾ ⦗I ∪₁ S ∩₁ Tid_ thread⦘ ⊆
                  ⦗D⦘ ⨾ Grppo ⨾ ⦗I ∪₁ S ∩₁ Tid_ thread⦘).
    { apply dom_rel_helper.
      rewrite IST_in_S.
      apply dom_rppo_S_in_D. }
    arewrite ((Gdata ∪ Crfi ∪ Grmw)＊ ⨾ ⦗D⦘ ⊆ ⦗D⦘ ⨾ (Gdata ∪ Crfi ∪ Grmw)＊ ⨾ ⦗D⦘).
    { apply dom_rel_helper.
      eapply dom_data_Crfi_rmw_D_in_D. }
    rewrite <- !seqA.
    do 4 rewrite AuxRel.dom_seq.
    apply dom_cert_detour_rfe_D. }
  admit.
Admitted.

End CertExec.
