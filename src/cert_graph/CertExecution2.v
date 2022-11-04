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
From imm Require Import FairExecution.

From imm Require Import AuxRel2.
From imm Require Import TraversalOrder.
From imm Require Import TLSCoherency.
From imm Require Import IordCoherency.
From imm Require Import SimClosure. 
From imm Require Import TlsEventSets.
Require Import ExtTraversalConfig ExtTraversalProperties.
From imm Require Import AuxRel.
From imm Require Import FinExecution.
Require Import ExtTraversalConfig.
From imm Require Import AuxDef.

Require Import CertT.
Require Import Cert_co.
Require Import Cert_D.
Require Import Cert_rf.

Set Implicit Arguments.

Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'NTid_' t" := (fun x => tid x <> t) (at level 1).

Section CertExec.

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
(* Hypothesis TCCOH : tc_coherent G sc T. *)
(* Hypothesis TCOH : tls_coherent G T. *)
(* Hypothesis ICOH : iord_coherent G sc T. *)
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

(* Hypothesis TCCOH_rst_new_T : tc_coherent G sc (mkTC (C ∪₁ (E ∩₁ NTid_ thread)) I). *)
Hypothesis TCOH_rst_new_T : tls_coherent G (certT G T thread).
Hypothesis ICOH_rst_new_T : iord_coherent G sc (certT G T thread).

Hypothesis S_in_W : S ⊆₁ W.
Hypothesis RPPO_S : dom_rel ((Gdetour ∪ Grfe) ⨾ (Gdata ∪ Grfi ∪ Grmw)＊ ⨾ Grppo ⨾ ⦗S⦘) ⊆₁ I.
Hypothesis RMW_S : dom_rel ((Gdetour ∪ Grfe) ⨾ Grmw ⨾ ⦗S⦘) ⊆₁ I.
Hypothesis ST_in_E : S ∩₁ Tid_ thread ⊆₁ E.
Hypothesis I_in_S : I ⊆₁ S.

Hypothesis F_in_C : E ∩₁ F ∩₁ Acq/Rel ⊆₁ C.

Hypothesis S_I_in_W_ex : (S ∩₁ Tid_ thread) \₁ I ⊆₁ W_ex G.

Hypothesis ETC_DR_R_ACQ_I : dom_rel ((Gdetour ∪ Grfe) ⨾ (Grmw ⨾ Grfi)＊ ⨾ ⦗R∩₁Acq⦘ ⨾ Gsb ⨾ ⦗S⦘) ⊆₁ I.

Hypothesis COMP_R_ACQ_SB : dom_rel ((Grmw ⨾ Grfi)＊ ⨾ ⦗E ∩₁ R ∩₁ Acq⦘) ⊆₁ codom_rel Grf.

Hypothesis INIT_TLS_T: init_tls G ⊆₁ T. 
(******************************************************************************)
(** The new label function   *)
(******************************************************************************)

Variable lab' : actid -> label.
Hypothesis SAME : same_lab_u2v lab' Glab.
Hypothesis NEW_VAL : forall r w (RF: cert_rf w r), val lab' w = val lab' r.
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
    {| acts_set := (acts_set G);
       threads_set := threads_set G;
       lab := lab' ;
       rmw := Grmw ;
       data := Gdata ;
       addr := Gaddr ;
       ctrl := Gctrl ;
       rmw_dep := Grmw_dep ;
       rf := cert_rf ;
       co := cert_co ;
    |}.

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
(** properties of the ceritifcation execution   *)
(******************************************************************************)

Lemma cert_lab_init : forall a (IN: is_init a), lab' a = Glab a.
Proof using SAME OLD_VAL TCOH_rst_new_T. 
ins; cut (val lab' a = Gval a).
- assert (same_label_u2v (lab' a) (Glab a)) as SS by (by apply SAME).
  unfold same_label_u2v in *. unfold val; desf; desf.
  all: intros HH; inv HH.
- apply OLD_VAL.
  unfolder; desf.
  intros [Ea NDa]. destruct NDa.
  apply D_init; basic_solver.   
Qed.

Lemma cert_E : (acts_set certG) ≡₁ E.
Proof using. unfold certG; vauto. Qed.
Lemma cert_sb : (sb certG) ≡ Gsb.
Proof using. by unfold Execution.sb; rewrite cert_E. Qed.
Lemma cert_W_ex : (W_ex certG) ≡₁ GW_ex.
Proof using. unfold Execution.W_ex; ins. Qed.
Lemma cert_rmw : Crmw ≡ Grmw.
Proof using. by unfold certG; ins. Qed.
Lemma cert_rf_eq : Crf ≡ cert_rf.
Proof using. by unfold certG; ins. Qed.
Lemma cert_rfi_eq : Crfi ≡ cert_rfi.
Proof using. by unfold certG; ins. Qed.
Lemma cert_rfe_eq : Crfe ≡ cert_rfe.
Proof using. by unfold certG; ins. Qed.

Lemma cert_fwbob : (fwbob certG) ≡ Gfwbob.
Proof using SAME. 
unfold imm_bob.fwbob.
rewrite cert_W, cert_F, cert_Rel, cert_AcqRel.
by rewrite cert_sb, cert_same_loc.
Qed.

Lemma cert_bob : (bob certG) ≡ Gbob.
Proof using SAME. 
unfold imm_bob.bob.
by rewrite cert_R, cert_Acq, cert_fwbob, cert_sb.
Qed.

Lemma cert_W_ex_acq : (W_ex certG) ∩₁ is_xacq lab' ≡₁ GW_ex ∩₁ xacq.
Proof using SAME.
unfold Execution.W_ex.
by rewrite cert_xacq; ins.
Qed.

Lemma WF_cert : Wf certG.
Proof using All.
(* Proof using WF WF_SC TCCOH Grfe_E IT_new_co NEW_VAL OLD_VAL SAME ST_in_E S_in_W. *)
  constructor; ins.
  all: rewrite ?cert_sb, ?cert_R, ?cert_W, ?cert_same_loc, ?cert_E, ?cert_rf, ?cert_co, ?cert_R_ex.
  all: try by apply WF.
  { eby apply cert_rfE. }
  { eby apply cert_rfD. }
  { eby apply cert_rfl. }
  { red. ins. by apply NEW_VAL. }
  (* apply OLD_VAL. *)
  (* unfold Cert_rf.cert_rf. *)
  (* rewrite dom_rf_D_helper; try edone. *)
  (* rewrite (wf_rfE WF). *)
  (* ins; unfolder; ins; desf; eauto. *)
  (* { rewrite !OLD_VAL. *)
  (*   { by apply wf_rfv; eauto. } *)
  (*   { by intro B; eapply B; eauto. } *)
  (*     by intro A; eapply A. } *)
  { apply cert_rff; try edone. }
  { apply wf_new_coE; [eapply IST_new_co|apply (wf_coE WF)]; edone. }
  { apply wf_new_coD; [eapply IST_new_co|apply (wf_coD WF)]; edone. }
  { apply wf_new_col; [eapply IST_new_co|apply (wf_coD WF)]; edone. }
  { apply new_co_trans.
    eapply IST_new_co; try edone.
    all: apply WF. }
  { intros. erewrite same_lab_u2v_loc; try edone.
    apply wf_new_co_total. 
    eapply IST_new_co; try edone.
    all: apply WF. }
  { apply new_co_irr. 
    eapply IST_new_co; try edone.
    all: apply WF. }
  { ins; desf; apply cert_E.
    apply (wf_init WF); exists b; splits; [apply cert_E| rewrite <- cert_loc]; done. }
  ins; rewrite cert_lab_init.
  apply (wf_init_lab WF). by unfold is_init.
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

Lemma cert_complete (FIN: fin_exec G) (FAIR: mem_fair G):
  complete certG.
Proof using All.
  unfold complete; ins.
  rewrite cert_R.
  (* rewrite cert_E. *)
  unfold Cert_rf.cert_rf.
  arewrite (E ∩₁ R ⊆₁ E ∩₁ R ∩₁ D ∪₁ 
                      E ∩₁ R ∩₁ set_compl (dom_rel Grmw) ∩₁ set_compl D ∪₁ 
                      E ∩₁ R ∩₁ (dom_rel Grmw) ∩₁ set_compl D).
  { unfolder; ins; desf. 
    destruct (classic (D x)); destruct (classic ((dom_rel Grmw) x)); eauto 10. }
  unionL.
  { unfolder; ins; desf.
    forward (eapply (complete_D) with (T:=T) (x:=x)); try edone.
    { erewrite <- coveredE; [..| apply TCOH_rst_new_T]; auto.
      rewrite covered_certT. basic_solver. }
    { erewrite <- issuedE; [..| apply TCOH_rst_new_T]; auto.
      rewrite issued_certT. basic_solver. }
    unfold Cert_rf.cert_rf.
    unfolder; ins; desf; eauto 20. }
  { unfolder; ins; desf.
    forward (apply new_rf_comp); try edone. 
    unfold Cert_rf.cert_rf; basic_solver 12. }
  unfolder; ins; desf.
  assert (AA: exists z, (immediate cert_co) z y).
  { eapply (imm_cert_co_inv_exists) with (T:=T); eauto.
    apply (wf_rmwD WF) in H1; unfolder in H1; desf.
    apply (wf_rmwE WF) in H3; unfolder in H3; desf.
    apply (rmw_non_init_lr WF) in H5; unfolder in H5; desf. }
  desf; eexists; eauto.
Qed.


End CertExec.
