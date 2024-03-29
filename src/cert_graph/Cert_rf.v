From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.

From imm Require Import Events.
From imm Require Import Execution.
From imm Require Import Execution_eco.
From imm Require Import imm_bob imm_s_ppo.
From imm Require Import imm_s_hb.
From imm Require Import imm_s.
From imm Require Import imm_common_more.
From imm Require Import CertCOhelper.
From imm Require Import CombRelations.

(* From imm Require Import TraversalConfig. *)
(* From imm Require Import TraversalConfigAlt. *)
(* From imm Require Import TraversalConfigAltOld. *)
From imm Require Import FinExecution. 
From imm Require Import TraversalOrder.
From imm Require Import TLSCoherency.
From imm Require Import IordCoherency.
From imm Require Import SimClosure. 
From imm Require Import TlsEventSets.
From imm Require Import EventsTraversalOrder.
Require Import ExtTraversalConfig ExtTraversalProperties.
Require Import Cert_co.
Require Import Cert_D.
Require Import CertT.

Import ListNotations.

Set Implicit Arguments.

Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'NTid_' t" := (fun x => tid x <> t) (at level 1).

Section CertExec_rf.

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

Notation "'C'" := (covered T).
Notation "'I'" := (issued T).
Notation "'S'" := (reserved T). 

Variable thread : BinNums.positive.

Notation "'cert_co'" := (cert_co G T thread).

Notation "'D'" := (D G T thread).


Hypothesis WF : Wf G.
Hypothesis WF_SC : wf_sc G sc.
Hypothesis RELCOV : W ∩₁ Rel ∩₁ I ⊆₁ C.
(* Hypothesis TCCOH : tc_coherent G sc T. *)
(* Hypotheses *)
(*   (* (TCOH: tls_coherent G T) *) *)
(*   (* (ICOH: iord_coherent G sc T) *) *)
(*            (* (RCOH: reserve_coherent Gf T). *) *)
(*            . *)

Hypothesis ACYC_EXT : acyc_ext G sc.
Hypothesis CSC : coh_sc G sc.
Hypothesis COH : coherence G.
Hypothesis AT : rmw_atomicity G.

Hypothesis FIN: fin_exec G. 

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
(* TODO: are both of them needed? *)
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
Hypothesis RMWREX        : dom_rel Grmw ⊆₁ GR_ex.

Hypothesis INIT_TLS_T: init_tls G ⊆₁ T. 

(******************************************************************************)
(** Definition of the new rf edges   *)
(******************************************************************************)

Definition new_rf := Gfurr ∩ Gsame_loc ⨾ ⦗(E \₁ D) ∩₁ R⦘ \ cert_co ⨾ Gfurr.

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
  exfalso. eapply wf_cert_co_total in X; try edone.
  unfold new_rf in *. desf.
  all: unfolder in H12; unfolder in H5; basic_solver 40.
Qed.

Lemma cert_co_furr_fin (b: actid) (l: location):
  exists findom, forall c (REL: (cert_co ⨾ ⦗fun x : actid => Gfurr x b⦘)＊ (InitEvent l) c),
      In c findom.
Proof using WF S_in_W ST_in_E IT_new_co FIN.
  cdes FIN. destruct FIN as [findom FINDOM].
  exists (InitEvent l :: findom). 

  ins. 
  assert (A: (cert_co ⨾ ⦗fun x : actid => Gfurr x b⦘)^? (InitEvent l) c).
  { apply rt_of_trans; try done.
    apply transitiveI; unfolder; ins; desf; splits; eauto.
    eapply cert_co_trans; eauto. }
  
  unfolder in A; desf.
  { tauto. }
  eapply wf_cert_coE in A; try edone. unfolder in A; desc.
  eapply wf_cert_coD in A1; try edone. unfolder in A1; desc.
  eapply wf_cert_col in A3; try edone. unfold same_loc in *. unfolder in A.
  
  destruct (classic (is_init c)).
  2: { right. apply FINDOM. split; auto. }
  destruct c; [| done]. unfold "Gloc" in A3.
  rewrite !wf_init_lab in A3; auto. left. congruence.
Qed.


Lemma new_rf_comp : forall b (IN: ((E \₁ D) ∩₁ R) b) , exists a, new_rf a b.
Proof using WF WF_SC IT_new_co ST_in_E S_in_W FIN.
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

  edestruct (cert_co_furr_fin b l) as [findom FINDOM]; eauto.
  
  forward (eapply last_exists with (s:=cert_co ⨾ ⦗fun x=> Gfurr x b⦘) 
                                   (* (dom:= filterP (W_ l) (acts G)) *)
                                   (a:=(InitEvent l))).
  { eapply acyclic_mon.
    apply trans_irr_acyclic; [eapply cert_co_irr| eapply cert_co_trans]; try edone.
    basic_solver. }
  { eauto. }
  ins; desf.
  assert (A: (cert_co ⨾ ⦗fun x : actid => Gfurr x b⦘)^? (InitEvent l) b0).
  { apply rt_of_trans; try done.
    apply transitiveI; unfolder; ins; desf; splits; eauto.
    eapply cert_co_trans; eauto. }
  assert (Gloc b0 = Some l).
  { unfolder in A; desf.
    eapply wf_cert_col in A; try edone.
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
Proof using WF WF_SC IT_new_co ST_in_E S_in_W FIN.
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
  { unfold Cert_D.D. clear. unfolder. ins. desf; tauto. }
  clear -new_rf_hb WF.
  unfolder; ins; desf.
  rewrite <- H6 in H3. 
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
Proof using WF WF_SC ACYC_EXT COH COMP_ACQ CSC IT_new_co ST_in_E S_in_W.
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

- eapply eco_furr_irr; try edone.
  eexists; splits; [|eby apply new_rf_in_furr].
  unfold eco, fr.
  basic_solver 12.
- eapply H3.
  exists z; split; [| apply furr_alt; basic_solver 12].
  eapply I_co_in_cert_co; try edone.
  apply seq_eqv_l. split; auto.
    by apply I_in_cert_co_base.
Qed.

Lemma Grfi_nD_in_new_rf : Grfi ⨾ ⦗set_compl D⦘ ⊆ new_rf.
Proof using All.
  unfold new_rf.
  rewrite minus_inter_compl.
  apply inclusion_inter_r.
  { rewrite furr_alt; [|done].
    arewrite (Grfi ⊆ Grf).
    rewrite (dom_r (wf_rfE WF)) at 1.
    rewrite ((wf_rfD WF)) at 1.
    arewrite (Grf ⊆ Grf ∩ Grf) at 1.
    rewrite ((wf_rfl WF)) at 1.
    clear.
    basic_solver 21. }
  arewrite (Grfi ⨾ ⦗set_compl D⦘ ⊆ ⦗Tid_ thread⦘ ⨾ Grfi ⨾ ⦗set_compl D⦘).
  { forward (eapply dom_Grfi_nD_in_thread with (T:=T) (thread:=thread)); try edone.
    basic_solver. }
  arewrite (Grfi ⊆ Grf).
  rewrite cert_co_alt'; try edone.
  unfolder; ins; desf.
  intro; desf.
  eapply eco_furr_irr; try edone.
  exists z; splits; eauto.
  red; right. unfolder; ins; desf.
  exists z; splits; eauto; red.
  basic_solver.
Qed.

(******************************************************************************)
(** Definition of certification graph rf relation   *)
(******************************************************************************)

Definition cert_rf := Grf ⨾ ⦗D⦘ ∪ new_rf ⨾ ⦗set_compl (dom_rel Grmw)⦘
                          ∪ immediate cert_co ⨾ Grmw⁻¹ ⨾ ⦗set_compl D⦘.
Definition cert_rfe := cert_rf \ Gsb.
Definition cert_rfi := cert_rf ∩ Gsb.

Lemma cert_rfi_union_cert_rfe : cert_rf ≡ cert_rfi ∪ cert_rfe.
Proof using.
  unfold cert_rfi, cert_rfe.
  clear. unfolder. split; ins; desf; tauto.
Qed.

Lemma cert_rfE : cert_rf ≡ ⦗E⦘ ⨾ cert_rf ⨾ ⦗E⦘.
Proof using WF WF_SC IT_new_co ST_in_E S_in_W.
  apply dom_helper_3. 
  unfold cert_rf.
  rewrite (wf_new_rfE), (wf_rfE WF), (wf_rmwE WF), wf_cert_coE; eauto.
  clear. basic_solver.
Qed.

Lemma cert_rfD : cert_rf ≡ ⦗W⦘ ⨾ cert_rf ⨾ ⦗R⦘.
Proof using WF S_in_W ST_in_E IT_new_co.
  apply dom_helper_3. 
  unfold cert_rf.
  rewrite (wf_new_rfD), (wf_rfD WF), (wf_rmwD WF), wf_cert_coD; eauto.
  clear. basic_solver.
Qed.

Lemma cert_rfl : cert_rf ⊆ Gsame_loc.
Proof using WF S_in_W ST_in_E IT_new_co.
  unfold cert_rf.
  rewrite (wf_new_rfl), (wf_rfl WF).
  rewrite (wf_rmwl WF) at 2. 
  rewrite immediate_in.
  rewrite wf_cert_col; eauto.
  generalize (@same_loc_trans _ Glab).
  rewrite transp_sym_equiv; [|by apply same_loc_sym].
  clear. basic_solver 10.
Qed.

Lemma cert_rff : functional cert_rf⁻¹.
Proof using IT_new_co ST_in_E S_in_W WF WF_SC.
  unfold cert_rf.
  rewrite (dom_l (wf_rmwD WF)) at 2.
  rewrite (dom_r wf_new_rfE).
  rewrite transp_union. apply functional_union.
  3: { clear. basic_solver. }
  { apply functional_union.
    3: { unfolder; ins; desf. }
    { unfolder; ins; eapply (wf_rff WF); basic_solver. }
    eapply functional_mori.
    2: by apply wf_new_rff.
    red. clear. basic_solver. }
  forward (eapply imm_cert_co_tf); try edone.
  generalize (wf_rmwf WF).
  clear.
  unfold functional, transp, seq, eqv_rel.
  ins; desf.
  assert (z0 = z1) by eauto; subst; eauto.
Qed.


Lemma tls_events_empty_helper T' TLS
      (DISJ: TLS ∩₁ T' ⊆₁ ∅):
  event ↑₁ (TLS ∩₁ T') ≡₁ ∅. 
Proof using. split; [| basic_solver]. rewrite DISJ. basic_solver. Qed. 

Lemma cert_co_sb_irr':
  irreflexive (Cert_co.cert_co G (certT G T thread) thread ⨾ Gsb).
Proof using WF TCOH_rst_new_T S_in_W S_I_in_W_ex ST_in_E IT_new_co COH.
  clear detour_E W_hb_sc_hb_to_I_NTid ICOH_rst_new_T COMP_NTID. 
  apply cert_co_sb_irr; try edone.
  { apply TCOH_rst_new_T. } 
  all: try rewrite issued_certT; eauto.
  { rewrite reserved_certT, <- issued_certT, S_in_W.  
    rewrite issuedW; eauto. basic_solver. }
  { rewrite reserved_certT, <- issued_certT.
    rewrite issuedE, ST_in_E; eauto. basic_solver. }
  { rewrite reserved_certT. basic_solver. }
  rewrite reserved_certT. generalize S_I_in_W_ex. basic_solver. 
Qed. 
  

(* TODO: generalize? *)
(* see "rte'" local tactic for an example of 'unf' parameter *)
Ltac remove_tls_extension unf :=
  rewrite set_pair_alt, ?covered_union, ?issued_union, ?reserved_union;
  unf;
  repeat (rewrite tls_events_empty_helper; [| iord_dom_solver]);
  rewrite ?set_union_empty_r, ?set_union_empty_l. 

Lemma cert_rfe_alt : cert_rfe ≡ ⦗I⦘ ⨾ Grfe ⨾ ⦗D⦘ 
   ∪ ⦗I⦘ ⨾ (new_rf \ Gsb) ⨾ ⦗set_compl (dom_rel Grmw)⦘
   ∪ ⦗I⦘ ⨾ (immediate cert_co ⨾  Grmw⁻¹ \ Gsb) ⨾ ⦗set_compl D⦘.
Proof using WF_SC WF S_in_W S_I_in_W_ex 
  ST_in_E IT_new_co Grfe_E CSC COH ACYC_EXT I_in_S TCOH_rst_new_T.
  (* for some reason these hypotheses are required by Qed otherwise *)
  clear detour_E W_hb_sc_hb_to_I_NTid ICOH_rst_new_T COMP_NTID.
  (* clear TCOH_rst_new_T.  *)
  unfold Execution.rfe, cert_rfe, cert_rf.
  split; [|clear; basic_solver 21].
  rewrite !minus_union_l; unionL.
  { generalize Grfe_E; ie_unfolder; clear; basic_solver 21. }
  { rewrite wf_new_rfE at 1; try edone.
    arewrite (⦗E⦘ ⊆ ⦗E ∩₁ I⦘ ∪ ⦗E \₁ I⦘) at 1.
    { unfolder; ins; desf; tauto. }
    relsf; rewrite minus_union_l; unionL.
    clear; basic_solver 21.
    rewrite <- seqA.
    rewrite (non_I_new_rf); try edone.
    clear; basic_solver 21. }
  unionR right.
  rewrite <- !seqA. rewrite minus_eqv_r.
  rewrite !seqA.
  apply dom_rel_helper.
  rewrite immediate_in.
  rewrite (dom_l (wf_rmwE WF)) at 1; try edone.
  rewrite transp_seq, transp_eqv_rel.
  rewrite <- seqA, minus_eqv_r, !seqA.
  arewrite (⦗E⦘ ⨾ ⦗set_compl D⦘ ⊆ ⦗Tid_ thread⦘ ⨾ ⦗E⦘ ⨾ ⦗set_compl D⦘).
  { generalize (@E_minus_D_in_tid G T thread). clear; basic_solver 21. }
  arewrite (cert_co ⊆ ⦗ E ∩₁ W ⦘ ⨾ cert_co).
  { rewrite wf_cert_coD at 1; try edone.
    rewrite wf_cert_coE at 1; try edone.
    clear; basic_solver. }

  Ltac rte' := remove_tls_extension ltac:((try unfold issued at 2); (try unfold reserved at 2)). 

  arewrite (⦗E ∩₁ W⦘ ⊆ ⦗E ∩₁ W⦘ ⨾ ⦗set_compl Init⦘ ∪ ⦗Init ∩₁ E⦘).
  { unfolder; ins; desf.
    destruct (classic (is_init y)); eauto. }
  rewrite init_issued; try edone.
  rewrite <- IT_new_co at 1.
  rewrite !id_union, !seq_union_l, !seq_eqv, !minus_union_l, !seq_union_l, !dom_union; unionL.
  { clear. basic_solver. }
  2: { rewrite issued_certT. basic_solver. }
  rewrite wf_cert_coD at 1; try edone.
  rewrite (wf_rmwD WF) at 1.
  forward (eapply transp_rmw_sb); try edone; intro AA.
  forward (eapply cert_co_irr); try edone; intro BB.

  forward eapply cert_co_sb_irr' as CC. clear - AA BB CC WF.
  unfolder; ins; desf; exfalso.
  assert (A: (y = z \/ Gsb y z) \/ Gsb z y).
  { eapply (@tid_n_init_sb G). basic_solver. }
  desf.
  { type_solver. }
  assert (B: z1 = z \/ Gsb z1 z).
  { eapply AA; basic_solver. }
  desf; eauto.
  eapply CC.

  red. exists z1. split; eauto. 
  eapply hahn_inclusion_exp; [| apply H4].  
  unfold cert_co, cert_co_base.
  erewrite new_co_more; [reflexivity| ..]; auto.
  rewrite reserved_certT, issued_certT.
  basic_solver 10. 
Qed.

Lemma cert_rfe_D : cert_rfe ⨾ ⦗D⦘ ⊆ ⦗I⦘ ⨾ Grfe.
Proof using All.
  rewrite cert_rfe_alt.
  rewrite (dom_r wf_new_rfE).
  basic_solver 12.
Qed.

Lemma cert_rf_D : cert_rf ⨾ ⦗D⦘ ≡ Grf ⨾ ⦗D⦘.
Proof using WF WF_SC.
  unfold cert_rf.
  ins; split; [rewrite wf_new_rfE|].
  all: clear; basic_solver 20.
Qed.

Lemma dom_rf_D_helper: Grf ⨾ ⦗D⦘ ≡ ⦗D⦘ ⨾ Grf ⨾ ⦗D⦘.
Proof using Grfe_E WF TCOH_rst_new_T ICOH_rst_new_T.
  forward (eapply dom_rf_D with (T:=T) (thread:=thread)); try edone.
  basic_solver 12.
Qed.

Lemma cert_rfi_D : cert_rfi ⨾ ⦗D⦘ ⊆ ⦗D⦘ ⨾ Grfi ⨾ ⦗D⦘.
Proof using WF WF_SC Grfe_E TCOH_rst_new_T ICOH_rst_new_T.
  unfold cert_rfi, cert_rf.
  rewrite <- seq_eqv_inter_lr.
  seq_rewrite cert_rf_D. 
  rewrite dom_rf_D_helper.
  clear.
  basic_solver 12.
Qed.

Lemma dom_cert_rfe_in_I: dom_rel cert_rfe ⊆₁ I.
Proof using All.
rewrite cert_rfe_alt.
clear; basic_solver.
Qed.

Lemma non_I_cert_rf : ⦗set_compl I⦘ ⨾ cert_rf ⊆ Gsb.
Proof using All.
  rewrite cert_rfi_union_cert_rfe. unfold cert_rfi.
  rewrite (dom_rel_helper dom_cert_rfe_in_I).
  clear. basic_solver 10.
Qed.


Lemma Grfi_in_cert_rfi : Grfi ⊆ cert_rfi.
Proof using All.
  assert (sc_per_loc G) as GSPL.
  { by apply coherence_sc_per_loc. }
  arewrite (Grfi ⊆ Grfi ⨾ ⦗D ∪₁ set_compl D⦘).
  { clear; unfolder; ins; desf; tauto. }
  rewrite id_union; rewrite seq_union_r; unionL.
  { unfold rfi, cert_rfi, cert_rf.
    generalize cert_rf_D.
    clear; unfolder; ins; desf; unfolder; eauto 12. }
  arewrite (Grfi ⨾ ⦗set_compl D⦘ ⊆ Gsb ∩ (Grfi ⨾ ⦗set_compl D⦘)).
  { clear; unfold rfi. basic_solver. }
  arewrite (⦗set_compl D⦘ ⊆ 
            ⦗set_compl D⦘ ⨾ ⦗set_compl (dom_rel Grmw)⦘ ∪
            ⦗set_compl D⦘ ⨾ ⦗dom_rel Grmw⦘).
  { clear. unfolder. ins. desf. tauto. }
  rewrite !seq_union_r. rewrite inter_union_r. unionL.
  { sin_rewrite Grfi_nD_in_new_rf. 
    unfold rfi, cert_rfi, cert_rf.
    clear; simpl. basic_solver. }
  unfold cert_rfi.
  cut (Grfi ⨾ ⦗dom_rel Grmw⦘ ⨾ ⦗set_compl D⦘ ⊆ cert_rf).
  { clear. basic_solver 10. }
  unfold cert_rf. unionR right. 
  cut (Grfi ⨾ ⦗set_compl D⦘ ⨾ Grmw ⊆ immediate cert_co).
  { basic_solver 10. }
  arewrite (Grfi ⨾ ⦗set_compl D⦘ ⨾ Grmw ⊆ (Grfi ⨾ ⦗set_compl D ⦘⨾ Grmw) ∩ Gco).
  { forward (eapply rf_rmw_in_co); eauto.
    unfold rfi. clear. basic_solver 20. }
  rewrite Gco_in_cert_co_sym_clos; eauto.
  rewrite inter_union_r. unionL.
  2: { transitivity (fun _ _ : actid => False); [|basic_solver].
       arewrite_id ⦗set_compl D⦘. rewrite seq_id_l.
       rewrite (rfi_rmw_in_sb_loc WF).
       forward (eapply cert_co_irr); try edone; intro BB.
       forward (eapply cert_co_sb_irr with (T:=T)); eauto.
       clear. basic_solver. }
  arewrite (⦗set_compl D⦘ ⨾ Grmw ⊆ ∅₂).
  2: { clear. basic_solver. }
  rewrite (dom_rel_helper RMWREX).
  rewrite (dom_l (wf_rmwE WF)).
  seq_rewrite <- !id_inter.
  rewrite set_interA. rewrite Rex_in_D; eauto.
  clear. basic_solver.
Qed.

Lemma cert_rf_in_furr : cert_rf ⨾ ⦗set_compl (dom_rel Grmw)⦘ ⊆ Gfurr.
Proof using WF.
  unfold cert_rf.
  rewrite new_rf_in_furr.
  rewrite rf_in_furr with (sc := sc); auto. 
  unfolder; ins; desf; splits; eauto 20.
  exfalso; eauto.
Qed.

Lemma Grfe_in_inv_Gco_cr_cert_rf : Grfe ⊆ (Gco^{-1})^? ⨾ cert_rf.
Proof using All.
  arewrite (Grfe ⊆ Grfe ⨾ ⦗D ∪₁ set_compl D⦘).
  { clear; unfolder; ins; desf; tauto. }
  rewrite id_union; rewrite seq_union_r; unionL.
  { arewrite (Grfe ⊆ Grf).
    rewrite <- cert_rf_D. 
    basic_solver. }
  arewrite (⦗set_compl D⦘ ⊆ (⦗set_compl D⦘ ⨾ ⦗set_compl (dom_rel Grmw)⦘ ∪ ⦗set_compl D⦘ ⨾ ⦗(dom_rel Grmw)⦘)).
  { clear. unfolder. ins. desf. tauto. }
  rewrite !seq_union_r. unionL.
  {   arewrite (Grfe ⨾ ⦗set_compl D⦘ ⨾ ⦗set_compl (dom_rel Grmw)⦘ ⊆ ((Gco ∪ Gco^{-1})^? ⨾ cert_rf) ∩ Grfe ⨾ ⦗set_compl (dom_rel Grmw)⦘).
  { rewrite (wf_rfeE WF).
    rewrite (wf_rfeD WF).
    unfolder; ins; desf.
    splits; eauto.
    edestruct new_rf_comp as [a x1].
    { unfolder; ins; splits; eauto. }
    desf; exists a; splits; eauto.
    {
    assert (H55:=H5).
    eapply is_w_loc in H5; desc.
    assert (H11:=x1).
    apply wf_new_rfD in x1.
    unfolder in x1; desf.
    assert (H111:=x1).
    eapply is_w_loc in x1; desc.
    cut (x <> a -> Gco x a \/ Gco a x).
    { tauto. }
    eapply (wf_co_total WF).
    unfolder; splits; eauto.
    unfolder; splits; eauto.
    apply wf_new_rfE in H11; unfolder in H11; desf.
    apply wf_new_rfl in H11; unfolder in H11; desf.
    unfold rfe in H0; unfolder in H0; desf.
    apply (wf_rfl WF) in H0; unfolder in H0; desf.
    unfold same_loc in *; congruence. }
    unfold cert_rf; left; right.
    unfolder; ins; desf; splits; eauto. }
  rewrite crE at 1; relsf.
  rewrite !inter_union_l; relsf; unionL.
  
  1,3: basic_solver.
  transitivity (fun _ _ : actid => False); [|basic_solver].
  arewrite ((Gco ⨾ cert_rf) ∩ Grfe ⨾ ⦗set_compl (dom_rel Grmw)⦘ ⊆ (Gco ⨾ cert_rf  ⨾ ⦗set_compl (dom_rel Grmw)⦘) ∩ Grfe).
  { clear. basic_solver. }
  sin_rewrite cert_rf_in_furr.
  clear - COH WF WF_SC CSC.
  unfold rfe.
  unfolder; ins; desf.
  eapply eco_furr_irr; eauto.
  eexists; splits; eauto.
  apply fr_in_eco; eexists; splits; eauto. }

  rewrite (dom_l (wf_rmwE WF)). rewrite dom_eqv1.
  rewrite RMWREX. rewrite set_interC.
  rewrite Rex_in_D; eauto.
  clear. basic_solver.
Qed.

Lemma I_Grfe_in_inv_Gco_cr_cert_rf : Grfe ⊆ (cert_co ∩ Gco^{-1})^? ⨾ cert_rf.
Proof using All.
  rewrite (dom_rel_helper Grfe_E).
  arewrite (Grfe ⊆ Grfe ⨾ ⦗D ∪₁ set_compl D⦘).
  { clear; unfolder; ins; desf; tauto. }
  rewrite id_union; rewrite !seq_union_r; unionL.
  { clear; unfold cert_rf, rfe; simpl. basic_solver 12. }
  arewrite (Grfe ⊆ Grfe ∩ Grfe).
  rewrite Grfe_in_inv_Gco_cr_cert_rf at 1.
  rewrite !crE; relsf.
  rewrite !inter_union_l, seq_union_l, seq_union_r; unionL.
  { basic_solver. }
  unionR right.
  arewrite (Gco ⊆ Gco ∩ Gco) at 1.
  rewrite Gco_in_cert_co_sym_clos at 1; eauto.
  rewrite inter_union_l, transp_union, seq_union_l, inter_union_l, seq_union_l, seq_union_r.
  unionL.
  2: { basic_solver 21. }

  transitivity (fun _ _ : actid => False); [|basic_solver].
  arewrite (⦗set_compl D⦘ ⊆ (⦗set_compl D⦘ ⨾ ⦗set_compl (dom_rel Grmw)⦘ ∪ ⦗set_compl D⦘ ⨾ ⦗(dom_rel Grmw)⦘)).
  { clear. unfolder. ins. desf. tauto. }
  rewrite !seq_union_r. unionL.

  { unfold cert_rf.
    rewrite !seq_union_r, !inter_union_l, !seq_union_l.
    relsf; unionL.
    1,3: basic_solver.
    unfold new_rf.
    unfold rfe.
    rewrite rf_in_furr with (sc := sc); basic_solver. }

  unfold cert_rf.
  rewrite !seq_union_r, !inter_union_l, !seq_union_l.
  relsf; unionL.
  1,2: basic_solver.

  arewrite (Grfe ⊆ Grf).
  arewrite ((cert_co ∩ Gco)⁻¹ ⊆ cert_co⁻¹).
  rewrite <- !seqA.
  rewrite transp_cert_co_imm_cert_co'; eauto.
  rewrite !seqA.
  rewrite I_in_cert_co_base with (T:=T) (thread:=thread); eauto.
  seq_rewrite <- seq_eqv_inter_ll.

  arewrite (⦗cert_co_base G T thread⦘ ⨾ (cert_co⁻¹)^? ⊆ Gco⁻¹^?).
  { forward (eapply cert_co_I); eauto.
    clear. unfolder; ins; desf; eauto.
    right; eapply H; eauto. }
    unfolder; ins; desf.
  { forward (eapply rf_rmw_in_co); eauto.
    { apply coherence_sc_per_loc; eauto. }
    generalize (co_irr WF). basic_solver 21. }

  eapply COH.
  clear H1.
  eexists; splits.
  { apply sb_in_hb, (rmw_in_sb WF); eauto. }
  unfold eco.
  basic_solver 12.
Qed.

Lemma Grf_to_Acq_S_in_cert_rf : Grf ⨾ ⦗ dom_rel ((Grmw ⨾ Grfi)＊ ⨾ ⦗R∩₁Acq⦘ ⨾ Gsb ⨾ ⦗S⦘) ⦘ ⊆ cert_rf.
Proof using All.
  rewrite rfi_union_rfe at 1. rewrite seq_union_l. unionL.
  { rewrite Grfi_in_cert_rfi. arewrite (cert_rfi ⊆ cert_rf). clear. basic_solver. }
  arewrite (Grfe ⊆ Grfe ⨾ ⦗D ∪₁ set_compl D⦘).
  { clear; unfolder; ins; desf; tauto. }
  rewrite id_union; rewrite !seq_union_l, !seq_union_r; unionL.
  { clear; unfold cert_rf, rfe; simpl; basic_solver 12. }
  (*unfold certG; simpl; unionR right.*)
  rewrite (dom_rel_helper Grfe_E).
  arewrite (⦗I⦘ ⨾ Grfe ⊆ (Grfe) ∩ (⦗I⦘ ⨾ Grfe)).
  sin_rewrite I_Grfe_in_inv_Gco_cr_cert_rf.
  rewrite crE.
  rewrite seq_union_l, !inter_union_l, !seq_union_l; unionL.
  { basic_solver. }
  transitivity (fun _ _ : actid => False); [|basic_solver].
  arewrite (cert_co ∩ Gco⁻¹ ⊆ cert_co ∩ Gco⁻¹ ⨾ ⦗set_compl I⦘).
  { cut (codom_rel (cert_co ∩ Gco⁻¹) ⊆₁ set_compl I).
    basic_solver 21.
    rewrite cert_co_alt'; try edone. unfolder; ins; desf; eauto.
    exfalso; eapply (co_irr WF); eapply (co_trans WF); eauto. }
  rewrite (dom_l (wf_coE WF)) at 1.
  rewrite transp_seq; rels.
  rewrite seq_eqv_inter_rr, !seqA.
  seq_rewrite <- seq_eqv_inter_lr.
  rewrite !seqA.
  arewrite (⦗E⦘ ⨾ ⦗set_compl I⦘ ⨾ cert_rf ⨾ ⦗set_compl D⦘ ⊆ ⦗set_compl I⦘ ⨾ Gsb).
  { arewrite (⦗set_compl I⦘ ⊆ ⦗set_compl I⦘ ⨾ ⦗set_compl I⦘) by (clear; basic_solver).
    sin_rewrite non_I_cert_rf. clear. basic_solver. }
  rewrite coi_union_coe, transp_union, inter_union_r; relsf.
  rewrite inter_union_l; relsf.
  unionL.
  2: revert ETC_DR_R_ACQ_I; unfold detour; basic_solver 21.
  rewrite (dom_l (@wf_sbE G)) at 1.
  arewrite (⦗set_compl I⦘ ⨾ ⦗E⦘ ⊆ ⦗set_compl Init⦘).
  { generalize T_INIT_init_issued; basic_solver 21. }
  arewrite (⦗set_compl Init⦘ ⊆ ⦗set_compl Init⦘ ⨾ ⦗set_compl Init⦘).
  { basic_solver. }
  arewrite (Gcoi ⊆ Gsb).
  rewrite ninit_sb_same_tid.
  rewrite <- seqA.
  rewrite <- !seq_eqv_inter_rr.
  arewrite (Gsb⁻¹ ⨾ ⦗set_compl Init⦘ ⊆ same_tid).
  { generalize (@ninit_sb_same_tid G).
    unfold same_tid; unfolder; clear; ins; desf; symmetry; eauto. }
  arewrite (cert_co ∩ same_tid ⨾ same_tid ⊆ same_tid).
  { clear; generalize same_tid_trans; basic_solver 21. }
  generalize (rfe_n_same_tid WF COH).
  basic_solver 21.
Qed.

Lemma cert_rfi_to_Grfe_in_Gdetour : cert_rfi ⨾ ⦗ codom_rel Grfe ⦘ ⊆ Gdetour.
Proof using All.
  arewrite (Grfe ⊆ Grfe ∩ Grfe).
  rewrite I_Grfe_in_inv_Gco_cr_cert_rf at 1.
  unfold cert_rfi, rfe.
  unfolder; ins; desf.
  all: assert (x = z); [eby eapply cert_rff|]; subst.
  { exfalso; auto. }
  split; auto.
  unfold coe, rfe.
  eexists; do 2 split; eauto.
  intros HH.
  eapply cert_co_sb_irr; eauto.

  (* (* TODO: unify with cert_rfe_alt fragments *) *)
  (* 1-5: rte'. *)
  (* 1: rewrite <- IT_new_co at 2. 3: generalize ST_in_E. 5: generalize S_I_in_W_ex. *)
  (* 1-5: basic_solver 10.  *)
  red. eexists. split; eauto. 
Qed.

Lemma cert_rf_to_Acq_S_in_Grf : cert_rf ⨾ ⦗ dom_rel ((Grmw ⨾ Grfi)＊ ⨾ ⦗R∩₁Acq⦘ ⨾ Gsb ⨾ ⦗S⦘) ⦘ ⊆ Grf.
Proof using All.
  remember (dom_rel ((Grmw ⨾ Grfi)＊ ⨾ ⦗R ∩₁ Acq⦘ ⨾ Gsb ⨾ ⦗S⦘)) as X.
  arewrite (cert_rf ⨾ ⦗X⦘ ⊆ cert_rf ⨾ ⦗ codom_rel Grf ⦘ ⨾ ⦗X⦘).
  { subst X.  rewrite (dom_l (@wf_sbE G)), !seqA.
    arewrite (⦗R ∩₁ Acq⦘ ⨾ ⦗E⦘ ⊆ ⦗E ∩₁ R ∩₁ Acq⦘) by basic_solver.
    generalize COMP_R_ACQ_SB.
    basic_solver 21. }
  unfolder. ins. desf.
  assert (x0 = x); subst; auto.
  eapply cert_rff; eauto. red.
  eapply Grf_to_Acq_S_in_cert_rf.
  apply seq_eqv_r. by splits.
Qed.

Lemma cert_rf_to_Acq_nC_in_Grf : cert_rf ⨾ ⦗ dom_rel ((Grmw ⨾ Grfi)＊ ⨾ ⦗E∩₁R∩₁Acq \₁ C⦘) ⦘ ⊆ Grf.
Proof using All.
  arewrite (E∩₁R∩₁Acq \₁ C ⊆₁ R∩₁Acq ∩₁ dom_rel (Gsb ⨾ ⦗S⦘)).
  2: { rewrite id_inter. rewrite <- !seqA. rewrite dom_rel_eqv_dom_rel.
       rewrite !seqA. apply cert_rf_to_Acq_S_in_Grf. }
  rewrite E_to_S.
  rewrite crE, seq_union_l. rewrite S_in_W at 1.
  clear. type_solver 20.
Qed.

Lemma cert_rf_to_rmwrfi_Acq_in_Grf : cert_rf ⨾ ⦗ dom_rel ((Grmw ⨾ Grfi)＊ ⨾ ⦗Acq⦘) ⦘ ⊆ Grf.
Proof using All.
arewrite (⦗Acq⦘ ⊆ ⦗E∩₁R∩₁Acq \₁ C⦘ ∪ ⦗set_compl E ∪₁ set_compl R ∪₁ C⦘).
{ unfolder; ins; desf. clear. splits; eauto. 
destruct (classic (E y)); destruct (classic (is_r Glab y)); 
destruct (classic (C y)); eauto. }

relsf; rewrite id_union; relsf; unionL.
{ apply cert_rf_to_Acq_nC_in_Grf. }
rewrite !id_union; relsf.
rewrite !id_union; relsf; unionL.
{ rewrite (dom_r (wf_rfiE WF)).
rewrite (dom_r (cert_rfE)).
rewrite rtE.
rewrite <- !seqA, !inclusion_ct_seq_eqv_r.
basic_solver. }
{ rewrite (dom_r (wf_rfiD WF)).
rewrite (dom_r (cert_rfD)).
rewrite rtE.
rewrite <- !seqA, !inclusion_ct_seq_eqv_r.
basic_solver. }

arewrite (Grfi ⊆ Gsb).
rewrite (rmw_in_sb WF).
ins; relsf.

rewrite rewrite_trans, rt_of_trans; auto using sb_trans.
rewrite crE; relsf.
rewrite dom_sb_C_in_D; eauto.
rewrite C_in_D, set_unionK. rewrite cert_rf_D. basic_solver. 
Qed.

Lemma cert_rf_to_Acq_in_Grf : cert_rf ⨾ ⦗Acq⦘ ⊆ Grf.
Proof using All.
generalize cert_rf_to_rmwrfi_Acq_in_Grf.
rewrite rtE; basic_solver 12.
Qed.

Lemma cert_rfi_to_Acq_in_Grfi : cert_rfi ⨾ ⦗Acq⦘  ⊆ Grfi.
Proof using All.
generalize cert_rf_to_Acq_in_Grf.
unfold rfi, cert_rfi.
basic_solver 12.
Qed.

Lemma cert_rfe_to_Acq_in_Grfe : cert_rfe ⨾ ⦗Acq⦘ ⊆ Grfe.
Proof using All.
generalize cert_rf_to_Acq_in_Grf.
unfold rfe, cert_rfe.
basic_solver 12.
Qed.

Lemma cert_rfi_Grmw_in_Grfi_Grmw :
    cert_rfi ⨾ Grmw ⨾ (Grfi ⨾ Grmw)＊ ⨾ Grfi ⨾ ⦗Acq \₁ C⦘ ⊆
    Grfi ⨾ Grmw ⨾ (Grfi ⨾ Grmw)＊ ⨾ Grfi.
Proof using All.
  rewrite (dom_r (wf_rfiE WF)) at 2.
  rewrite E_to_S.
  rewrite (dom_r (wf_rfiD WF)) at 2. rewrite !seqA.
  arewrite (⦗R⦘ ⨾ ⦗C ∪₁ dom_rel (Gsb^? ⨾ ⦗S⦘)⦘ ⨾ ⦗Acq \₁ C⦘ ⊆
            ⦗dom_rel (Gsb ⨾ ⦗S⦘)⦘ ⨾ ⦗Acq⦘).
  { generalize S_in_W. clear. 
    ins. unfolder. ins. desf; splits; eauto.
    exfalso. apply S_in_W in H5. type_solver 10. }
  arewrite (Grmw ⨾ (Grfi ⨾ Grmw)＊ ⨾ Grfi ⨾ ⦗dom_rel (Gsb ⨾ ⦗S⦘)⦘ ⨾ ⦗Acq⦘ ⊆
            ⦗dom_rel ((Grmw ⨾ Grfi)＊ ⨾ ⦗R ∩₁ Acq⦘ ⨾ Gsb ⨾ ⦗S⦘)⦘ ⨾ Grmw ⨾ (Grfi ⨾ Grmw)＊ ⨾ Grfi).
  2: { hahn_frame.
       unfold cert_rfi, rfi.
       generalize cert_rf_to_Acq_S_in_Grf. basic_solver 20. }
  seq_rewrite <- !rt_seq_swap. rewrite !seqA.
  remember (Grmw ⨾ Grfi) as X.
  rewrite (dom_r (wf_rfiD WF)) at 1.
  assert (Grmw ⨾ Grfi ⊆ X) as AA by (by subst X).
  rewrite !seqA. sin_rewrite AA. seq_rewrite <- !ct_end.
  rewrite <- inclusion_t_rt.
  basic_solver 10.
Qed.

Lemma cert_rfi_Grmw_rt_in_Grfi_Grmw :
    (cert_rfi ⨾ Grmw)＊ ⨾ Grfi ⨾ ⦗Acq \₁ C⦘ ⊆
    (Grfi ⨾ Grmw)＊ ⨾ Grfi.
Proof using All.
  eapply rt_ind_left with (P:=fun r=> r ⨾ Grfi ⨾ ⦗Acq \₁ C⦘); eauto with hahn.
  { rewrite rtE. basic_solver 12. }
  intros k H.
  arewrite (⦗Acq \₁ C⦘ ⊆ ⦗Acq \₁ C⦘ ⨾ ⦗Acq \₁ C⦘) by (clear; basic_solver).
  sin_rewrite H. rewrite !seqA.
  rewrite cert_rfi_Grmw_in_Grfi_Grmw.
  rewrite <- !seqA. rewrite <- ct_begin. by rewrite inclusion_t_rt.
Qed.

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
    apply (dom_r (wf_releaseD WF)) in REL.
    clear -REL. unfolder in REL. desf. }
  assert (E w) as EW.
  { hahn_rewrite (wf_rfE WF) in A; unfolder in A; desf. }
  exists z; split; eauto.
  cut ((co G ⨾ ⦗cert_co_base G T thread⦘) w z).
  { basic_solver. }
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

Lemma cert_rmw_S_in_rf_rmw_S
      (COMP_RMW_S : dom_rel (Grmw ⨾ ⦗S⦘) ⊆₁ codom_rel Grf) :
  cert_rf ⨾ Grmw ⨾ ⦗S⦘ ≡ Grf ⨾ Grmw ⨾ ⦗S⦘.
Proof using All.
  split.
  2: { rewrite rfi_union_rfe. rewrite !seq_union_l.
       unionL.
       { rewrite Grfi_in_cert_rfi.
         clear. hahn_frame_r. unfold cert_rfi. basic_solver. }
       arewrite (Grfe ⨾ Grmw ⨾ ⦗S⦘ ⊆ Grfe ⨾ ⦗D⦘ ⨾ Grmw ⨾ ⦗S⦘).
       { unfold Cert_D.D. clear. basic_solver 20. }
       rewrite rfe_in_rf. seq_rewrite <- cert_rf_D.
       clear. hahn_frame_r. unfold cert_rfi. basic_solver. }
  arewrite (Grmw ⨾ ⦗S⦘ ⊆ ⦗codom_rel Grf⦘ ⨾ Grmw ⨾ ⦗S⦘) at 1
    by (by apply dom_rel_helper).
  rewrite rfi_union_rfe at 1. rewrite codom_union, id_union.
  rewrite !seq_union_l, !seq_union_r. unionL.
  2: { arewrite (⦗codom_rel Grfe⦘ ⨾ Grmw ⨾ ⦗S⦘ ⊆ ⦗D⦘ ⨾ Grmw ⨾ ⦗S⦘).
       { unfold Cert_D.D. clear. basic_solver 20. }
       seq_rewrite cert_rf_D. clear. basic_solver. }
  arewrite (Grfi ⊆ cert_rf ∩ Grf).
  2: { unfolder. ins. desf. eexists. splits; eauto.
       assert (x0 = x); subst; auto.
       eapply cert_rff; eauto. }
  apply inclusion_inter_r.
  2: by apply rfi_in_rf.
  rewrite Grfi_in_cert_rfi. unfold cert_rfi. clear. basic_solver.
Qed.

(*
Lemma cert_rf_sb: irreflexive (cert_rf ⨾ Ghb).
Proof using WF WF_SC CSC COH ACYC_EXT.
unfold cert_rf; relsf; unionL.
{ revert COH; unfold coherence.
rewrite rf_in_eco.
unfold  rfe; clear.
 basic_solver 12. }
{ rewrite new_rf_in_furr.
forward (eapply furr_hb_sc_hb_irr); try edone.
basic_solver 12. }
SearchAbout cert_co.
Qed.*)

End CertExec_rf.
