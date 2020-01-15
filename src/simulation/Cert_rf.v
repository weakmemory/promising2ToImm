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

Set Implicit Arguments.
Remove Hints plus_n_O.

Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'NTid_' t" := (fun x => tid x <> t) (at level 1).

Section CertExec_rf.

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
    apply trans_irr_acyclic; [eapply cert_co_irr| eapply cert_co_trans]; try edone.
    basic_solver. }
  { ins.
    assert (A: (cert_co ⨾ ⦗fun x : actid => Gfurr x b⦘)^? (InitEvent l) c).
    { apply rt_of_trans; try done.
      apply transitiveI; unfolder; ins; desf; splits; eauto.
      eapply cert_co_trans; eauto. }
    unfolder in A; desf.
    { apply in_filterP_iff; split; auto. }
    apply in_filterP_iff.
    eapply wf_cert_coE in A; try edone.
    unfolder in A; desc.
    eapply wf_cert_coD in A1; try edone.
    unfolder in A1; desc.
    eapply wf_cert_col in A3; try edone.
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
  { unfold Cert_D.D. clear. unfolder. ins. desf; tauto. }
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

- eapply eco_furr_irr; try edone.
  eexists; splits; [|eby apply new_rf_in_furr].
  unfold eco, fr.
  basic_solver 12.
- eapply H3.
  exists z; split; [| apply furr_alt; basic_solver 12].
  eapply I_co_in_cert_co; try edone.
  apply seq_eqv_l. split; auto.
  red. basic_solver.
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
  arewrite (Grfi ⨾ ⦗set_compl D⦘ ⊆ ⦗Tid_ thread⦘ ⨾ Grfi ⨾ ⦗set_compl D⦘).
  { forward (eapply dom_Grfi_nD_in_thread with (T:=T) (S:=S) (thread:=thread)); try edone.
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
                          ∪ immediate cert_co ;; Grmw⁻¹ ⨾ ⦗set_compl D⦘.
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
  rewrite R_ex_in_R at 2.
  clear. basic_solver.
Qed.

Lemma cert_rfl : cert_rf ⊆ Gsame_loc.
Proof using WF S_in_W ST_in_E IT_new_co.
  unfold cert_rf.
  rewrite (wf_new_rfl), (wf_rfl WF).
  rewrite (wf_rmwl WF) at 2. 
  rewrite AuxRel.immediate_in.
  rewrite wf_cert_col; eauto.
  generalize (@same_loc_trans _ Glab).
  rewrite AuxRel.transp_sym_equiv; [|by apply same_loc_sym].
  clear. basic_solver 10.
Qed.

Lemma cert_rff : functional cert_rf⁻¹.
Proof using IT_new_co ST_in_E S_in_W WF WF_SC.
  unfold cert_rf.
  rewrite (dom_l WF.(wf_rmwD)) at 2.
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
  generalize WF.(wf_rmwf).
  clear.
  unfold functional, transp, seq, eqv_rel.
  ins; desf.
  assert (z0 = z1) by eauto; subst; eauto.
Qed.

(* TODO: move to AuxRel *)
Lemma minus_eqv_r {A: Type} (r r': relation A) (s : A -> Prop) : r ;; <| s |> \ r' ≡ (r \ r') ;; <| s |>.
Proof.
basic_solver 21.
Qed.

Lemma cert_rfe_alt : cert_rfe ≡ ⦗I⦘ ⨾ Grfe ⨾ ⦗D⦘ 
   ∪ ⦗I⦘ ⨾ (new_rf \ Gsb) ⨾ ⦗set_compl (dom_rel Grmw)⦘
   ∪ ⦗I⦘ ⨾ (immediate cert_co ⨾  Grmw⁻¹ \ Gsb) ⨾ ⦗set_compl D⦘.
Proof using All.
  unfold Execution.rfe, cert_rfe, cert_rf.
  split; [|basic_solver 21].
  rewrite !minus_union_l; unionL.
  { generalize Grfe_E; ie_unfolder; basic_solver 21. }
  { rewrite wf_new_rfE at 1; try edone.
    arewrite (⦗E⦘ ⊆ ⦗E ∩₁ I⦘ ∪ ⦗E \₁ I⦘) at 1.
    { unfolder; ins; desf; tauto. }
    relsf; rewrite minus_union_l; unionL.
    basic_solver 21.
    rewrite <- seqA.
    rewrite (non_I_new_rf); try edone.
    basic_solver 21. }
  unionR right.
  rewrite <- !seqA. rewrite minus_eqv_r.
  rewrite !seqA.
  apply dom_rel_helper.
  rewrite AuxRel.immediate_in.
  rewrite (dom_l WF.(wf_rmwE)) at 1; try edone.
  rewrite transp_seq, transp_eqv_rel.
  rewrite <- seqA, minus_eqv_r, !seqA.
  arewrite (⦗E⦘ ⨾ ⦗set_compl D⦘ ⊆ ⦗Tid_ thread⦘ ⨾ ⦗E⦘ ⨾ ⦗set_compl D⦘).
  { generalize (@E_minus_D_in_tid G T S thread). basic_solver 21. }
  arewrite (cert_co ⊆ <| E ∩₁ W |> ;; cert_co).
  { rewrite wf_cert_coD at 1; try edone.
    rewrite wf_cert_coE at 1; try edone.
    clear; basic_solver. }
  arewrite (⦗E ∩₁ W⦘ ⊆ ⦗E ∩₁ W⦘ ;; ⦗set_compl Init⦘ ∪ ⦗Init ∩₁ E⦘).
  { unfolder; ins; desf.
    destruct (classic (is_init y)); eauto. }
  rewrite init_issued; try edone.
  rewrite <- IT_new_co at 1.
  rewrite !id_union, !seq_union_l, !seq_eqv, !minus_union_l, !seq_union_l, !dom_union; unionL.
  { clear. basic_solver. }
  2: basic_solver.
  rewrite wf_cert_coD at 1; try edone.
  rewrite WF.(wf_rmwD) at 1.
  unfolder; ins; desf; exfalso.
  assert (A: (y = z \/ Gsb y z) \/ Gsb z y).
  { eapply (@tid_n_init_sb G). basic_solver. }
  desf.
  { type_solver. }
  assert (B: z1 = z \/ Gsb z1 z).
  { eapply transp_rmw_sb; basic_solver. }
  desf.
  { by eapply cert_co_irr; try edone. }
  eapply cert_co_sb_irr; try edone; basic_solver.
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

Lemma dom_rf_D_helper: Grf ⨾ ⦗D⦘ ≡ ⦗D⦘ ;; Grf ⨾ ⦗D⦘.
Proof using Grfe_E TCCOH WF.
  forward (eapply dom_rf_D with (T:=T) (S:=S) (thread:=thread)); try edone.
  basic_solver 12.
Qed.

Lemma cert_rfi_D : cert_rfi ⨾ ⦗D⦘ ⊆ ⦗D⦘ ⨾ Grfi ⨾ ⦗D⦘.
Proof using WF WF_SC TCCOH Grfe_E.
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
  arewrite (Grfi ⊆ Grfi ⨾ ⦗D ∪₁ set_compl D⦘).
  { clear; unfolder; ins; desf; tauto. }
  rewrite id_union; rewrite seq_union_r; unionL.
  { unfold rfi, cert_rfi, cert_rf.
    generalize cert_rf_D.
    clear; unfolder; ins; desf; unfolder; eauto 12. }
  arewrite (Grfi ⨾ ⦗set_compl D⦘ ⊆ Gsb ∩ (Grfi ⨾ ⦗set_compl D⦘)).
  { clear; unfold rfi. basic_solver. }
  arewrite (⦗set_compl D⦘ ⊆ 
  (⦗set_compl D⦘ ;; ⦗set_compl (dom_rel Grmw)⦘ ∪ ⦗dom_rel Grmw⦘)).
  { clear. unfolder. ins. desf. tauto. }
  rewrite !seq_union_r. rewrite inter_union_r. unionL.
  { sin_rewrite Grfi_nD_in_new_rf. 
    unfold rfi, cert_rfi, cert_rf.
    clear; simpl. basic_solver. }
    
Admitted.

(* TODO: move to CombRelations.v *)
Lemma rf_in_furr : Grf ⊆ Gfurr.
Proof using WF.
  unfold furr, urr.
  do 2 rewrite (dom_l WF.(wf_rfD)).
  unfolder; ins; desc.
  apply is_w_loc in H1; desf.
  basic_solver 21.
Qed.

(*
Lemma cert_rf_in_furr : cert_rf ;; ⦗set_compl GR_ex⦘ ⊆ Gfurr.
Proof using WF.
  unfold cert_rf.
  rewrite new_rf_in_furr.
  rewrite rf_in_furr.
  basic_solver.
Qed.
*)

Lemma Grfe_in_inv_Gco_cr_cert_rf : Grfe ⊆ (Gco^{-1})^? ;; cert_rf.
Proof using All.
  arewrite (Grfe ⊆ Grfe ⨾ ⦗D ∪₁ set_compl D⦘).
  { clear; unfolder; ins; desf; tauto. }
  rewrite id_union; rewrite seq_union_r; unionL.
  { arewrite (Grfe ⊆ Grf).
    rewrite <- cert_rf_D. 
    basic_solver. }
  arewrite (⦗set_compl D⦘ ⊆ (⦗set_compl D⦘ ;; ⦗set_compl GR_ex⦘ ∪ ⦗GR_ex⦘)).
  { clear. unfolder. ins. desf. tauto. }
  rewrite !seq_union_r. unionL.
  { admit. }
  admit.  
    (*
  arewrite (Grfe ⨾ ⦗set_compl D⦘ ⊆ ((Gco ∪ Gco^{-1})^? ;; cert_rf) ∩ Grfe).
  { rewrite WF.(wf_rfeE).
    rewrite WF.(wf_rfeD).
    unfolder; ins; desf.
    splits; eauto.
    exploit new_rf_comp; unfolder; ins; splits; eauto.
    desf; exists a; splits; eauto.
    2: unfold cert_rf; basic_solver.
    assert (H44:=H4).
    eapply is_w_loc in H4; desc.
    assert (H11:=x1).
    apply wf_new_rfD in x1.
    unfolder in x1; desf.
    assert (H111:=x1).
    eapply is_w_loc in x1; desc.
    cut (x <> a -> Gco x a \/ Gco a x).
    { tauto. }
    eapply WF.(wf_co_total).
    unfolder; splits; eauto.
    unfolder; splits; eauto.
    apply wf_new_rfE in H11; unfolder in H11; desf.
    apply wf_new_rfl in H11; unfolder in H11; desf.
    unfold rfe in H0; unfolder in H0; desf.
    apply WF.(wf_rfl) in H0; unfolder in H0; desf.
    unfold same_loc in *; congruence. }
  rewrite crE at 1; relsf.
  rewrite !inter_union_l; unionL.
  1,3: basic_solver.
  transitivity (fun _ _ : actid => False); [|basic_solver].
  rewrite cert_rf_in_furr.
  clear - COH WF WF_SC CSC.
  unfold rfe.
  unfolder; ins; desf.
  eapply eco_furr_irr; eauto.
  eexists; splits; eauto.
  apply fr_in_eco; eexists; splits; eauto.
Qed.*)
Admitted.

Lemma I_Grfe_in_inv_Gco_cr_cert_rf : Grfe ⊆ (cert_co ∩ Gco^{-1})^? ;; cert_rf.
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
  arewrite (⦗set_compl D⦘ ⊆ (⦗set_compl D⦘ ;; ⦗set_compl GR_ex⦘ ∪ ⦗GR_ex⦘)).
  { clear. unfolder. ins. desf. tauto. }
  rewrite !seq_union_r. unionL.
{ admit.
  (*
  rewrite WF.(wf_coE).
  rewrite WF.(wf_coD).
  arewrite (Gco ⊆ Gco ∩ Gsame_loc) at 1.
  { generalize WF.(wf_col); basic_solver. }
  unfolder; ins; desf.
  edestruct is_w_loc; eauto.
  exists z0; splits; eauto 10.
  eapply tot_ex.
  { apply wf_new_co_total.
    eapply IST_new_co; try edone.
    all: apply WF. }
  { unfolder; eauto. }
  { unfolder; eauto. }
  2: by intro; subst; eapply WF.(co_irr); eauto.
  unfold cert_rf in H3.
  unfolder in H3; desf.
  intro HH.
  apply H3.
  eexists; splits; eauto.
  apply rf_in_furr; unfold rfe in *; unfolder in H2; desf; eauto.
  *) }
  admit.
Admitted.

Lemma Grf_to_Acq_S_in_cert_rf : Grf ;; <| dom_rel ((Grmw ⨾ Grfi)^* ⨾ ⦗R∩₁Acq⦘ ⨾ Gsb ⨾ ⦗S⦘) |> ⊆ cert_rf.
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
  arewrite (cert_co ∩ Gco⁻¹ ⊆ cert_co ∩ Gco⁻¹ ;; <|set_compl I|>).
  { cut (codom_rel (cert_co ∩ Gco⁻¹) ⊆₁ set_compl I).
    basic_solver 21.
    rewrite cert_co_alt'; try edone. unfolder; ins; desf; eauto.
    exfalso; eapply WF.(co_irr); eapply WF.(co_trans); eauto. }
  rewrite (dom_l WF.(wf_coE)) at 1.
  rewrite transp_seq; rels.
  rewrite AuxRel.seq_eqv_inter_rr, !seqA.
  seq_rewrite <- seq_eqv_inter_lr.
  rewrite !seqA.
  arewrite (⦗E⦘ ⨾ ⦗set_compl I⦘ ⨾ cert_rf ⨾ ⦗set_compl D⦘ ⊆ ⦗set_compl I⦘ ⨾ Gsb).
  { arewrite (⦗set_compl I⦘ ⊆ ⦗set_compl I⦘ ;; ⦗set_compl I⦘) by (clear; basic_solver).
    sin_rewrite non_I_cert_rf. clear. basic_solver. }
  rewrite coi_union_coe, transp_union, inter_union_r; relsf.
  rewrite inter_union_l; relsf.
  unionL.
  2: revert ETC_DR_R_ACQ_I; unfold detour; basic_solver 21.
  rewrite (dom_l (@wf_sbE G)) at 1.
  arewrite (⦗set_compl I⦘ ⨾ ⦗E⦘ ⊆ ⦗set_compl Init⦘).
  { generalize init_issued; basic_solver 21. }
  arewrite (⦗set_compl Init⦘ ⊆ ⦗set_compl Init⦘ ;; ⦗set_compl Init⦘).
  { basic_solver. }
  arewrite (Gcoi ⊆ Gsb).
  rewrite ninit_sb_same_tid.
  rewrite <- seqA.
  rewrite <- !AuxRel.seq_eqv_inter_rr.
  arewrite (Gsb⁻¹ ⨾ ⦗set_compl Init⦘ ⊆ same_tid).
  { generalize (@ImmProperties.ninit_sb_same_tid G).
    unfold same_tid; unfolder; clear; ins; desf; symmetry; eauto. }
  arewrite (cert_co ∩ same_tid ⨾ same_tid ⊆ same_tid).
  { clear; generalize (ImmProperties.same_tid_trans); basic_solver 21. }
  generalize (rfe_n_same_tid WF COH).
  basic_solver 21.
Qed.

Lemma cert_rfi_to_Grfe_in_Gdetour : cert_rfi ;; <| codom_rel Grfe |> ⊆ Gdetour.
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
  basic_solver.
Qed.

Lemma cert_rf_to_Acq_S_in_Grf : cert_rf ;; <| dom_rel ((Grmw ⨾ Grfi)^* ⨾ ⦗R∩₁Acq⦘ ⨾ Gsb ⨾ ⦗S⦘) |> ⊆ Grf.
Proof using All.
  remember (dom_rel ((Grmw ⨾ Grfi)＊ ⨾ ⦗R ∩₁ Acq⦘ ⨾ Gsb ⨾ ⦗S⦘)) as X.
  arewrite (cert_rf ⨾ ⦗X⦘ ⊆ cert_rf ⨾ <| codom_rel Grf |> ⨾ ⦗X⦘).
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

Lemma cert_rf_to_Acq_nC_in_Grf : cert_rf ;; <| dom_rel ((Grmw ⨾ Grfi)^* ⨾ ⦗E∩₁R∩₁Acq \₁ C⦘) |> ⊆ Grf.
Proof using All.
  arewrite (E∩₁R∩₁Acq \₁ C ⊆₁ R∩₁Acq ∩₁ dom_rel (Gsb ⨾ ⦗S⦘)).
  2: { rewrite id_inter. rewrite <- !seqA. rewrite dom_rel_eqv_dom_rel.
       rewrite !seqA. apply cert_rf_to_Acq_S_in_Grf. }
  rewrite E_to_S.
  rewrite crE, seq_union_l. rewrite S_in_W at 1.
  clear. type_solver 20.
Qed.

Lemma cert_rf_to_Acq_in_Grf : cert_rf ;; <| dom_rel ((Grmw ⨾ Grfi)^* ⨾ ⦗Acq⦘) |> ⊆ Grf.
Proof using All.
  (* TODO: easy w/ the previous lemma. *)
Admitted.

Lemma cert_rfi_to_Acq_in_Grf : cert_rfi ⨾ ⦗Acq⦘  ⊆ Grfi.
Proof using All.
  (* TODO: easy w/ the previous lemma. *)
Admitted.

Lemma cert_rfi_Grmw_in_Grfi_Grmw :
    cert_rfi ⨾ Grmw ⨾ (Grfi ⨾ Grmw)＊ ⨾ Grfi ⨾ ⦗Acq \₁ C⦘ ⊆
    Grfi ⨾ Grmw ⨾ (Grfi ⨾ Grmw)＊ ⨾ Grfi.
Proof using All.
  rewrite (dom_r WF.(wf_rfiE)) at 2.
  rewrite E_to_S.
  rewrite (dom_r WF.(wf_rfiD)) at 2. rewrite !seqA.
  arewrite (⦗R⦘ ⨾ ⦗C ∪₁ dom_rel (Gsb^? ⨾ ⦗S⦘)⦘ ⨾ ⦗Acq \₁ C⦘ ⊆
            ⦗dom_rel (Gsb ⨾ ⦗S⦘)⦘ ⨾ ⦗Acq⦘).
  { generalize S_in_W. clear. 
    ins. unfolder. ins. desf; splits; eauto.
    exfalso. apply S_in_W in H5. type_solver 10. }
  arewrite (Grmw ⨾ (Grfi ⨾ Grmw)＊ ⨾ Grfi ⨾ ⦗dom_rel (Gsb ⨾ ⦗S⦘)⦘ ⨾ ⦗Acq⦘ ⊆
            ⦗dom_rel ((Grmw ⨾ Grfi)＊ ⨾ ⦗R ∩₁ Acq⦘ ⨾ Gsb ⨾ ⦗S⦘)⦘ ;; Grmw ⨾ (Grfi ⨾ Grmw)＊ ⨾ Grfi).
  2: { hahn_frame.
       unfold cert_rfi, rfi.
       generalize cert_rf_to_Acq_S_in_Grf. basic_solver 20. }
  seq_rewrite <- !rt_seq_swap. rewrite !seqA.
  remember (Grmw ⨾ Grfi) as X.
  rewrite (dom_r WF.(wf_rfiD)) at 1.
  assert (Grmw ⨾ Grfi ⊆ X) as AA by (by subst X).
  rewrite !seqA. sin_rewrite AA. seq_rewrite <- !ct_end.
  rewrite <- inclusion_t_rt.
  basic_solver 10.
Qed.

Lemma cert_rfi_Grmw_rt_in_Grfi_Grmw :
    (cert_rfi ⨾ Grmw)＊ ⨾ Grfi ⨾ ⦗Acq \₁ C⦘ ⊆
    (Grfi ⨾ Grmw)＊ ⨾ Grfi.
Proof using All.
  eapply rt_ind_left with (P:=fun r=> r ;; Grfi ;; ⦗Acq \₁ C⦘); eauto with hahn.
  { rewrite rtE. basic_solver 12. }
  intros k H.
  arewrite (⦗Acq \₁ C⦘ ⊆ ⦗Acq \₁ C⦘ ;; ⦗Acq \₁ C⦘) by (clear; basic_solver).
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
    apply (dom_r WF.(wf_releaseD)) in REL.
    clear -REL. unfolder in REL. desf. }
  assert (E w) as EW.
  { hahn_rewrite (wf_rfE WF) in A; unfolder in A; desf. }
  exists z; split; eauto.
  cut ((co G ⨾ ⦗cert_co_base G T⦘) w z).
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

End CertExec_rf.
