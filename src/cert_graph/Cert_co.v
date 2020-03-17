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
From imm Require Import AuxDef.


(* From imm Require Import Events Execution Execution_eco *)
(*      imm_bob imm_s_ppo imm_s imm_s_hb CombRelations AuxDef. *)

From imm Require Import AuxRel2.
From imm Require Import TraversalConfig.
From imm Require Import TraversalConfigAlt.
From imm Require Import TraversalConfigAltOld.
Require Import ExtTraversalConfig.

Set Implicit Arguments.
Remove Hints plus_n_O.

Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'NTid_' t" := (fun x => tid x <> t) (at level 1).

Section CertExec_CO.

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
Hypothesis S_in_W : S ⊆₁ W.
Hypothesis ST_in_E : S ∩₁ Tid_ thread ⊆₁ E.
Hypothesis I_in_S : I ⊆₁ S.
Hypothesis S_I_in_W_ex : (S ∩₁ Tid_ thread) \₁ I ⊆₁ W_ex G.

Definition cert_co_base := codom_rel (<|I ∪₁ S ∩₁ Tid_ thread|> ;; (Grfi ;; Grmw)^*).
(* Lemma cert_co_base_alt : cert_co_base ≡₁ I ∪₁ S ∩₁ Tid_ thread. *)
(* Proof using WF IT_new_co. *)
(*   clear -WF IT_new_co. *)
(*   unfold cert_co_base. *)
(*   split; [|basic_solver]. *)
(*   unionL; [basic_solver|]. *)
(*   basic_solver. *)
(* Qed. *)
                                      
Lemma cert_co_base_rfirmw_clos :
  codom_rel (<|cert_co_base|> ;; Grfi ;; Grmw) ⊆₁ cert_co_base.
Proof using.
  unfold cert_co_base at 2.
  rewrite <- rt_unit.
  unfold cert_co_base.
  unfolder. ins. desc. subst.
  do 2 eexists. split; [split; [|by eauto]|]; eauto.
Qed.

Lemma I_in_cert_co_base : I ⊆₁ cert_co_base.
Proof using. unfold cert_co_base. rewrite rtE. basic_solver 10. Qed.

Lemma IST_in_cert_co_base : I ∪₁ S ∩₁ Tid_ thread ⊆₁ cert_co_base.
Proof using S_I_in_W_ex.
  unfold cert_co_base. clear.
  rewrite rtE. basic_solver 10.
Qed.

(* Lemma W_ex_in_cert_co_base : GW_ex ⊆₁ cert_co_base. *)
(* Proof using. unfold cert_co_base. clear. basic_solver. Qed. *)

Definition cert_co := new_co G cert_co_base (E ∩₁ W ∩₁ Tid_ thread).

Lemma cert_co_base_in_E_W : cert_co_base ⊆₁ E ∩₁ W.
Proof using WF S_in_W ST_in_E IT_new_co.
  clear S_I_in_W_ex.
  unfold cert_co_base.
  rewrite rtE.
  arewrite (Grmw ⊆ Grmw ;; <|E ∩₁ W|>).
  { apply codom_rel_helper.
    rewrite WF.(wf_rmwE), WF.(wf_rmwD).
    clear. basic_solver. }
  rewrite <- !seqA.
  rewrite inclusion_ct_seq_eqv_r.
  arewrite (I ∪₁ S ∩₁ Tid_ thread ⊆₁ E ∩₁ W).
  2: basic_solver.
  unionL.
  2: { generalize S_in_W ST_in_E. basic_solver. }
  rewrite <- IT_new_co. clear. basic_solver 10.
Qed.

Lemma IST_new_co : cert_co_base ∪₁ E ∩₁ W ∩₁ Tid_ thread ≡₁ E ∩₁ W.
Proof using WF S_in_W ST_in_E IT_new_co.
  clear S_I_in_W_ex.
  rewrite <- IT_new_co at 2.
  split.
  2: by rewrite I_in_cert_co_base.
  unionL.
  2: basic_solver.
  rewrite IT_new_co.
  apply cert_co_base_in_E_W.
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

Lemma Gco_in_cert_co_sym_clos : Gco ⊆ cert_co ∪ cert_co^{-1}.
Proof.
  rewrite WF.(wf_coE). do 2 rewrite WF.(wf_coD).
  arewrite (W ⊆₁ fun x => exists l, loc Glab x = Some l) at 1.
  { clear. unfolder. ins. by apply is_w_loc. }
  arewrite (Gco ⊆ Gco ∩ Gco).
  rewrite WF.(wf_col) at 1.
  unfolder. ins. desf. eapply wf_cert_co_total.
  3: eby intros HH; subst; eapply WF.(co_irr).
  all: split; [split|]; eauto.
Qed.

Lemma cert_co_in_Gco_sym_clos : cert_co ⊆ Gco ∪ Gco^{-1}.
Proof.
  rewrite (wf_cert_coE). do 2 rewrite (wf_cert_coD).
  arewrite (W ⊆₁ fun x => exists l, loc Glab x = Some l) at 1.
  { clear. unfolder. ins. by apply is_w_loc. }
  arewrite (cert_co ⊆ cert_co ∩ cert_co).
  rewrite (wf_cert_col) at 1.
  unfolder. ins. desf. eapply WF.(wf_co_total).
  3: eby intros HH; subst; eapply cert_co_irr.
  all: split; [split|]; eauto.
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
Proof using WF S_in_W ST_in_E IT_new_co S_I_in_W_ex COH.
  unfold cert_co.
  red; intros x y H.
  assert (A: (E ∩₁ W ∩₁ Tid_ thread) y).
  { apply (co_for_split IST_new_co (wf_coE WF) (wf_coD WF)).
    red. eauto. }
  unfolder in H; desc.
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
    destruct A0; try subst y.
    { eapply (co_irr WF); edone. }
    eapply COH.
    hahn_rewrite <- (@sb_in_hb G).
    hahn_rewrite <- (@co_in_eco G).
    clear -H2 D0.
    basic_solver. }
  hahn_rewrite (no_co_to_init WF (coherence_sc_per_loc COH)) in D.
  unfolder in D. apply D.
Qed.

Lemma cert_co_for_split :
  ⦗set_compl cert_co_base⦘ ⨾ immediate cert_co ⊆ Gsb.
Proof using WF S_in_W S_I_in_W_ex ST_in_E IT_new_co COH.
  arewrite (immediate cert_co ⊆
            ⦗cert_co_base ∪₁ set_compl cert_co_base⦘ ⨾ immediate cert_co).
  { rewrite AuxRel.set_compl_union_id. unfold set_full. by rewrite seq_id_l. }
  rewrite id_union, seq_union_l, seq_union_r. unionL.
  2: { rewrite cert_co_for_split_helper. clear. basic_solver. }
  rewrite <- seqA. rewrite <- id_inter.
  rewrite set_interC. rewrite <- set_minusE.
  clear; basic_solver.
Qed.

Lemma cert_co_base_nTid : cert_co_base \₁ E ∩₁ W ∩₁ Tid_ thread ≡₁ I \₁ Tid_ thread.
Proof using IT_new_co ST_in_E S_in_W WF.
  unfold cert_co_base.
  split.
  2: { rewrite rtE. clear. intros x [HH BB]. split; [basic_solver 10|].
       unfolder. intros AA. desf. }
  intros x [HH AA]. 
  apply cert_co_base_in_E_W in HH.
  destruct (classic (I x)).
  { split; auto. intros BB. apply AA. split; auto. }
  exfalso.
  apply IT_new_co in HH. destruct HH; desf.
Qed.

Lemma cert_co_alt :
  cert_co  ⊆ Gco ∩ cert_co ⨾ ⦗ cert_co_base ⦘ ∪ ⦗ Tid_ thread ⦘ ⨾ Gco ∩ cert_co ∪ 
           ⦗ I ∩₁ NTid_ thread ⦘ ⨾ cert_co ⨾ ⦗ (E ∩₁ W ∩₁ Tid_ thread) \₁
                                              cert_co_base ⦘.
Proof using WF TCCOH S_in_W ST_in_E S IT_new_co.
  rewrite <- cert_co_base_nTid.
  arewrite (cert_co ⊆ cert_co ∩ cert_co) at 1.
  unfold cert_co at 1.
  rewrite new_co_in at 1.
  all: try by apply WF.
  { clear. basic_solver 40. }
  apply IST_new_co.
Qed.

Lemma cert_co_alt' : cert_co  ⊆ Gco ∩ cert_co ∪ 
  ⦗ I ∩₁ NTid_ thread ⦘ ⨾ cert_co ⨾ ⦗ (E ∩₁ W ∩₁ Tid_ thread) \₁ I ⦘.
Proof using WF TCCOH S_in_W ST_in_E S IT_new_co.
  rewrite cert_co_alt at 1.
  clear.
  unionL.
  3: rewrite <- I_in_cert_co_base at 1.
  all: basic_solver 12.
Qed.

Lemma imm_cert_cof : functional (immediate cert_co).
Proof using WF S_in_W ST_in_E S IT_new_co.
  intros x y z ICOXY ICOXZ.
  assert (cert_co x y) as COXY by apply ICOXY.
  assert (cert_co x z) as COXZ by apply ICOXZ.
  apply wf_cert_coD in COXY. destruct_seq COXY as [BB1 BB2].
  apply wf_cert_coE in COXY. destruct_seq COXY as [BB3 BB4].
  apply wf_cert_coD in COXZ. destruct_seq COXZ as [AA1 AA2].
  apply wf_cert_coE in COXZ. destruct_seq COXZ as [AA3 AA4].
  apply is_w_loc in AA1. desf.
  set (CC:=COXY). apply wf_cert_col in CC. red in CC.
  set (DD:=COXZ). apply wf_cert_col in DD. red in DD.
  destruct (classic (y = z)); auto.
  edestruct (wf_cert_co_total); eauto.
  1,2: split; [split|]; eauto.
  { by etransitivity; [|by eauto]. }
  { exfalso. by apply ICOXZ with (c:=y). }
  exfalso. by apply ICOXY with (c:=z).
Qed.

Lemma imm_cert_co_tf : functional (immediate cert_co)⁻¹.
Proof using WF S_in_W ST_in_E S IT_new_co.
  intros x y z ICOXY ICOXZ. red in ICOXY. red in ICOXZ.
  assert (cert_co y x) as COXY by apply ICOXY.
  assert (cert_co z x) as COXZ by apply ICOXZ.
  apply wf_cert_coD in COXY. destruct_seq COXY as [BB1 BB2].
  apply wf_cert_coE in COXY. destruct_seq COXY as [BB3 BB4].
  apply wf_cert_coD in COXZ. destruct_seq COXZ as [AA1 AA2].
  apply wf_cert_coE in COXZ. destruct_seq COXZ as [AA3 AA4].
  apply is_w_loc in AA2. desf.
  set (CC:=COXY). apply wf_cert_col in CC. red in CC.
  set (DD:=COXZ). apply wf_cert_col in DD. red in DD.
  destruct (classic (y = z)); auto.
  edestruct (wf_cert_co_total); eauto.
  1,2: split; [split|]; eauto.
  { exfalso. by apply ICOXY with (c:=z). }
  exfalso. by apply ICOXZ with (c:=y).
Qed.

Lemma cert_co_sb_irr : irreflexive (cert_co ⨾ Gsb).
Proof using WF COH TCCOH S_in_W S_I_in_W_ex ST_in_E S IT_new_co I_in_S.
  rewrite cert_co_alt at 1.
  relsf; unionL.
  1-2: rewrite co_in_eco, sb_in_hb; 
       revert COH; unfold coherence; basic_solver 21.
  rewrite !seqA.
  arewrite (⦗E ∩₁ W ∩₁ Tid_ thread \₁ cert_co_base⦘ ⊆ ⦗Tid_ thread⦘ ⨾ ⦗set_compl Init⦘).
  { unfold cert_co_base. 
    generalize (init_issued WF TCCOH).
    basic_solver 21. }
  rewrite ninit_sb_same_tid.
  unfold same_tid; basic_solver.
Qed.

Lemma imm_cert_co_inv_exists : E ∩₁ W ∩₁ set_compl Init ⊆₁ codom_rel (immediate cert_co).
Proof using WF TCCOH S_in_W S_I_in_W_ex ST_in_E S IT_new_co COH I_in_S.
unfolder; ins.
ins; eapply fsupp_immediate_pred.
{ eapply fsupp_mon; [| eapply fsupp_cross].
  apply dom_helper_3.
  eapply wf_cert_coE.
  unfold acts_set.
  unfold set_finite.
  eauto. }
{ eapply cert_co_irr. }
{ eapply cert_co_trans. }
unfolder; intro HH.
exploit is_w_loc; eauto; ins; desf.
eapply HH with (b := InitEvent l).
eapply tot_ex.
{ apply wf_cert_co_total. }
{ basic_solver. }
{ unfolder; splits; try edone.
  eapply (wf_init WF); exists x; splits; eauto.
  { by unfold is_w; rewrite (wf_init_lab WF) in *. }
  rewrite x1.
  by unfold loc; rewrite (wf_init_lab WF) in *. }
{ intro A.
  eapply cert_co_sb_irr; eauto.
  unfolder; eexists; splits; eauto.
  eapply init_ninit_sb; eauto.
  by apply (wf_init WF); eexists; splits; eauto. }
unfold is_init in *; desf.
Qed.

Lemma transp_cert_co_imm_cert_co : (immediate cert_co)⁻¹ ⨾ cert_co  ⊆ cert_co^?.
Proof using WF S_in_W ST_in_E S IT_new_co.
rewrite wf_cert_coE at 2.
rewrite wf_cert_coD at 2.
unfolder; ins; desf.
cut (x = y \/ cert_co y x \/ cert_co x y).
by ins; desf; eauto 21; exfalso; eauto.
cut (x <> y -> cert_co y x \/ cert_co x y).
tauto.
ins.
eapply wf_cert_co_total; eauto.
by unfolder; ins; desf.
hahn_rewrite wf_cert_coE in H; unfolder in H; desf.
hahn_rewrite wf_cert_coD in H7; unfolder in H7; desf.
hahn_rewrite wf_cert_col in H9; unfolder in H7; desf.
hahn_rewrite wf_cert_col in H1; unfolder in H1; desf.
unfold same_loc in *; desf.
unfolder; splits; eauto.
congruence.
Qed.

Lemma transp_cert_co_imm_cert_co' : cert_co⁻¹ ⨾ immediate cert_co  ⊆ cert_co⁻¹^?.
Proof using WF S_in_W ST_in_E S IT_new_co.
apply inclusion_transpE.
rewrite transp_seq, transp_cr.
rels.
apply transp_cert_co_imm_cert_co.
Qed.

End CertExec_CO.
