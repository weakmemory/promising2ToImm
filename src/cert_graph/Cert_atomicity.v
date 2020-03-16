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
Require Import TraversalConfig.
Require Import TraversalConfigAlt.
Require Import TraversalConfigAltOld.
Require Import ExtTraversalConfig.

Require Import Cert_co.
Require Import Cert_D.
Require Import Cert_rf.
Require Import CertExecution2.

Set Implicit Arguments.
Remove Hints plus_n_O.

Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'NTid_' t" := (fun x => tid x <> t) (at level 1).

Section CertExec_at.

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

Notation "'cert_co'" := (cert_co G T S thread).

Notation "'D'" := (D G T S thread).

Notation "'new_rf'" := (new_rf G sc T S thread).
Notation "'cert_rf'" := (cert_rf G sc T S thread).
Notation "'cert_rfi'" := (cert_rfi G sc T S thread).
Notation "'cert_rfe'" := (cert_rfe G sc T S thread).

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
Hypothesis RMW_S : dom_rel ((Gdetour ∪ Grfe) ⨾ Grmw ⨾ ⦗S⦘) ⊆₁ I.
Hypothesis ST_in_E : S ∩₁ Tid_ thread ⊆₁ E.
Hypothesis I_in_S : I ⊆₁ S.

Hypothesis F_in_C : E ∩₁ F ∩₁ Acq/Rel ⊆₁ C.

Hypothesis S_I_in_W_ex : (S ∩₁ Tid_ thread) \₁ I ⊆₁ W_ex G.

Hypothesis ETC_DR_R_ACQ_I : dom_rel ((Gdetour ∪ Grfe) ⨾ (Grmw ⨾ Grfi)＊ ⨾ ⦗R∩₁Acq⦘ ⨾ Gsb ⨾ ⦗S⦘) ⊆₁ I.

Hypothesis COMP_R_ACQ_SB : dom_rel ((Grmw ⨾ Grfi)＊ ⨾ ⦗E ∩₁ R ∩₁ Acq⦘) ⊆₁ codom_rel Grf.
Hypothesis SB_S          : dom_sb_S_rfrmw G (mkETC T S) (Grf ⨾ ⦗GR_ex⦘) I ⊆₁ S.
Hypothesis RMWREX        : dom_rel Grmw ⊆₁ GR_ex.
Hypothesis FACQREL       : E ∩₁ F ⊆₁ Acq/Rel.

Variable lab' : actid -> label.
Hypothesis SAME : same_lab_u2v lab' Glab.


Notation "'certG'" := (certG G sc T S thread lab').


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

Notation "'cert_co_base'" := (cert_co_base G T S thread).

Lemma cert_rmw_atomicity : rmw_atomicity certG.
Proof using All.
  generalize (atomicity_alt WF (coherence_sc_per_loc COH) AT).
  intro AT'; clear AT.

  red; ins; cut (irreflexive (Cfr ⨾ (cert_co \ Gsb) ⨾ Grmw^{-1})).
  { basic_solver 12. }
  rotate 1.
  unfold fr. ins; unfold Cert_rf.cert_rf.

  rewrite !transp_union.
  arewrite (new_rf ⊆ new_rf ⨾ ⦗ E \₁ D ⦘).
  { rewrite wf_new_rfE; eauto. basic_solver. }

  rewrite !transp_seq, !transp_eqv_rel, !seqA.
  relsf. unionL; rewrite !seqA.
  2: { basic_solver. }
  2: { arewrite (Grmw⁻¹ ⨾ ⦗set_compl D⦘ ⨾ Grmw ⊆ ⦗fun _ => True⦘).
       2: basic_solver.
       arewrite_id  ⦗set_compl D⦘.
       rels.
       apply functional_alt.
       apply WF.(wf_rmwf). }

  arewrite ((cert_co \ Gsb) ⊆ (cert_co \ Gsb) ;; <|fun _ => True|>) by basic_solver.
  arewrite (<|fun _ => True|> ⊆
            <| cert_co_base ∪₁ set_compl cert_co_base|>).
  { unfolder. ins. tauto. }
  rewrite id_union, !seq_union_r. apply irreflexive_union. split.
  { arewrite ((cert_co \ Gsb) ⨾ ⦗cert_co_base⦘ ⊆
            (cert_co ∩ Gco \ Gsb) ⨾ ⦗cert_co_base⦘).
    { cut (new_co G (cert_co_base) (E ∩₁ W ∩₁ Tid_ thread) ⨾
           ⦗cert_co_base⦘ ⊆ Gco).
      { basic_solver 21. }
      erewrite new_co_I; try apply WF.
      clear. basic_solver.
      eapply IST_new_co; eauto. }

    unfold Cert_co.cert_co.
    erewrite new_co_in at 1; try apply WF.
    2: eapply IST_new_co; eauto.
    relsf; unionL.
    1,2: generalize (co_trans WF); revert AT'; unfold fr; basic_solver 12.

    remember (new_co G cert_co_base (E ∩₁ W ∩₁ Tid_ thread)) as new.
    rewrite !seqA.
    arewrite (⦗E ∩₁ W ∩₁ Tid_ thread \₁ cert_co_base⦘
                ⨾ (new ∩ Gco \ Gsb) ⨾ ⦗cert_co_base⦘ ⊆
                ⦗E ∩₁ W ∩₁ Tid_ thread \₁ cert_co_base⦘
                ⨾ new ⨾ ⦗cert_co_base \₁ E ∩₁ W ∩₁ Tid_ thread⦘).
    { unfolder; ins; desf; splits; eauto.
      intros [[EY WY] TT].
      eapply same_thread in TT; desf; eauto.
      2: { hahn_rewrite (no_co_to_init WF (coherence_sc_per_loc COH)) in H3.
           unfolder in H3; desf. }
      destruct TT; desf; try subst z2; eauto.
      eapply COH. eexists. splits; [apply sb_in_hb | right; apply co_in_eco]; edone. }

    subst new.

    rewrite (inter_inclusion
               (@T_I_new_co_I_T G (cert_co_base)
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
    eapply (@new_co_irr _  (cert_co_base)); try apply WF.
    eapply IST_new_co; eauto.
    eapply (@new_co_trans _  (cert_co_base)); try apply WF.
    eapply IST_new_co; eauto.
    
    apply H3.
    apply new_co_helper; [apply WF| apply WF| basic_solver 12]. }
  
  rewrite WF.(rmw_non_init_lr).
  rewrite WF.(wf_rmwD). rewrite WF.(wf_rmwE).
  rewrite wf_cert_coE; auto.
  rewrite wf_cert_coD; auto.
  unfold Cert_co.cert_co_base.

  unfolder. ins. desf.
  rename z1 into z0.
  rename z3 into z1.
  rename H6 into CCBX.
  assert ((E ∩₁ W) x) as EWX by (by split).
  assert ((E ∩₁ W) z0) as EWZ0 by (by split).
  assert ((E ∩₁ W) z1) as EWZ1 by (by split).

  assert (~ I x) as NIX.
  { intros HH. eapply I_in_cert_co_base in HH; eauto.
      by apply CCBX in HH. }
  assert (~ C x) as NCX.
  { intros HH. apply NIX. eapply w_covered_issued; eauto. by split. }

  destruct (classic (Tid_ thread x)) as [TIDX|].
  2: { apply NIX. apply IT_new_co in EWX. unfolder in EWX. desf. }

  assert (~ S x) as NSX.
  { intros HH. apply CCBX. apply IST_in_cert_co_base; auto.
    right. by split. }

  assert (dom_rel (Gsb ⨾ ⦗S⦘) x) as AAA.
  { destruct (E_to_S x) as [|TT]; desf.
    generalize NSX TT. clear. basic_solver 10. }

  assert (NTid_ thread z1) as NTIDZ1.
  { intros HH. subst.
    assert ((<|E|> ;; same_tid ;; <|E|>) z1 x) as AA.
    { apply seq_eqv_lr. splits; auto. }
    apply tid_sb in AA. unfolder in AA. desf.
    { eapply cert_co_irr; eauto. }
    eapply cert_co_sb_irr; eauto. basic_solver. }
  
  assert (I z1) as IZ1.
  { apply IT_new_co in EWZ1. unfolder in EWZ1. desf. }

  match goal with
  | H : Grf ?X ?Y |- _ => rename H into RF
  end.

  destruct (classic (I z0)) as [IZ0|NIZ0].
  { apply NSX. apply SB_S. red. split; auto.
    exists z0. apply seq_eqv_l. split; auto.
    apply seqA.
    exists z. split; auto.
    apply seq_eqv_l. split; auto.
    apply RMWREX. red. eauto. }

  destruct (classic (Tid_ (tid x) z0)).
  2: { apply NIZ0. apply IT_new_co in EWZ0. unfolder in EWZ0. desf. }

  set (RFA:=RF).
  apply rfi_union_rfe in RFA. destruct RFA; auto.
  2: { eapply rfe_n_same_tid; eauto. split; eauto. red.
       apply WF.(wf_rmwt) in H17. by rewrite H17. }

  assert (~ cert_co_base z0) as CCBZ0.
  { intros HH. apply CCBX.
    apply cert_co_base_rfirmw_clos.
    exists z0. apply seq_eqv_l. split; auto. basic_solver. }

  destruct (classic (S z0)) as [SZ0|NSZ0].
  { apply CCBZ0. apply IST_in_cert_co_base; auto. basic_solver. }
  assert (cert_co_base z1) as CCBZ1 by (by apply I_in_cert_co_base).

  generalize (@T_I_new_co_I_T
                G cert_co_base
                (E ∩₁ W ∩₁ Tid_ (tid x)) (co_trans WF)).
  intros HH.
  specialize (HH z0 z1).
  destruct HH as [d [COA COB]].
  { apply seq_eqv_lr.
    splits; auto.
    2: by desf.
    all: split; auto.
    { basic_solver. }
    unfolder; intro; desf. }
  unfolder in COB. desc.

  enough (new_co G cert_co_base (E ∩₁ W ∩₁ Tid_ (tid x)) x d) as AA.
  { desf.
    eapply cert_co_irr with (x:=d); eauto.
    eapply cert_co_trans with (y:=x); eauto.
    eapply cert_co_trans with (y:=z1); eauto.
    apply I_co_in_cert_co; auto.
    apply seq_eqv_l. split; auto. }

  destruct (classic (d = x)).
  { desf. }
  desf.
  edestruct wf_cert_co_total; eauto.
  1,2: unfolder; ins; splits; auto.
  { transitivity (Gloc z0).
    { symmetry. apply wf_rfrmwl; auto. basic_solver. }
      by apply WF.(wf_col). }
  exfalso.
  eapply cert_co_alt' in H6; eauto.
  unfolder in H6. desf.
  eapply AT'. split; eauto. unfold fr. unfolder. eauto.
Qed.

End CertExec_at.
