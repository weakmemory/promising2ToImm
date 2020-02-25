Require Import Setoid.
From hahn Require Import Hahn.
From imm Require Import Events Execution Execution_eco
     imm_bob imm_s_ppo imm_s imm_s_hb CombRelations AuxDef TraversalConfig.
Require Import AuxRel AuxRel2.

Set Implicit Arguments.

Section ImmProperties.
Variable G : execution.
Hypothesis WF : Wf G.
Variable sc : relation actid.
Hypothesis CON : imm_consistent G sc.
Hypothesis WF_SC : wf_sc G sc.


Notation "'acts'" := G.(acts).
Notation "'sb'" := G.(sb).
Notation "'rmw'" := G.(rmw).
Notation "'data'" := G.(data).
Notation "'addr'" := G.(addr).
Notation "'ctrl'" := G.(ctrl).
Notation "'rmw_dep'" := G.(rmw_dep).
Notation "'rf'" := G.(rf).
Notation "'co'" := G.(co).
Notation "'coe'" := G.(coe).
Notation "'fr'" := G.(fr).

Notation "'eco'" := G.(eco).

Notation "'bob'" := G.(bob).
Notation "'fwbob'" := G.(fwbob).
Notation "'ppo'" := G.(ppo).
Notation "'fre'" := G.(fre).
Notation "'rfi'" := G.(rfi).
Notation "'rfe'" := G.(rfe).
Notation "'deps'" := G.(deps).
Notation "'detour'" := G.(detour).
Notation "'release'" := G.(release).
Notation "'sw'" := G.(sw).
Notation "'hb'" := G.(hb).

Notation "'urr'" := (urr G sc).
Notation "'c_acq'" := (c_acq G sc).
Notation "'c_cur'" := (c_cur G sc).
Notation "'c_rel'" := (c_rel G sc).
Notation "'t_acq'" := (t_acq G sc).
Notation "'t_cur'" := (t_cur G sc).
Notation "'t_rel'" := (t_rel G sc).
Notation "'S_tm'" := G.(S_tm).
Notation "'S_tmr'" := G.(S_tmr).
Notation "'msg_rel'" := (msg_rel G sc).

Notation "'lab'" := G.(lab).
Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'mod'" := (Events.mod lab).
Notation "'same_loc'" := (same_loc lab).

Notation "'E'" := G.(acts_set).
Notation "'R'" := (fun x => is_true (is_r lab x)).
Notation "'W'" := (fun x => is_true (is_w lab x)).
Notation "'F'" := (fun x => is_true (is_f lab x)).
Notation "'RW'" := (R ∪₁ W).
Notation "'FR'" := (F ∪₁ R).
Notation "'FW'" := (F ∪₁ W).
Notation "'R_ex'" := (fun a => is_true (R_ex lab a)).
Notation "'W_ex'" := (W_ex G).
Notation "'W_ex_acq'" := (W_ex ∩₁ (fun a => is_true (is_xacq lab a))).

Notation "'Init'" := (fun a => is_true (is_init a)).
Notation "'Loc_' l" := (fun x => loc x = Some l) (at level 1).
Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'NTid_' t" := (fun x => tid x <> t) (at level 1).
Notation "'W_' l" := (W ∩₁ Loc_ l) (at level 1).

Notation "'Pln'" := (fun x => is_true (is_only_pln lab x)).
Notation "'Rlx'" := (fun x => is_true (is_rlx lab x)).
Notation "'Rel'" := (fun x => is_true (is_rel lab x)).
Notation "'Acq'" := (fun x => is_true (is_acq lab x)).
Notation "'Acqrel'" := (fun x => is_true (is_acqrel lab x)).
Notation "'Sc'" := (fun x => is_true (is_sc lab x)).
Notation "'Acq/Rel'" := (fun a => is_true (is_ra lab a)).

Lemma ninit_sb_same_tid : ⦗ set_compl is_init ⦘ ⨾ sb ⊆ same_tid.
Proof using.
  rewrite sb_tid_init'.
  basic_solver.
Qed.

Lemma ninit_rfi_same_tid : ⦗ set_compl is_init ⦘ ⨾ rfi ⊆ same_tid.
Proof using.
  arewrite (rfi ⊆ sb).
  apply ninit_sb_same_tid.
Qed.

Lemma same_tid_trans : transitive same_tid.
Proof using.
  red. unfold same_tid. ins.
  etransitivity; eauto.
Qed.

Lemma ninit_rfi_rmw_same_tid : ⦗ set_compl is_init ⦘ ⨾ rfi ⨾ rmw ⊆ same_tid.
Proof using WF.
  rewrite WF.(wf_rmwt).
  sin_rewrite ninit_rfi_same_tid.
  apply transitiveI. apply same_tid_trans.
Qed.

Lemma rmw_non_init_lr : rmw ≡ ⦗set_compl is_init⦘ ⨾ rmw ⨾ ⦗set_compl is_init⦘.
Proof using WF.
  split; [|basic_solver].
  rewrite WF.(rmw_from_non_init) at 1.
  rewrite <- seqA.
  apply codom_rel_helper.
  rewrite WF.(rmw_in_sb).
  rewrite no_sb_to_init.
  basic_solver.
Qed.

Lemma ninit_rfi_rmw_rt_same_tid : ⦗ set_compl is_init ⦘ ⨾ (rfi ⨾ rmw)＊ ⊆ same_tid.
Proof using WF.
  apply rt_ind_left with (P:= fun r => ⦗set_compl is_init⦘ ⨾ r).
  { by eauto with hahn. }
  { unfold same_tid. basic_solver 12. }
  intros k AA. rewrite !seqA.
  rewrite (dom_r rmw_non_init_lr). rewrite !seqA.
  rewrite AA.
  sin_rewrite ninit_rfi_rmw_same_tid.
  apply transitiveI. apply same_tid_trans.
Qed.

Lemma wf_immcof : functional (immediate co).
Proof using WF.
  intros x y z ICOXY ICOXZ.
  assert (co x y) as COXY by apply ICOXY.
  assert (co x z) as COXZ by apply ICOXZ.
  apply WF.(wf_coD) in COXY. destruct_seq COXY as [BB1 BB2].
  apply WF.(wf_coE) in COXY. destruct_seq COXY as [BB3 BB4].
  apply WF.(wf_coD) in COXZ. destruct_seq COXZ as [AA1 AA2].
  apply WF.(wf_coE) in COXZ. destruct_seq COXZ as [AA3 AA4].
  apply is_w_loc in AA1. desf.
  set (CC:=COXY). apply WF.(wf_col) in CC. red in CC.
  set (DD:=COXZ). apply WF.(wf_col) in DD. red in DD.
  destruct (classic (y = z)); auto.
  edestruct WF.(wf_co_total); eauto.
  1,2: split; [split|]; eauto.
  { by etransitivity; [|by eauto]. }
  { exfalso. by apply ICOXZ with (c:=y). }
  exfalso. by apply ICOXY with (c:=z).
Qed.

Lemma wf_immcotf : functional (immediate co)⁻¹.
Proof using WF.
  intros x y z ICOXY ICOXZ. red in ICOXY. red in ICOXZ.
  assert (co y x) as COXY by apply ICOXY.
  assert (co z x) as COXZ by apply ICOXZ.
  apply WF.(wf_coD) in COXY. destruct_seq COXY as [BB1 BB2].
  apply WF.(wf_coE) in COXY. destruct_seq COXY as [BB3 BB4].
  apply WF.(wf_coD) in COXZ. destruct_seq COXZ as [AA1 AA2].
  apply WF.(wf_coE) in COXZ. destruct_seq COXZ as [AA3 AA4].
  apply is_w_loc in AA2. desf.
  set (CC:=COXY). apply WF.(wf_col) in CC. red in CC.
  set (DD:=COXZ). apply WF.(wf_col) in DD. red in DD.
  destruct (classic (y = z)); auto.
  edestruct WF.(wf_co_total); eauto.
  1,2: split; [split|]; eauto.
  { exfalso. by apply ICOXY with (c:=z). }
  exfalso. by apply ICOXZ with (c:=y).
Qed.

Lemma wf_immcoPtf P : functional (immediate (⦗P⦘ ⨾ co))⁻¹.
Proof using WF.
  intros x y z ICOXY ICOXZ. red in ICOXY. red in ICOXZ.
  assert (co y x /\ P y) as [COXY PY].
  { destruct ICOXY as [AA BB]. generalize AA. basic_solver. }
  assert (co z x /\ P z) as [COXZ PZ].
  { destruct ICOXZ as [AA BB]. generalize AA. basic_solver. }
  apply WF.(wf_coD) in COXY. destruct_seq COXY as [BB1 BB2].
  apply WF.(wf_coE) in COXY. destruct_seq COXY as [BB3 BB4].
  apply WF.(wf_coD) in COXZ. destruct_seq COXZ as [AA1 AA2].
  apply WF.(wf_coE) in COXZ. destruct_seq COXZ as [AA3 AA4].
  apply is_w_loc in AA2. desf.
  set (CC:=COXY). apply WF.(wf_col) in CC. red in CC.
  set (DD:=COXZ). apply WF.(wf_col) in DD. red in DD.
  destruct (classic (y = z)); auto.
  edestruct WF.(wf_co_total); eauto.
  1,2: split; [split|]; eauto.
  { exfalso. apply ICOXY with (c:=z).
    all: apply seq_eqv_l; split; auto. }
  exfalso. apply ICOXZ with (c:=y).
  all: apply seq_eqv_l; split; auto.
Qed.
  
Lemma wf_rfrmwsf : functional (rf ⨾ rmw).
Proof using WF CON.
  rewrite rfrmw_in_im_co; eauto.
  apply wf_immcof.
Qed.

Lemma P_co_nP_co_P_imm P
      (P_in_E : P ⊆₁ E)
      (P_in_W : P ⊆₁ W) :
  immediate (⦗P⦘ ⨾ co) ⨾ ⦗set_compl P⦘ ⨾ immediate (co ⨾ ⦗P⦘) ⊆
            immediate (⦗P⦘ ⨾ co ⨾ ⦗P⦘).
Proof using WF.
  intros x y [z [AA BB]].
  destruct_seq_l BB as CC.
  set (DD := AA). destruct DD as [DD _]. destruct_seq_l DD as PX.
  set (EE := BB). destruct EE as [EE _]. destruct_seq_r EE as PY.
  assert (co x y) as CO.
  { eapply WF.(co_trans); eauto. }
  apply WF.(wf_coD) in CO. destruct_seq CO as [WX WY].
  apply WF.(wf_coE) in CO. destruct_seq CO as [EX EY].
  apply WF.(wf_coD) in DD. destruct_seq DD as [XLOC WZ].
  apply WF.(wf_coE) in DD. destruct_seq DD as [EX' EZ].
  apply is_w_loc in XLOC. desf.
  assert (loc y = Some l /\ loc z = Some l) as [YLOC ZLOC].
  { split; rewrite <- XLOC; symmetry; by apply WF.(wf_col). }

  split.
  { apply seq_eqv_lr. by splits. }
  ins.
  destruct_seq R1 as [A1 B1].
  destruct_seq R2 as [A2 B2].
  destruct (classic (c = z)) as [|CNEQ]; desf.
  assert (loc c = Some l) as LOCC.
  { rewrite <- YLOC. by apply WF.(wf_col). }
  assert (E c) as EC.
  { by apply P_in_E. }
  assert (W c) as WC.
  { by apply P_in_W. }
  
  assert (c <> x /\ c <> y) as [CNNEXT CNPREV].
  { split; intros HH; subst; eapply WF.(co_irr); eauto. }

  assert (co c z \/ co z c) as [QQ|QQ].
  { eapply WF.(wf_co_total); eauto; unfolder; eauto. }
  { eapply AA with (c:=c); apply seq_eqv_l; eauto. }
  eapply BB with (c:=c); apply seq_eqv_r; eauto.
Qed.

Lemma P_co_immediate_P_co_transp_in_co_cr P
      (P_in_E : P ⊆₁ E)
      (P_in_W : P ⊆₁ W) :
  (⦗P⦘ ⨾ co) ⨾ (immediate (⦗P⦘⨾ co))⁻¹ ⊆ co^?.
Proof using WF.
  intros x y [z [AA [BB CC]]].
  destruct_seq_l AA as PZ.
  destruct_seq_l BB as DD.
  destruct (classic (x = y)) as [|NEQ]; subst; [by left|right].
  apply WF.(wf_coD) in AA. destruct_seq AA as [WX WZ].
  apply WF.(wf_coE) in AA. destruct_seq AA as [EX EZ].
  apply WF.(wf_coD) in BB. destruct_seq BB as [WY ZLOC].
  apply WF.(wf_coE) in BB. destruct_seq BB as [EY FF].
  apply is_w_loc in ZLOC. desf.
  assert (loc x = Some l /\ loc y = Some l) as [XLOC YLOC].
  { rewrite <- !ZLOC. split; by apply WF.(wf_col). }
  edestruct WF.(wf_co_total); eauto.
  1,2: by split; [split|]; eauto.
  exfalso.
  apply CC with (c:=x).
  all: apply seq_eqv_l; split; auto.
Qed.

(* TODO: rename in accordance with the previous lemma. *)
Lemma co_imm_co_in_co_cr : co ⨾ (immediate co)⁻¹ ⊆ co^?.
Proof using WF.
  assert (co ≡ ⦗E∩₁W⦘⨾co) as AA.
  { split; [|basic_solver].
    rewrite WF.(wf_coE) at 1. rewrite WF.(wf_coD) at 1.
    basic_solver. }
  rewrite AA at 1 2.
  apply P_co_immediate_P_co_transp_in_co_cr.
  all: basic_solver.
Qed.

Lemma immediate_co_P_transp_co_P_in_co_cr P
      (P_in_E : P ⊆₁ E)
      (P_in_W : P ⊆₁ W) :
  (immediate (co ⨾ ⦗P⦘))⁻¹ ⨾ (co ⨾ ⦗P⦘) ⊆ co^?.
Proof using WF.
  intros x y [z [[BB CC] AA]].
  destruct_seq_r AA as PZ.
  destruct_seq_r BB as DD.
  destruct (classic (x = y)) as [|NEQ]; subst; [by left|right].
  apply WF.(wf_coD) in AA. destruct_seq AA as [WZ WY].
  apply WF.(wf_coE) in AA. destruct_seq AA as [EZ EY].
  apply WF.(wf_coD) in BB. destruct_seq BB as [ZLOC WX].
  apply WF.(wf_coE) in BB. destruct_seq BB as [FF EX].
  apply is_w_loc in ZLOC. desf.
  assert (loc x = Some l /\ loc y = Some l) as [XLOC YLOC].
  { rewrite <- !ZLOC. split; symmetry; by apply WF.(wf_col). }
  edestruct WF.(wf_co_total); eauto.
  1,2: by split; [split|]; eauto.
  exfalso.
  apply CC with (c:=y).
  all: apply seq_eqv_r; split; auto.
Qed.

Lemma rfrmwP_in_immPco P P'
    (DRES : dom_rel (rf ⨾ rmw ⨾ ⦗P'⦘) ⊆₁ P) :
  rf ⨾ rmw ⨾ ⦗P'⦘ ⊆ immediate (⦗P⦘ ⨾ co).
Proof using WF CON.
  assert (sc_per_loc G) as SPL.
  { apply coherence_sc_per_loc. apply CON. }

  rewrite <- immediate_inter_mori with (x:=co).
  2: basic_solver.
  apply inclusion_inter_r.
  2: { rewrite <- seqA. rewrite rfrmw_in_im_co; eauto. basic_solver. }
  rewrite <- rf_rmw_in_co; auto.
  generalize DRES. basic_solver 10.
Qed.

Lemma co_imm : co ≡ (immediate co)⁺.
Proof using WF.
  apply fsupp_imm_t; try apply WF.
  rewrite WF.(wf_coE).
  red. ins. eexists. ins. destruct_seq_l REL as AA.
  apply AA.
Qed.

Lemma W_ex_in_E : W_ex ⊆₁ acts_set G.
Proof using WF.
  unfold Execution.W_ex. rewrite WF.(wf_rmwE). basic_solver.
Qed.

Lemma rfrmw_in_eco (SPL : sc_per_loc G) (COMP : complete G) :
  rf ⨾ rmw ⊆ eco.
Proof using WF.
  rewrite rf_in_eco. rewrite rmw_in_fr; auto.
  rewrite fr_in_eco.
  apply transitiveI. by apply eco_trans.
Qed.

Lemma rfrmw_sb_irr : 
  irreflexive (rf ⨾ rmw ⨾ sb).
Proof using WF CON.
  arewrite (rf ⨾ rmw ⊆ eco).
  { apply rfrmw_in_eco; auto.
    apply coherence_sc_per_loc.
    all: by apply CON. }
  rewrite sb_in_hb.
  rewrite irreflexive_seqC.
  arewrite (eco ⊆ eco^?).
  apply CON. 
Qed.

Lemma W_ex_in_codom_rfrmw : W_ex ⊆₁ codom_rel (rf ⨾ rmw).
Proof using WF CON.
  intros x [y RMW].
  assert (exists z, rf z y) as [z RF].
  { apply CON.
    apply (dom_l WF.(wf_rmwE)) in RMW. destruct_seq_l RMW as AA. split; auto.
    apply (dom_l WF.(wf_rmwD)) in RMW. destruct_seq_l RMW as BB. type_solver. }
  exists z. eexists. eauto.
Qed.

Lemma W_ex_eq_EW_W_ex : W_ex ≡₁ E ∩₁ W ∩₁ W_ex.
Proof using WF.
  generalize W_ex_in_E.
  generalize WF.(W_ex_in_W). clear. basic_solver 10.
Qed.

Lemma tid_set_dec thread : Tid_ thread ∪₁ NTid_ thread ≡₁ (fun x => True).
Proof using. unfolder; split; ins; desf; tauto. Qed.

Lemma sc_rfe_ct_in_sc_rfe (Wf_sc : wf_sc G sc) : (sc ∪ rfe)⁺ ⊆ sc ∪ rfe.
Proof using WF.
  rewrite path_union.
  generalize (sc_trans Wf_sc); ins; relsf; unionL; [basic_solver|].
  rewrite crE at 2; relsf; unionL.
  { arewrite (sc^? ⨾ rfe ⊆ rfe).
    { rewrite crE; relsf; unionL; [basic_solver|].
      rewrite (dom_l (wf_rfeD WF)) at 1.
      rewrite (dom_r (wf_scD Wf_sc)) at 1.
      type_solver. }
    rewrite ct_begin, rtE; relsf; unionL; [basic_solver|].
    rewrite ct_begin.
    rewrite (wf_rfeD WF).
    type_solver. }
  rewrite (dom_r (wf_rfeD WF)).
  rewrite <- !seqA.
  rewrite inclusion_ct_seq_eqv_r, !seqA.
  rewrite (dom_l (wf_scD Wf_sc)) at 2.
  type_solver.
Qed.

Lemma ppo_helper : ppo ⊆
 ⦗R⦘ ⨾ (data ∪ ctrl ∪ addr ⨾ sb^? ∪ rfi ∪ rmw ∪ rmw_dep ⨾ sb^?)＊ ⨾  
   (⦗R_ex⦘ ⨾ sb)^?⨾ ⦗W⦘.
Proof using WF.
unfold imm_s_ppo.ppo.
rewrite path_ut_first.
rewrite !seq_union_l, !seq_union_r; unionL.
{ basic_solver 21. }
hahn_frame_l.
hahn_frame_l.
hahn_frame_r.
rewrite WF.(data_in_sb).
rewrite WF.(ctrl_in_sb).
rewrite WF.(addr_in_sb).
rewrite WF.(rmw_dep_in_sb).
rewrite WF.(rmw_in_sb).
arewrite (rfi ⊆ sb).
arewrite_id ⦗R_ex⦘ at 2.
generalize (@sb_trans G); ins; relsf.
Qed.

Lemma rmwrf_ct_Acq_in_ar_rfrmw_ct : (rmw ⨾ rf)⁺ ⨾ ⦗Acq⦘ ⊆ (ar G sc ∪ rf ⨾ rmw)⁺.
Proof using WF.
  rewrite rmw_W_ex at 1. rewrite !seqA.
  rewrite clos_trans_rotl, !seqA.
  arewrite (⦗W_ex⦘ ⨾ rf ⨾ ⦗Acq⦘ ⊆ ar G sc).
  { rewrite rfi_union_rfe, !seq_union_l, !seq_union_r.
    unionL.
    2: { rewrite rfe_in_ar. basic_solver. }
    rewrite (dom_r WF.(wf_rfiD)), !seqA. rewrite <- id_inter.
    unfold ar, ar_int. eauto with hahn. }
  rewrite WF.(rmw_in_ar_int) at 1. rewrite ar_int_in_ar with (sc:=sc).
  arewrite (⦗W_ex⦘ ⨾ rf ⨾ rmw ⊆ ar G sc ∪ rf ⨾ rmw).
  arewrite (ar G sc ⊆ ar G sc ∪ rf ⨾ rmw) at 1.
  arewrite (ar G sc ⊆ ar G sc ∪ rf ⨾ rmw) at 3.
  rewrite <- ct_end.
  rewrite ct_step with (r:=ar G sc ∪ rf ⨾ rmw) at 1.
  apply ct_ct.
Qed.

Lemma rmwrf_rt_Acq_in_ar_rfrmw_rt : (rmw ⨾ rf)＊ ⨾ ⦗Acq⦘ ⊆ (ar G sc ∪ rf ⨾ rmw)＊.
Proof using WF.
  rewrite !rtE, seq_union_l. rewrite rmwrf_ct_Acq_in_ar_rfrmw_ct. basic_solver.
Qed.

Lemma nS_imm_co_in_sb (S : actid -> Prop) w wnext
      (WW : is_w lab w)
      (NSW : ~ S w)
      (NCOIMM : immediate (co ⨾ ⦗S⦘) w wnext)
      (ISSNEXT : S wnext)
      (CONEXT : co w wnext)
      (FOR_SPLIT : ⦗set_compl S⦘ ⨾ immediate co ⊆ sb) :
  sb w wnext.
Proof using WF.
  clear -WF WW NSW FOR_SPLIT NCOIMM ISSNEXT CONEXT. simpls. desc.
  apply clos_trans_of_transitiveD; [apply sb_trans|].
  apply (inclusion_t_t FOR_SPLIT).
  eapply ct_imm1 in CONEXT.
  2: by apply WF.(co_irr).
  2: by apply WF.(co_trans).
  2: by intros x [y H']; apply WF.(wf_coE) in H'; apply seq_eqv_l in H'; desf; eauto.
  apply t_rt_step in CONEXT. destruct CONEXT as [z [IMMS IMM]].
  apply t_rt_step. exists z; split; [|apply seq_eqv_l; split; [|done]].
  { apply rtE in IMMS. destruct IMMS as [IMMS|IMMS].
    { red in IMMS; desf. apply rt_refl. }
    assert (immediate (co ⨾ ⦗S⦘) z wnext) as IMM'.
    { red; split; [apply seq_eqv_r; split; auto|].
      { apply clos_trans_immediate1; auto.
        eapply WF.(co_trans). }
      ins. eapply NCOIMM; [|by apply R2].
      apply seq_eqv_r in R1; destruct R1 as [R1 R3].
      apply seq_eqv_r; split; auto.
      eapply WF.(co_trans); [|by apply R1].
      apply clos_trans_immediate1; auto.
      eapply WF.(co_trans). }
    clear IMM.
    induction IMMS.
    { apply rt_step. apply seq_eqv_l; split; auto. }
    assert (co y wnext) as YNEXT.
    { apply clos_trans_immediate1; auto.
      eapply WF.(co_trans).
      eapply transitive_ct; [by apply IMMS2|].
      eapply clos_trans_immediate2.
      { apply WF.(co_trans). }
      { apply WF.(co_irr). }
      { red; ins. apply WF.(wf_coE) in REL.
        apply seq_eqv_l in REL; destruct REL as [_ REL].
        apply seq_eqv_r in REL. apply REL. }
      destruct IMM' as [II _].
      apply seq_eqv_r in II; apply II. }
    assert (immediate (co ⨾ ⦗S⦘) y wnext) as YNEXTIMM.
    { red; split; [by apply seq_eqv_r; split|].
      ins. eapply NCOIMM; [|by apply R2].
      apply seq_eqv_r in R1; destruct R1 as [R1 R3].
      apply seq_eqv_r; split; auto.
      eapply WF.(co_trans); [|by apply R1].
      apply clos_trans_immediate1; auto.
      eapply WF.(co_trans). }
    eapply rt_trans.
    { by apply IHIMMS1. }
    apply IHIMMS2; auto.
    { apply WF.(wf_coD) in YNEXT.
      apply seq_eqv_l in YNEXT; desf. }
    intros NISS. eapply NCOIMM; apply seq_eqv_r; split; auto.
    2: by apply NISS.
    2: done.
    apply clos_trans_immediate1; auto.
      by apply WF.(co_trans). }
  intros HH. apply rtE in IMMS; destruct IMMS as [IMSS|IMMS].
  { red in IMSS; desf. }
  eapply NCOIMM; apply seq_eqv_r; split; auto.
  2: by apply HH.
  all: apply clos_trans_immediate1; auto.
  all: apply WF.(co_trans).
Qed.

Lemma wf_rfirmwsf : functional (rfi ⨾ rmw).
Proof using WF CON. arewrite (rfi ⊆ rf). eapply wf_rfrmwsf; eauto. Qed.

Lemma wf_rfirmwf : functional (rfi ⨾ rmw)⁻¹.
Proof using WF. arewrite (rfi ⊆ rf). eapply wf_rfrmwf; eauto. Qed.

Lemma rmw_in_ppo_loc : rmw ⊆ ppo ∩ same_loc.
Proof using WF.
  apply inclusion_inter_r.
  { by apply rmw_in_ppo. }
  apply WF.(wf_rmwl).
Qed.

Lemma no_ar_rf_ppo_loc_to_init : (ar G sc ∪ rf ⨾ ppo ∩ same_loc) ;; <|is_init|> ≡ ∅₂.
Proof using WF CON.
  split; [|basic_solver].
  rewrite seq_union_l, seqA, no_ar_to_init; auto.
  arewrite (ppo ∩ same_loc ⊆ ppo).
  rewrite WF.(ppo_in_sb). rewrite no_sb_to_init.
  basic_solver.
Qed.

Lemma wf_ar_rf_ppo_locE :
  ar G sc ∪ rf ;; ppo ∩ same_loc ≡ <|E|> ;; (ar G sc ∪ rf ;; ppo ∩ same_loc) ;; <|E|>.
Proof using WF CON WF_SC.
  rewrite wf_arE at 1; auto.
  rewrite (dom_l WF.(wf_rfE)) at 1.
  rewrite (dom_r WF.(wf_ppoE)) at 1.
  basic_solver 10.
Qed.

Lemma wf_ar_rf_ppo_loc_ctE :
  (ar G sc ∪ rf ;; ppo ∩ same_loc)⁺ ≡ <|E|> ;; (ar G sc ∪ rf ;; ppo ∩ same_loc)⁺ ;; <|E|>.
Proof using WF WF_SC CON.
  split; [|basic_solver].
  rewrite wf_ar_rf_ppo_locE at 1; auto.
  rewrite inclusion_ct_seq_eqv_l.
    by rewrite inclusion_ct_seq_eqv_r.
Qed.

End ImmProperties.
