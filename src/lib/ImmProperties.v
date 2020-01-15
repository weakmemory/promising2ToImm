Require Import Setoid.
From hahn Require Import Hahn.
From imm Require Import Events Execution Execution_eco
     imm_bob imm_s_ppo imm_s imm_s_hb CombRelations AuxDef TraversalConfig.
Require Import AuxRel AuxRel2.

Set Implicit Arguments.

Section ImmProperties.
Variable G : execution.
Variable WF : Wf G.
Variable sc : relation actid.
Variable CON : imm_consistent G sc.

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

Lemma wf_immcoPtf P : functional (immediate (<|P|> ;; co))⁻¹.
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
    (DRES : dom_rel (rf ;; rmw ;; <|P'|>) ⊆₁ P) :
  rf ;; rmw ;; <|P'|> ⊆ immediate (⦗P⦘ ⨾ co).
Proof using WF CON.
  assert (sc_per_loc G) as SPL.
  { apply coherence_sc_per_loc. apply CON. }

  rewrite <- immediate_inter_mori with (x:=co).
  2: basic_solver.
  apply inclusion_inter_r.
  2: { rewrite <- seqA. rewrite rfrmw_in_im_co; eauto. basic_solver. }
  rewrite <- rf_rmw_in_co; auto.
  2: by apply CON.
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
  rf ;; rmw ⊆ eco.
Proof using WF.
  rewrite rf_in_eco. rewrite rmw_in_fr; auto.
  rewrite fr_in_eco.
  apply transitiveI. by apply eco_trans.
Qed.

Lemma rfrmw_sb_irr : 
  irreflexive (rf ;; rmw ;; sb).
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

(* TODO: fix lemma in imm_s.v *)
Lemma rfe_n_same_tid (COH: coherence G) : rfe ∩ same_tid ⊆ ∅₂.
Proof using WF.
  arewrite (rfe ∩ same_tid ⊆ rfe ∩ (<|E|> ;; same_tid ;; <|E|>)).
  { rewrite WF.(wf_rfeE) at 1. basic_solver. }
  arewrite (⦗E⦘ ⨾ same_tid ⨾ ⦗E⦘ ⊆ same_tid ∩ (⦗E⦘ ⨾ same_tid ⨾ ⦗E⦘)) by basic_solver.
  rewrite tid_sb.
  rewrite !inter_union_r.
  unionL.
  3: { rewrite WF.(wf_rfeD). rewrite init_w; eauto. type_solver. }
  2: { unfolder. ins. desf.
       eapply COH. eexists. split.
       { eby apply sb_in_hb. }
       right. apply rf_in_eco.
       match goal with
       | H : rfe _ _ |- _ => apply H
       end. }
  unfolder. ins. desf.
  { eapply eco_irr; eauto. apply rf_in_eco.
    match goal with
    | H : rfe _ _ |- _ => apply H
    end. }
  eapply (thread_rfe_sb WF (coherence_sc_per_loc COH)).
  basic_solver 10.
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

End ImmProperties.

