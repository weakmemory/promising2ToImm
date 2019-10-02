Require Import Setoid.
From hahn Require Import Hahn.
From imm Require Import Events Execution Execution_eco
     imm_common imm_s imm_s_hb CombRelations AuxDef.
Require Import AuxRel AuxRel2.
Require Import TraversalConfig Traversal.
Require Import ExtTraversal.
Require Import ImmProperties.

Set Implicit Arguments.

Section ExtTraversalProperties.
Variable G : execution.
Variable WF : Wf G.
Variable COM : complete G.
Variable sc : relation actid.
Variable IMMCON : imm_consistent G sc.

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
Notation "'rppo'" := G.(rppo).

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
Notation "'W_' l" := (W ∩₁ Loc_ l) (at level 1).

Notation "'Pln'" := (fun x => is_true (is_only_pln lab x)).
Notation "'Rlx'" := (fun x => is_true (is_rlx lab x)).
Notation "'Rel'" := (fun x => is_true (is_rel lab x)).
Notation "'Acq'" := (fun x => is_true (is_acq lab x)).
Notation "'Acqrel'" := (fun x => is_true (is_acqrel lab x)).
Notation "'Sc'" := (fun x => is_true (is_sc lab x)).
Notation "'Acq/Rel'" := (fun a => is_true (is_ra lab a)).

Variable T : ext_trav_config.
Variable ETCCOH : etc_coherent G sc T.

Notation "'S'" := (reserved T).
Notation "'C'" := (ecovered T).
Notation "'I'" := (eissued  T).

Lemma dom_rf_rmw_S_in_I : dom_rel (⦗W_ex⦘ ⨾ rf ⨾ rmw ⨾ ⦗S⦘) ⊆₁ I.
Proof using WF ETCCOH.
  rewrite rmw_W_ex, !seqA.
  arewrite (⦗W_ex⦘ ⨾ ⦗S⦘ ⊆ ⦗S ∩₁ W_ex⦘) by basic_solver.
  rewrite ETCCOH.(etc_S_W_ex_rfrmw_I).
  rewrite <- seqA with (r2:=rmw).
  intros x [y HH].
  destruct_seq HH as [WX BB].
  destruct BB as [z BB].
  destruct_seq_l BB as IZ.
  assert (x = z); desf.
  eapply wf_rfrmwf; eauto.
Qed.

Lemma dom_rf_rmw_S : dom_rel (⦗W_ex⦘ ⨾ rf ⨾ rmw ⨾ ⦗S⦘) ⊆₁ S.
Proof using WF ETCCOH.
  rewrite <- ETCCOH.(etc_I_in_S) at 2.
  apply dom_rf_rmw_S_in_I.
Qed.

Lemma rf_rmw_S : ⦗W_ex⦘ ⨾ rf ⨾ rmw ⨾ ⦗S⦘ ≡
                 ⦗S⦘ ⨾ ⦗ W_ex ⦘ ⨾  rf ⨾ rmw ⨾ ⦗S⦘.
Proof using WF ETCCOH.
  apply dom_rel_helper.
  apply dom_rf_rmw_S.
Qed.

Lemma dom_rf_rmw_rt_S : dom_rel (⦗W_ex⦘ ⨾ (rf ⨾ rmw)＊ ⨾ ⦗S⦘) ⊆₁ S.
Proof using WF ETCCOH.
  cut (⦗W_ex⦘ ⨾ (rf ⨾ rmw)＊ ⨾ ⦗S⦘ ⊆ ⦗S⦘ ⨾ (fun _ _ => True)).
  { unfolder; ins; desf; eauto 21; eapply H; splits; eauto 10. }
  apply rt_ind_left with (P:= fun r => ⦗W_ex⦘ ⨾ r ⨾ ⦗S⦘).
  { auto with hahn. }
  { basic_solver. }
  intros k H.
  sin_rewrite rmw_W_ex; rewrite !seqA.
  sin_rewrite H.
  seq_rewrite rf_rmw_S.
  basic_solver.
Qed.

Lemma dom_rf_rmw_ct_S : dom_rel (⦗W_ex⦘ ⨾ (rf ⨾ rmw)⁺ ⨾ ⦗S⦘) ⊆₁ S.
Proof using WF ETCCOH.
  rewrite inclusion_t_rt.
  apply dom_rf_rmw_rt_S.
Qed.

Lemma rfe_rmw_S : dom_rel (rfe ⨾ rmw ⨾ ⦗S⦘) ⊆₁ I.
Proof using WF ETCCOH.
rewrite (rmw_in_rppo WF).
generalize (etc_rppo_S ETCCOH).
basic_solver 21.
Qed.

Lemma nI_rfrmw_in_rfirmw :
  ⦗set_compl I⦘ ⨾ rf ⨾ rmw ⨾ ⦗S⦘ ≡ ⦗set_compl I⦘ ⨾ rfi ⨾ rmw ⨾ ⦗S⦘.
Proof using WF ETCCOH.
  split.
  2: by arewrite (rfi ⊆ rf).
  rewrite rfi_union_rfe. rewrite !seq_union_l, !seq_union_r.
  unionL; [done|].
  rewrite (dom_rel_helper rfe_rmw_S).
  basic_solver.
Qed.

Lemma rt_rf_rmw_S' :
  (rf ⨾ rmw)＊ ⨾ ⦗S⦘ ⊆ (rfi ⨾  rmw)＊ ⨾ (⦗I⦘ ⨾ (rf ⨾ rmw)⁺)^? ⨾ ⦗S⦘.
Proof using WF ETCCOH.
  apply rt_ind_left with (P:= fun r => r ⨾ ⦗S⦘).
  { by eauto with hahn. }
  { basic_solver 12. }
  intros k H. rewrite !seqA, H.
  rewrite rfi_union_rfe at 1. rewrite !seq_union_l; unionL.
  { hahn_frame. rewrite rt_begin at 2. basic_solver 21. }
  arewrite ((rfi ⨾ rmw)＊ ⨾ (⦗I⦘ ⨾ (rf ⨾ rmw)⁺)^? ⊆ (rf ⨾ rmw)＊).
  { arewrite (rfi ⊆ rf); arewrite_id (⦗I⦘); relsf. }
  relsf.
  sin_rewrite rmw_W_ex; rewrite !seqA.
  rewrite (dom_rel_helper dom_rf_rmw_rt_S).
  seq_rewrite (dom_rel_helper rfe_rmw_S).
  arewrite (rfe ⊆ rf).
  rewrite ct_begin.
  basic_solver 21.
Qed.

Lemma nI_rfrmw_rt_in_rfirmw_rt :
  ⦗set_compl I⦘ ⨾ (rf ⨾ rmw)＊ ⨾ ⦗S⦘ ⊆ ⦗set_compl I⦘ ⨾ (rfi ⨾ rmw)＊ ⨾ ⦗S⦘.
Proof using WF ETCCOH.
  rewrite rt_rf_rmw_S'.
  rewrite crE. rewrite !seq_union_l, !seq_union_r, !seq_id_l.
  unionL; [done|].
  rewrite !seqA.
  arewrite (⦗set_compl I⦘ ⨾ (rfi ⨾ rmw)＊ ⨾ ⦗I⦘ ⊆ ∅₂).
  2: basic_solver.
  arewrite (rfi ⊆ rf).
  intros x y HH. apply seq_eqv_l in HH. destruct HH as [AA HH].
  apply AA. eapply rfrmw_rt_I_in_I; eauto.
  { apply ETCCOH. }
  eexists. apply HH.
Qed.

End ExtTraversalProperties.
