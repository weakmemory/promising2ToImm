Require Import Setoid.
From hahn Require Import Hahn.
From imm Require Import AuxDef Events Execution Execution_eco
     imm_bob imm_s_ppo imm_s imm_s_hb CombRelations SubExecution.
Require Import AuxRel AuxRel2.

Set Implicit Arguments.

Section RPPO.
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

(******************************************************************************)
(** **   *)
(******************************************************************************)

(* TODO: continue from here *)
Definition rppo := (ctrl ∪ addr ⨾ sb^? ∪ rmw_dep^? ⨾ ⦗ R_ex ⦘ ⨾ sb) ⨾ ⦗ W ⦘.

Lemma wf_rppoE : rppo ≡ ⦗E⦘ ⨾ rppo ⨾ ⦗E⦘.
Proof using WF.
  split; [|basic_solver].
  unfold rppo.
  rewrite WF.(wf_ctrlE) at 1.
  rewrite WF.(wf_addrE) at 1.
  rewrite wf_sbE at 1 2.
  rewrite WF.(wf_rmw_depE) at 1.
  basic_solver 10.
Qed.

Lemma wf_rppoD : rppo ≡ ⦗R⦘ ⨾ rppo ⨾ ⦗W⦘.
Proof using WF.
  split; [|basic_solver].
  unfold rppo.
  arewrite (R_ex ⊆₁ R_ex ∩₁ R) at 1.
  { generalize (R_ex_in_R). basic_solver. }
  rewrite WF.(wf_ctrlD) at 1.
  rewrite WF.(wf_addrD) at 1.
  rewrite WF.(wf_rmw_depD) at 1.
  basic_solver 10.
Qed.

Lemma addr_sb_W_in_rppo : addr ⨾ sb^? ⨾ ⦗ W ⦘ ⊆ rppo.
Proof using.
  unfold rppo. basic_solver 10.
Qed.

Lemma ctrl_W_in_rppo : ctrl ⨾ ⦗ W ⦘ ⊆ rppo.
Proof using.
  unfold rppo. basic_solver 10.
Qed.

Lemma rmw_dep_sb_W_in_rppo : rmw_dep ⨾ sb ⨾ ⦗W⦘ ⊆ rppo.
Proof using WF.
  rewrite (dom_r WF.(wf_rmw_depD)).
  unfold rppo. basic_solver 10.
Qed.

Lemma R_ex_sb_W_in_rppo : ⦗R_ex⦘ ⨾ sb ⨾ ⦗W⦘ ⊆ rppo.
Proof using.
  unfold rppo. basic_solver 10.
Qed.

Lemma rppo_in_ppo : rppo ⊆ ppo.
Proof using WF.
  unfold rppo, imm_s_ppo.ppo. hahn_frame.
  rewrite WF.(wf_ctrlD) at 1.
  rewrite (dom_l WF.(wf_addrD)) at 1.
  arewrite (rmw_dep^? ⨾ ⦗R_ex⦘ ⊆ ⦗R⦘ ⨾ rmw_dep^? ⨾ ⦗R_ex⦘).
  { rewrite (dom_l WF.(wf_rmw_depD)) at 1.
    arewrite (⦗R_ex⦘ ⊆ ⦗R⦘ ⨾ ⦗R_ex⦘) at 1.
    { type_solver. }
    basic_solver. }
  rewrite <- !seq_union_r.
  hahn_frame.
  unionL.
  1,2: rewrite <- ct_step; eauto with hahn.
  rewrite <- cr_ct, <- ct_step.
  apply seq_mori; eauto with hahn.
Qed.

Lemma rppo_in_sb : rppo ⊆ sb.
Proof using WF. by rewrite rppo_in_ppo, ppo_in_sb. Qed.

Lemma rppo_sb_in_rppo : rppo ⨾ sb ⨾ ⦗W⦘ ⊆ rppo.
Proof using WF.
  unfold rppo.
  hahn_frame. arewrite_id ⦗W⦘. rewrite seq_id_l.
  rewrite !seq_union_l, !seqA.
  rewrite WF.(ctrl_sb).
  arewrite (sb^? ⨾ sb ⊆ sb^?).
  { generalize (@sb_trans G). basic_solver. }
  arewrite (sb ⨾ sb ⊆ sb).
  2: done.
  apply transitiveI. apply sb_trans.
Qed.

Lemma rppo_cr_sb_in_rppo : rppo ⨾ sb^? ⨾ ⦗W⦘ ⊆ rppo.
Proof using WF.
  rewrite crE. rewrite seq_union_l, seq_union_r. rewrite rppo_sb_in_rppo.
  basic_solver.
Qed.

Lemma data_rfi_rppo_in_ppo : ⦗R⦘ ⨾ (data ∪ rfi)＊ ⨾ rppo ⊆ ppo.
Proof using.
  unfold rppo, imm_s_ppo.ppo.
  hahn_frame.
  rewrite <- rt_ct.
  apply seq_mori.
  { apply clos_refl_trans_mori; eauto 10 with hahn. }
  unionL.
  1,2: by rewrite <- ct_step; eauto 10 with hahn.
  rewrite <- cr_ct, <- ct_step.
  basic_solver 10.
Qed.

Lemma detour_rfe_data_rfi_rppo_in_detour_rfe_ppo :
  (detour ∪ rfe) ⨾ (data ∪ rfi)＊ ⨾ rppo ⊆ (detour ∪ rfe) ⨾ ppo.
Proof using WF.
  rewrite (dom_r WF.(wf_detourD)) at 1.
  rewrite (dom_r WF.(wf_rfeD)) at 1.
  rewrite <- seq_union_l, !seqA.
    by rewrite data_rfi_rppo_in_ppo.
Qed.

Lemma rmw_in_rppo : rmw ⊆ rppo.
Proof using WF.
  rewrite WF.(wf_rmwD), WF.(rmw_in_sb).
  unfold rppo. basic_solver 10.
Qed.

Lemma rmw_sb_W_in_rppo : rmw ⨾ sb ⨾ ⦗W⦘ ⊆ rppo.
Proof using WF.
  rewrite (dom_l WF.(wf_rmwD)), WF.(rmw_in_sb), !seqA.
  arewrite (sb ⨾ sb ⊆ sb).
  { apply transitiveI. apply sb_trans. }
  unfold rppo. basic_solver 10.
Qed.

Lemma rmw_sb_cr_W_in_rppo : rmw ⨾ sb^? ⨾ ⦗W⦘ ⊆ rppo.
Proof using WF.
  rewrite crE. rewrite seq_union_l, seq_union_r, seq_id_l.
  rewrite rmw_sb_W_in_rppo.
  rewrite rmw_in_rppo. eauto with hahn hahn_full.
Qed.

End RPPO.

Lemma sub_rppo_in G G' sc sc' (SUB : sub_execution G G' sc sc') :
  rppo G' ⊆ rppo G.
Proof using.
  unfold rppo.
  rewrite (sub_ctrl SUB).
  rewrite (sub_addr SUB).
  rewrite (sub_sb SUB).
  rewrite (sub_frmw SUB).
  rewrite (sub_R_ex SUB), (sub_W SUB).
  hahn_frame.
  basic_solver 12.
Qed.
