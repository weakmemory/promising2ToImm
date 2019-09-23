Require Import Setoid.
From hahn Require Import Hahn.
From imm Require Import Events Execution Execution_eco
     imm_common imm_s imm_s_hb CombRelations.
Require Import AuxRel AuxRel2.

Set Implicit Arguments.

Section ImmProperties.
Variable G : execution.
Variable WF : Wf G.
Variable sc : relation actid.

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

End ImmProperties.
