Require Import Setoid.
From hahn Require Import Hahn.
From imm Require Import AuxDef Events Execution Execution_eco
     imm_bob imm_s_ppo imm_s imm_s_hb CombRelations SubExecution AuxRel2.
From imm Require Import AuxRel.

Set Implicit Arguments.

Section RPPO.
Variable G : execution.
Variable WF : Wf G.
Variable COM : complete G.
Variable sc : relation actid.
Variable IMMCON : imm_consistent G sc.

(* Notation "'acts'" := (acts_set G). *)
Notation "'sb'" := (sb G).
Notation "'rmw'" := (rmw G).
Notation "'data'" := (data G).
Notation "'addr'" := (addr G).
Notation "'ctrl'" := (ctrl G).
Notation "'rmw_dep'" := (rmw_dep G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'coe'" := (coe G).
Notation "'fr'" := (fr G).

Notation "'eco'" := (eco G).

Notation "'bob'" := (bob G).
Notation "'fwbob'" := (fwbob G).
Notation "'ppo'" := (ppo G).
Notation "'fre'" := (fre G).
Notation "'rfi'" := (rfi G).
Notation "'rfe'" := (rfe G).
Notation "'deps'" := (deps G).
Notation "'detour'" := (detour G).
Notation "'release'" := (release G).
Notation "'sw'" := (sw G).
Notation "'hb'" := (hb G).

Notation "'urr'" := (urr G sc).
Notation "'c_acq'" := (c_acq G sc).
Notation "'c_cur'" := (c_cur G sc).
Notation "'c_rel'" := (c_rel G sc).
Notation "'t_acq'" := (t_acq G sc).
Notation "'t_cur'" := (t_cur G sc).
Notation "'t_rel'" := (t_rel G sc).
Notation "'S_tm'" := (S_tm G).
Notation "'S_tmr'" := (S_tmr G).
Notation "'msg_rel'" := (msg_rel G sc).

Notation "'lab'" := (lab G).
Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'mod'" := (Events.mod lab).
Notation "'same_loc'" := (same_loc lab).

Notation "'E'" := (acts_set G).
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

Definition rppo := (ctrl ∪ addr ⨾ sb^? ∪ rmw_dep ⨾ sb
                         ∪ ⦗R_ex⦘ ⨾ sb) ⨾ ⦗ W ⦘.

Lemma wf_rppoE : rppo ≡ ⦗E⦘ ⨾ rppo ⨾ ⦗E⦘.
Proof using WF.
  split; [|basic_solver].
  unfold rppo.
  rewrite (wf_ctrlE WF) at 1.
  rewrite (wf_addrE WF) at 1.
  rewrite wf_sbE at 1 2 3.
  rewrite (wf_rmw_depE WF) at 1.
  (* rewrite (wf_rmwE WF) at 1. *)
  basic_solver 10.
Qed.

Lemma wf_rppoD : rppo ≡ ⦗R⦘ ⨾ rppo ⨾ ⦗W⦘.
Proof using WF.
  split; [|basic_solver].
  unfold rppo.
  rewrite (wf_ctrlD WF) at 1.
  rewrite (wf_addrD WF) at 1.
  rewrite (wf_rmw_depD WF) at 1.
  (* rewrite (wf_rmwD WF) at 1. *)
  generalize R_ex_in_R.
  basic_solver 20.
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
  rewrite (dom_r (wf_rmw_depD WF)).
  unfold rppo. basic_solver 10.
Qed.

Lemma R_ex_sb_W_in_rppo : ⦗R_ex⦘ ⨾ sb ⨾ ⦗W⦘ ⊆ rppo.
Proof using.
  unfold rppo. basic_solver 10.
Qed.

Lemma rppo_in_ppo : rppo ⊆ ppo.
Proof using WF.
  unfold rppo, imm_s_ppo.ppo. hahn_frame.
  rewrite (wf_ctrlD WF) at 1.
  rewrite (dom_l (wf_addrD WF)) at 1.
  (* rewrite (dom_l (wf_rmwD WF)) at 1. rewrite R_ex_in_R at 1. *)
  rewrite (dom_l (wf_rmw_depD WF)) at 1.
  arewrite (⦗R_ex⦘ ⊆ ⦗R⦘ ⨾ ⦗R_ex⦘).
  { type_solver. }
  rewrite <- !seq_union_r.
  hahn_frame.
  unionL.
  all: rewrite <- ct_step; eauto 10 with hahn.
Qed.

Lemma rppo_in_sb : rppo ⊆ sb.
Proof using WF. by rewrite rppo_in_ppo, ppo_in_sb. Qed.

Lemma rppo_sb_in_rppo : rppo ⨾ sb ⨾ ⦗W⦘ ⊆ rppo.
Proof using WF.
  unfold rppo.
  hahn_frame. arewrite_id ⦗W⦘. rewrite seq_id_l.
  rewrite !seq_union_l, !seqA.
  rewrite (ctrl_sb WF).
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

Lemma data_rfi_rmw_rppo_in_ppo : ⦗R⦘ ⨾ (data ∪ rfi ∪ rmw)＊ ⨾ rppo ⊆ ppo.
Proof using.
  unfold rppo, imm_s_ppo.ppo.
  hahn_frame.
  rewrite <- rt_ct.
  apply seq_mori.
  { apply clos_refl_trans_mori; eauto 10 with hahn. }
  unionL.
  all: by rewrite <- ct_step; eauto 10 with hahn.
Qed.

Lemma data_rfi_rppo_in_ppo : ⦗R⦘ ⨾ (data ∪ rfi)＊ ⨾ rppo ⊆ ppo.
Proof using.
  arewrite (rfi ⊆ rfi ∪ rmw). rewrite <- unionA.
  apply data_rfi_rmw_rppo_in_ppo.
Qed.

Lemma detour_rfe_data_rfi_rmw_rppo_in_detour_rfe_ppo :
  (detour ∪ rfe) ⨾ (data ∪ rfi ∪ rmw)＊ ⨾ rppo ⊆ (detour ∪ rfe) ⨾ ppo.
Proof using WF.
  rewrite (dom_r (wf_detourD WF)) at 1.
  rewrite (dom_r (wf_rfeD WF)) at 1.
  rewrite <- seq_union_l, !seqA.
    by rewrite data_rfi_rmw_rppo_in_ppo.
Qed.

Lemma detour_rfe_data_rfi_rppo_in_detour_rfe_ppo :
  (detour ∪ rfe) ⨾ (data ∪ rfi)＊ ⨾ rppo ⊆ (detour ∪ rfe) ⨾ ppo.
Proof using WF.
  arewrite (rfi ⊆ rfi ∪ rmw). rewrite <- unionA.
  apply detour_rfe_data_rfi_rmw_rppo_in_detour_rfe_ppo.
Qed.

(* Lemma rmw_in_rppo : rmw ⊆ rppo. *)
(* Proof using WF. *)
(*   rewrite (dom_r (wf_rmwD WF)). *)
(*   unfold rppo. basic_solver 10. *)
(* Qed. *)

(* Lemma rmw_sb_W_in_rppo : rmw ⨾ sb ⨾ ⦗W⦘ ⊆ rppo. *)
(* Proof using WF. *)
(*   rewrite (dom_l (wf_rmwD WF)), (rmw_in_sb WF), !seqA. *)
(*   arewrite (sb ⨾ sb ⊆ sb). *)
(*   { apply transitiveI. apply sb_trans. } *)
(*   unfold rppo. basic_solver 10. *)
(* Qed. *)

(* Lemma rmw_sb_cr_W_in_rppo : rmw ⨾ sb^? ⨾ ⦗W⦘ ⊆ rppo. *)
(* Proof using WF. *)
(*   rewrite crE. rewrite seq_union_l, seq_union_r, seq_id_l. *)
(*   rewrite rmw_sb_W_in_rppo. *)
(*   rewrite rmw_in_rppo. eauto with hahn hahn_full. *)
(* Qed. *)

End RPPO.

Lemma sub_rppo_in G G' sc sc'
      (SUB : sub_execution G G' sc sc')
      (RMWCLOS : codom_rel (⦗acts_set G'⦘ ⨾ (rmw G)) ⊆₁ acts_set G') :
  rppo G' ⊆ rppo G.
Proof using.
  unfold rppo.
  rewrite (sub_ctrl SUB).
  rewrite (sub_addr SUB).
  rewrite (sub_sb SUB) at 1 2.
  rewrite (sub_frmw SUB).
  (* rewrite (sub_rmw SUB) at 1. *)
  rewrite (sub_W SUB).
  rewrite (sub_R_ex SUB).
  hahn_frame.
  unionL.
  1-3: basic_solver 12.
  unionR right.
  rewrite (dom_l (@wf_sbE G')).
  rewrite (sub_sb_in SUB).
  unfolder. ins. desf.
Qed.
