Require Import Setoid.
From hahn Require Import Hahn.
From imm Require Import Events Execution Execution_eco
     TraversalConfig Traversal imm_common imm_s imm_s_hb CombRelations.
Require Import AuxRel AuxRel2.
Require Import ExtTraversal.

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

Lemma rmw_in_rppo : rmw ⊆ rppo.
Proof.
  unfold ExtTraversal.rppo.
  rewrite WF.(wf_rmwD).
  rewrite WF.(rmw_in_sb).
  basic_solver 10.
Qed.

Lemma rf_rmw_S : <|W_ex|> ;; rf ;; rmw ;; <|S|> ≡
                 <|S|> ;; <| W_ex |> ;;  rf ;; rmw ;; <|S|>.
Proof.
  apply dom_rel_helper.
  rewrite rfi_union_rfe, seq_union_l, seq_union_r, dom_union.
  unionL.
  { arewrite (rfi ⊆ sb). rewrite WF.(rmw_in_sb).
    arewrite (sb ;; sb ⊆ sb).
    { apply transitiveI. apply sb_trans. }
    apply ETCCOH. }
  arewrite_id ⦗W_ex⦘. rewrite seq_id_l.
  rewrite rmw_in_rppo.
  etransitivity.
  2: by apply ETCCOH.(etc_I_in_S).
  etransitivity.
  2: by apply ETCCOH.(etc_rppo_S).
  rewrite <- inclusion_id_rt, seq_id_l.
  basic_solver 10.
Qed.

(* Lemma rf_rmw_S_rt *)

End ExtTraversalProperties.
