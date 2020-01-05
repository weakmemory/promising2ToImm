Require Import Classical Peano_dec Setoid PeanoNat.
From hahn Require Import Hahn.

From imm Require Import Events.
From imm Require Import Execution.
From imm Require Import Execution_eco.
From imm Require Import imm_s_hb.
From imm Require Import imm_s.
From imm Require Import imm_bob imm_s_ppo.
From imm Require Import CombRelations.
From imm Require Import imm_s_rfrmw.
From imm Require Import AuxDef.
Require Import AuxRel2.
Require Import TraversalConfig.
Require Import Traversal.
Require Import ImmProperties.

Section TraversalProperties.
  Variable G : execution.
  Variable WF : Wf G.
  Variable sc : relation actid.
  Variable IMMCON : imm_consistent G sc.

  Notation "'acts'" := G.(acts).
  Notation "'sb'" := G.(sb).
  Notation "'rmw'" := G.(rmw).
  Notation "'data'" := G.(data).
  Notation "'addr'" := G.(addr).
  Notation "'ctrl'" := G.(ctrl).
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

Notation "'R_ex'" := (R_ex G).
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

Variable T : trav_config.
Hypothesis TCCOH : tc_coherent G sc T.

Lemma itrav_stepE e T' (STEP : itrav_step G sc e T T') :
  E e.
Proof using TCCOH.
  assert (tc_coherent G sc T') as TCCOH'.
  { eapply trav_step_coherence; eauto. red. eauto. }
  red in STEP. desf.
  { eapply coveredE with (T:=T'); eauto. apply COVEQ. basic_solver. }
  eapply issuedE with (T:=T'); eauto. apply ISSEQ. basic_solver.
Qed.

Lemma dom_rfrmw_issuable_in_I :
  dom_rel (rf ⨾ rmw ⨾ ⦗issuable G sc T⦘) ⊆₁ issued T.
Proof using WF TCCOH.
  rewrite <- rfrmw_coverable_issuable_in_I; eauto.
  basic_solver 10.
Qed.

Lemma I_rfrmw_issuable :
  rf ⨾ rmw ⨾ ⦗issuable G sc T⦘ ≡ <|issued T|> ⨾ rf ⨾ rmw ⨾ ⦗issuable G sc T⦘.
Proof using WF TCCOH. apply dom_rel_helper. by apply dom_rfrmw_issuable_in_I. Qed.

Lemma issuable_W_ex_in_codom_I_rfrmw :
  issuable G sc T ∩₁ W_ex ⊆₁ codom_rel (⦗issued T⦘ ⨾ rf ⨾ rmw).
Proof using WF TCCOH IMMCON.
  rewrite W_ex_in_codom_rfrmw; eauto.
  rewrite set_interC. rewrite <- codom_eqv1, seqA.
  rewrite I_rfrmw_issuable; auto.
  basic_solver 10.
Qed.

End TraversalProperties.
