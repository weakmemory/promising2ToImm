From hahn Require Import Hahn.
From imm Require Import Events Execution imm_s AuxDef.
Require Import ExtTraversalConfig.
Require Import ExtTraversal.
Require Import ExtSimTraversal.

Set Implicit Arguments.

Section ExtSimTraversalProperties.
Variable G : execution.
Variable WF : Wf G.
Variable COM : complete G.
Variable sc : relation actid.
Variable IMMCON : imm_consistent G sc.

(* Notation "'acts'" := (acts G). *)
Notation "'sb'" := (sb G).
Notation "'rmw'" := (rmw G).
Notation "'data'" := (data G).
Notation "'addr'" := (addr G).
Notation "'ctrl'" := (ctrl G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'coe'" := (coe G).
Notation "'fr'" := (fr G).

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

Lemma ext_sim_trav_step_coherence (C C' : ext_trav_config)
      (STEP : ext_sim_trav_step G sc C C') :
  etc_coherent G sc C'.
Proof using.
  red in STEP. desf.
  inv STEP; try apply TS.
  all: try apply TS2.
  apply TS3.
Qed.

Lemma ext_sim_trav_step_ct_coherence (C C' : ext_trav_config)
      (STEPS : (ext_sim_trav_step G sc)⁺ C C') :
  etc_coherent G sc C'.
Proof using.
  apply ct_end in STEPS. unfolder in STEPS.
  desf. eapply ext_sim_trav_step_coherence; eauto.
Qed.

Lemma ext_sim_trav_step_rt_coherence (C C' : ext_trav_config)
      (STEPS : (ext_sim_trav_step G sc)＊ C C')
      (TCCOH : etc_coherent G sc C):
  etc_coherent G sc C'.
Proof using.
  apply rtE in STEPS.
  unfolder in STEPS. desf.
  eapply ext_sim_trav_step_ct_coherence; eauto.
Qed.

Lemma ext_sim_trav_step_issued_le (C C' : ext_trav_config)
      (STEP : ext_sim_trav_step G sc C C') :
  eissued C ⊆₁ eissued C'.
Proof using.
  red in STEP. destruct STEP as [thread T].
  destruct T.
  all: unfold eissued; simpls.
  all: basic_solver.
Qed.

Lemma ext_sim_trav_steps_issued_le (C C' : ext_trav_config)
      (STEPS : (ext_sim_trav_step G sc)＊ C C') :
  eissued C ⊆₁ eissued C'.
Proof using.
  induction STEPS; auto.
  { by apply ext_sim_trav_step_issued_le. }
  etransitivity; eauto.
Qed.

Lemma ext_sim_trav_step_covered_le (C C' : ext_trav_config)
      (STEP : ext_sim_trav_step G sc C C') :
  ecovered C ⊆₁ ecovered C'.
Proof using.
  red in STEP. destruct STEP as [thread T].
  destruct T.
  all: unfold ecovered; simpls.
  all: basic_solver.
Qed.

Lemma ext_sim_trav_steps_covered_le (C C' : ext_trav_config)
      (STEPS : (ext_sim_trav_step G sc)＊ C C') :
  ecovered C ⊆₁ ecovered C'.
Proof using.
  induction STEPS; auto.
  { by apply ext_sim_trav_step_covered_le. }
  etransitivity; eauto.
Qed.

Lemma ext_sim_trav_step_rel_covered (C C' : ext_trav_config)
      (STEP : ext_sim_trav_step G sc C C')
      (RELCOV : W ∩₁ Rel ∩₁ eissued C ⊆₁ ecovered C) :
  W ∩₁ Rel ∩₁ eissued C' ⊆₁ ecovered C'.
Proof using.
  red in STEP. destruct STEP as [thread STEP].
  destruct STEP; unfold eissued, ecovered; simpls.
  1,2,4,6: by etransitivity; eauto; basic_solver.
  { etransitivity.
    2: by apply RELCOV.
    basic_solver. }
  { rewrite set_inter_union_r. rewrite RELCOV.
    basic_solver. }
  rewrite set_inter_union_r. rewrite RELCOV.
  basic_solver.
Qed. 

Lemma ext_sim_trav_steps_rel_covered (C C' : ext_trav_config)
      (STEPS : (ext_sim_trav_step G sc)＊ C C')
      (RELCOV : W ∩₁ Rel ∩₁ eissued C ⊆₁ ecovered C) :
  W ∩₁ Rel ∩₁ eissued C' ⊆₁ ecovered C'.
Proof using.
  induction STEPS.
  2: done.
  { eapply ext_sim_trav_step_rel_covered; eauto. }
  apply IHSTEPS2. by apply IHSTEPS1.
Qed.

Lemma ext_sim_trav_step_rmw_covered (C C' : ext_trav_config)
      (STEP : ext_sim_trav_step G sc C C')
      (RMWCOV : forall r w (RMW : rmw r w), ecovered C r <-> ecovered C w) :
  forall r w (RMW : rmw r w), ecovered C' r <-> ecovered C' w.
Proof using WF.
  ins.
  red in STEP. destruct STEP as [thread STEP].
  apply (wf_rmwD WF) in RMW.
  apply seq_eqv_l in RMW. destruct RMW as [RR RMW].
  apply seq_eqv_r in RMW. destruct RMW as [RMW WW].
  destruct STEP; unfold eissued, ecovered in *; simpls.
  all: try by apply RMWCOV.
  { specialize (RMWCOV r w RMW).
    split; intros [HH|HH]; left. 
    all: type_solver. }
  { specialize (RMWCOV r w RMW).
    split; intros [HH|HH]; subst; left. 
    all: try type_solver.
    exfalso. apply NRMW. eexists; eauto. }
  { specialize (RMWCOV r w RMW).
    split; intros [HH|HH]; subst; left. 
    all: try type_solver.
    exfalso. apply NRMW. eexists; eauto. }
  { specialize (RMWCOV r w RMW).
    split; intros [HH|HH]; subst; left. 
    all: try type_solver.
    exfalso. apply NRMW. eexists; eauto. }
  { split; intros [[HH|HH]|HH]; subst. 
    { left. left. by apply (RMWCOV r w RMW). }
    { right. eapply (wf_rmwf WF); eauto. }
    { apply (dom_r (wf_rmwD WF)) in RMW0. apply seq_eqv_r in RMW0.
      type_solver. }
    { left. left. by apply (RMWCOV r w RMW). }
    { apply (dom_l (wf_rmwD WF)) in RMW0. apply seq_eqv_l in RMW0.
      type_solver. }
    left. right. eapply wf_rmw_invf; eauto. }
  split; intros [[HH|HH]|HH]; subst. 
  { left. left. by apply (RMWCOV r w RMW). }
  { right. eapply (wf_rmwf WF); eauto. }
  { apply (dom_r (wf_rmwD WF)) in RMW0. apply seq_eqv_r in RMW0.
    type_solver. }
  { left. left. by apply (RMWCOV r w RMW). }
  { apply (dom_l (wf_rmwD WF)) in RMW0. apply seq_eqv_l in RMW0.
    type_solver. }
  left. right. eapply wf_rmw_invf; eauto.
Qed. 

Lemma ext_sim_trav_steps_rmw_covered (C C' : ext_trav_config)
      (STEPS : (ext_sim_trav_step G sc)＊ C C')
      (RMWCOV : forall r w (RMW : rmw r w), ecovered C r <-> ecovered C w) :
  forall r w (RMW : rmw r w), ecovered C' r <-> ecovered C' w.
Proof using WF.
  induction STEPS.
  2: done.
  { eapply ext_sim_trav_step_rmw_covered; eauto. }
  apply IHSTEPS2. by apply IHSTEPS1.
Qed.

Lemma ext_sim_trav_step_in_trav_steps : ext_sim_trav_step G sc ⊆ (ext_trav_step G sc)⁺.
Proof using.
  intros C C' [tid TT].
  inv TT.
  1-5: by apply t_step; eexists; eauto.
  1,2: by eapply t_trans; apply t_step; eexists; eauto.
  eapply t_trans.
  2: by apply t_step; eexists; eauto.
  eapply t_trans; apply t_step; eexists; eauto.
Qed.

Lemma ext_isim_trav_step_new_e_tid thread (C C' : ext_trav_config)
      (STEP : ext_isim_trav_step G sc thread C C') :
  ecovered C' ∪₁ eissued C' ≡₁
  ecovered C ∪₁ eissued C ∪₁ (ecovered C' ∪₁ eissued C') ∩₁ Tid_ thread.
Proof using WF.
  inv STEP; unfold ecovered, eissued; simpls.
  all: split; [|basic_solver].
  all: unionL; eauto with hahn.
  all: unionR right.
  1-7,9: basic_solver.
  all: arewrite (tid r = tid w); [|basic_solver].
  all: eapply wf_rmwt; eauto.
Qed.

End ExtSimTraversalProperties.
