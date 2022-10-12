From hahn Require Import Hahn.
From imm Require Import Events Execution imm_s AuxDef.
Require Import ExtTraversalConfig.
Require Import ExtTraversal.
Require Import ExtSimTraversal.
From imm Require Import TLSCoherency.
From imm Require Import IordCoherency.
From imm Require Import TraversalOrder. 
From imm Require Import SimClosure. 
Require Import TlsEventSets.

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

Lemma ext_sim_trav_step_coherence (T T' : trav_label -> Prop)
      (STEP : ext_sim_trav_step G sc T T') :
  (* etc_coherent G sc C'. *)
  tls_coherent G T' /\ iord_coherent G sc T' /\ reserve_coherent G T'. 
Proof using.
  red in STEP. desf.
  inversion STEP; subst.
  all: try by (inversion TS; vauto). 
  all: try by (inversion TS2; vauto).
  inversion TS3; vauto. 
Qed.

Lemma ext_sim_trav_step_ct_coherence (T T' : trav_label -> Prop)
      (STEPS : (ext_sim_trav_step G sc)⁺ T T') :
  tls_coherent G T' /\ iord_coherent G sc T' /\ reserve_coherent G T'. 
Proof using.
  apply ct_end in STEPS. unfolder in STEPS.
  desf. eapply ext_sim_trav_step_coherence; eauto.
Qed.

Lemma ext_sim_trav_step_rt_coherence (T T' : trav_label -> Prop)
      (STEPS : (ext_sim_trav_step G sc)＊ T T')
      (COH0: tls_coherent G T /\ iord_coherent G sc T /\ reserve_coherent G T):
  tls_coherent G T' /\ iord_coherent G sc T' /\ reserve_coherent G T'.
Proof using.
  apply rtE in STEPS.
  unfolder in STEPS. desf.
  eapply ext_sim_trav_step_ct_coherence; eauto.
Qed.

Lemma ext_sim_trav_step_issued_le (T T' : trav_label -> Prop)
      (STEP : ext_sim_trav_step G sc T T'):
  issued T ⊆₁ issued T'.
Proof using.
  red in STEP. destruct STEP as [thread STEP].
  inversion STEP; subst.
  all: try by (inversion TS; rewrite ets_upd; clear;
               simplify_tls_events; basic_solver).
  all: try by (inversion TS1; inversion TS2; rewrite ets_upd0, ets_upd;
               clear; simplify_tls_events; basic_solver). 
  inversion TS1; inversion TS2; inversion TS3; rewrite ets_upd1, ets_upd0, ets_upd; clear; simplify_tls_events; basic_solver. 
Qed.

Lemma ext_sim_trav_steps_issued_le (T T' : trav_label -> Prop)
      (STEPS : (ext_sim_trav_step G sc)＊ T T') :
  issued T ⊆₁ issued T'.
Proof using.
  induction STEPS; auto.
  { by apply ext_sim_trav_step_issued_le. }
  etransitivity; eauto.
Qed.

Lemma ext_sim_trav_step_covered_le (T T' : trav_label -> Prop)
      (STEP : ext_sim_trav_step G sc T T'):
  covered T ⊆₁ covered T'.
Proof using.
  red in STEP. destruct STEP as [thread STEP].
  inversion STEP; subst.
  all: try by (inversion TS; rewrite ets_upd; clear;
               simplify_tls_events; basic_solver).
  all: try by (inversion TS1; inversion TS2; rewrite ets_upd0, ets_upd;
               clear; simplify_tls_events; basic_solver). 
  inversion TS1; inversion TS2; inversion TS3; rewrite ets_upd1, ets_upd0, ets_upd; clear; simplify_tls_events; basic_solver. 
Qed.

Lemma ext_sim_trav_steps_covered_le (T T' : trav_label -> Prop)
      (STEPS : (ext_sim_trav_step G sc)＊ T T'):
  covered T ⊆₁ covered T'.
Proof using.
  induction STEPS; auto.
  { by apply ext_sim_trav_step_covered_le. }
  etransitivity; eauto.
Qed.

Ltac subst_next_T := 
  repeat (match goal with
    | STEP: ext_itrav_step ?G ?sc ?lbl ?T1 ?T2 |- _ =>
        inversion STEP;
        (match goal with | EQ2: T2 ≡₁ _ |- _ => rewrite EQ2; clear EQ2 end);
        clear STEP
    end).

Lemma ext_sim_trav_step_rel_covered (T T' : trav_label -> Prop)
      (STEP : ext_sim_trav_step G sc T T')
      (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T) :
  W ∩₁ Rel ∩₁ issued T' ⊆₁ covered T'.
Proof using.
  red in STEP. destruct STEP as [thread STEP].
  inversion STEP; subst.
  all: subst_next_T; simplify_tls_events; generalize RELCOV; basic_solver 10. 
Qed. 

Lemma ext_sim_trav_steps_rel_covered (T T' : trav_label -> Prop)
      (STEPS : (ext_sim_trav_step G sc)＊ T T')
      (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T) :
  W ∩₁ Rel ∩₁ issued T' ⊆₁ covered T'.
Proof using.
  induction STEPS.
  2: done.
  { eapply ext_sim_trav_step_rel_covered; eauto. }
  apply IHSTEPS2. by apply IHSTEPS1.
Qed.

Lemma ext_sim_trav_step_rmw_covered (T T' : trav_label -> Prop)
      (STEP : ext_sim_trav_step G sc T T')
      (RMWCOV : forall r w (RMW : rmw r w), covered T r <-> covered T w) :
  forall r w (RMW : rmw r w), covered T' r <-> covered T' w.
Proof using WF.
  ins.
  red in STEP. destruct STEP as [thread STEP].
  apply (wf_rmwD WF), seq_eqv_lr in RMW as (RR & RMW & WW).
  inversion STEP; subst; specialize (RMWCOV r w RMW). 
  { inversion TS. 
    etransitivity; [| etransitivity].
    1, 3: eapply set_equiv_exp; rewrite ets_upd; clear; by simplify_tls_events.
    split; intros [HH|HH]; left. 
    all: type_solver. }  
  { inversion TS. 
    etransitivity; [| etransitivity].
    1, 3: eapply set_equiv_exp; rewrite ets_upd; clear; by simplify_tls_events.
    split; intros [HH|HH]; left. 
    all: try type_solver. 
    subst. exfalso; apply NRMW; eexists; eauto. }  
  { inversion TS. 
    etransitivity; [| etransitivity].
    1, 3: eapply set_equiv_exp; rewrite ets_upd; clear; by simplify_tls_events.
    eauto. }  
  { inversion TS. 
    etransitivity; [| etransitivity].
    1, 3: eapply set_equiv_exp; rewrite ets_upd; clear; by simplify_tls_events.
    eauto. }
  { inversion TS. 
    etransitivity; [| etransitivity].
    1, 3: eapply set_equiv_exp; rewrite ets_upd; clear; by simplify_tls_events.
    split; intros [HH|HH]; left. 
    all: try type_solver. 
    subst. exfalso; apply NRMW; eexists; eauto. }  
  { inversion TS1. inversion TS2.
    etransitivity; [| etransitivity].
    1, 3: eapply set_equiv_exp; rewrite ?ets_upd0, ?ets_upd; clear; by simplify_tls_events.
    split; intros [HH|HH]; subst. 
    { left. eapply RMWCOV; eauto. }
    { type_solver. }
    { type_solver. }
    edestruct NRMW; vauto. }
  { inversion TS1. inversion TS2. 
    etransitivity; [| etransitivity].
    1, 3: eapply set_equiv_exp; rewrite ?ets_upd0, ?ets_upd; clear; by simplify_tls_events.
    split; intros [[HH|HH]|HH]; subst. 
    { left. left. eapply RMWCOV; eauto. }
    { right. eapply (wf_rmwf WF); eauto. }
    { apply (dom_r (wf_rmwD WF)) in RMW0. apply seq_eqv_r in RMW0.
      type_solver. }
    { left. left. eapply RMWCOV; eauto. }
    { apply (dom_l (wf_rmwD WF)) in RMW0. apply seq_eqv_l in RMW0.
      type_solver. }
    left. right. eapply wf_rmw_invf; eauto. }
  { inversion TS1. inversion TS2. inversion TS3.
    etransitivity; [| etransitivity].
    1, 3: eapply set_equiv_exp; rewrite ?ets_upd1, ?ets_upd0, ?ets_upd; clear; by simplify_tls_events.
    split; intros [[HH|HH]|HH]; subst. 
    { left. left. eapply RMWCOV; eauto. }
    { right. eapply (wf_rmwf WF); eauto. }
    { apply (dom_r (wf_rmwD WF)) in RMW0. apply seq_eqv_r in RMW0.
      type_solver. }
    { left. left. eapply RMWCOV; eauto. }
    { apply (dom_l (wf_rmwD WF)) in RMW0. apply seq_eqv_l in RMW0.
      type_solver. }
    left. right. eapply wf_rmw_invf; eauto. }
  { inversion TS. 
    etransitivity; [| etransitivity].
    1, 3: eapply set_equiv_exp; rewrite ets_upd; clear; by simplify_tls_events.
    split; intros HH; by apply RMWCOV. }
Qed. 

Lemma ext_sim_trav_steps_rmw_covered (T T' : trav_label -> Prop)
      (STEPS : (ext_sim_trav_step G sc)＊ T T')
      (RMWCOV : forall r w (RMW : rmw r w), covered T r <-> covered T w) :
  forall r w (RMW : rmw r w), covered T' r <-> covered T' w.
Proof using WF.
  induction STEPS.
  2: done.
  { eapply ext_sim_trav_step_rmw_covered; eauto. }
  apply IHSTEPS2. by apply IHSTEPS1.
Qed.

Lemma ext_sim_trav_step_in_trav_steps:
  ext_sim_trav_step G sc ⊆ (ext_trav_step G sc)⁺.
Proof using.
  intros C C' [tid TT].
  inv TT.
  1-5, 9: by apply t_step; eexists; eauto.
  1,2: by eapply t_trans; apply t_step; eexists; eauto.
  eapply t_trans.
  2: by apply t_step; eexists; eauto.
  eapply t_trans; apply t_step; eexists; eauto. 
Qed.

Lemma ext_isim_trav_step_new_e_tid thread (T T' : trav_label -> Prop)
      (STEP : ext_isim_trav_step G sc thread T T') :
  covered T' ∪₁ issued T' ≡₁
  covered T ∪₁ issued T ∪₁ (covered T' ∪₁ issued T') ∩₁ Tid_ thread.
Proof using WF.
  inv STEP.
  1-6, 9: subst_next_T; clear; simplify_tls_events; basic_solver 10.
  all: subst_next_T; clear -RMW WF; simplify_tls_events;
    assert (tid r = tid w) as TID by (eapply wf_rmwt; eauto);
    basic_solver 10. 
Qed.

End ExtSimTraversalProperties.
