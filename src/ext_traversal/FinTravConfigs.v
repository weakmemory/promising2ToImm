From hahn Require Import Hahn.
From imm Require Import Events.
From imm Require Import Execution.
From imm Require Import imm_s.
From imm Require Import CombRelations.
From imm Require Import ProgToExecutionProperties.
From imm Require Import RMWinstrProps.
From imm Require Import AuxRel2.
From imm Require Import FairExecution.
From imm Require Import FinExecution.
From imm Require Import Traversal.
From imm Require Import TraversalConfig.
Require Import ExtTraversalConfig.
Require Import ExtTraversal.
Require Import ExtSimTraversal.
Require Import ExtSimTraversalProperties.
Import ListNotations.
Require Import IndefiniteDescription.

(* TODO: move this file to another place *)


Definition tc_fin (tc: trav_config) :=
  ⟪ COV_FIN: set_finite (covered tc \₁ is_init) ⟫ /\
  ⟪ ISS_FIN: set_finite (issued tc \₁ is_init) ⟫.

Definition etc_fin (etc: ext_trav_config) :=
  ⟪ TC_FIN: tc_fin (etc_TC etc) ⟫ /\
  ⟪ RES_FIN: set_finite (reserved etc \₁ is_init) ⟫ .

Section FinTravConfigs.
  Variable (G: execution).
  Variable (sc: relation actid).
  Hypothesis (WF: Wf G). 

  Lemma init_tc_fin:
    tc_fin (init_trav G).
  Proof using.
    unfold init_trav. red. simpl. apply set_finite_union.
    eapply set_finite_mori; [| by apply set_finite_empty].
    red. basic_solver.
  Qed.

  Lemma init_etc_fin:
    etc_fin (ext_init_trav G).
  Proof using.
    red. splits; [by apply init_tc_fin| ].
    unfold ext_init_trav. simpl. 
    eapply set_finite_mori; [| by apply set_finite_empty].
    red. basic_solver.
  Qed.

  Lemma isim_step_preserves_fin (T T': ext_trav_config) (t: thread_id)
        (FIN: etc_fin T) (STEP: ext_isim_trav_step G sc t T T'):
      etc_fin T'.
  Proof using WF.
    red in FIN. desc. red in TC_FIN. desc.

    assert (forall S e, set_finite (S \₁ is_init) ->
                   set_finite ((S ∪₁ eq e) \₁ is_init)) as FIN_HELPER.
    { ins. rewrite set_minus_union_l. apply set_finite_union. split; auto.
      exists [e]. basic_solver. }

    assert (forall w, set_finite ((reserved T ∪₁ eq w ∪₁ dom_sb_S_rfrmw G T (rfi G) (eq w)) \₁ is_init)) as RES'_HELPER.
    { ins. rewrite set_minus_union_l. apply set_finite_union. split; auto.
      unfold dom_sb_S_rfrmw.
      eapply set_finite_mori.
      { red. eapply set_subset_minus; [| by apply set_subset_refl].
        unfold set_inter. red. intros ?. apply proj1. }
      rewrite set_minusE, set_interC, <- dom_eqv1.
      rewrite no_sb_to_init, seqA, <- id_inter. 
      rewrite <- seqA. apply fin_dom_rel_fsupp.
      2: { apply fsupp_sb; auto. }
      eapply set_finite_more; [| by apply RES_FIN]. basic_solver. }
    
    inversion STEP; subst.
    all: red; unfold tc_fin; simpl; splits; auto. 
  Qed.

  Lemma sim_steps_preserves_fin T T'
        (STEPS: (ext_sim_trav_step G sc)＊ T T')
        (FIN: etc_fin T):
    etc_fin T'.
  Proof using WF.
    apply rtEE in STEPS as [n [_ STEPS]].
    generalize dependent T'. induction n. 
    { ins. red in STEPS. desc. congruence. }
    intros T'' [T' [STEPS' STEP]]. apply IHn in STEPS'.
    inversion_clear STEP as [t ISTEP].
    eapply isim_step_preserves_fin; eauto.
  Qed.

End FinTravConfigs. 

