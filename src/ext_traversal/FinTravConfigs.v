From hahn Require Import Hahn.
From imm Require Import Events.
From imm Require Import Execution.
From imm Require Import imm_s.
From imm Require Import CombRelations.
From imm Require Import ProgToExecutionProperties.
From imm Require Import RMWinstrProps.
From hahnExt Require Import HahnExt.
From imm Require Import FairExecution.
From imm Require Import FinExecution.
From imm Require Import FinThreads.
From hahnExt Require Import HahnExt. 
From imm Require Import TLSCoherency.
From imm Require Import IordCoherency.
From imm Require Import TraversalOrder. 
From imm Require Import SimClosure.
From imm Require Import TlsEventSets.
Require Import ExtTraversalConfig.
Require Import ExtTraversal.
Require Import ExtSimTraversal.
Require Import ExtSimTraversalProperties.
Import ListNotations.
Require Import IndefiniteDescription.

Set Implicit Arguments. 

Definition tls_fin (T: trav_label -> Prop) :=
  set_finite (T ∩₁ event ↓₁ (set_compl is_init)). 

Global Add Parametric Morphism : tls_fin with signature
       Basics.flip set_subset ==> Basics.impl as tls_fin_mori. 
Proof using. ins. red. unfold tls_fin. ins. by rewrite H. Qed. 

Global Add Parametric Morphism : tls_fin with signature
       set_equiv ==> iff as tls_fin_more. 
Proof using. ins. destruct H. split; apply tls_fin_mori; auto. Qed. 

Lemma tls_fin_union T1 T2 (FIN1: tls_fin T1) (FIN2: tls_fin T2):
  tls_fin (T1 ∪₁ T2). 
Proof using. 
  unfold tls_fin in *. rewrite set_inter_union_l.
  apply set_finite_union. split; auto. 
Qed. 

Lemma tls_fin_T_fin T (FIN: set_finite T):
  tls_fin T. 
Proof using.
  unfold tls_fin. eapply set_finite_mori; eauto. red. basic_solver 10. 
Qed. 

Section FinTravConfigs.
  Variable (G: execution).
  Variable (sc: relation actid).
  Hypothesis (WF: Wf G). 

  Lemma init_tls_fin:
    tls_fin (init_tls G).
  Proof using.
    unfold init_tls, tls_fin. rewrite set_pair_alt.
    exists []. basic_solver 10. 
  Qed.


  Lemma tls_fin_event_set T (a: trav_action) (TFIN: tls_fin T):
    set_finite ((event ↑₁ (T ∩₁ action ↓₁ eq a)) \₁ is_init). 
  Proof using. 
    destruct TFIN as [ts TFIN]. exists (map event ts). ins.
    apply in_map_iff. exists (mkTL a x). split; auto.
    destruct IN. 
    apply TFIN. split; [| done].
    by apply tls_set_alt.
  Qed. 

  Lemma dom_sb_S_rfrmw_tls_fin T rrf M (TFIN: tls_fin T):
    set_finite (dom_sb_S_rfrmw G T rrf M).
  Proof using WF.
    unfold dom_sb_S_rfrmw.
    rewrite rmw_non_init_lr; eauto. rewrite !codom_seq, codom_eqv.
    rewrite set_interC, <- dom_eqv1.
    rewrite no_sb_to_init, seqA, <- id_inter. 
    rewrite <- seqA. apply fin_dom_rel_fsupp.
    { eapply fsupp_sb; auto. }
    rewrite set_interC. by apply tls_fin_event_set. 
  Qed. 

  (* TODO: move *)
  Lemma tls_set_fin_events_fin (a: trav_action) (M: actid -> Prop)
        (EFIN: set_finite M):
    set_finite (eq a <*> M). 
  Proof using. 
    destruct EFIN as [es EFIN]. exists (map (mkTL a) es). intros [? e] [<- Me]. 
    apply in_map_iff. exists e. split; auto. 
  Qed. 
  
  Lemma dom_sb_S_rfrmw_same_reserved rrf P T1 T2
        (SAME_RES: reserved T1 ≡₁ reserved T2):
    dom_sb_S_rfrmw G T1 rrf P ≡₁ dom_sb_S_rfrmw G T2 rrf P.
  Proof using. unfold dom_sb_S_rfrmw. by rewrite SAME_RES. Qed. 

  Lemma isim_step_preserves_fin (T T': trav_label -> Prop) (t: thread_id)
        (FIN: tls_fin T) (STEP: ext_isim_trav_step G sc t T T'):
      tls_fin T'.
  Proof using WF.
    inversion STEP; subst.
    { inversion TS. rewrite ets_upd.
      rewrite set_unionA. apply tls_fin_union; auto.
      simpl. simpl_sets. apply tls_fin_T_fin, set_finite_eq. }
    { inversion TS. rewrite ets_upd.
      rewrite set_unionA. apply tls_fin_union; auto.
      simpl. simpl_sets. apply tls_fin_T_fin, set_finite_eq. }
    { inversion TS. rewrite ets_upd.
      rewrite set_unionA. apply tls_fin_union; auto.
      simpl. simpl_sets. apply tls_fin_T_fin, set_finite_eq. }
    { inversion TS. rewrite ets_upd.
      rewrite set_unionA. apply tls_fin_union; auto.
      apply tls_fin_T_fin, set_finite_union. split. 
      { apply set_finite_eq. }
      apply tls_set_fin_events_fin. simpl. apply set_finite_union.
      split; auto using set_finite_eq, dom_sb_S_rfrmw_tls_fin. }
    { inversion TS. rewrite ets_upd.
      rewrite set_unionA. apply tls_fin_union; auto.
      simpl. simpl_sets. apply tls_fin_T_fin, set_finite_eq. }
    { inversion TS1. inversion TS2. rewrite ets_upd0, ets_upd.
      simpl. simpl_sets. rewrite !set_unionA. apply tls_fin_union; auto.
      apply tls_fin_T_fin. 
      repeat (apply set_finite_union; split); try by (apply set_finite_eq).
      apply tls_set_fin_events_fin. simpl. apply set_finite_union.
      split; auto using set_finite_eq, dom_sb_S_rfrmw_tls_fin. }
    { inversion TS1. inversion TS2. rewrite ets_upd0, ets_upd.
      simpl. simpl_sets. rewrite !set_unionA. apply tls_fin_union; auto.
      apply tls_fin_T_fin. 
      repeat (apply set_finite_union; split); apply set_finite_eq. }
    2: { inversion TS. rewrite ets_upd.
         rewrite set_unionA. apply tls_fin_union; auto.
         simpl. simpl_sets. apply tls_fin_T_fin, set_finite_eq. } 
    inversion TS1. inversion TS2. inversion TS3.
    rewrite ets_upd1, ets_upd0, ets_upd.
    simpl. simpl_sets.
    rewrite dom_sb_S_rfrmw_same_reserved with (T2 := T).
    2: { clear. by simplify_tls_events. }
    rewrite !set_unionA. apply tls_fin_union; auto.      
    apply tls_fin_T_fin.
    repeat (apply set_finite_union; split); try by apply set_finite_eq.
    apply tls_set_fin_events_fin. simpl. apply set_finite_union.
    split; auto using set_finite_eq, dom_sb_S_rfrmw_tls_fin.   
  Qed.

  Lemma sim_steps_preserves_fin T T'
        (STEPS: (ext_sim_trav_step G sc)＊ T T')
        (FIN: tls_fin T):
    tls_fin T'.
  Proof using WF.
    apply rtEE in STEPS as [n [_ STEPS]].
    generalize dependent T'. induction n. 
    { ins. red in STEPS. desc. congruence. }
    intros T'' [T' [STEPS' STEP]]. apply IHn in STEPS'.
    inversion_clear STEP as [t ISTEP].
    eapply isim_step_preserves_fin; eauto.
  Qed.

  (* TODO: move*)
  Lemma fin_exec_exec_tls
        (FIN: fin_exec G)
        (FIN_THREADS: fin_threads G):
    set_finite (exec_tls G).
  Proof using.
    unfold exec_tls.
    destruct FIN as [acts ACTS]. destruct FIN_THREADS as [threads THREADS].
    arewrite ((acts_set G \₁ is_init) ∩₁ is_w (lab G) ⊆₁ acts_set G \₁is_init) by basic_solver.
    rewrite !set_pair_alt. rewrite <- set_inter_union_l.
    exists (flat_map (fun e => map (fun a => mkTL a e) [ta_cover; ta_issue; ta_reserve]
                       ++ map (fun t => mkTL (ta_propagate t) e) threads) acts).
    unfolder. ins. apply in_flat_map.
    exists (event x). split.
    { apply ACTS, IN. }
    destruct x; des; ins; subst; try by tauto. 
    repeat right. apply in_map_iff.
    do 2 red in IN. desc. eexists. splits; vauto.
    apply THREADS, IN. 
  Qed. 

  Lemma fin_exec_tls_fin T
        (FIN: fin_exec G)
        (FIN_THREADS: fin_threads G)
        (TCOH: tls_coherent G T):
    tls_fin T.
  Proof using. 
    destruct TCOH. red. rewrite tls_coh_exec.
    rewrite set_inter_union_l. apply set_finite_union. split.
    { rewrite init_tls_EI. vauto. exists []. basic_solver. }
    eapply set_finite_mori.
    2: { apply fin_exec_exec_tls; eauto. }
    red. basic_solver.
  Qed.
  
End FinTravConfigs. 

