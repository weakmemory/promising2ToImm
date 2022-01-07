Require Import Classical Peano_dec Setoid PeanoNat.
From hahn Require Import Hahn.
Require Import Omega.

From imm Require Import Events Execution imm_s.
From imm Require Import AuxRel2.
From imm Require Import TraversalConfig.
From imm Require Import Traversal.
From imm Require Import FinExecution. 
Require Import ExtTraversalConfig.
Require Import ExtTraversal.
Require Import ExtSimTraversal.
Require Import ExtSimTraversalProperties.
(* Require Import FinExecutionExt.  *)

Require Import IndefiniteDescription.
Require Import SetSize.

Set Implicit Arguments.
Remove Hints plus_n_O.

Definition countP (f: actid -> Prop) l :=
  length (filterP f l).

Add Parametric Morphism : countP with signature
    set_subset ==> eq ==> le as countP_mori.
Proof using.
  ins. unfold countP.
  induction y0.
  { simpls. }
  ins. desf; simpls.
  1,3: omega.
  exfalso. apply n. by apply H.
Qed.

Add Parametric Morphism : countP with signature
    set_equiv ==> eq ==> eq as countP_more.
Proof using.
  ins. unfold countP.
  erewrite filterP_set_equiv; eauto.
Qed.

Lemma countP_strict_mori e l P P'
      (IN : P ⊆₁ P')
      (INP  : ~ P e)
      (INP' :  P' e)
      (INL  : In e l) :
  countP P l < countP P' l.
Proof using.
  generalize dependent e.
  induction l; simpls.
  ins. desf.
  { unfold countP; simpls. desf. simpls.
    apply le_lt_n_Sm. by apply countP_mori. }
  unfold countP; simpls. desf; simpls.
  { apply lt_n_S. eapply IHl; eauto. }
  { exfalso. apply n. by apply IN. }
  { apply le_lt_n_Sm. by apply countP_mori. }
    by apply IHl with (e:=e).
Qed.

Section ExtTraversalCounting.
  Variable G : execution.
  Variable sc : relation actid.
  Variable WF : Wf G.
  
  Notation "'E'" := (acts_set G).
  Notation "'lab'" := (lab G).
  Notation "'W'" := (fun x => is_true (is_w lab x)).
  Notation "'Rel'" := (fun x => is_true (is_rel lab x)).
  Notation "'rmw'" := (rmw G).


  (* TODO: get rid while generalizing to infinite case *)
  (***********)
  Hypothesis FINDOM: fin_exec_full G. 
  Definition acts_list: list actid :=
    filterP (acts_set G)
            (proj1_sig (@constructive_indefinite_description _ _ FINDOM)).
  Lemma acts_set_findom: acts_set G ≡₁ (fun e => In e acts_list).
  Proof.
    unfold acts_list. destruct constructive_indefinite_description. simpl.
    apply AuxRel.set_equiv_exp_equiv. intros e.
    rewrite in_filterP_iff. intuition. 
  Qed.
  Opaque acts_list.
  (***********)

  Definition trav_steps_left (T : ext_trav_config) :=
    countP (set_compl (ecovered T)) acts_list +
    countP (W ∩₁ set_compl (eissued T)) acts_list +
    countP (W ∩₁ set_compl (reserved T)) acts_list.
  
  Lemma trav_steps_left_step_decrease (T T' : ext_trav_config)
        (STEP : ext_trav_step G sc T T') :
    trav_steps_left T > trav_steps_left T'.
  Proof using WF.
    assert (etc_coherent G sc T') as ETCCOH'.
    { red in STEP. desf. apply STEP. }
    assert (tc_coherent G sc (etc_TC T')) as TCCOH'.
    { apply ETCCOH'. }
    assert (forall e,
               countP (W ∩₁ set_compl (reserved T)) acts_list >=
               countP (W ∩₁ set_compl (reserved T ∪₁ eq e)) acts_list) as AA.
    { intros e. red. apply countP_mori; auto.
      basic_solver. }
    red in STEP. desc. red in STEP.
    desf.
    { clear AA.
      unfold trav_steps_left.
      rewrite ISSEQ, RESEQ.
      assert (countP (set_compl (ecovered T)) acts_list >
              countP (set_compl (ecovered T')) acts_list) as HH.
      2: omega.
      eapply countP_strict_mori with (e:=e); auto.
      { rewrite COVEQ. basic_solver. }
      { unfold set_compl. intros HH. apply HH. apply COVEQ. basic_solver. }
      apply acts_set_findom. 
      apply (coveredE TCCOH'). apply COVEQ. basic_solver. }
    { unfold trav_steps_left.
      rewrite COVEQ.
      assert (reserved T' e) as RESE.
      { apply RESEQ. basic_solver. }
      assert (W e) as WE by (by apply (reservedW WF ETCCOH')).
      assert (countP (W ∩₁ set_compl (reserved T )) acts_list >=
              countP (W ∩₁ set_compl (reserved T')) acts_list).
      { apply countP_mori; auto. rewrite RESEQ. basic_solver 10. }
      assert (countP (W ∩₁ set_compl (eissued T )) acts_list >
              countP (W ∩₁ set_compl (eissued T')) acts_list).
      2: omega.
      apply countP_strict_mori with (e:=e).
      { rewrite ISSEQ. basic_solver. }
      { intros BB. apply BB. apply ISSEQ. basic_solver. }
      { by split. }
      apply acts_set_findom. by apply (etc_S_in_E ETCCOH'). }
    unfold trav_steps_left.
    rewrite COVEQ, ISSEQ.
    assert (countP (W ∩₁ set_compl (reserved T )) acts_list >
            countP (W ∩₁ set_compl (reserved T')) acts_list).
    2: omega.
    assert (reserved T' e) as RESE.
    { apply RESEQ. basic_solver. }
    assert (W e) as WE by (by apply (reservedW WF ETCCOH')).
    apply countP_strict_mori with (e:=e).
    { rewrite RESEQ. basic_solver. }
    { intros BB. apply BB. apply RESEQ. basic_solver. }
    { by split. }
    apply acts_set_findom. by apply (etc_S_in_E ETCCOH').
  Qed.

  Lemma trav_steps_left_steps_decrease (T T' : ext_trav_config)
        (STEPS : (ext_trav_step G sc)⁺ T T') :
    trav_steps_left T > trav_steps_left T'.
  Proof using WF.
    induction STEPS.
    2: by intuition.
      by apply trav_steps_left_step_decrease.
  Qed.

  Lemma trav_steps_left_decrease_sim (T T' : ext_trav_config)
        (STEP : ext_sim_trav_step G sc T T') :
    trav_steps_left T > trav_steps_left T'.
  Proof using WF.
    apply trav_steps_left_steps_decrease. by apply ext_sim_trav_step_in_trav_steps.
  Qed.
  
  Lemma trav_steps_left_null_cov (T : ext_trav_config)
        (NULL : trav_steps_left T = 0) :
    E ⊆₁ ecovered T.
  Proof using.
    unfold trav_steps_left in *.
    assert (countP (set_compl (ecovered T)) acts_list = 0) as HH by omega.
    clear NULL.
    unfold countP in *.
    apply length_zero_iff_nil in HH.
    intros x EX.
    destruct (classic (ecovered T x)) as [|NN]; auto.
    exfalso. 
    assert (In x (filterP (set_compl (ecovered T)) acts_list)) as UU.
    2: { rewrite HH in UU. inv UU. }
    apply in_filterP_iff. split; [by apply acts_set_findom| done].
  Qed.

  Lemma trav_steps_left_ncov_nnull (T : ext_trav_config) e
        (EE : E e) (NCOV : ~ ecovered T e):
    trav_steps_left T <> 0.
  Proof using.
    destruct (classic (trav_steps_left T = 0)) as [EQ|NEQ]; auto.
    exfalso. apply NCOV. apply trav_steps_left_null_cov; auto.
  Qed.

  Lemma trav_steps_left_nnull_ncov (T : ext_trav_config) (ETCCOH : etc_coherent G sc T)
        (NNULL : trav_steps_left T > 0):
    exists e, E e /\ ~ ecovered T e.
  Proof using.
    assert (tc_coherent G sc (etc_TC T)) as TCCOH by apply ETCCOH.

    assert (countP (set_compl (ecovered T)) acts_list >=
            countP (W ∩₁ set_compl (eissued T)) acts_list) as AA.
    { apply countP_mori; auto.
      intros x [WX NN] COV.
      apply NN. eapply w_covered_issued; eauto. by split. }

    assert (countP (W ∩₁ set_compl (eissued  T)) acts_list >=
            countP (W ∩₁ set_compl (reserved T)) acts_list) as BB.
    { apply countP_mori; auto.
      intros x [WX NN].
      split; auto. intros CC. apply NN. by apply (etc_I_in_S ETCCOH). }

    unfold trav_steps_left in *.
    assert (countP (set_compl (ecovered T)) acts_list > 0 \/
            countP (W ∩₁ set_compl (eissued T)) acts_list > 0 \/
            countP (W ∩₁ set_compl (reserved T)) acts_list > 0) as YY by omega.
    assert (countP (set_compl (ecovered T)) acts_list > 0) as HH.
    { destruct YY as [|[]]; auto; omega. }
    clear YY.
    unfold countP in HH.
    assert (exists h l, filterP (set_compl (ecovered T)) acts_list = h :: l) as YY.
    { destruct (filterP (set_compl (ecovered T)) acts_list); eauto.
      inv HH. }
    desc. exists h.
    assert (In h (filterP (set_compl (ecovered T)) acts_list)) as GG.
    { rewrite YY. red. by left. }
    apply in_filterP_iff in GG. generalize acts_set_findom. basic_solver. 
  Qed.

  Lemma trav_steps_left_decrease_sim_trans (T T' : ext_trav_config)
        (STEPS : (ext_sim_trav_step G sc)⁺ T T') :
    trav_steps_left T > trav_steps_left T'.
  Proof using WF.
    induction STEPS.
    { by apply trav_steps_left_decrease_sim. }
    eapply lt_trans; eauto.
  Qed.

  Lemma sim_traversal_helper T
        (IMMCON : imm_consistent G sc)
        (ETCCOH : etc_coherent G sc T)
        (RELCOV : W ∩₁ Rel ∩₁ eissued T ⊆₁ ecovered T)
        (RMWCOV : forall r w (RMW : rmw r w), ecovered T r <-> ecovered T w) :
    exists T', (ext_sim_trav_step G sc)＊ T T' /\ ((acts_set G) ⊆₁ ecovered T').
  Proof using WF FINDOM.
    assert
      (exists T' : ext_trav_config,
          (ext_sim_trav_step G sc)＊ T T' /\ trav_steps_left T' = 0).
    2: { desc. eexists. splits; eauto. by apply trav_steps_left_null_cov. }
    assert (exists n, n = trav_steps_left T) as [n NN] by eauto.
    generalize dependent T. generalize dependent n.
    set (P n :=
           forall T,
             etc_coherent G sc T ->
             W ∩₁ Rel ∩₁ eissued T ⊆₁ ecovered T ->
             (forall r w, rmw r w -> ecovered T r <-> ecovered T w) ->
             n = trav_steps_left T ->
             exists T', (ext_sim_trav_step G sc)＊ T T' /\ trav_steps_left T' = 0).
    assert (forall n, P n) as YY.
    2: by apply YY.
    apply nat_ind_lt. unfold P. 
    ins.
    destruct (classic (trav_steps_left T = 0)) as [EQ|NEQ].
    { eexists. splits; eauto. apply rt_refl. }
    assert (trav_steps_left T > 0) as HH by omega.
    eapply trav_steps_left_nnull_ncov in HH; auto.
    desc.
    eapply exists_next in HH0; eauto. desc.
    eapply exists_ext_trav_step in HH1; eauto.
    desc.
    apply exists_ext_sim_trav_step in HH1; eauto.
    2: by apply IMMCON.
    desc.
    clear T'. subst.
    specialize (H (trav_steps_left T'')).
    edestruct H as [T' [II OO]].
    { by apply trav_steps_left_decrease_sim. }
    { eapply ext_sim_trav_step_coherence; eauto. }
    { eapply ext_sim_trav_step_rel_covered; eauto. }
    { eapply ext_sim_trav_step_rmw_covered; eauto. }
    { done. }
    exists T'. splits; auto. apply rt_begin.
    right. eexists. eauto.
  Qed.
  
  Lemma sim_traversal (IMMCON : imm_consistent G sc) :
    exists T, (ext_sim_trav_step G sc)＊ (ext_init_trav G) T /\ ((acts_set G) ⊆₁ ecovered T).
  Proof using WF FINDOM.
    apply sim_traversal_helper; auto.
    { by apply ext_init_trav_coherent. }
    { unfold ext_init_trav. simpls. basic_solver. }
    unfold ecovered, eissued.
    ins. split; intros [HH AA].
    { apply (init_w WF) in HH.
      apply (dom_l (wf_rmwD WF)) in RMW. apply seq_eqv_l in RMW.
      type_solver. }
    apply (rmw_in_sb WF) in RMW. apply no_sb_to_init in RMW.
    apply seq_eqv_r in RMW. desf.
  Qed.

  Notation "'NTid_' t" := (fun x => tid x <> t) (at level 1).
  Notation "'Tid_' t"  := (fun x => tid x =  t) (at level 1).

  Lemma sim_step_cov_full_thread T T' thread thread'
        (ETCCOH : etc_coherent G sc T)
        (TS : ext_isim_trav_step G sc thread' T T')
        (NCOV : NTid_ thread ∩₁ (acts_set G) ⊆₁ ecovered T) :
    thread' = thread.
  Proof using WF.
    assert (tc_coherent G sc (etc_TC T)) as TCCOH by apply ETCCOH.
    destruct (classic (thread' = thread)) as [|NEQ]; [by subst|].
    exfalso.
    apply ext_sim_trav_step_to_step in TS; auto. desf.
    assert (ecovered T e) as AA.
    { apply NCOV. split; eauto.
      eapply ext_itrav_stepE; eauto. }
    eapply ext_itrav_step_nC; eauto.
  Qed.

  Lemma sim_step_cov_full_traversal T thread
        (IMMCON : imm_consistent G sc)
        (TCCOH : etc_coherent G sc T)
        (NCOV : NTid_ thread ∩₁ (acts_set G) ⊆₁ ecovered T)
        (RELCOV : W ∩₁ Rel ∩₁ eissued T ⊆₁ ecovered T)
        (RMWCOV : forall r w : actid, rmw r w -> ecovered T r <-> ecovered T w) : 
    exists T', (ext_isim_trav_step G sc thread)＊ T T' /\ ((acts_set G) ⊆₁ ecovered T').
  Proof using WF FINDOM.
    edestruct sim_traversal_helper as [T']; eauto.
    desc. exists T'. splits; auto.
    clear H0.
    induction H.
    2: ins; apply rt_refl.
    { ins. apply rt_step. destruct H as [thread' H].
      assert (thread' = thread); [|by subst].
      eapply sim_step_cov_full_thread; eauto. }
    ins. 
    set (NCOV' := NCOV).
    apply IHclos_refl_trans1 in NCOV'; auto.
    eapply rt_trans; eauto.
    eapply IHclos_refl_trans2.
    { eapply ext_sim_trav_step_rt_coherence; eauto. }
    { etransitivity; eauto.
      eapply ext_sim_trav_steps_covered_le; eauto. }
    { eapply ext_sim_trav_steps_rel_covered; eauto. }
    eapply ext_sim_trav_steps_rmw_covered; eauto.
  Qed.
  
End ExtTraversalCounting.
