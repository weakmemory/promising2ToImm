Require Import Classical Peano_dec Setoid PeanoNat.
From hahn Require Import Hahn.
Require Import Lia.

From imm Require Import Events Execution imm_s.
From imm Require Import AuxRel2.
From imm Require Import TraversalConfig.
From imm Require Import Traversal.
From imm Require Import FinExecution. 
Require Import ExtTraversalConfig.
Require Import ExtTraversal.
Require Import ExtSimTraversal.
Require Import ExtSimTraversalProperties.

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
  1,3: lia.
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
    apply Lt.le_lt_n_Sm. by apply countP_mori. }
  unfold countP; simpls. desf; simpls.
  { apply Lt.lt_n_S. eapply IHl; eauto. }
  { exfalso. apply n. by apply IN. }
  { apply Lt.le_lt_n_Sm. by apply countP_mori. }
    by apply IHl with (e:=e).
Qed.

Section ExtTraversalCounting.
  Variable G : execution.
  Variable sc : relation actid.
  Variable WF : Wf G.
  Variable WFSC : wf_sc G sc.
  
  Hypothesis COMP: complete G. 
                    
  Notation "'E'" := (acts_set G).
  Notation "'lab'" := (lab G).
  Notation "'W'" := (fun x => is_true (is_w lab x)).
  Notation "'Rel'" := (fun x => is_true (is_rel lab x)).
  Notation "'rmw'" := (rmw G).


  Hypothesis FINDOM: fin_exec G. 
  Definition acts_list: list actid :=
    filterP (acts_set G \₁ is_init)
            (proj1_sig (@constructive_indefinite_description _ _ FINDOM)).
  Lemma acts_set_findom: acts_set G \₁ is_init ≡₁ (fun e => In e acts_list).
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
        (ETCCOH : etc_coherent G sc T)
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
    red in STEP. desc.
    assert (~ is_init e) as NINITE.
    { eapply ext_itrav_step_ninit with (T:=T); eauto. }
    red in STEP.
    desf.
    { clear AA.
      unfold trav_steps_left.
      rewrite ISSEQ, RESEQ.
      assert (countP (set_compl (ecovered T)) acts_list >
              countP (set_compl (ecovered T')) acts_list) as HH.
      2: lia.
      eapply countP_strict_mori with (e:=e); auto.
      { rewrite COVEQ. basic_solver. }
      { unfold set_compl. intros HH. apply HH. apply COVEQ. basic_solver. }
      apply acts_set_findom. 
      split; auto.
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
      2: lia.
      apply countP_strict_mori with (e:=e).
      { rewrite ISSEQ. basic_solver. }
      { intros BB. apply BB. apply ISSEQ. basic_solver. }
      { by split. }
      apply acts_set_findom. split; auto.
      now apply (etc_S_in_E ETCCOH'). }
    unfold trav_steps_left.
    rewrite COVEQ, ISSEQ.
    assert (countP (W ∩₁ set_compl (reserved T )) acts_list >
            countP (W ∩₁ set_compl (reserved T')) acts_list).
    2: lia.
    assert (reserved T' e) as RESE.
    { apply RESEQ. basic_solver. }
    assert (W e) as WE by (by apply (reservedW WF ETCCOH')).
    apply countP_strict_mori with (e:=e).
    { rewrite RESEQ. basic_solver. }
    { intros BB. apply BB. apply RESEQ. basic_solver. }
    { by split. }
    apply acts_set_findom. split; auto.
    now apply (etc_S_in_E ETCCOH').
  Qed.

  Lemma trav_steps_left_steps_decrease (T T' : ext_trav_config)
        (ETCCOH : etc_coherent G sc T)
        (STEPS : (ext_trav_step G sc)⁺ T T') :
    trav_steps_left T > trav_steps_left T'.
  Proof using WF.
    induction STEPS.
    { apply trav_steps_left_step_decrease; auto. }
    red. etransitivity.
    2: now apply IHSTEPS1.
    apply IHSTEPS2. apply clos_trans_tn1 in STEPS1.
    inv STEPS1.
    all: red in H; desf; apply H.
  Qed.

  Lemma trav_steps_left_decrease_sim (T T' : ext_trav_config)
        (ETCCOH : etc_coherent G sc T)
        (STEP : ext_sim_trav_step G sc T T') :
    trav_steps_left T > trav_steps_left T'.
  Proof using WF.
    apply trav_steps_left_steps_decrease; auto. by apply ext_sim_trav_step_in_trav_steps.
  Qed.
  
  Lemma trav_steps_left_null_cov (T : ext_trav_config)
        (ETCCOH : etc_coherent G sc T)
        (NULL : trav_steps_left T = 0) :
    E ⊆₁ ecovered T.
  Proof using.
    unfold trav_steps_left in *.
    assert (countP (set_compl (ecovered T)) acts_list = 0) as HH by lia.
    clear NULL.
    unfold countP in *.
    apply length_zero_iff_nil in HH.
    intros x EX.
    destruct (classic (ecovered T x)) as [|NN]; auto.
    exfalso. 
    assert (In x (filterP (set_compl (ecovered T)) acts_list)) as UU.
    2: { rewrite HH in UU. inv UU. }
    apply in_filterP_iff. split; [|done].
    apply acts_set_findom. split; auto.
    intros BB. apply NN. red. eapply init_covered.
    { apply ETCCOH. }
    split; auto.
  Qed.

  Lemma trav_steps_left_ncov_nnull (T : ext_trav_config) e
        (ETCCOH : etc_coherent G sc T)
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
            countP (W ∩₁ set_compl (reserved T)) acts_list > 0) as YY by lia.
    assert (countP (set_compl (ecovered T)) acts_list > 0) as HH.
    { destruct YY as [|[]]; auto; lia. }
    clear YY.
    unfold countP in HH.
    assert (exists h l, filterP (set_compl (ecovered T)) acts_list = h :: l) as YY.
    { destruct (filterP (set_compl (ecovered T)) acts_list); eauto.
      inv HH. }
    desc. exists h.
    assert (In h (filterP (set_compl (ecovered T)) acts_list)) as GG.
    { rewrite YY. red. by left. }
    apply in_filterP_iff in GG. desf.
    split; auto.
    apply acts_set_findom in GG. apply GG.
  Qed.

  Lemma trav_steps_left_decrease_sim_trans (T T' : ext_trav_config)
        (ETCCOH : etc_coherent G sc T)
        (STEPS : (ext_sim_trav_step G sc)⁺ T T') :
    trav_steps_left T > trav_steps_left T'.
  Proof using WF.
    induction STEPS.
    { now apply trav_steps_left_decrease_sim. }
    eapply Lt.lt_trans with (m:=trav_steps_left y); try intuition.
    apply IHSTEPS2.
    eapply ext_sim_trav_step_ct_coherence; eauto.
  Qed.

  Lemma sim_traversal_helper T
        (IMMCON : imm_consistent G sc)
        (ETCCOH : etc_coherent G sc T)
        (RELCOV : W ∩₁ Rel ∩₁ eissued T ⊆₁ ecovered T)
        (RMWCOV : forall r w (RMW : rmw r w), ecovered T r <-> ecovered T w) :
    exists T', (ext_sim_trav_step G sc)＊ T T' /\ ((acts_set G) ⊆₁ ecovered T').
  Proof using WF WFSC FINDOM COMP.
    assert
      (exists T' : ext_trav_config,
          (ext_sim_trav_step G sc)＊ T T' /\ trav_steps_left T' = 0).
    2: { desc. eexists. splits; eauto. apply trav_steps_left_null_cov; auto.
         eapply ext_sim_trav_step_rt_coherence; eauto. }
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
    assert (trav_steps_left T > 0) as HH by lia.
    eapply trav_steps_left_nnull_ncov in HH; auto.
    desc.
    eapply exists_next in HH0; eauto. desc.
    eapply exists_ext_trav_step in HH1; eauto.
    desc.
    apply exists_ext_sim_trav_step in HH1; eauto.
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
  Proof using WF WFSC FINDOM COMP.
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

  Lemma sim_traversal_trace_helper T
        (IMMCON : imm_consistent G sc)
        (ETCCOH : etc_coherent G sc T)
        (RELCOV : W ∩₁ Rel ∩₁ eissued T ⊆₁ ecovered T)
        (RMWCOV : forall r w (RMW : rmw r w), ecovered T r <-> ecovered T w) :
    exists (lst : nat) (TCtr : nat -> ext_trav_config),
      << TCINIT : TCtr 0 = T >> /\
      << TCSTEP : forall n (LT : n < lst),
          ext_sim_trav_step G sc (TCtr n) (TCtr (1 + n)) >> /\
      << TCLAST : acts_set G ⊆₁ ecovered (TCtr lst) >>.
  Proof using WF WFSC FINDOM COMP.
    assert (exists lst TCtr,
               << TCINIT : TCtr 0 = T >> /\
               << TCSTEP : forall n (LT : n < lst),
                   ext_sim_trav_step G sc (TCtr n) (TCtr (1 + n)) >> /\
               << TCLAST : trav_steps_left (TCtr lst) = 0 >>).
    2: { desc. exists lst, TCtr. splits; auto.
         apply trav_steps_left_null_cov; auto.
         destruct lst.
         { now rewrite TCINIT. }
         eapply ext_sim_trav_step_coherence.
         apply TCSTEP. lia. }
    assert (exists n, n = trav_steps_left T) as [n NN] by eauto.
    generalize dependent T.
    pattern n. apply nat_ind_lt. clear n.
    intros n QQ; ins.
    destruct (classic (trav_steps_left T = 0)) as [EQ|NEQ].
    { exists 0, (fun _ => T). splits; eauto. lia. }
    assert (trav_steps_left T > 0) as HH by lia.
    eapply trav_steps_left_nnull_ncov in HH; auto.
    desc.
    eapply exists_next in HH0; eauto. desc.
    eapply exists_ext_trav_step in HH1; eauto.
    desc.
    apply exists_ext_sim_trav_step in HH1; eauto.
    (* 2: by apply IMMCON. *)
    desc.
    clear T'. subst.
    specialize (QQ (trav_steps_left T'')).
    edestruct QQ as [lst' [TCtr' OO]]; desc.
    { by apply trav_steps_left_decrease_sim. }
    { eapply ext_sim_trav_step_coherence; eauto. }
    { eapply ext_sim_trav_step_rel_covered; eauto. }
    { eapply ext_sim_trav_step_rmw_covered; eauto. }
    { done. }
    exists (1 + lst').
    exists (fun n =>
              match n with
              | 0 => T
              | S n' => TCtr' n'
              end).
    splits; auto.
    ins. desf. apply TCSTEP. lia.
  Qed.
  
  Lemma sim_traversal_trace (IMMCON : imm_consistent G sc) :
    exists (lst : nat) (TCtr : nat -> ext_trav_config),
      << TCINIT : TCtr 0 = ext_init_trav G >> /\
      << TCSTEP : forall n (LT : n < lst),
          ext_sim_trav_step G sc (TCtr n) (TCtr (1 + n)) >> /\
      << TCLAST : acts_set G ⊆₁ ecovered (TCtr lst) >>.
  Proof using WF WFSC FINDOM COMP.
    apply sim_traversal_trace_helper; auto.
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
  Proof using WF WFSC FINDOM COMP.
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
