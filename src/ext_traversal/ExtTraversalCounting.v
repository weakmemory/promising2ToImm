Require Import Classical Peano_dec Setoid PeanoNat.
From hahn Require Import Hahn.
Require Import Omega.

From imm Require Import Events Execution imm_s.
Require Import TraversalConfig.
Require Import Traversal.
Require Import ExtTraversal.
Require Import ExtSimTraversal.
Require Import ExtSimTraversalProperties.

Set Implicit Arguments.
Remove Hints plus_n_O.

Definition countP (f: actid -> Prop) l :=
  length (filterP f l).

Add Parametric Morphism : countP with signature
    set_subset ==> eq ==> le as countP_mori.
Proof.
  ins. unfold countP.
  induction y0.
  { simpls. }
  ins. desf; simpls.
  1,3: omega.
  exfalso. apply n. by apply H.
Qed.

Add Parametric Morphism : countP with signature
    set_equiv ==> eq ==> eq as countP_more.
Proof.
  ins. unfold countP.
  erewrite filterP_set_equiv; eauto.
Qed.

Section ExtTraversalCounting.
  Variable G : execution.
  Variable sc : relation actid.
  Variable WF : Wf G.
  
  Notation "'E'" := G.(acts_set).
  Notation "'lab'" := G.(lab).
  Notation "'W'" := (fun x => is_true (is_w lab x)).
  Notation "'Rel'" := (fun x => is_true (is_rel lab x)).
  Notation "'rmw'" := G.(rmw).

  Definition trav_steps_left (T : ext_trav_config) :=
    countP (set_compl (ecovered T)) G.(acts) +
    countP (W ∩₁ set_compl (eissued T)) G.(acts) +
    countP (W ∩₁ set_compl (reserved T)) G.(acts).
  
  Lemma trav_steps_left_step_decrease (T T' : ext_trav_config)
        (STEP : ext_trav_step G sc T T') :
    trav_steps_left T > trav_steps_left T'.
  Proof.
    assert (etc_coherent G sc T') as ETCCOH'.
    { red in STEP. desf. apply STEP. }
    assert (tc_coherent G sc (etc_TC T')) as TCCOH'.
    { apply ETCCOH'. }
    assert (forall e,
               countP (W ∩₁ set_compl (reserved T)) (acts G) >=
               countP (W ∩₁ set_compl (reserved T ∪₁ eq e)) (acts G)) as AA.
    { intros e. red. apply countP_mori; auto.
      basic_solver. }

    red in STEP. desc. red in STEP.
    desf.
    { clear AA.
      unfold trav_steps_left.
      rewrite ISSEQ, RESEQ.
      assert (countP (set_compl (ecovered T)) (acts G) >
              countP (set_compl (ecovered T')) (acts G)) as HH.
      2: omega.
      rewrite COVEQ.
      unfold countP.
      assert (List.In e (acts G)) as LL.
      { apply TCCOH'.(coveredE). apply COVEQ. basic_solver. }
      induction (acts G).
      { done. }
      destruct l as [|h l].
      { assert (a = e); subst.
        { inv LL. }
        simpls. desf.
        exfalso. apply s0. by right. }
      destruct LL as [|H]; subst.
      2: { apply IHl in H. clear IHl.
           simpls. desf; simpls; try omega.
           all: try by (exfalso; apply s0; left; apply NNPP).
             by exfalso; apply s; left; apply NNPP. }
      clear IHl.
      assert (exists l', l' = h :: l) as [l' HH] by eauto.
      rewrite <- HH. clear h l HH.
      simpls. desf; simpls.
      { exfalso. apply s0. by right. }
      assert (length (filterP (set_compl (ecovered T ∪₁ eq e)) l') <=
              length (filterP (set_compl (ecovered T)) l')).
      2: omega.
      eapply countP_mori; auto.
      basic_solver. }
    { unfold trav_steps_left.
      rewrite COVEQ, RESEQ.
      assert (countP (W ∩₁ set_compl (eissued T )) (acts G) >
              countP (W ∩₁ set_compl (eissued T')) (acts G)) as HH.
      2: { specialize (AA e). omega. }
      clear AA.
      rewrite ISSEQ.
      unfold countP.
      assert (List.In e (acts G)) as LL.
      { apply TCCOH'.(issuedE). apply ISSEQ. basic_solver. }
      assert (W e) as WE.
      { apply TCCOH'.(issuedW). apply ISSEQ. basic_solver. }
      induction (acts G).
      { done. }
      destruct l as [|h l].
      { assert (a = e); subst.
        { inv LL. }
        simpls. desf.
        { exfalso. apply s0. by right. }
        all: by exfalso; apply n; split. }
      destruct LL as [|H]; subst.
      2: { apply IHl in H. clear IHl.
           simpls. desf; simpls; try omega.
           1-2: by exfalso; apply n; destruct s0 as [H1 H2];
             split; auto; intros HH; apply H2; left.
           all: by exfalso; apply n; destruct s as [H1 H2];
             split; auto; intros HH; apply H2; left. }
      clear IHl.
      assert (exists l', l' = h :: l) as [l' HH] by eauto.
      rewrite <- HH. clear h l HH.
      simpls. desf; simpls.
      { exfalso. apply s0. by right. }
      2: { exfalso. apply s. by right. }
      2: { exfalso. apply n. by split. }
      assert (length (filterP (W ∩₁ set_compl (eissued T ∪₁ eq e)) l') <=
              length (filterP (W ∩₁ set_compl (eissued T)) l')).
      2: omega.
      eapply countP_mori; auto.
      basic_solver. }
    clear AA.
    unfold trav_steps_left.
    rewrite COVEQ, ISSEQ.
    assert (countP (W ∩₁ set_compl (reserved T )) (acts G) >
            countP (W ∩₁ set_compl (reserved T')) (acts G)) as HH.
    2: omega.
    rewrite RESEQ.
    unfold countP.
    assert (List.In e (acts G)) as LL.
    { apply ETCCOH'.(etc_S_in_E). apply RESEQ. basic_solver. }
    assert (W e) as WE.
    { apply (reservedW WF ETCCOH'). apply RESEQ. basic_solver. }
    induction (acts G).
    { done. }
    destruct l as [|h l].
    { assert (a = e); subst.
      { inv LL. }
      simpls. desf.
      { exfalso. apply s0. by right. }
      all: by exfalso; apply n; split. }
    destruct LL as [|H]; subst.
    2: { apply IHl in H. clear IHl.
         simpls. desf; simpls; try omega.
         1-2: by exfalso; apply n; destruct s0 as [H1 H2];
           split; auto; intros HH; apply H2; left.
         all: by exfalso; apply n; destruct s as [H1 H2];
           split; auto; intros HH; apply H2; left. }
    clear IHl.
    assert (exists l', l' = h :: l) as [l' HH] by eauto.
    rewrite <- HH. clear h l HH.
    simpls. desf; simpls.
    { exfalso. apply s0. by right. }
    2: { exfalso. apply s. by right. }
    2: { exfalso. apply n. by split. }
    assert (length (filterP (W ∩₁ set_compl (reserved T ∪₁ eq e)) l') <=
            length (filterP (W ∩₁ set_compl (reserved T)) l')).
    2: omega.
    eapply countP_mori; auto.
    basic_solver.
  Qed.

  Lemma trav_steps_left_steps_decrease (T T' : ext_trav_config)
        (STEPS : (ext_trav_step G sc)⁺ T T') :
    trav_steps_left T > trav_steps_left T'.
  Proof.
    induction STEPS.
    2: by intuition.
      by apply trav_steps_left_step_decrease.
  Qed.

  Lemma trav_steps_left_decrease_sim (T T' : ext_trav_config)
        (STEP : ext_sim_trav_step G sc T T') :
    trav_steps_left T > trav_steps_left T'.
  Proof.
    apply trav_steps_left_steps_decrease. by apply ext_sim_trav_step_in_trav_steps.
  Qed.
  
  Lemma trav_steps_left_null_cov (T : ext_trav_config)
        (NULL : trav_steps_left T = 0) :
    E ⊆₁ ecovered T.
  Proof.
    unfold trav_steps_left in *.
    assert (countP (set_compl (ecovered T)) (acts G) = 0) as HH by omega.
    clear NULL.
    unfold countP in *.
    apply length_zero_iff_nil in HH.
    intros x EX.
    destruct (classic (ecovered T x)) as [|NN]; auto.
    exfalso. 
    assert (In x (filterP (set_compl (ecovered T)) (acts G))) as UU.
    2: { rewrite HH in UU. inv UU. }
    apply in_filterP_iff. by split.
  Qed.

  Lemma trav_steps_left_ncov_nnull (T : ext_trav_config) e
        (EE : E e) (NCOV : ~ ecovered T e):
    trav_steps_left T <> 0.
  Proof.
    destruct (classic (trav_steps_left T = 0)) as [EQ|NEQ]; auto.
    exfalso. apply NCOV. apply trav_steps_left_null_cov; auto.
  Qed.

  Lemma trav_steps_left_nnull_ncov (T : ext_trav_config) (ETCCOH : etc_coherent G sc T)
        (NNULL : trav_steps_left T > 0):
    exists e, E e /\ ~ ecovered T e.
  Proof.
    assert (tc_coherent G sc (etc_TC T)) as TCCOH by apply ETCCOH.

    assert (countP (set_compl (ecovered T)) (acts G) >=
            countP (W ∩₁ set_compl (eissued T)) (acts G)) as AA.
    { apply countP_mori; auto.
      intros x [WX NN] COV.
      apply NN. eapply w_covered_issued; eauto. by split. }

    assert (countP (W ∩₁ set_compl (eissued  T)) (acts G) >=
            countP (W ∩₁ set_compl (reserved T)) (acts G)) as BB.
    { apply countP_mori; auto.
      intros x [WX NN].
      split; auto. intros CC. apply NN. by apply ETCCOH.(etc_I_in_S). }

    unfold trav_steps_left in *.
    assert (countP (set_compl (ecovered T)) (acts G) > 0 \/
            countP (W ∩₁ set_compl (eissued T)) (acts G) > 0 \/
            countP (W ∩₁ set_compl (reserved T)) (acts G) > 0) as YY by omega.
    assert (countP (set_compl (ecovered T)) (acts G) > 0) as HH.
    { destruct YY as [|[]]; auto; omega. }
    clear YY.
    unfold countP in HH.
    assert (exists h l, filterP (set_compl (ecovered T)) (acts G) = h :: l) as YY.
    { destruct (filterP (set_compl (ecovered T)) (acts G)); eauto.
      inv HH. }
    desc. exists h.
    assert (In h (filterP (set_compl (ecovered T)) (acts G))) as GG.
    { rewrite YY. red. by left. }
    apply in_filterP_iff in GG. simpls.
  Qed.

  Lemma trav_steps_left_decrease_sim_trans (T T' : ext_trav_config)
        (STEPS : (ext_sim_trav_step G sc)⁺ T T') :
    trav_steps_left T > trav_steps_left T'.
  Proof.
    induction STEPS.
    { by apply trav_steps_left_decrease_sim. }
    eapply lt_trans; eauto.
  Qed.

  Theorem nat_ind_lt (P : nat -> Prop)
          (HPi : forall n, (forall m, m < n -> P m) -> P n) :
    forall n, P n.
  Proof.
    set (Q n := forall m, m <= n -> P m).
    assert (forall n, Q n) as HH.
    2: { ins. apply (HH n). omega. }
    ins. induction n.
    { unfold Q. ins. inv H. apply HPi. ins. inv H0. }
    unfold Q in *. ins.
    apply le_lt_eq_dec in H.
    destruct H as [Hl | Heq].
    { unfold lt in Hl. apply le_S_n in Hl. by apply IHn. }
    rewrite Heq. apply HPi. ins.
    apply le_S_n in H. by apply IHn.
  Qed.

  Lemma sim_traversal_helper T
        (IMMCON : imm_consistent G sc)
        (ETCCOH : etc_coherent G sc T)
        (RELCOV : W ∩₁ Rel ∩₁ eissued T ⊆₁ ecovered T)
        (RMWCOV : forall r w (RMW : rmw r w), ecovered T r <-> ecovered T w) :
    exists T', (ext_sim_trav_step G sc)＊ T T' /\ (G.(acts_set) ⊆₁ ecovered T').
  Proof.
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
    2: by apply IMMCON.
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
  
  (* TODO: move to ExtTraversal.v *)
  Definition ext_init_trav := mkETC (mkTC (is_init ∩₁ E) (is_init ∩₁ E)) (is_init ∩₁ E).

  (* TODO: move to ExtTraversal.v *)
  Lemma ext_init_trav_coherent (IMMCON : imm_consistent G sc) :
    etc_coherent G sc ext_init_trav.
  Proof.
    unfold ext_init_trav.
    constructor; unfold eissued, ecovered; simpls.
    { by apply init_trav_coherent. }
    { basic_solver. }
    6: rewrite WF.(rppo_in_sb).
    2-6: rewrite no_sb_to_init; basic_solver.
    intros x [AA BB]. intuition.
  Qed.

  Lemma sim_traversal (IMMCON : imm_consistent G sc) :
    exists T, (ext_sim_trav_step G sc)＊ ext_init_trav T /\ (G.(acts_set) ⊆₁ ecovered T).
  Proof.
    apply sim_traversal_helper; auto.
    { by apply ext_init_trav_coherent. }
    { unfold ext_init_trav. simpls. basic_solver. }
    unfold ecovered, eissued.
    ins. split; intros [HH AA].
    { apply WF.(init_w) in HH.
      apply (dom_l WF.(wf_rmwD)) in RMW. apply seq_eqv_l in RMW.
      type_solver. }
    apply WF.(rmw_in_sb) in RMW. apply no_sb_to_init in RMW.
    apply seq_eqv_r in RMW. desf.
  Qed.

  Notation "'NTid_' t" := (fun x => tid x <> t) (at level 1).
  Notation "'Tid_' t"  := (fun x => tid x =  t) (at level 1).

  (* TODO: move to more appropriate place. *)
  Lemma ext_itrav_stepE e T T' (STEP : ext_itrav_step G sc e T T') : E e.
  Proof.
    red in STEP. desf.
    { eapply coveredE.
      2: apply COVEQ; basic_solver.
      apply ETCCOH'. }
    { eapply issuedE.
      { apply ETCCOH'. }
      apply ISSEQ. basic_solver. }
    eapply ETCCOH'.(etc_S_in_E).
    apply RESEQ. basic_solver.
  Qed.

  (* TODO: move to more appropriate place. *)
  Lemma ext_itrav_step_nC e T T'
        (ETCCOH : etc_coherent G sc T)
        (STEP : ext_itrav_step G sc e T T') : ~ ecovered T e.
  Proof.
    assert (tc_coherent G sc (etc_TC T)) as TCCOH by apply ETCCOH.
    intros AA.
    red in STEP. desf.
    { assert (issued (etc_TC T') e) as BB.
      { apply ISSEQ. basic_solver. }
      apply NISS. eapply w_covered_issued; eauto.
      split; auto.
      eapply issuedW; [|by eauto].
      apply ETCCOH'. }
    apply NISS. apply ETCCOH.(etc_I_in_S).
    eapply w_covered_issued; eauto.
    split; auto.
    eapply WF.(reservedW).
    { apply ETCCOH'. }
    apply RESEQ. basic_solver.
  Qed.

  (* TODO: move to more appropriate place. *)
  Lemma ext_itrav_step_ninit e T T'
        (ETCCOH : etc_coherent G sc T)
        (STEP : ext_itrav_step G sc e T T') : ~ is_init e.
  Proof.
    assert (tc_coherent G sc (etc_TC T)) as TCCOH by apply ETCCOH.
    intros II. eapply ext_itrav_step_nC; eauto.
    eapply init_covered; eauto.
    split; auto.
    eapply ext_itrav_stepE; eauto.
  Qed.

  Lemma sim_step_cov_full_thread T T' thread thread'
        (ETCCOH : etc_coherent G sc T)
        (TS : ext_isim_trav_step G sc thread' T T')
        (NCOV : NTid_ thread ∩₁ G.(acts_set) ⊆₁ ecovered T) :
    thread' = thread.
  Proof.
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
        (NCOV : NTid_ thread ∩₁ G.(acts_set) ⊆₁ ecovered T)
        (RELCOV : W ∩₁ Rel ∩₁ eissued T ⊆₁ ecovered T)
        (RMWCOV : forall r w : actid, rmw r w -> ecovered T r <-> ecovered T w) : 
    exists T', (ext_isim_trav_step G sc thread)＊ T T' /\ (G.(acts_set) ⊆₁ ecovered T').
  Proof.
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