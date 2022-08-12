Require Import Classical Peano_dec Setoid PeanoNat.
From hahn Require Import Hahn.
Require Import Lia.

From imm Require Import Events Execution imm_s.
From imm Require Import AuxRel2.
From imm Require Import TLSCoherency.
From imm Require Import IordCoherency.
From imm Require Import TraversalOrder. 
Require Import TlsEventSets.
Require Import ExtTraversalConfig.
Require Import ExtTraversal.
Require Import ExtSimTraversal.
Require Import ExtSimTraversalProperties.

Require Import IndefiniteDescription.
Require Import SetSize.
From imm Require Import FinExecution.

Require Import TlsEventSets.

Set Implicit Arguments.

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

  (* TODO: move*)
  From imm Require Import ThreadBoundedExecution.
  Definition threads := map tid acts_list.
  (* Definition b := max threads.  *)
  (* Lemma threads_bound_G: *)
  (*   threads_bound G b.  *)

  (* TODO: move*)
  Global Add Parametric Morphism : propagated_thread with signature
         set_equiv ==> eq ==> set_equiv as propagated_thread_more.
  Proof using. 
    ins. unfold propagated_thread. rewrite H. auto.
  Qed. 

  Definition props_left (TS: thread_id -> actid  -> Prop) :=
    list_sum (map (fun t => countP (TS t) acts_list) threads). 

  Add Parametric Morphism: props_left with signature
      (eq ==> set_equiv) ==> eq as props_left_more.
  Proof using. 
    ins. unfold props_left. f_equal.
    induction threads; [done| ].
    simpl. erewrite countP_more; [| rewrite (H a); reflexivity| reflexivity].
    rewrite IHl. auto.
  Qed. 

  Definition trav_steps_left (T : trav_label -> Prop) :=
    countP (set_compl (covered T)) acts_list +
    countP (W ∩₁ set_compl (issued T)) acts_list +
    countP (W ∩₁ set_compl (reserved T)) acts_list +
    props_left (fun t => W ∩₁ set_compl (propagated_thread T t)).

  (* Add Parametric Morphism: trav_steps_left with signature *)
  (*        set_equiv ==> eq as trav_steps_left_more.  *)
  (* Proof using.  *)
  (*   ins. unfold trav_steps_left. rewrite H. *)
  (*   erewrite props_left_more. *)
  (*   2: { red. ins. pattern x0. rewrite H0, H. reflexivity.   *)
  (*   auto. *)
  (* Qed.  *)

  (* TODO: move*)
  Lemma emiT {A: Type} {P: Prop} (b1 b2: A) (p: P):
    (ifP P then b1 else b2) = b1.
  Proof. by destruct (excluded_middle_informative P). Qed. 
  
  Lemma emiF {A: Type} {P: Prop} (b1 b2: A) (np: ~ P):
    (ifP P then b1 else b2) = b2.
  Proof. by destruct (excluded_middle_informative P). Qed. 
  
  (* TODO: move*)
  Lemma countP_union_disj S1 S2 l
        (DISJ: set_disjoint S1 S2):
    countP S1 l + countP S2 l = countP (S1 ∪₁ S2) l. 
  Proof using. 
    unfold countP.
    induction l.
    { simpl. lia. }
    simpl. destruct (excluded_middle_informative (S1 a)), (excluded_middle_informative (S2 a)); ins.
    { edestruct DISJ; eauto. }
    1, 2: rewrite emiT; [| by vauto]; simpl; lia.
    rewrite emiF.
    2: { unfold set_union. tauto. }
    lia.
  Qed. 

  Lemma In_alt {A: Type} (l: list A):
    0 < length l <-> exists a, In a l. 
  Proof using. 
    destruct l.
    { simpl. split; [lia| ins; desf]. }
    simpl. split; [| lia]. ins. vauto.
  Qed.  

  (* Lemma countP_lt S1 S2 l *)
  (*       (IN: S1 ⊆₁ S2) *)
  (*       (DIFF: exists e, S2 e /\ ~ S1 e /\ In e l): *)
  (*   countP S1 l < countP S2 l.  *)
  (* Proof using.  *)
  (*   rewrite set_split_complete with (s' := S2) (s := S1). *)
  (*   rewrite <- countP_union_disj; [| basic_solver]. *)
  (*   rewrite set_inter_absorb_l; auto. *)
  (*   rewrite plus_n_O at 1. apply Plus.plus_lt_compat_l. *)
  (*   unfold countP. apply In_alt. *)
  (*   desc. exists e. apply in_filterP_iff. splits; vauto.  *)
  (* Qed.   *)
  
  Lemma tls_set_alt_compl T a e:
    ~ (event ↑₁ (T ∩₁ action ↓₁ eq a)) e <-> ~ T (mkTL a e). 
  Proof using.
    apply not_iff_compat, tls_set_alt. 
  Qed.

  (* TODO: move to tlseventsets*)
  Lemma propagated_singleton t e
        (TS: (threads_set G \₁ eq tid_init) t):
    propagated G (eq (mkTL (ta_propagate t) e)) ≡₁ eq e.
  Proof using. 
    unfold propagated. split; try basic_solver. apply set_subset_eq.
    exists (mkTL (ta_propagate t) e). do 2 split; vauto.
  Qed.

  (*TODO: move*)
  From imm Require Import AuxDef. 

  (* TODO: move to tlseventsets *)
  Lemma prop_in_thread_set T t e
        (TCOH: tls_coherent G T)
        (PROP: T (mkTL (ta_propagate t) e)):
    (threads_set G \₁ eq tid_init) t. 
  Proof using.
    destruct TCOH. 
    unfold init_tls, exec_tls in tls_coh_exec. rewrite !set_pair_alt in tls_coh_exec.
    eapply tls_coh_exec in PROP. unfolder in PROP. des; ins; try by vauto.
    all: destruct PROP; desc; congruence. 
  Qed. 

  Lemma trav_steps_left_step_decrease (T T' : trav_label -> Prop)
        (* (ETCCOH : etc_coherent G sc T) *)
        (TCOH: tls_coherent G T)
        (ICOH: iord_coherent G sc T)
        (RCOH: reserve_coherent G T)
        (STEP : ext_trav_step G sc T T') :
    trav_steps_left T > trav_steps_left T'.
  Proof using WF.
    assert (forall e,
               countP (W ∩₁ set_compl (reserved T)) acts_list >=
               countP (W ∩₁ set_compl (reserved T ∪₁ eq e)) acts_list) as AA.
    { intros e. red. apply countP_mori; auto.
      basic_solver. }
    red in STEP. destruct STEP as [[a e] STEP]. 
    assert (~ is_init e) as NINITE.
    { eapply ext_itrav_step_ninit in STEP; eauto. }
    eapply ext_itrav_stepE in STEP as Ee; eauto. ins. 

    inversion STEP. 
    unfold trav_steps_left. 
    rewrite ets_upd.    
    simplify_tls_events. unfold gt. 

    Local Ltac sum_gt_l := apply NPeano.Nat.add_lt_le_mono; [| apply countP_mori; basic_solver 10]. 
    Local Ltac sum_gt_r := apply NPeano.Nat.add_le_lt_mono; [apply countP_mori; basic_solver 10| ]. 
    apply tls_set_alt_compl in ets_new_ta.
    assert (T' (a, e)) as T'ae%tls_set_alt by (apply ets_upd; basic_solver). 
    assert (In e acts_list) as INe by (apply acts_set_findom; split; auto). 
    
    (* TODO: move to TlsEventSets*)
    assert (forall a (NP: forall t, a <> ta_propagate t),
               set_disjoint (eq (a, e)) (action ↓₁ is_ta_propagate_to_G G)) as NP.
    { unfold is_ta_propagate_to_G. unfolder. ins. subst. desc. ins. congruence. }

  (*   destruct a; simplify_tls_events. *)
  (*   (* 1, 2, 4: rewrite propagated_nonpropagated_empty with (S := eq _); [| apply NP; by vauto]; rewrite set_union_empty_r. *) *)
  (*   { sum_gt_l.  *)
  (*     do 3 sum_gt_l. apply countP_strict_mori with (e := e); try basic_solver. } *)
  (*   { do 2 sum_gt_l. sum_gt_r. *)
  (*     eapply countP_strict_mori with (e := e); try basic_solver. *)
  (*     { apply or_not_and. right. apply set_compl_compl. by right. } *)
  (*     split; auto. eapply issuedW; eauto. } *)
  (*   { sum_gt_l. rewrite <- !Nat.add_assoc. do 2 sum_gt_r. *)
  (*     eapply countP_strict_mori with (e := e); try basic_solver. *)
  (*     { apply or_not_and. right. apply set_compl_compl. by right. } *)
  (*     split; auto. eapply reservedW; eauto. } *)
  (*   { rewrite <- !Nat.add_assoc. repeat sum_gt_r. *)
  (*     forward eapply prop_in_thread_set as TS; eauto. *)
  (*     { apply ets_upd. vauto. } *)
  (*     arewrite (propagated G (eq (ta_propagate tid, e)) ≡₁ eq e). *)
  (*     { by apply propagated_singleton. } *)
  (*     eapply countP_strict_mori with (e := e); try basic_solver. *)
  (*     2: { split. *)
  (*          { eapply propagatedW; eauto. red. *)
  (*            exists (mkTL (ta_propagate tid) e). do 2 split; auto. *)
  (*            { apply ets_upd. vauto. } *)
  (*            red. red. exists tid. split; vauto. } *)
  (*          intros PROP. destruct ets_new_ta. *)
  (*          destruct PROP, x.  *)
  (*          exists (mkTL (ta_propagate tid) e). do 2 split; vauto. *)
  (*          apply tls_set_alt.  *)
  (*          red. red. exists tid. split; vauto. } *)
  (*     { apply or_not_and. right. apply set_compl_compl. right. }       *)
  (* Qed. *)
  Admitted.

  (* TODO: move*)
  Lemma ext_trav_step_coh_crt (T T' : trav_label -> Prop)
        (TCOH: tls_coherent G T)
        (ICOH: iord_coherent G sc T)
        (RCOH: reserve_coherent G T)
        (STEPS: (ext_trav_step G sc)^* T T'):
    tls_coherent G T' /\ iord_coherent G sc T' /\ reserve_coherent G T'.
  Proof using. 
    induction STEPS.
    { inv H. inv H0. }
    { auto. }
    apply IHSTEPS2; apply IHSTEPS1; auto.
  Qed.


  Lemma trav_steps_left_steps_decrease (T T' : trav_label -> Prop)
        (* (ETCCOH : etc_coherent G sc T) *)
        (TCOH: tls_coherent G T)
        (ICOH: iord_coherent G sc T)
        (RCOH: reserve_coherent G T)
        (STEPS : (ext_trav_step G sc)⁺ T T') :
    trav_steps_left T > trav_steps_left T'.
  Proof using WF.
    induction STEPS.
    { apply trav_steps_left_step_decrease; auto. }
    red. etransitivity.
    2: now apply IHSTEPS1.
    apply inclusion_t_rt in STEPS1. 
    apply IHSTEPS2.
    all: eapply (@ext_trav_step_coh_crt x y); eauto. 
  Qed.

  Lemma trav_steps_left_decrease_sim T T'
        (TCOH: tls_coherent G T)
        (ICOH: iord_coherent G sc T)
        (RCOH: reserve_coherent G T)
        (STEP : ext_sim_trav_step G sc T T') :
    trav_steps_left T > trav_steps_left T'.
  Proof using WF.
    apply trav_steps_left_steps_decrease; auto. by apply ext_sim_trav_step_in_trav_steps.
  Qed.
  
  Lemma trav_steps_left_null_cov T
        (TCOH: tls_coherent G T)
        (ICOH: iord_coherent G sc T)
        (RCOH: reserve_coherent G T)
        (NULL : trav_steps_left T = 0) :
    E ⊆₁ covered T.
  Proof using.
    unfold trav_steps_left in *.
    assert (countP (set_compl (covered T)) acts_list = 0) as HH by lia.
    clear NULL.
    unfold countP in *.
    apply length_zero_iff_nil in HH.
    intros x EX.
    destruct (classic (covered T x)) as [|NN]; auto.
    exfalso. 
    assert (In x (filterP (set_compl (covered T)) acts_list)) as UU.
    2: { rewrite HH in UU. inv UU. }
    apply in_filterP_iff. split; [|done].
    apply acts_set_findom. split; auto.
    intros BB. apply NN. red. eapply init_covered; eauto.
    split; auto.
  Qed.

  Lemma trav_steps_left_ncov_nnull T e
        (TCOH: tls_coherent G T)
        (ICOH: iord_coherent G sc T)
        (RCOH: reserve_coherent G T)
        (EE : E e) (NCOV : ~ covered T e):
    trav_steps_left T <> 0.
  Proof using.
    destruct (classic (trav_steps_left T = 0)) as [EQ|NEQ]; auto.
    exfalso. apply NCOV. apply trav_steps_left_null_cov; auto.
  Qed.

  Lemma trav_steps_left_nnull_ncov T
        (TCOH: tls_coherent G T)
        (ICOH: iord_coherent G sc T)
        (RCOH: reserve_coherent G T)
        (NNULL : trav_steps_left T > 0):
    exists e, E e /\ ~ covered T e.
  Proof using.

    assert (countP (set_compl (covered T)) acts_list >=
            countP (W ∩₁ set_compl (issued T)) acts_list) as AA.
    { apply countP_mori; auto.
      intros x [WX NN] COV.
      apply NN. eapply w_covered_issued; eauto. by split. }

    assert (countP (W ∩₁ set_compl (issued  T)) acts_list >=
            countP (W ∩₁ set_compl (reserved T)) acts_list) as BB.
    { apply countP_mori; auto.
      intros x [WX NN].
      split; auto. intros CC. apply NN. eapply rcoh_I_in_S; eauto. }

    assert (countP (W ∩₁ set_compl (issued  T)) acts_list >=
            props_left (fun t => W ∩₁ set_compl (propagated_thread T t))) as CC.
    { red. etransitivity.
      2: { eapply countP_mori; [| done].
           apply set_subset_inter; [apply set_subset_refl2| ].
           apply set_subset_compl. apply rcoh_

      PROP
                                         
      apply countP_mori; auto.
      intros x [WX NN].
      split; auto. intros CC. apply NN. eapply rcoh_I_in_S; eauto. }

    unfold trav_steps_left in *.
    assert (countP (set_compl (covered T)) acts_list > 0 \/
            countP (W ∩₁ set_compl (issued T)) acts_list > 0 \/
            countP (W ∩₁ set_compl (reserved T)) acts_list > 0 \/
            props_leaft
            (fun t => W ∩₁ set_compl (propagated_thread T t)) > 0
           ) as YY by lia.
    assert (countP (set_compl (covered T)) acts_list > 0) as HH.
    { destruct YY as [|[]]; auto; try lia. }
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
