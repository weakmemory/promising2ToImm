Require Import Classical Peano_dec Setoid PeanoNat.
From hahn Require Import Hahn.
Require Import Lia.

From imm Require Import Events Execution imm_s.
From imm Require Import AuxRel2.
From imm Require Import TraversalConfig.
From imm Require Import Traversal.
From imm Require Import FinExecution. 
From imm Require Import FairExecution. 
Require Import ExtTraversalConfig.
Require Import ExtTraversal.
Require Import ExtSimTraversal.
Require Import ExtSimTraversalProperties.
Require Import SetSize.

Require Import IndefiniteDescription.
Require Import Coq.Program.Basics.
Require Import Coq.Logic.ClassicalChoice.

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


  (* (* TODO: get rid while generalizing to infinite case *) *)
  (* (***********) *)
  (* Hypothesis FINDOM: fin_exec_full G.  *)
  (* Definition acts_list: list actid := *)
  (*   filterP (acts_set G) *)
  (*           (proj1_sig (@constructive_indefinite_description _ _ FINDOM)). *)
  (* Lemma acts_set_findom: acts_set G ≡₁ (fun e => In e acts_list). *)
  (* Proof. *)
  (*   unfold acts_list. destruct constructive_indefinite_description. simpl. *)
  (*   apply AuxRel.set_equiv_exp_equiv. intros e. *)
  (*   rewrite in_filterP_iff. intuition.  *)
  (* Qed. *)
  (* Opaque acts_list. *)
  (* (***********) *)

  Definition trav_sets_left (T : ext_trav_config) :
    (actid -> Prop) * (actid -> Prop) * (actid -> Prop) :=
    (set_compl (ecovered T) ∩₁ E,
     W ∩₁ set_compl (eissued T) ∩₁ E,
     W ∩₁ set_compl (reserved T) ∩₁ E).

  (* Definition trav_sets_le : relation ext_trav_config := *)
  (*   trav_sets_left ↓ *)
  (*   RelationPairs.RelProd *)
  (*   (RelationPairs.RelProd (@set_subset actid) (@set_subset actid)) *)
  (*   (@set_subset actid).  *)

  Definition sets_le : relation ((actid -> Prop) * (actid -> Prop) * (actid -> Prop)) :=
    (* trav_sets_left ↓ *)
    RelationPairs.RelProd
    (RelationPairs.RelProd (@set_subset actid) (@set_subset actid))
    (@set_subset actid). 

  (* Definition trav_sets_equiv : relation ext_trav_config := *)
  (*   trav_sets_left ↓ *)
  (*   RelationPairs.RelProd *)
  (*   (RelationPairs.RelProd (@set_equiv actid) (@set_equiv actid)) *)
  (*   (@set_equiv actid).      *)

  Definition sets_equiv : relation ((actid -> Prop) * (actid -> Prop) * (actid -> Prop)) :=
    (* trav_sets_left ↓ *)
    RelationPairs.RelProd
    (RelationPairs.RelProd (@set_equiv actid) (@set_equiv actid))
    (@set_equiv actid).

  (* (* TODO: unify / move *) *)
  (* Definition strict_inclusion {A: Type} (s1 s2: A -> Prop) := *)
  (*   s1 ⊆₁ s2 /\ ~ s1 ≡₁ s2. *)
  (* Notation "a ⊂₁ b" := (strict_inclusion a b)  (at level 60). *)

  Instance reflexive_map_rel {A B: Type} (r: relation B) (f: A -> B)
        (REFL: Reflexive r):
    Reflexive (f ↓ r). 
  Proof. basic_solver. Qed.  

  Instance transitive_map_rel {A B: Type} (r: relation B) (f: A -> B)
        (TRANS: Transitive r):
    Transitive (f ↓ r). 
  Proof. basic_solver. Qed.  

  Instance symmetric_map_rel {A B: Type} (r: relation B) (f: A -> B)
        (SYMM: Symmetric r):
    Symmetric (f ↓ r). 
  Proof. basic_solver. Qed.  

  Instance equivalence_map_rel {A B: Type} (r: relation B) (f: A -> B)
        (EQ: Equivalence r):
    Equivalence (f ↓ r). 
  Proof.
    inversion EQ. 
    constructor;
      auto using reflexive_map_rel, transitive_map_rel, symmetric_map_rel.
  Qed.

  Instance PreOrder_map_rel {A B: Type} (r: relation B) (f: A -> B)
        (PO: PreOrder r):
    PreOrder (f ↓ r). 
  Proof.
    inversion PO. constructor; auto using reflexive_map_rel, transitive_map_rel.
  Qed.
  
  (* Instance trav_sets_le_PreOrder: PreOrder trav_sets_le. *)
  (* Proof. *)
  (*   apply PreOrder_map_rel.  *)
  (*   constructor. *)
  (*   { repeat apply RelationPairs.RelProd_Reflexive; auto. } *)
  (*   repeat apply RelationPairs.RelProd_Transitive; basic_solver.  *)
  (* Qed. *)

  (* Instance trav_sets_equiv_Equivalence: Equivalence trav_sets_equiv. *)
  (* Proof. *)
  (*   apply equivalence_map_rel. *)
  (*   repeat apply RelationPairs.RelProd_Equivalence; apply set_equiv_rel. *)
  (* Qed.  *)

  Instance PartialOrder_map_rel {A B: Type} (r req: relation B) (f: A -> B)
        `{PO: PartialOrder B req r}:
    PartialOrder (f ↓ req) (f ↓ r). 
  Proof.
    constructor.
    all: ins; by apply PO in H. 
  Qed.

  Instance RelProd_PreOrder {A B: Type}
           (ra: relation A) (rb: relation B)
           `{POa: PreOrder A ra} `{POb: PreOrder B rb}:
    PreOrder (RelationPairs.RelProd ra rb).
  Proof.
    inversion POa. inversion POb. 
    constructor; auto using RelationPairs.RelProd_Reflexive, RelationPairs.RelProd_Transitive.
  Qed. 

  Instance RelProd_PartialOrder {A B: Type}
           (ra raeq: relation A) (rb rbeq: relation B)
           `{POa: PartialOrder A raeq ra} `{POb: PartialOrder B rbeq rb}:
    PartialOrder 
                 (RelationPairs.RelProd raeq rbeq)
                 (RelationPairs.RelProd ra rb).
  Proof.
    constructor. 
    { intros. apply RelationPairs.pair_compat.
      - split.
        + apply POa. symmetry. eapply RelationPairs.fst_compat; eauto.
        + apply POb. symmetry. eapply RelationPairs.snd_compat; eauto.
      - split.
        + apply POa. eapply RelationPairs.fst_compat; eauto.
        + apply POb. eapply RelationPairs.snd_compat; eauto. }
    ins. do 3 red in H. desc. red in H0.
    pose proof (RelationPairs.fst_compat _ _ _ _ H).
    pose proof (RelationPairs.fst_compat _ _ _ _ H0). 
    pose proof (RelationPairs.snd_compat _ _ _ _ H).
    pose proof (RelationPairs.snd_compat _ _ _ _ H0). 
    apply RelationPairs.pair_compat; [apply POa | apply POb]; do 3 red; auto. 
  Qed.       
  
  Instance sets_le_PartialOrder: PartialOrder sets_equiv sets_le.
  Proof.
    repeat apply RelProd_PartialOrder; basic_solver.
  Qed.
  
  (* Definition trav_sets_lt := trav_sets_le \ trav_sets_equiv. *)
  Definition sets_lt := sets_le \ sets_equiv.
  
  Instance trav_sets_lt_StrictOrder: StrictOrder sets_lt.
  Proof.
    assert (Irreflexive sets_lt) as IRR.
    { red. unfold sets_lt. red. ins. intros [LE NEQ].
      destruct NEQ. repeat apply RelationPairs.pair_compat; basic_solver. }
    split; auto.
    red. ins. destruct H0, H.
    split.
    { etransitivity; eauto. }
    intros EQ.
    apply sets_le_PartialOrder in EQ.
    do 3 red in EQ. desc. red in EQ0.
    destruct (partial_order_antisym sets_le_PartialOrder x y); try done.
    { etransitivity; eauto. }
    by destruct H2.
  Qed.

  Lemma prod3_alt {A: Type} (S1 S2 S3 S1' S2' S3': A) (r: relation A):
    RelationPairs.RelProd (RelationPairs.RelProd r r) r (S1, S2, S3) (S1', S2', S3') <->
    ((r S1 S1') /\ (r S2 S2') /\ (r S3 S3')).
  Proof.
    split.
    2: { ins. desc. repeat apply RelationPairs.pair_compat; auto. }
    ins. splits.
    - by repeat apply RelationPairs.fst_compat in H.
    - by apply RelationPairs.fst_compat, RelationPairs.snd_compat in H.
    - by apply RelationPairs.snd_compat in H. 
  Qed. 
  
  Lemma etc_dom (T : ext_trav_config) (ETCCOH : etc_coherent G sc T):
    ecovered T ∪₁ eissued T ∪₁ reserved T ⊆₁ acts_set G.
  Proof.
    destruct T. inversion ETCCOH.
    do 2 try (apply set_subset_union_l; split); simpl. 
    - unfold ecovered. simpl. eapply coveredE; eauto.
    - unfold eissued. simpl. eapply issuedE; eauto.
    - inversion ETCCOH. auto.
  Qed. 

  Lemma trav_sets_left_step_decrease (T T' : ext_trav_config)
        (STEP : ext_trav_step G sc T T') :
    sets_lt (trav_sets_left T') (trav_sets_left T). 
  Proof using WF.
    red in STEP. desc. red in STEP.
    desf.
    { unfold sets_lt. split.
      { repeat apply RelationPairs.pair_compat;
          (rewrite COVEQ || rewrite ISSEQ || rewrite RESEQ); basic_solver 10. }
      intros EQ. apply prod3_alt in EQ. desc.
      apply AuxRel.set_equiv_exp_equiv with (x := e), proj2 in EQ.
      destruct EQ.
      { split; auto. inversion ETCCOH'. eapply coveredE; eauto.
        apply COVEQ. basic_solver. }
      destruct H. apply COVEQ. basic_solver. }
    { unfold sets_lt. split.
      { repeat apply RelationPairs.pair_compat;
          (rewrite COVEQ || rewrite ISSEQ || rewrite RESEQ); basic_solver 10. }

      intros EQ. apply prod3_alt in EQ. desc.
      apply AuxRel.set_equiv_exp_equiv with (x := e) in EQ0.
      destruct (proj2 EQ0).
      { unfolder. splits; auto.
        { apply (reservedW WF ETCCOH'). apply RESEQ. basic_solver. }
        eapply etc_dom; eauto. left. right. apply ISSEQ. basic_solver. }
      destruct H. destruct H1. apply ISSEQ. basic_solver. }
    { unfold sets_lt. split.
      { repeat apply RelationPairs.pair_compat;
          (rewrite COVEQ || rewrite ISSEQ || rewrite RESEQ); basic_solver 10. }
      intros EQ%RelationPairs.snd_compat. simpl in EQ.
      apply AuxRel.set_equiv_exp_equiv with (x := e) in EQ.
      destruct (proj2 EQ).
      { unfolder. splits; auto.
        { apply (reservedW WF ETCCOH'). apply RESEQ. basic_solver. }
        eapply etc_dom; eauto. right. apply RESEQ. basic_solver. }
      destruct H, H1. apply RESEQ. basic_solver. } 
  Qed.
      
  Lemma trav_sets_left_steps_decrease (T T' : ext_trav_config)
        (STEPS : (ext_trav_step G sc)⁺ T T') :
    sets_lt (trav_sets_left T') (trav_sets_left T). 
  Proof using WF.
    induction STEPS.
    { by apply trav_sets_left_step_decrease. }
    etransitivity; eauto.
  Qed.

  Lemma trav_sets_left_decrease_sim (T T' : ext_trav_config)
        (STEP : ext_sim_trav_step G sc T T') :
    sets_lt (trav_sets_left T') (trav_sets_left T). 
  Proof using WF.
    apply trav_sets_left_steps_decrease. by apply ext_sim_trav_step_in_trav_steps.
  Qed.

  (* incorrect *)
  (* Lemma trav_sets_left_null_cov (T : ext_trav_config) *)
  (*       (NULL : sets_le (trav_sets_left T) (set_compl E, ∅, ∅)) : *)
  (*   E ⊆₁ ecovered T. *)
  (* Proof using. *)
  (*   repeat apply RelationPairs.fst_compat in NULL. simpl in NULL. *)
  (*   apply set_subset_compl in NULL. by rewrite !set_compl_compl in NULL.  *)
  (* Qed. *)
  
  (* Lemma trav_sets_left_ncov_nnull (T : ext_trav_config) e *)
  (*       (EE : E e) (NCOV : ~ ecovered T e): *)
  (*   ~ (fst (fst (trav_sets_left T)) ≡₁ ∅). *)
  (* Proof using. *)
  (*   simpl. intros EQ. destruct NCOV. *)
    
  (*   generalize NCOV. basic_solver 10.  *)
  (*   destruct (classic (trav_steps_left T = 0)) as [EQ|NEQ]; auto. *)
  (*   exfalso. apply NCOV. apply trav_steps_left_null_cov; auto. *)
  (* Qed. *)

  
  (* Lemma sets_le_alt (S1 S2 S3 S1' S2' S3': actid -> Prop): *)
  (*   sets_equiv (S1, S2, S3) (S1', S2', S3') <-> *)
  (*   ((S1 ≡₁ S1') /\ (S2 ≡₁ S2') /\ (S3 ≡₁ S3')). *)
  (* Proof. *)
  (*   split. *)
  (*   2: { ins. desc. repeat apply RelationPairs.pair_compat; auto. } *)
  (*   ins. splits. *)
  (*   - by repeat apply RelationPairs.fst_compat in H. *)
  (*   - by apply RelationPairs.fst_compat, RelationPairs.snd_compat in H. *)
  (*   - by apply RelationPairs.snd_compat in H.  *)
  (* Qed.  *)

  
  Lemma trav_sets_left_nnull_ncov (T : ext_trav_config)
        (ETCCOH : etc_coherent G sc T)
        (NNULL : sets_lt (∅, ∅, ∅) (trav_sets_left T)):
    exists e, (set_compl (ecovered T) ∩₁ E) e.
  Proof using.
    assert (tc_coherent G sc (etc_TC T)) as TCCOH by apply ETCCOH.

    assert (W ∩₁ set_compl (eissued T) ∩₁ E ⊆₁ set_compl (ecovered T) ∩₁ E) as AA.
    { intros x [[WX NN] Ex]. split; auto. intros NC.
      apply NN. eapply w_covered_issued; eauto. by split. }

    assert (W ∩₁ set_compl (reserved T) ∩₁ E ⊆₁ W ∩₁ set_compl (eissued T) ∩₁ E) as BB.
    { intros x [[WX NN] Ex]. unfolder. splits; auto. intros NI.  
      apply NN. by apply (etc_I_in_S ETCCOH). }
          
    apply set_nonemptyE. intros NO.
    rewrite NO in AA. rewrite set_subset_empty_r in AA.
    rewrite AA in BB. rewrite set_subset_empty_r in BB. 

    destruct NNULL. destruct H0. apply prod3_alt. splits; symmetry; auto. 
  Qed.

  
  Lemma trav_sets_left_decrease_sim_trans (T T' : ext_trav_config)
        (STEPS : (ext_sim_trav_step G sc)⁺ T T') :
    sets_lt (trav_sets_left T') (trav_sets_left T). 
  Proof using WF.
    induction STEPS.
    { by apply trav_sets_left_decrease_sim. }
    etransitivity; eauto. 
  Qed.

  (* Lemma acts_nexts_enum T *)
  (*       (IMMCON : imm_consistent G sc) *)
  (*       (ETCCOH : etc_coherent G sc T) *)
  (*       (RELCOV : W ∩₁ Rel ∩₁ eissued T ⊆₁ ecovered T) *)
  (*       (RMWCOV : forall r w (RMW : rmw r w), ecovered T r <-> ecovered T w) : *)
  (* exists (len: nat_omega) (enum: nat -> actid), *)
  (*   ⟪ COVERS: acts_set G ≡₁ ⋃₁ i ∈ (flip NOmega.lt_nat_l len), eq (enum i) ⟫ *)
  (*   /\ *)
  (*   ⟪ STEPS: forall i (DOM: NOmega.lt_nat_l i len), *)
  (*         (ext_sim_trav_step G sc)＊ T (T's i) ⟫. *)
  (* Proof. *)
  (* Abort.  *)

Lemma simulation_enum_impl T
      (FAIR: mem_fair G)
      (IMMCON : imm_consistent G sc)
      (ETCCOH : etc_coherent G sc T)
      (RELCOV : W ∩₁ Rel ∩₁ eissued T ⊆₁ ecovered T)
      (RMWCOV : forall r w (RMW : rmw r w), ecovered T r <-> ecovered T w):      
  exists (len: nat_omega) (Ts: nat -> ext_trav_config),
    ⟪ TRAV: acts_set G ≡₁ ⋃₁ i ∈ (flip NOmega.lt_nat_l len),
                             ecovered (Ts i) ⟫ /\
    ⟪ TINIT: Ts 0 = T ⟫ /\
    ⟪ TSTEP: forall i (DOM: NOmega.lt_nat_l i len),
        (ext_sim_trav_step G sc)＊ T (Ts i)⟫. 
Proof using All.
  (* See notes in PromiseToImm_s *)
Admitted. 
  

Lemma simulation_enum
      (FAIR: mem_fair G)
      (IMMCON : imm_consistent G sc):
  exists (len: nat_omega) (Ts: nat -> ext_trav_config),
    ⟪ TRAV: acts_set G ≡₁ ⋃₁ i ∈ (flip NOmega.lt_nat_l len),
                             ecovered (Ts i) ⟫ /\
    (* ⟪ TINIT: Ts 0 = ext_trav_init G ⟫ /\ *)
    ⟪ TSTEP: forall i (DOM: NOmega.lt_nat_l i len),
        (ext_sim_trav_step G sc)＊ (ext_init_trav G) (Ts i)⟫. 
Proof using All.
  forward eapply simulation_enum_impl with (T := ext_init_trav G); eauto.
  { by eapply ext_init_trav_coherent. }
  { unfold ext_init_trav. simpls. basic_solver. }
  { unfold ecovered, eissued.
    ins. split; intros [HH AA].
    { apply (init_w WF) in HH.
      apply (dom_l (wf_rmwD WF)) in RMW. apply seq_eqv_l in RMW.
      type_solver. }
    apply (rmw_in_sb WF) in RMW. apply no_sb_to_init in RMW.
    apply seq_eqv_r in RMW. desf. }
  ins. desc. do 2 eexists. splits; eauto. 
Qed.  

End ExtTraversalCounting.
