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
Require Import ThreadsSetFin. 
Require Import FinTravConfigs. 

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

(* TODO: move *)
From imm Require Import SimIordTraversal.
From imm Require Import FairExecution. 
From imm Require Import ImmFair. 
(* From imm Require Import ThreadBoundedExecution.  *)


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

  Notation "'NTid_' t" := (fun x => tid x <> t) (at level 1).
  Notation "'Tid_' t"  := (fun x => tid x =  t) (at level 1).

  (* TODO: move*)
  From imm Require Import EnumPrefix. 

  (* TODO: move*)
  Lemma iord_coherent_crt T
        (ICOH: iord_coherent G sc T):
    dom_rel ((iord G sc)^* ⨾ ⦗T⦘) ⊆₁ T.
  Proof using.
  Admitted.

  (* TODO: move*)
  Lemma set_size_finite {A: Type} (S: A -> Prop)
    (FIN: set_finite S):
    exists n, set_size S = NOnum n.
  Proof using.
    unfold set_size. destruct (excluded_middle_informative _); by vauto.
  Qed.

  (* (TODO: move) *)
  Require Import Basics.
  Lemma enumerates_set_bunion {A: Type} (steps: nat -> A) (S: A -> Prop)
        (ENUM: enumerates steps S):
    S ≡₁ ⋃₁ i ∈ flip NOmega.lt_nat_l (set_size S), eq (steps i).
  Proof using. 
    apply enumeratesE' in ENUM. desc.
    split; unfolder; ins; desc; subst. 
    by apply INSET.
  Qed.

  (* TODO: temporary hack to fall back to old threads_bound definition *)
  From imm Require Import ThreadBoundedExecution.
  Lemma fin_threads2threads_bound:
    fin_threads G -> exists t, threads_bound G t.
  Proof using. Admitted.
    
  Lemma iord_enum_exists' T
        (CONS: imm_consistent G sc)
        (FAIR: mem_fair G)
        (IMM_FAIR: imm_s_fair G sc)
        (FIN_THREADS: fin_threads G)
        (TCOH: tls_coherent G T)
        (ICOH: iord_coherent G sc T)
        (T_FIN: tls_fin T)
    :
    exists (steps: nat -> trav_label),
      enumerates steps (exec_tls G) /\
      respects_rel steps (iord G sc)⁺ (exec_tls G) /\
      (exists i, NOmega.le (NOnum i) (set_size (exec_tls G)) /\ 
            trav_prefix steps i ∪₁ init_tls G ≡₁ T). 
  Proof using WFSC WF COMP.
    edestruct countable_ext with (s := exec_tls G) (r := ⦗event ↓₁ (set_compl is_init)⦘ ⨾ ((iord G sc)⁺ ∪ (T × (set_compl T) \ (iord G sc)^+)))
      as [| [steps [ENUM RESP]]].
    { eapply countable_subset; [| by apply set_subset_full_r].
      apply trav_label_countable. }
    { red. split.
      { rewrite inclusion_seq_eqv_l.
        apply irreflexive_union. split.
        { by apply iord_acyclic. }
        basic_solver. }
      red. intros ? ? ? ?%seq_eqv_l  ?%seq_eqv_l. desc.
      apply seq_eqv_l. split; auto.
      destruct (classic ((iord G sc)⁺ x z)); [by vauto | ]. right. split; auto.
      destruct H2, H1. 
      { edestruct H3. eapply transitive_ct; eauto. }
      { destruct H1 as [[Ty NTz] NRELyz].
        split; auto.
        apply iord_coherent_crt in ICOH. apply ICOH.
        apply inclusion_t_rt in H2. basic_solver 10. }
      { destruct H2 as [[Tx NTy] NRELxy].
        split; auto. 
        intros Tz. apply NTy.
        apply iord_coherent_crt in ICOH. apply ICOH.
        apply inclusion_t_rt in H1. basic_solver 10. }
      { generalize H2, H1. basic_solver. }
    }
    { relsf. apply fsupp_union.
      { apply fin_threads2threads_bound in FIN_THREADS. desc. 
        eapply iord_ct_fsupp; eauto. }
      rewrite inclusion_minus_rel.
      rewrite <- cross_inter_l. apply fsupp_cross.
      rewrite set_interC. apply T_FIN. }
    { edestruct H. constructor. econstructor; vauto. }

    exists steps. splits; eauto.
    red. ins. apply RESP; auto.
    1, 2: by apply set_lt_size.
    { apply seq_eqv_l. splits; auto.
      2: { by left. }
      apply enumeratesE' in ENUM. desc. apply INSET in DOMi.
      apply ct_begin in Rij. generalize Rij. unfold iord. basic_solver. }

    apply enumeratesE' in ENUM as ENUM_. desc. 
    (* forward eapply set_size_finite as [n SIZE]; eauto. *)
    (* exists n.  *)
    destruct (classic (exists k, ((exec_tls G) \₁ T) (steps k) /\ NOmega.lt_nat_l k (set_size (exec_tls G)))) as [NTk | ALLT].
    2: { assert (T ≡₁ init_tls G ∪₁ exec_tls G).
         { split.
           { apply TCOH. }
           unfolder. ins.
           destruct (classic (T x)); [done| ]. 
           destruct H; [by apply TCOH| ]. 
           apply IND in H as INDk. desc. subst.
           destruct ALLT. by vauto. }
         unfold trav_prefix. 
         forward eapply set_size_finite as [n SIZE]; eauto. 
         assert (set_size (exec_tls G) = NOnum n) as EQ_SIZE. 
         { rewrite <- SIZE. symmetry. apply set_size_equiv.
           rewrite H. unfold init_tls, exec_tls.
           rewrite !AuxDef.set_pair_alt. basic_solver 10. } 
         exists n. split.
         { by rewrite EQ_SIZE. }
         rewrite H. rewrite set_unionC. apply set_equiv_union; [done| ].  
         erewrite enumerates_set_bunion with (S := exec_tls G); eauto.
         rewrite EQ_SIZE. by vauto. }

    apply exists_min in NTk as [m [[NTm DOMm] MINm]].
    destruct (classic (exists k, T (steps k) /\ m < k /\ NOmega.lt_nat_l k (set_size (exec_tls G)))).
    { desc. specialize (RESP k m). specialize_full RESP.
      { by apply set_lt_size. }
      { apply set_lt_size. eapply NOmega.lt_lt_nat; eauto. }
      { apply seq_eqv_l. split. 
        { eapply exec_tls_ENI. eapply step_event_dom; eauto. }
        destruct (classic ((iord G sc)⁺ (steps k) (steps m))) as [IORD | NIORD].
        { vauto. }
        right. split; auto. 
        split; auto. apply NTm. }
      lia. }

    exists m. unfold trav_prefix. split.
    { destruct (set_size (exec_tls G)); [by vauto| ]. ins. lia. }
    arewrite (T ≡₁ T ∩₁ event ↓₁ set_compl is_init ∪₁ init_tls G).
    { rewrite set_split_complete with (s' := T) (s := event ↓₁ is_init) at 1.
      rewrite set_unionC. apply set_equiv_union; [basic_solver| ].
      destruct TCOH. 
      split.
      2: { relsf. split; auto. rewrite init_tls_EI. basic_solver. }
      rewrite tls_coh_exec.
      unfold init_tls, exec_tls. rewrite !AuxDef.set_pair_alt. basic_solver 10. }
    apply set_equiv_union; [| done]. 
    split; unfolder; ins; desc.
    { apply MINm in H0 as MIN'. AuxDef.contra NTx. destruct MIN'.
      split.
      2: { eapply NOmega.lt_lt_nat; eauto. }
      apply not_and_or in NTx. destruct NTx as [NTx | Ix]. 
      2: { apply NNPP in Ix.
           specialize (INSET y). specialize_full INSET.
           { eapply NOmega.lt_lt_nat; eauto. }
           apply exec_tls_ENI, proj2 in INSET. vauto. }  
      split; try congruence.
      apply INSET.
      eapply NOmega.lt_lt_nat; eauto. }
    specialize (IND x). specialize_full IND.
    { apply TCOH in H0 as [Ix | ?]; [| done].
      apply init_tls_EI in Ix. destruct H1. apply Ix. }
    desc. eexists. splits; eauto.
    AuxDef.contra GE. apply Compare_dec.not_lt in GE. red in GE.
    apply Lt.le_lt_or_eq in GE. destruct GE as [LT | ->].
    2: { apply proj2 in NTm. destruct NTm. congruence. }
    destruct H. exists i. splits; eauto. congruence.
  Qed. 

  
  (* TODO: move *)
  From imm Require Import AuxDef.
  From imm Require Import SimClosure.

  (* TODO: move *)
  Lemma sim_traversal_inf' T
        (FAIR: mem_fair G)
        (IMM_FAIR: imm_s_fair G sc)
        (CONS: imm_consistent G sc)
        (FIN_THREADS: fin_threads G)
        (T_FIN: tls_fin T)
        (TCOH: tls_coherent G T)
        (ICOH: iord_coherent G sc T):
    exists (sim_enum: nat -> (trav_label -> Prop)),
      ⟪INIT: sim_enum 0 ≡₁ init_tls G ⟫ /\
      ⟪COH: forall i (DOMi: NOmega.le (NOnum i) (set_size (exec_tls G))),
          tls_coherent G (sim_enum i)⟫ /\
      ⟪STEPS: forall i (DOMi: NOmega.lt_nat_l i (set_size (exec_tls G))),
          (sim_clos_step G sc)^* (sim_enum i) (sim_enum (1 + i)) ⟫ /\
      ⟪ENUM: forall e (Ee: (E \₁ is_init) e), exists i,
           NOmega.le (NOnum i) (set_size (exec_tls G)) /\
             (sim_enum i) (mkTL ta_cover e)⟫ /\
      ⟪CLOS_T: exists i, NOmega.le (NOnum i) (set_size (exec_tls G)) /\
                    sim_enum i ≡₁ sim_clos G T ∪₁ init_tls G⟫. 
  Proof using WFSC WF COMP.
    edestruct iord_enum_exists' with (T := T) as [steps_enum [ENUM [RESP T_I]]]; eauto.
    exists (tc_enum G steps_enum). splits.
    { unfold tc_enum. rewrite trav_prefix_init.
      rewrite sim_clos_empty. basic_solver. }
    { apply tc_enum_tls_coherent; eauto. }
    { apply sim_traversal_next; auto.
      rewrite iord_exec_tls. basic_solver. }
    { intros e Ee.
      pose proof ENUM as ENUM'. apply enumeratesE' in ENUM. desc.
      specialize (IND (mkTL ta_cover e)). specialize_full IND.
      { red. left. vauto. }
      desc. exists (S i0). split; [by vauto| ]. 
      eapply set_equiv_exp.
      { unfold tc_enum. rewrite trav_prefix_ext; eauto. }
      rewrite IND0. unfold sim_clos. basic_solver 10.  }
    desc. exists i. split; auto. 
    unfold tc_enum.
    rewrite <- set_unionK with (s := init_tls G)at 1. rewrite <- set_unionA.
    forward eapply init_tls_sim_coh as INIT;eauto. red in INIT. rewrite INIT at 1.
    rewrite <- sim_clos_dist. by rewrite T_I0.
  Qed.

  (* TODO: move*)
  Lemma list_max_In (l: list nat) (NNIL: l <> nil):
    In (list_max l) l. 
  Proof using.
    generalize dependent NNIL. induction l; [by vauto| ].
    ins. 
    destruct l eqn:LL.
    { ins. lia. }
    specialize_full IHl; [done| ]. rewrite <- LL in *. clear LL.  
    destruct (Nat.max_spec_le a (list_max l)); desc.
    { rewrite H0. by right. }
    auto.
  Qed.

  (* TODO: move EnumProperties section from Hardwarefairness to lib and refactor it*)
  From imm Require Import HardwareFairness.

  (* TODO: move*)
  Lemma enum_steps_crt {A: Type} (r: relation A) (f: nat -> A) (b: nat_omega)
        (STEPS: forall i (DOM: NOmega.lt_nat_l i b), r (f i) (f (i + 1))):
    forall i j (LE: i <= j) (DOM: NOmega.le (NOnum j) b), r^* (f i) (f j).
  Proof using.
  (*   ins. apply Lt.le_lt_or_eq in LE as [LT | ->]. *)
  (*   { apply inclusion_t_rt. apply enum_steps; auto. } *)
  (*   apply rt_refl.  *)
  (* Qed. *)
  Admitted.

  Lemma iiord_step_incl T1 T2 l
        (STEP: (iiord_step G sc) l T1 T2):
    T1 ⊆₁ T2.
  Proof using.
    do 2 red in STEP. desc. generalize STEP. basic_solver.
  Qed. 

  Lemma sim_clos_step_incl T1 T2
        (STEP: (sim_clos_step G sc) T1 T2):
    T1 ⊆₁ T2.
  Proof using. 
    inversion STEP. desc. red in H.
    Local Ltac destr := (match goal with
    | tls: list trav_label |- _ => destruct tls as [| [?a ?e] tll]; [| destruct a]
    end).
    repeat (destr; try done).
    all: try by (eapply iiord_step_incl; eauto).
    1, 3: by apply proj2 in H; destruct H; desc;
    etransitivity; eapply iiord_step_incl; eauto. 
    apply proj2 in H. destruct H. desc. destruct H2. desc.
    etransitivity; [etransitivity| ]; eapply iiord_step_incl; eauto. 
  Qed. 

  Lemma sim_clos_step_crt_incl T1 T2
        (STEP: (sim_clos_step G sc)^* T1 T2):
    T1 ⊆₁ T2.
  Proof using.
    induction STEP; [by apply sim_clos_step_incl| basic_solver| ].
    etransitivity; eauto.
  Qed. 
    
  Hypothesis FINDOM: fin_exec G.
  (* TODO: move to FinExecution *)
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

  (* TODO: move *)
  Lemma sim_traversal_inf'_fin T
        (FAIR: mem_fair G)
        (IMM_FAIR: imm_s_fair G sc)
        (CONS: imm_consistent G sc)
        (FIN_THREADS: fin_threads G)
        (TCOH: tls_coherent G T)
        (ICOH: iord_coherent G sc T):
    exists T',
      let Tclos := sim_clos G T ∪₁ init_tls G in 
      (* ⟪INIT: sim_enum 0 ≡₁ init_tls G ⟫ /\ *)
      ⟪COH: tls_coherent G T'⟫ /\
      ⟪STEPS1: (sim_clos_step G sc)^* (init_tls G) Tclos⟫ /\
      ⟪STEPS2: (sim_clos_step G sc)^* Tclos T'⟫ /\
      ⟪COV: acts_set G ⊆₁ covered T'⟫. 
  Proof using WFSC WF COMP FINDOM. 
    forward eapply sim_traversal_inf' with (T := T) as TRAV; eauto.
    { eapply fin_exec_tls_fin; eauto. }
    desc.
    forward eapply set_size_finite as [n SIZE].
    { eapply fin_exec_exec_tls; eauto. }
    exists (sim_enum n). simpl. splits.
    { apply COH. rewrite SIZE. simpl. lia. }
    { apply rt_of_rt.
      rewrite <- CLOS_T0, <- INIT.
      eapply enum_steps_crt; eauto; [| lia].
      ins. rewrite Nat.add_comm. by apply STEPS. }
    { rewrite <- CLOS_T0.
      apply rt_of_rt.
      eapply enum_steps_crt with (b := NOnum n); try by vauto.
      { ins. rewrite Nat.add_comm. apply STEPS. by rewrite SIZE. }
      by rewrite SIZE in CLOS_T. }
    rewrite set_split_complete with (s' := E) (s := is_init). unionL. 
    { transitivity (covered (sim_enum 0)).
      { rewrite INIT. rewrite set_interC, init_covered; [reflexivity| ].
        apply init_tls_tls_coherent. }
      apply covered_mori. apply sim_clos_step_crt_incl.
      apply rt_of_rt.
      eapply enum_steps_crt with (b := NOnum n); (try by vauto); [| lia].
      ins. rewrite Nat.add_comm. apply STEPS. by rewrite SIZE. }
    unfolder. intros. apply ENUM in H. desc. 
    eapply covered_mori.
    2: { apply tls_set_alt. apply H0. }
    apply sim_clos_step_crt_incl. 
    apply rt_of_rt.
    eapply enum_steps_crt with (b := NOnum n); (try by vauto).
    { intros. rewrite Nat.add_comm. apply STEPS. by rewrite SIZE. }
    by rewrite SIZE in H.
  Qed.

  Lemma sim_clos_step2ext_isim_trav_step thread T1 T2
        (NCOV : NTid_ thread ∩₁ (acts_set G) ⊆₁ covered T1)
        (STEP: (sim_clos_step G sc) T1 T2)

        (RCOH: reserve_coherent G T1)

        (TCOH2: tls_coherent G T2)
        (RCOH2: reserve_coherent G T2)

    :
    (ext_isim_trav_step G sc thread) T1 T2.
  Proof using.
    destruct STEP. desc. red in H.
    repeat (destr; try done).
    { destruct H as ([NT1e T2_EQ]%seq_eqv_l & ICOH1 & ICOH2).
      destruct (classic (tid e = thread)) as [<- | Nte].
      2: { destruct NT1e. apply tls_set_alt, NCOV. split; auto.
           replace e with (event (ta_cover, e)) by done. 
           eapply tlsc_E; eauto. apply T2_EQ. vauto. }
      destruct (lab_rwf lab e) as [R | [W | F]].
      { rename e into r. 
        destruct (classic (dom_rel rmw r)) as [RMWe | NRMWe].
        2: { eapply ext_read_trav_step; eauto.
             split; eauto.
             { ins. }
             simpl. rewrite set_pair_alt. rewrite T2_EQ. basic_solver. }
        destruct RMWe as [w RMW].
        destruct NT1e. 
        
        red in H1. unfold sim_clos, rmw_clos in H1.
        admit. }
      { admit. }
      admit. }
  Admitted. 

  Lemma sim_clos_step2ext_isim_trav_step_crt thread T1 T2
        (NCOV : NTid_ thread ∩₁ (acts_set G) ⊆₁ covered T1)
        (STEP: (sim_clos_step G sc)^* T1 T2)
        (RCOH: reserve_coherent G T1)
        (TCOH2: tls_coherent G T2)
        (RCOH2: reserve_coherent G T2):
    (ext_isim_trav_step G sc thread)^* T1 T2.
  Proof using. 
    induction STEP.
    { apply rt_step, sim_clos_step2ext_isim_trav_step; auto. }
    { apply rt_refl. }
    eapply rt_trans; [apply IHSTEP1 | apply IHSTEP2]; eauto.
    (* TODO: show that needed premises are preserved by sim_clos_step *)
    all: admit.
  Admitted. 


  Lemma sim_coherent_alt T
        (TCOH: tls_coherent G T)
        (ICOH: iord_coherent G sc T)
        (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
        (RMWCOV : forall r w, rmw r w -> covered T r <-> covered T w):
    sim_coherent G T.
  Proof using WF. 
    red. unfold sim_clos. split; [basic_solver| ].
    unionL; [done| ..].
    { unfold rmw_clos. rewrite set_pair_alt. unfolder.
      intros [a w] [LBLw [r [COVr RMW]]]. ins. 
      assert (T (mkTL ta_cover w)) as COV.
      { apply tls_set_alt. eapply (RMWCOV r w); eauto. }
      des; apply tls_set_alt; vauto.
      eapply w_covered_issued; eauto. split.
      { apply wf_rmwD, seq_eqv_lr in RMW; eauto. by desc. }
      by apply tls_set_alt. }
    unfold rel_clos. rewrite set_pair_alt. unfolder. ins.
    destruct x. ins. desc. subst.
    apply tls_set_alt, RELCOV. unfolder. splits; auto.
    eapply issuedW in H1; eauto.
  Qed.


  Lemma sim_step_cov_full_traversal T thread
        (IMMCON : imm_consistent G sc)
        (FAIR: mem_fair G)
        (FIN_THREADS: fin_threads G)
        (IMM_FAIR: imm_s_fair G sc)
        (TCOH: tls_coherent G T)
        (ICOH: iord_coherent G sc T)
        (RCOH: reserve_coherent G T)
        (NCOV : NTid_ thread ∩₁ (acts_set G) ⊆₁ covered T)
        (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
        (RMWCOV : forall r w : actid, rmw r w -> covered T r <-> covered T w) :
    exists T', (ext_isim_trav_step G sc thread)＊ T T' /\ ((acts_set G) ⊆₁ covered T').
  Proof using WF WFSC FINDOM COMP.
    forward eapply sim_traversal_inf'_fin with (T := T); eauto.
    ins. desc. eexists. splits; eauto. 
    assert (T ≡₁ sim_clos G T ∪₁ init_tls G) as T_ALT. 
    { forward eapply (@sim_coherent_alt T) as SCOH; eauto. red in SCOH.
      rewrite <- set_union_absorb_r with (s' := T) (s := init_tls G) at 1. 
      2: { apply TCOH. }
      apply set_equiv_union; [| done].
      by apply sim_coherent_alt. }    
    apply sim_clos_step2ext_isim_trav_step_crt; eauto.
    { apply set_extensionality in T_ALT as T_ALT'. by rewrite T_ALT'. }
    (* TODO: show that reserve_coherent is preserved by sim_clos_step *)
    admit.     
  Admitted. 
      
End ExtTraversalCounting.
