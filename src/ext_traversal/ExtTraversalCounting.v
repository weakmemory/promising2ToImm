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

(* TODO: move *)
From imm Require Import SimIordTraversal.
From imm Require Import FairExecution. 
From imm Require Import ImmFair. 
From imm Require Import ThreadBoundedExecution. 


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

  (* TODO: move*)
  Definition tls_ninit_fin T :=
    set_finite (T ∩₁ event ↓₁ set_compl is_init). 
    
  Lemma iord_enum_exists' T
        (CONS: imm_consistent G sc)
        (FAIR: mem_fair G)
        (IMM_FAIR: imm_s_fair G sc)
        t (TB: threads_bound G t)
        (TCOH: tls_coherent G T)
        (ICOH: iord_coherent G sc T)
        (T_FIN: tls_ninit_fin T)
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
      { eapply iord_ct_fsupp; eauto. }
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
        t (TB: threads_bound G t)
        (T_FIN: tls_ninit_fin T)
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

  (* TODO: move*)
  Import ListNotations. 
  (* TODO: move*)
  Lemma fin_exec_exec_tls t (BOUND: threads_bound G t):
    set_finite (exec_tls G).
  Proof using FINDOM.
    unfold exec_tls.
    destruct FINDOM as [acts ACTS]. 
    forward eapply (BinPos_lt_fin t) as [threads THREADS].
    set (threads' := filterP (threads_set G \₁ eq tid_init) threads).
    (* set (threads' := filterP (fun t => exists e, tid e = t /\ E e) threads). *)
    arewrite ((E \₁ is_init) ∩₁ W ⊆₁ E\₁is_init) by basic_solver.
    rewrite !set_pair_alt. rewrite <- set_inter_union_l.
    exists (flat_map (fun e => map (fun a => mkTL a e) [ta_cover; ta_issue; ta_reserve]
                       ++ map (fun t => mkTL (ta_propagate t) e) threads') acts).
    unfolder. ins. apply in_flat_map.
    exists (event x). split.
    { apply ACTS, IN. }
    destruct x; des; ins; subst; try by tauto. 
    repeat right. apply in_map_iff.
    do 2 red in IN. desc. eexists. splits; vauto.
    subst threads'. apply in_filterP_iff. split; auto.
    (* TODO: make threads_bound a requirement of fin_exec *)
  Admitted.

  (* TODO: move *)
  Lemma sim_traversal_inf'_fin T
        (FAIR: mem_fair G)
        (IMM_FAIR: imm_s_fair G sc)
        (CONS: imm_consistent G sc)
        t (TB: threads_bound G t)
        (T_FIN: tls_ninit_fin T)
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
    forward eapply sim_traversal_inf' with (T := T) as TRAV; eauto. desc.
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


  Lemma sim_step_cov_full_traversal T thread t
        (IMMCON : imm_consistent G sc)
        (FAIR: mem_fair G)
        (IMM_FAIR: imm_s_fair G sc)
        (BOUND: threads_bound G t)
        (TCOH: tls_coherent G T)
        (ICOH: iord_coherent G sc T)
        (* (T_EXEC: T ⊆₁ exec_tls G) *)
        (T_FIN: tls_ninit_fin T)
        (* (RCOH: reserve_coherent G T) *)
        (* (NCOV : NTid_ thread ∩₁ (acts_set G) ⊆₁ covered T) *)
        (* (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T) *)
        (* (RMWCOV : forall r w : actid, rmw r w -> covered T r <-> covered T w) :  *)
        :
    exists T', (ext_isim_trav_step G sc thread)＊ T T' /\ ((acts_set G) ⊆₁ covered T').
  Proof using WF WFSC FINDOM COMP.
    forward eapply sim_traversal_inf'_fin with (T := T); eauto.
    ins. desc. eexists. splits; eauto. 
    (* TODO: how to infer that transitions happen only with the given thread? *)
    foobar.
  Abort.
    
    

  (* From imm Require Import SimTraversal.  *)

  (* Lemma isim_trav_step2ext_isim_trav_step (tc1 tc2: trav_label -> Prop) t *)
  (*       (TCOH: tls_coherent G tc1) *)
  (*       (ICOH: iord_coherent G sc tc2) *)
  (*       (STEP: isim_trav_step G sc t tc1 tc2) *)
  (*       (w_ex_is_xacq : W_ex G ⊆₁ W_ex G ∩₁ is_xacq (lab G)): *)
  (*   (ext_isim_trav_step G sc t)^* (mkETC tc1 (issued tc1)) (mkETC tc2 (issued tc2)). *)
  (* Proof. *)
  (*   forward eapply sim_trav_step_coherence as COH2; [by red; eauto| done |].  *)
    
  (*   inversion STEP; subst. *)
  (*   { apply rt_step. destruct tc1. simpl in *. *)
  (*     eapply ext_fence_trav_step, itrav_step2ext_itrav_step_cover; eauto. } *)
  (*   { apply rt_step. destruct tc1. simpl in *. *)
  (*     eapply eaxt_read_trav_step, itrav_step2ext_itrav_step_cover; eauto. } *)
  (*   { destruct tc1 as [C I] eqn:TC1. simpl in *. *)
  (*     assert (issuable G sc tc1 w) as ISS'w. *)
  (*     { inversion TS; red in H; desc; simpl in *. *)
  (*       2: congruence.  *)
  (*       destruct NEXT. apply COVEQ. basic_solver. } *)
  (*     apply itrav_step2ext_itrav_step_issue in TS as [tc' [STEPres STEP']]; auto. *)
  (*     apply seq_eqv_l in STEP' as [COH' STEP']. *)
      
  (*     destruct tc' as [[C' I'] R']. *)
  (*     assert (C' = C /\ I' = I /\ (R' = I \/ R' = I ∪₁ eq w)) as [-> [-> RES']]. *)
  (*     { destruct STEPres. *)
  (*       { inversion H. auto. } *)
  (*       apply seq_eqv_r in H. desc. inversion H0. auto. } *)
  (*     assert (R' ⊆₁ I ∪₁ eq w) as RES'_. *)
  (*     { destruct RES'; basic_solver. }  *)
      
  (*     apply rt_unit. exists [C # I # R']. split. *)
  (*     { destruct RES' as [-> | ->]; [by apply rt_refl| ].  *)
  (*       apply rt_step. apply ext_reserve_trav_step. red. splits; vauto. } *)
      
  (*     forward eapply ext_rlx_write_promise_step  *)
  (*       with (T := [C # I # R']) (sc := sc) as WSTEP; eauto. *)
  (*     { eapply ext_itrav_step_more; try by vauto. *)
  (*       rewrite reserved_rewrite_helper; vauto. } *)
  (*     rewrite reserved_rewrite_helper in WSTEP; vauto. } *)
  (*   { apply rt_step. destruct tc1. simpl in *. *)
  (*     eapply ext_rlx_write_cover_step, itrav_step2ext_itrav_step_cover; eauto. } *)
  (*   { destruct tc1 as [C I] eqn:TC1. simpl in *. *)
      
  (*     assert (tc_coherent G sc (mkTC C (I ∪₁ eq w))) as COH1'.  *)
  (*     { simpl. eapply trav_step_coherence; [| by apply COH1]. red. eauto. } *)
      
  (*     apply itrav_step2ext_itrav_step_issue in TS1 as [tc' [STEPres STEP']]; auto. *)
  (*     apply seq_eqv_l in STEP' as [COH' STEP']. *)
  (*     destruct tc' as [[C' I'] R']. *)
  (*     assert (C' = C /\ I' = I /\ (R' = I \/ R' = I ∪₁ eq w)) as [-> [-> RES']]. *)
  (*     { destruct STEPres. *)
  (*       { inversion H. auto. } *)
  (*       apply seq_eqv_r in H. desc. inversion H0. auto. } *)
  (*     assert (R' ⊆₁ I ∪₁ eq w) as RES'_. *)
  (*     { destruct RES'; basic_solver. }  *)
      
  (*     apply rt_unit. exists [C # I # R']. split. *)
  (*     { destruct RES' as [-> | ->]; [by apply rt_refl| ].  *)
  (*       apply rt_step. apply ext_reserve_trav_step. red. splits; vauto. } *)
      
  (*     assert (issuable G sc (mkTC C I) w) as ISS'w. *)
  (*     { apply issuable_add_eq_iff; auto. *)
  (*       apply issued_in_issuable; basic_solver. } *)
      
  (*     forward eapply ext_rel_write_step with (T := [C # I # R']) (sc := sc) *)
  (*       as WSTEP; eauto. *)
  (*     { rewrite reserved_rewrite_helper; vauto. } *)
  (*     { rewrite reserved_rewrite_helper; try by vauto. *)
  (*       unfold ecovered, eissued. simpl. *)
  (*       apply itrav_step2ext_itrav_step_cover; auto. } *)
  (*     rewrite reserved_rewrite_helper in WSTEP; vauto. }   *)
  (*   { destruct tc1 as [C I] eqn:TC1. simpl in *. *)
  (*     apply rt_step. apply ext_rlx_rmw_cover_step; auto.  *)
  (*     { apply itrav_step2ext_itrav_step_cover; auto. } *)
  (*     apply itrav_step2ext_itrav_step_cover; auto. *)
  (*     unfold ecovered. simpl. *)
  (*     eapply trav_step_coherence; [| by apply COH1]. red. eauto. } *)
    
  (*   destruct tc1 as [C I] eqn:TC1. simpl in *. *)
  (*   apply rt_unit. eexists. split. *)
  (*   { replace (tid r) with (tid w). *)
  (*     2: { symmetry. erewrite wf_rmwt; eauto. } *)
  (*     apply rt_step. apply ext_reserve_trav_step. red. splits; vauto. *)
  (*     eapply etc_coh_extend_reserved_rmw; eauto. *)
  (*     { eexists. eauto. } *)
  (*     { apply coverable_add_eq_iff; auto. *)
  (*       apply covered_in_coverable. *)
  (*       { eapply trav_step_coherence; [| by apply COH1]. red. eauto. } *)
  (*       basic_solver. } *)
  (*     apply tc_coh2etc_coh; auto. } *)
    
  (*   assert (tc_coherent G sc (mkTC (C ∪₁ eq r) I)) as COH'. *)
  (*   { eapply trav_step_coherence; [| by apply COH1]. red. eauto. } *)
  (*   assert (tc_coherent G sc (mkTC (C ∪₁ eq r) (I ∪₁ eq w))) as COH''. *)
  (*   { eapply trav_step_coherence; [| by apply COH']. red. eauto. } *)
    
  (*   forward eapply (@reserved_rewrite_helper [C ∪₁ eq r # I # I ∪₁ eq w]) as RES_ALT; auto.  *)
  (*   { eapply etc_coh_extend_reserved_rmw; eauto. *)
  (*     { exists r. basic_solver. } *)
  (*     { apply covered_in_coverable; vauto. } *)
  (*     simpl. apply tc_coh2etc_coh; auto. } *)
  (*   { basic_solver. } *)
  (*   { apply issuable_add_eq_iff; auto. *)
  (*     apply issued_in_issuable; vauto. } *)
    
  (*   simpl. forward eapply ext_rel_rmw_step *)
  (*     with (T := [C # I # I ∪₁ eq w]) (sc := sc) as RMWSTEP; eauto. *)
  (*   { unfold ecovered, eissued; simpl.  *)
  (*     eapply eis_add_res_rmw; eauto. *)
  (*     { basic_solver. } *)
  (*     apply itrav_step2ext_itrav_step_cover; auto. } *)
  (*   { replace (reserved [C # I # I ∪₁ eq w]) with (reserved [C ∪₁ eq r# I # I ∪₁ eq w]) by vauto. *)
  (*     replace (dom_sb_S_rfrmw G [C # I # I ∪₁ eq w]) with (dom_sb_S_rfrmw G [C ∪₁ eq r# I # I ∪₁ eq w]) by vauto.       *)
  (*     rewrite RES_ALT.  *)
      
  (*     unfold ecovered, eissued; simpl. *)
  (*     red. splits. *)
  (*     2: { apply tc_coh2etc_coh; auto. } *)
  (*     right. left. *)
  (*     rewrite RES_ALT.  *)
  (*     unfold ecovered, eissued; simpl. splits; vauto. }     *)
  (*   { rewrite RES_ALT. unfold ecovered, eissued; simpl. *)
  (*     apply itrav_step2ext_itrav_step_cover; auto. } *)
    
  (*   rewrite RES_ALT in RMWSTEP. auto.  *)
  (* Qed.   *)
  (* Admitted. *)
  
  (* (* TODO: get rid of FRELACQ *) *)
  (* Lemma sim_trav_step2ext_sim_trav_step (tc1 tc2: trav_config) *)
  (*       (COH1: tc_coherent G sc tc1) *)
  (*       (STEP: sim_trav_step G sc tc1 tc2) *)
  (*       (w_ex_is_xacq : W_ex G ⊆₁ W_ex G ∩₁ is_xacq (lab G)): *)
  (*   (ext_sim_trav_step G sc)^* (mkETC tc1 (issued tc1)) (mkETC tc2 (issued tc2)). *)
  (* Proof using WF IMMCON FRELACQ. *)
  (*   red in STEP. desc.  *)
  (*   apply isim_trav_step2ext_isim_trav_step in STEP; auto. *)
  (*   induction STEP. *)
  (*   { apply rt_step. red. eauto. } *)
  (*   { apply rt_refl. } *)
  (*   eapply rt_trans; eauto.  *)
  (* Qed.  *)




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
        (* (NOPROPS: props_left (fun t => W ∩₁ set_compl (propagated_thread T t)) = 0): *)
    exists e, E e /\ ~ covered T e.
  Proof using.
    
  (*   assert (countP (set_compl (covered T)) acts_list >= *)
  (*           countP (W ∩₁ set_compl (issued T)) acts_list) as AA. *)
  (*   { apply countP_mori; auto. *)
  (*     intros x [WX NN] COV. *)
  (*     apply NN. eapply w_covered_issued; eauto. by split. } *)

  (*   assert (countP (W ∩₁ set_compl (issued  T)) acts_list >= *)
  (*           countP (W ∩₁ set_compl (reserved T)) acts_list) as BB. *)
  (*   { apply countP_mori; auto. *)
  (*     intros x [WX NN]. *)
  (*     split; auto. intros CC. apply NN. eapply rcoh_I_in_S; eauto. } *)

  (*   assert (countP (W ∩₁ set_compl (issued  T)) acts_list >= *)
  (*           props_left (fun t => W ∩₁ set_compl (propagated_thread T t))) as CC. *)
  (*   { red. etransitivity. *)
  (*     2: { eapply countP_mori; [| done]. *)
  (*          apply set_subset_inter; [apply set_subset_refl2| ]. *)
  (*          apply set_subset_compl. apply rcoh_ *)

  (*     PROP *)
                                         
  (*     apply countP_mori; auto. *)
  (*     intros x [WX NN]. *)
  (*     split; auto. intros CC. apply NN. eapply rcoh_I_in_S; eauto. } *)

  (*   unfold trav_steps_left in *. *)
  (*   assert (countP (set_compl (covered T)) acts_list > 0 \/ *)
  (*           countP (W ∩₁ set_compl (issued T)) acts_list > 0 \/ *)
  (*           countP (W ∩₁ set_compl (reserved T)) acts_list > 0 \/ *)
  (*           props_leaft *)
  (*           (fun t => W ∩₁ set_compl (propagated_thread T t)) > 0 *)
  (*          ) as YY by lia. *)
  (*   assert (countP (set_compl (covered T)) acts_list > 0) as HH. *)
  (*   { destruct YY as [|[]]; auto; try lia. } *)
  (*   clear YY. *)
  (*   unfold countP in HH. *)
  (*   assert (exists h l, filterP (set_compl (ecovered T)) acts_list = h :: l) as YY. *)
  (*   { destruct (filterP (set_compl (ecovered T)) acts_list); eauto. *)
  (*     inv HH. } *)
  (*   desc. exists h. *)
  (*   assert (In h (filterP (set_compl (ecovered T)) acts_list)) as GG. *)
  (*   { rewrite YY. red. by left. } *)
  (*   apply in_filterP_iff in GG. desf. *)
  (*   split; auto. *)
  (*   apply acts_set_findom in GG. apply GG. *)
  (* Qed. *)
  Admitted. 
    
  Lemma trav_steps_left_decrease_sim_trans T T'
        (TCOH: tls_coherent G T)
        (ICOH: iord_coherent G sc T)
        (RCOH: reserve_coherent G T)
        (STEPS : (ext_sim_trav_step G sc)⁺ T T') :
    trav_steps_left T > trav_steps_left T'.
  Proof using WF.
    induction STEPS.
    { now apply trav_steps_left_decrease_sim. }
    eapply Lt.lt_trans with (m:=trav_steps_left y); try intuition.
    apply IHSTEPS2.
    eapply ext_sim_trav_step_ct_coherence; eauto.
    all: admit. 
  Admitted. 

  Lemma sim_traversal_helper T
        (IMMCON : imm_consistent G sc)
        (TCOH: tls_coherent G T)
        (ICOH: iord_coherent G sc T)
        (RCOH: reserve_coherent G T)
        (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
        (RMWCOV : forall r w (RMW : rmw r w), covered T r <-> covered T w) :
    exists T', (ext_sim_trav_step G sc)＊ T T' /\ ((acts_set G) ⊆₁ covered T').
  Proof using WF WFSC FINDOM COMP.
    assert
      (exists T',
          (ext_sim_trav_step G sc)＊ T T' /\ trav_steps_left T' = 0).
    2: { desc. eexists. splits; eauto. apply trav_steps_left_null_cov; auto.
         eapply ext_sim_trav_step_rt_coherence; eauto.
         all: admit. }
    assert (exists n, n = trav_steps_left T) as [n NN] by eauto.
    generalize dependent T. generalize dependent n.
    set (P n :=
           forall T,
             tls_coherent G T ->
             iord_coherent G sc T ->
             reserve_coherent G T ->
             W ∩₁ Rel ∩₁ issued T ⊆₁ covered T ->
             (forall r w, rmw r w -> covered T r <-> covered T w) ->
             n = trav_steps_left T ->
             exists T', (ext_sim_trav_step G sc)＊ T T' /\ trav_steps_left T' = 0).
    assert (forall n, P n) as YY.
    2: by apply YY.
    apply nat_ind_lt. unfold P. 
    ins.
    destruct (classic (trav_steps_left T = 0)) as [EQ|NEQ].
    { eexists. splits; eauto. apply rt_refl. }
    assert (trav_steps_left T > 0) as HH by lia.
    
    
    destruct (classic (props_left (fun t => W ∩₁ set_compl (propagated_thread T t)) = 0)) as [NOPROPS | PROPS].
    2: { exists_trav_step 
    

    
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
