Require Import Classical Peano_dec Setoid PeanoNat.
From hahn Require Import Hahn.
Require Import Lia.

From imm Require Import Events.
From imm Require Import Execution.
(* Require Import imm_bob. *)
From imm Require Import imm_s.
(* Require Import imm_s_ppo. *)
(* Require Import imm_s_rfppo. *)
From imm Require Import TraversalConfig.
From imm Require Import Traversal.
From imm Require Import TraversalConfigAlt.
From imm Require Import SetSize.
From imm Require Import FairExecution.
Require Import ExtTraversalConfig.
Require Import ExtTraversal.
Require Import ExtSimTraversal.
Require Import ExtSimTraversalProperties.
Import ListNotations.
From imm Require Import IordTraversal.
Require Import IndefiniteDescription.
Require Import ListSum.
Require Import Coq.Program.Basics.

(* taken from 'relive' project *)
(* TODO: move a lot of stuff from here *)
Section FunTrace.
  Variable (A: Type).
  Hypothesis (INH: inhabited A). 
  
  Definition fun_trace_equiv (f: nat -> A) (tr: trace A) (size: nat_omega) :=
    ⟪SIZE: trace_length tr = size ⟫ /\
    ⟪F_TR_EQ: (forall d i (DOM: NOmega.lt_nat_l i size), trace_nth i tr d = f i) ⟫.
  
  
  Lemma trace_of_fun (f: nat -> A) (size: nat_omega):
    exists tr, fun_trace_equiv f tr size. 
  Proof.
    unfold fun_trace_equiv. 
    destruct size.
    { by exists (trace_inf f). }
    exists (trace_fin (map f (List.seq 0 n))). split.
    { simpls. red. f_equal. rewrite map_length. apply seq_length. }
    red. ins. rewrite <- mk_listE. rewrite nth_mk_list.
    destruct (Compare_dec.le_lt_dec n i); auto. lia.
  Qed.
  
  Lemma fun_of_trace (tr: trace A):
    exists f, fun_trace_equiv f tr (trace_length tr). 
  Proof.
    unfold fun_trace_equiv. 
    destruct tr; simpl; eauto.
    inversion INH as [a]. 
    exists (fun i => nth i l a). splits; ins; auto.
    by apply nth_indep. 
  Qed.

  Lemma equiv_trace_elems (f: nat -> A) (tr: trace A) (size: nat_omega)
        (EQUIV: fun_trace_equiv f tr size):
    trace_elems tr ≡₁ ⋃₁ i ∈ (flip NOmega.lt_nat_l size), eq (f i).
  Proof.
    inversion INH as [d]. cdes EQUIV.
    rewrite trace_elems_nth with (d := d).
    apply set_equiv_bunion.
    { by rewrite SIZE. }
    ins. rewrite F_TR_EQ; auto. congruence. 
  Qed. 

  Lemma equiv_trace_nodup_enum (f: nat -> A) (tr: trace A) (S: A -> Prop)
        (EQUIV: fun_trace_equiv f tr (set_size S))
        (ENUM: enumerates f S):
    trace_nodup tr.
  Proof.
    red. ins. intros EQ.
    cdes EQUIV. rewrite SIZE in *. 
    rewrite !F_TR_EQ in EQ; eauto using NOmega.lt_lt_nat. 
    apply enumeratesE' in ENUM. desc.
    apply INJ in EQ; eauto using NOmega.lt_lt_nat.
    lia.     
  Qed. 

End FunTrace.

(* TODO: move to another place *)
Lemma trace_nodup_list {A: Type} (l: list A):
  NoDup l <-> trace_nodup (trace_fin l).
Proof.
  destruct (classic (inhabited A)).
  2: { destruct l; [| by destruct H]. 
       split; ins. red. ins. lia. }
  destruct H as [a]. 
  split. 
  { intros ND. red. ins. red. ins. apply NoDup_nth in H; auto; lia. }
  { ins. apply NoDup_nth with (d := a). ins.
    red in H. simpl in H.
    pose proof (Nat.lt_trichotomy i j). des; auto.
    all: specialize H with (d := a); specialize_full H; eauto; congruence. }
Qed.

(* TODO: move to another place *)
Lemma trace_nodup_size {A: Type} (tr: trace A) (ND: trace_nodup tr):
  trace_length tr = set_size (trace_elems tr).
Proof.
  destruct tr.
  { simpl. apply trace_nodup_list in ND.
    unfold set_size. destruct (excluded_middle_informative _).
    2: { destruct n. vauto. }
    f_equal. destruct (constructive_indefinite_description _ _). simpl in *.
    apply Permutation_length. apply NoDup_Permutation; auto.
    ins.
    symmetry. etransitivity.
    { rewrite in_undup_iff, in_filterP_iff. reflexivity. }
    intuition. }
  { simpl.
    unfold set_size. destruct (excluded_middle_informative _); auto.    
    exfalso.
    apply set_finiteE in s. desc.
    red in ND. simpl in ND.
        
    forward eapply (@list_sum_separation _ _ fl (List.seq 0 (S (length findom)))) as EQ. 
    { apply seq_NoDup. }
    { eauto. }
    { ins. apply s0. eauto. }
    forward eapply list_sum_bound with (l := (map
            (fun tn : nat =>
             length
               (filterP
                  (fun e : nat => nth_error findom tn = Some (fl e))
                  (List.seq 0 (S (length findom)))))
            (List.seq 0 (length findom)))) (k := 1).
    2: { rewrite <- EQ, map_length, !seq_length. lia. }
    intros len' H. apply in_map_iff in H as [ind [LEN IND]]. desc.
    remember (filterP (fun e : nat => nth_error findom ind = Some (fl e))
                      (List.seq 0 (S (length findom)))) as poss.
    rewrite <- LEN. do 2 (destruct poss; [vauto| ]).
    assert (In n (n :: n0 :: poss)) as IN1 by done. assert (In n0 (n :: n0 :: poss)) as IN2 by vauto.
    rewrite Heqposs in IN1, IN2. apply in_filterP_iff in IN1. apply in_filterP_iff in IN2. desc.
    pose proof (NPeano.Nat.lt_trichotomy n n0). des. 
    2: { subst n0.
         assert (NoDup (n :: n :: poss)).
         { rewrite Heqposs. apply nodup_filterP, seq_NoDup. }
         inversion H. subst. by destruct H2. }
    all: edestruct ND; eauto; congruence. }  
Qed.

Lemma enumerates_set_bunion {A: Type} (S: A -> Prop) (enum: nat -> A)
      (ENUM: enumerates enum S):
  (⋃₁i ∈ flip NOmega.lt_nat_l (set_size S), eq (enum i)) ≡₁ S.
Proof.
  apply enumeratesE' in ENUM. desc. split.
  { intros e [i [DOMi Ie]]. rewrite <- Ie. eapply INSET; eauto. }
  intros e Se. apply IND in Se as [? ?]. vauto. 
Qed.

Lemma trace_nodup_mapE' {A B} (f : A -> B) (t : trace A)
      (INJ : forall a b (NEQ : a <> b)
                    (INA : trace_elems t a)
                    (INB : trace_elems t b),
          f a <> f b)
      (NODUP : trace_nodup t) :
  trace_nodup (trace_map f t).
Proof using.
  destruct t; red; ins.
  { assert (exists al, In al l); desc.
    { destruct l as [|a]; vauto; ins. lia. }
    rewrite nth_indep with (n:=i) (d':=f al); [|lia].
    rewrite nth_indep with (n:=j) (d':=f al); auto.
    rewrite !map_nth.
    rewrite map_length in LTj.
    apply INJ.
    { by apply NODUP. }
    all: apply nth_In; lia. }
  apply INJ; eauto.
  red in NODUP; ins. apply NODUP; auto.
Qed.

Module X.
  Parameter (GG: execution).
  Lemma foo (WF: Wf GG): True.
  Proof. vauto. Qed. 
End X.



Module ExtTraversalSeq.
  Include IordTraversal.
(* Context (G : execution) (sc : relation actid). *)
Implicit Types (WF : Wf G) (COMP : complete G)
         (WFSC : wf_sc G sc) (CONS : imm_consistent G sc)
         (MF : mem_fair G).

From hahn Require Import HahnTrace.

(* Lemma trace_map_filter {A B: Type} (tr: trace A) (S: B -> Prop) (f: A -> B): *)
(*   trace_map f (trace_filter (compose S f) tr) = trace_filter S (trace_map f tr). *)
(* Proof. *)
  
Definition ev2step_index (steps_enum: nat -> TraversalOrder.TravLabel.t)
           (* (ENUM: enumerates steps_enum IordTraversal.graph_steps) *)
           (e: actid)
  : nat.
  (* destruct (excluded_middle_informative ((acts_set G \₁ is_init) e)). *)
  (* 2: { exact 0. } *)
  (* apply enumeratesE' in ENUM. desc. *)
  (* specialize (IND (mkTL TraversalOrder.TravAction.cover e)). specialize_full IND. *)
  (* { red. basic_solver. } *)
  (* apply constructive_indefinite_description in IND as [i [DOM I]]. *)
  (* exact i. *)
  destruct (excluded_middle_informative (exists i, steps_enum i = mkTL TraversalOrder.TravAction.cover e)) as [I | ?]. 
  2: { exact 0. }
  apply constructive_indefinite_description in I as [i I].
  exact i. 
Defined. 

Lemma ev2step_index_corr steps_enum
      (ENUM: enumerates steps_enum IordTraversal.graph_steps)
      (e: actid)
      (DOM: (acts_set G \₁ is_init) e):
  steps_enum (ev2step_index steps_enum e) =
  mkTL TraversalOrder.TravAction.cover e.
Proof.
  apply enumeratesE' in ENUM. desc. 
  unfold ev2step_index. destruct excluded_middle_informative as [[i I] | N].
  2: { destruct N. specialize (IND (mkTL TraversalOrder.TravAction.cover e)).
       specialize_full IND.
       { red. basic_solver. }
       desc. eauto. }
  destruct constructive_indefinite_description. congruence. 
Qed.



Lemma sim_traversal WF COMP WFSC CONS MF
      (IMM_FAIR: fsupp ar⁺):
  (* ⟪ ⟫ *)
  exists (ev_enum: nat -> actid) (tc_enum: nat -> trav_config),
    enumerates ev_enum (acts_set G \₁ is_init) /\
    (forall i (DOMi: NOmega.lt_nat_l i (set_size (acts_set G \₁ is_init))),
        covered (tc_enum i) ≡₁ (⋃₁ j < i, eq (ev_enum j)) ∪₁ E ∩₁ is_init) /\
    (forall i (DOMi: NOmega.lt_nat_l i (set_size (acts_set G \₁ is_init))),
        (trav_step G sc)^* (tc_enum (i - 1)) (tc_enum i)). 
Proof.
  (* forward eapply (trace_of_fun _ steps_enum (set_size IordTraversal.graph_steps)) as [steps_tr EQUIV'].  *)
  (* set (ev_cov_tr := trace_map event (trace_filter (IordTraversal.action ↓₁ eq TraversalOrder.TravAction.cover) steps_tr)). *)
  (* set (d := ThreadEvent tid_init 0).  *)
  (* forward eapply (fun_of_trace _ (inhabits d) ev_cov_tr) as [ev_enum EQUIV'']. *)
  (* exists ev_enum. *)

  (* set (tc_all_enum := *)
  (*        fun i => set2trav_config (trav_prefix steps_enum *)
  (*                                           (ev2step_index steps_enum (ev_enum i)))). *)
  (* exists tc_all_enum.  *)

  (* assert (trace_elems ev_cov_tr ≡₁ E \₁ is_init) as EV_COV_TR_ELEMS. *)
  (* { subst ev_cov_tr. rewrite trace_elems_map, trace_elems_filter. *)
  (*   rewrite equiv_trace_elems; eauto. *)
  (*   2: { econstructor. vauto. } *)
  (*   erewrite enumerates_set_bunion; eauto.  *)
  (*   apply enumeratesE' in ENUM. desc.  *)
  (*   unfold IordTraversal.graph_steps. *)
  (*   erewrite AuxRel.set_collect_more; [| reflexivity| ]. *)
  (*   2: { rewrite set_inter_union_l. *)
  (*        erewrite set_equiv_union; [by apply set_union_empty_r| | ]. *)
  (*        { rewrite set_interC, <- set_interA, set_interK. reflexivity. } *)
  (*        apply set_subset_empty_r. unfolder. ins. desf. congruence. } *)
  (*   split; unfolder; ins; desf.  *)
  (*   exists (mkTL TraversalOrder.TravAction.cover x). splits; auto. } *)
  
  (* remember ((set_size (E \₁ (fun a : actid => is_init a)))) as evs_size. *)
  
  (* assert (trace_nodup ev_cov_tr) as EV_COV_TR_NODUP. *)
  (* { apply trace_nodup_mapE'. *)
  (*   2: { apply trace_nodup_filter. eapply equiv_trace_nodup_enum; eauto. } *)
  (*   ins. intros EQ. destruct a as [a1 e], b as [a2 e']. simpl in *. subst e'. *)
  (*   apply trace_in_filter in INA, INB. desc. red in INA0, INB0. *)
  (*   simpl in *. congruence. } *)
  
  (* assert (trace_length ev_cov_tr = evs_size) as TR_LEN. *)
  (* { rewrite trace_nodup_size; auto.  *)
  (*   subst evs_size. apply set_size_equiv. auto. } *)

  (* splits. *)
  (* { apply enumeratesE'. simpl. cdes EQUIV''.  *)
  (*   splits. *)
  (*   { ins. rewrite <- (F_TR_EQ d i). *)
  (*     2: { congruence. } *)
  (*     apply EV_COV_TR_ELEMS. apply trace_nth_in. congruence. } *)
  (*   { ins. rewrite <- !(F_TR_EQ d) in H1; try congruence. *)
  (*     destruct (Nat.lt_trichotomy i j) as [? | [? | ?]]; auto. *)
  (*     2: symmetry in H1.  *)
  (*     all: eapply EV_COV_TR_NODUP in H1; (congruence || done). } *)
  (*   ins. apply EV_COV_TR_ELEMS, trace_in_nth with (d := d) in H as [i [DOM ITH]]. *)
  (*   exists i. split; [congruence| ]. erewrite <- F_TR_EQ; eauto. } *)

  (* { ins. split. *)
  (*   { unfolder. ins. desf; eauto. left. *)
  (*     destruct H3 as [j fff].  *)
Admitted.       
      

End ExtTraversalSeq. 
