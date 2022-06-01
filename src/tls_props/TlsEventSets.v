From hahn Require Import Hahn.
From imm Require Import TraversalOrder.
From imm Require Import TLSCoherency.
From imm Require Import IordCoherency.
From imm Require Import Events.
From imm Require Import Execution.
Require Import AuxRel.
From imm Require Import AuxDef.
From imm Require Import imm_s.


Definition covered  TLS := event ↑₁ (TLS ∩₁ action ↓₁ (eq ta_cover)).
Definition issued   TLS := event ↑₁ (TLS ∩₁ action ↓₁ (eq ta_issue)).
Definition reserved TLS := event ↑₁ (TLS ∩₁ action ↓₁ (eq ta_reserve)).
Definition propagated G TLS :=
  event ↑₁ (TLS ∩₁ (action ↓₁ is_ta_propagate_to_G G)). 


Definition coverable G sc T :=
  acts_set G ∩₁ event ↑₁ (dom_cond (iord G sc) T ∩₁ action ↓₁ eq ta_cover). 
Definition issuable G sc T :=
  acts_set G ∩₁ (is_w (lab G)) ∩₁ event ↑₁ (dom_cond (iord G sc) T ∩₁ action ↓₁ eq ta_issue). 


Section MorphismsCIRP.

Local Ltac cirp_morph :=
  intros x y HH; unfold covered, issued, reserved, propagated;
  solve [now rewrite HH|now rewrite <- HH].

Global Add Parametric Morphism : covered with signature
    (@set_subset trav_label) ==> (@set_subset actid)
       as covered_mori.
Proof using. cirp_morph. Qed.

Global Add Parametric Morphism : issued with signature
    (@set_subset trav_label) ==> (@set_subset actid)
       as issued_mori.
Proof using. cirp_morph. Qed.

Global Add Parametric Morphism : reserved with signature
    (@set_subset trav_label) ==> (@set_subset actid)
       as reserved_mori.
Proof using. cirp_morph. Qed.

Global Add Parametric Morphism : propagated with signature
    eq ==> (@set_subset trav_label) ==> (@set_subset actid)
       as propagated_mori.
Proof using. intros G. cirp_morph. Qed. 

Global Add Parametric Morphism : covered with signature
    (@set_equiv trav_label) ==> (@set_equiv actid)
       as covered_more.
Proof using. cirp_morph. Qed.

Global Add Parametric Morphism : issued with signature
    (@set_equiv trav_label) ==> (@set_equiv actid)
       as issued_more.
Proof using. cirp_morph. Qed. 

Global Add Parametric Morphism : reserved with signature
    (@set_equiv trav_label) ==> (@set_equiv actid)
       as reserved_more.
Proof using. cirp_morph. Qed. 

Global Add Parametric Morphism : propagated with signature
    eq ==> (@set_equiv trav_label) ==> (@set_equiv actid)
       as propagated_more.
Proof using. intros G. cirp_morph. Qed. 

End MorphismsCIRP. 

Section SimplificationsCIRP. 

Lemma covered_events (A: actid -> Prop):
  covered (event ↓₁ A) ⊆₁ A. 
Proof using. unfold covered. basic_solver. Qed. 

Lemma issued_events (A: actid -> Prop):
  issued (event ↓₁ A) ⊆₁ A. 
Proof using. unfold issued. basic_solver. Qed. 

Lemma reserved_events (A: actid -> Prop):
  reserved (event ↓₁ A) ⊆₁ A. 
Proof using. unfold reserved. basic_solver. Qed. 

Lemma propagated_events G (A: actid -> Prop):
  propagated G (event ↓₁ A) ⊆₁ A. 
Proof using. unfold propagated. basic_solver. Qed. 

Lemma covered_union T1 T2:
  covered (T1 ∪₁ T2) ≡₁ covered T1 ∪₁ covered T2. 
Proof using. unfold covered. basic_solver 10. Qed. 

Lemma issued_union T1 T2:
  issued (T1 ∪₁ T2) ≡₁ issued T1 ∪₁ issued T2. 
Proof using. unfold issued. basic_solver 10. Qed. 

Lemma reserved_union T1 T2:
  reserved (T1 ∪₁ T2) ≡₁ reserved T1 ∪₁ reserved T2. 
Proof using. unfold reserved. basic_solver 10. Qed. 

Lemma propagated_union G T1 T2:
  propagated G (T1 ∪₁ T2) ≡₁ propagated G T1 ∪₁ propagated G T2. 
Proof using. unfold propagated. basic_solver 10. Qed. 

Lemma covered_singleton e:
  covered (eq (mkTL ta_cover e)) ≡₁ eq e.
Proof using. unfold covered. split; basic_solver. Qed. 

Lemma issued_singleton e:
  issued (eq (mkTL ta_issue e)) ≡₁ eq e.
Proof using. unfold issued. split; basic_solver. Qed. 

Lemma reserved_singleton e:
  reserved (eq (mkTL ta_reserve e)) ≡₁ eq e.
Proof using. unfold reserved. split; basic_solver. Qed. 

(* TODO: find the correct statement and premises *)
(* Lemma propagated_singleton G t e : *)
(*   propagated G (eq (mkTL (ta_propagate t) e)) ≡₁ eq e. *)

Lemma covered_noncover_empty S
      (NONCOVER: set_disjoint S (action ↓₁ eq ta_cover)):
  covered S ≡₁ ∅.
Proof using. unfold covered. split; basic_solver. Qed. 

Lemma issued_nonissue_empty S
      (NONISSUE: set_disjoint S (action ↓₁ eq ta_issue)):
  issued S ≡₁ ∅.
Proof using. unfold issued. split; basic_solver. Qed. 

Lemma reserved_nonreserve_empty S
      (NONISSUE: set_disjoint S (action ↓₁ eq ta_reserve)):
  reserved S ≡₁ ∅.
Proof using. unfold reserved. split; basic_solver. Qed. 

Lemma covered_only_cover M
      (COV: M ⊆₁ action ↓₁ eq ta_cover):
  covered M ≡₁ event ↑₁ M. 
Proof using. 
  unfold covered. split; [basic_solver| ].
  apply set_collect_mori; auto. generalize COV. basic_solver. 
Qed. 

Lemma issued_only_issue M
      (ISS: M ⊆₁ action ↓₁ eq ta_issue):
  issued M ≡₁ event ↑₁ M. 
Proof using. 
  unfold issued. split; [basic_solver| ].
  apply set_collect_mori; auto. generalize ISS. basic_solver. 
Qed. 

Lemma reserved_only_reserve M
      (RES: M ⊆₁ action ↓₁ eq ta_reserve):
  reserved M ≡₁ event ↑₁ M. 
Proof using. 
  unfold reserved. split; [basic_solver| ].
  apply set_collect_mori; auto. generalize RES. basic_solver. 
Qed. 

(* TODO: move to TraversalOrder *)
Lemma set_pair_cancel_action a B:
    event ↑₁ (eq a <*> B) ≡₁ B. 
Proof using. 
  rewrite set_pair_alt. split; try basic_solver.
  intros b Bb. exists (mkTL a b). vauto. 
Qed.   

(* TODO: move to TraversalOrder *)
Lemma set_pair_exact a e:
  eq a <*> eq e ≡₁ eq (mkTL a e). 
Proof using. 
  unfold set_pair. split; try basic_solver.
  intros [? ?] [-> ->]. auto. 
Qed. 

End SimplificationsCIRP. 


(* The idea for these tactics is to try simplifying all appropriate terms once *)
(* TODO: is there a better way to do this? *)
Ltac remember_tls_sets :=
  repeat (match goal with
          |  |- context [ (covered ?S) ] => remember (@covered S) eqn:?HeqS
          |  |- context [ (issued ?S) ] => remember (@issued S) eqn:?HeqS
          |  |- context [ (reserved ?S) ] => remember (@reserved S) eqn:?HeqS
          end).

Ltac subst_tls_sets_simpl :=
  repeat (match goal with
          | H: ?E = covered ?S |- _ => subst E; try (rewrite covered_noncover_empty; [| basic_solver 10])
          | H: ?E = issued ?S |- _ => subst E; try (rewrite issued_nonissue_empty; [| basic_solver 10])
          | H: ?E = reserved ?S |- _ => subst E; try (rewrite reserved_nonreserve_empty; [| basic_solver 10])
            end
         ).

Ltac simplify_tls_events :=
  (repeat rewrite ?covered_union, ?issued_union, ?reserved_union);
  (repeat rewrite ?covered_singleton, ?issued_singleton, ?reserved_singleton);
  remember_tls_sets; subst_tls_sets_simpl. 


Section WfSets.
  Context (G: execution) (sc: relation actid) (WF: Wf G). 
  Context
    (T : trav_label -> Prop)
    (TLSCOH  : tls_coherent G T)
    (IORDCOH : iord_coherent G sc T).
  
  Notation "'E'" := (acts_set G).
  Notation "'W'" := (fun x => is_true (is_w (lab G) x)).

  Lemma issuedW :
    issued T ⊆₁ W.
  Proof using WF TLSCOH. 
    unfold issued. rewrite tlsc_I_in_W; eauto. basic_solver.  
  Qed. 

  Lemma propagatedW : propagated G T ⊆₁ W.
  Proof using WF TLSCOH.
    clear -WF TLSCOH.
    unfold propagated.
    unfolder. ins. desf.
    unfold is_ta_propagate_to_G in *.
    unfolder in *. desf.
    eapply tlsc_P_in_W; eauto.
    basic_solver.
  Qed. 

  Lemma issuedE :
    issued T ⊆₁ E.
  Proof using WF TLSCOH.
    unfold issued. rewrite (tlsc_E WF TLSCOH). basic_solver.  
  Qed. 

  Lemma coveredE:
    covered T ⊆₁ E.
  Proof using WF TLSCOH.
    unfold covered. rewrite (tlsc_E WF TLSCOH). basic_solver.
  Qed. 

  Lemma w_covered_issued :
    W ∩₁ covered T ⊆₁ issued T.
  Proof using TLSCOH IORDCOH.
    unfold covered.
    unfolder. ins. desc.
    forward eapply tlsc_w_covered_issued with (x := mkTL ta_cover x); eauto.
    destruct y; ins; vauto. 
  Qed.

  Lemma init_issued : is_init ∩₁ E ⊆₁ issued T.
  Proof using TLSCOH.
    unfolder; ins; desf. red.
    exists (mkTL ta_issue x). repeat split; auto. 
    destruct TLSCOH. apply tls_coh_init. red. split; basic_solver. 
  Qed. 

  Lemma init_covered : is_init ∩₁ E ⊆₁ covered T.
  Proof using TLSCOH. 
    unfolder; ins; desf. red.
    exists (mkTL ta_cover x). repeat split; auto. 
    destruct TLSCOH. apply tls_coh_init. red. split; basic_solver. 
  Qed.

  Lemma covered_in_coverable: 
    covered T ⊆₁ coverable G sc T.
  Proof using WF TLSCOH IORDCOH. 
    unfold covered, coverable. apply set_subset_inter_r. split; [apply coveredE|].
    apply set_collect_mori; [done| ]. apply set_subset_inter; [| done].
    by apply dom_rel_to_cond.
  Qed.

  Lemma issued_in_issuable:
    issued T ⊆₁ issuable G sc T.
  Proof using WF TLSCOH IORDCOH. 
    unfold issued, issuable. repeat (apply set_subset_inter_r; split); auto using issuedE, issuedW. 
    apply set_collect_mori; [done| ]. apply set_subset_inter; [| done].
    by apply dom_rel_to_cond.
  Qed.

  Lemma issuableE:
    issuable G sc T ⊆₁ acts_set G. 
  Proof using. unfold issuable. basic_solver. Qed. 
  
  Lemma issuableW:
    issuable G sc T ⊆₁ is_w (lab G).
  Proof using. unfold issuable. basic_solver. Qed. 

  Lemma w_coverable_issued :
    W ∩₁ coverable G sc T ⊆₁ issued T.
  Proof using TLSCOH.
    rewrite AuxRel2.set_split_complete with (s' := _ ∩₁ _) (s := is_init).
    apply set_subset_union_l. split.
    { rewrite <- init_issued. unfold coverable. basic_solver. } 
    rewrite <- dom_eqv with (d := _ ∩₁ _). rewrite id_inter, seq_eqvC. 
    unfold coverable, issued. rewrite !id_inter, <- !seqA. 
    eapply dom_rel_iord_ext_parts.
    3: by apply init_issued.
    2: basic_solver. 
    transitivity (RF G); [| unfold iord_simpl; basic_solver 10].
    unfold RF. hahn_frame. basic_solver 10. 
  Qed.

End WfSets. 

(* TODO: move to IordCoherency in IMM *)
Lemma iord_coherent_extend G sc T lbl
      (ICOH: iord_coherent G sc T)
      (ADD: dom_cond (iord G sc) T lbl):
  iord_coherent G sc (T ∪₁ eq lbl). 
Proof using. 
  red. rewrite id_union, seq_union_r, dom_union.
  red in ICOH, ADD. rewrite ICOH, ADD. basic_solver. 
Qed.

(* TODO: move to IordCoherency in IMM *)
Lemma iord_coherent_element_prefix G sc (T: trav_label -> Prop) (lbl: trav_label)
      (Tlbl: T lbl)
      (ICOH: iord_coherent G sc T)
      (IMMCON: imm_consistent G sc)
      (WF: Wf G):
  dom_rel (iord G sc ⨾ ⦗eq lbl⦘) ⊆₁ T \₁ eq lbl.
Proof using.
  rewrite set_minusE. apply set_subset_inter_r. split.
  { etransitivity; [| apply ICOH]. basic_solver. }
  intros x [y [REL ->]%seq_eqv_r]. intros ->.  
  edestruct iord_irreflexive; eauto; apply IMMCON.
Qed.
