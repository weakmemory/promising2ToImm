From hahn Require Import Hahn.
From imm Require Import Events.
From imm Require Import Execution.
From imm Require Import TraversalOrder.
From imm Require Import TLSCoherency.
From imm Require Import IordCoherency.
From imm Require Import SimClosure.
From imm Require Import TlsEventSets.
From imm Require Import EventsTraversalOrder.
From imm Require Import AuxDef.

Section CertT.
Variables (G: execution) (sc: relation actid) (T: trav_label -> Prop). 
Variable (thread: BinNums.positive). 

Notation "'Init'" := (fun a => is_true (is_init a)).
Notation "'E'" := (acts_set G).
Notation "'NTid_' t" := (fun x => tid x <> t) (at level 1).
Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).

Notation "'I'" := (issued T).
Notation "'C'" := (covered T).
Notation "'S'" := (reserved T).



Definition certT :=
  (T ∪₁ eq ta_cover <*> (E ∩₁ NTid_ thread)) \₁ action ↓₁ eq ta_reserve ∪₁
  eq ta_reserve <*> (issued T ∪₁ reserved T ∩₁ Tid_ thread). 

Lemma tls_cover_certT:
  certT ∩₁ action ↓₁ eq ta_cover ≡₁
  (T ∪₁ event ↓₁ (E ∩₁ NTid_ thread)) ∩₁ action ↓₁ eq ta_cover. 
Proof using. 
  unfold certT. rewrite !set_pair_alt. fold action event.
  rewrite set_minus_union_l, !set_inter_union_l.
  rewrite set_equiv_union with (t' := ∅); [| reflexivity| ].  
  2: { split; [| basic_solver]. iord_dom_solver. }
  rewrite set_union_empty_r. apply set_equiv_union.
  all: split; [basic_solver| iord_dom_solver]. 
Qed. 

Lemma covered_certT:
  covered certT ≡₁ C ∪₁ E ∩₁ NTid_ thread. 
Proof using.
  (* it's just easier to prove it separately without appealing to tls_cover_certT *)
  clear. 
  unfold certT. simplify_tls_events. basic_solver 10.
Qed. 
  
Lemma tls_issue_certT:
  certT ∩₁ action ↓₁ eq ta_issue ≡₁ T ∩₁ action ↓₁ eq ta_issue. 
Proof using. 
  unfold certT. rewrite !set_pair_alt. fold action event.
  rewrite set_minus_union_l, !set_inter_union_l.
  rewrite set_equiv_union with (t' := ∅); [rewrite set_union_empty_r| reflexivity| ].
  2: { split; [| basic_solver]. iord_dom_solver. }
  rewrite set_equiv_union with (t' := ∅); [rewrite set_union_empty_r| reflexivity| ]. 
  2: { split; [| basic_solver]. iord_dom_solver. }
  split; [basic_solver| iord_dom_solver]. 
Qed. 

Lemma issued_certT:
  issued certT ≡₁ I. 
Proof using.
  clear. 
  unfold certT. simplify_tls_events. basic_solver 10. 
Qed. 
  
Lemma reserved_certT:
  reserved certT ≡₁ issued T ∪₁ reserved T ∩₁ Tid_ thread. 
Proof using.
  clear. 
  unfold certT. simplify_tls_events.
  rewrite set_minus_absorb_l; [basic_solver| ]. 
  unfold reserved. unfolder. ins. desc. vauto.   
Qed. 

Lemma T_propagations_certT_thread t:
  certT ∩₁ action ↓₁ (eq (ta_propagate t)) ≡₁
  T ∩₁ action ↓₁ (eq (ta_propagate t)).
Proof using.
  clear. 
  unfold certT. simplify_tls_events.
  rewrite !set_pair_alt. fold action event. 
  rewrite set_minus_union_l, !set_inter_union_l.
  rewrite set_unionA, set_equiv_union with (t' := ∅). 
  2: { rewrite set_minusE, set_interA.
       rewrite set_interC with (s := set_compl _).
       rewrite set_inter_absorb_r with (s := action ↓₁ _); [reflexivity| ].
       unfolder. by intros ? <-. }
  2: { split; [| basic_solver].
       unfolder. ins; des; vauto; congruence. }
  basic_solver.
Qed.  


Lemma T_propagations_certT:
  certT ∩₁ action ↓₁ (is_ta_propagate_to_G G) ≡₁
  T ∩₁ action ↓₁ (is_ta_propagate_to_G G).
Proof using.
  unfold is_ta_propagate_to_G.
  rewrite set_map_bunion, <- !set_bunion_inter_compat_l.
  apply set_equiv_bunion; [done| ].
  ins. apply T_propagations_certT_thread. 
Qed. 

Lemma propagated_thread_certT t:
  propagated_thread certT t ≡₁ propagated_thread T t.
Proof using. 
  unfold propagated_thread. by rewrite T_propagations_certT_thread. 
Qed. 

Lemma propagated_certT: propagated G certT ≡₁ propagated G T.
Proof using.
  unfold propagated. by rewrite T_propagations_certT. 
Qed. 


Lemma certT_alt:
  certT ≡₁ T ∩₁ action ↓₁ (eq ta_cover ∪₁ eq ta_issue ∪₁
                     is_ta_propagate) ∪₁
    (eq ta_reserve <*> (I ∪₁ S ∩₁ Tid_ thread)) ∪₁
    ((eq ta_cover) <*> (E ∩₁ NTid_ thread)). 
Proof using.
  clear. 
  unfold certT. rewrite !set_pair_alt. apply AuxRel.set_equiv_exp_equiv.
  unfolder. intros [t a]. split; ins; des; destruct t; ins; splits. 
  all: try (by vauto || tauto).
  all: try by (repeat left; vauto). 
  { left. right. vauto. }
  right. vauto.
Qed.  

End CertT. 
