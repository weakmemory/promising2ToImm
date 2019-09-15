(* Require Import Program.Basics. *)
From hahn Require Import Hahn.
Require Import Setoid.
Require Import AuxRel.

Set Implicit Arguments.

Lemma dom_eqv_seq {A} a (r r' : relation A) (NE : exists b, r' a b) :
  dom_rel (r ;; <|eq a|> ) ≡₁ dom_rel (r ⨾ <|eq a|> ;; r').
Proof.
  split.
  2: { rewrite <- !seqA. apply dom_seq. }
  unfolder. ins. desf. eauto.
Qed.

Add Parametric Morphism A : (@set_union A) with signature 
  set_equiv ==> set_equiv ==> set_equiv as set_union_more.
Proof. red; unfolder; splits; ins; desf; eauto. Qed.

Add Parametric Morphism A : (@set_union A) with signature 
  set_subset ==> set_subset ==> set_subset as set_union_mori.
Proof. red; unfolder; splits; ins; desf; eauto. Qed.

Lemma codom_rel_helper {A} (r : relation A) (d : A -> Prop) (HH : codom_rel r ⊆₁ d) :
  r ≡ r ⨾ ⦗d⦘.
Proof.
  split; [|basic_solver].
  unfolder. ins. split; auto. apply HH. red. eauto.
Qed.

Lemma inter_inclusion {A : Type} (r r' : relation A) (IN : r ⊆ r') :
  r ⊆ r ∩ r'.
Proof. basic_solver. Qed.

Lemma inter_eq {A : Type} (r r' : relation A) (EQ : r ≡ r') : r ≡ r ∩ r'.
Proof. generalize EQ. basic_solver. Qed.

Lemma forall_not_or_exists {A} (s P : A -> Prop):
  (exists e, s e /\ P e) \/ (forall e, s e -> ~ P e).
Proof. apply NNPP. intros X. firstorder. Qed.

Lemma tot_ext_nat_extends2 (r : relation nat) : r⁺ ⊆ tot_ext_nat r.
Proof.
  apply inclusion_t_ind; try apply tot_ext_nat_trans.
  red; ins.
    by apply tot_ext_nat_extends.
Qed.
