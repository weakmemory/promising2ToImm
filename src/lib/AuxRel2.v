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
