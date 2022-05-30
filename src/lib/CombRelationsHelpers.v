From hahn Require Import Hahn.
From imm Require Import CombRelations.
From imm Require Import Events. 

(* TODO: move the whole file to CombRelations in IMM *)

Add Parametric Morphism : c_cur with signature
    eq ==> (@same_relation actid) ==> eq ==> eq ==> (@set_equiv actid) ==>
       (@same_relation actid) as c_cur_more. 
Proof using. 
  ins. unfold c_cur, urr.
  rewrite H, H0. reflexivity. 
Qed. 
       
Add Parametric Morphism : c_acq with signature
    eq ==> (@same_relation actid) ==> eq ==> eq ==> (@set_equiv actid) ==>
       (@same_relation actid) as c_acq_more. 
Proof using. 
  ins. unfold c_acq, urr.
  rewrite H, H0. reflexivity. 
Qed. 

