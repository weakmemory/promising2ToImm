From hahn Require Import Hahn.
From imm Require Import CertCOhelper. 
From imm Require Import Events.
Require Import AuxRel.

(* TODO: move the whole file contents to CombRelations in CertCOhelper *)

Add Parametric Morphism : col0 with signature
    eq ==> (@set_subset actid) ==> (@set_subset actid) ==> eq ==>
       (@inclusion actid) as col0_mori.
Proof using.
  ins. unfold col0. rewrite H, H0. basic_solver. 
Qed. 

Add Parametric Morphism : col0 with signature
    eq ==> (@set_equiv actid) ==> (@set_equiv actid) ==> eq ==>
       (@same_relation actid) as col0_more.
Proof using.
  ins. destruct H, H0. 
  split; apply col0_mori; basic_solver. 
Qed.
  
Add Parametric Morphism : new_co with signature
    eq ==> (@set_equiv actid) ==> (@set_equiv actid) ==>
       (@inclusion actid) as new_co_more_impl.
Proof using.
  ins. unfold new_co, new_col.
  unfolder. ins. desc. red in H1.
  destruct H, H0.
  exists l. des.
  { left. eapply col0_mori; eauto. }
  apply pref_union_alt.
  right. split.
  { splits; vauto.
    { by apply H. }
    intro. apply H6. basic_solver. }
  intro. apply H4. eapply col0_mori; eauto. 
Qed.  

Add Parametric Morphism : new_co with signature
    eq ==> (@set_equiv actid) ==> (@set_equiv actid) ==>
       (@same_relation actid) as new_co_more.
Proof using.
  ins. split; [| symmetry in H, H0]; eapply new_co_more_impl; eauto.
Qed. 

