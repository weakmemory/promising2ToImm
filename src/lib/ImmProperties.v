From hahn Require Import Hahn.
From imm Require Import Prog.
From imm Require Import ProgToExecution.
From imm Require Import Events.
From imm Require Import Execution.
From hahnExt Require Import HahnExt.

Section ImmProperties.

Variable G : execution.
Hypothesis WF : Wf G.

Lemma sb_rmw_split_disj r w rel' 
      (RMW: rmw G r w)
      (REL'_NIr: ~ codom_rel rel' r):
  rel' ⨾ sb G ⨾ ⦗eq w⦘ ⊆ rel' ⨾ sb G⨾ ⦗eq r⦘ ⨾ rmw G ⨾ ⦗eq w⦘.
Proof using WF. 
  arewrite (⦗eq w⦘ ⊆ (rmw G)⁻¹ ⨾ rmw G ⨾ ⦗eq w⦘) at 1.
  { basic_solver. }
  sin_rewrite sb_transp_rmw; auto.
  arewrite (rmw G ⨾ ⦗eq w⦘ ⊆ ⦗eq r⦘ ⨾ rmw G ⨾ ⦗eq w⦘) at 1.
  { apply doma_rewrite.
    red. ins. apply seq_eqv_r in REL as [REL <-].
    eapply wf_rmw_invf; eauto. }
  do 2 hahn_frame_r.
  rewrite crE. repeat case_union _ _. apply inclusion_union_l; [| basic_solver].
  rewrite seq_id_l. intros ? ? REL'r%seq_eqv_r. desc. subst y.
  destruct REL'_NIr. basic_solver. 
Qed. 

Lemma sb_rmw_split r w 
      (RMW: rmw G r w):
  sb G ⨾ ⦗eq w⦘ ≡ (sb G)^?⨾ ⦗eq r⦘ ⨾ rmw G ⨾ ⦗eq w⦘.
Proof using WF.
  split.
  2: { rewrite rmw_in_sb; auto. rewrite inclusion_seq_eqv_l.
       sin_rewrite rewrite_trans_seq_cr_l; [| by apply sb_trans]. reflexivity. }
  rewrite <- seq_id_l with (r := _ ⨾ _).
  rewrite set_full_split with (S := eq r), id_union. repeat case_union _ _.
  apply inclusion_union_l.
  2: { rewrite sb_rmw_split_disj; eauto; [basic_solver 10| ].
       unfolder. intros ?. desc. vauto. }
  unfolder. ins. desc. subst x y. exists r. splits; auto. 
Qed. 

End ImmProperties.
