Require Import Program.Basics.
From hahn Require Import Hahn.
From imm Require Import Execution Events SubExecution.
Require Import Lia.

(* TODO: merge with FinExecution *)

Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).

Definition fin_exec (G: execution) := set_finite (acts_set G \₁ Tid_ tid_init).


(* TODO: move to SubExecution *)
Lemma set_bunion_separation {A B: Type} (S: A -> Prop) (fab: A -> B):
  S ≡₁ ⋃₁ b, S ∩₁ (fun a => fab a = b).
Proof. basic_solver. Qed.       

Lemma events_separation G:
  acts_set G ≡₁ ⋃₁ t, acts_set (restrict G (Tid_ t)).
Proof.
  unfold restrict. simpl.
  rewrite set_bunion_inter_compat_r, set_interC, <- set_bunion_inter_compat_l.
  apply set_bunion_separation. 
Qed.

(* TODO: move to separate file *)
Definition threads_bound (G: execution) (b: thread_id) :=
  forall e (Ge: acts_set G e), BinPos.Pos.lt (tid e) b.

Lemma set_full_split {A: Type} (S: A -> Prop):
  set_full ≡₁ S ∪₁ set_compl S.
Proof.
  split; [| basic_solver]. red. ins. destruct (classic (S x)); basic_solver.
Qed. 

Lemma BinPos_lt_fin b:
  set_finite (fun t => BinPos.Pos.lt t b). 
Proof.
  exists (map BinPos.Pos.of_nat (List.seq 0 (BinPos.Pos.to_nat b))).
  ins. apply Pnat.Pos2Nat.inj_lt in IN. 
  apply in_map_iff. eexists. splits.
  { by apply Pnat.Pos2Nat.id. }
  apply in_seq. lia.
Qed. 

Lemma fin_exec_bounded_threads G b
      (TB: threads_bound G b)
      (FIN_B: forall t (NI: t <> tid_init) (LTB: BinPos.Pos.lt t b),
          fin_exec (restrict G (Tid_ t))):
  fin_exec G. 
Proof.
  red. rewrite events_separation, <- set_bunion_minus_compat_r.
  rewrite set_full_split with (S := fun t => BinPos.Pos.lt t b).
  rewrite set_bunion_union_l. apply set_finite_union. split.
  2: { exists nil. unfold restrict. simpl. unfolder. ins. desc.
       red in TB. apply TB in IN2. congruence. }
  apply set_finite_bunion; [by apply BinPos_lt_fin| ].
  intros t LT.
  destruct (classic (t = tid_init)) as [-> | NI]. 
  2: { by apply FIN_B. }
  exists nil. unfold restrict. simpl. unfolder. ins. by desc. 
Qed.

End FinExecution.  
