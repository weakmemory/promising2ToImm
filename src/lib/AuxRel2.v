(* Require Import Program.Basics. *)
Require Import Omega.
From hahn Require Import Hahn.
Require Import Setoid.
Require Import AuxRel.
From Promising2 Require Import Time.

Set Implicit Arguments.

Lemma time_lt_bot a : ~ Time.lt a Time.bot.
Proof using.
  intros H.
  destruct (classic (a = Time.bot)) as [|NEQ]; subst.
  all: eapply Time.lt_strorder; etransitivity; eauto.
  assert (Time.le Time.bot a) as HH by apply Time.bot_spec.
  apply Time.le_lteq in HH; destruct HH as [HH|HH]; desf.
Qed.

Lemma dom_eqv_seq {A} a (r r' : relation A) (NE : exists b, r' a b) :
  dom_rel (r ⨾ ⦗eq a⦘ ) ≡₁ dom_rel (r ⨾ ⦗eq a⦘ ⨾ r').
Proof using.
  split.
  2: { rewrite <- !seqA. apply dom_seq. }
  unfolder. ins. desf. eauto.
Qed.

Add Parametric Morphism A : (@set_union A) with signature 
  set_equiv ==> set_equiv ==> set_equiv as set_union_more.
Proof using. red; unfolder; splits; ins; desf; eauto. Qed.

Add Parametric Morphism A : (@set_union A) with signature 
  set_subset ==> set_subset ==> set_subset as set_union_mori.
Proof using. red; unfolder; splits; ins; desf; eauto. Qed.

Lemma codom_rel_helper {A} (r : relation A) (d : A -> Prop) (HH : codom_rel r ⊆₁ d) :
  r ≡ r ⨾ ⦗d⦘.
Proof using.
  split; [|basic_solver].
  unfolder. ins. split; auto. apply HH. red. eauto.
Qed.

Lemma inter_inclusion {A : Type} (r r' : relation A) (IN : r ⊆ r') :
  r ⊆ r ∩ r'.
Proof using. basic_solver. Qed.

Lemma inter_eq {A : Type} (r r' : relation A) (EQ : r ≡ r') : r ≡ r ∩ r'.
Proof using. generalize EQ. basic_solver. Qed.

Lemma forall_not_or_exists {A} (s P : A -> Prop):
  (exists e, s e /\ P e) \/ (forall e, s e -> ~ P e).
Proof using. apply NNPP. intros X. firstorder. Qed.

Lemma tot_ext_nat_extends2 (r : relation nat) : r⁺ ⊆ tot_ext_nat r.
Proof using.
  apply inclusion_t_ind; try apply tot_ext_nat_trans.
  red; ins.
    by apply tot_ext_nat_extends.
Qed.

Lemma pair_app :
  forall (A B : Prop), A -> (A -> A /\ B) -> A /\ B.
Proof using. ins. intuition. Qed.

Theorem nat_ind_lt (P : nat -> Prop)
        (HPi : forall n, (forall m, m < n -> P m) -> P n) :
  forall n, P n.
Proof using.
  set (Q n := forall m, m <= n -> P m).
  assert (forall n, Q n) as HH.
  2: { ins. apply (HH n). omega. }
  ins. induction n.
  { unfold Q. ins. inv H. apply HPi. ins. inv H0. }
  unfold Q in *. ins.
  apply le_lt_eq_dec in H.
  destruct H as [Hl | Heq].
  { unfold lt in Hl. apply le_S_n in Hl. by apply IHn. }
  rewrite Heq. apply HPi. ins.
  apply le_S_n in H. by apply IHn.
Qed.

Lemma immediate_inter_mori {A} (x y : relation A) (IN : y ⊆ x) :
  y ∩ (immediate x) ⊆ immediate y.
Proof using.
  intros e e' [HH BB].
  split; auto.
  ins. eapply BB; apply IN; eauto.
Qed.

Lemma seq_codom_dom_inter_iff {A} (r r' : relation A) :
  codom_rel r ∩₁ dom_rel r' ≡₁ ∅ <-> r ⨾ r' ≡ ∅₂.
Proof using.
  ins. split.
  { by apply seq_codom_dom_inter. }
  intros AA.
  split; [|basic_solver].
  unfolder. ins. desf.
  eapply AA. eexists. eauto.
Qed.

Lemma time_middle_le_lhs t t' (LT : Time.lt t t') :
  ~ Time.le (Time.middle t t') t.
Proof using.
  intros HH. eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt; eauto.
    by apply Time.middle_spec.
Qed.

Lemma time_middle_lt_lhs t t' (LT : Time.lt t t') :
  ~ Time.lt (Time.middle t t') t.
Proof using.
  intros HH. eapply time_middle_le_lhs.
  2: { apply Time.le_lteq. eby left. }
  done.
Qed.

Lemma time_middle_le_rhs t t' (LT : Time.lt t t') :
  ~ Time.le t' (Time.middle t t').
Proof using.
  intros HH. eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt; eauto.
    by apply Time.middle_spec.
Qed.

Lemma time_middle_lt_rhs t t' (LT : Time.lt t t') :
  ~ Time.lt t' (Time.middle t t').
Proof using.
  intros HH. eapply time_middle_le_rhs.
  2: { apply Time.le_lteq. eby left. }
  done.
Qed.
