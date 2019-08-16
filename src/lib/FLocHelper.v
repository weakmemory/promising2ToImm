Require Import PropExtensionality.
Require Import PromisingLib.

Set Implicit Arguments.

Lemma floc_inj_eq (l1 l2 : FLoc.t) : FLoc.loc l1 = FLoc.loc l2 <-> l1 = l2.
Proof.
  destruct l1 as [l1 R1].
  destruct l2 as [l2 R2].
  simpl in *; subst.
  split; intros HH; [|inversion HH]; subst; auto.
  assert (R1 = R2); [|subst; auto].
  apply proof_irrelevance.
Qed.

Lemma floc_inj_neq (l1 l2 : FLoc.t) : FLoc.loc l1 <> FLoc.loc l2 <-> l1 <> l2.
Proof. split; intros AA BB; apply AA; apply floc_inj_eq; auto. Qed.

Lemma floc_eq_dec_eq {A} (l : FLoc.t) (a1 a2 : A) :
  (if FLoc.eq_dec l l then a1 else a2) = a1.
Proof. destruct (FLoc.eq_dec l l) as [EQ|NEQ']; intuition. Qed.

Lemma floc_eq_dec_eq_eq {A} (l1 l2 : FLoc.t) (a1 a2 : A) (EQ : l1 = l2) :
  (if FLoc.eq_dec l1 l2 then a1 else a2) = a1.
Proof. subst. destruct (FLoc.eq_dec l2 l2) as [EQ|NEQ']; intuition. Qed.

Lemma floc_eq_dec_neq {A} (l1 l2 : FLoc.t) (a1 a2 : A) (NEQ : l1 <> l2) :
  (if FLoc.eq_dec l1 l2 then a1 else a2) = a2.
Proof. destruct (FLoc.eq_dec l1 l2) as [EQ|NEQ']; intuition. Qed.

(* TODO: <> on FLoc.t should be declared as symmetric relation. *)
