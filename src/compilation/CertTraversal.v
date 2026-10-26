(** A traversal that covers the whole graph using steps of a single thread,
    starting from a certification state: proves [sim_step_cov_full_traversal]
    via the step translation of ReserveClosStep. *)

Require Import Classical Peano_dec Setoid PeanoNat.
From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution imm_s.
From imm Require Import FairExecution FinExecution FinThreads ImmFair.
From imm Require Import TraversalOrder TLSCoherency IordCoherency TlsEventSets.
From imm Require Import SimClosure ReserveClos.
Require Import ExtTraversalConfig ExtTraversal ExtSimTraversal.
Require Import ExtTraversalCounting.
Require Import ReserveClosStep.

Set Implicit Arguments.

(** * Removing propagation labels *)

Section RemovePropagations.

Variable G : execution.
Variable sc : relation actid.

Definition is_propagate_label (l : trav_label) :=
  exists t, action l = ta_propagate t.

(* Nothing has to wait for a propagation: propagation labels are never the
   source of an iord edge. *)
Lemma iord_dom_no_propagate l (PL : is_propagate_label l) :
  ~ dom_rel (iord G sc) l.
Proof using.
  intros [l' HH]. destruct PL as [t AL].
  destruct l as [a e]. simpl in AL. subst a.
  unfold iord, SB, RF, FWBOB, AR, IPROP, PROP in HH.
  unfolder in HH. desf.
Qed.

Variable P : trav_label -> Prop.
Hypothesis PPROP : P ⊆₁ is_propagate_label.

Lemma iord_coherent_minus_props X
  (ICOH : iord_coherent G sc X) :
  iord_coherent G sc (X \₁ P).
Proof using PPROP.
  red. intros l [l' HH]. apply seq_eqv_r in HH as [IORD [XL NP]].
  split.
  { apply ICOH. exists l'. apply seq_eqv_r. split; auto. }
  intros PL. eapply iord_dom_no_propagate; eauto. exists l'. eauto.
Qed.

Lemma sim_coherent_minus_props X
  (SCOH : sim_coherent G X) :
  sim_coherent G (X \₁ P).
Proof using PPROP.
  red. split; [unfold sim_clos; eauto with hahn|].
  assert (NOPROP : forall l, action l = ta_cover \/ action l = ta_issue -> ~ P l).
  { intros [a e] AA PL. apply PPROP in PL. destruct PL as [t BB].
    simpl in *. desf. }
  unfold sim_clos. apply set_subset_union_l. split.
  apply set_subset_union_l. split; [eauto with hahn|].
  all: intros [a e] HL; split.
  1,3: apply SCOH; unfold sim_clos.
  1: left; right.
  2: right.
  1,2: generalize HL; unfold rmw_clos, rel_clos, set_pair;
       rewrite ?covered_minus, ?issued_minus; unfold covered, issued;
       clear; unfolder; ins; desf; splits; eauto 10.
  all: apply NOPROP; simpl.
  all: generalize HL; unfold rmw_clos, rel_clos, set_pair; clear; unfolder; ins; desf; auto.
Qed.

Lemma iiord_step_minus_props l X1 X2
  (STEP : iiord_step G sc l X1 X2) :
  (P l /\ X1 \₁ P ≡₁ X2 \₁ P) \/
  (~ P l /\ iiord_step G sc l (X1 \₁ P) (X2 \₁ P)).
Proof using PPROP.
  destruct STEP as [ST [IA IB]]. apply seq_eqv_l in ST as [NL EQ].
  destruct (classic (P l)) as [PL|NPL].
  { left. split; auto. rewrite EQ. clear -PL.
    split; unfolder; ins; desf; eauto. }
  right. split; auto.
  split; [|split; now apply iord_coherent_minus_props].
  apply seq_eqv_l. split.
  { intros [AA _]. auto. }
  rewrite EQ. clear -NPL. split; unfolder; ins; desf; eauto.
Qed.

Lemma isim_clos_step_minus_props tl X1 X2
  (STEP : isim_clos_step G sc tl X1 X2) :
  X1 \₁ P ≡₁ X2 \₁ P \/ isim_clos_step G sc tl (X1 \₁ P) (X2 \₁ P).
Proof using PPROP.
  assert (NOPROP : forall a e, a = ta_cover \/ a = ta_issue -> ~ P (a, e)).
  { intros a e AA PL. apply PPROP in PL. destruct PL as [t BB].
    simpl in *. desf. }
  (* a cover or issue step is not removed *)
  assert (KEEP : forall a e Y1 Y2, a = ta_cover \/ a = ta_issue ->
                   iiord_step G sc (a, e) Y1 Y2 ->
                   iiord_step G sc (a, e) (Y1 \₁ P) (Y2 \₁ P)).
  { intros a e Y1 Y2 AA ST.
    destruct (iiord_step_minus_props ST) as [[PL _]|[_ BB]]; auto.
    exfalso. eapply NOPROP; eauto. }
  unfold isim_clos_step in *. desf.
  (* single-label steps *)
  all: try now (destruct (iiord_step_minus_props STEP) as [[_ EQ]|[_ BB]]; auto).
  (* multi-label steps only cover and issue *)
  all: right.
  all: destruct STEP as [AA [y [ST1 ST2]]].
  all: split; auto.
  all: exists (y \₁ P).
  all: split; [apply KEEP; auto|].
  2: { destruct ST2 as [z [ST2 ST3]].
       exists (z \₁ P). split; apply KEEP; auto. }
  all: apply KEEP; auto.
Qed.

End RemovePropagations.

Lemma isim_clos_step_head G sc tl A B
  (STEP : isim_clos_step G sc tl A B) :
  exists l tl', tl = l :: tl' /\ ~ A l /\ B l.
Proof using.
  assert (ST : forall l X Y, iiord_step G sc l X Y -> ~ X l /\ Y l).
  { intros l X Y [S [_ _]]. apply seq_eqv_l in S as [NL EQ].
    split; auto. apply EQ. now right. }
  assert (MON : forall l X Y, iiord_step G sc l X Y -> X ⊆₁ Y).
  { intros l X Y S. eapply iiord_step_incl; eauto. }
  unfold isim_clos_step in STEP. desf.
  all: eexists; eexists; split; [reflexivity|].
  all: try now apply ST.
  all: destruct STEP as [_ [y [S1 S2]]].
  all: apply ST in S1 as [N1 Y1]; split; auto.
  1,3: now apply (MON _ _ _ S2).
  destruct S2 as [z [S2 S3]].
  apply (MON _ _ _ S3), (MON _ _ _ S2), Y1.
Qed.
