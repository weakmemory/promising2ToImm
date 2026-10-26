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

(** * From a certification state to a full cover with steps of one thread *)

Section CertTraversal.

Variable G : execution.
Variable sc : relation actid.
Hypothesis WF : Wf G.
Hypothesis WFSC : wf_sc G sc.
Hypothesis IMMCON : imm_consistent G sc.
Hypothesis FRELACQ : (acts_set G) ∩₁ (fun a => is_true (is_f (lab G) a))
                     ⊆₁ (fun a => is_true (is_ra (lab G) a)).
Hypothesis W_EX_IS_XACQ : W_ex G ⊆₁ W_ex G ∩₁ is_xacq (lab G).

Variable thread : thread_id.
Variable T : trav_label -> Prop.
Hypothesis TCOH : tls_coherent G T.
Hypothesis ICOH : iord_coherent G sc T.
Hypothesis RCOH : reserve_coherent G T.
Hypothesis NCOV : (fun x => tid x <> thread) ∩₁ acts_set G ⊆₁ covered T.

(* Propagations to other threads that T doesn't contain: never needed to
   cover events, and not steps of [thread]. *)
Definition other_props : trav_label -> Prop :=
  fun l => (exists t, action l = ta_propagate t /\ t <> thread) /\ ~ T l.

Lemma other_props_propagate : other_props ⊆₁ is_propagate_label.
Proof using. intros l [[t [AA _]] _]. now exists t. Qed.

(* Keep T's reservations and drop the other threads' new propagations. *)
Definition cert_clos X := reserve_fix_clos (reserved T) X \₁ other_props.

Lemma reserve_labels_of_reserved X :
  eq ta_reserve <*> reserved X ⊆₁ X.
Proof using.
  intros [a e] [AA RR]. simpl in AA, RR. subst a.
  destruct RR as [[b e'] [[XL BB] EE]]. simpl in BB, EE. subst.
  unfolder in BB. simpl in BB. now subst.
Qed.

Lemma cert_clos_T : cert_clos T ≡₁ T.
Proof using.
  unfold cert_clos, reserve_fix_clos. split.
  { intros l [[[TL _] | RL] _]; auto. now apply reserve_labels_of_reserved. }
  intros [a e] TL. split.
  2: { intros [_ NT]. auto. }
  destruct (classic (a = ta_reserve)) as [-> | NR].
  { right. split; [easy|]. exists (ta_reserve, e). unfolder. splits; auto. }
  left. split; auto.
  all: intros AA; apply NR; now red in AA.
Qed.

Lemma T_in_cert_clos X (TX : T ⊆₁ X) : T ⊆₁ cert_clos X.
Proof using.
  intros l TL. apply cert_clos_T in TL as [TL NP]. split; auto.
  unfold reserve_fix_clos in *. destruct TL as [[TL NR] | RL]; [| now right].
  left. split; auto.
Qed.

Lemma reserved_minus A B
  (BNR : B ⊆₁ set_compl (action ↓₁ eq ta_reserve)) :
  reserved (A \₁ B) ≡₁ reserved A.
Proof using.
  unfold reserved. split; [clear; basic_solver|].
  intros e [l [[AL RL] EL]]. exists l. splits; auto. split; auto.
  split; auto. intros BL. now apply (BNR l BL).
Qed.

Lemma covered_minus A B
  (BNC : B ⊆₁ set_compl (action ↓₁ eq ta_cover)) :
  covered (A \₁ B) ≡₁ covered A.
Proof using.
  unfold covered. split; [clear; basic_solver|].
  intros e [l [[AL CL] EL]]. exists l. splits; auto. split; auto.
  split; auto. intros BL. now apply (BNC l BL).
Qed.

Lemma reserved_fix R X : reserved (reserve_fix_clos R X) ≡₁ R.
Proof using.
  unfold reserve_fix_clos. rewrite reserved_union, reserved_ta_reserve.
  arewrite (reserved (X \₁ action ↓₁ eq ta_reserve) ≡₁ ∅).
  { unfold reserved. clear. basic_solver. }
  now rewrite set_union_empty_l.
Qed.

Lemma covered_fix R X : covered (reserve_fix_clos R X) ≡₁ covered X.
Proof using.
  unfold reserve_fix_clos. rewrite covered_union, covered_ta_reserve.
  rewrite set_union_empty_r. apply covered_minus.
  intros [a e] AA BB. red in AA, BB. simpl in *. congruence.
Qed.

Lemma other_props_not_reserve : other_props ⊆₁ set_compl (action ↓₁ eq ta_reserve).
Proof using. intros [a e] [[t [AA _]] _] BB. red in BB. simpl in *. congruence. Qed.

Lemma other_props_not_cover : other_props ⊆₁ set_compl (action ↓₁ eq ta_cover).
Proof using. intros [a e] [[t [AA _]] _] BB. red in BB. simpl in *. congruence. Qed.

Lemma reserved_cert_clos X : reserved (cert_clos X) ≡₁ reserved T.
Proof using.
  unfold cert_clos. rewrite reserved_minus; [apply reserved_fix|].
  apply other_props_not_reserve.
Qed.

Lemma covered_cert_clos X : covered (cert_clos X) ≡₁ covered X.
Proof using.
  unfold cert_clos. rewrite covered_minus; [apply covered_fix|].
  apply other_props_not_cover.
Qed.

Lemma init_in_cert_clos X (TX : T ⊆₁ X) : init_tls G ⊆₁ cert_clos X.
Proof using TCOH.
  rewrite <- T_in_cert_clos; auto. apply TCOH.
Qed.

Lemma cert_clos_tls_coherent X (TX : T ⊆₁ X) (TCOHX : tls_coherent G X) :
  tls_coherent G (cert_clos X).
Proof using TCOH.
  constructor; [now apply init_in_cert_clos|].
  unfold cert_clos, reserve_fix_clos.
  rewrite set_minus_union_l. apply set_subset_union_l. split.
  { transitivity X; [clear; basic_solver | apply TCOHX]. }
  transitivity T; [| apply TCOH].
  rewrite reserve_labels_of_reserved. clear. basic_solver.
Qed.

Lemma cert_clos_sim_coherent X (SCOH : sim_coherent G X) :
  sim_coherent G (cert_clos X).
Proof using.
  apply sim_coherent_minus_props; [apply other_props_propagate|].
  now apply reserve_fix_clos_sim_coherent.
Qed.

(* The first label of a translated step belongs to [thread]. *)
Lemma cert_clos_step_thread l X Y
  (TX : T ⊆₁ X)
  (TCOHY : tls_coherent G Y)
  (NX : ~ cert_clos X l)
  (YL : cert_clos Y l) :
  thread = ta_label2thread l.
Proof using WF TCOH ICOH NCOV.
  assert (NT : ~ T l) by (intros TL; apply NX, T_in_cert_clos; auto).
  destruct YL as [YL NP].
  destruct l as [a e]. destruct a as [| | t |]; simpl.
  4: { exfalso. destruct YL as [[_ NR] | [_ RT]]; [apply NR; now red|].
       apply NT. apply reserve_labels_of_reserved. split; auto. }
  3: { destruct (classic (t = thread)) as [EQ|NEQ]; auto.
       exfalso. apply NP. split; auto. exists t. auto. }
  all: destruct YL as [[YL _] | [RA _]]; [| now inv RA].
  all: assert (EE : acts_set G e).
  1,3: apply (tls_coh_exec TCOHY) in YL;
       destruct YL as [II|EX];
       [ destruct II as [_ [II _]]; auto
       | unfold exec_tls, set_pair in EX; unfolder in EX; desf ].
  all: destruct (classic (tid e = thread)) as [EQ|NEQ]; auto.
  all: exfalso; apply NT.
  all: assert (CT : covered T e) by (apply NCOV; split; auto).
  { destruct CT as [[b e'] [[TY BB] EV]]. simpl in *. subst.
    unfolder in BB. simpl in BB. now subst. }
  assert (WE : is_w (lab G) e).
  { apply (tls_coh_exec TCOHY) in YL.
    destruct YL as [II|EX].
    { destruct II as [_ [_ II]]. now apply init_w. }
    unfold exec_tls, set_pair in EX. unfolder in EX. desf. }
  assert (IT : issued T e) by (eapply w_covered_issued; eauto; split; auto).
  destruct IT as [[b e'] [[TY BB] EV]]. simpl in *. subst.
  unfolder in BB. simpl in BB. now subst.
Qed.

Lemma sim_clos_step2ext_cert X Y
  (TX : T ⊆₁ X)
  (TCOHY : tls_coherent G Y)
  (STEP : sim_clos_step G sc X Y) :
  (ext_isim_trav_step G sc thread)^* (reserve_clos (cert_clos X))
                                     (reserve_clos (cert_clos Y)).
Proof using WF WFSC IMMCON FRELACQ W_EX_IS_XACQ TCOH ICOH RCOH NCOV.
  assert (XY : X ⊆₁ Y) by (eapply sim_clos_step_crt_incl; eauto using rt_step).
  destruct STEP as [[tl ISTEP] [SX SY]].
  apply reserve_fix_clos_isim_clos_step with (R := reserved T) in ISTEP.
  destruct ISTEP as [EQ | ISTEP].
  { unfold cert_clos. rewrite EQ. apply rt_refl. }
  apply isim_clos_step_minus_props with (P := other_props) in ISTEP;
    [| apply other_props_propagate].
  destruct ISTEP as [EQ | ISTEP].
  { apply set_extensionality in EQ. unfold cert_clos. rewrite EQ. apply rt_refl. }
  fold (cert_clos X) (cert_clos Y) in ISTEP.
  eapply isim_clos_step2ext_isim_trav_step_rt_gen with (T0 := T); eauto.
  { now apply init_in_cert_clos. }
  { now apply T_in_cert_clos. }
  { now rewrite reserved_cert_clos. }
  { apply cert_clos_tls_coherent; auto. now rewrite TX. }
  { now apply cert_clos_sim_coherent. }
  { now apply cert_clos_sim_coherent. }
  destruct (@isim_clos_step_head G sc _ _ _ ISTEP) as [l [tl' [-> [NX YL]]]].
  red. eapply cert_clos_step_thread; eauto.
Qed.

End CertTraversal.
