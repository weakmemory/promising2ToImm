Require Import PArith Setoid.
From hahn Require Import Hahn.
Require Import PromisingLib.
From Promising2 Require Import Time.

From imm Require Import Events Execution.
From imm Require Import imm_s_hb.
From imm Require Import imm_s.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section FtoCoherent.
Variable G : execution.
Variable WF : Wf G.
Variable sc : relation actid.
Variable IMMCON : imm_consistent G sc.
Variable I : actid -> Prop.

Notation "'acts'" := G.(acts).
Notation "'co'" := G.(co).
Notation "'coi'" := G.(coi).
Notation "'sb'" := G.(sb).
Notation "'rf'" := G.(rf).
Notation "'rfe'" := G.(rfe).
Notation "'rmw'" := G.(rmw).
Notation "'lab'" := G.(lab).

Notation "'E'" := G.(acts_set).
Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'Loc_' l" := (fun x => loc lab x = Some l) (at level 1). (* , format "'Loc_'  l"). *)
Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'W_'" := (fun l => W ∩₁ Loc_ l).
(* Notation "'RW'" := (fun x => R x \/ W x). *)
Notation "'FR'" := (fun x => F x \/ R x).
Notation "'FW'" := (fun x => F x \/ W x).

Notation "'Pln'" := (fun a => is_true (is_only_pln lab a)).
Notation "'Rlx'" := (is_rlx lab).
Notation "'Rel'" := (is_rel lab).
Notation "'Acq'" := (is_acq lab).
Notation "'Acqrel'" := (is_acqrel lab).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

Notation "'W_ex'" := G.(W_ex).
Notation "'W_ex_acq'" := (W_ex ∩₁ (fun a => is_true (is_xacq lab a))).
  
Variable IE : I ⊆₁ E ∩₁ W.
Variable INITINI: is_init ∩₁ E ⊆₁ I. Variables f_to f_from : actid -> Time.t.

Definition f_to_coherent :=
  (* ⟪ NW  : forall a, ~ is_w lab a -> f_to a = tid_init ⟫ /\ *)
  ⟪ TINITTO : forall x, (is_init ∩₁ E) x -> f_to x = tid_init ⟫ /\
  ⟪ TINITFROM : forall x, (is_init ∩₁ E) x -> f_from x = tid_init ⟫ /\
  ⟪ TTOFROM : forall x,
      I x -> ~ is_init x -> Time.lt (f_from x) (f_to x) ⟫ /\
  ⟪ TCO : forall x y,
      I x -> I y ->
      co x y -> Time.le (f_to x) (f_from y) ⟫ /\
  ⟪ TRMW : forall x y,
      I x -> I y -> (rf ⨾ rmw) x y -> f_to x = f_from y ⟫
.

Section Props.

Variable FCOH : f_to_coherent.

Lemma f_to_co_mon e e' (CO : co e e') (ISS : I e) (ISS' : I e') :
  Time.lt (f_to e) (f_to e').
Proof using WF IMMCON FCOH.
  eapply TimeFacts.le_lt_lt.
  2: eapply FCOH; auto.
  { by apply FCOH. }
  apply Execution_eco.no_co_to_init in CO; auto.
  { apply seq_eqv_r in CO. desf. }
  apply coherence_sc_per_loc.
  apply IMMCON.
Qed.

Lemma f_from_co_mon e e' (NINIT : ~ is_init e) (CO : co e e') (ISS : I e) (ISS' : I e') :
  Time.lt (f_from e) (f_from e').
Proof using FCOH.
  eapply TimeFacts.lt_le_lt.
  { eapply FCOH; eauto. }
    by apply FCOH.
Qed.

Lemma f_to_coherent_strict x y z (ISSX : I x) (ISSY : I y) (ISSZ : I z)
      (COXY: co x y) (COYZ: co y z) :
  Time.lt (f_to x) (f_from z).
Proof using WF IMMCON FCOH.
  eapply TimeFacts.le_lt_lt.
  { apply FCOH.
    3: by apply COXY.
    all: eauto. }
  eapply f_from_co_mon; eauto.
  apply Execution_eco.no_co_to_init in COXY; auto.
  { apply seq_eqv_r in COXY. desf. }
  apply coherence_sc_per_loc.
  apply IMMCON.
Qed.

Lemma lt_init_ts e (EE : E e) (WW : W e) (ISS : I e) (NINIT : ~ is_init e) :
  Time.lt tid_init (f_to e).
Proof using WF IMMCON IE INITINI FCOH.
  unfold is_w in *.
  destruct e; desf.
  cdes FCOH.
  assert (E (InitEvent l)) as EL.
  { apply WF.(wf_init). eexists.
    split; eauto. unfold loc. desf. }
  assert ((is_init ∩₁ E) (InitEvent l)) as LL.
  { by split; eauto. }
  erewrite <- TINITTO; eauto.
  eapply f_to_co_mon; eauto.
  eapply init_co_w; eauto.
  { unfold is_w. desf. }
  red. unfold loc. rewrite WF.(wf_init_lab).
  desf.
Qed.

Lemma le_init_ts e (EE : E e) (WW : W e) (ISS : I e) :
  Time.le tid_init (f_to e).
Proof using WF IMMCON IE INITINI FCOH.
  unfold is_w in *.
  destruct e; desf.
  { apply Time.le_lteq. right.
    symmetry. cdes FCOH. apply TINITTO.
    split; auto. }
  apply Time.le_lteq. left.
  eapply lt_init_ts; eauto.
  unfold is_w. desf.
Qed.

Lemma le_init_ts_from e (EE : E e) (WW : W e) (ISS : I e) (NINIT : ~ is_init e) :
  Time.le tid_init (f_from e).
Proof using WF IMMCON IE INITINI FCOH.
  unfold is_w in *.
  destruct e; desf.
  cdes FCOH.
  assert (E (InitEvent l)) as EL.
  { apply WF.(wf_init). eexists.
    split; eauto. unfold loc. desf. }
  assert ((is_init ∩₁ E) (InitEvent l)) as LL.
  { by split; eauto. }
  erewrite <- TINITTO; eauto.
  apply FCOH; eauto.
  eapply init_co_w; eauto.
  { unfold is_w. desf. }
  red. unfold loc. rewrite WF.(wf_init_lab).
  desf.
Qed.

Lemma f_to_eq e e' (SAME_LOC : same_loc lab e e') (ISS : I e) (ISS' : I e')
      (FEQ : f_to e = f_to e') :
  e = e'.
Proof using WF IMMCON IE FCOH.
  assert (E e /\ E e') as [EE EE']. 
  { by split; apply IE. }
  assert (W e /\ W e') as [WE WE']. 
  { by split; apply IE. }
  destruct (classic (e = e')) as [|NEQ]; auto.
  exfalso.
  edestruct (wf_co_total WF); eauto.
  1,2: split; [split|]; eauto.
  { assert (Time.lt (f_to e) (f_to e')) as HH.
    { eapply f_to_co_mon; eauto. }
    rewrite FEQ in *.
      by apply DenseOrder.lt_strorder in HH. }
  assert (Time.lt (f_to e') (f_to e)) as HH.
  { eapply f_to_co_mon; eauto. }
  rewrite FEQ in *.
    by apply DenseOrder.lt_strorder in HH.
Qed.

Lemma f_from_eq e e' (SAME_LOC : same_loc lab e e') (ISS : I e) (ISS' : I e')
      (NINIT : ~ is_init e) (NINIT' : ~ is_init e')
      (FEQ : f_from e = f_from e') :
  e = e'.
Proof using WF IMMCON IE FCOH.
  assert (E e /\ E e') as [EE EE']. 
  { by split; apply IE. }
  assert (W e /\ W e') as [WE WE']. 
  { by split; apply IE. }
  destruct (classic (e = e')) as [|NEQ]; auto.
  exfalso.
  edestruct (wf_co_total WF); eauto.
  1,2: split; [split|]; eauto.
  { assert (Time.lt (f_from e) (f_from e')) as HH.
    { eapply f_from_co_mon; eauto. }
    rewrite FEQ in *.
      by apply DenseOrder.lt_strorder in HH. }
  assert (Time.lt (f_from e') (f_from e)) as HH.
  { eapply f_from_co_mon; eauto. }
  rewrite FEQ in *.
    by apply DenseOrder.lt_strorder in HH.
Qed.

Lemma co_S_f_to_le w w'
      (SW  : I w)
      (SW' : I w')
      (CO  : co^? w w') :
  Time.le (f_to w) (f_to w').
Proof using WF IMMCON FCOH.
  destruct CO as [|CO]; [subst; reflexivity|].
  apply Time.le_lteq; left.
  eapply f_to_co_mon; eauto.
Qed.

Lemma co_S_f_from_le w w'
      (NINIT : ~ is_init w)
      (SW  : I w)
      (SW' : I w')
      (CO  : co^? w w') :
  Time.le (f_from w) (f_from w').
Proof using WF FCOH.
  destruct CO as [|CO]; [subst; reflexivity|].
  apply Time.le_lteq; left.
  eapply f_from_co_mon; eauto.
Qed.

End Props.

End FtoCoherent.
