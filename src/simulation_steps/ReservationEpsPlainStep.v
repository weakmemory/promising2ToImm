Require Import PArith Arith.
From hahn Require Import Hahn.
Require Import PromisingLib.
From Promising2 Require Import Configuration TView View Time Event Cell Thread Memory Local.

From imm Require Import Events.
From imm Require Import Execution.
From imm Require Import Execution_eco.
From imm Require Import imm_s.
From imm Require Import imm_s_hb.
From imm Require Import imm_common.
From imm Require Import ProgToExecution.
From imm Require Import CombRelations CombRelationsMore.
From imm Require Import AuxDef.

Require Import AuxRel.
Require Import AuxRel2.
Require Import TraversalConfig.
Require Import Traversal.
Require Import ExtTraversal.
Require Import ExtTraversalProperties.
Require Import ViewRelHelpers.
Require Import PlainStepBasic.
Require Import MemoryAux.
Require Import SimulationRel.
Require Import SimState.
Require Import SimStateHelper.
Require Import PromiseLTS.
Require Import MaxValue.
Require Import ViewRel.
Require Import SimulationPlainStepAux.
Require Import FtoCoherent.

Set Implicit Arguments.

Section ReservationEpsPlainStep.

Variable G : execution.
Variable WF : Wf G.
Variable sc : relation actid.
Variable CON : imm_consistent G sc.

Notation "'E'" := G.(acts_set).
Notation "'sb'" := G.(sb).
Notation "'rf'" := G.(rf).
Notation "'co'" := G.(co).
Notation "'rmw'" := G.(rmw).
Notation "'data'" := G.(data).
Notation "'addr'" := G.(addr).
Notation "'ctrl'" := G.(ctrl).

Notation "'fr'" := G.(fr).
Notation "'coe'" := G.(coe).
Notation "'coi'" := G.(coi).
Notation "'deps'" := G.(deps).
Notation "'rfi'" := G.(rfi).
Notation "'rfe'" := G.(rfe).
Notation "'detour'" := G.(detour).
Notation "'hb'" := G.(hb).
Notation "'sw'" := G.(sw).

Notation "'lab'" := G.(lab).
(* Notation "'loc'" := (loc lab). *)
(* Notation "'val'" := (val lab). *)
(* Notation "'mod'" := (mod lab). *)
(* Notation "'same_loc'" := (same_loc lab). *)

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'RW'" := (R ∪₁ W).
Notation "'FR'" := (F ∪₁ R).
Notation "'FW'" := (F ∪₁ W).

Notation "'Pln'" := (fun a => is_true (is_only_pln lab a)).
Notation "'Rlx'" := (fun a => is_true (is_rlx lab a)).
Notation "'Rel'" := (fun a => is_true (is_rel lab a)).
Notation "'Acq'" := (fun a => is_true (is_acq lab a)).
Notation "'Acqrel'" := (fun a => is_true (is_acqrel lab a)).
Notation "'Acq/Rel'" := (fun a => is_true (is_ra lab a)).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

Notation "'Loc_' l" := (fun x => loc lab x = Some l) (at level 1).
Notation "'W_ex'" := G.(W_ex).
Notation "'W_ex_acq'" := (W_ex ∩₁ (fun a => is_true (is_xacq lab a))).

Lemma reservation_eps_step PC T S f_to f_from thread w smode
      (SIMREL_THREAD : simrel_thread G sc PC T S f_to f_from thread smode)
      (TID : tid w = thread)
      (TSTEP : ext_itrav_step
                 G sc w (mkETC T S) (mkETC T (S ∪₁ eq w)))
      (PRMW : codom_rel (⦗S \₁ issued T⦘ ⨾ rfi ⨾ rmw) w) :
  exists f_to' f_from',
    ⟪ SIMREL_THREAD : simrel_thread G sc PC T (S ∪₁ eq w) f_to' f_from' thread smode ⟫ /\
    ⟪ SIMREL :
        smode = sim_normal -> simrel G sc PC T S f_to f_from ->
        simrel G sc PC T (S ∪₁ eq w) f_to' f_from' ⟫.
Proof.
  cdes SIMREL_THREAD. cdes COMMON. cdes LOCAL.
  assert (tc_coherent G sc T) as sTCCOH by apply TCCOH.

  assert (~ S w) as NSW.
  { (* TODO: extract a lemma *)
    cdes TSTEP. desf; unfold ecovered, eissued in *; simpls; intros AA.
    { apply NCOV. apply COVEQ. basic_solver. }
    apply NISS. apply ISSEQ. basic_solver. }

  assert (~ issued T w) as NISSW.
  { intros AA. apply NSW. by apply TCCOH.(etc_I_in_S). }

  destruct PRMW as [wp PRMW].
  destruct_seq_l PRMW as SWP.

  assert (S wp /\ ~ issued T wp) as [SSWP NISSWP] by (split; apply SWP).

  set (ts := Time.middle (f_from wp) (f_to wp)).
  set (f_to' := upd (upd f_to wp ts) w (f_to wp)).
  set (f_from' := upd f_from w ts).
  
  assert (ISSEQ_TO   : forall w (ISS : issued T w), f_to' w = f_to w).
  { ins. unfold f_to'.
    rewrite updo; auto; [|by intros AA; desf].
    rewrite updo; auto. intros AA. desf. }
  assert (ISSEQ_FROM : forall w (ISS : issued T w), f_from' w = f_from w).
  { ins. unfold f_from'.
    rewrite updo; auto. intros AA. desf. }

  assert (E w) as EW.
  { eapply ext_itrav_stepE; eauto. }
  assert (~ is_init w) as NIW.
  { intros IN. apply NSW. apply TCCOH.(etc_I_in_S).
    eapply init_issued; eauto. split; auto. }
  assert (~ (is_init ∩₁ E) w) as NIEW.
  { intros [AA BB]. desf. }

  assert (E wp) as EWP.
  { by apply TCCOH.(etc_S_in_E). }
  assert (~ is_init wp) as NIWP.
  { intros IN. apply NISSWP. eapply init_issued; eauto. split; auto. }
  assert (~ (is_init ∩₁ E) wp) as NIEWP.
  { intros [AA BB]. desf. }

  assert (f_to_coherent G (S ∪₁ eq w) f_to' f_from') as FCOH'.
  { red. unfold f_to', f_from'. splits.
    { ins.
      do 2 (rewrite updo; [|by intros AA; desf]).
        by apply FCOH. }
    { ins.
      rewrite updo; [|by intros AA; desf].
        by apply FCOH. }
    { intros x [SX|] NINX; subst.
      { do 2 (rewrite updo; [|by intros AA; desf]).
        destruct (classic (x = wp)); subst.
        { rewrite upds. unfold ts.
          apply Time.middle_spec. by apply FCOH. }
        rewrite updo; [|by intros AA; desf].
          by apply FCOH. }
      rewrite !upds. unfold ts.
      apply Time.middle_spec. by apply FCOH. }
    all: admit. }
  
  exists f_to', f_from'.
  splits; [red; splits|].
Admitted.
  (* { red; splits; try apply SIMREL_THREAD. *)
  (*   { apply TSTEP. } *)
  (*   { admit. } *)
  (*   { ins. *)

End ReservationEpsPlainStep.
