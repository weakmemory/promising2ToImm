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
From imm Require Import Prog.
From imm Require Import ProgToExecution.

Require Import AuxRel.
Require Import AuxRel2.
Require Import TraversalConfig.
Require Import Traversal.
Require Import ExtTraversal.
Require Import ExtSimTraversal.
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
Require Import PlainStepBasic.
Require Import FencePlainStep.
Require Import ReadPlainStep.
(* TODO: Require Import WritePlainStep. *)
(* TODO: Require Import RMWPlainStep. *)

Set Implicit Arguments.

Section PlainStep.

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

Lemma plain_sim_step thread PC T S f_to f_from T' S' smode
      (TCSTEP : ext_isim_trav_step G sc thread (mkETC T S) (mkETC T' S'))
      (SIMREL_THREAD : simrel_thread G sc PC T S f_to f_from thread smode) :
    exists PC' f_to' f_from',
      ⟪ PSTEP : plain_step MachineEvent.silent thread PC PC' ⟫ /\
      ⟪ SIMREL_THREAD : simrel_thread G sc PC' T' S' f_to' f_from' thread smode ⟫ /\
      ⟪ SIMREL :
          smode = sim_normal -> simrel G sc PC T S f_to f_from ->
          simrel G sc PC' T' S' f_to' f_from' ⟫.
Proof.
  cdes SIMREL_THREAD. cdes COMMON. cdes LOCAL.
  set (TCSTEP' := TCSTEP).
  inv TCSTEP'.
  { (* Fence covering *)
    cdes TS. desf.
    2,3: exfalso; assert (W f) as WFF; [|type_solver].
    2,3: eapply WF.(reservedW); [by apply TS|].
    2,3: apply RESEQ; basic_solver.
    edestruct fence_step as [PC' HH]; eauto. }
  { (* Read covering *)
    cdes TS. desf.
    2,3: exfalso; assert (W r) as WFF; [|type_solver].
    2,3: eapply WF.(reservedW); [by apply TS|].
    2,3: apply RESEQ; basic_solver.
    edestruct read_step; eauto. }
Admitted.
(*   { (* Relaxed write issuing *) *)
(*     cdes TS. desf. *)
(*     { exfalso. apply NISS. red in COV.  *)
(*       destruct COV as [_ [[COV|COV]|COV]]. *)
(*       { apply COV. } *)
(*       all: type_solver. } *)
(*     edestruct rlx_write_promise_step; eauto. } *)
(*   { (* Relaxed write covering *) *)
(*     cdes TS. desf. *)
(*     edestruct rlx_write_cover_step; eauto. *)
(*     red. split; [split|]; auto. all: apply COV. } *)
(*   { (* Release write covering *) *)
(*     cdes TS1. desf. *)
(*     { exfalso. apply NISS. red in COV.  *)
(*       destruct COV as [_ [[COV|COV]|COV]]. *)
(*       { apply COV. } *)
(*       all: type_solver. } *)
(*     edestruct rel_write_step; eauto. *)
(*     red. split; [split|]; auto. *)
(*     { apply ISS. } *)
(*     2: { intros COV. apply NISS. eapply w_covered_issued; eauto. by split. } *)
(*     red in ISS. *)
(*     destruct ISS as [[[_ ISS] _] _]. red in ISS. *)
(*     red. etransitivity. *)
(*     2: by apply ISS. *)
(*     unfold fwbob. *)
(*     arewrite (eq w ⊆₁ W ∩₁ Rel ∩₁ eq w). *)
(*     basic_solver. *)
(*     basic_solver 10. } *)
(*   { (* Relaxed RMW covering *) *)
(*     assert (R r) as RR. *)
(*     { apply (dom_l WF.(wf_rmwD)) in RMW. hahn_rewrite (R_ex_in_R) in RMW. apply seq_eqv_l in RMW. desf. } *)
(*     cdes TS1. desf. *)
(*     2: { red in ISS0. type_solver. } *)
(*     edestruct rlx_rmw_cover_step; eauto. *)
(*     red. split; [split|]; auto. all: apply COV. } *)
(*   (* Release RMW covering *) *)
(*   assert (R r) as RR. *)
(*   { apply (dom_l WF.(wf_rmwD)) in RMW. hahn_rewrite (R_ex_in_R) in RMW. apply seq_eqv_l in RMW. desf. } *)
(*   cdes TS1. desf. *)
(*   2: { red in ISS. type_solver. } *)
(*   edestruct rel_rmw_cover_step; eauto. *)
(*   red. split; [split|]; auto. *)
(*   all: apply COV. *)
(* Qed. *)

End PlainStep.
