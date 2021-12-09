Require Import PArith Arith.
From hahn Require Import Hahn.
Require Import PromisingLib.
From Promising2 Require Import Configuration TView View Time Event Cell Thread Memory Local.

From imm Require Import Events.
From imm Require Import Execution.
From imm Require Import Execution_eco.
From imm Require Import imm_s.
From imm Require Import imm_s_hb.
From imm Require Import imm_bob imm_s_ppo.
From imm Require Import ProgToExecution.
From imm Require Import CombRelations CombRelationsMore.
From imm Require Import Prog.
From imm Require Import ProgToExecution.

Require Import AuxRel.
From imm Require Import AuxRel2.
From imm Require Import TraversalConfig.
From imm Require Import Traversal.
Require Import ExtTraversalConfig.
Require Import ExtTraversal.
Require Import ExtSimTraversal.
From imm Require Import ViewRelHelpers.
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
Require Import WriteRlxCovPlainStep.
Require Import RMWRlxCovPlainStep.
Require Import ReservePlainStep.
Require Import IssuePlainStep.
Require Import IssueNextPlainStep.
Require Import IssueRelPlainStep.
Require Import IssueRelNextPlainStep.
Require Import IssueReservedPlainStep.
Require Import IssueReservedRelPlainStep.
Require Import IssueReservedRelNextPlainStep.

Set Implicit Arguments.

Section PlainStep.

Variable G : execution.
Variable WF : Wf G.
Variable sc : relation actid.
Variable CON : imm_consistent G sc.

Notation "'E'" := (acts_set G).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'rmw'" := (rmw G).
Notation "'data'" := (data G).
Notation "'addr'" := (addr G).
Notation "'ctrl'" := (ctrl G).

Notation "'fr'" := (fr G).
Notation "'coe'" := (coe G).
Notation "'coi'" := (coi G).
Notation "'deps'" := (deps G).
Notation "'rfi'" := (rfi G).
Notation "'rfe'" := (rfe G).
Notation "'detour'" := (detour G).
Notation "'hb'" := (hb G).
Notation "'sw'" := (sw G).

Notation "'lab'" := (lab G).

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
Notation "'W_ex'" := (W_ex G).
Notation "'W_ex_acq'" := (W_ex ∩₁ (fun a => is_true (is_xacq lab a))).

Lemma plain_sim_step thread PC T S f_to f_from T' S' smode
      (TCSTEP : ext_isim_trav_step G sc thread (mkETC T S) (mkETC T' S'))
      (SIMREL_THREAD : simrel_thread G sc PC T S f_to f_from thread smode) :
    exists PC' f_to' f_from',
      ⟪ PSTEP : (plain_step MachineEvent.silent thread)＊ PC PC' ⟫ /\
      ⟪ SIMREL_THREAD : simrel_thread G sc PC' T' S' f_to' f_from' thread smode ⟫ /\
      ⟪ SIMREL :
          smode = sim_normal -> simrel G sc PC T S f_to f_from ->
          simrel G sc PC' T' S' f_to' f_from' ⟫.
Proof using WF CON.
  cdes SIMREL_THREAD. cdes COMMON. cdes LOCAL.
  set (TCSTEP' := TCSTEP).
  inv TCSTEP'.
  { (* Fence covering *)
    cdes TS. desf.
    { edestruct fence_step; eauto.
      desc. do 3 eexists. splits; eauto. by eapply inclusion_r_rt; eauto. }
    all: exfalso; assert (W f) as WFF; [|type_solver].
    all: eapply (reservedW WF); [by apply TS|].
    all: apply RESEQ; basic_solver. }

  { (* Read covering *)
    cdes TS. desf.
    { edestruct read_step; eauto.
      desc. do 3 eexists. splits; eauto. by eapply inclusion_r_rt; eauto. }
    all: exfalso; assert (W r) as WFF; [|type_solver].
    all: eapply (reservedW WF); [by apply TS|].
    all: apply RESEQ; basic_solver. }

  { (* Write reserving *)
    cdes TS. desf; unfold eissued, ecovered in *; simpls.
    { exfalso. apply NCOV. apply COVEQ. basic_solver. }
    { exfalso. apply NISS. apply ISSEQ. basic_solver. }
    edestruct reserve_step; eauto.
    desc. do 3 eexists. splits; eauto. by eapply inclusion_r_rt; eauto. }

  { (* Relaxed write issuing *)
    cdes TS. desf; unfold eissued, ecovered in *; simpls.
    3: { exfalso. apply NISS. apply ISSEQ. basic_solver. }
    { exfalso. apply NCOV. apply COVEQ. basic_solver. }
    destruct (classic (S w)) as [SW|NSW].
    { destruct (classic (exists wnext, dom_sb_S_rfrmw G {| etc_TC := T; reserved := S |} rfi (eq w) wnext))
      as [NEMP|EMP].
      2: { edestruct issue_rlx_reserved_step_no_next; eauto.
           { generalize EMP. clear. basic_solver. }
           desc. do 3 eexists. splits; eauto. by eapply inclusion_t_rt; eauto. }
      desc. edestruct issue_rlx_reserved_step_with_next; eauto.
      desc. do 3 eexists. splits; eauto. by eapply inclusion_t_rt; eauto. }
    destruct (classic (exists wnext, dom_sb_S_rfrmw G (mkETC T S) rfi (eq w) wnext))
      as [NEMP|EMP].
    2: { edestruct issue_rlx_step_no_next; eauto.
         { generalize EMP. clear. basic_solver. }
         desc. do 3 eexists. splits; eauto. by eapply inclusion_t_rt; eauto. }
    desc. edestruct issue_rlx_step_next; eauto.
    desc. do 3 eexists. splits; eauto. by eapply inclusion_t_rt; eauto. }

  { (* Relaxed write covering *)
    cdes TS. desf; unfold eissued, ecovered in *; simpls.
    { edestruct rlx_write_cover_step; eauto.
      desc. do 3 eexists. splits; eauto. by eapply inclusion_r_rt; eauto. }
    exfalso.
    eapply ext_itrav_step_nC.
    3: by eauto.
    all: eauto.
    apply COVEQ. basic_solver. }

  { (* Release write covering *)
    cdes TS1. desf; unfold eissued, ecovered in *; simpls.
    3: { exfalso. apply NISS. apply ISSEQ. basic_solver. }
    { exfalso. apply NCOV. apply COVEQ. basic_solver. }
    destruct (classic (S w)) as [SW|NSW].
    { exfalso. apply NRMW. apply TCCOH. by split. }

    destruct (classic (exists wnext, dom_sb_S_rfrmw G (mkETC T S) rfi (eq w) wnext))
      as [NEMP|EMP].
    2: { edestruct issue_rel_step_no_next; eauto.
         { generalize EMP. clear. basic_solver. }
         desc. do 3 eexists. splits; eauto. by eapply inclusion_t_rt; eauto. }
    desc. edestruct issue_rel_step_next; eauto.
    desc. do 3 eexists. splits; eauto. by eapply inclusion_t_rt; eauto. }

  { (* Relaxed RMW covering *)
    assert (R r) as RR.
    { apply (dom_l (wf_rmwD WF)) in RMW. apply seq_eqv_l in RMW. desf. }
    cdes TS1. desf; unfold eissued, ecovered in *; simpls.
    { edestruct rlx_rmw_cover_step; eauto.
      desc. do 3 eexists. splits; eauto. by eapply inclusion_r_rt; eauto. }
    all: exfalso; assert (W r) as WFF; [|type_solver].
    all: eapply (reservedW WF); [by apply TS1|].
    all: apply RESEQ; basic_solver. }

  (* Release RMW covering *)
  cdes TS2. desf; unfold eissued, ecovered in *; simpls.
  1,3: exfalso; apply NISS; apply ISSEQ; clear; basic_solver.
  assert (S w) as SW.
  { apply RES. by exists r. }
  destruct (classic (exists wnext, dom_sb_S_rfrmw G {| etc_TC := T; reserved := S |} rfi (eq w) wnext))
      as [NEMP|EMP].
  2: { edestruct issue_rel_reserved_step_no_next; eauto.
       { generalize EMP. clear. basic_solver. }
       desc. do 3 eexists. splits; eauto. by eapply inclusion_t_rt; eauto. }
  desc. edestruct issue_rel_reserved_step_with_next; eauto.
  desc. do 3 eexists. splits; eauto. by eapply inclusion_t_rt; eauto.
Qed.

End PlainStep.
