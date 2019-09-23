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
Require Import SimulationRelProperties.

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
Proof using WF CON.
  cdes SIMREL_THREAD. cdes COMMON. cdes LOCAL.
  assert (tc_coherent G sc T) as sTCCOH by apply TCCOH.

  assert (sc_per_loc G) as SC_PER_LOC.
  { by apply coherence_sc_per_loc; cdes CON. }
  assert (complete G) as COMPL by apply CON.

  assert (~ S w) as NSW.
  { (* TODO: extract a lemma *)
    cdes TSTEP. desf; unfold ecovered, eissued in *; simpls; intros AA.
    { apply NCOV. apply COVEQ. basic_solver. }
    apply NISS. apply ISSEQ. basic_solver. }

  assert (~ issued T w) as NISSW.
  { intros AA. apply NSW. by apply TCCOH.(etc_I_in_S). }

  destruct PRMW as [wp PRMWI].
  destruct_seq_l PRMWI as SWP.

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

  assert (sb wp w) as SB.
  { by apply imm_s_rfrmw.rfi_rmw_in_sb_loc. }
  assert (tid wp = tid w) as TWP.
  { apply sb_tid_init' in SB. destruct SB as [AA|AA].
    { apply AA. }
    destruct_seq_l AA as BB. desf. }
  
  (* TODO: make a lemma and move to more appropriate place *)
  assert (forall x y z (COXY : co x y) (ICOZY : immediate co z y), co^? x z)
    as co_imm_co_in_co_cr.
  { ins. destruct (classic (x = z)) as [|NXZ]; subst; [by left|right].
    assert (co z y) as COZY by apply ICOZY.
    apply WF.(wf_coD) in COZY. destruct_seq COZY as [AA1 AA2].
    apply WF.(wf_coE) in COZY. destruct_seq COZY as [AA3 AA4].
    apply WF.(wf_coD) in COXY. destruct_seq COXY as [BB1 BB2].
    apply WF.(wf_coE) in COXY. destruct_seq COXY as [BB3 BB4].
    apply is_w_loc in AA2. desf.
    set (CC:=COXY). apply WF.(wf_col) in CC. red in CC.
    set (DD:=COZY). apply WF.(wf_col) in DD. red in DD.
    edestruct WF.(wf_co_total); eauto.
    1,2: split; [split|]; eauto.
    exfalso. eapply ICOZY; eauto. }

  (* TODO: make a lemma and move to more appropriate place *)
  assert (wf_rfrmwsf: functional (rf ⨾ rmw)).
  { intros x y z AA BB.
    assert (immediate co x y) as ICOXY.
    { eapply rfrmw_in_im_co; eauto. }
    assert (co x y) as COXY by apply ICOXY.
    assert (immediate co x z) as ICOXZ.
    { eapply rfrmw_in_im_co; eauto. }
    assert (co x z) as COXZ by apply ICOXZ.
    apply WF.(wf_coD) in COXY. destruct_seq COXY as [BB1 BB2].
    apply WF.(wf_coE) in COXY. destruct_seq COXY as [BB3 BB4].
    apply WF.(wf_coD) in COXZ. destruct_seq COXZ as [AA1 AA2].
    apply WF.(wf_coE) in COXZ. destruct_seq COXZ as [AA3 AA4].
    apply is_w_loc in AA1. desf.
    set (CC:=COXY). apply WF.(wf_col) in CC. red in CC.
    set (DD:=COXZ). apply WF.(wf_col) in DD. red in DD.
    destruct (classic (y = z)); auto.
    edestruct WF.(wf_co_total); eauto.
    1,2: split; [split|]; eauto.
    { by etransitivity; [|by eauto]. }
    { exfalso. by apply ICOXZ with (c:=y). }
    exfalso. by apply ICOXY with (c:=z). }

  (* TODO: make a lemma and move to more appropriate place *)
  assert (dom_rf_rmw_S : dom_rel (⦗W_ex⦘ ⨾ rf ⨾ rmw ⨾ ⦗S⦘) ⊆₁ S).
  { rewrite (rf_rmw_S WF TCCOH). basic_solver. }
  
  assert ((rf ⨾ rmw) wp w) as PRMW.
  { generalize PRMWI. unfold Execution.rfi. basic_solver. }
  assert (immediate co wp w) as ICOWPW.
  { eapply rfrmw_in_im_co; eauto. }

  assert (f_to_coherent G (S ∪₁ eq w) f_to' f_from') as FCOH_NEW.
  { unfold f_to', f_from'; red; splits.
    { ins.
      do 2 (rewrite updo; [|by intros AA; desf]).
        by apply FCOH. }
    { ins.
      rewrite updo; [|by intros AA; desf].
        by apply FCOH. }
    { intros x [SX|] NINX; subst.
      { do 2 (rewrite updo; [|by intros AA; desf]).
        destruct (classic (x = wp)); subst.
        { rewrite upds.
          unfold ts. apply Time.middle_spec. by apply FCOH. }
        rewrite updo; [|by intros AA; desf].
          by apply FCOH. }
      rewrite !upds. unfold ts.
      apply Time.middle_spec. by apply FCOH. }
    { intros x y SX SY COXY.
      assert (x <> y) as NXY.
      { intros HH; subst. eapply co_irr; eauto. }
      destruct SX as [SX|]; destruct SY as [SY|]; subst.
      { rewrite updo; [|by intros AA; desf].
        rewrite updo with (f:=f_from); [|by intros AA; desf].
        destruct (classic (x = wp)); subst.
        2: { rewrite updo; auto. by apply FCOH. }
        rewrite upds.
        apply Time.le_lteq; left.
        eapply TimeFacts.lt_le_lt.
        { unfold ts. apply Time.middle_spec. by apply FCOH. }
          by apply FCOH. }
      { rewrite upds. rewrite updo; auto.
        destruct (classic (x = wp)); subst.
        { rewrite upds. reflexivity. }
        rewrite updo; auto.
        apply Time.le_lteq; left.
        eapply TimeFacts.le_lt_lt.
        2: { unfold ts.
             apply Time.middle_spec with (lhs:=f_from wp) (rhs:=f_to wp).
               by apply FCOH. }
        apply FCOH; auto.
        apply co_imm_co_in_co_cr with (x:=x) in ICOWPW; auto.
        destruct ICOWPW; desf. }
      { rewrite upds. rewrite updo; auto.
        apply FCOH; auto. eapply WF.(co_trans).
        { apply ICOWPW. }
        done. }
      exfalso. eapply WF.(co_irr); eauto. }
    intros x y SX SY COXY.
    assert (x <> y) as NXY.
    { intros HH; subst. eapply WF.(co_irr).
      eapply rf_rmw_in_co; eauto. }
    destruct SX as [SX|]; destruct SY as [SY|]; subst.
    { rewrite updo; [|by intros AA; desf].
      rewrite updo with (f:=f_from); [|by intros AA; desf].
      destruct (classic (x = wp)); subst.
      2: { rewrite updo; auto. by apply FCOH. }
      exfalso.
      assert (y = w); desf.
      eapply wf_rfrmwsf; eauto. }
    { rewrite updo; [|by intros AA; desf].
      rewrite upds.
      assert (x = wp); subst.
      2: by rewrite upds.
      eapply wf_rfrmwf; eauto. }
    { exfalso. apply NSW.
      apply dom_rf_rmw_S. eexists.
      apply seq_eqv_l. split.
      { generalize PRMW. unfold Execution.W_ex. basic_solver 10. }
      apply seqA. apply seq_eqv_r. eauto. }
    exfalso. eapply wf_rfrmw_irr; eauto. }

  assert (reserved_time G T (S ∪₁ eq w) f_to' f_from' smode (Configuration.memory PC))
    as RST.
  { red in RESERVED_TIME.
    red. desf; desc; splits.
    5: { rewrite RMW_RESERVED. basic_solver. }
    4: { etransitivity.
         2: by apply FOR_SPLIT.
         basic_solver. }
    { (* TODO: make a lemma message_to_event_f_issued and
               and move to SimulationRelProperties.v *)
      red. ins.
      apply MEM in MSG. desf; eauto.
      right. exists b. splits; auto. }
    { (* TODO: make a separate lemma? *)
      red. ins. apply HMEM in MSG. desf.
      assert (b <> w) as NBW.
      { intros AA; subst. apply NSW.
        apply seq_eqv_lr in RFRMWS. apply RFRMWS. }
      assert (b' <> w) as NBW'.
      { intros AA; subst. apply NSW.
        apply seq_eqv_lr in RFRMWS. apply RFRMWS. }
      destruct (classic (b' = wp)) as [|NEQ]; subst.
      2: { unfold f_to', f_from'.
           exists b, b'. splits; eauto.
           { destruct_seq RFRMWS as [AA BB].
             apply seq_eqv_lr. splits; auto.
             all: generalize AA BB NBW NBW'; basic_solver. }
           1,2: by rewrite !updo; auto.
           intros [x AA]. apply seqA in AA.
           destruct_seq_r AA as BB. destruct BB as [BB|]; subst.
           { apply NOAFT. eexists. apply seqA. apply seq_eqv_r. eauto. }
           apply NEQ. eapply wf_rfrmwf; eauto. }
      unfold f_to', f_from'.
      exists b, w.
      splits; auto.
      { destruct_seq RFRMWS as [AA BB].
        apply seq_eqv_lr. splits; auto.
        2: { apply rt_unit. exists wp. split; auto. }
        all: generalize AA BB NBW NBW'; basic_solver. }
      { by rewrite updo. }
      { by rewrite upds. }
      intros [x AA]. apply seqA in AA.
      destruct_seq_r AA as BB. destruct BB as [BB|]; subst.
      2: by eapply wf_rfrmw_irr; eauto.
      apply NSW. apply dom_rf_rmw_S.
      exists x. apply seq_eqv_l. split.
      { generalize PRMW. unfold Execution.W_ex. basic_solver. }
      apply seqA. apply seq_eqv_r. eauto. }

    intros x y SX SY COXY. unfold f_to', f_from'.
    assert (x <> y) as NEQ.
    { intros HH; subst. eapply WF.(co_irr); eauto. }
    destruct SX as [SX|]; destruct SY as [SY|]; desf.
    { rewrite updo; [|by intros AA; desf].
      rewrite updo with (f:=f_from); [|by intros AA; desf].
      destruct (classic (x = wp)); subst.
      2: { rewrite updo; auto. }
      rewrite upds.
      intros AA. exfalso.
      admit. }
    { rewrite updo; auto. rewrite upds.
      destruct (classic (x = wp)); subst; auto.
      rewrite updo; auto.
      intros AA. exfalso.
      admit. }
    rewrite upds. rewrite updo; auto.
    intros AA. exfalso.
    admit. }

  assert (sim_res_prom G T (S ∪₁ eq w) f_to' f_from' thread (Local.promises local))
    as SRPROM.
  { (* TODO: make a separate lemma? Share smth with the previous TODO? *)
    red. ins.
    apply SIM_RPROM in RES. desf.
    assert (b <> w) as NBW.
    { intros AA; subst. apply NSW.
      apply seq_eqv_lr in RFRMWS. apply RFRMWS. }
    assert (b' <> w) as NBW'.
    { intros AA; subst. apply NSW.
      apply seq_eqv_lr in RFRMWS. apply RFRMWS. }
    destruct (classic (b' = wp)) as [|NEQ]; subst.
    2: { unfold f_to', f_from'.
         exists b, b'. splits; eauto.
         { destruct_seq RFRMWS as [AA BB].
           apply seq_eqv_lr. splits; auto.
           all: generalize AA BB NBW NBW'; basic_solver. }
         1,2: by rewrite !updo; auto.
         intros [x AA]. apply seqA in AA.
         destruct_seq_r AA as BB. destruct BB as [CC [BB|]]; subst.
         { apply NOAFT. eexists. apply seqA. apply seq_eqv_r.
           splits; eauto. split; auto. }
         apply NEQ.
         assert ((rf ⨾ rmw) b' x) as DD.
         { generalize AA. unfold Execution.rfi. basic_solver. }
         eapply wf_rfrmwf; eauto. }
    unfold f_to', f_from'.
    exists b, w.
    splits; auto.
    { destruct_seq RFRMWS as [AA BB].
      apply seq_eqv_lr. splits; auto.
      2: { apply rt_unit. exists wp. split; auto. }
      all: generalize AA BB NBW NBW'; basic_solver. }
    { by rewrite updo. }
    { by rewrite upds. }
    intros [x AA]. apply seqA in AA.
    destruct_seq_r AA as BB.
    assert ((rf ⨾ rmw) w x) as DD.
    { generalize AA. unfold Execution.rfi. basic_solver. }
    destruct BB as [CC [BB|]]; subst.
    2: by eapply wf_rfrmw_irr; eauto.
    apply NSW. apply dom_rf_rmw_S.
    exists x. apply seq_eqv_l. split.
    { generalize PRMW. unfold Execution.W_ex. basic_solver. }
    apply seqA. apply seq_eqv_r. eauto. }

  assert (simrel_thread G sc PC T (S ∪₁ eq w) f_to' f_from' thread smode) as STL.
  { red; splits.
    { red; splits; auto; try apply SIMREL_THREAD.
      { apply TSTEP. }
      ins. eapply sc_view_f_issued; eauto. }
    red. exists state, local. splits; auto.
    { eapply sim_prom_f_issued; eauto. }
    { eapply sim_mem_f_issued; eauto. }
    eapply sim_tview_f_issued; eauto. }

  exists f_to', f_from'.
  splits; auto.
  intros AA HH; subst.
  red. splits.
  { apply STL. }
  ins. destruct (classic (thread = tid w)) as [|NTEQ]; subst.
  { apply STL. }
  cdes HH. apply THREADS in TP.
  cdes TP.
  assert (sim_res_prom G T (S ∪₁ eq w) f_to' f_from' thread (Local.promises local0)) as SRP'.
  { eapply sim_res_prom_other_thread with (f_to:=f_to) (f_from:=f_from); eauto.
    { unfolder. ins. desf. eauto. }
    { unfold f_to'. ins.
      rewrite updo; [|by intros AA; desf].
      rewrite updo; auto. intros AA; desf. }
    unfold f_from'. ins. by rewrite updo; [|by intros AA; desf]. }

  red. exists state0, local0. splits; auto.
  { eapply sim_prom_f_issued; eauto. }
  { eapply sim_mem_f_issued; eauto. }
  eapply sim_tview_f_issued; eauto.
Admitted.

End ReservationEpsPlainStep.
