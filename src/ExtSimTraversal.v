From hahn Require Import Hahn.

From imm Require Import Events.
From imm Require Import Execution.
From imm Require Import Execution_eco.
From imm Require Import imm_s.
From imm Require Import imm_s_hb.
From imm Require Import imm_common.
From imm Require Import CombRelations.
From imm Require Import TraversalConfig.
From imm Require Import Traversal.
Require Import ExtTraversal.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section ExtSimTraversal.
  Variable G : execution.
  Variable WF : Wf G.
  Variable COM : complete G.
  Variable sc : relation actid.
  Variable IMMCON : imm_consistent G sc.

  Notation "'acts'" := G.(acts).
  Notation "'sb'" := G.(sb).
  Notation "'rmw'" := G.(rmw).
  Notation "'data'" := G.(data).
  Notation "'addr'" := G.(addr).
  Notation "'ctrl'" := G.(ctrl).
  Notation "'rf'" := G.(rf).
  Notation "'co'" := G.(co).
  Notation "'coe'" := G.(coe).
  Notation "'fr'" := G.(fr).

  Notation "'eco'" := G.(eco).

  Notation "'bob'" := G.(bob).
  Notation "'fwbob'" := G.(fwbob).
  Notation "'ppo'" := G.(ppo).
  Notation "'fre'" := G.(fre).
  Notation "'rfi'" := G.(rfi).
  Notation "'rfe'" := G.(rfe).
  Notation "'deps'" := G.(deps).
  Notation "'detour'" := G.(detour).
  Notation "'release'" := G.(release).
  Notation "'sw'" := G.(sw).
  Notation "'hb'" := G.(hb).

  Notation "'urr'" := (urr G sc).
  Notation "'c_acq'" := (c_acq G sc).
  Notation "'c_cur'" := (c_cur G sc).
  Notation "'c_rel'" := (c_rel G sc).
  Notation "'t_acq'" := (t_acq G sc).
  Notation "'t_cur'" := (t_cur G sc).
  Notation "'t_rel'" := (t_rel G sc).
  Notation "'S_tm'" := G.(S_tm).
  Notation "'S_tmr'" := G.(S_tmr).
  Notation "'msg_rel'" := (msg_rel G sc).

Notation "'lab'" := G.(lab).
Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'mod'" := (Events.mod lab).
Notation "'same_loc'" := (same_loc lab).

Notation "'E'" := G.(acts_set).
Notation "'R'" := (fun x => is_true (is_r lab x)).
Notation "'W'" := (fun x => is_true (is_w lab x)).
Notation "'F'" := (fun x => is_true (is_f lab x)).
Notation "'RW'" := (R ∪₁ W).
Notation "'FR'" := (F ∪₁ R).
Notation "'FW'" := (F ∪₁ W).

Notation "'R_ex'" := (R_ex G).
Notation "'W_ex'" := (W_ex G).
Notation "'W_ex_acq'" := (W_ex ∩₁ (fun a => is_true (is_xacq lab a))).

Notation "'Init'" := (fun a => is_true (is_init a)).
Notation "'Loc_' l" := (fun x => loc x = Some l) (at level 1).
Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'W_' l" := (W ∩₁ Loc_ l) (at level 1).

Notation "'Pln'" := (fun x => is_true (is_only_pln lab x)).
Notation "'Rlx'" := (fun x => is_true (is_rlx lab x)).
Notation "'Rel'" := (fun x => is_true (is_rel lab x)).
Notation "'Acq'" := (fun x => is_true (is_acq lab x)).
Notation "'Acqrel'" := (fun x => is_true (is_acqrel lab x)).
Notation "'Sc'" := (fun x => is_true (is_sc lab x)).
Notation "'Acq/Rel'" := (fun a => is_true (is_ra lab a)).

Inductive ext_isim_trav_step : thread_id -> ext_trav_config -> ext_trav_config -> Prop :=
  ext_fence_trav_step T
    f (FF : F f)
    (TS : ext_itrav_step
            G sc f T
            (mkETC (mkTC (ecovered T ∪₁ eq f) (eissued T))
                   (reserved T))) :
    ext_isim_trav_step
      (tid f) T
      (mkETC (mkTC (ecovered T ∪₁ eq f) (eissued T)) (reserved T))

| ext_read_trav_step T
    r (RR : R r) (NRMW : ~ dom_rel rmw r)
    (TS : ext_itrav_step
            G sc r T
            (mkETC (mkTC (ecovered T ∪₁ eq r) (eissued T))
                   (reserved T))) :
    ext_isim_trav_step
      (tid r) T
      (mkETC (mkTC (ecovered T ∪₁ eq r) (eissued T))
             (reserved T))

| ext_reserve_trav_step T w
    (TS : ext_itrav_step
            G sc w T
            (mkETC (etc_TC T) (reserved T ∪₁ eq w))) :
    ext_isim_trav_step
      (tid w) T
      (mkETC (etc_TC T) (reserved T ∪₁ eq w))

| ext_rlx_write_promise_step T
    w (WW : W w) (NREL : ~ Rel w) (NISS : ~ eissued T w)
    (TS : ext_itrav_step
            G sc w T
            (mkETC (mkTC (ecovered T) (eissued T ∪₁ eq w))
                   (reserved T ∪₁ eq w))) :
    ext_isim_trav_step
      (tid w) T (mkETC (mkTC (ecovered T) (eissued T ∪₁ eq w))
                       (reserved T ∪₁ eq w))

| ext_rlx_write_cover_step T
    w (WW : W w) (NREL : ~ Rel w) (NRMW : ~ codom_rel rmw w)
    (ISS : eissued T w)
    (TS : ext_itrav_step
            G sc w T
            (mkETC (mkTC (ecovered T ∪₁ eq w) (eissued T))
                   (reserved T))) :
    ext_isim_trav_step
      (tid w) T (mkETC (mkTC (ecovered T ∪₁ eq w) (eissued T))
                       (reserved T))

| ext_rel_write_step T
    w (WW : W w) (REL : Rel w) (NRMW : ~ codom_rel rmw w)
    (NISS : ~ eissued T w)
    (TS1 : ext_itrav_step
             G sc w T
             (mkETC (mkTC (ecovered T) (eissued T ∪₁ eq w))
                    (reserved T ∪₁ eq w)))
    (TS2 : ext_itrav_step
             G sc w
             (mkETC (mkTC (ecovered T) (eissued T ∪₁ eq w))
                    (reserved T ∪₁ eq w))
             (mkETC (mkTC (ecovered T ∪₁ eq w) (eissued T ∪₁ eq w))
                    (reserved T ∪₁ eq w))) :
    ext_isim_trav_step
      (tid w) T (mkETC (mkTC (ecovered T ∪₁ eq w) (eissued T ∪₁ eq w))
                       (reserved T ∪₁ eq w))

| ext_rlx_rmw_cover_step T
    r w (RMW : rmw r w) (NREL : ~ Rel w) (ISS : eissued T w)
    (TS1 : ext_itrav_step
             G sc r T
             (mkETC (mkTC (ecovered T ∪₁ eq r) (eissued T))
                    (reserved T)))
    (TS2 : ext_itrav_step
             G sc w
             (mkETC (mkTC (ecovered T ∪₁ eq r) (eissued T))
                    (reserved T))
             (mkETC (mkTC (ecovered T ∪₁ eq r ∪₁ eq w) (eissued T))
                    (reserved T))):
    ext_isim_trav_step
      (tid r) T
      (mkETC (mkTC (ecovered T ∪₁ eq r ∪₁ eq w) (eissued T))
                       (reserved T))

| ext_rel_rmw_step T
    r w (RMW : rmw r w) (REL : Rel w) (NISS : ~ eissued T w)
    (TS1 : ext_itrav_step
             G sc r T
             (mkETC (mkTC (ecovered T ∪₁ eq r) (eissued T))
                    (reserved T)))
    (TS2 : ext_itrav_step
             G sc w
             (mkETC (mkTC (ecovered T ∪₁ eq r) (eissued T))
                    (reserved T))
             (mkETC (mkTC (ecovered T ∪₁ eq r) (eissued T ∪₁ eq w))
                    (reserved T ∪₁ eq w)))
    (TS3 : ext_itrav_step
             G sc w
             (mkETC (mkTC (ecovered T ∪₁ eq r) (eissued T ∪₁ eq w))
                    (reserved T ∪₁ eq w))
             (mkETC (mkTC (ecovered T ∪₁ eq r ∪₁ eq w) (eissued T ∪₁ eq w))
                    (reserved T ∪₁ eq w))):
    ext_isim_trav_step
      (tid r) T
      (mkETC (mkTC (ecovered T ∪₁ eq r ∪₁ eq w) (eissued T ∪₁ eq w))
             (reserved T ∪₁ eq w))
.

Definition ext_sim_trav_step T T' :=
  exists thread, ext_isim_trav_step thread T T'.

Lemma exists_ext_sim_trav_step T (ETCCOH : etc_coherent G sc T)
      (RELCOV :  W ∩₁ Rel ∩₁ eissued T ⊆₁ ecovered T)
      (RMWCOV : forall r w (RMW : rmw r w), ecovered T r <-> ecovered T w)
      T' (TS : ext_trav_step G sc T T') :
  exists T'', ext_sim_trav_step T T''.
Proof.
  destruct TS as [e TS].
  cdes TS. desf.
  { destruct (lab_rwf lab e) as [RE|[WE|FE]].
    3: { eexists; eexists. eapply ext_fence_trav_step; eauto.
         eapply ext_itrav_step_more.
         4: by eauto.
         { done. }
         { apply same_ext_trav_config_refl. }
         red. unfold ecovered, eissued in *; simpls.
         rewrite COVEQ, ISSEQ, RESEQ. eauto. }
    { destruct (classic (dom_rel rmw e)) as [RMW|NRMW].
      2: { eexists; eexists. eapply ext_read_trav_step; eauto.
           eapply ext_itrav_step_more.
           4: by eauto.
           { done. }
           { apply same_ext_trav_config_refl. }
           red. unfold ecovered, eissued in *; simpls.
           rewrite COVEQ, ISSEQ, RESEQ. eauto. }
      (* TODO: continue from here. *)
      destruct RMW as [w RMW].
      assert (~ ecovered T w) as COVW.
      { intros WCOV. apply NEXT. apply TCCOH in WCOV.
        apply WCOV. eexists. apply seq_eqv_r. split; eauto.
          by apply rmw_in_sb. }
      assert (is_w lab w) as WW.
      { apply (dom_r WF.(wf_rmwD)) in RMW.
        apply seq_eqv_r in RMW. desf. }
      assert (dom_rel (sb ⨾ ⦗eq w⦘) ⊆₁ covered T ∪₁ eq e) as SBW.
      { hahn_rewrite (rmw_from_non_init WF) in RMW.
        hahn_rewrite WF.(wf_rmwi) in RMW.
        hahn_rewrite (sb_immediate_adjacent WF) in RMW.
        unfold adjacent in *; unfolder in *; ins; desf.
        apply LA_ca in H; desf; eauto.
        generalize (sb_coverable TCCOH); unfolder; ins; desf.
        left; eapply H0; eauto. }
      assert (E w) as EW.
      { apply (dom_r WF.(wf_rmwE)) in RMW.
        apply seq_eqv_r in RMW. desf. }
      assert (~ (covered T ∪₁ eq e) w) as C1.
      { intros [H|H]; desf. type_solver. }
      destruct (classic (issued T w)) as [ISS|NISS].
      { eexists; eexists. 
        eapply rlx_rmw_cover_step; eauto.
        { intros REL. apply COVW. apply RELCOV.
            by split; [split|]. }
        { red. left. splits; simpls. }
        red. left. splits; simpls.
        split; [split|left; left; split]; auto. }
      destruct (classic (Rel w)) as [REL|NREL].
      2: { eexists; eexists. 
           eapply rlx_write_promise_step; eauto.
           red. right. splits; auto.
           red. split; [split; [split; [split|]|]|]; auto.
           { red. intros y H.
             specialize (SBW y).
             destruct SBW as [COVY|EY]; desf.
             { destruct H as [x H].
               apply seq_eqv_r in H; desf.
               exists x. apply seq_eqv_r. split; auto.
               apply bob_in_sb. by apply fwbob_in_bob. }
             destruct H as [x H]. apply seq_eqv_r in H. desf.
             red in H. destruct H as [[[H|H]|H]|H].
             1,3: by apply seq_eqv_r in H; mode_solver.
             all: by apply seq_eqv_l in H; mode_solver. }
           { red. rewrite WF.(ppo_in_sb). rewrite bob_in_sb.
             arewrite (sb ∪ sb ⊆ sb).
             rewrite (dom_l WF.(wf_detourD)). rewrite (dom_l WF.(wf_rfeD)).
             rewrite <- seq_union_r. rewrite seqA.
             rewrite dom_eqv1.
             assert (dom_rel (sb ⨾ ⦗eq w⦘) ⊆₁ coverable G sc T) as DD.
             { rewrite SBW. cdes TCCOH. rewrite CC. basic_solver. }
             arewrite (sb ⨾ ⦗eq w⦘ ⊆ ⦗coverable G sc T⦘ ⨾ sb ⨾ ⦗eq w⦘).
             { generalize DD. basic_solver. }
             rewrite seq_union_l.
             arewrite (rfe ⊆ rf). sin_rewrite rf_coverable; auto.
             rewrite detour_in_sb. sin_rewrite sb_coverable; auto.
             generalize (w_covered_issued TCCOH).
             basic_solver. }
           red. rewrite !seqA. rewrite dom_eqv1.
           rewrite SBW. rewrite WF.(W_ex_in_W).
           rewrite set_inter_union_r.
           apply set_subset_union_l; split; [|type_solver].
           generalize (w_covered_issued TCCOH). basic_solver. }
      eexists. eexists. 
      assert (itrav_step G sc e T {| covered := covered T ∪₁ eq e; issued := issued T |})
        as A1.
      { red. left. splits; auto. }
      assert (tc_coherent G sc {| covered := covered T ∪₁ eq e; issued := issued T |}) as B1.
      { eapply trav_step_coherence; eauto. by exists e. }

      assert (itrav_step G sc w {| covered := covered T ∪₁ eq e; issued := issued T |}
                         {| covered := covered T ∪₁ eq e; issued := issued T ∪₁ eq w |})
        as A2.
      { red. right. splits; simpls.
        eapply issuable_next_w; eauto.
        split; auto. red. split; [split|]; auto. }
      
      apply rel_rmw_step; eauto.
      red. left. simpls. splits; auto.
      red. split; [split|]; auto. left. left.
      split; auto. by right. }
    assert (issued T e) as ISS.
    { eapply w_coverable_issued; eauto. by split. }
    destruct (classic (Rel e)) as [REL|NREL].
    { exfalso. apply NEXT. apply RELCOV. split; [split|]; auto. }
    destruct (classic (codom_rel rmw e)) as [RMW|NRMW].
    2: { eexists. eexists. eapply rlx_write_cover_step; eauto.
         eapply itrav_step_more.
         4: by eauto.
         { done. }
         { apply same_tc_Reflexive. }
         red. rewrite COVEQ. rewrite ISSEQ. by split. }
    exfalso. apply NEXT.
    destruct RMW as [r RMW].
    apply (RMWCOV _ _ RMW). eapply COV.
    eexists. apply seq_eqv_r. split; eauto.
      by apply WF.(rmw_in_sb). }
  assert (is_w lab e) as WW by apply ISS.
  destruct (classic (Rel e)) as [REL|NREL].
  2: { eexists; eexists. eapply rlx_write_promise_step; eauto.
       eapply itrav_step_more.
       4: by eauto.
       { done. }
       { apply same_tc_Reflexive. }
       red. rewrite COVEQ. rewrite ISSEQ. by split. }
  eexists; eexists.
  apply rel_write_step; eauto.
  { intros [r RMW]. apply NISS.
    eapply w_covered_issued; eauto. split; auto.
    apply (RMWCOV _ _ RMW).
    red in ISS. eapply ISS.
    eexists. apply seq_eqv_r. split; eauto.
    red. repeat left. apply seq_eqv_r. split.
    { by apply rmw_in_sb. }
      by split. }
  { eapply itrav_step_more; eauto.
    { apply same_tc_Reflexive. }
    red. rewrite COVEQ. rewrite ISSEQ. by split. }
  eapply itrav_step_more with (y0:= mkTC (covered T) (issued T ∪₁ eq e)); eauto.
  { red; eauto. }
  { apply same_tc_Reflexive. }
  apply w_rel_trav_step; eauto.
  { by split. }
  eapply itrav_step_more with (y1:=T'); eauto.
  { apply same_tc_Reflexive. }
  red. simpls. rewrite COVEQ, ISSEQ. by split.
Qed.

Lemma sim_trav_step_to_step T T' thread
      (TS : isim_trav_step thread T T') :
  exists e T'', itrav_step G sc e T T'' /\ tid e = thread.
Proof. destruct TS; eauto. Qed.

End ExtSimTraversal.
