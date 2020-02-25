From hahn Require Import Hahn.

From imm Require Import Events.
From imm Require Import Execution.
From imm Require Import Execution_eco.
From imm Require Import imm_s.
From imm Require Import imm_s_rfrmw.
From imm Require Import imm_s_hb.
From imm Require Import imm_bob imm_s_ppo.
From imm Require Import CombRelations.
From imm Require Import AuxDef.
Require Import TraversalConfig.
Require Import TraversalConfigAlt.
Require Import Traversal.
Require Import ExtTraversalConfig.
Require Import ExtTraversal.
Require Import ExtTraversalProperties.
Require Import AuxRel AuxRel2.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section ExtSimTraversal.
  Variable G : execution.
  Variable WF : Wf G.
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

Notation "'R_ex'" := (R_ex lab).
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
                   (reserved T ∪₁ eq w ∪₁
                    dom_sb_S_rfrmw G T rfi (eq w)))) :
    ext_isim_trav_step
      (tid w) T (mkETC (mkTC (ecovered T) (eissued T ∪₁ eq w))
                       (reserved T ∪₁ eq w ∪₁
                        dom_sb_S_rfrmw G T rfi (eq w)))

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
                    (reserved T ∪₁ eq w ∪₁
                     dom_sb_S_rfrmw G T rfi (eq w))))
    (TS2 : ext_itrav_step
             G sc w
             (mkETC (mkTC (ecovered T) (eissued T ∪₁ eq w))
                    (reserved T ∪₁ eq w ∪₁
                     dom_sb_S_rfrmw G T rfi (eq w)))
             (mkETC (mkTC (ecovered T ∪₁ eq w) (eissued T ∪₁ eq w))
                    (reserved T ∪₁ eq w ∪₁
                     dom_sb_S_rfrmw G T rfi (eq w)))) :
    ext_isim_trav_step
      (tid w) T (mkETC (mkTC (ecovered T ∪₁ eq w) (eissued T ∪₁ eq w))
                       (reserved T ∪₁ eq w ∪₁
                        dom_sb_S_rfrmw G T rfi (eq w)))

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
                    (reserved T ∪₁ eq w ∪₁
                     dom_sb_S_rfrmw G T rfi (eq w))))
    (TS3 : ext_itrav_step
             G sc w
             (mkETC (mkTC (ecovered T ∪₁ eq r) (eissued T ∪₁ eq w))
                    (reserved T ∪₁ eq w ∪₁
                     dom_sb_S_rfrmw G T rfi (eq w)))
             (mkETC (mkTC (ecovered T ∪₁ eq r ∪₁ eq w) (eissued T ∪₁ eq w))
                    (reserved T ∪₁ eq w ∪₁
                     dom_sb_S_rfrmw G T rfi (eq w)))):
    ext_isim_trav_step
      (tid r) T
      (mkETC (mkTC (ecovered T ∪₁ eq r ∪₁ eq w) (eissued T ∪₁ eq w))
             (reserved T ∪₁ eq w ∪₁
              dom_sb_S_rfrmw G T rfi (eq w)))
.

Definition ext_sim_trav_step T T' :=
  exists thread, ext_isim_trav_step thread T T'.

Lemma exists_ext_sim_trav_step T (ETCCOH : etc_coherent G sc T)
      (WFSC : wf_sc G sc)
      (RELCOV :  W ∩₁ Rel ∩₁ eissued T ⊆₁ ecovered T)
      (RMWCOV : forall r w (RMW : rmw r w), ecovered T r <-> ecovered T w)
      T' (TS : ext_trav_step G sc T T') :
  exists T'', ext_sim_trav_step T T''.
Proof using WF IMMCON.
  assert (tc_coherent G sc (etc_TC T)) as TCCOH.
  { apply ETCCOH. }
  assert (tc_coherent_alt G sc (etc_TC T)) as TCCOHalt.
  { eapply tc_coherent_implies_tc_coherent_alt; eauto. }
  assert (tc_coherent G sc (etc_TC T')) as TCCOH'.
  { destruct TS as [e TS]. apply TS. }
  assert (tc_coherent_alt G sc (etc_TC T')) as TCCOHalt'.
  { eapply tc_coherent_implies_tc_coherent_alt; eauto. }

  assert ((rmw ⨾ rfi)＊ ⨾ ⦗R ∩₁ Acq⦘ ⨾ sb ⊆ sb) as RMWRFI_ACQ_SB.
  { arewrite_id ⦗R ∩₁ Acq⦘. rewrite seq_id_l.
    arewrite (rfi ⊆ sb). rewrite WF.(rmw_in_sb).
    arewrite (sb ⨾ sb ⊆ sb).
    { generalize (@sb_trans G). clear. basic_solver 10. }
    rewrite <- ct_end. apply ct_of_trans. apply sb_trans. }

  assert (forall w,
             dom_rel ((detour ∪ rfe) ⨾ rmw ⨾ ⦗dom_sb_S_rfrmw G T rfi (eq w)⦘) ≡₁ ∅)
    as DRFE_EMP1.
  { ins. split; [|clear; basic_solver].
    unfold Execution.detour, Execution.rfi, Execution.rfe, dom_sb_S_rfrmw.
    unfolder. ins. desf. 
    all: assert (z2 = z) by (eapply WF.(wf_rmw_invf); eauto); subst.
    { assert (z3 = z0); subst; eauto.
      eapply WF.(wf_rff); eauto. }
    assert (x = z0); subst; eauto.
    eapply WF.(wf_rff); eauto. }

  assert
  (forall w,
      dom_rel ((detour ∪ rfe) ⨾ rmw ⨾ ⦗reserved T ∪₁ eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w)⦘) ≡₁
      dom_rel ((detour ∪ rfe) ⨾ rmw ⨾ ⦗reserved T ∪₁ eq w⦘)) as DRFE_EMP.
  { ins. rewrite id_union. rewrite !seq_union_r. rewrite dom_union.
      by rewrite DRFE_EMP1, set_union_empty_r. }
  
  assert (forall w (EW : E w), 
             reserved T ∪₁ eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w) ⊆₁ E) as RED.
  { ins. rewrite WF.(dom_sb_S_rfrmwE). rewrite ETCCOH.(etc_S_in_E).
    generalize EW. clear. basic_solver. }

  assert (forall w,
             dom_rel (sb ⨾ ⦗reserved T ∪₁ eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w)⦘) ≡₁
             dom_rel (sb ⨾ ⦗reserved T ∪₁ eq w⦘)) as RR.
  { ins. split; [|basic_solver 10].
    rewrite !id_union, !seq_union_r, !dom_union.
    unionL.
    1,2: basic_solver.
    unfold dom_sb_S_rfrmw. generalize (@sb_trans G).
    clear. basic_solver 10. }

  assert (forall w, 
             dom_rel (rppo G ⨾ ⦗reserved T ∪₁ eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w)⦘) ≡₁
             dom_rel (rppo G ⨾ ⦗reserved T ∪₁ eq w⦘)) as RR1.
  { split; [|basic_solver 10].
    rewrite !id_union, !seq_union_r, !dom_union.
    unionL.
    1,2: basic_solver.
    unfold dom_sb_S_rfrmw. generalize WF.(rppo_sb_in_rppo).
    arewrite (⦗reserved T⦘ ⊆ ⦗W⦘ ⨾ ⦗reserved T⦘) at 1.
    { generalize (reservedW WF ETCCOH). clear. basic_solver. }
    clear. basic_solver 10. }

  assert (forall e (NISS : ~ eissued T e)
                 (WSBW : dom_rel (⦗W⦘ ⨾ sb ⨾ ⦗eq e⦘) ⊆₁ issued (etc_TC T)),
             dom_rel (sb ⨾ ⦗reserved T ∪₁ eq e⦘) ∩₁
             codom_rel (⦗issued (etc_TC T) ∪₁ eq e⦘ ⨾ rf ⨾ ⦗R_ex⦘ ⨾ rmw) ⊆₁
             reserved T ∪₁ eq e ∪₁ dom_sb_S_rfrmw G T rfi (eq e))
    as RESRES.
  { ins. rewrite id_union, !seq_union_r, dom_union.
    rewrite set_inter_union_l.
    unionL.
    2: { rewrite (dom_r WF.(wf_rmwD)).
         rewrite <- !seqA. rewrite codom_eqv1.
         rewrite <- !set_interA. rewrite set_interC with (s':=W).
         rewrite <- !set_interA. rewrite <- dom_eqv1.
         rewrite WSBW. rewrite ETCCOH.(etc_I_in_S). basic_solver. }
    rewrite id_union, !seq_union_l, codom_union.
    rewrite set_inter_union_r.
    unionL.
    { unionR left -> left.
      etransitivity; [|by apply ETCCOH.(etc_sb_S)].
      unfold dom_sb_S_rfrmw. by rewrite !seqA. }
    unionR right.
    unfold dom_sb_S_rfrmw.
    rewrite rfi_union_rfe.
    rewrite !seq_union_l, !seq_union_r, codom_union.
    rewrite set_inter_union_r.
    unionL.
    { arewrite_id ⦗R_ex⦘. by rewrite seq_id_l. }
    rewrite set_interC.
    arewrite (codom_rel (⦗eq e⦘ ⨾ rfe ⨾ ⦗R_ex⦘ ⨾ rmw) ∩₁ dom_rel (sb ⨾ ⦗reserved T⦘) ⊆₁ ∅).
    2: basic_solver.
    apply seq_codom_dom_inter_iff.
    split; [|clear; basic_solver].
    rewrite !seqA.
    arewrite (⦗reserved T⦘ ⊆ ⦗W⦘ ⨾ ⦗reserved T⦘).
    { generalize (reservedW WF ETCCOH). basic_solver. }
    rewrite WF.(rmw_in_sb).
    arewrite (sb ⨾ sb ⊆ sb).
    { generalize (@sb_trans G). clear. basic_solver. }
    sin_rewrite R_ex_sb_W_in_rppo.
    arewrite (rfe ⨾ rppo G ⨾ ⦗reserved T⦘ ⊆ ⦗eissued T⦘ ⨾ rfe ⨾ rppo G ⨾ ⦗reserved T⦘).
    2: { generalize NISS. clear. basic_solver. }
    apply dom_rel_helper_in.
    eapply dom_rfe_rppo_S_in_I; eauto. }

  destruct TS as [e TS].
  cdes TS. desf.
  3: { eexists. eexists. eapply ext_reserve_trav_step.
       eapply ext_itrav_step_more; eauto.
       { apply same_etc_Reflexive. }
       red. unfold ecovered, eissued. by simpls; splits; symmetry. }

  { assert (dom_rel (sb ⨾ ⦗eq e⦘) ⊆₁ covered (etc_TC T)) as SBE.
    { set (AA:=TCCOHalt').
      apply tc_sb_C in AA.
      unfold ecovered in *. rewrite COVEQ in AA.
      rewrite id_union in AA. rewrite seq_union_r in AA.
      rewrite dom_union in AA.
      apply set_subset_union_l in AA. destruct AA as [_ AA].
      clear -AA. unfolder in *. ins. desf.
      edestruct AA.
      { eauto. }
      { done. }
      subst. exfalso. eapply sb_irr; eauto. }

    assert (coverable G sc (etc_TC T) e) as COVERABLEE.
    { eapply coverable_add_eq_iff; eauto.
      apply covered_in_coverable.
      2: basic_solver.
      eapply tc_coherent_more.
      2: by apply TCCOH'.
      red. simpls. unfold eissued, ecovered in *. by split; symmetry. }

    destruct (lab_rwf lab e) as [RE|[WE|FE]].
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
      destruct RMW as [w RMW].
      assert (~ ecovered T w) as COVW.
      { intros WCOV. apply NCOV. apply ETCCOH in WCOV.
        apply WCOV. eexists. apply seq_eqv_r. split; eauto.
          by apply rmw_in_sb. }
      assert (is_w lab w) as WW.
      { apply (dom_r WF.(wf_rmwD)) in RMW.
        apply seq_eqv_r in RMW. desf. }

      assert (dom_rel (sb ⨾ ⦗eq w⦘) ⊆₁ ecovered T ∪₁ eq e) as SBW.
      { hahn_rewrite (rmw_from_non_init WF) in RMW.
        hahn_rewrite WF.(wf_rmwi) in RMW.
        hahn_rewrite (sb_immediate_adjacent WF) in RMW.
        unfold adjacent in *; unfolder in *; ins; desf.
        apply LA_ca in H; desf; eauto.
        eapply tc_sb_C with (T:=mkTC (ecovered T ∪₁ eq e) (eissued T)).
        2: by unfolder; ins; eauto 10.
        eapply tc_coherent_implies_tc_coherent_alt; eauto.
        eapply tc_coherent_more.
        2: by apply ETCCOH'.
        destruct T'; simpls. }

      assert (E e /\ E w) as [ER EW].
      { apply WF.(wf_rmwE) in RMW.
        apply seq_eqv_lr in RMW. desf. }
      assert (W_ex w) as WEXW.
      { red. basic_solver. }
      assert (~ (ecovered T ∪₁ eq e) w) as C1.
      { intros [H|H]; desf. type_solver. }

      assert (ext_itrav_step
                G sc e T
                (mkETC (mkTC (ecovered T ∪₁ eq e) (eissued T))
                       (reserved T))) as ST1.
      { red. splits; eauto.
        eapply etc_coherent_more; eauto.
        red. unfold ecovered, eissued in *. simpls.
        splits; by symmetry. }

      destruct (classic (eissued T w)) as [ISS|NISS].
      { eexists; eexists.
        eapply ext_rlx_rmw_cover_step; eauto.
        { intros REL. apply COVW. apply RELCOV.
            by split; [split|]. }
        red. splits; eauto.
        (* TODO: introduce a lemma. *)
        constructor; unfold ecovered, eissued; simpls.
        all: try apply ETCCOH.
        2: by unionR left -> left; apply ETCCOH.
        eapply trav_step_coherence.
        2: apply ETCCOH'.
        red. exists w.
        red. unnw. left; simpls.
        rewrite COVEQ, ISSEQ.
        unfold ecovered, eissued in *.
        splits; simpls.
        { intros HH. apply COVEQ in HH. red in HH. desf. }
        red. split; [split|]; auto.
        { red. by rewrite COVEQ. }
        do 2 left. split.
        2: by apply ISSEQ.
        eapply issuedW with (T:=etc_TC T); eauto. }

      assert (dom_rel (⦗FW⦘ ⨾ sb ⨾ ⦗eq w⦘) ⊆₁ covered (etc_TC T)) as FWSBW.
      { rewrite dom_eqv1. rewrite SBW; unfold ecovered.
        arewrite (eq e ⊆₁ R) by basic_solver.
        type_solver. }

      assert (dom_rel (⦗W⦘ ⨾ sb ⨾ ⦗eq w⦘) ⊆₁ issued (etc_TC T)) as WSBW.
      { rewrite <- seq_eqvK, !seqA, dom_eqv1.
        arewrite (W ⊆₁ FW) at 2. rewrite FWSBW.
        rewrite set_interC. eapply tc_W_C_in_I; eauto. }

      assert (dom_rel (rf ⨾ sb ⨾ ⦗eq w⦘) ⊆₁ issued (etc_TC T)) as RFSB.
      { rewrite <- ISSEQ.
        etransitivity.
        2: eapply tc_rf_C; eauto.
        unfolder. ins. desf.
        eexists. splits; eauto.
        eapply COVEQ. apply SBW. basic_solver 10. }

      assert (dom_rel (detour ⨾ sb ⨾ ⦗eq w⦘) ⊆₁ issued (etc_TC T)) as AA'.
      { rewrite (dom_l WF.(wf_detourD)), !seqA.
        rewrite detour_in_sb.
        arewrite (sb ⨾ sb ⊆ sb) by (generalize (@sb_trans G); basic_solver). }
      
      assert (dom_rel ((detour ∪ rfe) ⨾ sb ⨾ ⦗eq w⦘) ⊆₁ issued (etc_TC T)) as AA.
      { rewrite !seq_union_l, dom_union. unionL; auto. by arewrite (rfe ⊆ rf). }
      
      assert (dom_rel ((detour ∪ rfe) ⨾ rmw ⨾
                       ⦗reserved T ∪₁ eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w)⦘) ⊆₁
              issued (etc_TC T) ∪₁ eq w) as AAH.
      { unionR left. rewrite DRFE_EMP.
        rewrite id_union, !seq_union_r, dom_union.
        unionL; [eby eapply etc_rmw_S|]. by rewrite WF.(rmw_in_sb). }

      assert (sb e w) as SBEW.
      { apply rmw_in_sb; auto. }
      assert (dom_rel (rf ⨾ ⦗eq e⦘) ⊆₁ issued (etc_TC T)) as IRF.
      { rewrite dom_eqv_seq with (r':= sb ⨾ ⦗eq w⦘).
        2: { exists w. apply seq_eqv_r. split; auto. }
        arewrite_id ⦗eq e⦘. by rewrite seq_id_l. }

      assert (dom_rel ((detour ∪ rfe) ⨾ (data ∪ rfi ∪ rmw)＊ ⨾ rppo G ⨾ ⦗reserved T ∪₁ eq w⦘)
                      ⊆₁ issued (etc_TC T) /\
              (* dom_rel (⦗W_ex⦘ ⨾ sb ⨾ ⦗reserved T ∪₁ eq w⦘) ⊆₁ reserved T /\ *)
              dom_rel (⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗reserved T ∪₁ eq w⦘) ⊆₁ issued (etc_TC T) /\
              dom_rel ((detour ∪ rfe) ⨾ (rmw ⨾ rfi)＊ ⨾
                                      ⦗R ∩₁ Acq⦘ ⨾ sb ⨾ ⦗reserved T ∪₁ eq w⦘)
                      ⊆₁ issued (etc_TC T)) as [PP0 [PP2 PP3]].
      { splits.
        all: rewrite id_union, !seq_union_r, dom_union; unionL.
        all: try by apply ETCCOH.
        { arewrite ((data ∪ rfi ∪ rmw)＊ ⨾ rppo G ⊆ sb); [|done].
          arewrite (rfi ⊆ sb). rewrite WF.(rmw_in_sb).
          rewrite WF.(data_in_sb), !unionK.
          rewrite rppo_in_sb.
          rewrite rt_of_trans.
          all: generalize (@sb_trans G); auto.
          basic_solver 10. }
(*         { rewrite <- etc_I_in_S; eauto; rewrite WF.(W_ex_in_W); auto. } *)
        { arewrite (W_ex_acq ⊆₁ W); auto.
          rewrite WF.(W_ex_in_W); basic_solver. }
          by sin_rewrite RMWRFI_ACQ_SB. }
      assert (dom_rel (⦗F ∩₁ Acq/Rel⦘ ⨾ sb ⨾ ⦗reserved T ∪₁ eq w⦘) ⊆₁
                      covered (etc_TC T)) as PP5.
      { rewrite id_union, !seq_union_r, dom_union. unionL.
        { apply ETCCOH. }
        arewrite (F ∩₁ Acq/Rel ⊆₁ FW); [|done].
        type_solver. }

      assert (codom_rel (⦗issued (etc_TC T)⦘ ⨾ rf ⨾ rmw) w) as [wprev RFRMW].
      { cdes IMMCON. red in Comp. specialize (Comp e).
        assert (E e /\ R e) as ERE by (by split).
        apply Comp in ERE. destruct ERE as [wprev ERE].
        exists wprev.
        apply seq_eqv_l. split.
        2: by exists e; split.
        apply ISSEQ.
        eapply tc_rf_C with (T:=etc_TC T').
        { eapply tc_coherent_implies_tc_coherent_alt; eauto. }
        eexists. apply seq_eqv_r. split; eauto.
        apply COVEQ. by right. }

      assert (dom_sb_S_rfrmw G (mkETC (etc_TC T) (reserved T ∪₁ eq w)) (rf ⨾ ⦗R_ex⦘)
                             (issued (etc_TC T)) ⊆₁ reserved T ∪₁ eq w) as DD.
      { unfold dom_sb_S_rfrmw. simpls.
        rewrite id_union, !seq_union_r, dom_union.
        rewrite set_inter_union_l.
        rewrite ETCCOH.(etc_sb_S).
        unionL; [basic_solver|].
        rewrite (dom_r WF.(wf_rmwD)).
        rewrite <- !seqA. rewrite codom_eqv1.
        rewrite <- !set_interA. rewrite set_interC with (s':=W).
        rewrite <- !set_interA. rewrite <- dom_eqv1.
        rewrite WSBW. rewrite ETCCOH.(etc_I_in_S). basic_solver. }

      destruct (classic (reserved T w)) as [RES|NRES].
      2: { eexists. red. eexists.
           apply ext_reserve_trav_step.
           red. splits.
           { do 2 right. splits; eauto. }
           constructor; auto.
           all: unfold eissued, ecovered; simpls.
           { unionL; [by apply ETCCOH|]. basic_solver. }
           { rewrite ETCCOH.(etc_I_in_S). eauto with hahn. }
           { rewrite set_minus_union_l. rewrite ETCCOH.(etc_S_I_in_W_ex).
             basic_solver. }
           { rewrite id_union, !seq_union_r, dom_union.
             unionL; [by apply ETCCOH|]. by rewrite WF.(rmw_in_sb). }
           rewrite set_inter_union_l. unionL; [by apply ETCCOH|].
           generalize RFRMW. clear. basic_solver 10. }

      assert
      (dom_rel ((⦗W⦘ ⨾ (ar G sc ∪ rf ⨾ ppo ∩ same_loc)⁺) ⨾ ⦗eq w⦘) ⊆₁ issued (etc_TC T))
        as PP4.
      { rewrite ct_end.
        rewrite !seq_union_r, !seq_union_l, dom_union, !seqA.
        unionL.
        2: { arewrite (ppo ∩ same_loc ⊆ ppo) at 2.
             rewrite WF.(ppo_in_sb) at 2.
             rewrite (dom_rel_helper RFSB).
             rewrite <- !seqA. do 3 rewrite dom_seq.
             rewrite !seqA.
               by apply ar_rf_ppo_loc_rt_I_in_I. }
        arewrite (⦗eq w⦘ ⊆ ⦗W⦘ ⨾ ⦗eq w⦘) by basic_solver.
        sin_rewrite ar_W_in_ar_int; auto.
        rewrite ar_int_in_sb; auto.
        arewrite (sb ⨾ ⦗eq w⦘ ⊆ ⦗coverable G sc (etc_TC T)⦘ ⨾ sb ⨾ ⦗eq w⦘).
        { apply dom_rel_helper.
          rewrite SBW.
          unfold ecovered. rewrite covered_in_coverable; eauto.
          unionL; auto.
          red. by ins; subst. }
        rewrite <- !seqA. do 2 rewrite dom_seq. rewrite !seqA.
          by apply ar_rf_ppo_loc_rt_coverable_in_I. }
      
      assert (covered (etc_TC T) ⊆₁ coverable G sc (mkTC (covered (etc_TC T))
                                                         (issued (etc_TC T) ∪₁ eq w)))
        as COVCOV.
      { etransitivity.
        2: { eapply traversal_mon with (T:=etc_TC T); basic_solver. }
        apply ETCCOH. }

      assert (forall C' (CC : (C' = covered (etc_TC T) /\ issuable G sc (etc_TC T) w) \/
                              C' = covered (etc_TC T) ∪₁ eq e),
        etc_coherent G sc
                     (mkETC (mkTC C' (issued (etc_TC T) ∪₁ eq w))
                            (reserved T ∪₁ eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w))))
        as COHSTEP1.
      { constructor; unfold eissued, ecovered; simpls.
        { red. splits; simpls.
          { desf; [|unionR left]; apply ETCCOH. }
          { desf. unionL.
            { etransitivity.
              2: eapply traversal_mon.
              { apply ETCCOH. }
              all: basic_solver. }
            intros x HH; subst.
            red; simpls. split.
            { split; auto.
              red. rewrite SBE. eauto with hahn. }
            left. right. split; auto.
            red. rewrite IRF. eauto with hahn. }
          desf.
          { etransitivity.
            2: { eapply traversal_mon with (T:=etc_TC T); basic_solver. }
            unionL; auto; [apply ETCCOH|basic_solver]. }
          unionL.
          { etransitivity.
            2: eapply traversal_mon.
            { apply ETCCOH. }
            all: basic_solver. }
          intros x HH; subst.
          red; simpls. unfold set_inter. splits; auto; red.
          { by rewrite fwbob_in_sb. }
          rewrite PP4. eauto with hahn. }
        { by apply RED. }
        { rewrite ETCCOH.(etc_I_in_S). clear. basic_solver. }
        { rewrite dom_sb_S_rfrmw_in_W_ex.
          rewrite !set_minus_union_l. unionL.
          2,3: basic_solver.
          generalize ETCCOH.(etc_S_I_in_W_ex). clear. unfold eissued. basic_solver 10. }
        { desf; try unionR left.
          all: by rewrite dom_eqv1; rewrite RR; rewrite <- dom_eqv1. }
        2: by rewrite dom_eqv1; rewrite RR; rewrite <- dom_eqv1; try unionR left.
        { do 2 rewrite <- seqA. rewrite <- dom_rel_eqv_dom_rel, RR.
          rewrite dom_rel_eqv_dom_rel, !seqA. by unionR left. }
        { unfold dom_sb_S_rfrmw. simpls.
          rewrite RR. rewrite seqA. by apply RESRES. }
        { rewrite <- seqA. rewrite <- dom_rel_eqv_dom_rel, RR1.
          rewrite dom_rel_eqv_dom_rel, seqA. by unionR left. }
        { by arewrite (detour ⊆ detour ∪ rfe). }
        rewrite !set_inter_union_l. unionL.
        { rewrite ETCCOH.(etc_S_W_ex_rfrmw_I). clear. basic_solver 10. }
        { generalize RFRMW. clear. basic_solver 10. }
        unfold dom_sb_S_rfrmw. arewrite (rfi ⊆ rf). basic_solver 10. }

      destruct (classic (Rel w)) as [REL|NREL].
      2: { assert (issuable G sc (etc_TC T) w) as WISS.
           { red. unfold set_inter. splits; auto; red.
             arewrite
               (fwbob ⨾ ⦗eq w⦘ ⊆
                      (⦗W ∩₁ Rel⦘ ⨾ sb ∩ same_loc ⨾ ⦗W⦘ ∪ ⦗F ∩₁ Acq/Rel⦘ ⨾ sb) ⨾ ⦗eq w⦘).
             { unfold imm_bob.fwbob. rewrite !seq_union_l, !seqA.
               unionL; eauto 10 with hahn.
               all: type_solver. }
             arewrite ((⦗W ∩₁ Rel⦘ ⨾ sb ∩ same_loc ⨾ ⦗W⦘ ∪ ⦗F ∩₁ Acq/Rel⦘ ⨾ sb) ⊆ ⦗FW⦘ ⨾ sb).
             2: done.
             basic_solver. }
           eexists; eexists.
           eapply ext_rlx_write_promise_step; eauto.
           red. unfold ecovered, eissued in *.
           splits; eauto 10; simpls. }

      eexists; eexists.
      eapply ext_rel_rmw_step; eauto.
      { red. unfold ecovered, eissued; simpls; splits.
        { right. left. splits; auto. }
        eapply COHSTEP1. eauto. }
      red; unfold ecovered, eissued; simpls.
      splits; eauto.
      constructor; unfold eissued, ecovered; simpls.
      { red. simpls; splits.
        { unionR left -> left. apply ETCCOH. }
        { unionL.
          { etransitivity.
            2: eapply traversal_mon.
            { apply ETCCOH. }
            all: basic_solver. }
          all: intros x HH; subst.
          all: red; simpls; split; [split; auto; red|].
          { rewrite SBE. eauto with hahn. }
          { left. right. split; auto.
            red. rewrite IRF. eauto with hahn. }
          { rewrite SBW. eauto with hahn. }
          do 2 left. split; auto. by right. }
        unionL.
        { etransitivity.
          2: eapply traversal_mon.
          { apply ETCCOH. }
          all: basic_solver. }
        intros x HH; subst.
        red; simpls. unfold set_inter. splits; auto; red.
        { rewrite fwbob_in_sb. rewrite SBW. eauto with hahn. }
        rewrite PP4. eauto with hahn. }
      { by apply RED. }
      { rewrite ETCCOH.(etc_I_in_S). clear. basic_solver. }
      { rewrite dom_sb_S_rfrmw_in_W_ex.
        rewrite !set_minus_union_l. unionL.
        2,3: basic_solver.
        generalize ETCCOH.(etc_S_I_in_W_ex). clear. unfold eissued. basic_solver 10. }
      { unionR left -> left.
        all: by rewrite dom_eqv1; rewrite RR; rewrite <- dom_eqv1. }
      2: by rewrite dom_eqv1; rewrite RR; rewrite <- dom_eqv1; try unionR left.
      { do 2 rewrite <- seqA. rewrite <- dom_rel_eqv_dom_rel, RR.
        rewrite dom_rel_eqv_dom_rel, !seqA. by unionR left. }
      { unfold dom_sb_S_rfrmw. simpls.
        rewrite RR. rewrite !seqA. by apply RESRES. }
      { rewrite <- seqA. rewrite <- dom_rel_eqv_dom_rel, RR1.
        rewrite dom_rel_eqv_dom_rel, seqA. by unionR left. }
      { by arewrite (detour ⊆ detour ∪ rfe). }
      rewrite !set_inter_union_l. unionL.
      { rewrite ETCCOH.(etc_S_W_ex_rfrmw_I). clear. basic_solver 10. }
      { generalize RFRMW. clear. basic_solver 10. }
      unfold dom_sb_S_rfrmw. arewrite (rfi ⊆ rf). basic_solver 10. }

    assert (E e) as EE.
    { eapply tc_C_in_E.
      2: { apply COVEQ. basic_solver. }
      eauto. }
    assert (eissued T e) as ISS.
    { apply ISSEQ. eapply tc_W_C_in_I; eauto.
      split; auto. apply COVEQ. basic_solver. }
    assert (coverable G sc (etc_TC T) e) as COVERE.
    { red. unfold set_inter. splits; auto.
      do 2 left. split; auto. }
    destruct (classic (Rel e)) as [REL|NREL].
    { exfalso. apply NCOV. apply RELCOV. split; [split|]; auto. }
    destruct (classic (codom_rel rmw e)) as [RMW|NRMW].
    2: { eexists. eexists. eapply ext_rlx_write_cover_step; eauto.
         eapply ext_itrav_step_more.
         4: by eauto.
         { done. }
         { apply same_etc_Reflexive. }
         red. rewrite COVEQ. rewrite ISSEQ. splits; simpls. by symmetry. }
    exfalso. apply NCOV.
    destruct RMW as [r RMW].
    apply (RMWCOV _ _ RMW). eapply SBE.
    eexists. apply seq_eqv_r. split; eauto.
      by apply WF.(rmw_in_sb). }

  assert (is_w lab e) as WW.
  { eapply issuedW.
    2: { apply ISSEQ. basic_solver. }
    eauto.  }
  assert (issuable G sc (etc_TC T') e) as ISS'.
  { eapply issued_in_issuable; eauto. apply ISSEQ. basic_solver. }
  assert (issuable G sc (etc_TC T) e) as ISS.
  { eapply issuable_add_eq_iff; eauto.
    eapply issuable_more; eauto.
    unfold ecovered, eissued in *.
    red. simpls. splits; by symmetry. }

  assert (~ covered (etc_TC T) e) as NCOV.
  { intros AA. apply NISS. eapply tc_W_C_in_I; eauto. by split. }

  destruct (classic (Rel e)) as [REL|NREL].
  2: { eexists; eexists. eapply ext_rlx_write_promise_step; eauto.
       eapply ext_itrav_step_more.
       4: by eauto.
       { done. }
       { apply same_etc_Reflexive. }
       red. rewrite COVEQ. rewrite ISSEQ. splits; simpls. by symmetry. }
  eexists; eexists.
  apply ext_rel_write_step; eauto.
  { intros [r RMW]. apply NISS.
    eapply w_covered_issued; eauto. split; auto.
    apply (RMWCOV _ _ RMW).
    red in ISS. apply COVEQ. eapply ISS'.
    eexists. apply seq_eqv_r. split; eauto.
    red. repeat left. apply seq_eqv_r. split.
    { by apply rmw_in_sb. }
      by split. }
  { eapply ext_itrav_step_more; eauto.
    { apply same_etc_Reflexive. }
    red. rewrite COVEQ. rewrite ISSEQ. splits; simpls. by symmetry. }
  red; unfold eissued, ecovered; simpls; splits.
  { left. by splits. }

  assert (dom_rel (sb ⨾ ⦗eq e⦘) ⊆₁ covered (etc_TC T)) as SBE.
  { destruct ISS as [[_ ISS] _]. red in ISS.
    arewrite (sb ⨾ ⦗eq e⦘ ⊆ fwbob ⨾ ⦗eq e⦘); auto.
    unfold imm_bob.fwbob.
    basic_solver 10. }
  
  assert (E e) as EE by apply ISS.
  
  assert (coverable G sc (mkTC (covered (etc_TC T)) (issued (etc_TC T) ∪₁ eq e)) e) as CCX.
  { red. split; [split|]; auto.
    do 2 left. split; auto. simpls. basic_solver. }

  assert (dom_rel (⦗W⦘ ⨾ sb ⨾ ⦗eq e⦘) ⊆₁ issued (etc_TC T)) as WSBW.
  { rewrite dom_eqv1. rewrite SBE.
    rewrite set_interC. eapply tc_W_C_in_I; eauto. }

  assert (dom_rel (rf ⨾ sb ⨾ ⦗eq e⦘) ⊆₁ issued (etc_TC T)) as RFSB.
  { etransitivity.
    2: eapply tc_rf_C; eauto.
    unfolder. ins. desf.
    eexists. splits; eauto.
    apply SBE. basic_solver 10. }

  assert (dom_rel ((detour ∪ rfe) ⨾ sb ⨾ ⦗eq e⦘) ⊆₁ issued (etc_TC T)) as DRFSB.
  { rewrite !seq_union_l, dom_union. unionL.
    2: by arewrite (rfe ⊆ rf).
    rewrite (dom_l WF.(wf_detourD)), !seqA.
    rewrite detour_in_sb.
    arewrite (sb ⨾ sb ⊆ sb) by (generalize (@sb_trans G); basic_solver). }

  assert (dom_rel ((detour ∪ rfe) ⨾ rmw ⨾ ⦗reserved T ∪₁ eq e⦘) ⊆₁ issued (etc_TC T))
    as DRFSBE.
  { rewrite id_union, !seq_union_r, dom_union.
    unionL.
    { eby eapply etc_rmw_S. }
      by rewrite WF.(rmw_in_sb). }

  constructor; unfold eissued, ecovered; simpls.
  { red. splits; simpls.
    { etransitivity.
      { apply TCCOH. }
      eauto with hahn. }
    { unionL.
      { etransitivity.
        2: { eapply traversal_mon with (T:=etc_TC T); basic_solver. }
        apply ETCCOH. }
      red. ins; desf.
      apply coverable_add_eq_iff
        with (T := mkTC (covered (etc_TC T)) (issued (etc_TC T) ∪₁ eq x)); auto. }
    unionL.
    { etransitivity.
      2: { eapply traversal_mon; basic_solver. }
      apply ETCCOH. }
    red. ins. desf.
    eapply traversal_mon with (T:=etc_TC T); basic_solver. }
  { by apply RED. }
  { unionL; [by unionR left -> left; apply ETCCOH|]. basic_solver. }
  { rewrite dom_sb_S_rfrmw_in_W_ex.
    rewrite !set_minus_union_l. unionL.
    3: basic_solver.
    { generalize ETCCOH.(etc_S_I_in_W_ex). clear. unfold eissued. basic_solver 10. }
    unfolder. intros x [AA HH]. exfalso. apply HH. eauto. }
  { unionR left.
    rewrite dom_eqv1. rewrite RR. rewrite <- dom_eqv1.
    rewrite id_union, !seq_union_r, dom_union; unionL; [by apply ETCCOH|].
    arewrite_id ⦗F ∩₁ Acq/Rel⦘. by rewrite seq_id_l. }
  { unionR left.
    do 2 rewrite <- seqA. rewrite <- dom_rel_eqv_dom_rel, RR.
    rewrite dom_rel_eqv_dom_rel, seqA.
    rewrite id_union, !seq_union_r, dom_union, !seqA.
    unionL; [by apply ETCCOH|]. by sin_rewrite RMWRFI_ACQ_SB. }
  { unfold dom_sb_S_rfrmw. simpls.
    rewrite dom_eqv1; rewrite RR. rewrite <- dom_eqv1. unionR left.
    rewrite id_union, !seq_union_r, dom_union; unionL; [by apply ETCCOH|].
    arewrite (W_ex_acq ⊆₁ W); auto. rewrite WF.(W_ex_in_W); basic_solver. }
  { unfold dom_sb_S_rfrmw. simpls.
    rewrite RR. rewrite !seqA. by apply RESRES. }
  { rewrite <- seqA. rewrite <- dom_rel_eqv_dom_rel, RR1.
    rewrite dom_rel_eqv_dom_rel, seqA.
    unionR left.
    rewrite id_union, !seq_union_r, dom_union; unionL; [by apply ETCCOH|].
    arewrite ((data ∪ rfi ∪ rmw)＊ ⨾ rppo G ⊆ sb); [|done].
    arewrite (rfi ⊆ sb). rewrite WF.(rmw_in_sb).
    rewrite WF.(data_in_sb), !unionK.
    rewrite WF.(rppo_in_sb).
    rewrite rt_of_trans.
    all: generalize (@sb_trans G); auto.
    basic_solver 10. }
  { arewrite (detour ⊆ detour ∪ rfe). rewrite DRFE_EMP. by unionR left. }
  rewrite !set_inter_union_l. unionL.
  { rewrite ETCCOH.(etc_S_W_ex_rfrmw_I). clear. basic_solver 10. }
  { rewrite <- ISSEQ.
    arewrite (eq e ∩₁ W_ex ⊆₁ codom_rel (rf ⨾ rmw ⨾ ⦗eissued T'⦘)).
    { intros x [AA [e' WEX]]; subst.
      rename e' into e. rename x into w.
      cdes IMMCON. red in Comp. specialize (Comp e).
      assert (E e /\ R e) as ERE.
      { set (CC:=WEX).
        apply WF.(wf_rmwE) in CC. destruct_seq CC as [CC1 CC2].
        apply WF.(wf_rmwD) in CC. destruct_seq CC as [CC3 CC4].
        split; auto. }
      apply Comp in ERE. destruct ERE as [wprev ERE].
      exists wprev. apply seqA.
      apply seq_eqv_r. split.
      { by exists e; split. }
      apply ISSEQ. by right. }
    arewrite (codom_rel (rf ⨾ rmw ⨾ ⦗eissued T'⦘) ⊆₁ codom_rel (⦗eissued T'⦘ ⨾ rf ⨾ rmw ⨾ ⦗eissued T'⦘)).
    2: basic_solver 10.
    apply codom_rel_mori.
    apply dom_rel_helper.
    eapply rfrmw_I_in_I; eauto. }
  unfold dom_sb_S_rfrmw. arewrite (rfi ⊆ rf). basic_solver 10.
Qed.

Lemma ext_sim_trav_step_to_step T T' thread
      (TS : ext_isim_trav_step thread T T') :
  exists e T'', ext_itrav_step G sc e T T'' /\ tid e = thread.
Proof using. destruct TS; eauto. Qed.

End ExtSimTraversal.
