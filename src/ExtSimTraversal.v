From hahn Require Import Hahn.

From imm Require Import Events.
From imm Require Import Execution.
From imm Require Import Execution_eco.
From imm Require Import imm_s.
From imm Require Import imm_s_hb.
From imm Require Import imm_common.
From imm Require Import CombRelations.
From imm Require Import TraversalConfig.
From imm Require Import TraversalConfigAlt.
From imm Require Import Traversal.
Require Import ExtTraversal.
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

(* TODO: move to imm/TraveralConfig.v *)
Lemma coverable_add_eq_iff T (WFSC : wf_sc G sc) e:
  coverable G sc T e <-> coverable G sc (mkTC (covered T ∪₁ eq e) (issued T)) e.
Proof.
  split.
  { eapply traversal_mon; simpls. eauto with hahn. }
  unfold coverable; simpls. 
  intros [[EE COVE] HH].
  split.
  { clear HH. split; auto.
    unfolder in *. ins. desf.
    edestruct COVE.
    { eexists; eauto. }
    { done. }
    exfalso. desf. eapply sb_irr; eauto. }
  destruct HH as [[HH|HH]|[AA HH]]; [do 2 left| left;right|right]; auto.
  split; auto.
  unfolder in *. ins. desf. edestruct HH.
  { eexists; eauto. }
  { done. }
  exfalso. desf. eapply sc_irr; eauto.
Qed.

(* TODO: move to imm/TraveralConfig.v *)
Lemma issuable_add_eq_iff T e :
  issuable G T e <-> issuable G (mkTC (covered T) (issued T ∪₁ eq e)) e.
Proof.
  cdes IMMCON.
  split.
  { eapply traversal_mon; simpls. eauto with hahn. }
  unfold issuable; simpls. 
  intros [[EE ISSE] HH].
  unfold dom_cond in *.
  split; [split|]; auto.
  all: intros x BB; set (CC:=BB).
  2: apply HH in CC.
  apply ISSE in CC.
  all: destruct CC; desf.
  all: exfalso; clear -BB WF Cext.
  all: unfolder in *; desf.
  5: by eapply sb_irr; eauto.
  all: eapply Cext.
  all: apply ct_unit; eexists; split; [apply ct_step|]; unfold ar, ar_int; basic_solver 10.
Qed.

(* TODO: move to ExtTraversal.v *)
Lemma ext_trav_step_in_trav_step (WFSC : wf_sc G sc) :
  ext_trav_step G sc ⊆ etc_TC ⋄ (same_trav_config ∪ trav_step G sc).
Proof.
  unfold ext_trav_step, ext_itrav_step, map_rel.
  intros T T'. ins. desf.
  3: { left. red. by split; symmetry. }
  all: right; exists e; red; unnw.
  all: unfold ecovered, eissued in *.
  2: right.
  left.
  all: splits; auto.
  { apply coverable_add_eq_iff; auto.
    apply covered_in_coverable; [|basic_solver].
    eapply tc_coherent_more.
    4: apply ETCCOH'.
    1,2: done.
    red; splits; simpls; by symmetry. }
  apply issuable_add_eq_iff; auto. 
  eapply issued_in_issuable; [|basic_solver].
  eapply tc_coherent_more.
  4: apply ETCCOH'.
  1,2: done.
  red; splits; simpls; by symmetry.
Qed.

Lemma exists_ext_sim_trav_step T (ETCCOH : etc_coherent G sc T)
      (WFSC : wf_sc G sc)
      (RELCOV :  W ∩₁ Rel ∩₁ eissued T ⊆₁ ecovered T)
      (RMWCOV : forall r w (RMW : rmw r w), ecovered T r <-> ecovered T w)
      T' (TS : ext_trav_step G sc T T') :
  exists T'', ext_sim_trav_step T T''.
Proof.
  assert (tc_coherent G sc (etc_TC T)) as TCCOH.
  { apply ETCCOH. }
  assert (tc_coherent_alt G sc (etc_TC T)) as TCCOHalt.
  { eapply tc_coherent_implies_tc_coherent_alt; eauto. }
  assert (tc_coherent_alt G sc (etc_TC T')) as TCCOHalt'.
  { eapply tc_coherent_implies_tc_coherent_alt; eauto.
    destruct TS as [e TS]. apply TS. }

  destruct TS as [e TS].
  cdes TS. desf.
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
        4: by apply ETCCOH'.
        1,2: done.
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
        eapply issuedW; eauto. }

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
      
      assert (dom_rel ((detour ∪ rfe) ⨾ sb ⨾ ⦗eq w⦘) ⊆₁ issued (etc_TC T)) as AA.
      { rewrite !seq_union_l, dom_union. unionL.
        2: by arewrite (rfe ⊆ rf).
        rewrite (dom_l WF.(wf_detourD)), !seqA.
        rewrite detour_in_sb.
        arewrite (sb ⨾ sb ⊆ sb) by (generalize (@sb_trans G); basic_solver). }

      assert (sb e w) as SBEW.
      { apply rmw_in_sb; auto. }
      assert (dom_rel (rf ⨾ ⦗eq e⦘) ⊆₁ issued (etc_TC T)) as IRF.
      { rewrite dom_eqv_seq with (r':= sb ;; <|eq w|>).
        2: { exists w. apply seq_eqv_r. split; auto. }
        arewrite_id ⦗eq e⦘. by rewrite seq_id_l. }

      assert (dom_rel ((detour ∪ rfe) ⨾ (data ∪ rfi)＊ ⨾ rppo G ⨾ ⦗reserved T ∪₁ eq w⦘)
                      ⊆₁ issued (etc_TC T) /\
              dom_rel (⦗W_ex⦘ ⨾ sb ⨾ ⦗reserved T ∪₁ eq w⦘) ⊆₁ reserved T /\
              dom_rel (⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗reserved T ∪₁ eq w⦘) ⊆₁ issued (etc_TC T) /\
              dom_rel ((detour ∪ rfe) ⨾ ⦗R ∩₁ Acq⦘ ⨾ sb ⨾ ⦗reserved T ∪₁ eq w⦘)
                      ⊆₁ issued (etc_TC T)) as [PP0 [PP1 [PP2 PP3]]].
      { splits.
        all: rewrite id_union, !seq_union_r, dom_union; unionL.
        all: try by apply ETCCOH.
        { arewrite ((data ∪ rfi)＊ ⨾ rppo G ⊆ sb); [|done].
          arewrite (rfi ⊆ sb).
          rewrite WF.(data_in_sb), unionK.
          rewrite rppo_in_sb.
          rewrite rt_of_trans.
          all: generalize (@sb_trans G); auto.
          basic_solver 10. }
        { rewrite <- etc_I_in_S; eauto; rewrite WF.(W_ex_in_W); auto. }
        { arewrite (W_ex_acq ⊆₁ W); auto. rewrite WF.(W_ex_in_W); basic_solver. }
        arewrite_id ⦗R ∩₁ Acq⦘. by rewrite seq_id_l. }

      destruct (classic (reserved T w)) as [RES|NRES].
      2: { eexists. red. eexists.
           apply ext_reserve_trav_step.
           red. splits.
           { do 2 right. splits; eauto. }

           constructor.
           { apply ETCCOH. }
           all: unfold eissued, ecovered; simpls.
           { rewrite ETCCOH.(etc_I_in_S). eauto with hahn. }
           { rewrite set_minus_union_l. rewrite ETCCOH.(etc_S_I_in_W_ex).
             basic_solver. }
           unionR left; auto. }
      destruct (classic (Rel w)) as [REL|NREL].
      2: { assert (issuable G (etc_TC T) w) as WISS.
           { red. unfold set_inter. splits; auto; red.
             3: { arewrite ((fun x => W_ex x /\ is_xacq lab x) ⊆₁ W). 
                  2: done.
                  generalize WF.(W_ex_in_W). basic_solver. }
             2: { rewrite WF.(ppo_in_sb). rewrite bob_in_sb. by rewrite unionK, !seqA. }
             arewrite
               (fwbob ⨾ ⦗eq w⦘ ⊆
                      (⦗W ∩₁ Rel⦘ ⨾ sb ∩ same_loc ⨾ ⦗W⦘ ∪ ⦗F ∩₁ Acq/Rel⦘ ⨾ sb) ⨾ ⦗eq w⦘).
             { unfold imm_common.fwbob. rewrite !seq_union_l, !seqA.
               unionL; eauto 10 with hahn.
               all: type_solver. }
             arewrite ((⦗W ∩₁ Rel⦘ ⨾ sb ∩ same_loc ⨾ ⦗W⦘ ∪ ⦗F ∩₁ Acq/Rel⦘ ⨾ sb) ⊆ ⦗FW⦘ ⨾ sb).
             2: done.
             basic_solver. }
           eexists; eexists. 
           eapply ext_rlx_write_promise_step; eauto.
           red. unfold ecovered, eissued in *.
           splits; eauto 10; simpls.
           constructor; unfold eissued, ecovered; simpls.
           all: try by (unionR left; auto).
           3: { generalize ETCCOH.(etc_S_I_in_W_ex). basic_solver 10. }
           2: { apply set_union_mori; [|done]. apply ETCCOH. }
           red. splits; simpls.
           { apply ETCCOH. }
           { etransitivity.
             2: { eapply traversal_mon with (T:=etc_TC T); basic_solver. }
             apply ETCCOH. }
           etransitivity.
           2: { eapply traversal_mon with (T:=etc_TC T); basic_solver. }
           unionL; auto; [apply ETCCOH|basic_solver]. }
      eexists; eexists. 
      eapply ext_rel_rmw_step; eauto.
      { red. unfold ecovered, eissued; simpls; splits.
        { right. left. splits; auto. }
        constructor; unfold ecovered, eissued; simpls.
        all: try by (unionR left; auto).
        3: { generalize ETCCOH.(etc_S_I_in_W_ex). basic_solver 10. }
        2: { apply set_union_mori; [|done]. apply ETCCOH. }
        red. simpls; splits.
        { unionR left. apply ETCCOH. }
        { unionL.
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
        unionL.
        { etransitivity. 
          2: eapply traversal_mon.
          { apply ETCCOH. }
          all: basic_solver. }
        intros x HH; subst.
        red; simpls. unfold set_inter. splits; auto; red.
        { by rewrite fwbob_in_sb. }
        all: unionR left.
        { rewrite WF.(ppo_in_sb). rewrite bob_in_sb. by rewrite unionK, !seqA. }
        arewrite ((fun x => W_ex x /\ is_xacq lab x) ⊆₁ W). 
        2: done.
        generalize WF.(W_ex_in_W). basic_solver. }
      red; unfold ecovered, eissued; simpls.
      splits; eauto.
      constructor; unfold eissued, ecovered; simpls.
      all: try by (unionR left; auto).
      3: { generalize ETCCOH.(etc_S_I_in_W_ex). basic_solver 10. }
      2: { apply set_union_mori; [|done]. apply ETCCOH. }
      red. simpls; splits.
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
      all: unionR left.
      { rewrite WF.(ppo_in_sb). rewrite bob_in_sb. by rewrite unionK, !seqA. }
      arewrite ((fun x => W_ex x /\ is_xacq lab x) ⊆₁ W). 
      2: done.
      generalize WF.(W_ex_in_W). basic_solver. }

split; auto.
          red. rewrite SBE. eauto with hahn. }
        left. right. split; auto.
        red. rewrite IRF. eauto with hahn. }

            re
          2: { left. right. split; auto.


splits; simpls.
        { 

red. splits; simpls.


      red. unfold ecovered, eissued in *.
      splits; auto; simpls.
      { right. left. splits; eauto. }
      assert (issuable G (etc_TC T) w) as WISS.
      { red. unfold set_inter. splits; auto; red.
        3: { arewrite ((fun x => W_ex x /\ is_xacq lab x) ⊆₁ W). 
             2: done.
             generalize WF.(W_ex_in_W). basic_solver. }
        2: { rewrite WF.(ppo_in_sb). rewrite bob_in_sb. by rewrite unionK, !seqA. }
        arewrite
        (fwbob ⨾ ⦗eq w⦘ ⊆
               (⦗W ∩₁ Rel⦘ ⨾ sb ∩ same_loc ⨾ ⦗W⦘ ∪ ⦗F ∩₁ Acq/Rel⦘ ⨾ sb) ⨾ ⦗eq w⦘).
        { unfold imm_common.fwbob. rewrite !seq_union_l, !seqA.
          unionL; eauto 10 with hahn.
          all: type_solver. }
        arewrite ((⦗W ∩₁ Rel⦘ ⨾ sb ∩ same_loc ⨾ ⦗W⦘ ∪ ⦗F ∩₁ Acq/Rel⦘ ⨾ sb) ⊆ ⦗FW⦘ ⨾ sb).
        2: done.
        basic_solver. }

      constructor; unfold ecovered, eissued; simpls.
      { red. splits; simpls.
        { apply ETCCOH. }
        { etransitivity.
          2: { eapply traversal_mon with (T:=etc_TC T); basic_solver. }
          apply ETCCOH. }
        etransitivity.
        2: { eapply traversal_mon with (T:=etc_TC T); basic_solver. }
        unionL; auto; [apply ETCCOH|basic_solver]. }
      { apply set_union_mori; [|done]. apply ETCCOH. }
      { generalize ETCCOH.(etc_S_I_in_W_ex). basic_solver 10. }
      all: unionR left; auto. }


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
