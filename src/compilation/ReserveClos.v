
Lemma tc_coh2etc_coh tc (COH: tc_coherent G sc tc)
      (w_ex_is_xacq : W_ex G ⊆₁ W_ex G ∩₁ is_xacq (lab G)):
  etc_coherent G sc (mkETC tc (issued tc)). 
Proof using WF IMMCON.
  forward eapply tc_coherent_implies_tc_coherent_alt as COH_ALT; eauto.
  { apply IMMCON. }
  inversion COH_ALT.
  destruct tc as [C I]. simpl in *. 
  split; auto; unfold ecovered, eissued; simpl.
  { basic_solver. }
  { etransitivity; [| by apply tc_fwbob_I]. apply dom_rel_mori.
    rewrite <- !seqA. hahn_frame. apply imm_bob.sb_from_f_in_fwbob. }
  { forward eapply dom_detour_rmwrfi_rfe_acq_sb_issued as IN; eauto. }
  { forward eapply dom_wex_sb_issued as IN; eauto. }
  { unfold dom_sb_S_rfrmw. simpl.
    rewrite rmw_W_ex. repeat rewrite codom_seq. rewrite codom_eqv.
    rewrite set_interC, <- dom_eqv1.
    rewrite w_ex_is_xacq. forward eapply dom_wex_sb_issued as IN; eauto. }
  { sin_rewrite detour_rfe_data_rfi_rmw_rppo_in_detour_rfe_ppo; auto.
    rewrite seqA. forward eapply dom_detour_rfe_ppo_issued as IN; eauto. }
  { rewrite (dom_l (wf_detourD WF)); auto. 
    rewrite detour_in_ar, imm_s_ppo.rmw_in_ar_int, ar_int_in_ar; eauto.
    etransitivity; [| by apply tc_I_ar_rf_ppo_loc_I]. apply dom_rel_mori.
    hahn_frame. rewrite <- ct_unit, <- ct_step. apply seq_mori; basic_solver 10. }
  forward eapply TraversalProperties.issuable_W_ex_in_codom_I_rfrmw as IN; eauto.
  rewrite <- IN, <- issued_in_issuable; auto.
Qed.

Lemma itrav_step2ext_itrav_step_cover (C I: actid -> Prop) (e: actid)
      (COH: tc_coherent G sc (mkTC C I))
      (w_ex_is_xacq : W_ex G ⊆₁ W_ex G ∩₁ is_xacq (lab G))
      (STEP: itrav_step G sc e (mkTC C I) (mkTC (C ∪₁ eq e) I)):
  ext_itrav_step G sc e (mkETC (mkTC C I) I) (mkETC (mkTC (C ∪₁ eq e) I) I).
Proof.
  forward eapply trav_step_coherence as COH2; [by red; eauto| done |]. 
  inversion STEP.
  2: { red in H. desc. simpl in *. destruct NISS. apply ISSEQ. basic_solver. }
  red in H. desc. red. splits; unfold ecovered, eissued; simpl in *; eauto. 
  by apply tc_coh2etc_coh.
Qed.

Lemma etc_coh_extend_reserved tc w
      (w_ex_is_xacq : W_ex G ⊆₁ W_ex G ∩₁ is_xacq (lab G))
      (WEXw: W_ex G w)
      (NISS: ~ issued tc w)
      (ISS'w: issuable G sc tc w)
      (TCOH: etc_coherent G sc (mkETC tc (issued tc))):
  etc_coherent G sc (mkETC tc (issued tc ∪₁ eq w)). 
Proof using WF IMMCON.
  pose proof COH as COH'. destruct COH'.
  destruct tc as [C I] eqn:TC. 
  split; auto; unfold ecovered, eissued in *; simpl in *.
  { apply W_ex_in_E in WEXw; auto. basic_solver. }
  { basic_solver. }
  { basic_solver. }
  { rewrite id_union. repeat rewrite seq_union_r. rewrite dom_union. 
    apply set_subset_union_l. split; auto.
    etransitivity; [| by apply ISS'w]. apply dom_rel_mori. hahn_frame.
    apply imm_bob.sb_from_f_in_fwbob. }
  { rewrite id_union. repeat rewrite seq_union_r. rewrite dom_union. 
    apply set_subset_union_l. split; auto.
    replace I with (issued tc) by vauto.
    etransitivity; [| by eapply dom_detour_rmwrfi_rfe_acq_sb_issuable; eauto].
    apply dom_rel_mori. repeat hahn_frame_l. basic_solver. }
  { rewrite id_union. repeat rewrite seq_union_r. rewrite dom_union. 
    apply set_subset_union_l. split; auto.
    replace I with (issued tc) by vauto.
    etransitivity; [| by eapply dom_wex_sb_issuable; eauto].
    apply dom_rel_mori. repeat hahn_frame_l. basic_solver. }
  { rewrite dom_sb_S_rfrmw_issuable; auto.
    { simpl. basic_solver. }
    simpl. replace I with (issued tc) by vauto.
    rewrite issued_in_issuable at 1; vauto. basic_solver. }
  { rewrite id_union. repeat rewrite seq_union_r. rewrite dom_union.
    apply set_subset_union_l. split; auto.
    sin_rewrite detour_rfe_data_rfi_rmw_rppo_in_detour_rfe_ppo; auto.
    replace I with (issued tc) by vauto.
    etransitivity; [| by apply dom_detour_rfe_ppo_issuable; eauto].
    apply dom_rel_mori. hahn_frame. basic_solver. }
  { rewrite id_union. repeat rewrite seq_union_r. rewrite dom_union.
    apply set_subset_union_l. split; auto.
    rewrite (dom_l (wf_detourD WF)); auto. 
    rewrite detour_in_ar, imm_s_ppo.rmw_in_ar_int, ar_int_in_ar; eauto.
    etransitivity; [| by apply ISS'w]. apply dom_rel_mori.
    hahn_frame. rewrite <- ct_unit, <- ct_step. apply seq_mori; basic_solver. }
  rewrite set_inter_union_l. apply set_subset_union_l. split; auto.
  replace I with (issued tc) by vauto.
  rewrite <- TraversalProperties.issuable_W_ex_in_codom_I_rfrmw; try by vauto.
  basic_solver. 
Qed.

Lemma etc_coh_extend_reserved_rmw tc r w
      (w_ex_is_xacq : W_ex G ⊆₁ W_ex G ∩₁ is_xacq (lab G))
      (WEXw: W_ex G w)
      (COV'r: coverable G sc tc r)
      (RMW: rmw G r w)
      (COH: etc_coherent G sc (mkETC tc (issued tc))):
  etc_coherent G sc (mkETC tc (issued tc ∪₁ eq w)). 
Proof using WF IMMCON.
  clear FRELACQ. 
  apply wf_rmwD, seq_eqv_lr in RMW as (Rr & RMW & Ww); eauto. 
  destruct (classic (issued tc w)) as [ISSw | NISSw].
  { eapply etc_coherent_more; eauto. red. splits; basic_solver. }

  assert (sb G ⨾ ⦗eq w⦘ ⊆ ⦗coverable G sc tc⦘  ⨾ (sb G)^? ⨾ rmw G ⨾ ⦗eq w⦘) as DOM_SBw.
  { assert (⦗eq r⦘ ⨾ rmw G ⨾ ⦗eq w⦘ ⊆ rmw G ⨾ ⦗eq w⦘) as <- by basic_solver.
    rewrite sb_rmw_split; eauto. do 2 hahn_frame_r. 
    rewrite crE. repeat case_union _ _. apply union_mori; [basic_solver 10| ].
    red in COV'r. apply proj1, proj2 in COV'r. red in COV'r.
    apply dom_rel_helper_in in COV'r. rewrite COV'r at 1.
    hahn_frame. apply eqv_rel_mori. apply covered_in_coverable. apply COH. }

  pose proof COH as COH'. destruct COH'.
  destruct tc as [C I] eqn:TC. unfold ecovered, eissued in *; simpl in *.

  assert (dom_rel (⦗is_w (lab G)⦘ ⨾ sb G ⨾ ⦗eq r⦘ ⨾ rmw G ⨾ ⦗eq w⦘) ⊆₁ I) as SB_R_HELPER. 
  { rewrite <- !seqA. do 2 rewrite dom_seq. rewrite seqA.  
    red in COV'r. apply proj1, proj2 in COV'r. red in COV'r.
    apply dom_rel_helper_in in COV'r. rewrite COV'r at 1.
    seq_rewrite <- id_inter. repeat rewrite dom_seq. rewrite dom_eqv.
    rewrite w_covered_issued; eauto using COH. } 

  assert (dom_rel ((detour G ∪ rfe G) ⨾ sb G ⨾ ⦗eq w⦘) ⊆₁ I) as DET_RFE_ISS. 
  { rewrite DOM_SBw. rewrite <- !seqA. do 3 rewrite dom_seq.
    rewrite seq_union_l, dom_union. apply set_subset_union_l. split.
    { rewrite (dom_l (wf_detourD WF)). rewrite detour_in_sb, seqA, dom_eqv1. 
      rewrite dom_sb_coverable. rewrite w_covered_issued; eauto. }
    rewrite rfe_in_rf. apply dom_rf_coverable; auto. }


  split; auto; unfold ecovered, eissued in *; simpl in *.
  { apply W_ex_in_E in WEXw; auto. basic_solver. }
  { basic_solver. }
  { basic_solver. }
  { rewrite id_union. repeat rewrite seq_union_r. rewrite dom_union. 
    apply set_subset_union_l. split; auto.
    erewrite sb_rmw_split_disj; eauto.
    2: { unfolder. intros ?. desc. subst. type_solver. }
    etransitivity; [| apply COV'r]. basic_solver. }
  { rewrite id_union. repeat rewrite seq_union_r. rewrite dom_union. 
    apply set_subset_union_l. split; auto.
    rewrite inclusion_seq_eqv_l.
    rewrite rmw_in_sb, rfi_in_sb, sb_sb; auto.
    seq_rewrite <- ct_end. rewrite ct_of_trans; [| by apply sb_trans]. auto. }
  { rewrite id_union. repeat rewrite seq_union_r. rewrite dom_union. 
    apply set_subset_union_l. split; auto.
    rewrite W_ex_in_W; auto. erewrite eqv_rel_mori; [| red; intro; apply proj1].
    rewrite sb_rmw_split_disj; eauto.
    unfolder. intros ?. desc. subst x. type_solver. }
  { unfold dom_sb_S_rfrmw. simpl.
    rewrite id_union, seq_union_r, dom_union. rewrite set_inter_union_l.
    apply set_subset_union_l. split.
    { rewrite etc_sb_S. basic_solver. }
    rewrite wf_rmwD; auto. repeat rewrite codom_seq. rewrite codom_eqv.
    rewrite set_interC, <- dom_eqv1.
    rewrite sb_rmw_split_disj; eauto.
    2: { unfolder. intro. type_solver 10. }
    rewrite SB_R_HELPER. basic_solver. }
  { rewrite id_union. repeat rewrite seq_union_r. rewrite dom_union.
    apply set_subset_union_l. split; auto.
    rewrite rppo_in_sb, data_in_sb, rfi_in_sb, rmw_in_sb; auto. rewrite !unionK.
    seq_rewrite <- ct_end. rewrite ct_of_trans; [| by apply sb_trans]. auto. }
  { rewrite id_union. repeat rewrite seq_union_r. rewrite dom_union.
    apply set_subset_union_l. split; auto.
    rewrite <- DET_RFE_ISS. apply dom_rel_mori.
    rewrite rmw_in_sb; auto. basic_solver 10. }
  rewrite set_inter_union_l. apply set_subset_union_l. split; auto.
  red. intros ? [<- _].
  cdes IMMCON. destruct (Comp r) as [w' RF].
  { apply wf_rmwE in RMW; auto. generalize RMW, Rr. basic_solver 10. }
  exists w'. forward eapply dom_rf_coverable with (x := w'); eauto; basic_solver 10. 
Qed. 

(* Notation "'[' C '#' I '#' R ']'" := (mkETC (mkTC C I) R).  *)
  
Lemma itrav_step2ext_itrav_step_issue (C I: actid -> Prop) (e: actid)
      (w_ex_is_xacq : W_ex G ⊆₁ W_ex G ∩₁ is_xacq (lab G))
      (COH: tc_coherent G sc (mkTC C I))
      (STEP: itrav_step G sc e (mkTC C I) (mkTC C (I ∪₁ eq e))):
  ((ext_itrav_step G sc e ⨾ ⦗eq [C # I # I ∪₁ eq e]⦘)^? ⨾ 
                  ⦗etc_coherent G sc⦘ ⨾ (ext_itrav_step G sc e))
                         [C # I # I]
                         [C # I ∪₁ eq e # I ∪₁ eq e].
Proof.
  forward eapply trav_step_coherence as COH2; [by red; eauto| done |]. 
  inversion STEP.
  { red in H. desc. simpl in *. destruct NEXT. apply COVEQ. basic_solver. }
  red in H. desc. unfold ecovered, eissued; simpl in *.
  destruct (classic (W_ex G e)) as [WEXe | NWEXe].
  2: { eexists. splits; [by apply r_refl| ].
       apply seq_eqv_l. split; [by apply tc_coh2etc_coh| ]. 
       red. splits.
       2: { apply tc_coh2etc_coh; eauto. }
       right. left. unfold ecovered, eissued; simpl in *. splits; eauto.
       { tauto. }
       rewrite set_unionA, set_unionC with (s := eq e), <- set_unionA.
       rewrite set_union_absorb_r with (s := dom_sb_S_rfrmw _ _ _ _); auto.
       rewrite dom_sb_S_rfrmw_issuable; auto.
       rewrite <- issued_in_issuable; auto. }
  forward eapply (@etc_coh_extend_reserved (mkTC C I) e) as COH'; eauto.
  { apply tc_coh2etc_coh; auto. }
  simpl in COH'. remember [C # I # I ∪₁ eq e] as tc'.
  exists tc'. split.
  { apply r_step, seq_eqv_r. split; auto. 
    red. splits; auto. 
    do 2 right. subst tc'. splits; eauto. }
  apply seq_eqv_l. split; auto. 
  red. splits; [| subst tc'; vauto]. 
  2: { apply tc_coh2etc_coh; auto. }
  right. left. splits; vauto. simpl. split; [basic_solver| ]. 
  rewrite dom_sb_S_rfrmw_issuable; auto.
  { basic_solver. }
  apply set_subset_union_l. split; [| basic_solver].
  rewrite <- issued_in_issuable; auto.
Qed.

Lemma ext_isim_trav_step_more_helper:
  forall (y : thread_id) x y0,
  same_ext_trav_config x y0 ->
  forall x0 y1 : ext_trav_config,
  same_ext_trav_config x0 y1 ->
  ext_isim_trav_step G sc y x x0 -> ext_isim_trav_step G sc y y0 y1. 
Proof.
  intros t tc1 tc2 SAME tc1' tc2' SAME' STEP.
  apply same_etc_extensionality in SAME, SAME'. congruence. 
Qed.

Global Add Parametric Morphism : (ext_isim_trav_step G sc) with signature
    eq ==> same_ext_trav_config ==> same_ext_trav_config ==> iff as
        ext_isim_trav_step_more.
Proof using.
  ins; split; apply ext_isim_trav_step_more_helper.
  3, 4: symmetry. all: done. 
Qed. 

Lemma eis_add_res_rmw (C I C' I': actid -> Prop)
      (e: actid) (r w: actid)
      (RMWrw: rmw G r w)
      (w_ex_is_xacq : W_ex G ⊆₁ W_ex G ∩₁ is_xacq (lab G))
      (COV'r: C' r)
      (Erw: ⟪Erw: e = r \/ e = w⟫)
      (STEP: ext_itrav_step G sc e [C # I # I] [C' # I' # I'])
      (COH: tc_coherent G sc (mkTC C I)):
  ext_itrav_step G sc e [C # I # I ∪₁ eq w] [C' # I' # I' ∪₁ eq w].
Proof.
  assert (etc_coherent G sc [C # I # I]) as COH1. 
  { apply tc_coh2etc_coh; auto. }
  destruct STEP as [STEP COH2]. red in COH2. 

  red. splits.
  2: { eapply etc_coh_extend_reserved_rmw; eauto.
       { eexists. eauto. }
       eapply covered_in_coverable; eauto. apply COH2. }
  unfold ecovered, eissued in *. simpl in *. desf.
  { left. splits; try by vauto. by rewrite ISSEQ. }
  { right. left. splits; try by vauto.
    { intuition. }
    red in Erw. des; subst e. 
    { destruct COH2. apply issuedW in etc_tccoh.
      simpl in etc_tccoh. rewrite ISSEQ in etc_tccoh.
      apply set_subset_union_l in etc_tccoh. desc.
      apply wf_rmwD, seq_eqv_lr in RMWrw; auto. desc. 
      exfalso. generalize RMWrw, etc_tccoh0. unfolder. ins.
      specialize (etc_tccoh1 r eq_refl). type_solver. }
    rewrite ISSEQ. 
    split; [basic_solver| ]. 
    arewrite (dom_sb_S_rfrmw G [C # I # I ∪₁ eq w] (rfi G) (eq w) ≡₁ dom_sb_S_rfrmw G [C' # I' # I'] (rfi G) (eq w)).
    { unfold dom_sb_S_rfrmw. simpl. rewrite <- ISSEQ. basic_solver. }
    rewrite dom_sb_S_rfrmw_issuable; try by vauto.
    { unfold eissued. simpl. rewrite ISSEQ. basic_solver. }
    simpl. rewrite <- issued_in_issuable; auto. apply COH2. }
  right. right.
  destruct NISS. apply ISSEQ, RESEQ. basic_solver. 
Qed. 

Lemma isim_trav_step2ext_isim_trav_step tc1 tc2 t
      (COH1: tc_coherent G sc tc1)
      (STEP: isim_trav_step G sc t tc1 tc2)
      (w_ex_is_xacq : W_ex G ⊆₁ W_ex G ∩₁ is_xacq (lab G)):
  (ext_isim_trav_step G sc t)^* (mkETC tc1 (issued tc1)) (mkETC tc2 (issued tc2)).
Proof.
  forward eapply sim_trav_step_coherence as COH2; [by red; eauto| done |]. 

  inversion STEP; subst.
  { apply rt_step. destruct tc1. simpl in *.
    eapply ext_fence_trav_step, itrav_step2ext_itrav_step_cover; eauto. }
  { apply rt_step. destruct tc1. simpl in *.
    eapply ext_read_trav_step, itrav_step2ext_itrav_step_cover; eauto. }
  { destruct tc1 as [C I] eqn:TC1. simpl in *.
    assert (issuable G sc tc1 w) as ISS'w.
    { inversion TS; red in H; desc; simpl in *.
      2: congruence. 
      destruct NEXT. apply COVEQ. basic_solver. }
    apply itrav_step2ext_itrav_step_issue in TS as [tc' [STEPres STEP']]; auto.
    apply seq_eqv_l in STEP' as [COH' STEP'].

    destruct tc' as [[C' I'] R'].
    assert (C' = C /\ I' = I /\ (R' = I \/ R' = I ∪₁ eq w)) as [-> [-> RES']].
    { destruct STEPres.
      { inversion H. auto. }
      apply seq_eqv_r in H. desc. inversion H0. auto. }
    assert (R' ⊆₁ I ∪₁ eq w) as RES'_.
    { destruct RES'; basic_solver. } 
        
    apply rt_unit. exists [C # I # R']. split.
    { destruct RES' as [-> | ->]; [by apply rt_refl| ]. 
      apply rt_step. apply ext_reserve_trav_step. red. splits; vauto. }
  
    forward eapply ext_rlx_write_promise_step 
      with (T := [C # I # R']) (sc := sc) as WSTEP; eauto.
    { eapply ext_itrav_step_more; try by vauto.
      rewrite reserved_rewrite_helper; vauto. }
    rewrite reserved_rewrite_helper in WSTEP; vauto. }
  { apply rt_step. destruct tc1. simpl in *.
    eapply ext_rlx_write_cover_step, itrav_step2ext_itrav_step_cover; eauto. }
  { destruct tc1 as [C I] eqn:TC1. simpl in *.

    assert (tc_coherent G sc (mkTC C (I ∪₁ eq w))) as COH1'. 
    { simpl. eapply trav_step_coherence; [| by apply COH1]. red. eauto. }

    apply itrav_step2ext_itrav_step_issue in TS1 as [tc' [STEPres STEP']]; auto.
    apply seq_eqv_l in STEP' as [COH' STEP'].
    destruct tc' as [[C' I'] R'].
    assert (C' = C /\ I' = I /\ (R' = I \/ R' = I ∪₁ eq w)) as [-> [-> RES']].
    { destruct STEPres.
      { inversion H. auto. }
      apply seq_eqv_r in H. desc. inversion H0. auto. }
    assert (R' ⊆₁ I ∪₁ eq w) as RES'_.
    { destruct RES'; basic_solver. } 

    apply rt_unit. exists [C # I # R']. split.
    { destruct RES' as [-> | ->]; [by apply rt_refl| ]. 
      apply rt_step. apply ext_reserve_trav_step. red. splits; vauto. }

    assert (issuable G sc (mkTC C I) w) as ISS'w.
    { apply issuable_add_eq_iff; auto.
      apply issued_in_issuable; basic_solver. }
  
    forward eapply ext_rel_write_step with (T := [C # I # R']) (sc := sc)
                                           as WSTEP; eauto.
    { rewrite reserved_rewrite_helper; vauto. }
    { rewrite reserved_rewrite_helper; try by vauto.
      unfold ecovered, eissued. simpl.
      apply itrav_step2ext_itrav_step_cover; auto. }
    rewrite reserved_rewrite_helper in WSTEP; vauto. }  
  { destruct tc1 as [C I] eqn:TC1. simpl in *.
    apply rt_step. apply ext_rlx_rmw_cover_step; auto. 
    { apply itrav_step2ext_itrav_step_cover; auto. }
    apply itrav_step2ext_itrav_step_cover; auto.
    unfold ecovered. simpl.
    eapply trav_step_coherence; [| by apply COH1]. red. eauto. }

  destruct tc1 as [C I] eqn:TC1. simpl in *.
  apply rt_unit. eexists. split.
  { replace (tid r) with (tid w).
    2: { symmetry. erewrite wf_rmwt; eauto. }
    apply rt_step. apply ext_reserve_trav_step. red. splits; vauto.
    eapply etc_coh_extend_reserved_rmw; eauto.
    { eexists. eauto. }
    { apply coverable_add_eq_iff; auto.
      apply covered_in_coverable.
      { eapply trav_step_coherence; [| by apply COH1]. red. eauto. }
      basic_solver. }
    apply tc_coh2etc_coh; auto. }
  
  assert (tc_coherent G sc (mkTC (C ∪₁ eq r) I)) as COH'.
  { eapply trav_step_coherence; [| by apply COH1]. red. eauto. }
  assert (tc_coherent G sc (mkTC (C ∪₁ eq r) (I ∪₁ eq w))) as COH''.
  { eapply trav_step_coherence; [| by apply COH']. red. eauto. }
  
  forward eapply (@reserved_rewrite_helper [C ∪₁ eq r # I # I ∪₁ eq w]) as RES_ALT; auto. 
  { eapply etc_coh_extend_reserved_rmw; eauto.
    { exists r. basic_solver. }
    { apply covered_in_coverable; vauto. }
    simpl. apply tc_coh2etc_coh; auto. }
  { basic_solver. }
  { apply issuable_add_eq_iff; auto.
    apply issued_in_issuable; vauto. }
  
  simpl. forward eapply ext_rel_rmw_step
    with (T := [C # I # I ∪₁ eq w]) (sc := sc) as RMWSTEP; eauto.
  { unfold ecovered, eissued; simpl. 
    eapply eis_add_res_rmw; eauto.
    { basic_solver. }
    apply itrav_step2ext_itrav_step_cover; auto. }
  { replace (reserved [C # I # I ∪₁ eq w]) with (reserved [C ∪₁ eq r# I # I ∪₁ eq w]) by vauto.
    replace (dom_sb_S_rfrmw G [C # I # I ∪₁ eq w]) with (dom_sb_S_rfrmw G [C ∪₁ eq r# I # I ∪₁ eq w]) by vauto.      
    rewrite RES_ALT. 
    
    unfold ecovered, eissued; simpl.
    red. splits.
    2: { apply tc_coh2etc_coh; auto. }
    right. left.
    rewrite RES_ALT. 
    unfold ecovered, eissued; simpl. splits; vauto. }    
  { rewrite RES_ALT. unfold ecovered, eissued; simpl.
    apply itrav_step2ext_itrav_step_cover; auto. }
  
  rewrite RES_ALT in RMWSTEP. auto. 
Qed.  

(* TODO: get rid of FRELACQ *)
Lemma sim_trav_step2ext_sim_trav_step (tc1 tc2: trav_config)
      (COH1: tc_coherent G sc tc1)
      (STEP: sim_trav_step G sc tc1 tc2)
      (w_ex_is_xacq : W_ex G ⊆₁ W_ex G ∩₁ is_xacq (lab G)):
  (ext_sim_trav_step G sc)^* (mkETC tc1 (issued tc1)) (mkETC tc2 (issued tc2)).
Proof using WF IMMCON FRELACQ.
  red in STEP. desc. 
  apply isim_trav_step2ext_isim_trav_step in STEP; auto.
  induction STEP.
  { apply rt_step. red. eauto. }
  { apply rt_refl. }
  eapply rt_trans; eauto. 
Qed. 
