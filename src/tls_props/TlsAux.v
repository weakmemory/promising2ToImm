From hahn Require Import Hahn.

From imm Require Import AuxDef Events Execution.
From imm Require Import Execution_eco imm_s_hb imm_s imm_bob.
From imm Require Import imm_s_ppo CombRelations.
From imm Require Import imm_s_rfppo.
From imm Require Import FinExecution.

From imm Require Import TraversalOrder.
From imm Require Import TLSCoherency.
From imm Require Import IordCoherency.

Set Implicit Arguments.

Definition covered  TLS := event ↑₁ (TLS ∩₁ action ↓₁ (eq ta_cover)).
Definition issued   TLS := event ↑₁ (TLS ∩₁ action ↓₁ (eq ta_issue)).
Definition reserved TLS := event ↑₁ (TLS ∩₁ action ↓₁ (eq ta_reserve)).

Section TlsProperties.
  Variable G : execution.
  Variable WF : Wf G.
  Variable COM : complete G.
  Variable sc : relation actid.
  Variable IMMCON : imm_consistent G sc.

  Notation "'sb'" := (sb G).
  Notation "'rmw'" := (rmw G).
  Notation "'data'" := (data G).
  Notation "'addr'" := (addr G).
  Notation "'ctrl'" := (ctrl G).
  Notation "'rf'" := (rf G).
  Notation "'co'" := (co G).
  Notation "'coe'" := (coe G).
  Notation "'fr'" := (fr G).

  Notation "'eco'" := (eco G).

  Notation "'bob'" := (bob G).
  Notation "'fwbob'" := (fwbob G).
  Notation "'ppo'" := (ppo G).
  Notation "'fre'" := (fre G).
  Notation "'rfi'" := (rfi G).
  Notation "'rfe'" := (rfe G).
  Notation "'deps'" := (deps G).
  Notation "'detour'" := (detour G).
  Notation "'release'" := (release G).
  Notation "'sw'" := (sw G).
  Notation "'hb'" := (hb G).

  Notation "'ar'" := (ar G sc).

  Notation "'urr'" := (urr G sc).
  Notation "'c_acq'" := (c_acq G sc).
  Notation "'c_cur'" := (c_cur G sc).
  Notation "'c_rel'" := (c_rel G sc).
  Notation "'t_acq'" := (t_acq G sc).
  Notation "'t_cur'" := (t_cur G sc).
  Notation "'t_rel'" := (t_rel G sc).
  Notation "'S_tm'" := (S_tm G).
  Notation "'S_tmr'" := (S_tmr G).
  Notation "'msg_rel'" := (msg_rel G sc).

Notation "'lab'" := (lab G).
Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'mod'" := (Events.mod lab).
Notation "'same_loc'" := (same_loc lab).

Notation "'E'" := (acts_set G).
Notation "'R'" := (fun x => is_true (is_r lab x)).
Notation "'W'" := (fun x => is_true (is_w lab x)).
Notation "'F'" := (fun x => is_true (is_f lab x)).
Notation "'RW'" := (R ∪₁ W).
Notation "'FR'" := (F ∪₁ R).
Notation "'FW'" := (F ∪₁ W).
Notation "'R_ex'" := (fun a => is_true (R_ex lab a)).
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

Context
  (T : trav_label -> Prop)
  (TLSCOH  : tls_coherent G T)
  (IORDCOH : iord_coherent G sc T)
  (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T).

  Lemma issuedW :
    issued T ⊆₁ W.
  Proof using WF TLSCOH. 
    unfold issued. rewrite tlsc_I_in_W; eauto. basic_solver.  
  Qed. 

  Lemma issuedE :
    issued T ⊆₁ E.
  Proof using WF TLSCOH.
    unfold issued. rewrite (tlsc_E WF TLSCOH). basic_solver.  
  Qed. 

  Lemma w_covered_issued :
    W ∩₁ covered T ⊆₁ issued T.
  Proof using TLSCOH IORDCOH.
    unfold covered.
    unfolder. ins. desc.
    forward eapply tlsc_w_covered_issued with (x := mkTL ta_cover x); eauto.
    destruct y; ins; vauto. 
  Qed. 

  Lemma init_issued : is_init ∩₁ E ⊆₁ issued T.
  Proof using TLSCOH.
    unfolder; ins; desf. red.
    exists (mkTL ta_issue x). repeat split; auto. 
    destruct TLSCOH. apply tls_coh_init. red. split; vauto.
  Qed. 

  Lemma init_covered : is_init ∩₁ E ⊆₁ covered T.
  Proof using TLSCOH. 
    unfolder; ins; desf. red.
    exists (mkTL ta_cover x). repeat split; auto. 
    destruct TLSCOH. apply tls_coh_init. red. split; vauto.
  Qed.

  Lemma dom_sb_covered :
    dom_rel (sb ⨾ ⦗ covered T ⦘) ⊆₁ covered T.
  Proof using WF TLSCOH IORDCOH IMMCON.
    apply iord_coh_implies_iord_simpl_coh in IORDCOH; auto.
    unfold covered. unfolder. ins. desc. destruct y0; ins; subst.
    exists (mkTL ta_cover x). splits; auto. apply IORDCOH.
    eexists. apply seq_eqv_r. split; eauto. red. repeat left.
    red. apply seq_eqv_lr. splits; vauto.
  Qed.  

  Lemma sb_covered :
    sb ⨾ ⦗ covered T ⦘ ≡ ⦗ covered T ⦘ ⨾ sb ⨾ ⦗ covered T ⦘.
  Proof using WF TLSCOH IORDCOH IMMCON.
    rewrite (dom_rel_helper dom_sb_covered). basic_solver.
  Qed.

  (* Lemma dom_rf_coverable : *)
  (*   dom_rel (rf ⨾ ⦗ coverable T ⦘) ⊆₁ issued T. *)
  (* Proof using WF TCCOH. *)
  (*   unfold coverable, dom_cond. *)
  (*   rewrite (dom_r (wf_rfD WF)). *)
  (*   type_solver 40. *)
  (* Qed. *)

  Lemma dom_rf_covered :
    dom_rel (rf ⨾ ⦗ covered  T ⦘) ⊆₁ issued T.
  Proof using WF TLSCOH IORDCOH IMMCON. 
    unfold covered, issued. unfolder. ins. desc. destruct y0; ins; subst.
    exists (mkTL ta_issue x). splits; auto.
    apply iord_coh_implies_iord_simpl_coh in IORDCOH; auto. apply IORDCOH.
    eexists. apply seq_eqv_r. split; eauto. red. do 4 left. right. 
    red. apply seq_eqv_lr. splits; vauto. red. apply seq_eqv_l. split.
    2: { basic_solver. }
    apply wf_rfD, seq_eqv_lr in H; basic_solver.
  Qed. 

  Lemma rf_covered :
    rf ⨾ ⦗ covered T ⦘ ≡ ⦗ issued T ⦘ ⨾ rf ⨾ ⦗ covered T ⦘.
  Proof using WF TLSCOH IORDCOH IMMCON.
    rewrite (dom_rel_helper dom_rf_covered). basic_solver.
  Qed.

  (* Lemma dom_sc_coverable : *)
  (*   dom_rel (sc ⨾ ⦗ coverable T ⦘) ⊆₁ covered T. *)
  (* Proof using IMMCON. *)
  (*   cdes IMMCON. *)
  (*   rewrite (dom_r (@wf_scD G sc Wf_sc)). *)
  (*   unfold coverable, dom_cond; type_solver 42. *)
  (* Qed. *)

  Lemma dom_sc_covered :
    dom_rel (sc ⨾ ⦗ covered T ⦘) ⊆₁ covered T.
  Proof using WF TLSCOH IORDCOH IMMCON.
    apply iord_coh_implies_iord_simpl_coh in IORDCOH; auto.
    unfold covered. unfolder. ins. desc. destruct y0; ins; subst.
    exists (mkTL ta_cover x). splits; auto. apply IORDCOH.
    eexists. apply seq_eqv_r. split; eauto. red. repeat left.
    red. apply seq_eqv_lr. splits; vauto.
  Qed.

  (* Lemma sc_coverable  : *)
  (*   sc ⨾ ⦗ coverable T ⦘ ⊆ ⦗covered T⦘ ⨾ sc. *)
  (* Proof using IMMCON. *)
  (*   seq_rewrite (dom_rel_helper dom_sc_coverable). *)
  (*   basic_solver. *)
  (* Qed. *)

  Lemma sc_covered  :
    sc ⨾ ⦗ covered T ⦘ ⊆ ⦗covered T⦘ ⨾ sc.
  Proof using WF TLSCOH IORDCOH IMMCON.
    seq_rewrite (dom_rel_helper dom_sc_covered). basic_solver.
  Qed.

  Lemma ar_C_in_CI  :
    dom_rel (ar ⨾ ⦗covered T⦘) ⊆₁ covered T ∪₁ issued T.
  Proof using WF TLSCOH IORDCOH IMMCON.
    unfold imm_s.ar.
    rewrite !seq_union_l.
    rewrite (ar_int_in_sb WF).
    arewrite (rfe ⊆ rf).
    rewrite sb_covered, rf_covered.
    rewrite sc_covered.
    basic_solver.
  Qed.

  Lemma JJJ (b : trav_action) A B r
        (UU : B ⊆₁ action ↓₁ eq b)
        (AA : dom_rel (<| action ↓₁ eq b|> ;; event ↓ r ;; <|A|>) ⊆₁ B) :
    dom_rel (r ⨾ ⦗event ↑₁ A⦘) ⊆₁ event ↑₁ B.
  Proof using.
    clear -AA UU. unfolder. ins. desf.
    exists (mkTL b x); ins.
    split; auto.
    apply AA.
    unfolder. do 2 eexists; ins; eauto.
    splits; eauto.
  Qed.

  Lemma ar_rf_ppo_loc_ct_I_in_I  :
    dom_rel (⦗W⦘ ⨾ (ar ∪ rf ⨾ (ppo ∩ same_loc))⁺ ⨾ ⦗issued T⦘) ⊆₁ issued T.
  Proof using WF TLSCOH IORDCOH IMMCON.
    unfold issued.
    rewrite <- !seqA. eapply JJJ.
    { clear. basic_solver. }
    apply set_subset_inter_r. split.
    2: { clear; basic_solver 10. }
    etransitivity.
    2: { apply iord_coh_implies_iord_simpl_coh; eauto. }
    apply dom_rel_mori.
    assert (AR G sc ⊆ iord_simpl G sc) as AA.
    { unfold iord_simpl. clear; basic_solver 10. }
    rewrite <- AA.
    unfold AR.
    set (BB:=event_surj). 
    rewrite <- !map_rel_seq2; auto.
    repeat hahn_frame_l.
    generalize (tlsc_I_in_W WF TLSCOH).
    clear. basic_solver.
  Qed. 

  Lemma ar_rfrmw_ct_I_in_I  :
    dom_rel (⦗W⦘ ⨾ (ar ∪ rf ⨾ rmw)⁺ ⨾ ⦗issued T⦘) ⊆₁ issued T.
  Proof using WF TLSCOH IORDCOH IMMCON.
    rewrite (rmw_in_ppo_loc WF). by apply ar_rf_ppo_loc_ct_I_in_I.
  Qed.

  Lemma ar_rf_ppo_loc_rt_I_in_I  :
    dom_rel (⦗W⦘ ⨾ (ar ∪ rf ⨾ (ppo ∩ same_loc))＊ ⨾ ⦗issued T⦘) ⊆₁ issued T.
  Proof using WF TLSCOH IORDCOH IMMCON.
    rewrite rtE. rewrite !seq_union_l, !seq_union_r, dom_union; unionL.
    { basic_solver. }
    apply ar_rf_ppo_loc_ct_I_in_I.
  Qed.

  Lemma ar_rfrmw_rt_I_in_I  :
    dom_rel (⦗W⦘ ⨾ (ar ∪ rf ⨾ rmw)＊ ⨾ ⦗issued T⦘) ⊆₁ issued T.
  Proof using WF TLSCOH IORDCOH IMMCON.
    rewrite (rmw_in_ppo_loc WF). by apply ar_rf_ppo_loc_rt_I_in_I.
  Qed.

  Lemma ar_rf_ppo_loc_I_in_I  :
    dom_rel (⦗W⦘ ⨾ (ar ∪ rf ⨾ (ppo ∩ same_loc)) ⨾ ⦗issued T⦘) ⊆₁ issued T.
  Proof using WF TLSCOH IORDCOH IMMCON.
    rewrite ct_step with (r := ar ∪ rf ⨾ (ppo ∩ same_loc)).
    by apply ar_rf_ppo_loc_ct_I_in_I.
  Qed.

  Lemma ar_rfrmw_I_in_I  :
    dom_rel (⦗W⦘ ⨾ (ar ∪ rf ⨾ rmw) ⨾ ⦗issued T⦘) ⊆₁ issued T.
  Proof using WF TLSCOH IORDCOH IMMCON.
    rewrite (rmw_in_ppo_loc WF). by apply ar_rf_ppo_loc_I_in_I.
  Qed.

  Lemma ar_ct_I_in_I  :
    dom_rel (⦗W⦘ ⨾ ar⁺ ⨾ ⦗issued T⦘) ⊆₁ issued T.
  Proof using WF TLSCOH IORDCOH IMMCON.
    arewrite (ar ⊆ ar ∪ rf ⨾ rmw). by apply ar_rfrmw_ct_I_in_I.
  Qed.

  Lemma ar_I_in_I  :
    dom_rel (⦗W⦘ ⨾ ar ⨾ ⦗issued T⦘) ⊆₁ issued T.
  Proof using WF TLSCOH IORDCOH IMMCON.
    rewrite ct_step with (r:=ar). apply ar_ct_I_in_I.
  Qed.

  Lemma rf_rmw_issued_rfi_rmw_issued : 
    (rf ⨾ rmw)＊ ⨾ ⦗issued T⦘ ⊆ (rfi ⨾ rmw)＊ ⨾ ⦗issued T⦘ ⨾ (rf ⨾ rmw)＊.
  Proof using WF IMMCON TLSCOH IORDCOH.
    assert (transitive sb) as SBT by apply sb_trans.
    eapply rt_ind_left with (P:= fun r => r ⨾ ⦗issued T⦘).
    { by eauto with hahn. }
    { basic_solver 12. }
    intros k H; rewrite !seqA.
    sin_rewrite H.
    rewrite rfi_union_rfe at 1; relsf; unionL.
    rewrite <- seqA; seq_rewrite <- ct_begin; basic_solver 12.
    rewrite rtE at 2.
    relsf; unionR left.
    arewrite (rfe ⨾ rmw ⨾ (rfi ⨾ rmw)＊ ⨾ ⦗issued T⦘ ⊆
                  ⦗issued T⦘ ⨾ rfe ⨾ rmw ⨾ (rfi ⨾ rmw)＊ ⨾ ⦗issued T⦘).
    { apply dom_rel_helper.
      arewrite (rmw ⨾ (rfi ⨾ rmw)＊ ⊆ ar＊).
      { arewrite (rfi ⊆ rf).
        rewrite (rmw_in_ppo WF) at 1. rewrite ppo_in_ar.
        rewrite rtE at 1. rewrite seq_union_r, seq_id_r.
        apply inclusion_union_l.
        { rewrite ct_step at 1. apply inclusion_t_rt. }
        rewrite rmw_in_ppo_loc; auto.
        rewrite ar_rf_ppo_loc_ct_in_ar_ct; auto. apply inclusion_t_rt. }
      rewrite (dom_l (wf_rfeD WF)), !seqA.
      arewrite (rfe ⊆ ar) at 1.
      seq_rewrite <- ct_begin. by apply ar_ct_I_in_I. }
    arewrite (rfe ⨾ rmw ⊆ rf ⨾ rmw).
    arewrite (rfi ⊆ rf).
    arewrite (rf ⨾ rmw ⨾ (rf ⨾ rmw)＊ ⊆ (rf ⨾ rmw)⁺).
    { rewrite <- seqA. apply ct_begin. }
    arewrite_id ⦗issued T⦘ at 2. rewrite seq_id_l.
    rewrite ct_rt. by rewrite inclusion_t_rt.
  Qed.

  Lemma dom_rfe_ppo_issued :
    dom_rel (rfe ⨾ ppo ⨾ ⦗issued T⦘) ⊆₁ issued T.
  Proof using WF TLSCOH IORDCOH IMMCON.
    rewrite (dom_l (wf_rfeD WF)).
    arewrite (rfe ⊆ ar).
    rewrite ppo_in_ar.
    sin_rewrite ar_ar_in_ar_ct.
    by apply ar_ct_I_in_I.
  Qed.

  Lemma dom_detour_rfe_ppo_issued :
    dom_rel ((detour ∪ rfe) ⨾ ppo ⨾ ⦗issued T⦘) ⊆₁ issued T.
  Proof using WF TLSCOH IORDCOH IMMCON.
    rewrite (dom_l (wf_rfeD WF)).
    rewrite (dom_l (wf_detourD WF)).
    arewrite (rfe ⊆ ar).
    arewrite (detour ⊆ ar).
    relsf.
    rewrite ppo_in_ar, !seqA.
    sin_rewrite ar_ar_in_ar_ct.
    apply ar_ct_I_in_I.
  Qed.

  Lemma dom_detour_rfe_acq_sb_issued :
    dom_rel ((detour ∪ rfe) ⨾ ⦗R ∩₁ Acq⦘ ⨾ sb ⨾ ⦗issued T⦘) ⊆₁ issued T.
  Proof using WF TLSCOH IORDCOH IMMCON.
    rewrite (dom_l (wf_detourD WF)).
    rewrite (dom_l (wf_rfeD WF)).
    arewrite (rfe ⊆ ar).
    arewrite (detour ⊆ ar).
    relsf.
    arewrite (⦗R ∩₁ Acq⦘ ⨾ sb ⊆ ar).
    { arewrite (⦗R ∩₁ Acq⦘ ⨾ sb ⊆ bob). unfold imm_s.ar, ar_int. eauto with hahn. }
    sin_rewrite ar_ar_in_ar_ct.
    apply ar_ct_I_in_I.
  Qed.

  Lemma dom_detour_rmwrfi_rfe_acq_sb_issued :
    dom_rel ((detour ∪ rfe) ⨾ (rmw ⨾ rfi)＊ ⨾ ⦗R ∩₁ Acq⦘ ⨾ sb ⨾ ⦗issued T⦘) ⊆₁ issued T.
  Proof using WF TLSCOH IORDCOH IMMCON.
    arewrite (⦗R ∩₁ Acq⦘ ⊆ ⦗Acq⦘ ⨾ ⦗R ∩₁ Acq⦘) by basic_solver.
    arewrite (rfi ⊆ rf).
    sin_rewrite (@rmwrf_rt_Acq_in_ar_rfrmw_rt G WF sc); auto.
    rewrite (dom_l (wf_detourD WF)).
    rewrite (dom_l (wf_rfeD WF)).
    arewrite (rfe ⊆ ar).
    arewrite (detour ⊆ ar).
    relsf.
    arewrite (⦗R ∩₁ Acq⦘ ⨾ sb ⊆ ar).
    { arewrite (⦗R ∩₁ Acq⦘ ⨾ sb ⊆ bob). unfold imm_s.ar, ar_int. eauto with hahn. }
    arewrite (ar ⊆ ar ∪ rf ⨾ rmw) at 3.
    arewrite (ar ⊆ ar ∪ rf ⨾ rmw) at 1.
    seq_rewrite <- ct_end.
    arewrite ((ar ∪ rf ⨾ rmw) ⨾ (ar ∪ rf ⨾ rmw)⁺ ⊆ (ar ∪ rf ⨾ rmw)⁺).
    { rewrite ct_step with (r:= ar ∪ rf ⨾ rmw) at 1. apply ct_ct. }
    apply ar_rfrmw_ct_I_in_I.
  Qed.

  Lemma dom_rfe_acq_sb_issued :
    dom_rel (rfe ⨾ ⦗R ∩₁ Acq⦘ ⨾ sb ⨾ ⦗issued T⦘) ⊆₁ issued T.
  Proof using WF TLSCOH IORDCOH IMMCON.
    arewrite (rfe ⊆ detour ∪ rfe).
    apply dom_detour_rfe_acq_sb_issued.
  Qed.

  Lemma dom_wex_sb_issued :
    dom_rel (⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗issued T⦘) ⊆₁ issued T.
  Proof using WF TLSCOH IORDCOH IMMCON.
    arewrite (⦗W_ex_acq⦘ ⊆ ⦗W⦘ ⨾ ⦗W_ex_acq⦘).
    { rewrite <- seq_eqvK at 1.
      rewrite (W_ex_in_W WF) at 1. basic_solver. }
    arewrite (⦗issued T⦘ ⊆ ⦗W⦘ ⨾ ⦗issued T⦘).
    { generalize issuedW. basic_solver. }
    arewrite (⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ ⊆ ar).
    apply ar_I_in_I.
  Qed. 
  
  Lemma wex_rfi_rfe_rmw_issued_is_issued :
    dom_rel ((⦗ W_ex_acq ⦘ ⨾ rfi ∪ rfe) ⨾ rmw ⨾ ⦗ issued T ⦘) ⊆₁ issued T.
  Proof using WF TLSCOH IORDCOH IMMCON.
    rewrite seq_union_l. rewrite dom_union.
    apply set_subset_union_l; split.
    { rewrite seqA. rewrite (rfi_in_sbloc' WF). rewrite (rmw_in_sb WF).
      arewrite (sb ∩ same_loc ⨾ sb ⊆ sb).
      { generalize (@sb_trans G). basic_solver. }
      arewrite (⦗issued T⦘ ⊆ ⦗W⦘ ⨾ ⦗issued T⦘).
      { generalize issuedW. basic_solver. }
      arewrite (⦗W_ex_acq⦘ ⊆ ⦗W⦘ ⨾ ⦗W_ex_acq⦘).
      { rewrite <- seq_eqvK at 1.
        rewrite (W_ex_in_W WF) at 1. basic_solver. }
      arewrite (⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ ⊆ ar).
      rewrite ct_step with (r:=ar).
      apply ar_ct_I_in_I. }
    rewrite (rmw_in_ppo WF).
    rewrite ppo_in_ar.
    rewrite (dom_l (wf_rfeD WF)), !seqA.
    arewrite (rfe ⊆ ar).
    sin_rewrite ar_ar_in_ar_ct.
    apply ar_ct_I_in_I.
  Qed. 

  Lemma wex_rf_rmw_issued_is_issued :
    dom_rel (⦗ W_ex_acq ⦘ ⨾ rf ⨾ rmw ⨾ ⦗ issued T ⦘) ⊆₁ issued T.
  Proof using WF TLSCOH IORDCOH IMMCON.
    arewrite (⦗W_ex_acq⦘ ⨾ rf ⊆ (⦗ W_ex_acq ⦘ ⨾ rfi ∪ rfe)).
    { rewrite rfi_union_rfe. basic_solver. }
      by apply wex_rfi_rfe_rmw_issued_is_issued.
  Qed.

  Lemma rf_rmw_issued :
    (rf ⨾ rmw)＊ ⨾ ⦗issued T⦘ ⊆ (rf ⨾ rmw ⨾ ⦗issued T⦘)＊.
  Proof using WF TLSCOH IORDCOH IMMCON.
    intros x y HH. destruct_seq_r HH as II.
    apply clos_rt_rtn1 in HH.
    induction HH as [|y z TT].
    { apply rt_refl. }
    apply rt_end. right. exists y.
    split.
    2: apply seqA; basic_solver.
    apply IHHH.
    apply ar_rfrmw_I_in_I. exists z.
    apply seq_eqv_lr. splits; auto.
    2: by right.
    red in TT. desf. apply (wf_rfD WF) in TT. unfolder in TT. desf.
  Qed.

  Lemma fwbob_I_in_C:
    dom_rel (fwbob ⨾ ⦗issued T⦘) ⊆₁ covered T. 
  Proof using WF TLSCOH IORDCOH IMMCON. 
    unfold covered, issued. unfolder. ins. desc. destruct y0; ins; subst.
    exists (mkTL ta_cover x). splits; auto.    
    apply iord_coh_implies_iord_simpl_coh in IORDCOH; auto. apply IORDCOH.
    eexists. apply seq_eqv_r. split; eauto. red. do 3 left. right.
    red. apply seq_eqv_l. splits; vauto. red. apply seq_eqv_r. split; vauto.
    red. apply seq_eqv_r. split; auto.
    apply issuedW. vauto.
  Qed. 
    

  Lemma dom_W_Rel_sb_loc_I_in_C :
    dom_rel (⦗W ∩₁ Rel⦘ ⨾ sb ∩ same_loc ⨾ ⦗W⦘ ⨾ ⦗issued T⦘) ⊆₁ covered T.
  Proof using WF TLSCOH IORDCOH IMMCON.
    arewrite (issued T ⊆₁ dom_cond fwbob (covered T)).
    { apply dom_rel_to_cond, fwbob_I_in_C. }
    rewrite <- !seqA.
    rewrite dom_cond_elim1; [basic_solver 21|].
    unfold imm_bob.fwbob.
    basic_solver 12.
  Qed. 

  Lemma I_eq_EW_I : issued T ≡₁ E ∩₁ W ∩₁ issued T.
  Proof using WF TLSCOH.
    split; [|clear; basic_solver].
    generalize issuedW, issuedE.
    basic_solver.
  Qed.

  Lemma W_rel_sb_loc_W_CI :
    (⦗W ∩₁ Rel⦘ ⨾ sb ∩ same_loc ⨾ ⦗W⦘) ⨾ ⦗covered T ∪₁ issued T⦘ ⊆
    ⦗covered T ∪₁ issued T⦘ ⨾ (⦗W ∩₁ Rel⦘ ⨾ sb ∩ same_loc ⨾ ⦗W⦘).
  Proof using WF TLSCOH IORDCOH IMMCON.
    (* case_refl _; [basic_solver|]. *)
    rewrite !seqA.
    arewrite (⦗W⦘ ⨾ ⦗covered T ∪₁ issued T⦘ ⊆ ⦗W⦘ ⨾ ⦗issued T⦘).
    { rewrite <- !id_inter. apply eqv_rel_mori.
      rewrite set_inter_union_r. rewrite <- set_interK with (s := W), set_interA.
      rewrite w_covered_issued. basic_solver. }
    generalize dom_W_Rel_sb_loc_I_in_C. basic_solver 12.
  Qed. 

  Lemma sb_W_rel_CI :
    (sb ⨾ ⦗W ∩₁ Rel⦘) ⨾ ⦗covered T ∪₁ issued T⦘ ⊆ ⦗covered T ∪₁ issued T⦘ ⨾ (sb ⨾ ⦗W ∩₁ Rel⦘).
  Proof using RELCOV WF TLSCOH IORDCOH IMMCON.
    generalize RELCOV, dom_sb_covered.
    basic_solver 12.
  Qed.

  Lemma W_Rel_sb_loc_I : dom_rel (⦗W ∩₁ Rel⦘ ⨾  (sb ∩ same_loc) ⨾ ⦗W ∩₁ issued T⦘) ⊆₁ issued T.
  Proof using WF TLSCOH IORDCOH IMMCON.
    generalize dom_W_Rel_sb_loc_I_in_C, w_covered_issued. basic_solver 21.
  Qed.

  Lemma sb_loc_issued  :
    ⦗W ∩₁ Rel⦘ ⨾ sb ∩ same_loc ⨾ ⦗W⦘ ⨾ ⦗issued T⦘ ⊆ 
               ⦗covered T⦘ ⨾ ⦗W ∩₁ Rel⦘ ⨾ sb ∩ same_loc ⨾ ⦗W⦘.
  Proof using WF TLSCOH IORDCOH IMMCON.
    seq_rewrite (dom_rel_helper dom_W_Rel_sb_loc_I_in_C).
    basic_solver.
  Qed.

  Lemma dom_F_sb_I_in_C :
    dom_rel (⦗F ∩₁ Acq/Rel⦘ ⨾ sb ⨾ ⦗issued T⦘) ⊆₁ covered T.
  Proof using WF TLSCOH IORDCOH IMMCON. 
    arewrite (issued T ⊆₁ dom_cond fwbob (covered T)).
    { apply dom_rel_to_cond, fwbob_I_in_C. }
    rewrite <- !seqA.
    rewrite dom_cond_elim1; [basic_solver 21|].
    unfold imm_bob.fwbob.
    basic_solver 12.
  Qed. 

  Lemma F_sb_I_in_C  :
    ⦗F ∩₁ Acq/Rel⦘ ⨾ sb ⨾ ⦗issued T⦘ ⊆ ⦗covered T⦘ ⨾ ⦗F ∩₁ Acq/Rel⦘ ⨾ sb.
  Proof using WF TLSCOH IORDCOH IMMCON. 
    seq_rewrite (dom_rel_helper dom_F_sb_I_in_C). basic_solver.
  Qed.

  Lemma dom_F_Rel_sb_I_in_C :  dom_rel (⦗F ∩₁ Rel⦘ ⨾  sb ⨾ ⦗issued T⦘) ⊆₁ covered T.
  Proof using RELCOV WF TLSCOH IORDCOH IMMCON.
    etransitivity; [|apply dom_F_sb_I_in_C]; mode_solver 21.
  Qed.

  Lemma dom_F_Acq_sb_I_in_C :  dom_rel (⦗F ∩₁ Acq⦘ ⨾  sb ⨾ ⦗issued T⦘) ⊆₁ covered T.
  Proof using RELCOV WF TLSCOH IORDCOH IMMCON. 
    etransitivity; [|apply dom_F_sb_I_in_C]; mode_solver 12. 
  Qed.
  
  Lemma dom_release_issued :
    dom_rel (release ⨾ ⦗ issued T ⦘) ⊆₁ covered T.
  Proof using WF IMMCON RELCOV TLSCOH IORDCOH.
    unfold imm_s_hb.release, imm_s_hb.rs.
    rewrite !seqA.
    sin_rewrite rf_rmw_issued_rfi_rmw_issued.
    rewrite (dom_r (wf_rmwD WF)) at 1.
    arewrite (⦗W⦘ ⨾ (rfi ⨾ rmw ⨾ ⦗W⦘)＊ ⊆ (rfi ⨾ rmw)＊ ⨾ ⦗W⦘).
    { rewrite rtE; relsf; unionL; [basic_solver|].
      rewrite <- seqA; rewrite inclusion_ct_seq_eqv_r; basic_solver. }
    rewrite (rmw_in_sb_loc WF) at 1; rewrite (rfi_in_sbloc' WF).
    generalize (@sb_same_loc_trans G); ins; relsf.
    rewrite !crE; relsf; unionL; splits.
    { revert RELCOV; basic_solver 21. }
    { generalize dom_W_Rel_sb_loc_I_in_C. basic_solver 21. }
    2: generalize (@sb_trans G).
    all: generalize dom_F_Rel_sb_I_in_C; basic_solver 40.
  Qed.

  Lemma release_issued :
    release ⨾ ⦗ issued T ⦘ ⊆ ⦗covered T⦘ ⨾ release.
  Proof using WF RELCOV IMMCON TLSCOH IORDCOH.
    seq_rewrite (dom_rel_helper dom_release_issued).
    basic_solver.
  Qed.

  Lemma dom_release_rf_covered :
    dom_rel (release ⨾ rf ⨾ ⦗ covered T ⦘) ⊆₁ covered T.
  Proof using WF RELCOV IMMCON TLSCOH IORDCOH.
    generalize dom_release_issued.
    generalize dom_rf_covered.
    basic_solver 21.
  Qed.

  Lemma release_rf_covered :
    release ⨾ rf ⨾ ⦗ covered T ⦘ ⊆ ⦗ covered T ⦘ ⨾ release ⨾ rf.
  Proof using WF RELCOV IMMCON TLSCOH IORDCOH.
    seq_rewrite (dom_rel_helper dom_release_rf_covered).
    basic_solver.
  Qed.

  Lemma dom_sb_W_rel_issued  :
    dom_rel (sb ⨾ ⦗W ∩₁ Rel⦘ ⨾ ⦗issued T⦘) ⊆₁ covered T.
  Proof using WF TLSCOH IORDCOH IMMCON.
    arewrite (issued T ⊆₁ dom_cond fwbob (covered T)).
    { apply dom_rel_to_cond, fwbob_I_in_C. }
    rewrite <- !seqA.
    rewrite dom_cond_elim1; [basic_solver 21|].
    unfold imm_bob.fwbob.
    basic_solver 12.
  Qed.

  Lemma sb_W_rel_issued  :
    sb ⨾ ⦗W ∩₁ Rel⦘ ⨾ ⦗issued T⦘ ⊆ ⦗covered T⦘ ⨾ sb ⨾ ⦗W ∩₁ Rel⦘.
  Proof using WF TLSCOH IORDCOH IMMCON.
    seq_rewrite (dom_rel_helper dom_sb_W_rel_issued).
    basic_solver.
  Qed.

  Lemma dom_sw_covered :
    dom_rel (sw ⨾ ⦗ covered T ⦘) ⊆₁ covered T.
  Proof using WF RELCOV IMMCON TLSCOH IORDCOH.
    unfold imm_s_hb.sw.
    generalize dom_sb_covered.
    generalize dom_release_rf_covered.
    basic_solver 21.
  Qed.

  Lemma sw_covered : sw ⨾ ⦗ covered T ⦘ ⊆ ⦗covered T⦘ ⨾ sw.
  Proof using WF RELCOV IMMCON TLSCOH IORDCOH.
    seq_rewrite (dom_rel_helper dom_sw_covered).
    basic_solver.
  Qed.

  Lemma hb_covered :
    hb ⨾ ⦗ covered T ⦘ ⊆ ⦗covered T⦘ ⨾ hb.
  Proof using WF RELCOV IMMCON TLSCOH IORDCOH.
    unfold imm_s_hb.hb.
    assert (A: (sb ∪ sw) ⨾ ⦗covered T⦘ ⊆ ⦗covered T⦘ ⨾ (sb ∪ sw)⁺).
    { relsf.
      rewrite sb_covered, sw_covered.
      rewrite <- ct_step; basic_solver. }
    unfold imm_s_hb.hb.
    eapply ct_ind_left with (P:= fun r => r ⨾ ⦗covered T⦘); eauto with hahn.
    intros k H; rewrite !seqA, H.
    sin_rewrite A.
    arewrite ((sb ∪ sw)⁺ ⊆ (sb ∪ sw)＊) at 1.
    relsf.
  Qed.

  Lemma dom_hb_covered :
    dom_rel (hb ⨾ ⦗ covered T ⦘) ⊆₁ covered T.
  Proof using WF RELCOV IMMCON TLSCOH IORDCOH.
    rewrite hb_covered; basic_solver 10.
  Qed.

  Lemma dom_urr_covered l:
    dom_rel (urr l ⨾ ⦗ covered T ⦘) ⊆₁ issued T.
  Proof using WF IMMCON RELCOV TLSCOH IORDCOH.
    unfold CombRelations.urr.
    generalize dom_rf_covered.
    generalize dom_sc_covered.
    generalize dom_hb_covered.
    generalize w_covered_issued.
    basic_solver 21.
  Qed.

  Lemma urr_covered l:
    urr l ⨾ ⦗ covered T ⦘ ⊆ ⦗issued T⦘ ⨾ urr l.
  Proof using WF IMMCON RELCOV TLSCOH IORDCOH.
    rewrite (dom_rel_helper (@dom_urr_covered l)).
    basic_solver.
  Qed.

  Lemma msg_rel_issued l:
    dom_rel (msg_rel l ⨾ ⦗ issued T ⦘) ⊆₁ issued T.
  Proof using WF IMMCON RELCOV TLSCOH IORDCOH.
    unfold CombRelations.msg_rel.
    generalize dom_release_issued.
    generalize (@dom_urr_covered l).
    basic_solver 21.
  Qed.

End TlsProperties.
