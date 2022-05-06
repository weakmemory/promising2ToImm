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

Definition coverable T :=
  E ∩₁ event ↑₁ (dom_cond (iord G sc) T ∩₁ action ↓₁ eq ta_cover). 
  (* E ∩₁ dom_cond sb (covered T) ∩₁  *)
  (*   ((W ∩₁ issued T) ∪₁ *)
  (*    (R ∩₁ (dom_cond rf (issued T))) ∪₁ *)
  (*    (F ∩₁ (dom_cond sc (covered T)))). *)

Definition issuable T :=
  E ∩₁ W ∩₁ event ↑₁ (dom_cond (iord G sc) T ∩₁ action ↓₁ eq ta_issue). 
(* Definition issuable T e := *)
(*   E ∩₁ W ∩₁ *)
(*   (dom_cond fwbob (covered T)) ∩₁ *)
(*   (dom_cond (⦗W⦘ ⨾ (ar ∪ rf ⨾ (ppo ∩ same_loc))⁺) (issued T)). *)

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

  Lemma coveredE:
    covered T ⊆₁ E.
  Proof using WF TLSCOH.
    unfold covered. rewrite (tlsc_E WF TLSCOH). basic_solver.
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

  (* TODO: move to imm/travorder *)
  Lemma dom_rel_collect_event (b : trav_action) A B r
        (UU : B ⊆₁ action ↓₁ eq b)
        (AA : dom_rel (⦗action ↓₁ eq b⦘ ⨾ event ↓ r ⨾ ⦗A⦘) ⊆₁ B) :
    dom_rel (r ⨾ ⦗event ↑₁ A⦘) ⊆₁ event ↑₁ B.
  Proof using.
    clear -AA UU. unfolder. ins. desf.
    exists (mkTL b x); ins.
    split; auto.
    apply AA.
    unfolder. do 2 eexists; ins; eauto.
    splits; eauto.
  Qed.

  (* TODO: move somewhere *)
  Lemma dom_rel_iord_parts (a1 a2: trav_action) (r: relation actid)
        (R_IORD: ⦗action ↓₁ eq a1⦘ ⨾ event ↓ r ⨾ ⦗action ↓₁ eq a2⦘
                 ⊆ iord_simpl G sc):
    dom_rel (r ⨾ ⦗event ↑₁ (T ∩₁ action ↓₁ eq a2)⦘)
    ⊆₁ event ↑₁ (T ∩₁ action ↓₁ eq a1).
  Proof using WF TLSCOH IORDCOH IMMCON. 
    eapply dom_rel_collect_event with (b := a1); [basic_solver| ].
    apply set_subset_inter_r. split; [| basic_solver].
    rewrite set_interC, id_inter. sin_rewrite R_IORD.
    eapply iord_coh_implies_iord_simpl_coh; eauto.
  Qed.

  Lemma dom_sb_covered :
    dom_rel (sb ⨾ ⦗ covered T ⦘) ⊆₁ covered T.
  Proof using WF TLSCOH IORDCOH IMMCON.
    apply dom_rel_iord_parts. unfold iord_simpl, SB.
    rewrite <- ct_step, <- inclusion_union_r1 with (r' := sc). intuition. 
  Qed. 

  Lemma sb_covered :
    sb ⨾ ⦗ covered T ⦘ ≡ ⦗ covered T ⦘ ⨾ sb ⨾ ⦗ covered T ⦘.
  Proof using WF TLSCOH IORDCOH IMMCON.
    rewrite (dom_rel_helper dom_sb_covered). basic_solver.
  Qed.

  Lemma dom_rf_covered :
    dom_rel (rf ⨾ ⦗covered T⦘) ⊆₁ issued T.
  Proof using WF TLSCOH IORDCOH IMMCON. 
    apply dom_rel_iord_parts. unfold iord_simpl, RF.
    rewrite crE, <- inclusion_union_r2 with (r := ⦗_⦘).
    rewrite (dom_l (wf_rfD WF)) at 1. intuition.
  Qed. 

  Lemma rf_covered :
    rf ⨾ ⦗ covered T ⦘ ≡ ⦗ issued T ⦘ ⨾ rf ⨾ ⦗ covered T ⦘.
  Proof using WF TLSCOH IORDCOH IMMCON.
    rewrite (dom_rel_helper dom_rf_covered). basic_solver.
  Qed.

  Lemma dom_sc_covered :
    dom_rel (sc ⨾ ⦗ covered T ⦘) ⊆₁ covered T.
  Proof using WF TLSCOH IORDCOH IMMCON.
    apply dom_rel_iord_parts. unfold iord_simpl, SB.
    rewrite <- ct_step, <- inclusion_union_r2 with (r := sb). intuition. 
  Qed.

  Lemma sc_covered  :
    sc ⨾ ⦗covered T⦘ ⊆ ⦗covered T⦘ ⨾ sc.
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

  Lemma ar_rf_ppo_loc_ct_I_in_I  :
    dom_rel (⦗W⦘ ⨾ (ar ∪ rf ⨾ (ppo ∩ same_loc))⁺ ⨾ ⦗issued T⦘) ⊆₁ issued T.
  Proof using WF TLSCOH IORDCOH IMMCON.
    arewrite (⦗issued T⦘ ⊆ ⦗W⦘ ⨾ ⦗issued T⦘) at 1.
    { rewrite <- id_inter. apply eqv_rel_mori. split; auto using issuedW. }
    rewrite <- !seqA. apply dom_rel_iord_parts. rewrite !seqA.
    unfold iord_simpl, AR. intuition. 
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
    arewrite (⦗issued T⦘ ⊆ ⦗W⦘ ⨾ ⦗issued T⦘) at 1.
    { rewrite <- id_inter. apply eqv_rel_mori. split; auto using issuedW. }
    rewrite <- seqA. apply dom_rel_iord_parts. unfold iord_simpl, FWBOB. intuition.
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

  Lemma dom_c_acq_covered i l A:
    dom_rel (c_acq i l A ⨾ ⦗ covered T ⦘) ⊆₁ issued T.
  Proof using WF IMMCON RELCOV TLSCOH IORDCOH. 
    unfold CombRelations.c_acq.
    generalize (@dom_urr_covered l).
    generalize dom_release_issued.
    generalize dom_rf_covered.
    basic_solver 21.
  Qed.

  Lemma c_acq_covered i l A:
    c_acq i l A ⨾ ⦗ covered T ⦘ ⊆ ⦗issued T⦘ ⨾ c_acq i l A.
  Proof using WF IMMCON  RELCOV TLSCOH IORDCOH.
    rewrite (dom_rel_helper (@dom_c_acq_covered i l A)).
    basic_solver.
  Qed.

  Lemma dom_c_cur_covered i l A:
    dom_rel (c_cur i l A ⨾ ⦗ covered T ⦘) ⊆₁ issued T.
  Proof using WF IMMCON  RELCOV TLSCOH IORDCOH.
    unfold CombRelations.c_cur.
    generalize (@dom_urr_covered l).
    basic_solver 21.
  Qed.

  Lemma c_cur_covered i l A:
    c_cur i l A ⨾ ⦗ covered T ⦘ ⊆ ⦗issued T⦘ ⨾ c_cur i l A.
  Proof using WF IMMCON RELCOV TLSCOH IORDCOH.
    seq_rewrite (dom_rel_helper (@dom_c_cur_covered i l A)).
    basic_solver.
  Qed.


  Lemma dom_c_rel_covered i l l' A:
    dom_rel (c_rel i l l' A ⨾ ⦗ covered T ⦘) ⊆₁ issued T.
  Proof using WF IMMCON RELCOV TLSCOH IORDCOH. 
    unfold CombRelations.c_rel.
    generalize (@dom_urr_covered l).
    basic_solver 21.
  Qed.

  Lemma c_rel_covered i l l' A:
    c_rel i l l' A ⨾ ⦗ covered T ⦘ ⊆ ⦗issued T⦘ ⨾ c_rel i l l' A.
  Proof using WF IMMCON RELCOV TLSCOH IORDCOH. 
    seq_rewrite (dom_rel_helper (@dom_c_rel_covered i l l' A)).
    basic_solver.
  Qed.

  Lemma t_acq_covered l thread:
    t_acq thread l (covered T) ⊆₁ issued T.
  Proof using WF IMMCON RELCOV TLSCOH IORDCOH.
    unfold CombRelations.t_acq.
    rewrite (dom_r (wf_c_acqD G sc thread l (covered T))).
    arewrite (⦗(Tid_ thread ∪₁ Init) ∩₁ covered T⦘ ⊆ ⦗covered T⦘) by basic_solver.
    rewrite c_acq_covered.
    basic_solver.
  Qed.

  Lemma t_cur_covered l thread:
    t_cur thread l (covered T) ⊆₁ issued T.
  Proof using WF IMMCON RELCOV TLSCOH IORDCOH. 
    etransitivity; [by apply t_cur_in_t_acq|].
      by apply t_acq_covered.
  Qed.

  Lemma t_rel_covered l l' thread:
    t_rel thread l l' (covered T) ⊆₁ issued T.
  Proof using WF IMMCON RELCOV TLSCOH IORDCOH.
    etransitivity; [by apply t_rel_in_t_cur|].
      by apply t_cur_covered.
  Qed.

  Lemma S_tm_covered l :
    S_tm l (covered T) ⊆₁ issued T.
  Proof using WF RELCOV IMMCON TLSCOH IORDCOH. 
    unfold CombRelations.S_tm, CombRelations.S_tmr.
    generalize dom_hb_covered.
    generalize w_covered_issued.
    generalize dom_release_issued.
    generalize dom_rf_covered.
    basic_solver 21.
  Qed.

  Lemma msg_rel_issued l:
    dom_rel (msg_rel l ⨾ ⦗ issued T ⦘) ⊆₁ issued T.
  Proof using WF IMMCON RELCOV TLSCOH IORDCOH.
    unfold CombRelations.msg_rel.
    generalize dom_release_issued.
    generalize (@dom_urr_covered l).
    basic_solver 21.
  Qed.

Section HbProps.

Notation "'C'" := (covered T).
Notation "'I'" := (issued  T).

Lemma sw_in_Csw_sb :
  sw ⨾ ⦗C ∪₁ dom_rel (sb^? ⨾ ⦗ I ⦘)⦘ ⊆ ⦗ C ⦘ ⨾ sw ∪ sb.
Proof using WF RELCOV IMMCON TLSCOH IORDCOH.
  rewrite !id_union. rewrite seq_union_r. 
  unionL.
  { rewrite sw_covered; eauto. basic_solver. }
  assert (forall (s : actid -> Prop), s ∪₁ set_compl s ≡₁ fun _ => True) as AA.
  { split; [basic_solver|].
    unfolder. ins. apply classic. }
  arewrite (sw ⊆ ⦗ C ∪₁ set_compl C ⦘ ⨾ sw) at 1.
  { rewrite AA. by rewrite seq_id_l. }
  rewrite id_union, !seq_union_l.
  apply union_mori; [basic_solver|].
  rewrite (dom_r (wf_swD WF)).
  rewrite sw_in_ar0; auto.
  remember (⦗Rel⦘ ⨾ (⦗F⦘ ⨾ sb)^? ⨾ ⦗W⦘ ⨾ (sb ∩ same_loc)^? ⨾ ⦗W⦘ ⨾ (rfe ∪ ar_int G)⁺) as ax.
  rewrite !seq_union_l, !seq_union_r.
  unionL; [|basic_solver].
  subst ax. rewrite !seqA.
  arewrite ((sb ∩ same_loc)^? ⨾ ⦗W⦘ ⊆ (sb ∩ same_loc)^? ⨾ ⦗W⦘ ⨾ ⦗W⦘) by basic_solver. 
  arewrite (⦗Rel⦘ ⨾ (⦗F⦘ ⨾ sb)^? ⨾ ⦗W⦘ ⨾ (sb ∩ same_loc)^? ⨾ ⦗W⦘ ⊆ release).
  { unfold imm_s_hb.release, imm_s_hb.rs. by rewrite <- inclusion_id_rt, seq_id_r. }
  enough (dom_rel (⦗W⦘ ⨾ (rfe ∪ ar_int G)⁺ ⨾ ⦗FR ∩₁ Acq⦘ ⨾ ⦗dom_rel (sb^? ⨾ ⦗I⦘)⦘) ⊆₁ I) as BB.
  { rewrite (dom_rel_helper BB).
    seq_rewrite (dom_rel_helper dom_release_issued).
    basic_solver. }
  rewrite <- !seqA. rewrite dom_rel_eqv_dom_rel. rewrite !seqA.
  arewrite (⦗FR ∩₁ Acq⦘ ⨾ sb^? ⊆ (rfe ∪ ar_int G)^?).
  { rewrite !crE, !seq_union_r. apply union_mori; [basic_solver|].
    unionR right. rewrite set_inter_union_l, id_union, seq_union_l.
    rewrite sb_from_r_acq_in_bob.
    arewrite (Acq ⊆₁ Acq/Rel) by mode_solver.
    rewrite sb_from_f_in_bob. rewrite bob_in_ar_int. eauto with hahn. }
  seq_rewrite ct_cr.
  arewrite (rfe ∪ ar_int G ⊆ ar). by apply ar_ct_I_in_I.
Qed.

Lemma hb_in_Chb_sb :
  hb ⨾ ⦗C ∪₁ dom_rel (sb^? ⨾ ⦗ I ⦘)⦘ ⊆ ⦗ C ⦘ ⨾ hb ∪ sb.
Proof using WF RELCOV IMMCON TLSCOH IORDCOH. 
  unfold imm_s_hb.hb.
  intros x y HH.
  destruct_seq_r HH as DOM.
  apply clos_trans_tn1 in HH.
  induction HH as [y [HH|HH]|y z AA].
  { by right. }
  { assert ((⦗C⦘ ⨾ sw ∪ sb) x y) as [ZZ|ZZ].
    3: by right.
    2: { destruct_seq_l ZZ as CX.
         left. apply seq_eqv_l. split; auto.
         apply ct_step. by right. }
    apply sw_in_Csw_sb; auto. apply seq_eqv_r. splits; auto. }
  assert (sb y z -> (C ∪₁ dom_rel (sb^? ⨾ ⦗I⦘)) y) as DOMY.
  { intros SB.
    destruct DOM as [DOM|DOM].
    2: { right. generalize (@sb_trans G) SB DOM. basic_solver 10. }
    left.
    eapply dom_sb_covered; eauto. eexists.
    apply seq_eqv_r. split; eauto. }

  assert ((C ∪₁ dom_rel (sb^? ⨾ ⦗I⦘)) y) as BB.
  2: { set (CC:=BB). apply IHHH in CC.
       destruct CC as [CC|CC].
       { left.
         destruct_seq_l CC as XX.
         apply seq_eqv_l. split; auto.
         (* TODO: is the last tactic needed? *)
         apply ct_ct. exists y. split; eauto; try by apply ct_step. }
       destruct AA as [AA|AA].
       { right. eapply (@sb_trans G); eauto. }
       assert ((sw ⨾ ⦗C ∪₁ dom_rel (sb^? ⨾ ⦗I⦘)⦘) y z) as DD.
       { apply seq_eqv_r. by split. }
       eapply sw_in_Csw_sb in DD; auto.
       destruct DD as [DD|DD].
       2: { right. eapply (@sb_trans G); eauto. }
       left.
       apply seq_eqv_l. split.
       2: { apply ct_ct. eexists.
            split; apply ct_step; [left|right]; eauto. }
       assert (C y) as CY.
       { by destruct_seq_l DD as XX. }
       eapply dom_sb_covered; eauto. eexists.
       apply seq_eqv_r. split; eauto. }
  destruct AA as [|AA]; [by intuition|].
  assert ((sw ⨾ ⦗C ∪₁ dom_rel (sb^? ⨾ ⦗I⦘)⦘) y z) as DD.
  { apply seq_eqv_r. by split. }
  eapply sw_in_Csw_sb in DD; auto.
  destruct DD as [DD|]; [|by intuition].
  left. by destruct_seq_l DD as CY.
Qed.

End HbProps.
  


End TlsProperties.
