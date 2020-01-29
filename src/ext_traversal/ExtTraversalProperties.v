Require Import Setoid.
From hahn Require Import Hahn.
From imm Require Import Events Execution Execution_eco
     imm_bob imm_s_ppo imm_s imm_s_hb CombRelations AuxDef.
Require Import AuxRel AuxRel2.
Require Import TraversalConfig Traversal.
Require Import ExtTraversalConfig.
Require Import ImmProperties.

Set Implicit Arguments.

Section ExtTraversalProperties.
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
Notation "'rmw_dep'" := G.(rmw_dep).
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
Notation "'rppo'" := G.(rppo).

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

Variable T : ext_trav_config.
Variable ETCCOH : etc_coherent G sc T.

Notation "'S'" := (reserved T).
Notation "'C'" := (ecovered T).
Notation "'I'" := (eissued  T).

Lemma dom_rf_rmw_S_in_I : dom_rel (rf ⨾ rmw ⨾ ⦗S⦘) ⊆₁ I.
Proof using WF ETCCOH.
  rewrite rmw_W_ex, !seqA.
  arewrite (⦗W_ex⦘ ⨾ ⦗S⦘ ⊆ ⦗S ∩₁ W_ex⦘) by basic_solver.
  rewrite ETCCOH.(etc_S_W_ex_rfrmw_I).
  rewrite <- seqA with (r2:=rmw).
  intros x [y HH].
  destruct_seq_r HH as BB.
  destruct BB as [z BB].
  destruct_seq_l BB as IZ.
  assert (x = z); desf.
  eapply wf_rfrmwf; eauto.
Qed.

Lemma dom_rf_rmw_S : dom_rel (rf ⨾ rmw ⨾ ⦗S⦘) ⊆₁ S.
Proof using WF ETCCOH.
  rewrite <- ETCCOH.(etc_I_in_S) at 2.
  apply dom_rf_rmw_S_in_I.
Qed.

Lemma rf_rmw_S : rf ⨾ rmw ⨾ ⦗S⦘ ≡
                 ⦗S⦘ ⨾ rf ⨾ rmw ⨾ ⦗S⦘.
Proof using WF ETCCOH.
  apply dom_rel_helper.
  apply dom_rf_rmw_S.
Qed.

Lemma dom_rf_rmw_rt_S : dom_rel ((rf ⨾ rmw)＊ ⨾ ⦗S⦘) ⊆₁ S.
Proof using WF ETCCOH.
  cut ((rf ⨾ rmw)＊ ⨾ ⦗S⦘ ⊆ ⦗S⦘ ⨾ (fun _ _ => True)).
  { unfolder; ins; desf; eauto 21; eapply H; splits; eauto 10. }
  apply rt_ind_left with (P:= fun r => r ⨾ ⦗S⦘).
  { auto with hahn. }
  { basic_solver. }
  intros k H.
  sin_rewrite rmw_W_ex; rewrite !seqA.
  sin_rewrite H.
  arewrite_id ⦗W_ex⦘. rewrite seq_id_l.
  seq_rewrite rf_rmw_S.
  basic_solver.
Qed.

Lemma dom_rf_rmw_ct_S : dom_rel ((rf ⨾ rmw)⁺ ⨾ ⦗S⦘) ⊆₁ S.
Proof using WF ETCCOH.
  rewrite inclusion_t_rt.
  apply dom_rf_rmw_rt_S.
Qed.

Lemma rfe_rmw_S : dom_rel (rfe ⨾ rmw ⨾ ⦗S⦘) ⊆₁ I.
Proof using WF ETCCOH.
  arewrite (rfe ⊆ rf).
  apply dom_rf_rmw_S_in_I.
Qed.

Lemma nI_rfrmw_in_rfirmw :
  ⦗set_compl I⦘ ⨾ rf ⨾ rmw ⨾ ⦗S⦘ ≡ ⦗set_compl I⦘ ⨾ rfi ⨾ rmw ⨾ ⦗S⦘.
Proof using WF ETCCOH.
  split.
  2: by arewrite (rfi ⊆ rf).
  rewrite rfi_union_rfe. rewrite !seq_union_l, !seq_union_r.
  unionL; [done|].
  rewrite (dom_rel_helper rfe_rmw_S).
  basic_solver.
Qed.

Lemma rt_rf_rmw_S' :
  (rf ⨾ rmw)＊ ⨾ ⦗S⦘ ⊆ (rfi ⨾  rmw)＊ ⨾ (⦗I⦘ ⨾ (rf ⨾ rmw)⁺)^? ⨾ ⦗S⦘.
Proof using WF ETCCOH.
  apply rt_ind_left with (P:= fun r => r ⨾ ⦗S⦘).
  { by eauto with hahn. }
  { basic_solver 12. }
  intros k H. rewrite !seqA, H.
  rewrite rfi_union_rfe at 1. rewrite !seq_union_l; unionL.
  { hahn_frame. rewrite rt_begin at 2. basic_solver 21. }
  arewrite ((rfi ⨾ rmw)＊ ⨾ (⦗I⦘ ⨾ (rf ⨾ rmw)⁺)^? ⊆ (rf ⨾ rmw)＊).
  { arewrite (rfi ⊆ rf); arewrite_id (⦗I⦘); relsf. }
  relsf.
  rewrite (dom_rel_helper dom_rf_rmw_rt_S).
  seq_rewrite (dom_rel_helper rfe_rmw_S).
  arewrite (rfe ⊆ rf).
  rewrite ct_begin.
  basic_solver 21.
Qed.

(* Lemma rt_rf_rmw_S'' : *)
(*   (rfe ⨾ rmw ⨾ (rfi ⨾ rmw)＊)⁺ ⨾ sb^? ⨾ ⦗S⦘ ⊆  *)
(*   ⦗I⦘ ⨾ (rfe ⨾ rmw ⨾ (rfi ⨾ rmw)＊)⁺ ⨾ sb^? ⨾ ⦗S⦘. *)
(* Proof using WF ETCCOH. *)
(*   apply ct_ind_left with (P:= fun r => r ⨾ sb^? ⨾ ⦗S⦘). *)
(*   { by eauto with hahn. } *)
(*   { rewrite !seqA. *)
(*     cut (dom_rel (rfe ⨾ rmw ⨾ (rfi ⨾ rmw)＊ ⨾  sb^? ⨾ ⦗S⦘)  ⊆₁ I). *)
(*     { intro A. *)
(*       rewrite (dom_rel_helper A). *)
(*       rewrite <- ct_step; basic_solver 12. } *)
(*     arewrite (rfi ⊆ sb). *)
(*     rewrite (rmw_in_sb WF) at 2. *)
(*     generalize (@sb_trans G); ins; relsf. *)
(*     arewrite (⦗S⦘ ⊆ ⦗S⦘ ⨾ ⦗S⦘) by basic_solver. *)
(*     rewrite (reservedW WF ETCCOH) at 1. *)
(*     sin_rewrite (rmw_sb_cr_W_in_rppo WF). *)
(*     generalize (etc_rppo_S ETCCOH).  *)
(*     basic_solver 12. } *)
(*   intros k H.  *)
(*   rewrite !seqA, H. *)
(*   cut (dom_rel (rfe ⨾ rmw ⨾ (rfi ⨾ rmw)＊ ⨾ ⦗I⦘)  ⊆₁ I). *)
(*   { intro A. *)
(*     seq_rewrite (dom_rel_helper A). *)
(*     arewrite_id ⦗I⦘ at 2; rels. *)
(*     rewrite ct_begin at 2. *)
(*     rewrite inclusion_t_rt. *)
(*     basic_solver 21. } *)
(*   arewrite (rfi ⊆ sb). *)
(*   rewrite (rmw_in_sb WF) at 2. *)
(*   generalize (@sb_trans G); ins; relsf. *)
(*   arewrite (⦗I⦘ ⊆ ⦗I⦘ ⨾ ⦗I⦘) by basic_solver. *)
(*   rewrite (eissuedW ETCCOH) at 1. *)
(*   rewrite (etc_I_in_S ETCCOH) at 1. *)
(*   sin_rewrite (rmw_sb_cr_W_in_rppo WF). *)
(*   generalize (etc_rppo_S ETCCOH); basic_solver 12. *)
(* Qed. *)

Lemma nI_rfrmw_rt_in_rfirmw_rt :
  ⦗set_compl I⦘ ⨾ (rf ⨾ rmw)＊ ⨾ ⦗S⦘ ⊆ ⦗set_compl I⦘ ⨾ (rfi ⨾ rmw)＊ ⨾ ⦗S⦘.
Proof using WF ETCCOH.
  rewrite rt_rf_rmw_S'.
  rewrite crE. rewrite !seq_union_l, !seq_union_r, !seq_id_l.
  unionL; [done|].
  rewrite !seqA.
  arewrite (⦗set_compl I⦘ ⨾ (rfi ⨾ rmw)＊ ⨾ ⦗I⦘ ⊆ ∅₂).
  2: basic_solver.
  arewrite (rfi ⊆ rf).
  intros x y HH. apply seq_eqv_l in HH. destruct HH as [AA HH].
  apply AA. eapply rfrmw_rt_I_in_I; eauto.
  { apply ETCCOH. }
  eexists. apply HH.
Qed.

Lemma dom_rfe_rmw_ct_rfi_Acq_sb_S_in_I :
  dom_rel (rfe ⨾ rmw ⨾ (rfi ⨾ rmw)＊ ⨾ rfi ⨾ ⦗Acq⦘ ⨾ sb^? ⨾ ⦗S⦘) ⊆₁ I.
Proof using WF ETCCOH.
seq_rewrite rt_seq_swap.
rewrite !seqA.
arewrite (rmw ⨾ rfi ⨾ (rmw ⨾ rfi)＊ ⊆ (rmw ⨾ rfi)＊).
{ rewrite rtE. rewrite ct_begin at 2. 
  basic_solver 21. }
rewrite (dom_r WF.(wf_rfeD)), !seqA.
rewrite (dom_r WF.(wf_rfiD)).
arewrite (⦗R⦘ ⨾ (rmw ⨾ rfi ⨾ ⦗R⦘)＊ ⊆ (rmw ⨾ rfi)＊ ⨾ ⦗R⦘).
{ rewrite !rtE, <- !seqA, inclusion_ct_seq_eqv_r.
  basic_solver. }
arewrite (⦗S⦘ ⊆ ⦗S⦘ ⨾ ⦗W⦘).
{ forward (eapply reservedW); eauto.
  basic_solver. }
arewrite (⦗R⦘ ⨾ ⦗Acq⦘ ⨾ sb^? ⨾ ⦗S⦘ ⨾ ⦗W⦘ ⊆ ⦗R⦘ ⨾ ⦗Acq⦘ ⨾ sb ⨾ ⦗S⦘).
{ type_solver 21. }
generalize (ETCCOH.(etc_dr_R_acq_I)).
basic_solver 21.
Qed.

Lemma co_next_to_imm_co_next w locw
      (LOC : loc w = Some locw)
      (WNEXT : exists wnext, (co ⨾ ⦗ S ⦘) w wnext) :
  exists wnext vnext,
    << NCOIMM   : immediate (co ⨾ ⦗ S ⦘) w wnext >> /\
    << ISSNEXT : S wnext >>  /\
    << CONEXT  : co w wnext >>  /\
    << ENEXT   : E wnext >>  /\
    << WNEXT   : W wnext >>  /\
    << LOCNEXT : Loc_ locw wnext >>  /\
    << VNEXT   : val wnext = Some vnext >> /\
    << NEQNEXT : wnext <> w >>.
Proof using WF ETCCOH.
  assert (exists wnext, immediate (co ⨾ ⦗ S ⦘) w wnext) as [wnext NIMMCO].
  { desc; eapply clos_trans_immediate2 in WNEXT.
    apply ct_begin in WNEXT; unfold seq in *; desc; eauto.
    generalize (co_trans WF); unfold transitive; basic_solver 21.
    generalize (co_irr WF); basic_solver 21.
    unfolder; ins; desc; hahn_rewrite (dom_r (wf_coE WF)) in REL.
    unfolder in REL; desc; eauto. }
  clear WNEXT.
  assert (S wnext /\ co w wnext) as [ISSNEXT CONEXT].
  { destruct NIMMCO as [AA _]. by destruct_seq_r AA as BB. }
  assert (E wnext) as ENEXT.
  { by apply ETCCOH.(etc_S_in_E). }
  assert (W wnext) as WNEXT.
  { by apply (reservedW WF ETCCOH). }
  assert (Loc_ locw wnext) as LOCNEXT.
  { apply WF.(wf_col) in CONEXT. by rewrite <- CONEXT. }
  assert (exists vnext, val wnext = Some vnext) as [vnext VNEXT].
  { unfold Events.val, is_w in *. desf.
    all: eexists; eauto. }
  exists wnext, vnext. splits; eauto.
  intros H; subst. by apply WF.(co_irr) in CONEXT.
Qed.

Lemma co_prev_to_imm_co_prev w locw
      (EW    : E w)
      (WW    : W w)
      (WNCOV : ~ ecovered T w)
      (LOC   : loc w = Some locw) :
  exists wprev vprev,
    << PCOIMM   : immediate (⦗ S ⦘ ⨾ co) wprev w >> /\
    << ISSPREV : S wprev >>  /\
    << COPREV  : co wprev w >>  /\
    << EPREV   : E wprev >>  /\
    << WPREV   : W wprev >>  /\
    << LOCPREV : Loc_ locw wprev >>  /\
    << VPREV   : val wprev = Some vprev >> /\
    << NEQPREV : wprev <> w >>.
Proof using WF IMMCON ETCCOH.
  assert (tc_coherent G sc (etc_TC T)) as TCCOH by apply ETCCOH.
  assert (~ is_init w) as WNINIT.
  { intros HH. apply WNCOV. eapply init_covered; eauto. by split. }
  assert (exists wprev, immediate (⦗ S ⦘ ⨾ co) wprev w) as [wprev PIMMCO].
  { assert ((⦗ S ⦘ ⨾ co) (InitEvent locw) w) as WPREV.
    { assert (W (InitEvent locw)) as WI.
      { by apply init_w. }
      assert (E (InitEvent locw)) as EI.
      { apply wf_init; auto. by exists w; split. }
      assert (eissued T (InitEvent locw)) as II.
      { apply (init_issued WF TCCOH). by split. }
      assert (S (InitEvent locw)) as IS.
      { by apply ETCCOH.(etc_I_in_S). }
      assert (InitEvent locw <> w) as NEQ.
      { intros H; subst. desf. }
      assert (loc (InitEvent locw) = Some locw) as LI.
      { unfold Events.loc. by rewrite WF.(wf_init_lab). }
      apply seq_eqv_l; split; auto.
      edestruct WF.(wf_co_total).
      3: by apply NEQ.
      1,2: split; [split|]; auto.
      { by rewrite LOC. }
      { done. }
      exfalso. cdes IMMCON. eapply Cint.
      eexists; split.
      2: { apply r_step. by apply Execution_eco.co_in_eco; apply H. }
      apply sb_in_hb. apply init_ninit_sb; auto. }
    desc; eapply clos_trans_immediate2 in WPREV.
    apply ct_end in WPREV; unfold seq in *; desc; eauto.
    generalize (co_trans WF); unfold transitive; basic_solver 21.
    generalize (co_irr WF); basic_solver 21.
    unfolder; ins; desc; hahn_rewrite (dom_r (wf_coE WF)) in REL0.
    unfolder in REL0; desc; eauto. }
  assert (S wprev /\ co wprev w) as [ISSPREV COPREV].
  { destruct PIMMCO as [AA _]. by destruct_seq_l AA as BB. }
  assert (E wprev) as EPREV.
  { by apply ETCCOH.(etc_S_in_E). }
  assert (W wprev) as WPREV.
  { by apply (reservedW WF ETCCOH). }
  assert (Loc_ locw wprev) as LOCPREV.
  { apply WF.(wf_col) in COPREV. by rewrite COPREV. }
  assert (exists vprev, val wprev = Some vprev) as [vprev VPREV].
  { unfold Events.val, is_w in *. desf.
    all: eexists; eauto. }
  exists wprev, vprev. splits; eauto.
  intros H; subst. by apply WF.(co_irr) in COPREV.
Qed.

End ExtTraversalProperties.
