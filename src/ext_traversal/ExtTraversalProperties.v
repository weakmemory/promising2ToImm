Require Import Setoid.
From hahn Require Import Hahn.
From imm Require Import Events Execution Execution_eco
     imm_bob imm_s_ppo imm_s imm_s_hb CombRelations AuxDef AuxRel2.
Require Import AuxRel.
(* From imm Require Import TraversalConfig Traversal. *)
From imm Require Import FairExecution.
Require Import ExtTraversalConfig.
From imm Require Import TraversalOrder.
From imm Require Import TLSCoherency.
From imm Require Import IordCoherency.
From imm Require Import SimClosure. 
Require Import TlsEventSets.
Require Import Next. 
Require Import EventsTraversalOrder.


Set Implicit Arguments.

Section ExtTraversalProperties.
Variable G : execution.
Variable WF : Wf G.
Variable COM : complete G.
Variable sc : relation actid.
Variable IMMCON : imm_consistent G sc.

(* Notation "'acts'" := (acts G). *)
Notation "'sb'" := (sb G).
Notation "'rmw'" := (rmw G).
Notation "'data'" := (data G).
Notation "'addr'" := (addr G).
Notation "'ctrl'" := (ctrl G).
Notation "'rmw_dep'" := (rmw_dep G).
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
Notation "'rppo'" := (rppo G).

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

Variable T : trav_label -> Prop. 
(* Variable ETCCOH : etc_coherent G sc T. *)
Hypotheses (TCOH: tls_coherent G T)
           (ICOH: iord_coherent G sc T)
           (RCOH: reserve_coherent G T). 

Notation "'S'" := (reserved T).
Notation "'C'" := (covered T).
Notation "'I'" := (issued  T).

Lemma dom_rf_rmw_S_in_I : dom_rel (rf ⨾ rmw ⨾ ⦗S⦘) ⊆₁ I.
Proof using WF RCOH.
  rewrite rmw_W_ex, !seqA.
  arewrite (⦗W_ex⦘ ⨾ ⦗S⦘ ⊆ ⦗S ∩₁ W_ex⦘) by basic_solver.
  erewrite rcoh_S_W_ex_rfrmw_I; eauto. 
  rewrite <- seqA with (r2:=rmw).
  intros x [y HH].
  destruct_seq_r HH as BB.
  destruct BB as [z BB].
  destruct_seq_l BB as IZ.
  assert (x = z); desf.
  eapply wf_rfrmwf; eauto.
Qed.

Lemma dom_rf_rmw_S : dom_rel (rf ⨾ rmw ⨾ ⦗S⦘) ⊆₁ S.
Proof using WF RCOH.
  erewrite <- rcoh_I_in_S at 2; eauto. 
  apply dom_rf_rmw_S_in_I.
Qed.

Lemma rf_rmw_S : rf ⨾ rmw ⨾ ⦗S⦘ ≡
                 ⦗S⦘ ⨾ rf ⨾ rmw ⨾ ⦗S⦘.
Proof using WF RCOH.
  apply dom_rel_helper. apply dom_rf_rmw_S.
Qed.

Lemma dom_rf_rmw_rt_S : dom_rel ((rf ⨾ rmw)＊ ⨾ ⦗S⦘) ⊆₁ S.
Proof using WF RCOH. 
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
Proof using WF RCOH. 
  rewrite inclusion_t_rt. apply dom_rf_rmw_rt_S.
Qed.

Lemma rfe_rmw_S : dom_rel (rfe ⨾ rmw ⨾ ⦗S⦘) ⊆₁ I.
Proof using WF RCOH. 
  arewrite (rfe ⊆ rf). apply dom_rf_rmw_S_in_I.
Qed.

Lemma nI_rfrmw_in_rfirmw :
  ⦗set_compl I⦘ ⨾ rf ⨾ rmw ⨾ ⦗S⦘ ≡ ⦗set_compl I⦘ ⨾ rfi ⨾ rmw ⨾ ⦗S⦘.
Proof using WF RCOH. 
  split.
  2: by arewrite (rfi ⊆ rf).
  rewrite rfi_union_rfe. rewrite !seq_union_l, !seq_union_r.
  unionL; [done|].
  rewrite (dom_rel_helper rfe_rmw_S).
  basic_solver.
Qed.

Lemma rt_rf_rmw_S' :
  (rf ⨾ rmw)＊ ⨾ ⦗S⦘ ⊆ (rfi ⨾  rmw)＊ ⨾ (⦗I⦘ ⨾ (rf ⨾ rmw)⁺)^? ⨾ ⦗S⦘.
Proof using WF RCOH.
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
Proof using WF TCOH RCOH IMMCON ICOH.
  rewrite rt_rf_rmw_S'.
  rewrite crE. rewrite !seq_union_l, !seq_union_r, !seq_id_l.
  unionL; [done|].
  rewrite !seqA.
  arewrite (⦗set_compl I⦘ ⨾ (rfi ⨾ rmw)＊ ⨾ ⦗I⦘ ⊆ ∅₂).
  2: basic_solver.
  arewrite (rfi ⊆ rf).
  intros x y HH. apply seq_eqv_l in HH. destruct HH as [AA HH].
  apply AA. eapply rfrmw_rt_I_in_I; eauto.
  eexists. apply HH.
Qed.

Lemma dom_rfe_rmw_ct_rfi_Acq_sb_S_in_I :
  dom_rel (rfe ⨾ rmw ⨾ (rfi ⨾ rmw)＊ ⨾ rfi ⨾ ⦗Acq⦘ ⨾ sb^? ⨾ ⦗S⦘) ⊆₁ I.
Proof using WF TCOH RCOH.
seq_rewrite rt_seq_swap.
rewrite !seqA.
arewrite (rmw ⨾ rfi ⨾ (rmw ⨾ rfi)＊ ⊆ (rmw ⨾ rfi)＊).
{ rewrite rtE. rewrite ct_begin at 2. 
  basic_solver 21. }
rewrite (dom_r (wf_rfeD WF)), !seqA.
rewrite (dom_r (wf_rfiD WF)).
arewrite (⦗R⦘ ⨾ (rmw ⨾ rfi ⨾ ⦗R⦘)＊ ⊆ (rmw ⨾ rfi)＊ ⨾ ⦗R⦘).
{ rewrite !rtE, <- !seqA, inclusion_ct_seq_eqv_r.
  basic_solver. }
arewrite (⦗S⦘ ⊆ ⦗S⦘ ⨾ ⦗W⦘).
{ forward (eapply reservedW); eauto.
  basic_solver. }
arewrite (⦗R⦘ ⨾ ⦗Acq⦘ ⨾ sb^? ⨾ ⦗S⦘ ⨾ ⦗W⦘ ⊆ ⦗R⦘ ⨾ ⦗Acq⦘ ⨾ sb ⨾ ⦗S⦘).
{ type_solver 21. }
generalize ((rcoh_dr_R_acq_I RCOH)).
basic_solver 21.
Qed.

(* Lemma exists_co_imm_helper w w' (D1 D2: actid -> Prop) *)
(*       (WNEXT: (⦗D1⦘ ⨾ co ⨾ ⦗D2⦘) w w'): *)
(*   exists w'', immediate (⦗D1⦘ ⨾ co ⨾ ⦗D2⦘) w w''. *)
(* Proof.  *)
(*  apply fsupp_imm_t in WNEXT. *)
(*  { apply ct_begin in WNEXT as (? & ? & _). eauto. } *)
(*  3: { generalize (co_trans WF). basic_solver 10. }  *)
(*  all: rewrite inclusion_seq_eqv_r, inclusion_seq_eqv_l. *)
(*  { apply TODO_mem_fair2. } *)
(*  by apply co_irr.  *)
(* Qed.  *)

Lemma co_next_to_imm_co_next w locw
      (LOC : loc w = Some locw)
      (WNEXT : exists wnext, (co ⨾ ⦗ S ⦘) w wnext)
      (FAIR: mem_fair G):
  exists wnext vnext,
    ⟪ NCOIMM   : immediate (co ⨾ ⦗ S ⦘) w wnext ⟫ /\
    ⟪ ISSNEXT : S wnext ⟫  /\
    ⟪ CONEXT  : co w wnext ⟫  /\
    ⟪ ENEXT   : E wnext ⟫  /\
    ⟪ WNEXT   : W wnext ⟫  /\
    ⟪ LOCNEXT : Loc_ locw wnext ⟫  /\
    ⟪ VNEXT   : val wnext = Some vnext ⟫ /\
    ⟪ NEQNEXT : wnext <> w ⟫.
Proof using WF TCOH RCOH.
  assert (exists wnext, immediate (co ⨾ ⦗ S ⦘) w wnext) as [wnext NIMMCO].
  {
    (* desc. apply seq_id_l, exists_co_imm_helper in WNEXT. desc. *)
    (* eexists. eapply immediate_more; [by symmetry; apply seq_id_l| eauto ]. *)
    desc. apply fsupp_imm_t in WNEXT.
    { apply ct_begin in WNEXT as (? & ? & _). eauto. }
    3: { generalize (co_trans WF). basic_solver 10. } 
    all: rewrite inclusion_seq_eqv_r. 
    { apply FAIR. }
    by apply co_irr. }
  clear WNEXT.
  assert (S wnext /\ co w wnext) as [ISSNEXT CONEXT].
  { destruct NIMMCO as [AA _]. by destruct_seq_r AA as BB. }
  assert (E wnext) as ENEXT.
  { eapply rcoh_S_in_E; eauto. }
  assert (W wnext) as WNEXT.
  { eapply reservedW; eauto. }
  assert (Loc_ locw wnext) as LOCNEXT.
  { apply (wf_col WF) in CONEXT. by rewrite <- CONEXT. }
  assert (exists vnext, val wnext = Some vnext) as [vnext VNEXT].
  { unfold Events.val, is_w in *. desf.
    all: eexists; eauto. }
  exists wnext, vnext. splits; eauto.
  intros H; subst. by apply (co_irr WF) in CONEXT.
Qed.

Lemma co_prev_to_imm_co_prev w locw
      (EW    : E w)
      (WW    : W w)
      (WNCOV : ~ covered T w)
      (LOC   : loc w = Some locw)
      (FAIR: mem_fair G):
  exists wprev vprev,
    ⟪ PCOIMM   : immediate (⦗ S ⦘ ⨾ co) wprev w ⟫ /\
    ⟪ ISSPREV : S wprev ⟫  /\
    ⟪ COPREV  : co wprev w ⟫  /\
    ⟪ EPREV   : E wprev ⟫  /\
    ⟪ WPREV   : W wprev ⟫  /\
    ⟪ LOCPREV : Loc_ locw wprev ⟫  /\
    ⟪ VPREV   : val wprev = Some vprev ⟫ /\
    ⟪ NEQPREV : wprev <> w ⟫.
Proof using WF TCOH RCOH IMMCON. 
  (* assert (tc_coherent G sc (etc_TC T)) as TCCOH by apply ETCCOH. *)
  assert (~ is_init w) as WNINIT.
  { intros HH. apply WNCOV. eapply init_covered; eauto. by split. }
  assert (exists wprev, immediate (⦗ S ⦘ ⨾ co) wprev w) as [wprev PIMMCO].
  { assert ((⦗ S ⦘ ⨾ co) (InitEvent locw) w) as WPREV.
    { assert (W (InitEvent locw)) as WI.
      { by apply init_w. }
      assert (E (InitEvent locw)) as EI.
      { apply wf_init; auto. by exists w; split. }
      assert (issued T (InitEvent locw)) as II.
      { eapply init_issued; vauto. } 
      assert (S (InitEvent locw)) as IS.
      { eapply rcoh_I_in_S; eauto. }
      assert (InitEvent locw <> w) as NEQ.
      { intros H; subst. desf. }
      assert (loc (InitEvent locw) = Some locw) as LI.
      { unfold Events.loc. by rewrite (wf_init_lab WF). }
      apply seq_eqv_l; split; auto.
      edestruct (wf_co_total WF).
      3: by apply NEQ.
      1,2: split; [split|]; auto.
      { by rewrite LOC. }
      { done. }
      exfalso. cdes IMMCON. eapply Cint.
      eexists; split.
      2: { apply r_step. by apply Execution_eco.co_in_eco; apply H. }
      apply sb_in_hb. apply init_ninit_sb; auto. }
    desc. apply fsupp_imm_t in WPREV.
    { apply ct_end in WPREV as (? & ? & ?). eauto. }
    3: { generalize (co_trans WF). basic_solver 10. } 
    all: rewrite inclusion_seq_eqv_l. 
    { apply FAIR. }
    by apply co_irr. }    
  assert (S wprev /\ co wprev w) as [ISSPREV COPREV].
  { destruct PIMMCO as [AA _]. by destruct_seq_l AA as BB. }
  assert (E wprev) as EPREV.
  { eapply rcoh_S_in_E; eauto. }
  assert (W wprev) as WPREV.
  { eapply reservedW; eauto. }
  assert (Loc_ locw wprev) as LOCPREV.
  { apply (wf_col WF) in COPREV. by rewrite COPREV. }
  assert (exists vprev, val wprev = Some vprev) as [vprev VPREV].
  { unfold Events.val, is_w in *. desf.
    all: eexists; eauto. }
  exists wprev, vprev. splits; eauto.
  intros H; subst. by apply (co_irr WF) in COPREV.
Qed.

Lemma dom_sb_S_rfrmwf w wn1 wn2
      (DD1 : dom_sb_S_rfrmw G T rfi (eq w) wn1)
      (DD2 : dom_sb_S_rfrmw G T rfi (eq w) wn2) :
  wn1 = wn2.
Proof using WF IMMCON.
  generalize wf_rfirmwsf, DD1, DD2. 
  unfold dom_sb_S_rfrmw.
  basic_solver 10.
Qed.
  
Lemma dom_sb_S_rfrmw_single w wn
      (DD : dom_sb_S_rfrmw G T rfi (eq w) wn) :
  dom_sb_S_rfrmw G T rfi (eq w) ≡₁ eq wn.
Proof using WF IMMCON.
  split.
  2: generalize DD; basic_solver.
  intros x HH. eapply dom_sb_S_rfrmwf; eauto.
Qed.

Lemma dom_sb_S_rfrmwE rrf P : dom_sb_S_rfrmw G T rrf P ⊆₁ E.
Proof using WF.
  unfold dom_sb_S_rfrmw. rewrite (wf_rmwE WF). basic_solver.
Qed.

Lemma dom_sb_S_rfrmw_in_W_ex rrf P : dom_sb_S_rfrmw G T rrf P ⊆₁ W_ex.
Proof using.
  unfold dom_sb_S_rfrmw. rewrite rmw_W_ex. basic_solver.
Qed.

Lemma dom_sb_S_rfrmwD rrf P : dom_sb_S_rfrmw G T rrf P ⊆₁ W.
Proof using WF.
  rewrite dom_sb_S_rfrmw_in_W_ex. by apply W_ex_in_W.
Qed.

Lemma codom_nS_imm_co_S_in_I :
  codom_rel (⦗set_compl S⦘ ⨾ immediate (co ⨾ ⦗S⦘)) ⊆₁ I \₁ W_ex.
Proof using WF RCOH IMMCON.
  cdes IMMCON.
  assert (sc_per_loc G) as SPL.
  { by apply coherence_sc_per_loc. }

  intros x [y HH].
  apply seq_eqv_l in HH. destruct HH as [AA HH].
  assert (S x /\ co y x) as [SX COYX].
  { generalize HH. clear. basic_solver. }
  destruct (classic (W_ex x)) as [WEX|NWEX].
  2: { split; auto. apply NNPP. intros II. apply NWEX. apply RCOH. by split. }
  exfalso.
  edestruct W_ex_in_codom_rfrmw as [z RFRMW]; eauto.
  assert (W x) as WX by (by apply W_ex_in_W).
  edestruct is_w_loc as [l XLOC].
  { apply WX. }
  assert (loc y = Some l) as YLOC.
  { rewrite <- XLOC. by apply (wf_col WF). }
  assert (co z x) as COZX.
  { apply rf_rmw_in_co; eauto. }
  assert (loc z = Some l) as ZLOC.
  { rewrite <- XLOC. by apply (wf_col WF). }
  
  assert (S z) as SZ.
  { apply dom_rf_rmw_S. exists x. apply seqA. basic_solver. }
  
  destruct (classic (z = y)) as [|NEQ]; subst.
  { by apply AA. }

  apply (dom_l (wf_coE WF)) in COZX. destruct_seq_l COZX as EZ.
  apply (dom_l (wf_coD WF)) in COZX. destruct_seq_l COZX as WZ.
  apply (dom_l (wf_coE WF)) in COYX. destruct_seq_l COYX as EY.
  apply (dom_l (wf_coD WF)) in COYX. destruct_seq_l COYX as WY.
  
  edestruct (wf_co_total WF) with (a:=z) (b:=y) as [COZY|COYZ]; eauto.
  1,2: by unfolder; splits; eauto.
  { eapply rf_rmw_in_coimm; eauto. }
  eapply HH with (c:=z).
  all: by apply seq_eqv_r; split.
Qed.

Section SingleDomSbSRfRmw.
Variables w wnext : actid.
Hypothesis WNEXT : dom_sb_S_rfrmw G T rfi (eq w) wnext.

Lemma dom_sb_S_rfrmw_single_props locw
      (WNISS : ~ issued T w)
      (WNCOV : ~ covered T w)
      (WLOC : loc w = Some locw) :
  ⟪ SBWWNEXT : sb w wnext ⟫ /\
  ⟪ EWNEXT : E wnext ⟫ /\
  ⟪ WWNEXT : W wnext ⟫ /\
  ⟪ WNEXTCOV : ~ covered T wnext ⟫ /\
  ⟪ RFIRMWNEXT : (rfi ⨾ rmw) w wnext ⟫ /\
  ⟪ RFRMWNEXT : (rf ⨾ rmw) w wnext ⟫ /\
  ⟪ COWWNEXT : co w wnext ⟫ /\
  ⟪ NSWNEXT : ~ reserved T wnext ⟫ /\
  ⟪ NIWNEXT : ~ issued T wnext ⟫ /\
  ⟪ WNEXTINIT : ~ is_init wnext ⟫ /\
  ⟪ WNEXTLOC : loc wnext = Some locw ⟫ /\
  ⟪ WNEXTTID : tid wnext = tid w ⟫.
Proof using WNEXT WF TCOH RCOH IMMCON ICOH. 
  assert (sc_per_loc G) as SPL. 
  { apply coherence_sc_per_loc. apply IMMCON. }
  (* assert (tc_coherent G sc (etc_TC T)) as TCCOH by apply ETCCOH. *)
  assert (sb w wnext) as SBWWNEXT.
  { destruct WNEXT as [_ AA].
    clear -AA WF.
    generalize (@sb_trans G), (@rfi_in_sb G), (rmw_in_sb WF), AA.
    basic_solver. }
  assert (W wnext) as WWNEXT.
  { eapply dom_sb_S_rfrmwD; eauto. }
  assert (E wnext) as EWNEXT.
  { eapply dom_sb_S_rfrmwE; eauto. }
  assert (~ covered T wnext) as WNEXTCOV.
  { intros HH. apply WNCOV. eapply dom_sb_covered; eauto.
    basic_solver 10. }
  assert ((rfi ⨾ rmw) w wnext) as RFIRMWNEXT.
  { destruct WNEXT as [_ [y AA]]. destruct_seq_l AA as BB; subst.
    generalize AA. clear. basic_solver. }
  assert ((rf ⨾ rmw) w wnext) as RFRMWNEXT.
  { generalize RFIRMWNEXT. unfold Execution.rfi. clear. basic_solver. }
  assert (co w wnext) as COWWNEXT.
  { apply rf_rmw_in_co; auto. }
  assert (~ reserved T wnext) as NSWNEXT.
  { intros HH. apply WNISS.
    eapply dom_rf_rmw_S_in_I; eauto.
    exists wnext. apply seqA. apply seq_eqv_r. split; auto. }
  assert (~ issued T wnext) as NIWNEXT.
  { intros HH. apply NSWNEXT. eapply rcoh_I_in_S; eauto. }
  assert (~ is_init wnext) as WNEXTINIT.
  { intros HH. apply WNEXTCOV. eapply init_covered; eauto. by split. }

  assert (loc wnext = Some locw) as WNEXTLOC.
  { rewrite <- WLOC. symmetry. by apply (wf_col WF). }
  
  assert (E w) as EW.
  { apply (dom_l (wf_rfrmwE WF)) in RFRMWNEXT.
    destruct_seq_l RFRMWNEXT as AA; auto. }
  assert (WNEXTTID : tid wnext = tid w).
  { symmetry. eapply ninit_sb_same_tid. apply seq_eqv_l. split; eauto.
    intros HH. apply WNCOV. eapply init_covered; eauto. split; auto. }

  splits; auto.
Qed.
  
End SingleDomSbSRfRmw.

End ExtTraversalProperties.
