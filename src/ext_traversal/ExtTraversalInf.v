Require Import Classical Peano_dec Setoid PeanoNat.
From hahn Require Import Hahn.

From imm Require Import Events.
From imm Require Import Execution.
From imm Require Import Execution_eco.
From imm Require Import imm_s_hb.
From imm Require Import imm_s.
From imm Require Import imm_bob imm_s_ppo.
From imm Require Import CombRelations.
From imm Require Import AuxDef.
From imm Require Import AuxRel2.
From imm Require Import TraversalConfig.
From imm Require Import imm_s_rfppo.
From imm Require Import Traversal. 
From imm Require Import FairExecution.

Set Implicit Arguments.

(* TODO: merge with imm.Traversal *)

Section Traversal.
  Variable G : execution.
  Hypothesis WF : Wf G.
  Variable sc : relation actid.
  Hypothesis IMMCON : imm_consistent G sc.

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


Lemma exists_trav_step_write T (TCCOH : tc_coherent G sc T)
      w (NEXT : next G (covered T) w) (Ww: W w):
  exists T', trav_step G sc T T'.
Proof. 
  destruct (classic (issued T w)).
  { exists (mkTC (covered T ∪₁ (eq w)) (issued T)).
    destruct T as [C I]; simpls.
    exists w; left; unnw; splits; simpls.
    { apply NEXT. }
    unfold coverable. split; [by apply NEXT|].
    left; unnw; basic_solver. }
  exists (mkTC (covered T) (issued T ∪₁ (eq w))).
  destruct T as [C I]; simpl in *.
  exists w; right; unnw; splits; simpls; try basic_solver.
  eapply issuable_next_w; eauto. by unfolder.
Qed.

Lemma exists_trav_step_coverable T (TCCOH : tc_coherent G sc T)
      e (NEXT : next G (covered T) e) (COV: coverable G sc T e):
  exists T', trav_step G sc T T'.
Proof.
    exists (mkTC (covered T ∪₁ (eq e)) (issued T)).
    exists e; left; splits; simpls; auto.
    apply NEXT.
Qed.

(* TODO: move upper *)
Hypothesis IMM_FAIR: fsupp (ar G sc)⁺.

(* TODO: move to IMM.FairExecution *)
Lemma fsupp_rf:
  fsupp rf.
Proof using WF.
  apply functional_inv_fsupp. by inversion WF.
  (* Qed.  *)
Admitted.

(* TODO: move to IMM.FairExecution *)
(* TODO: fix imports *)
Require Import FinExecutionExt.
Require Import CertGraphInit.
Import ListNotations.

(* TODO: move to IMM*)
Lemma is_f_loc (e : actid) (Fe: is_f lab e):
  loc e = None.
Proof.
  unfold Events.loc. destruct e; type_solver.
Qed. 


Lemma fsupp_sb_loc:
  fsupp (sb ∩ same_loc).
Proof using WF.
  rewrite <- seq_id_l.
  rewrite set_full_split with (S := is_init), id_union, seq_union_l.
  apply fsupp_union.
  2: { eapply fsupp_mori; [| by apply fsupp_sb; eauto].
       red. basic_solver. }
  
  red. ins.
  remember (loc y) as ly. destruct ly. 
  { exists [InitEvent l].
    intros x REL%seq_eqv_l. desc. destruct x; [| done].
    simpl. left. f_equal. apply proj2 in REL0.
    red in REL0.
    unfold Events.loc in REL0 at 1. rewrite wf_init_lab in REL0; auto.
    congruence. }
  exists []. red. intros x REL%seq_eqv_l. desc.
  apply proj2 in REL0. red in REL0.
  destruct x; [| done]. 
  unfold Events.loc in REL0 at 1. rewrite wf_init_lab in REL0; auto.
  congruence.
Qed.
  
  
Lemma fsupp_rf_ppo_loc: fsupp (rf ⨾ ppo ∩ same_loc).
Proof using WF. 
  apply fsupp_seq; [by apply fsupp_rf| ]. 
  rewrite ppo_in_sb; auto. by apply fsupp_sb_loc. 
Qed.

(* TODO: move to IMM *)
Lemma rf_sbl_w_in_co:
  rf ⨾ sb ∩ same_loc ⨾ ⦗W⦘ ⊆ co.
Proof using WF IMMCON.
  red. intros w1 w2 [w' [RF HH]]. apply seq_eqv_r in HH as [[SB LOC] W2].
  forward eapply is_w_loc as [l Ll]; eauto.
  red in LOC. pose proof (wf_rfl WF _ _ RF) as Ll'. red in Ll'.
  eapply same_relation_exp in RF.
  2: { rewrite wf_rfE, wf_rfD; auto. }
  apply wf_sbE in SB. 
  
  forward eapply (@wf_co_total _ WF (Some l)) with (a := w1) (b := w2). 
  1, 2: unfolder in *; desc; splits; congruence.
  { intros <-. cdes IMMCON. red in Cint. destruct (Cint w').
    exists w1. split.
    - apply sb_in_hb. generalize SB. basic_solver.
    - right. apply rf_in_eco. generalize RF. basic_solver. }
  ins. des; auto.
  cdes IMMCON. red in Cint. destruct (Cint w').
  exists w2. split.
  { apply sb_in_hb. generalize SB. basic_solver. }
  right. red. left. right. eexists. splits; eauto.
  generalize RF. basic_solver.
(* Qed.  *)
Admitted. 

Lemma fsupp_rf_ppo_loc_ct (FAIR: mem_fair G):
  fsupp (rf ⨾ ppo ∩ same_loc)⁺.
Proof using WF IMMCON.
  eapply fsupp_mori with (x := co^* ⨾ rf ⨾ ppo ∩ same_loc).
  2: { apply fsupp_seq; [| by apply fsupp_rf_ppo_loc].
       apply fsupp_ct_rt. rewrite ct_of_trans; [| by apply WF].
       apply FAIR. }
  red.
  rewrite ctEE. apply inclusion_bunion_l. intros i _. induction i.
  { simpl. apply seq_mori; basic_solver. }
  rewrite pow_S_end. rewrite IHi.
  arewrite (rf ≡ ⦗W⦘ ⨾ rf) at 2.
  { rewrite wf_rfD; basic_solver. }
  hahn_frame.
  etransitivity; [| apply inclusion_t_rt]. rewrite ct_end. hahn_frame_l.
  rewrite ppo_in_sb; auto. apply rf_sbl_w_in_co; auto. 
Qed.
  

Lemma wf_ar_rf_ppo_loc_ct_inf
      (WFSC: wf_sc G sc) (COM: complete G) (FAIR: mem_fair G):
  well_founded (ar G sc ∪ rf ;; ppo ∩ same_loc)⁺.
Proof using WF IMMCON IMM_FAIR. 
  apply fsupp_well_founded.
  3: by apply transitive_ct.
  2: by apply ar_rf_ppo_loc_acyclic.

  rewrite ct_unionE. apply fsupp_union.
  { by apply fsupp_rf_ppo_loc_ct. }
  apply fsupp_seq.
  { apply fsupp_ct_rt, fsupp_rf_ppo_loc_ct; auto. }  

  eapply fsupp_mori; [| by apply IMM_FAIR].
  red. rewrite rtE, seq_union_r, seq_id_r.
  rewrite ar_rf_ppo_loc_ct_in_ar_ct; auto.
  etransitivity.
  2: { rewrite <- ct_of_ct. reflexivity. }
  apply clos_trans_mori. basic_solver. 
Qed.


Lemma WMIN T (TCCOH : tc_coherent G sc T)
      (WFSC: wf_sc G sc) (COM: complete G) (FAIR: mem_fair G):
  (exists w : actid, is_w lab w /\ ~ issued T w /\ E w) ->
  exists w : actid,
    is_w lab w /\
    ~ issued T w /\
    dom_cond (⦗W⦘ ⨾ (ar G sc ∪ rf ⨾ ppo ∩ same_loc)⁺) (issued T) w /\ E w.
Proof using WF IMM_FAIR IMMCON. 
  intros P; desf.
  induction w using (well_founded_ind (wf_ar_rf_ppo_loc_ct_inf WFSC COM FAIR)).
  destruct (classic (dom_cond (⦗W⦘ ⨾ (ar G sc ∪ rf ⨾ ppo ∩ same_loc)⁺) (issued T) w)); eauto.
  unfolder in H0. unfold dom_rel in H0.
  apply not_all_ex_not in H0; desf.
  apply not_all_ex_not in H0; desf.
  eapply H; eauto. 
  cdes IMMCON.
  apply wf_ar_rf_ppo_loc_ctE in n3; auto. by destruct_seq_l n3 as AA.
Qed.
  
Lemma FMIN T (TCCOH : tc_coherent G sc T)
      (WFSC: wf_sc G sc)
      (COM: complete G)
      (FAIR: mem_fair G)
  :
  (exists f, (F∩₁Sc) f  /\ ~ covered T f /\ E f) ->
  exists f, (F∩₁Sc) f /\ ~ covered T f /\
       doma (⦗F∩₁Sc⦘ ⨾ (ar G sc ∪ rf ⨾ ppo ∩ same_loc)⁺ ⨾ ⦗eq f⦘) (covered T) /\
       E f.
Proof using WF IMM_FAIR IMMCON. 
  intros P; desf.
  induction f using (well_founded_ind (wf_ar_rf_ppo_loc_ct_inf WFSC COM FAIR)).
  destruct (classic (doma (⦗F∩₁Sc⦘ ⨾ (ar G sc ∪ rf ⨾ ppo ∩ same_loc)⁺ ⨾ ⦗eq f⦘) (covered T)))
    as [H0 | H0]; eauto.
  rewrite seq_eqv_r, seq_eqv_l in H0.
  unfold doma in H0.
  apply not_all_ex_not in H0; desf.
  apply not_all_ex_not in H0; desf.
  apply imply_to_and in H0; desf.
  eapply H; eauto.
  cdes IMMCON.
  apply wf_ar_rf_ppo_loc_ctE in H2; auto. by destruct_seq_l H2 as AA. 
Qed.

Lemma RorF T (TCCOH : tc_coherent G sc T)
      (NWNEXT: forall e, next G (covered T) e -> ~ is_w lab e)
      (NCOV: forall e, next G (covered T) e -> ~ coverable G sc T e):
  forall n, next G (covered T) n -> R n \/ (F∩₁Sc) n.
Proof using IMMCON.
  intros; destruct (lab_rwf lab n); auto.
  desf.
  { by apply NWNEXT in H. }
  right. split; auto.
  destruct (classic (is_sc lab n)) as [|NEQ]; [done|exfalso].
  set (NN := H).
  apply NCOV in NN.
  unfold coverable in NN.
  apply not_and_or in NN; desf; apply NN.
  { apply H. }
  right; split; auto.
  cdes IMMCON.
  unfold dom_cond. rewrite (wf_scD Wf_sc).
  type_solver.
Qed.
  

Lemma WIS T (TCCOH : tc_coherent G sc T)
      (COM: complete G):
  forall r, R r -> next G (covered T) r ->
       ~ coverable G sc T r ->
       exists w, W w /\ rf w r /\ ~ issued T w.
Proof using WF.
  intros r RR RNEXT NCOV.
  unfold coverable in NCOV.
  apply not_and_or in NCOV; desf.
  { exfalso; apply NCOV. apply RNEXT. }
  apply not_or_and in NCOV; desf.
  apply not_or_and in NCOV; desf.
  apply not_and_or in NCOV1; desf.
  assert (exists w, rf w r) as [w RF].
  { edestruct COM; esplit; eauto; auto. by apply RNEXT. }
  exists w; splits; auto.
  { apply (wf_rfD WF) in RF.
    apply seq_eqv_l in RF; desf. }
  intros II. apply NCOV1.
  intros x [y H]. apply seq_eqv_r in H; desf.
  assert (w = x); [|by subst].
  eapply (wf_rff WF); eauto.
Qed.

Lemma exists_trav_step_read T (TCCOH : tc_coherent G sc T)
      (COM: complete G) (WFSC: wf_sc G sc) (FAIR: mem_fair G)
      e (RNEXT: next G (covered T) e) (RNEXT0: is_r lab e)
      (NCOV: forall e, next G (covered T) e -> ~ coverable G sc T e)
      (NWNEXT: forall e, next G (covered T) e -> ~ is_w lab e):
  exists T': trav_config, trav_step G sc T T'.
Proof using WF IMM_FAIR IMMCON. 
  assert (exists w', W w' /\ ~ issued T w' /\ E w') as XW.
  { destruct (WIS TCCOH COM RNEXT0 RNEXT) as [w'].
    { eapply NCOV; eauto. }
    exists w'; splits; desf.
    apply wf_rfE in H0; auto.
    apply seq_eqv_l in H0; desf. }
  assert (WMIN := WMIN TCCOH WFSC COM FAIR XW).
  clear XW.
  desf.
  assert (~ covered T w) as WNCOV.
  { intro H. apply WMIN0.
      by apply (w_covered_issued TCCOH); split. }
  destruct (exists_next G (covered T) w WMIN2 WNCOV) as [n NSB]; desf.
  destruct NSB as [HSB|HSB]; desf.
  { exfalso; eapply NWNEXT; eauto. }
  exists (mkTC (covered T) (issued T ∪₁ (eq w))).
  exists w; right; unnw; splits; simpls.
  
  set (nRorF := RorF TCCOH NWNEXT NCOV).
  specialize (nRorF n NSB0).
  split; [split; [split|]|]; auto.
  intros x [y H]; desc; subst.
  apply seq_eqv_r in H. desc; subst.
  apply NNPP; intro COVX.
  
  assert (sb x y) as SBXY.
  { by apply bob_in_sb, fwbob_in_bob. }
  assert (sb^? n x) as NX.
  { destruct (eq_dec_actid n x) as [EQNX|NEQNX]; [by left|right].
    edestruct (sb_semi_total_r ) as [LL|RR]; eauto.
    { intros H'. apply COVX.
      apply TCCOH; vauto.
      apply (@wf_sbE G) in SBXY.
      unfolder in SBXY; basic_solver. }
    exfalso; apply COVX.
    eapply NSB0; basic_solver 12. }
  
  assert (fwbob⁺ n y) as BOB.
  { destruct NX as [NX|NX]; subst; [by apply t_step|].
    apply sb_fwbob_in_fwbob.
    eexists; eauto. }
  clear x H COVX NX SBXY.
  desf.
  { assert (NY := NSB0).
    apply NCOV in NSB0.
    unfold coverable in NSB0.
    apply not_and_or in NSB0; desf.
    { exfalso; apply NSB0. apply NY. }
    apply not_or_and in NSB0; desf.
    apply not_or_and in NSB0; desf.
    apply NSB2; unnw; split; auto.
    clear NSB0 NSB1 NSB2.
    red. intros x' [y' H'].
    apply seq_eqv_r in H'; desf.
    apply rfi_union_rfe in H'; destruct H' as [RFI|RFE].
    { destruct RFI as [RF SBXY].
      apply (w_covered_issued TCCOH); split.
      2: by eapply NY; eexists; apply seq_eqv_r; eauto.
      apply (wf_rfD WF) in RF.
      apply seq_eqv_l in RF; desf. }
    eapply WMIN1.
    eexists. apply seq_eqv_r. split; eauto.
    apply seq_eqv_l; split.
    { apply wf_rfeD in RFE; auto;
        apply seq_eqv_l in RFE; desf. }
    eapply ct_ct. exists y'.
    split.
    { apply t_step. left. by apply rfe_in_ar. }
    hahn_rewrite fwbob_in_bob in BOB.
    hahn_rewrite bob_in_ar in BOB.
    eapply clos_trans_mori.
    2: by apply BOB.
    basic_solver. }
  assert (exists f, (F∩₁Sc) f /\ ~ covered T f /\ E f) as FF.
  { exists n; splits; auto; apply NSB0. }
  specialize (FMIN TCCOH WFSC COM FAIR FF) as FMIN; clear FF; desf.


  destruct (exists_next G (covered T) f FMIN2 FMIN0) as [m MSB]; desf.
  destruct MSB as [MSB|MSB].
  { desf.
    specialize (NCOV f MSB0).
    apply NCOV. split.
    { apply MSB0. }
    right; split; auto.
    { type_solver. }
    intros x [z X]. apply seq_eqv_r in X; desf.
    eapply FMIN1.
    apply seq_eqv_l; split.
    { cdes IMMCON. apply (wf_scD Wf_sc) in X. apply seq_eqv_l in X; desf. }
    apply seq_eqv_r; split; auto.
    apply t_step. red. left. by apply sc_in_ar. }
  assert (R m) as RM.
  { specialize (RorF TCCOH NWNEXT NCOV MSB0) as RorF. 
    desf; auto.
    exfalso.
    destruct MSB0 as [MSB1 MSB2].
    apply MSB2.
    eapply FMIN1.
    hahn_rewrite seq_eqv_r.
    hahn_rewrite seq_eqv_l.
    splits; eauto. 
    apply t_step. left. apply bob_in_ar.
    apply sb_to_f_in_bob.
    apply seq_eqv_r. split; auto.
    mode_solver. }
  destruct (WIS TCCOH COM RM MSB0) as [w' [WW [WRF WI]]].
  { by apply NCOV. }
  apply WI.
  eapply WMIN1.
  eexists. apply seq_eqv_r. splits; eauto.
  hahn_rewrite seq_eqv_l; splits; auto.
  
  assert ((ar G sc)⁺ w' f) as wfWF'.
  { apply rfi_union_rfe in WRF; destruct WRF as [[RFI SB]|RFE].
    { assert (sb w' f) as SB'.
      { eapply sb_trans; eauto. }
      apply t_step.
      apply (bob_in_ar sc).
      apply sb_to_f_in_bob.
      apply seq_eqv_r. split; auto.
      mode_solver. }
    eapply t_trans; apply t_step.
    { apply rfe_in_ar; eauto. }
    apply bob_in_ar.
    apply sb_to_f_in_bob.
    apply seq_eqv_r. split; auto.
    mode_solver. }
  assert ((ar G sc ∪ rf ⨾ ppo ∩ same_loc)⁺ w' f) as wfWF.
  { eapply clos_trans_mori.
    2: by apply wfWF'.
    basic_solver. }
  eapply t_trans; [apply wfWF|].
  apply rt_ct; exists n.
  split.
  2: eapply clos_trans_mori; [|by apply BOB].
  2: rewrite fwbob_in_bob; rewrite bob_in_ar; basic_solver.
  destruct (classic (f = n)) as [|FNEQ]; subst.
  { apply rt_refl. }
  apply rt_step. left. apply sc_in_ar.
  cdes IMMCON.
  edestruct wf_sc_total as [J|J]; eauto.
  { split; [split|].
    2,3: by apply FMIN.
    apply (dom_r (wf_sbE G)) in MSB.
    apply seq_eqv_r in MSB. desf. }
  { split; [split|].
    2,3: by apply nRorF.
    apply (dom_l (wf_sbE G)) in HSB.
    apply seq_eqv_l in HSB. desf. }
  exfalso.
  apply NSB0.
  eapply FMIN1.
  apply seq_eqv_l; split; auto.
  apply seq_eqv_r; split; eauto.
  apply t_step. left. by apply sc_in_ar.
Qed.

Lemma FSC T (TCCOH : tc_coherent G sc T)
      (NWNEXT: forall e, next G (covered T) e -> ~ is_w lab e)
      (NRNEXT: forall e, next G (covered T) e -> ~ is_r lab e)
      (NCOV: forall e, next G (covered T) e -> ~ coverable G sc T e)
  :
    forall e, next G (covered T) e -> (F ∩₁ Sc) e.
Proof using WF IMMCON. 
  intros e H.
  specialize (NWNEXT e H); specialize (NCOV e H);
    specialize (NRNEXT e H).
  destruct (lab_rwf lab e) as [ | [| FF]]; vauto; split; auto.
  destruct (classic (Sc e)) as [SC|NSC]; auto.
  exfalso. apply NCOV; split.
  { apply H. }
  right; split; auto.
  unfold dom_cond. red.
  ins. destruct H0 as [y H0].
  apply seq_eqv_r in H0; desf.
  eapply wf_scD in H0.
  2: by apply IMMCON.
  apply seq_eqv_l in H0. destruct H0 as [_ H0].
  apply seq_eqv_r in H0.
  mode_solver.
Qed.

Lemma trav_step_contra T (TCCOH : tc_coherent G sc T)
      (WFSC: wf_sc G sc) (COM: complete G) (FAIR: mem_fair G)
      (NWNEXT: forall e, next G (covered T) e -> ~ is_w lab e)
      (NRNEXT: forall e, next G (covered T) e -> ~ is_r lab e)
      (NCOV: forall e, next G (covered T) e -> ~ coverable G sc T e)
      (FSC : forall e, next G (covered T) e -> (F ∩₁ Sc) e)
      (XF : exists f', (F ∩₁ Sc) f' /\ ~ covered T f' /\ E f')
  :
    False.
Proof using WF IMM_FAIR IMMCON. 
  destruct (FMIN TCCOH WFSC COM FAIR XF) as [esc X]; desf.
  destruct (exists_next G (covered T) esc X2 X0); desf.
  destruct H; desf.
  { eapply NCOV; eauto.
    split; [apply H0|].
    right; split; [by apply X|].
    intros x [y H]. eapply X1.
    apply seq_eqv_r in H; desf.
    apply seq_eqv_l; split.
    { eapply wf_scD in H.
      2: by apply IMMCON.
      apply seq_eqv_l in H; desf. }
    apply seq_eqv_r; split; auto.
    apply t_step. left. by apply sc_in_ar. }
  specialize (FSC _ H0).
  apply (NCOV _ H0). destruct TCCOH; desf. apply CC.
  rewrite seq_eqv_r, seq_eqv_l in X1.
  eapply X1.
  splits; eauto.
  apply t_step. left. apply bob_in_ar.
  apply sb_to_f_in_bob.
  apply seq_eqv_r. split; auto.
  mode_solver.
Qed. 


Lemma exists_trav_step T (TCCOH : tc_coherent G sc T) (FAIR: mem_fair G)
      e (N_FIN : next G (covered T) e):
    exists T', trav_step G sc T T'.
Proof using WF IMMCON IMM_FAIR.
  assert (wf_sc G sc) as WFSC by apply IMMCON.
  assert (complete G) as COM by apply IMMCON.
  
  destruct (forall_not_or_exists (next G (covered T)) W) as [WNEXT|NWNEXT].
  { desc. eapply exists_trav_step_write; eauto. }

  destruct (forall_not_or_exists (next G (covered T)) (coverable G sc T)) 
    as [COV|NCOV].
  { desc. eapply exists_trav_step_coverable; eauto. }
  
  destruct (forall_not_or_exists (next G (covered T)) R) as [RNEXT|NRNEXT].
  { desf. eapply exists_trav_step_read; eauto. }

  pose proof (FSC TCCOH NWNEXT NRNEXT NCOV) as FSC.     
  edestruct trav_step_contra; eauto.
  exists e; splits; try by apply N_FIN. by apply FSC.
Qed.

End Traversal.
