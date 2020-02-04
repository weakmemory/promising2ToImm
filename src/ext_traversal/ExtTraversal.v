Require Import Setoid.
From hahn Require Import Hahn.
From imm Require Import AuxDef Events Execution Execution_eco
     imm_bob imm_s_ppo imm_s imm_s_hb CombRelations.
Require Import TraversalConfig Traversal.
Require Import AuxRel AuxRel2.
Require Export ExtTravRelations.
Require Import TraversalProperties.
Require Import ImmProperties.
Require Import ExtTraversalConfig.

Set Implicit Arguments.

Section ExtTraversalConfig.
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
Notation "'rppo'" := G.(rppo).
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

(******************************************************************************)
(** **   *)
(******************************************************************************)

Definition ext_itrav_step (e : actid) T T' :=
  (⟪ COVER :
       ⟪ NCOV : ~ ecovered T e ⟫ /\
       ⟪ COVEQ: ecovered T' ≡₁ ecovered T ∪₁ eq e ⟫ /\
       ⟪ ISSEQ: eissued  T' ≡₁ eissued  T ⟫ /\
       ⟪ RESEQ: reserved T' ≡₁ reserved T ⟫
   ⟫ \/
   ⟪ ISSUE :
       ⟪ NISS : ~ eissued T e ⟫ /\
       ⟪ RES  : W_ex e -> reserved T e ⟫ /\
       ⟪ COVEQ: ecovered T' ≡₁ ecovered T ⟫ /\
       ⟪ ISSEQ: eissued  T' ≡₁ eissued  T ∪₁ eq e ⟫ /\
       ⟪ RESEQ: reserved T' ≡₁
                reserved T ∪₁ eq e ∪₁
                dom_sb_S_rfrmw G T rfi (eq e) ⟫
   ⟫ \/
   ⟪ RESERVE :
       ⟪ NISS : ~ reserved T e ⟫ /\
       ⟪ COVEQ: ecovered T' ≡₁ ecovered T ⟫ /\
       ⟪ ISSEQ: eissued  T' ≡₁ eissued  T ⟫ /\
       ⟪ RESEQ: reserved T' ≡₁ reserved T ∪₁ eq e ⟫
  ⟫) /\
  ⟪ ETCCOH' : etc_coherent G sc T' ⟫.

Definition ext_trav_step T T' := exists e, ext_itrav_step e T T'.

Lemma exists_next_to_reserve w T
      (NRES : ~ reserved T w) :
  exists w',
    ⟪ SBB : (⦗W_ex \₁ reserved T⦘ ⨾ sb)^? w' w ⟫ /\
    ⟪ NB  : ~ codom_rel (⦗W_ex \₁ reserved T⦘ ⨾ sb) w' ⟫.
Proof using.
  generalize dependent w.
  set (Q w := ~ reserved T w ->
              exists w',
                ⟪ SBB : (⦗W_ex \₁ reserved T⦘ ⨾ sb)^? w' w ⟫ /\
                ⟪ NB  : ~ codom_rel (⦗W_ex \₁ reserved T⦘ ⨾ sb) w' ⟫).
  apply (@well_founded_ind _ sb (wf_sb G) Q).
  intros x IND; subst Q; simpls.
  intros NRESX.
  destruct (classic (exists w', (⦗W_ex \₁ reserved T⦘ ⨾ sb) w' x)) as [[w' HH]|NEX].
  2: { exists x. splits.
       { by left. }
       apply NEX. }
  apply seq_eqv_l in HH. destruct HH as [WW SB].
  set (BB := SB).
  apply IND in BB.
  2: by apply WW.
  desf. eexists. splits; [|by eauto].
  right. apply seq_eqv_l.
  destruct SBB as [|AA]; desf.
  apply seq_eqv_l in AA. desf.
  split; auto.
  eapply sb_trans; eauto.
Qed.

Section Props.
  
Variable T : ext_trav_config.
Hypothesis ETCCOH : etc_coherent G sc T.

Lemma dom_r_sb_new_reserved e r :
  dom_rel (r ⨾ sb ⨾ ⦗reserved T ∪₁ eq e ∪₁
           dom_rel (sb ⨾ ⦗reserved T⦘) ∩₁ codom_rel (⦗eq e⦘ ⨾ rfi ⨾ rmw)⦘) ≡₁
  dom_rel (r ⨾ sb ⨾ ⦗reserved T ∪₁ eq e⦘).
Proof using ETCCOH.
  split; [|basic_solver 20].
  rewrite id_union. rewrite !seq_union_r, dom_union.
  unionL; [done|].
  arewrite (dom_rel (sb ⨾ ⦗reserved T⦘) ∩₁ codom_rel (⦗eq e⦘ ⨾ rfi ⨾ rmw) ⊆₁
            dom_rel (sb ⨾ ⦗reserved T⦘)) by basic_solver. 
  generalize (@sb_trans G).
  basic_solver 10.
Qed.

Lemma dom_r_rppo_new_reserved e r :
  dom_rel (r ⨾ rppo ⨾ ⦗reserved T ∪₁ eq e ∪₁
           dom_rel (sb ⨾ ⦗reserved T⦘) ∩₁ codom_rel (⦗eq e⦘ ⨾ rfi ⨾ rmw)⦘) ≡₁
  dom_rel (r ⨾ rppo ⨾ ⦗reserved T ∪₁ eq e⦘).
Proof using WF ETCCOH.
  split; [|basic_solver 20].
  rewrite id_union. rewrite !seq_union_r, dom_union.
  unionL; [done|].
  arewrite (dom_rel (sb ⨾ ⦗reserved T⦘) ∩₁ codom_rel (⦗eq e⦘ ⨾ rfi ⨾ rmw) ⊆₁
            dom_rel (sb ⨾ ⦗reserved T⦘)) by basic_solver. 
  arewrite (reserved T ⊆₁ W ∩₁ reserved T) at 1.
  { generalize (reservedW WF ETCCOH). basic_solver. }
  generalize WF.(rppo_sb_in_rppo).
  basic_solver 20.
Qed.

Lemma dom_sb_new_reserved e :
  dom_rel (sb ⨾ ⦗reserved T ∪₁ eq e ∪₁
           dom_rel (sb ⨾ ⦗reserved T⦘) ∩₁ codom_rel (⦗eq e⦘ ⨾ rfi ⨾ rmw)⦘) ≡₁
  dom_rel (sb ⨾ ⦗reserved T ∪₁ eq e⦘).
Proof using WF ETCCOH.
  assert (sb ≡ ⦗ fun _ => True ⦘ ⨾ sb) as AA by basic_solver.
  rewrite AA at 1 3.
  rewrite !seqA. by apply dom_r_sb_new_reserved.
Qed.

Lemma dom_rfe_rppo_S_in_I :
  dom_rel (rfe ⨾ rppo ⨾ ⦗reserved T⦘) ⊆₁ eissued T.
Proof using WF ETCCOH.
  rewrite <- etc_rppo_S; eauto.
  rewrite <- inclusion_id_rt. rewrite seq_id_l.
  basic_solver 10.
Qed.

(* TODO: move to ImmProperties.v *)
Lemma codom_rfi_rfe_empty : codom_rel rfi ∩₁ codom_rel rfe ⊆₁ ∅.
Proof using WF.
  unfold Execution.rfi, Execution.rfe.
  unfolder. ins. desf. 
  assert (x0 = x1); subst; eauto.
  eapply WF.(wf_rff); eauto.
Qed.

Lemma trav_step_to_ext_trav_step TC' (TS : trav_step G sc (etc_TC T) TC') :
  exists T', ext_trav_step T T'.
Proof using WF IMMCON ETCCOH.
  unionL.
  assert (tc_coherent G sc (etc_TC T)) as TCCOH.
  { apply ETCCOH. }
  assert (tc_coherent G sc TC') as TCCOH'.
  { eapply trav_step_coherence; eauto. }

  red in TS. desf. cdes TS.
  desf.
  { exists (mkETC (mkTC (ecovered T ∪₁ eq e) (eissued T)) (reserved T)).
    eexists e.
    red. splits.
    { left. splits; auto. }
    constructor; unfold eissued, ecovered; simpls.
    all: try by apply ETCCOH.
    (* TODO: generalize to a lemma *)
    eapply trav_step_coherence.
    2: by apply ETCCOH. 
    eapply trav_step_more_Proper.
    3: by eexists; eauto.
    { apply same_tc_Reflexive. }
    { red. simpls. split; by symmetry. }
    unionR left. apply ETCCOH. }

  assert (E e) as EE.
  { eapply itrav_stepE with (T:= etc_TC T); eauto. }
  assert (eq e ⊆₁ E) as EQEE.
  { basic_solver. }
  assert (W e) as WE by apply ISS.

  assert (eq e ⊆₁ issuable G sc (etc_TC T)) as EQEISS by basic_solver.
  assert (dom_rel (⦗F ∩₁ Acq/Rel⦘ ⨾ sb ⨾ ⦗eq e⦘) ⊆₁ covered (etc_TC T)) as COVSBE.
  { rewrite EQEISS. arewrite (⦗F ∩₁ Acq/Rel⦘ ⨾ sb ⊆ fwbob).
    unfold issuable. basic_solver 10. }
  assert (dom_rel ((detour ∪ rfe) ⨾ (rmw ⨾ rfi)＊ ⨾ ⦗R ∩₁ Acq⦘ ⨾ sb ⨾ ⦗eq e⦘) ⊆₁ issued (etc_TC T)) as ISSSBE.
  { rewrite EQEISS. by apply dom_detour_rmwrfi_rfe_acq_sb_issuable. }
  assert (dom_rel (⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗eq e⦘) ⊆₁ issued (etc_TC T)) as WEXACQE.
  { rewrite EQEISS. by apply dom_wex_sb_issuable. }

  assert (dom_rel ((detour ∪ rfe) ⨾ (data ∪ rfi ∪ rmw)＊ ⨾ rppo ⨾ ⦗eq e⦘) ⊆₁
                  issued (etc_TC T)) as RPPOSBE.
  { rewrite EQEISS. 
    sin_rewrite WF.(detour_rfe_data_rfi_rmw_rppo_in_detour_rfe_ppo).
    rewrite !seqA. by apply dom_detour_rfe_ppo_issuable. }

  destruct
  (classic (exists w',
               (dom_rel (sb ⨾ ⦗eq e⦘) ∩₁
                codom_rel (⦗eissued T⦘ ⨾ rf ⨾ ⦗R_ex⦘ ⨾ rmw) \₁ reserved T) w'))
    as [[w' WWB]|NWHH].
  { edestruct wf_impl_min_elt
              with (B := dom_rel (sb ⨾ ⦗eq e⦘) ∩₁
                         codom_rel (⦗eissued T⦘ ⨾ rf ⨾ ⦗R_ex⦘ ⨾ rmw) \₁ reserved T)
                   (r := ⦗W_ex⦘ ⨾ sb) as [w [[[WHH WAA] NRES] MIN]].
    { arewrite (⦗W_ex⦘ ⨾ sb ⊆ sb).
      apply wf_sb. }
    { intros [AA BB]. eapply AA; eauto. }

    assert (W_ex w) as WEXW.
    { generalize WAA.  unfold Execution.W_ex. basic_solver. }
    assert (E w) as EW by (by apply WF.(W_ex_in_E)).
    assert (eq w ⊆₁ E) as EQWE.
    { basic_solver. }
    assert (eq w ⊆₁ dom_rel (⦗W_ex⦘ ⨾ sb ⨾ ⦗eq e⦘)) as EQWSB.
    { generalize WHH. basic_solver 10. } 
    assert (rmw ⨾ ⦗eq w⦘ ⊆ rppo ⨾ ⦗eq w⦘) as RPPO_RMW_W.
    { destruct WAA as [y AA]. destruct_seq_l AA as BB.
      destruct AA as [z [_ AA]]. destruct_seq_l AA as DD.
      intros v u HH. destruct_seq_r HH as CC; subst.
      assert (v = z); subst.
      { eapply WF.(wf_rmw_invf); eauto. }
      apply seq_eqv_r. split; auto.
      apply R_ex_sb_W_in_rppo.
      apply seq_eqv_lr. splits; auto.
      { apply rmw_in_sb; auto. }
        by apply WF.(W_ex_in_W). }
    assert (rppo ⨾ ⦗W_ex⦘ ⨾ sb ⨾ ⦗eq e⦘ ⊆ rppo ⨾ ⦗eq e⦘) as RPPO_WEX_SB.
    { arewrite (⦗eq e⦘ ⊆ ⦗W⦘ ⨾ ⦗eq e⦘) at 1.
      { generalize WE. basic_solver. }
      arewrite_id ⦗W_ex⦘. rewrite seq_id_l.
        by sin_rewrite WF.(rppo_sb_in_rppo). }

    exists (mkETC (mkTC (ecovered T) (eissued T))
                  (reserved T ∪₁ eq w)).
    exists w.
    constructor; unfold eissued, ecovered; simpls.
    { do 2 right. splits; eauto. }
    unnw. constructor; unfold eissued, ecovered; simpls.
    { by unionL; [by apply ETCCOH|]. }
    { unionR left. apply ETCCOH. }
    { rewrite set_minus_union_l.
      unionL; [by apply ETCCOH|].
      basic_solver. }
    4: { unionR left.
         unfold dom_sb_S_rfrmw. simpls.
         rewrite id_union, !seq_union_r, dom_union, set_inter_union_l.
         unionL; [by apply ETCCOH|].
         rewrite <- set_interK with (s:=dom_rel (sb ⨾ ⦗eq w⦘)).
         rewrite set_interA.
         rewrite EQWSB at 2.
         rewrite <- !seqA, dom_rel_eqv_dom_rel, !seqA.
         arewrite (sb ⨾ ⦗W_ex⦘ ⨾ sb ⊆ sb) by (generalize (@sb_trans G); basic_solver).
         intros b [AA BB].
         apply NNPP. intros CC.
         eapply MIN.
         { split; [apply BB|apply CC]. }
         destruct AA as [y AA].
         apply seq_eqv_r in AA. desf.
         apply seq_eqv_l. split; auto. generalize BB. unfold Execution.W_ex. basic_solver. }
    1-5: rewrite id_union, !seq_union_r, dom_union.
    1-5: unionL; [by apply ETCCOH|].
    5: rewrite RPPO_RMW_W.
    1-5: rewrite EQWSB.
    1-5: rewrite <- !seqA, dom_rel_eqv_dom_rel, !seqA.
    1-3: by arewrite (sb ⨾ ⦗W_ex⦘ ⨾ sb ⊆ sb) by (generalize (@sb_trans G); basic_solver).
    1,2: rewrite RPPO_WEX_SB; auto.
    { etransitivity; [|by apply RPPOSBE].
      clear. rewrite rtE. basic_solver 15. }
    rewrite set_inter_union_l.
    unionL; [by apply ETCCOH|].
    generalize WAA. unfold eissued. basic_solver 10. }
  destruct (classic (reserved T e \/ ~ W_ex e)) as [RES|NRES].
  { exists (mkETC (mkTC (ecovered T) (eissued T ∪₁ eq e))
                  (reserved T ∪₁ eq e ∪₁
                   dom_rel (sb ⨾ ⦗reserved T⦘) ∩₁ codom_rel (⦗eq e⦘ ⨾ rfi ⨾ rmw))).

    exists e.
    constructor; unfold eissued, ecovered; simpls.
    { right. left. splits; eauto. intuition. }
    unnw. constructor; unfold eissued, ecovered; simpls.
    { eapply trav_step_coherence.
      2: by apply ETCCOH.
      eapply trav_step_more_Proper.
      3: by eexists; eauto.
      { apply same_tc_Reflexive. }
      red. simpls. split; by symmetry. }
    { unionL; auto.
      { apply ETCCOH. }
      rewrite WF.(wf_rmwE).
      basic_solver. }
    { unionL; [|basic_solver].
      unionR left -> left. apply ETCCOH. }
    { rewrite !set_minus_union_l. unionL.
      3: { rewrite rmw_W_ex. basic_solver. }
      { rewrite <- ETCCOH.(etc_S_I_in_W_ex). basic_solver. }
      rewrite set_minus_union_r.
      basic_solver. }
    2: do 2 rewrite <- seqA.
    1-3: rewrite dom_r_sb_new_reserved; auto.
    1-3: rewrite id_union, !seq_union_r, dom_union.
    1-3: try unionR left.
    1-3: try rewrite !seqA.
    1-3: by unionL; [by apply ETCCOH|].
    { unfold dom_sb_S_rfrmw. simpls.
      rewrite dom_sb_new_reserved; auto.
      rewrite !id_union, !seq_union_l, !seq_union_r.
      rewrite dom_union, codom_union, set_inter_union_r.
      rewrite !set_inter_union_l.
      unionL.
      1,2: unionR left -> left.
      { apply ETCCOH. }
      { intros w' BB. apply NNPP. intros AA.
        apply NWHH. exists w'. split; auto.
        generalize BB. clear. basic_solver 10. }
      { unionR right.
        rewrite !seqA.
        rewrite rfi_union_rfe.
        rewrite !seq_union_l, !seq_union_r, codom_union, set_inter_union_r.
        arewrite (rfi ⨾ ⦗R_ex⦘ ⊆ rfi).
        arewrite (dom_rel (sb ⨾ ⦗reserved T⦘) ∩₁ codom_rel (⦗eq e⦘ ⨾ rfe ⨾ ⦗R_ex⦘ ⨾ rmw) ⊆₁ ∅).
        2: { unionL; [done|]. basic_solver. }
        rewrite set_interC.
        apply seq_codom_dom_inter_iff.
        split; [|basic_solver].
        rewrite !seqA.
        arewrite (reserved T ⊆₁ W ∩₁ reserved T).
        { generalize (reservedW WF ETCCOH). basic_solver. }
        rewrite id_inter.
        arewrite (rmw ⨾ sb ⊆ sb).
        { rewrite WF.(rmw_in_sb). generalize (@sb_trans G).
          clear. basic_solver. }
        sin_rewrite R_ex_sb_W_in_rppo.
        generalize dom_rfe_rppo_S_in_I. unfold eissued.
        generalize NISS. basic_solver 10. }
      arewrite_id ⦗R_ex⦘. rewrite seq_id_l.
      intros w [[y AA] [z BB]].
      exfalso.
      destruct_seq_l BB as CC; subst.
      destruct_seq_r AA as DD; subst.
      eapply rfrmw_sb_irr; eauto.
      apply seqA. eexists. eauto. }
    { unionR left.
      rewrite <- seqA at 1.
      rewrite dom_r_rppo_new_reserved; auto.
      rewrite !seqA.
      rewrite id_union, !seq_union_r, dom_union.
      unionL; [by apply ETCCOH|].
      sin_rewrite WF.(detour_rfe_data_rfi_rmw_rppo_in_detour_rfe_ppo).
      arewrite (eq e ⊆₁ issuable G sc (etc_TC T)) by basic_solver.
      eapply dom_detour_rfe_ppo_issuable; eauto. }
    { rewrite !id_union, !seq_union_r, !dom_union. unionL.
      { unionR left. apply ETCCOH. }
      { unionR left.
        destruct RES as [RES|RES].
        { arewrite (eq e ⊆₁ reserved T) by (generalize RES; basic_solver).
          apply ETCCOH. }
        transitivity (fun _ : actid => False); [|basic_solver].
        generalize RES. unfold Execution.W_ex. clear. basic_solver. }
      transitivity (fun _ : actid => False); [|basic_solver].
      unfold Execution.detour.
      clear RES. unfolder. ins. desf.
      all: assert (z2 = z) by (eapply WF.(wf_rmw_invf); eauto); subst.
      all: eapply codom_rfi_rfe_empty; basic_solver. }
    rewrite id_union, !seq_union_l, codom_union.
    rewrite set_inter_union_l.
    apply set_union_mori.
    2: arewrite (rfi ⊆ rf); basic_solver 10.
    rewrite set_inter_union_l. unionL; [by apply ETCCOH|].
    rewrite <- issuable_W_ex_in_codom_I_rfrmw; eauto.
    basic_solver. }
  assert (W_ex e) as WEXE.
  { apply NNPP. intuition. }
  assert (~ reserved T e) as NRESE by intuition.

  exists (mkETC (mkTC (ecovered T) (eissued T))
                (reserved T ∪₁ eq e)).
  exists e.
  constructor; unfold eissued, ecovered; simpls.
  { do 2 right. splits; eauto. }
  unnw. constructor; unfold eissued, ecovered; simpls.
  { by unionL; [by apply ETCCOH|]. }
  { unionR left. apply ETCCOH. }
  { rewrite !set_minus_union_l. unionL; [by apply ETCCOH|].
    generalize WEXE. basic_solver. }
  4: { unfold dom_sb_S_rfrmw. simpls.
       unionR left.
       rewrite id_union, !seq_union_r, dom_union.
       rewrite set_inter_union_l.
       unionL; [by apply ETCCOH|].
       intros w' BB. apply NNPP. intros AA.
       apply NWHH. exists w'. split; auto.
       unfold eissued. generalize BB. clear. basic_solver 20. }
  6: { rewrite !set_inter_union_l.
       unionL; [by apply ETCCOH|].
       rewrite EQEISS. by apply issuable_W_ex_in_codom_I_rfrmw. }
  1-5: rewrite id_union, !seq_union_r, dom_union.
  1-4: by unionL; [by apply ETCCOH|].
  unionL; [by apply ETCCOH|].
  rewrite WF.(rmw_in_ppo).
  rewrite EQEISS. arewrite (detour ⊆ detour ∪ rfe). by apply dom_detour_rfe_ppo_issuable.
Qed.

Lemma exists_ext_trav_step e (N_FIN : next G (ecovered T) e) :
  exists T', ext_trav_step T T'.
Proof using WF IMMCON ETCCOH.
  edestruct exists_trav_step; eauto.
  { apply ETCCOH. }
  eapply trav_step_to_ext_trav_step; eauto.
Qed.

End Props.

Definition same_ext_trav_config (T T' : ext_trav_config) :=
  ecovered T ≡₁ ecovered T' /\ eissued T ≡₁ eissued T' /\
  reserved T ≡₁ reserved T'.

Lemma same_ext_trav_config_refl : reflexive same_ext_trav_config.
Proof using. split; basic_solver. Qed.

Lemma same_ext_trav_config_sym : symmetric same_ext_trav_config.
Proof using.
  unfold same_ext_trav_config; split; splits; ins; desf; symmetry; auto.
Qed.

Lemma same_ext_trav_config_trans : transitive same_ext_trav_config.
Proof using.
  unfold same_ext_trav_config; split; splits; ins; desf; etransitivity; eauto.
Qed.

Add Parametric Relation : ext_trav_config same_ext_trav_config
    reflexivity proved by same_ext_trav_config_refl
    symmetry proved by same_ext_trav_config_sym
    transitivity proved by same_ext_trav_config_trans
      as same_etc.

Add Parametric Morphism : etc_coherent with signature
    eq ==> eq ==> same_ext_trav_config ==> iff as etc_coherent_more.
Proof using.
  intros G' sc' T T' EQT. cdes EQT.
  split.
  symmetry in EQT0.
  symmetry in EQT1.
  symmetry in EQT2.
  (* TODO: introduce a morphism for dom_sb_S_rfrmw instead. *)
  all: intros HH; constructor; try unfold dom_sb_S_rfrmw.
  all: try rewrite EQT0.
  all: try rewrite EQT1.
  all: try rewrite EQT2.
  all: try apply HH.
  all: eapply tc_coherent_more; eauto; [|by apply HH].
  all: red; unfold ecovered, eissued in *; eauto.
Qed.

Add Parametric Morphism : ext_itrav_step with signature
    eq ==> same_ext_trav_config ==> same_ext_trav_config ==> iff as
        ext_itrav_step_more.
Proof using.
  intros x TA TB EQ TA' TB' EQ'.
  split.
  symmetry in EQ.
  symmetry in EQ'.
  all: intros HH; split; unnw;
    [|by eapply etc_coherent_more; eauto; apply HH].
  all: cdes EQ; cdes EQ'.
  all: try unfold dom_sb_S_rfrmw.
  all: try rewrite EQ0.
  all: try rewrite EQ1.
  all: try rewrite EQ2.
  all: try rewrite EQ'0.
  all: try rewrite EQ'1.
  all: try rewrite EQ'2.
  all: inv HH; desf; [left| right; left| right; right]; splits; auto.
  all: generalize EQ0 EQ1 EQ2; basic_solver 10.
Qed.

Lemma ext_trav_step_in_trav_step :
  ext_trav_step ⊆ etc_TC ⋄ (same_trav_config ∪ trav_step G sc).
Proof using WF IMMCON.
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
    2: apply ETCCOH'.
    red; splits; simpls; by symmetry. }
  apply issuable_add_eq_iff; auto. 
  eapply issued_in_issuable; [|basic_solver].
  eapply tc_coherent_more.
  2: apply ETCCOH'.
  red; splits; simpls; by symmetry.
Qed.

Definition ext_init_trav := mkETC (mkTC (is_init ∩₁ E) (is_init ∩₁ E)) (is_init ∩₁ E).

Lemma ext_init_trav_coherent : etc_coherent G sc ext_init_trav.
Proof using WF IMMCON.
  unfold ext_init_trav.
  constructor; unfold dom_sb_S_rfrmw, eissued, ecovered; simpls.
  { by apply init_trav_coherent. }
  { basic_solver. }
  6: rewrite WF.(rppo_in_sb).
  2-6: rewrite no_sb_to_init; basic_solver.
  { intros x [AA BB]. intuition. }
  rewrite rmw_W_ex.
  all: rewrite WF.(W_ex_not_init); basic_solver.
Qed.

Lemma ext_itrav_stepE e T T' (STEP : ext_itrav_step e T T') : E e.
Proof using.
  red in STEP. desf.
  { eapply coveredE.
    2: apply COVEQ; basic_solver.
    apply ETCCOH'. }
  { eapply issuedE.
    { apply ETCCOH'. }
    apply ISSEQ. basic_solver. }
  eapply ETCCOH'.(etc_S_in_E).
  apply RESEQ. basic_solver.
Qed.

Lemma ext_itrav_step_reserveW e T
      (STEP : ext_itrav_step e T (mkETC (etc_TC T) (reserved T ∪₁ eq e))) :
  W e.
Proof using WF.
  red in STEP. desf.
  { exfalso. apply NCOV.
    apply COVEQ. basic_solver. }
  { exfalso. apply NISS.
    apply ISSEQ. basic_solver. }
  apply (reservedW WF ETCCOH'). basic_solver.
Qed.

Lemma ext_itrav_step_reserve_nS e T
      (STEP : ext_itrav_step e T (mkETC (etc_TC T) (reserved T ∪₁ eq e))) :
  ~ reserved T e.
Proof using.
  red in STEP. desf.
  { exfalso. apply NCOV.
    apply COVEQ. basic_solver. }
  exfalso. apply NISS.
  apply ISSEQ. basic_solver.
Qed.

Lemma ext_itrav_step_nC e T T'
      (ETCCOH : etc_coherent G sc T)
      (STEP : ext_itrav_step e T T') : ~ ecovered T e.
Proof using WF.
  assert (tc_coherent G sc (etc_TC T)) as TCCOH by apply ETCCOH.
  intros AA.
  red in STEP. desf.
  { assert (issued (etc_TC T') e) as BB.
    { apply ISSEQ. basic_solver. }
    apply NISS. eapply w_covered_issued; eauto.
    split; auto.
    eapply issuedW; [|by eauto].
    apply ETCCOH'. }
  apply NISS. apply ETCCOH.(etc_I_in_S).
  eapply w_covered_issued; eauto.
  split; auto.
  eapply (reservedW WF ETCCOH').
  apply RESEQ. basic_solver.
Qed.

Lemma ext_itrav_step_ninit e T T'
      (ETCCOH : etc_coherent G sc T)
      (STEP : ext_itrav_step e T T') : ~ is_init e.
Proof using WF.
  assert (tc_coherent G sc (etc_TC T)) as TCCOH by apply ETCCOH.
  intros II. eapply ext_itrav_step_nC; eauto.
  eapply init_covered; eauto.
  split; auto.
  eapply ext_itrav_stepE; eauto.
Qed.

Lemma ext_itrav_step_cov_coverable T e
      (ETCCOH : etc_coherent G sc T)
      (TSTEP : ext_itrav_step
                 e T (mkETC (mkTC (ecovered T ∪₁ eq e) (eissued T)) (reserved T))) :
  coverable G sc (etc_TC T) e.
Proof using IMMCON.
  apply coverable_add_eq_iff; auto.
  apply covered_in_coverable; [|basic_solver].
  apply TSTEP.
Qed.

Lemma ext_itrav_step_cov_next T e
      (ETCCOH : etc_coherent G sc T)
      (TSTEP : ext_itrav_step
                 e T (mkETC (mkTC (ecovered T ∪₁ eq e) (eissued T)) (reserved T))) :
  next G (ecovered T) e.
Proof using WF IMMCON.
  split; [split|].
  { eapply ext_itrav_stepE; eauto. }
  { eapply ext_itrav_step_cov_coverable; eauto. }
  red. eapply (ext_itrav_step_nC ETCCOH). eauto.
Qed.

Lemma ext_itrav_step_iss_issuable T S' e
      (ETCCOH : etc_coherent G sc T)
      (TSTEP : ext_itrav_step
                 e T (mkETC (mkTC (ecovered T) (eissued T ∪₁ eq e)) S')) :
  issuable G sc (etc_TC T) e.
Proof using WF IMMCON.
  apply issuable_add_eq_iff; auto.
  apply issued_in_issuable; [|basic_solver].
  apply TSTEP.
Qed.

Lemma ext_itrav_step_iss_nI T e S'
      (ETCCOH : etc_coherent G sc T)
      (TSTEP : ext_itrav_step
                 e T (mkETC (mkTC (ecovered T) (eissued T ∪₁ eq e)) S')) :
  ~ eissued T e.
Proof using.
  assert (tc_coherent G sc (etc_TC T)) as TCCOH by apply ETCCOH.
  intros AA.
  red in TSTEP. desf.
  { apply NCOV. apply COVEQ. basic_solver. }
  apply NISS. by apply ETCCOH.(etc_I_in_S).
Qed.

Lemma dom_sb_S_rfrmw_same_tid T w (NINIT : ~ is_init w) :
  dom_sb_S_rfrmw G T rfi (eq w) ⊆₁ (fun x => tid x = (tid w)).
Proof using WF.
  unfold dom_sb_S_rfrmw.
  arewrite (rfi ⊆ sb).
  rewrite WF.(rmw_in_sb).
  arewrite (sb ⨾ sb ⊆ sb).
  { generalize (@sb_trans G). basic_solver. }
  arewrite (⦗eq w⦘ ⊆ ⦗eq w⦘ ⨾ ⦗ set_compl is_init ⦘).
  { basic_solver. }
  rewrite ninit_sb_same_tid.
  basic_solver.
Qed.

End ExtTraversalConfig.
