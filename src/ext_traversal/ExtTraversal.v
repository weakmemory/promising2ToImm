Require Import Setoid.
From hahn Require Import Hahn.
From imm Require Import AuxDef Events Execution Execution_eco
     imm_common imm_s imm_s_hb CombRelations.
Require Import TraversalConfig Traversal.
Require Import AuxRel AuxRel2.
Require Export ExtTravRelations.
Require Import TraversalProperties.

Set Implicit Arguments.

(* TODO: move to a more appropriate place (imm). *)
Lemma W_ex_in_E G (WF : Wf G): W_ex G ⊆₁ acts_set G.
Proof.
  unfold W_ex. rewrite WF.(wf_rmwE). basic_solver.
Qed.

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

Record ext_trav_config :=
  mkETC { etc_TC : trav_config; reserved : actid -> Prop; }.

Definition eissued  T := issued  (etc_TC T).
Definition ecovered T := covered (etc_TC T).

Record etc_coherent (T : ext_trav_config) :=
  mkETCC {
      etc_tccoh  : tc_coherent G sc (etc_TC T);

      etc_S_in_E : reserved T ⊆₁ E;
      etc_I_in_S : eissued T ⊆₁ reserved T;
      etc_S_I_in_W_ex : reserved T \₁ eissued T ⊆₁ W_ex;

      etc_F_sb_S : dom_rel (⦗F∩₁Acq/Rel⦘ ⨾ sb ⨾ ⦗reserved T⦘) ⊆₁ ecovered T ;
      etc_dr_R_acq_I :
        dom_rel ((detour ∪ rfe) ⨾ ⦗R∩₁Acq⦘ ⨾ sb ⨾ ⦗reserved T⦘) ⊆₁ eissued T ;
      etc_W_ex_sb_I : dom_rel (⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗reserved T⦘) ⊆₁ eissued T ;
      
      etc_sb_S :
        dom_rel (⦗W_ex⦘ ⨾ sb ⨾ ⦗ reserved T ⦘) ∩₁
        codom_rel (<|eissued T|> ;; rf ;; rmw) ⊆₁
        reserved T;

      etc_rppo_S :
        dom_rel ((detour ∪ rfe) ⨾ (data ∪ rfi)＊ ⨾ rppo ⨾ ⦗ reserved T ⦘) ⊆₁ eissued T;

      etc_S_W_ex_rfrmw_I : reserved T ∩₁ W_ex ⊆₁ codom_rel (<|eissued T|> ;; rf ;; rmw);
    }.

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
                (dom_rel (<|W_ex|> ;; sb ;; <|eissued T|>) ∩₁
                 codom_rel (<|eq e|> ;; rfi ;; rmw)) ⟫
   ⟫ \/
   ⟪ RESERVE :
       ⟪ NISS : ~ reserved T e ⟫ /\
       ⟪ COVEQ: ecovered T' ≡₁ ecovered T ⟫ /\
       ⟪ ISSEQ: eissued  T' ≡₁ eissued  T ⟫ /\
       ⟪ RESEQ: reserved T' ≡₁ reserved T ∪₁ eq e ⟫
  ⟫) /\
  ⟪ ETCCOH' : etc_coherent T' ⟫.

Definition ext_trav_step T T' := exists e, ext_itrav_step e T T'.

Lemma eissuedW T (ETCCOH : etc_coherent T) : eissued T ⊆₁ W.
Proof using. unfold eissued. eapply issuedW. apply ETCCOH. Qed.

Lemma reservedW T (ETCCOH : etc_coherent T) : reserved T ⊆₁ W.
Proof using WF.
  arewrite (reserved T ⊆₁ reserved T \₁ eissued T ∪₁ reserved T ∩₁ eissued T).
  2: { rewrite eissuedW at 2; auto. rewrite etc_S_I_in_W_ex; auto.
       rewrite W_ex_in_W; auto. basic_solver. }
  unfolder. ins.
  destruct (classic (eissued T x)); eauto.
Qed.

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

Lemma trav_step_to_ext_trav_step T (ETCCOH : etc_coherent T)
      TC' (TS : trav_step G sc (etc_TC T) TC') :
  exists T', ext_trav_step T T'.
Proof using WF.
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

  destruct
  (classic (exists w,
               (dom_rel (<|W_ex|> ;; sb ;; <|eq e|>) ∩₁
                codom_rel (<|eissued T|> ;; rf ;; rmw) \₁ reserved T) w)) as [[w WHH]|NWHH].
  2: { destruct (classic (reserved T e)) as [RES|NRES].
       { exists (mkETC (mkTC (ecovered T) (eissued T ∪₁ eq e))
                       (reserved T ∪₁ eq e ∪₁
                        dom_rel (⦗W_ex⦘ ⨾ sb ⨾ ⦗issued (etc_TC T)⦘) ∩₁ codom_rel (⦗eq e⦘ ⨾ rfi ⨾ rmw))).
         exists e.
         constructor; unfold eissued, ecovered; simpls.
         { right. left. splits; eauto. }
         unnw. constructor; unfold eissued, ecovered; simpls.
         { eapply trav_step_coherence.
           2: by apply ETCCOH. 
           eapply trav_step_more_Proper.
           3: by eexists; eauto.
           { apply same_tc_Reflexive. }
           red. simpls. split; by symmetry. }
         { unionL; auto.
           { apply ETCCOH. }
           rewrite WF.(W_ex_in_E), WF.(wf_rmwE).
           basic_solver. }
         { unionL; [|basic_solver].
           unionR left -> left. apply ETCCOH. }
         { rewrite !set_minus_union_l. unionL.
           3: basic_solver.
           { rewrite <- ETCCOH.(etc_S_I_in_W_ex). basic_solver. }
           rewrite set_minus_union_r.
           basic_solver. }
         (* TODO: continue from here. *)

         etransitivity.
         2: by apply ETCCOH.
         unfold eissued; simpls.
         basic_solver. }

         all: try by (unionR left; apply ETCCOH).
         all: try by apply ETCCOH.
       

  { destruct WHH as [[WSB RFRMW] NSW].
    assert (W_ex w) as WEW.
    { generalize WSB. basic_solver. }
    assert (E w) as EW.
    { by apply W_ex_in_E. }

    exists (mkETC (mkTC (ecovered T) (eissued T)) (reserved T ∪₁ eq w)), w.
    red. splits.
    { do 2 right. splits; auto. }
    split; unfold eissued, ecovered; simpls.
    all: try by (unionR left; apply ETCCOH).
    { unionL; [by apply ETCCOH|].
      basic_solver. }
    { rewrite set_minus_union_l. unionL; [by apply ETCCOH|].
      generalize WEW. basic_solver. }
    rewrite set_inter_union_l. unionL; [by apply ETCCOH|].
    generalize RFRMW. unfold eissued. basic_solver. }

  destruct (classic (reserved T e)) as [RES|NRES].
  { exists (mkETC (mkTC (ecovered T) (eissued T ∪₁ eq e))
                (reserved T ∪₁ eq e ∪₁ codom_rel (<|eq e|> ;; rfi ;; rmw))).
    red. exists e. red. unfold eissued, ecovered; splits; simpls.
    { right. left. splits; auto. }
    split; unfold eissued, ecovered; simpls.
    (* TODO: continue from here. *)

  red in TS. desf. cdes TS.
  desf.
  { exists (mkETC (mkTC (ecovered T ∪₁ eq e) (eissued T)) (reserved T)).
    eexists e.
    red. splits.
    { left. splits; auto. }
    constructor; unfold eissued, ecovered; simpls.
    all: try by apply ETCCOH.
    2: by unionR left; apply ETCCOH.
    (* TODO: generalize to a lemma *)
    eapply trav_step_coherence.
    2: by apply ETCCOH. 
    eapply trav_step_more_Proper.
    3: by eexists; eauto.
    { apply same_tc_Reflexive. }
    red. simpls. split; by symmetry. }
  destruct (classic (reserved T e)) as [RES|NRES].
  { exists (mkETC (mkTC (ecovered T) (eissued T ∪₁ eq e)) (reserved T)).
    exists e.
    constructor; unfold eissued, ecovered; simpls.
    { right. left. splits; eauto.
      generalize RES. basic_solver. }
    unnw. constructor; unfold eissued, ecovered; simpls.
    all: try by (unionR left; apply ETCCOH).
    all: try by apply ETCCOH.
    { eapply trav_step_coherence.
      2: by apply ETCCOH. 
      eapply trav_step_more_Proper.
      3: by eexists; eauto.
      { apply same_tc_Reflexive. }
      red. simpls. split; by symmetry. }
    { unionL.
      { by apply etc_I_in_S. }
      basic_solver. }
    etransitivity.
    2: by apply ETCCOH.
    unfold eissued; simpls.
    basic_solver. }
  edestruct exists_next_to_reserve as [w]; eauto. desf.
  assert (~ reserved T w) as NRESW.
  { destruct SBB as [|AA]; desf. apply seq_eqv_l in AA. apply AA. }
  assert (~ eissued T w) as NISSW.
  { intros AA. apply NRESW. apply etc_I_in_S; eauto. }
  assert (E e) as EE.
  { apply ISS. }
  assert (W e) as WE.
  { eapply issuableW; eauto. }
  assert (E w) as EW.
  { destruct SBB as [|SBB]; desf.
    destruct_seq_l SBB as AA.
    apply (dom_l G.(wf_sbE)) in SBB.
      by destruct_seq_l SBB as BB. }
  assert (eq e ⊆₁ issuable G sc (etc_TC T)) as EISS.
  { basic_solver. }

  destruct (classic (W_ex w)) as [WEX|NEWX].
  { exists (mkETC (etc_TC T) (reserved T ∪₁ eq w)).
    red. exists w. red.
    splits.
    { do 2 right. splits; simpls. }
    constructor; unfold eissued, ecovered; simpls.
    { apply ETCCOH. }
    { unionL; [by apply ETCCOH|].
      red. ins; desf. }
    { etransitivity.
      { by apply etc_I_in_S. }
      basic_solver. }
    { rewrite set_minus_union_l. unionL.
      { apply ETCCOH. }
      basic_solver. }
    all: rewrite id_union, !seq_union_r; rewrite dom_union; unionL.
    all: try by apply ETCCOH.
    5: { unionR left. unfolder. ins. desf.
         apply NNPP. intros HH. apply NB.  basic_solver 10. }
    4: { unionR left. apply ETCCOH. }
    all: rewrite <- !seqA.
    all: rewrite dom_eqv_seq with (r':=sb^? ⨾ ⦗eq e⦘) at 1;
      [|exists e; generalize SBB; basic_solver 10].
    all: rewrite !seqA.
    all: arewrite_id ⦗eq w⦘; rewrite seq_id_l.
    1,2,3: arewrite (sb ⨾ sb^? ⊆ sb) by (generalize (@sb_trans G); basic_solver).
    4: arewrite (⦗eq e⦘ ⊆ ⦗W⦘ ⨾ ⦗eq e⦘) at 1 by basic_solver.
    all: rewrite EISS.
    { arewrite (⦗F ∩₁ Acq/Rel⦘ ⨾ sb ⊆ fwbob).
      unfold issuable. basic_solver 10. }
    { eapply dom_detour_rfe_acq_sb_issuable; eauto. }
    { by apply dom_wex_sb_issuable. }
    sin_rewrite WF.(rppo_cr_sb_in_rppo).
    sin_rewrite WF.(detour_rfe_data_rfi_rppo_in_detour_rfe_ppo).
    rewrite !seqA. by apply dom_detour_rfe_ppo_issuable. }
  assert (w = e); subst.
  { destruct SBB as [|SBB]; desf.
    unfolder in SBB. desf. }
  exists (mkETC (mkTC (ecovered T) (eissued T ∪₁ eq e)) (reserved T ∪₁ eq e)).
  exists e.
  red. splits.
  { right. left. splits; auto. desf. }
  constructor; unfold eissued, ecovered; simpls.
  { (* TODO: generalize to a lemma *)
    eapply trav_step_coherence.
    2: by apply ETCCOH. 
    eapply trav_step_more_Proper.
    3: by eexists; eauto.
    { apply same_tc_Reflexive. }
    red. simpls. split; by symmetry. }
  { unionL; [by apply ETCCOH|]. 
    basic_solver. }
  { apply set_union_mori; [|done].
    apply ETCCOH. }
  { rewrite set_minus_union_l. unionL.
    2: { unfolder. intros x [HH AA]. desf. exfalso. apply AA. eauto. }
    etransitivity.
    2: by apply ETCCOH.
    basic_solver. }
  all: rewrite id_union, !seq_union_r; rewrite dom_union; unionL.
  all: try unionR left.
  all: try by apply ETCCOH.
  4: { unfolder. ins. desf.
       apply NNPP. intros HH. apply NB. basic_solver 10. }
  all: rewrite EISS.
  { arewrite (⦗F ∩₁ Acq/Rel⦘ ⨾ sb ⊆ fwbob).
    unfold issuable. basic_solver 10. }
  { eapply dom_detour_rfe_acq_sb_issuable; eauto. }
  { by apply dom_wex_sb_issuable. }
  sin_rewrite WF.(detour_rfe_data_rfi_rppo_in_detour_rfe_ppo).
  rewrite !seqA. by apply dom_detour_rfe_ppo_issuable.
Qed.

Lemma exists_ext_trav_step T (ETCCOH : etc_coherent T)
      e (N_FIN : next G (ecovered T) e) :
  exists T', ext_trav_step T T'.
Proof using WF IMMCON.
  edestruct exists_trav_step; eauto.
  { apply ETCCOH. }
  eapply trav_step_to_ext_trav_step; eauto.
Qed.

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
    same_ext_trav_config ==> iff as etc_coherent_more.
Proof using.
  intros T T' EQT. cdes EQT.
  split.
  symmetry in EQT0.
  symmetry in EQT1.
  symmetry in EQT2.
  all: intros HH; constructor.
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

Lemma ext_init_trav_coherent : etc_coherent ext_init_trav.
Proof using WF IMMCON.
  unfold ext_init_trav.
  constructor; unfold eissued, ecovered; simpls.
  { by apply init_trav_coherent. }
  { basic_solver. }
  6: rewrite WF.(rppo_in_sb).
  2-6: rewrite no_sb_to_init; basic_solver.
  intros x [AA BB]. intuition.
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
  apply ETCCOH'.(reservedW). basic_solver.
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
      (ETCCOH : etc_coherent T)
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
  eapply ETCCOH'.(reservedW).
  apply RESEQ. basic_solver.
Qed.

Lemma ext_itrav_step_ninit e T T'
      (ETCCOH : etc_coherent T)
      (STEP : ext_itrav_step e T T') : ~ is_init e.
Proof using WF.
  assert (tc_coherent G sc (etc_TC T)) as TCCOH by apply ETCCOH.
  intros II. eapply ext_itrav_step_nC; eauto.
  eapply init_covered; eauto.
  split; auto.
  eapply ext_itrav_stepE; eauto.
Qed.

Lemma ext_itrav_step_cov_coverable T e
      (ETCCOH : etc_coherent T)
      (TSTEP : ext_itrav_step
                 e T (mkETC (mkTC (ecovered T ∪₁ eq e) (eissued T)) (reserved T))) :
  coverable G sc (etc_TC T) e.
Proof using IMMCON.
  apply coverable_add_eq_iff; auto.
  apply covered_in_coverable; [|basic_solver].
  apply TSTEP.
Qed.

Lemma ext_itrav_step_cov_next T e
      (ETCCOH : etc_coherent T)
      (TSTEP : ext_itrav_step
                 e T (mkETC (mkTC (ecovered T ∪₁ eq e) (eissued T)) (reserved T))) :
  next G (ecovered T) e.
Proof using WF IMMCON.
  split; [split|].
  { eapply ext_itrav_stepE; eauto. }
  { eapply ext_itrav_step_cov_coverable; eauto. }
  red. eapply (ext_itrav_step_nC ETCCOH). eauto.
Qed.

Lemma ext_itrav_step_iss_issuable T e
      (ETCCOH : etc_coherent T)
      (TSTEP : ext_itrav_step
                 e T (mkETC (mkTC (ecovered T) (eissued T ∪₁ eq e)) (reserved T ∪₁ eq e))) :
  issuable G sc (etc_TC T) e.
Proof using WF IMMCON.
  apply issuable_add_eq_iff; auto.
  apply issued_in_issuable; [|basic_solver].
  apply TSTEP.
Qed.

Lemma ext_itrav_step_iss_nI T e
      (ETCCOH : etc_coherent T)
      (TSTEP : ext_itrav_step
                 e T (mkETC (mkTC (ecovered T) (eissued T ∪₁ eq e)) (reserved T ∪₁ eq e))) :
  ~ eissued T e.
Proof using.
  assert (tc_coherent G sc (etc_TC T)) as TCCOH by apply ETCCOH.
  intros AA.
  red in TSTEP. desf.
  { apply NCOV. apply COVEQ. basic_solver. }
  apply NISS. by apply ETCCOH.(etc_I_in_S).
Qed.

End ExtTraversalConfig.
