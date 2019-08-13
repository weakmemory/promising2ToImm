From hahn Require Import Hahn.
From imm Require Import Events Execution Execution_eco
     TraversalConfig Traversal imm_common imm_s imm_s_hb CombRelations.

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

  Definition rppo := (ctrl ∪ addr;;sb^? ∪ rmw_dep^? ;; <| R_ex |> ;; sb) ;; <| W |>.

  Record ext_trav_config :=
    mkETC { etc_TC : trav_config; reserved : actid -> Prop; }.
  
  Definition eissued  T := issued  (etc_TC T).
  Definition ecovered T := covered (etc_TC T).

  Record etc_coherent (T : ext_trav_config) :=
    mkETCC {
        etc_tccoh  : tc_coherent G sc (etc_TC T);

        etc_I_in_S : eissued T ⊆₁ reserved T;
        etc_S_I_in_W_ex : reserved T \₁ eissued T ⊆₁ W_ex;

        etc_dr_R_acq_I :
          dom_rel ((detour ∪ rfe) ⨾ <|R∩₁Acq|> ;; sb ⨾ ⦗reserved T⦘) ⊆₁ eissued T ;
        etc_W_ex_sb_I : dom_rel (⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗reserved T⦘) ⊆₁ eissued T ;
        etc_po_S      : dom_rel (<|W_ex|> ;; sb ;; <| reserved T |>) ⊆₁ reserved T;
        etc_rppo_S :
          dom_rel ((detour ∪ rfe) ;; (data ∪ rfi)^* ;; rppo ;; <| reserved T |>) ⊆₁ eissued T;
    }.
  
  Definition ext_itrav_step (e : actid) T T' :=
    (⟪ COVER :
         ⟪ NCOV : ~ ecovered T e ⟫ /\
         ⟪ COVEQ: ecovered T' ≡₁ ecovered T ∪₁ eq e ⟫ /\
         ⟪ ISSEQ: eissued  T' ≡₁ eissued  T ⟫
     ⟫ \/
     ⟪ ISSUE :
         ⟪ NISS : ~ eissued T e ⟫ /\
         ⟪ RES  : W_ex e -> reserved T e ⟫ /\
         ⟪ COVEQ: ecovered T' ≡₁ ecovered T ⟫ /\
         ⟪ ISSEQ: eissued  T' ≡₁ eissued  T ∪₁ eq e ⟫ /\
         ⟪ RESEQ: reserved T' ≡₁ reserved T ∪₁ eq e ⟫
    ⟫ \/
    ⟪ RESERVE :
        ⟪ NISS : ~ reserved T e ⟫ /\
        ⟪ COVEQ: ecovered T' ≡₁ ecovered T ⟫ /\
        ⟪ ISSEQ: eissued  T' ≡₁ eissued  T ⟫ /\
        ⟪ RESEQ: reserved T' ≡₁ reserved T ∪₁ (eq e) ⟫
    ⟫) /\
    ⟪ ETCCOH' : etc_coherent T' ⟫.

  Definition ext_trav_step T T' := exists e, ext_itrav_step e T T'.
  
  Lemma rppo_sb_in_rppo : rppo ;; sb ;; <|W|> ⊆ rppo.
  Proof.
    unfold rppo.
    hahn_frame. arewrite_id ⦗W⦘. rewrite seq_id_l.
    rewrite !seq_union_l, !seqA.
    rewrite WF.(ctrl_sb).
    arewrite (sb^? ⨾ sb ⊆ sb^?).
    { generalize (@sb_trans G). basic_solver. }
    arewrite (sb ⨾ sb ⊆ sb).
    2: done.
    apply transitiveI. apply sb_trans.
  Qed.

  Lemma exists_next_to_reserve w T
        (NRES : ~ reserved T w) :
    exists w',
      << SBB : (<|W_ex \₁ reserved T|> ;; sb)^? w' w >> /\
      << NB  : ~ codom_rel (<|W_ex \₁ reserved T|> ;; sb) w' >>.
  Proof.
    generalize dependent w.
    set (Q w := ~ reserved T w ->
                exists w',
                  << SBB : (<|W_ex \₁ reserved T|> ;; sb)^? w' w >> /\
                  << NB  : ~ codom_rel (<|W_ex \₁ reserved T|> ;; sb) w' >>).
    apply (@well_founded_ind _ sb (wf_sb G) Q).
    intros x IND; subst Q; simpls.
    intros NRESX.
    destruct (classic (exists w', (<|W_ex \₁ reserved T|> ;; sb) w' x)) as [[w' HH]|NEX].
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
  Proof.
    red in TS. desf. cdes TS.
    desf.
    { exists (mkETC (mkTC (ecovered T ∪₁ eq e) (eissued T)) (reserved T)).
      eexists e.
      red. splits.
      { left. splits; auto. }
      constructor; unfold eissued, ecovered; simpls.
      all: try by apply ETCCOH.
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
      4: by apply ETCCOH.
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
    
    assert (dom_rel ((detour ∪ rfe) ⨾ ⦗R ∩₁ Acq⦘ ⨾ sb ⨾ ⦗eq w⦘) ⊆₁ issued (etc_TC T)) as RP.
    { admit. }


    destruct SBB as [|SBB]; subst.
    2: { apply seq_eqv_l in SBB. destruct SBB as [[WEXW _] SBB].
         exists (mkETC (etc_TC T) (reserved T ∪₁ eq w)).
         red. exists w. red.
         splits.
         { do 2 right. splits; simpls. }
         constructor; unfold eissued, ecovered; simpls.
         { apply ETCCOH. }
         { etransitivity.
           { by apply etc_I_in_S. }
           basic_solver. }
         { rewrite set_minus_union_l. unionL.
           { apply ETCCOH. }
           basic_solver. }
         all: rewrite id_union, !seq_union_r; rewrite dom_union; unionL.
         all: try by apply ETCCOH.
         3: { unionR left. apply ETCCOH. }


    exists (mkETC (etc_TC T) (reserved T ∪₁ eq w)).
    red. exists w. red.
    splits.
    { do 2 right. splits; simpls. }
    constructor; unfold eissued, ecovered; simpls.
    { apply ETCCOH. }
    { etransitivity.
      { by apply etc_I_in_S. }
      basic_solver. }
    { rewrite set_minus_union_l. unionL.
      { apply ETCCOH. }

  Admitted.

  
  Lemma exists_ext_trav_step T (ETCCOH : etc_coherent T)
        e (N_FIN : next G (ecovered T) e) :
    exists T', ext_trav_step T T'.
  Proof.
  Admitted.

End ExtTraversalConfig.
