From hahn Require Import Hahn.

From imm Require Import Events.
From imm Require Import Execution.
From imm Require Import Execution_eco.
From imm Require Import imm_s.
From imm Require Import imm_s_hb.
From imm Require Import imm_bob imm_s_ppo.
From imm Require Import CombRelations.
From imm Require Import AuxDef.
From imm Require Import AuxRel2.
From imm Require Import travorder.SimClosure.
From imm Require Import TLSCoherency.
From imm Require Import IordCoherency.
From imm Require Import TraversalOrder. 
Require Import TlsEventSets.
Require Import Next.
Require Import ExtTraversalConfig.
Require Import ExtTraversal.
Require Import ExtTraversalProperties.
Require Import AuxRel.
Require Import EventsTraversalOrder.

Set Implicit Arguments.

(* TODO: move the section to IordCoherency *)
Section E_E.
  Variables (G: execution) (sc: relation actid). 
  Hypotheses (WF: Wf G)
             (WFSC: wf_sc G sc).
  Notation "'E'" := (acts_set G).

  Let E_E := E × E.

  Lemma co_E_E: co G ⊆ E_E. 
  Proof using WF. rewrite wf_coE; basic_solver. Qed.

  Lemma fr_E_E: fr G ⊆ E_E. 
  Proof using WF. rewrite wf_frE; basic_solver. Qed.

  Lemma E_E_trans: transitive E_E. 
  Proof using. unfold E_E. basic_solver. Qed. 

  Lemma iord_simpl_E_E:
    iord_simpl G sc ⊆ event ↓ E_E^?.
  Proof using WF WFSC.
    unfold iord_simpl. unfold SB, RF, FWBOB, AR, IPROP, PROP.
    rewrite ppo_in_sb, fwbob_in_sb; auto.
    repeat rewrite inclusion_seq_eqv_l with (dom := action ↓₁ eq _). 
    repeat rewrite inclusion_seq_eqv_r with (dom := action ↓₁ eq _). 
    rewrite inclusion_inter_l1 with (r := sb G).
    rewrite ?sb_E_ENI, ?rf_E_ENI, ?co_E_E; auto.
    rewrite ar_E_ENI; auto.
    rewrite (sc_E_ENI _ _ WF WFSC); auto.
    arewrite (E × (E \₁ is_init) ⊆ E × E) by basic_solver. 
    fold E_E. 
    rewrite <- !seqA.
    (rewrite ?(@rt_of_trans _ E_E), ?(@rewrite_trans _ E_E),
             ?unionK, ?(@rewrite_trans _ E_E),
             ?(@rewrite_trans_seq_cr_cr _ E_E), ?(@ct_of_trans _ E_E),
      ?cr_rt, ?rt_cr,
      ?(@rt_of_trans _ E_E)
           ); auto using E_E_trans.    
    basic_solver 10. 
  Qed.  

End E_E. 


(* TODO: move; update proof of iord_simpl_tc_doma_impl using this *)
Lemma iord_simpl_tc_doma_impl G sc S
      (WF: Wf G)
      (WFSC: wf_sc G sc)
      (S_E: S ⊆₁ event ↓₁ acts_set G)
  :
  doma (iord_simpl G sc ⨾ ⦗S⦘) (event ↓₁ acts_set G).
Proof using.
  rewrite iord_simpl_E_E; auto. rewrite crE, map_rel_union, seq_union_l.
  apply union_doma.
  2: { basic_solver. }
  rewrite S_E. unfolder. ins. desc. congruence. 
Qed.


(* TODO: move to EventsTraversalOrder *)
Lemma dom_sb_sc_ct_coverable G sc T
      (TCOH: tls_coherent G T)
      (WF: Wf G)
      (WFSC: wf_sc G sc):
  dom_rel ((sb G ∪ sc)^+ ⨾ ⦗coverable G sc T⦘) ⊆₁ covered T. 
Proof using. 
  unfold coverable, covered. rewrite id_inter, <- seqA.
  apply dom_rel_iord_ext_parts.
  3: { rewrite init_covered; eauto. basic_solver. }
  2: { rewrite inclusion_seq_eqv_r.
       rewrite <- ct_of_trans with (r := _ × _); [| basic_solver].
       apply clos_trans_mori. 
       rewrite (wf_scE WFSC), (no_sc_to_init WF WFSC), wf_sbE, no_sb_to_init; eauto.
       basic_solver. }
  transitivity (SB G sc); [| unfold iord_simpl; basic_solver 10].
  unfold SB. basic_solver. 
Qed. 

Lemma dom_sb_sc_ct_covered G sc T
      (TCOH: tls_coherent G T)
      (WF: Wf G)
      (WFSC: wf_sc G sc)
      (ICOH: iord_coherent G sc T):
  dom_rel ((sb G ∪ sc)^+ ⨾ ⦗covered T⦘) ⊆₁ covered T. 
Proof using.
  rewrite covered_in_coverable at 1; eauto. by apply dom_sb_sc_ct_coverable. 
Qed. 
  

Section ExtSimTraversal.
  Variable G : execution.
  Variable WF : Wf G.
  Variable sc : relation actid.
  Variable IMMCON : imm_consistent G sc.

  (* Notation "'acts'" := (acts G). *)
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

Notation "'R_ex'" := (R_ex lab).
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

Inductive ext_isim_trav_step:
  thread_id -> (trav_label -> Prop) -> (trav_label -> Prop) -> Prop :=
  ext_fence_trav_step T T'
    f (FF : F f)
    (TS : ext_itrav_step
            G sc (mkTL ta_cover f) T T'
            (* (mkETC (mkTC (ecovered T ∪₁ eq f) (eissued T)) *)
            (*        (reserved T))) *)
            )            
    :
    ext_isim_trav_step
      (tid f) T T'

| ext_read_trav_step T T'
    r (RR : R r) (NRMW : ~ dom_rel rmw r)
    (TS : ext_itrav_step
            G sc (mkTL ta_cover r) T T'
            ) :
    ext_isim_trav_step
      (tid r) T T'

| ext_reserve_trav_step T T' w
    (TS : ext_itrav_step
            G sc (mkTL ta_reserve w) T T') :
    ext_isim_trav_step
      (tid w) T T'

| ext_rlx_write_promise_step T T'
    w (WW : W w) (NREL : ~ Rel w) (NISS : ~ issued T w)
    (TS : ext_itrav_step
            G sc (mkTL ta_issue w) T T'
            (* TODO: can this form of T' be deduced? *)
            (* (mkETC (mkTC (ecovered T) (eissued T ∪₁ eq w)) *)
            (*        (reserved T ∪₁ eq w ∪₁ *)
            (*         dom_sb_S_rfrmw G T rfi (eq w))) *)
    )
  :
    ext_isim_trav_step
      (tid w) T T'

| ext_rlx_write_cover_step T T'
    w (WW : W w) (NREL : ~ Rel w) (NRMW : ~ codom_rel rmw w)
    (ISS : issued T w)
    (TS : ext_itrav_step
            G sc (mkTL ta_cover w) T T'
            (* (mkETC (mkTC (ecovered T ∪₁ eq w) (eissued T)) *)
            (*        (reserved T)) *)
    ) :
    ext_isim_trav_step
      (tid w) T T'

| ext_rel_write_step T T' T''
    w (WW : W w) (REL : Rel w) (NRMW : ~ codom_rel rmw w)
    (NISS : ~ issued T w)
    (TS1 : ext_itrav_step
             G sc (mkTL ta_issue w) T T'
             (* (mkETC (mkTC (ecovered T) (eissued T ∪₁ eq w)) *)
             (*        (reserved T ∪₁ eq w ∪₁ *)
             (*         dom_sb_S_rfrmw G T rfi (eq w))) *)
    )
    (TS2 : ext_itrav_step
             G sc (mkTL ta_cover w) T' T''
             (* (mkETC (mkTC (ecovered T) (eissued T ∪₁ eq w)) *)
             (*        (reserved T ∪₁ eq w ∪₁ *)
             (*         dom_sb_S_rfrmw G T rfi (eq w))) *)
             (* (mkETC (mkTC (ecovered T ∪₁ eq w) (eissued T ∪₁ eq w)) *)
             (*        (reserved T ∪₁ eq w ∪₁ *)
             (*         dom_sb_S_rfrmw G T rfi (eq w))) *)
    ) :
    ext_isim_trav_step
      (tid w) T T''

| ext_rlx_rmw_cover_step T T' T''
    r w (RMW : rmw r w) (NREL : ~ Rel w) (ISS : issued T w)
    (TS1 : ext_itrav_step
             G sc (mkTL ta_cover r) T T'
             (* (mkETC (mkTC (ecovered T ∪₁ eq r) (eissued T)) *)
             (*        (reserved T)) *)
    )
    (TS2 : ext_itrav_step
             G sc (mkTL ta_cover w) T' T''
             (* (mkETC (mkTC (ecovered T ∪₁ eq r) (eissued T)) *)
             (*        (reserved T)) *)
             (* (mkETC (mkTC (ecovered T ∪₁ eq r ∪₁ eq w) (eissued T)) *)
             (*        (reserved T)) *)
    ):
    ext_isim_trav_step
      (tid r) T T''
| ext_rel_rmw_step T T' T'' T'''
    r w (RMW : rmw r w) (REL : Rel w) (NISS : ~ issued T w)
    (TS1 : ext_itrav_step
             G sc (mkTL ta_cover r) T T'
             (* (mkETC (mkTC (ecovered T ∪₁ eq r) (eissued T)) *)
             (*        (reserved T)) *)
    )
    (TS2 : ext_itrav_step
             G sc (mkTL ta_issue w) T' T''
             (* (mkETC (mkTC (ecovered T ∪₁ eq r) (eissued T)) *)
             (*        (reserved T)) *)
             (* (mkETC (mkTC (ecovered T ∪₁ eq r) (eissued T ∪₁ eq w)) *)
             (*        (reserved T ∪₁ eq w ∪₁ *)
                     (* dom_sb_S_rfrmw G T rfi (eq w))) *)
)
    (TS3 : ext_itrav_step
             G sc (mkTL ta_cover w) T'' T'''
             (* (mkETC (mkTC (ecovered T ∪₁ eq r) (eissued T ∪₁ eq w)) *)
             (*        (reserved T ∪₁ eq w ∪₁ *)
             (*         dom_sb_S_rfrmw G T rfi (eq w))) *)
             (* (mkETC (mkTC (ecovered T ∪₁ eq r ∪₁ eq w) (eissued T ∪₁ eq w)) *)
             (*        (reserved T ∪₁ eq w ∪₁ *)
             (*         dom_sb_S_rfrmw G T rfi (eq w))) *)
    ):
    ext_isim_trav_step
      (tid r) T T'''
      (* (mkETC (mkTC (ecovered T ∪₁ eq r ∪₁ eq w) (eissued T ∪₁ eq w)) *)
      (*        (reserved T ∪₁ eq w ∪₁ *)
      (*         dom_sb_S_rfrmw G T rfi (eq w))) *)
.

Definition ext_sim_trav_step T T' :=
  exists thread, ext_isim_trav_step thread T T'.

Section SimTravStepExistence.
  Variable (T T': trav_label -> Prop).
  Hypotheses (TS : ext_trav_step G sc T T'). 
  Hypotheses (TCOH: tls_coherent G T)
             (ICOH: iord_coherent G sc T)
             (RCOH: reserve_coherent G T). 
  Hypothesis (WFSC : wf_sc G sc).
  Hypotheses (RELCOV :  W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
             (RMWCOV : forall r w (RMW : rmw r w), covered T r <-> covered T w). 
  
  Lemma RMWRFI_ACQ_SB: (rmw ⨾ rfi)＊ ⨾ ⦗R ∩₁ Acq⦘ ⨾ sb ⊆ sb.
  Proof using WF. 
    arewrite_id ⦗R ∩₁ Acq⦘. rewrite seq_id_l.
    arewrite (rfi ⊆ sb). rewrite (rmw_in_sb WF).
    arewrite (sb ⨾ sb ⊆ sb).
    { generalize (@sb_trans G). clear. basic_solver 10. }
    rewrite <- ct_end. apply ct_of_trans. apply sb_trans. 
  Qed. 

  Lemma DRFE_EMP1: 
    forall w, dom_rel ((detour ∪ rfe) ⨾ rmw ⨾ ⦗dom_sb_S_rfrmw G T rfi (eq w)⦘) ≡₁ ∅.
  Proof using WF. 
    ins. split; [|clear; basic_solver].
    unfold Execution.detour, Execution.rfi, Execution.rfe, dom_sb_S_rfrmw.
    unfolder. ins. desf. 
    all: assert (z2 = z) by (eapply (wf_rmw_invf WF); eauto); subst.
    { assert (z3 = z0); subst; eauto.
      eapply (wf_rff WF); eauto. }
    assert (x = z0); subst; eauto.
    eapply (wf_rff WF); eauto. 
  Qed. 

  Lemma DRFE_EMP: 
    forall w,
      dom_rel ((detour ∪ rfe) ⨾ rmw ⨾ ⦗reserved T ∪₁ eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w)⦘) ≡₁
      dom_rel ((detour ∪ rfe) ⨾ rmw ⨾ ⦗reserved T ∪₁ eq w⦘).
  Proof using WF. 
    ins. rewrite id_union. rewrite !seq_union_r. rewrite dom_union.
    by rewrite DRFE_EMP1, set_union_empty_r. 
  Qed. 
  
  Lemma RED:
    forall w (EW : E w), reserved T ∪₁ eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w) ⊆₁ E.
  Proof using WF RCOH. 
    ins. rewrite (dom_sb_S_rfrmwE WF). erewrite rcoh_S_in_E; eauto.
    generalize EW. clear. basic_solver. 
  Qed. 

  Lemma RR: 
    forall w,
      dom_rel (sb ⨾ ⦗reserved T ∪₁ eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w)⦘) ≡₁
      dom_rel (sb ⨾ ⦗reserved T ∪₁ eq w⦘).
  Proof using. 
    ins. split; [|basic_solver 10].
    rewrite !id_union, !seq_union_r, !dom_union.
    unionL.
    1,2: basic_solver.
    unfold dom_sb_S_rfrmw. generalize (@sb_trans G).
    clear. basic_solver 10.
  Qed. 

  Lemma RR1:
    forall w, 
      dom_rel (rppo G ⨾ ⦗reserved T ∪₁ eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w)⦘) ≡₁
      dom_rel (rppo G ⨾ ⦗reserved T ∪₁ eq w⦘).
  Proof using WF TCOH RCOH. 
    split; [|basic_solver 10].
    rewrite !id_union, !seq_union_r, !dom_union.
    unionL.
    1,2: basic_solver.
    unfold dom_sb_S_rfrmw. generalize (rppo_sb_in_rppo WF).
    arewrite (⦗reserved T⦘ ⊆ ⦗W⦘ ⨾ ⦗reserved T⦘) at 1.
    { generalize (reservedW WF TCOH RCOH). clear. basic_solver. }
    clear. basic_solver 10.
  Qed. 

  Lemma RESRES:
    forall e (NISS : ~ issued T e)
      (WSBW : dom_rel (⦗W⦘ ⨾ sb ⨾ ⦗eq e⦘) ⊆₁ issued T),
      dom_rel (sb ⨾ ⦗reserved T ∪₁ eq e⦘) ∩₁
        codom_rel (⦗issued T ∪₁ eq e⦘ ⨾ rf ⨾ ⦗R_ex⦘ ⨾ rmw) ⊆₁
      reserved T ∪₁ eq e ∪₁ dom_sb_S_rfrmw G T rfi (eq e). 
  Proof using WF TCOH RCOH. 
    ins. rewrite id_union, !seq_union_r, dom_union.
    rewrite set_inter_union_l.
    unionL.
    2: { rewrite (dom_r (wf_rmwD WF)).
         rewrite <- !seqA. rewrite codom_eqv1.
         rewrite <- !set_interA. rewrite set_interC with (s':=W).
         rewrite <- !set_interA. rewrite <- dom_eqv1.
         rewrite WSBW. rewrite (rcoh_I_in_S RCOH). basic_solver. }
    rewrite id_union, !seq_union_l, codom_union.
    rewrite set_inter_union_r.
    unionL.
    { unionR left -> left.
      etransitivity; [|by eapply rcoh_sb_S; eauto].
      unfold dom_sb_S_rfrmw. by rewrite !seqA. }
    unionR right.
    unfold dom_sb_S_rfrmw.
    rewrite rfi_union_rfe.
    rewrite !seq_union_l, !seq_union_r, codom_union.
    rewrite set_inter_union_r.
    unionL.
    { arewrite_id ⦗R_ex⦘. by rewrite seq_id_l. }
    rewrite set_interC.
    arewrite (codom_rel (⦗eq e⦘ ⨾ rfe ⨾ ⦗R_ex⦘ ⨾ rmw) ∩₁ dom_rel (sb ⨾ ⦗reserved T⦘) ⊆₁ ∅).
    2: basic_solver.
    apply seq_codom_dom_inter_iff.
    split; [|clear; basic_solver].
    rewrite !seqA.
    arewrite (⦗reserved T⦘ ⊆ ⦗W⦘ ⨾ ⦗reserved T⦘).
    { generalize (reservedW WF TCOH RCOH). basic_solver. }
    rewrite (rmw_in_sb WF).
    arewrite (sb ⨾ sb ⊆ sb).
    { generalize (@sb_trans G). clear. basic_solver. }
    sin_rewrite R_ex_sb_W_in_rppo.
    arewrite (rfe ⨾ rppo G ⨾ ⦗reserved T⦘ ⊆ ⦗issued T⦘ ⨾ rfe ⨾ rppo G ⨾ ⦗reserved T⦘).
    2: { generalize NISS. clear. basic_solver. }
    apply dom_rel_helper_in.
    eapply dom_rfe_rppo_S_in_I; eauto.
  Qed.


  (* TODO: move *)
  Global Add Parametric Morphism: ar with signature
         eq ==> (@inclusion actid) ==> (@inclusion actid) as ar_mori. 
  Proof using. ins. now unfold ar; rewrite H. Qed.

  (* TODO: move *)
  Global Add Parametric Morphism : iord with signature
         eq ==> (@inclusion actid) ==> (@inclusion trav_label) as iord_mori. 
  Proof using. ins. iord_parts_unfolder. rewrite H. done. Qed.  

  (* TODO: move *)
  Global Add Parametric Morphism : coverable with signature
         eq ==> (@same_relation actid) ==> (@set_subset trav_label) ==>
            (@set_subset actid) as coverable_mori. 
  Proof using. ins. unfold coverable. rewrite H, H0. done. Qed. 

  (* TODO: move *)
  Global Add Parametric Morphism : issuable with signature
         eq ==> (@same_relation actid) ==> (@set_subset trav_label) ==>
            (@set_subset actid) as issuable_mori. 
  Proof using. ins. unfold issuable. rewrite H, H0. done. Qed. 
  
  (* TODO: move*)
  Lemma tls_coherent_ext_union T1 T2
        (TCOH1: tls_coherent G T1)
        (EXEC2: T2 ⊆₁ exec_tls G):
    tls_coherent G (T1 ∪₁ T2).
  Proof using. 
    destruct TCOH1. split; try basic_solver.
    apply set_subset_union_l. split; auto. basic_solver.
  Qed.         

  Lemma exists_ext_sim_trav_step_cover e
        (TS_COV: ext_itrav_step G sc (mkTL ta_cover e) T T'):
    exists T'', ext_sim_trav_step T T''.
  Proof using WFSC WF TCOH RMWCOV RELCOV RCOH IMMCON ICOH.
    (* TODO: make TS more concrete *)
    clear TS.
    inversion TS_COV.
    simpl in ets_upd.
    assert (eq ta_reserve <*> (∅: actid -> Prop) ≡₁ ∅) as NO.
    { rewrite set_pair_alt. basic_solver. }
    rewrite NO, set_union_empty_r in ets_upd. clear NO.

    assert (dom_rel (sb ⨾ ⦗eq e⦘) ⊆₁ covered T) as SBE.
    { ins. rewrite ets_upd in ets_iord_coh.
      forward eapply dom_sb_covered with (T := T'); eauto.
      { rewrite ets_upd. eauto. }
      rewrite ets_upd. simplify_tls_events. rewrite id_union, seq_union_r, dom_union.
      intros DSB'%set_subset_union_l%proj2.
      red. intros e' DSBe'. specialize (DSB' _ DSBe'). red in DSB'. des; auto.
      subst. destruct DSBe' as [? [SB ->]%seq_eqv_r].
      edestruct sb_irr; eauto. }

    assert (coverable G sc T e) as COVERABLEE.
    { eapply ext_itrav_step_cov_coverable; eauto. }

    assert (~ covered T e) as NCOV.
    { eapply ext_itrav_step_cov_next; eauto. }     

    destruct (lab_rwf lab e) as [RE|[WE|FE]].
    3: { eexists; eexists. eapply ext_fence_trav_step; eauto. }
    { destruct (classic (dom_rel rmw e)) as [RMW|NRMW].
      2: { eexists; eexists. eapply ext_read_trav_step; eauto. }
      destruct RMW as [w RMW].
      assert (~ covered T w) as COVW.
      { intros WCOV. apply NCOV.
        eapply dom_sb_covered; eauto.
        apply rmw_in_sb in RMW; eauto. basic_solver 10. }
      assert (is_w lab w) as WW.
      { apply (dom_r (wf_rmwD WF)) in RMW.
        apply seq_eqv_r in RMW. desf. }

      assert (~ is_init e) as NIr.
      { apply rmw_from_non_init, seq_eqv_l in RMW; eauto. by desc. } 

      assert (dom_rel (sb ⨾ ⦗eq w⦘) ⊆₁ covered T ∪₁ eq e) as SBW.
      { hahn_rewrite (rmw_from_non_init WF) in RMW.
        hahn_rewrite (wf_rmwi WF) in RMW.
        hahn_rewrite (sb_immediate_adjacent WF) in RMW.
        unfold adjacent in *; unfolder in *; ins; desf.
        apply LA_ca in H; desf; eauto. }

      assert (E e /\ E w) as [ER EW].
      { apply (wf_rmwE WF) in RMW.
        apply seq_eqv_lr in RMW. desf. }
      assert (W_ex w) as WEXW.
      { red. basic_solver. }
      assert (~ (covered T ∪₁ eq e) w) as C1.
      { intros [H|H]; desf. type_solver. }

      assert (~ is_init w) as NIw.
      { apply rmw_non_init_lr, seq_eqv_lr in RMW; eauto. by desc. }
      
      assert (dom_rel ((sb ∪ sc)^+ ⨾ ⦗eq w⦘) ⊆₁ covered T ∪₁ eq e) as SBSC. 
      { intros b [? [SBSC <-]%seq_eqv_r]. 
        apply ct_end in SBSC as [e' [SBSC' [SB' | SC']]]. des.
        2: { eapply wf_scD, seq_eqv_lr in SC'; eauto. type_solver. }
        forward eapply sb_transp_rmw with (x := e') (y := e) as SB''; eauto.
        { basic_solver. }
        assert ((sb ∪ sc)^* b e) as SBSC.
        { apply rt_cr. eexists. split; eauto.
          generalize SB''. basic_solver 10. }
        apply rtE in SBSC as [[->] | SBSC]; [by vauto| ]. 
        left. eapply dom_sb_sc_ct_coverable; eauto. basic_solver 10. }

      destruct (classic (issued T w)) as [ISS|NISS].
      { eexists; eexists. 
        eapply ext_rlx_rmw_cover_step with (T'' := T' ∪₁ eq (mkTL ta_cover w)); eauto.
        { intros REL. apply COVW. apply RELCOV.
          by split; [split|]. }
        split; eauto.
        { eapply tls_coherent_ext; eauto.
          red. basic_solver. } 
        { apply iord_coherent_extend; eauto.
          red. iord_dom_unfolder; symmetry in d0; inv d0.
          { apply ets_upd.
            forward eapply SBSC with (x := b) as [CB | ->]; eauto; [basic_solver 10| ..].
            { left. by apply tls_set_alt. }
            vauto. }
          { apply ets_upd. left. by apply tls_set_alt. }
          apply wf_rfD, seq_eqv_lr in d7; eauto. type_solver. }
        { eapply reserve_coherent_add_cover; eauto. }
        { intros [Tw | [=->]]%ets_upd.
          { apply COVW. eapply tls_set_alt; eauto. }
          destruct C1. by right. }
        { vauto. }
        simpl. rewrite set_pair_alt. basic_solver 10. }
      
      assert (dom_rel (⦗FW⦘ ⨾ sb ⨾ ⦗eq w⦘) ⊆₁ covered T) as FWSBW.
      { rewrite dom_eqv1. rewrite SBW. 
        arewrite (eq e ⊆₁ R) by basic_solver.
        type_solver. }

      assert (dom_rel (⦗W⦘ ⨾ sb ⨾ ⦗eq w⦘) ⊆₁ issued T) as WSBW.
      { rewrite <- seq_eqvK, !seqA, dom_eqv1.
        arewrite (W ⊆₁ FW) at 2. rewrite FWSBW.
        eapply w_covered_issued; eauto. }

      assert (dom_rel (rf ⨾ sb ⨾ ⦗eq w⦘) ⊆₁ issued T) as RFSB.
      { rewrite <- dom_rel_eqv_dom_rel. rewrite SBW.
        rewrite <- dom_rf_coverable with (sc := sc); eauto.
        rewrite covered_in_coverable; eauto. basic_solver. }

      assert (dom_rel (detour ⨾ sb ⨾ ⦗eq w⦘) ⊆₁ issued T) as AA'.
      { rewrite (dom_l (wf_detourD WF)), !seqA.
        rewrite detour_in_sb.
        arewrite (sb ⨾ sb ⊆ sb) by (generalize (@sb_trans G); basic_solver). }
      
      assert (dom_rel ((detour ∪ rfe) ⨾ sb ⨾ ⦗eq w⦘) ⊆₁ issued T) as AA.
      { rewrite !seq_union_l, dom_union. unionL; auto. by arewrite (rfe ⊆ rf). }
      
      assert (dom_rel ((detour ∪ rfe) ⨾ rmw ⨾
                       ⦗reserved T ∪₁ eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w)⦘) ⊆₁
              issued T ∪₁ eq w) as AAH.
      { unionR left. rewrite DRFE_EMP.
        rewrite id_union, !seq_union_r, dom_union.
        unionL; [eby eapply rcoh_rmw_S|]. by rewrite (rmw_in_sb WF). }

      assert (sb e w) as SBEW.
      { apply rmw_in_sb; auto. }
      assert (dom_rel (rf ⨾ ⦗eq e⦘) ⊆₁ issued T) as IRF.
      { rewrite dom_eqv_seq with (r':= sb ⨾ ⦗eq w⦘).
        2: { exists w. apply seq_eqv_r. split; auto. }
        arewrite_id ⦗eq e⦘. by rewrite seq_id_l. }

      assert (dom_rel ((detour ∪ rfe) ⨾ (data ∪ rfi ∪ rmw)＊ ⨾ rppo G ⨾ ⦗reserved T ∪₁ eq w⦘)
                      ⊆₁ issued T /\
              dom_rel (⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗reserved T ∪₁ eq w⦘) ⊆₁ issued T /\
              dom_rel ((detour ∪ rfe) ⨾ (rmw ⨾ rfi)＊ ⨾
                                      ⦗R ∩₁ Acq⦘ ⨾ sb ⨾ ⦗reserved T ∪₁ eq w⦘)
                      ⊆₁ issued T) as [PP0 [PP2 PP3]].
      { splits.
        all: rewrite id_union, !seq_union_r, dom_union; unionL.
        all: try by apply RCOH.
        { arewrite ((data ∪ rfi ∪ rmw)＊ ⨾ rppo G ⊆ sb); [|done].
          arewrite (rfi ⊆ sb). rewrite (rmw_in_sb WF).
          rewrite (data_in_sb WF), !unionK.
          rewrite rppo_in_sb.
          rewrite rt_of_trans.
          all: generalize (@sb_trans G); auto.
          basic_solver 10. }
        { arewrite (W_ex_acq ⊆₁ W); auto.
          rewrite (W_ex_in_W WF); basic_solver. }
        by sin_rewrite RMWRFI_ACQ_SB. }
      assert (dom_rel (⦗F ∩₁ Acq/Rel⦘ ⨾ sb ⨾ ⦗reserved T ∪₁ eq w⦘) ⊆₁
                      covered T) as PP5.
      { rewrite id_union, !seq_union_r, dom_union. unionL.
        { apply RCOH. }
        arewrite (F ∩₁ Acq/Rel ⊆₁ FW); [|done].
        type_solver. }

      assert (codom_rel (⦗issued T⦘ ⨾ rf ⨾ rmw) w) as [wprev RFRMW].
      { cdes IMMCON. red in Comp. specialize (Comp e).
        assert (E e /\ R e) as ERE by (by split).
        apply Comp in ERE. destruct ERE as [wprev ERE].
        exists wprev.
        apply seq_eqv_l. split.
        2: by exists e; split.
        eapply dom_rf_coverable; eauto. basic_solver 10. }

      assert (dom_sb_S_rfrmw G
                             (* (mkETC (etc_TC T) (reserved T ∪₁ eq w)) *)
                             (T ∪₁ eq (mkTL ta_reserve w))
                             (rf ⨾ ⦗R_ex⦘)
                             (issued T) ⊆₁ reserved T ∪₁ eq w) as DD.
      { rewrite dom_sb_S_rfrmw_union_P.
        erewrite rcoh_sb_S; eauto. 
        unfold dom_sb_S_rfrmw. simpls.
        simplify_tls_events.
        rewrite (dom_r (wf_rmwD WF)). rewrite !codom_seq, codom_eqv.
        rewrite SBW. rewrite set_inter_union_l.
        arewrite (eq e ∩₁ W ⊆₁ ∅) by type_solver.
        rewrite set_interC, w_covered_issued, rcoh_I_in_S; eauto. basic_solver. }

      destruct (classic (reserved T w)) as [RES|NRES].
      2: { eexists. red. eexists. 
           apply ext_reserve_trav_step with (w := w) (T' := T ∪₁ eq (mkTL ta_reserve w)).
           split.
           { eapply tls_coherent_ext; eauto.
             red. right. basic_solver 10. }
           { apply iord_coherent_extend; eauto.
             clear. red. rewrite iord_no_reserve. basic_solver. }
           { split; simplify_tls_events; eauto. 
             { rewrite rcoh_S_in_E; basic_solver. }
             { rewrite rcoh_I_in_S; basic_solver. }
             { rewrite set_minus_union_l.
               rewrite rcoh_S_I_in_W_ex; eauto. basic_solver. }
             { rewrite id_union, !seq_union_r, dom_union.
               unionL; [by apply RCOH|]. by rewrite (rmw_in_sb WF). }
             rewrite set_inter_union_l. unionL; [by apply RCOH|].
             generalize RFRMW. clear. basic_solver 10. } 
           { intros Rw. apply NRES. by apply tls_set_alt. }
           { vauto. }
           simpl. rewrite set_pair_alt. basic_solver. }      

      assert
      (dom_rel ((⦗W⦘ ⨾ (ar G sc ∪ rf ⨾ ppo ∩ same_loc)⁺) ⨾ ⦗eq w⦘) ⊆₁ issued T)
        as PP4.
      { rewrite ct_end.
        rewrite !seq_union_r, !seq_union_l, dom_union, !seqA.
        unionL.
        2: { arewrite (ppo ∩ same_loc ⊆ ppo) at 2.
             rewrite (ppo_in_sb WF) at 2.
             rewrite (dom_rel_helper RFSB).
             rewrite <- !seqA. do 3 rewrite dom_seq.
             rewrite !seqA.
               by apply ar_rf_ppo_loc_rt_I_in_I. }
        arewrite (⦗eq w⦘ ⊆ ⦗W⦘ ⨾ ⦗eq w⦘) by basic_solver.
        sin_rewrite ar_W_in_ar_int; auto.
        rewrite ar_int_in_sb; auto.
        arewrite (sb ⨾ ⦗eq w⦘ ⊆ ⦗coverable G sc T⦘ ⨾ sb ⨾ ⦗eq w⦘).
        { apply dom_rel_helper.
          rewrite SBW.
          rewrite covered_in_coverable; eauto.
          unionL; auto.
          red. by ins; subst. }
        rewrite <- !seqA. do 2 rewrite dom_seq. rewrite !seqA.
          by apply ar_rf_ppo_loc_rt_coverable_in_I. }
      
      assert (covered T ⊆₁ coverable G sc
                      (T ∪₁ eq (mkTL ta_issue w))
             )
        as COVCOV.
      { rewrite covered_in_coverable; eauto.
        apply coverable_mori; auto. basic_solver. }

      assert (let T''_ := T ∪₁ eq (mkTL ta_issue w) ∪₁ eq ta_reserve <*> (eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w)) in 
              forall dT'' (DT: dT'' ≡₁ ∅ /\ issuable G sc T w \/ dT'' ≡₁ eq (mkTL ta_cover e)),
                let T'' := T''_ ∪₁ dT'' in 
                 tls_coherent G T'' /\
                 iord_coherent G sc T'' /\
                 reserve_coherent G T'')
        as COHSTEP1.
      { intros. splits.
        2: { red. subst T'' T''_. 
             rewrite !id_union, !seq_union_r, !dom_union.
             repeat (apply set_subset_union_l; split).
             { red in ICOH. rewrite ICOH. basic_solver. }
             { destruct DT as [[DT ISS] | DT].
               { do 3 unionR left. by apply issuable_iord_dom_cond. }
               rewrite DT. 
               iord_dom_unfolder.
               2: { repeat left.
                    symmetry in d0. inv d0.
                    apply tls_set_alt. apply PP4. basic_solver 10. }
               symmetry in d0. inv d0.
               specialize (SBW b). specialize_full SBW.
               { eexists. apply seq_eqv_r. split; eauto.
                 by apply fwbob_in_sb. }
               destruct SBW; try by vauto. 
               repeat left. by apply tls_set_alt. }
             { iord_dom_solver. }
             destruct DT as [[-> _] | ->].
             { basic_solver. }
             do 3 unionR left. by apply coverable_iord_dom_cond. }
        { subst T'' T''_.
          rewrite !set_unionA. apply tls_coherent_ext_union; auto.
          repeat (apply set_subset_union_l; split).
          { apply set_subset_single_l. red. right. split; basic_solver. } 
          { unfold exec_tls. unionR right. apply set_pair_mori; [basic_solver| ].
            apply set_subset_inter_r. split.
            2: { rewrite dom_sb_S_rfrmwD; basic_solver. }
            rewrite set_minusE. apply set_subset_inter_r. split.
            { rewrite dom_sb_S_rfrmwE; basic_solver. }
            rewrite dom_sb_S_rfrmw_in_W_ex.
            unfold W_ex. rewrite rmw_non_init_lr; basic_solver. }
          destruct DT as [[-> _] | ->]; [done| ].
          apply set_subset_single_l. red. left.
          split; basic_solver. }

        assert (covered T'' ≡₁ covered T \/ covered T'' ≡₁ covered T ∪₁ eq e) as COV''.
        { subst T'' T''_. destruct DT as [[-> _] | ->]; [left | right];
            clear; by simplify_tls_events. }
        assert (issued T'' ≡₁ issued T ∪₁ eq w) as ISS''.
        { subst T'' T''_. destruct DT as [[-> _] | ->];
            clear; by simplify_tls_events. }
        assert (reserved T'' ≡₁ reserved T ∪₁ eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w)) as RES''.
        { subst T'' T''_. destruct DT as [[-> _] | ->];
            clear; simplify_tls_events; basic_solver. }
        
        split; rewrite ?ISS'', ?RES''.
        { rewrite rcoh_S_in_E, dom_sb_S_rfrmwE; eauto. basic_solver. }
        { rewrite rcoh_I_in_S; eauto. basic_solver. }
        { rewrite dom_sb_S_rfrmw_in_W_ex.
          generalize rcoh_S_I_in_W_ex. basic_solver 10. }
        { assert (covered T ⊆₁ covered T'') as <-.
          { destruct COV'' as [-> | ->]; basic_solver. }
          rewrite <- dom_rel_eqv_dom_rel. rewrite RR.
          by rewrite dom_rel_eqv_dom_rel. } 
        { rewrite <- seqA with (r3 := sb ⨾ _). rewrite <- seqA. 
          rewrite <- dom_rel_eqv_dom_rel. rewrite RR.
          rewrite dom_rel_eqv_dom_rel. rewrite !seqA, PP3. basic_solver. }
        { rewrite <- dom_rel_eqv_dom_rel. rewrite RR.
          rewrite dom_rel_eqv_dom_rel.
          rewrite PP2. basic_solver. }
        { subst T'' T''_.
          unfold dom_sb_S_rfrmw at 1. simplify_tls_events. 
          assert (reserved dT'' ≡₁ ∅) as ->; [| rewrite set_union_empty_r]. 
          { destruct DT as [[-> _] | ->] ; clear; by simplify_tls_events. }
          rewrite <- set_unionA. rewrite RR.
          rewrite seqA, RESRES; auto. } 
        { rewrite <- seqA with (r3 := rppo G ⨾ _).
          rewrite <- dom_rel_eqv_dom_rel. rewrite RR1.
          rewrite dom_rel_eqv_dom_rel.
          rewrite seqA, PP0. basic_solver. }
        { rewrite <- AAH. basic_solver 10. }
        rewrite !set_inter_union_l. 
        repeat (apply set_subset_union_l; split).
        { rewrite rcoh_S_W_ex_rfrmw_I; auto. basic_solver 10. }
        { generalize RFRMW. basic_solver 10. }
        unfold dom_sb_S_rfrmw. rewrite rfi_in_rf. basic_solver 10. }
              
      destruct (classic (Rel w)) as [REL|NREL].
      2: { assert (issuable G sc T w) as WISS.
           { red. unfold set_inter. splits; auto; red.
             exists (mkTL ta_issue w). splits; try by vauto. 
             clear -NREL SBW RE PP4. 
             red. iord_dom_unfolder.
             2: { symmetry in d0. inv d0.
                  apply tls_set_alt. apply PP4. basic_solver 10. } 
             symmetry in d0. inv d0.
             specialize (SBW b). specialize_full SBW.
             { apply fwbob_in_sb in d5. basic_solver 10. }
             destruct SBW as [? | ->]; [by apply tls_set_alt| ].
             red in d5. unfold union in d5. des.
             { apply seq_eqv_r in d5. mode_solver. }
             { apply seq_eqv_lr in d5. type_solver. }
             { apply seq_eqv_r in d5. type_solver. }
             apply seq_eqv_l in d5. type_solver. }
           
           eexists. eexists.
           specialize COHSTEP1 with (dT'' := ∅). 
           eapply ext_rlx_write_promise_step; eauto. 
           split.
           1-3: by apply COHSTEP1; vauto. 
           { intros ?. apply NISS. by apply tls_set_alt. }
           { ins. by apply tls_set_alt. }
           basic_solver. }

      eexists; eexists.
      specialize COHSTEP1 with (dT'' := eq (mkTL ta_cover e)).
      simpl in COHSTEP1. specialize_full COHSTEP1; [vauto| ]. desc.       
      eapply ext_rel_rmw_step with (T''' := T ∪₁ eq (mkTL ta_issue w)
     ∪₁ eq ta_reserve <*> (eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w))
     ∪₁ eq (mkTL ta_cover e) ∪₁ eq (mkTL ta_cover w)); eauto. 
      { split; eauto. 
        { intros ISS'%ets_upd.
          apply NISS, tls_set_alt. destruct ISS'; vauto. }
        { ins. apply ets_upd. left. by apply tls_set_alt. }
        rewrite ets_upd. simpl.
        rewrite dom_sb_S_rfrmw_union_P.
        unfold dom_sb_S_rfrmw at 3. simplify_tls_events.
        rewrite !set_pair_alt. basic_solver 10. }


      split.
      { eapply tls_coherent_ext; eauto. red. left. split; auto. basic_solver. }
      { apply iord_coherent_extend; auto.
        red. clear -WF WW WFSC RMW COVERABLEE TCOH SBSC.
        iord_dom_unfolder; symmetry in d0; inv d0; cycle 1. 
        { tauto. }
        { apply wf_rfD, seq_eqv_lr in d7; eauto. type_solver. }
        forward eapply SBSC with (x := b) as [CB | ->]; eauto; [basic_solver 10| ].
        repeat left. by apply tls_set_alt. }
      { eapply reserve_coherent_add_cover; eauto. } 
      { intros COV'. unfold set_union in COV'. des; try by inversion COV'. 
        { apply COVW. by apply tls_set_alt. }
        inversion COV'. type_solver. }
      { vauto. }
      simpl. rewrite !set_pair_alt. basic_solver 10. } 
    
    assert (E e) as EE by apply COVERABLEE. 
    assert (issued T e) as ISS.
    { eapply w_coverable_issued; eauto. basic_solver. }
    destruct (classic (Rel e)) as [REL|NREL].
    { exfalso. apply NCOV. apply RELCOV. split; [split|]; auto. }
    destruct (classic (codom_rel rmw e)) as [RMW|NRMW].
    2: { eexists. eexists. eapply ext_rlx_write_cover_step; eauto. }
    exfalso. apply NCOV.
    destruct RMW as [r RMW].
    apply (RMWCOV _ _ RMW). eapply SBE.
    eexists. apply seq_eqv_r. split; eauto.
    by apply (rmw_in_sb WF).    
Qed. 

Lemma exists_ext_sim_trav_step_issue e
      (TS_ISS: ext_itrav_step G sc (mkTL ta_issue e) T T'):
  exists T'', ext_sim_trav_step T T''.
Proof using WFSC WF TCOH RMWCOV RCOH IMMCON ICOH. 
  clear TS. inversion TS_ISS. simpl in ets_upd.

  assert (issued T' e) as ISS'.
  { eapply issued_more; [apply ets_upd| ]. clear. find_event_set. }
  assert (is_w lab e) as WW.
  { eapply issuedW; eauto. }
  assert (issuable G sc T e) as ISS.
  { eapply ext_itrav_step_iss_issuable; eauto. }

  assert (~ covered T e) as NCOV.
  { intros COVe. apply ets_new_ta. apply tls_set_alt.
    eapply w_covered_issued; eauto. basic_solver. }

  assert (~ issued T e) as NISS.
  { intros ?. apply ets_new_ta. by apply tls_set_alt. }

  destruct (classic (Rel e)) as [REL|NREL].
  2: { eexists; eexists. eapply ext_rlx_write_promise_step; eauto. }
  eexists; eexists.
  eapply ext_rel_write_step with (T'' := T' ∪₁ eq (mkTL ta_cover e)); eauto.
  { intros [r RMW]. apply NISS.
    eapply w_covered_issued; eauto. split; auto.
    apply (RMWCOV _ _ RMW).
    eapply fwbob_issuable_in_C; eauto.
    exists e. apply seq_eqv_r. split; eauto.
    red. repeat left. apply seq_eqv_r. split; [| basic_solver].
    by apply rmw_in_sb. }

  assert (dom_rel (sb ⨾ ⦗eq e⦘) ⊆₁ covered T) as SBE.
  { etransitivity.
    2: { apply fwbob_issuable_in_C; eauto. }
    rewrite <- sb_to_w_rel_in_fwbob.
    basic_solver 10. }
  
  assert (E e) as EE by apply ISS.
  
  assert (coverable G sc (T ∪₁ eq (mkTL ta_issue e)) e) as CCX.
  { red. split; auto. exists (mkTL ta_cover e). do 2 (split; try by vauto).
    clear -SBE WW WFSC TCOH ICOH WF.
    red. iord_dom_unfolder; symmetry in d0; inv d0; cycle 1. 
    { vauto. }
    { apply wf_rfD, seq_eqv_lr in d7; eauto. type_solver. }
    left. apply tls_set_alt.
    apply ct_end in d5 as [e' [SBSC' [SB' | SC']]].
    2: { eapply wf_scD, seq_eqv_lr in SC'; eauto. type_solver. }
    assert (covered T e') as COV'. 
    { apply SBE. basic_solver 10. }
    apply rtE in SBSC' as [[->] | SBSC']; [done| ]. 
    eapply dom_sb_sc_ct_covered; eauto. basic_solver 10. }

  assert (dom_rel (⦗W⦘ ⨾ sb ⨾ ⦗eq e⦘) ⊆₁ issued T) as WSBW.
  { rewrite dom_eqv1. rewrite SBE. eapply w_covered_issued; eauto. }

  assert (dom_rel (rf ⨾ sb ⨾ ⦗eq e⦘) ⊆₁ issued T) as RFSB.
  { etransitivity.
    2: { eapply dom_rf_covered; eauto. }
    rewrite <- dom_rel_eqv_dom_rel, SBE. done. }

  assert (dom_rel ((detour ∪ rfe) ⨾ sb ⨾ ⦗eq e⦘) ⊆₁ issued T) as DRFSB.
  { rewrite !seq_union_l, dom_union. unionL.
    2: by arewrite (rfe ⊆ rf).
    rewrite (dom_l (wf_detourD WF)), !seqA.
    rewrite detour_in_sb.
    arewrite (sb ⨾ sb ⊆ sb) by (generalize (@sb_trans G); basic_solver). }

  assert (dom_rel ((detour ∪ rfe) ⨾ rmw ⨾ ⦗reserved T ∪₁ eq e⦘) ⊆₁ issued T) as DRFSBE.
  { rewrite id_union, !seq_union_r, dom_union.
    unionL.
    { eby eapply rcoh_rmw_S. }
    by rewrite (rmw_in_sb WF). }

  assert (~ is_init e) as NIe.
  { intros INIT. destruct NCOV. eapply init_covered; eauto. basic_solver. }

  constructor.
  { apply tls_coherent_ext; eauto. red. left. split; auto. basic_solver 10. }
  { apply iord_coherent_extend; eauto.
    red. apply coverable_iord_dom_cond.
    eapply coverable_mori; [.. | apply CCX]; eauto.
    rewrite ets_upd. basic_solver. }
  { eapply reserve_coherent_add_cover; eauto. }
  { intros [[COV' | ?] | ?]%ets_upd. 
    { apply NCOV. by apply tls_set_alt. } 
    { discriminate. }
    simpl in H. by desc. }
  { vauto. }
  rewrite ets_upd. simpl. rewrite !set_pair_alt. basic_solver 10. 
Qed.   

Lemma exists_ext_sim_trav_step_reserve e
      (TS_RES: ext_itrav_step G sc (mkTL ta_reserve e) T T'):
  exists T'', ext_sim_trav_step T T''.
Proof using.  
  clear TS. inversion TS_RES. 
  eexists. eexists. eapply ext_reserve_trav_step.
  econstructor; eauto.  
Qed. 

Lemma exists_ext_sim_trav_step:
  exists T'', ext_sim_trav_step T T''.
Proof using WF IMMCON.
  (* destruct TS as [e TS]. *)
  inversion_clear TS as [[a e] TS_]. rename TS_ into TS. 
  (* cdes TS. *)
  inversion TS.
  (* desf. *)
  destruct a.
  { eapply exists_ext_sim_trav_step_cover; eauto. }
  { eapply exists_ext_sim_trav_step_issue; eauto. }
  { (* TODO: add propagation step in ext_sim_trav_step *)
    admit. }
  eapply exists_ext_sim_trav_step_reserve; eauto. 
Admitted. 

End SimTravStepExistence. 


Lemma ext_sim_trav_step_to_step T T' thread
      (TS : ext_isim_trav_step thread T T') :
  exists lbl T'', ext_itrav_step G sc lbl T T'' /\ tid (event lbl) = thread.
Proof using. destruct TS; eauto. Qed.

End ExtSimTraversal.
