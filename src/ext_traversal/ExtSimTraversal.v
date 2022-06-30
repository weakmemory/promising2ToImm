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
(* From imm Require Import TraversalConfig. *)
(* From imm Require Import TraversalConfigAlt. *)
(* From imm Require Import Traversal. *)
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


(* (* TODO: move; update proof of iord_coh_implies_iord_simpl_coh using this *) *)
(* Lemma iord_coh_implies_iord_simpl_coh_impl G sc tc S *)
(*       (WF: Wf G) *)
(*       (WFSC: wf_sc G sc) *)
(*       (ICOH: iord_coherent G sc tc) *)
(*       (TCOH: tls_coherent G tc) *)
(*       (* (S_E: S ⊆₁ event ↓₁ acts_set G) *) *)
(*       (S_TC: S ⊆₁ tc) *)
(*   : *)
(*   dom_rel (iord_simpl G sc ⨾ ⦗S⦘) ⊆₁ tc. *)
(*   (* dom_rel (sb ⨾ ⦗eq e⦘) ⊆₁ tc.  *) *)
(* Proof using. *)
(*   rewrite set_split_complete with (s' := dom_rel _) (s := event ↓₁ is_init). *)
(*   forward eapply iord_simpl_tc_doma_impl with (S := S) as IS_DOM%doma_rewrite; eauto. *)
(*   { rewrite S_TC, tlsc_E; eauto. } *)
  
(*   apply set_subset_union_l. split. *)
(*   { rewrite IS_DOM. *)
(*     destruct TCOH. rewrite <- tls_coh_init. unfold init_tls. *)
(*     (* TODO: remove set_map_inter from AuxRel *) *)
(*     rewrite set_pair_alt. rewrite HahnSets.set_map_inter. *)
(*     rewrite <- set_interA. apply set_subset_inter; [| reflexivity]. *)
(*     rewrite dom_eqv1, set_interC. apply set_subset_inter; [| reflexivity]. *)
(*     unfold iord_simpl. unfold SB, RF, FWBOB, AR, IPROP, PROP. *)
(*     basic_solver 10. } *)
  
(*   rewrite set_interC, <- dom_eqv1. *)
(*   red in ICOH. rewrite <- ICOH. apply dom_rel_mori. *)
(*   unfold iord. fold (iord_simpl G sc). *)
(*   rewrite restr_relE. rewrite !seqA, seq_eqvC. *)
(*   rewrite set_minusE, HahnSets.set_map_inter, id_inter. *)
(*   rewrite !seqA, seq_eqvC. *)
(*   rewrite <- seqA with (r3 := ⦗_⦘ ⨾ ⦗_⦘). rewrite <- seqA with (r2 := _ ⨾ ⦗tc⦘). *)
(*   rewrite set_compl_set_mapC. *)
(*   etransitivity. *)
(*   2: { apply seq_mori; [reflexivity| ]. *)
(*        rewrite <- id_inter. apply domb_rewrite. *)
(*        fold (iord_simpl G sc). rewrite iord_simpl_E_E; auto. *)
(*        rewrite crE, map_rel_union. repeat case_union _ _. apply union_domb. *)
(*        { rewrite (@tlsc_E G tc) at 1; eauto. *)
(*          unfolder. ins. desc. split; congruence. } *)
(*        basic_solver. } *)
(*   rewrite IS_DOM, S_TC. basic_solver. *)
(* Qed. *)

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
  Lemma dom_rel_iord_parts_singleton
        (a1 a2: trav_action) (e: actid) (r: relation actid)
        (ENIe: (E \₁ is_init) e)
        (R_IORD: ⦗action ↓₁ eq a1⦘ ⨾ event ↓ r ⨾ ⦗action ↓₁ eq a2⦘
                 ⊆ iord_simpl G sc)
        (ICOH': iord_coherent G sc (T ∪₁ eq (mkTL a2 e))):
    dom_rel (r ⨾ ⦗eq e⦘) ⊆₁ event ↑₁ (T ∩₁ action ↓₁ eq a1).
  Proof using.
    arewrite (eq e ⊆₁ event ↑₁ (action ↓₁ eq a2 ∩₁ event ↓₁ eq e)).
    { red. ins. exists (mkTL a2 x). vauto. }
    eapply dom_rel_collect_event with (b := a1).
    apply set_subset_inter_r. split; [| basic_solver].
    arewrite (action ↓₁ eq a2 ∩₁ event ↓₁ eq e ⊆₁ action ↓₁ eq a2 ∩₁ eq (mkTL a2 e)).
    { unfolder. ins. destruct x; ins; desc; vauto. }
  Abort. 
    (* rewrite id_inter. sin_rewrite R_IORD. *)
  (*   apply iord_coh_implies_iord_simpl_coh_impl with (S := eq (mkTL a2 e)) in ICOH'; eauto. *)
  (*   2: { admit. } *)
  (*   2: { admit. } *)
  (*   2: { basic_solver. } *)

  (*   red in ICOH'. *)
  (*   etransitivity. *)
  (*   { eapply iord_coherent_element_prefix; eauto. *)
  (*   apply iord_coherent_ *)
  (*   eapply iord_coh_implies_iord_simpl_coh in ICOH'; eauto. *)

  (*   fold *)
  (*   eapply iord_coherent_extend_singleton; eauto. *)
  (*   eapply iord_coh_implies_iord_simpl_coh'; eauto. *)
  (* Qed. *)

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
  Proof using.
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
         (* eapply ext_itrav_step_more. *)
         (* 4: by eauto. *)
         (* { done. } *)
         (* { apply same_ext_trav_config_refl. } *)
         (* red. unfold ecovered, eissued in *; simpls. *)
         (* rewrite COVEQ, ISSEQ, RESEQ. eauto. } *)
    { destruct (classic (dom_rel rmw e)) as [RMW|NRMW].
      2: { eexists; eexists. eapply ext_read_trav_step; eauto. }
           (* eapply ext_itrav_step_more. *)
           (* 4: by eauto. *)
           (* { done. } *)
           (* { apply same_ext_trav_config_refl. } *)
           (* red. unfold ecovered, eissued in *; simpls. *)
           (* rewrite COVEQ, ISSEQ, RESEQ. eauto. } *)
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

      (* assert (ext_itrav_step *)
      (*           G sc e T *)
      (*           (mkETC (mkTC (ecovered T ∪₁ eq e) (eissued T)) *)
      (*                  (reserved T))) as ST1. *)
      (* { red. splits; eauto. *)
      (*   eapply etc_coherent_more; eauto. *)
      (*   red. unfold ecovered, eissued in *. simpls. *)
      (*   splits; by symmetry. } *)

      assert (~ is_init w) as NIw.
      { apply rmw_non_init_lr, seq_eqv_lr in RMW; eauto. by desc. }

      
      destruct (classic (issued T w)) as [ISS|NISS].
      { eexists; eexists. 
        eapply ext_rlx_rmw_cover_step with (T'' := T' ∪₁ eq (mkTL ta_cover w)); eauto.
        { intros REL. apply COVW. apply RELCOV.
          by split; [split|]. }
        split; eauto.
        { eapply tls_coherent_ext; eauto.
          red. basic_solver. } 
        { apply iord_coherent_extend; eauto.
          red.
          iord_parts_unfolder.  
          admit. }
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
              (* dom_rel (⦗W_ex⦘ ⨾ sb ⨾ ⦗reserved T ∪₁ eq w⦘) ⊆₁ reserved T /\ *)
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
(*         { rewrite <- etc_I_in_S; eauto; rewrite (W_ex_in_W WF); auto. } *)
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
                      (* (mkTC (covered (etc_TC T)) (issued (etc_TC T) ∪₁ eq w))*)
                      (T ∪₁ eq (mkTL ta_issue w))
             )
        as COVCOV.
      { rewrite covered_in_coverable; eauto.
        apply coverable_mori; auto. basic_solver. }

      (* assert (forall C' *)
      (*           (CC : (C' = covered T /\ issuable G sc T w) \/ *)
      (*                   C' = covered T ∪₁ eq e), *)

      (*   (* etc_coherent G sc *) *)
      (*   (*              (mkETC (mkTC C' (issued (etc_TC T) ∪₁ eq w)) *) *)
      (*   (*                     (reserved T ∪₁ eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w))) *) *)

      (*          forall T'' (COV'': covered T'' ≡₁ C') *)
      (*            (ISS'': issued T'' ≡₁ issued T ∪₁ eq w) *)
      (*            (RES'': reserved T'' ≡₁ reserved T ∪₁ eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w)), *)
                 
      (*            tls_coherent G T'' /\ *)
      (*            iord_coherent G sc T'' /\ *)
      (*            reserve_coherent G T'') *)
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
        { foobar. 
          etransitivity.
          { rewrite DRFE_EMP. 
            

        

        constructor; unfold eissued, ecovered; simpls.
        { red. splits; simpls.
          { desf; [|unionR left]; apply ETCCOH. }
          { desf. unionL.
            { etransitivity.
              2: eapply traversal_mon.
              { apply ETCCOH. }
              all: basic_solver. }
            intros x HH; subst.
            red; simpls. split.
            { split; auto.
              red. rewrite SBE. eauto with hahn. }
            left. right. split; auto.
            red. rewrite IRF. eauto with hahn. }
          desf.
          { etransitivity.
            2: { eapply traversal_mon with (T:=etc_TC T); basic_solver. }
            unionL; auto; [apply ETCCOH|basic_solver]. }
          unionL.
          { etransitivity.
            2: eapply traversal_mon.
            { apply ETCCOH. }
            all: basic_solver. }
          intros x HH; subst.
          red; simpls. unfold set_inter. splits; auto; red.
          { by rewrite fwbob_in_sb. }
          rewrite PP4. eauto with hahn. }
        { by apply RED. }
        { rewrite (etc_I_in_S ETCCOH). clear. basic_solver. }
        { rewrite dom_sb_S_rfrmw_in_W_ex.
          rewrite !set_minus_union_l. unionL.
          2,3: basic_solver.
          generalize (etc_S_I_in_W_ex ETCCOH). clear. unfold eissued. basic_solver 10. }
        { desf; try unionR left.
          all: by rewrite dom_eqv1; rewrite RR; rewrite <- dom_eqv1. }
        2: by rewrite dom_eqv1; rewrite RR; rewrite <- dom_eqv1; try unionR left.
        { do 2 rewrite <- seqA. rewrite <- dom_rel_eqv_dom_rel, RR.
          rewrite dom_rel_eqv_dom_rel, !seqA. by unionR left. }
        { unfold dom_sb_S_rfrmw. simpls.
          rewrite RR. rewrite seqA. by apply RESRES. }
        { rewrite <- seqA. rewrite <- dom_rel_eqv_dom_rel, RR1.
          rewrite dom_rel_eqv_dom_rel, seqA. by unionR left. }
        { by arewrite (detour ⊆ detour ∪ rfe). }
        rewrite !set_inter_union_l. unionL.
        { rewrite (etc_S_W_ex_rfrmw_I ETCCOH). clear. basic_solver 10. }
        { generalize RFRMW. clear. basic_solver 10. }
        unfold dom_sb_S_rfrmw. arewrite (rfi ⊆ rf). basic_solver 10. }

      destruct (classic (Rel w)) as [REL|NREL].
      2: { assert (issuable G sc (etc_TC T) w) as WISS.
           { red. unfold set_inter. splits; auto; red.
             arewrite
               (fwbob ⨾ ⦗eq w⦘ ⊆
                      (⦗W ∩₁ Rel⦘ ⨾ sb ∩ same_loc ⨾ ⦗W⦘ ∪ ⦗F ∩₁ Acq/Rel⦘ ⨾ sb) ⨾ ⦗eq w⦘).
             { unfold imm_bob.fwbob. rewrite !seq_union_l, !seqA.
               unionL; eauto 10 with hahn.
               all: type_solver. }
             arewrite ((⦗W ∩₁ Rel⦘ ⨾ sb ∩ same_loc ⨾ ⦗W⦘ ∪ ⦗F ∩₁ Acq/Rel⦘ ⨾ sb) ⊆ ⦗FW⦘ ⨾ sb).
             2: done.
             basic_solver. }
           eexists; eexists.
           eapply ext_rlx_write_promise_step; eauto.
           red. unfold ecovered, eissued in *.
           splits; eauto 10; simpls. }

      eexists; eexists.
      eapply ext_rel_rmw_step; eauto.
      { red. unfold ecovered, eissued; simpls; splits.
        { right. left. splits; auto. }
        eapply COHSTEP1. eauto. }
      red; unfold ecovered, eissued; simpls.
      splits; eauto.
      constructor; unfold eissued, ecovered; simpls.
      { red. simpls; splits.
        { unionR left -> left. apply ETCCOH. }
        { unionL.
          { etransitivity.
            2: eapply traversal_mon.
            { apply ETCCOH. }
            all: basic_solver. }
          all: intros x HH; subst.
          all: red; simpls; split; [split; auto; red|].
          { rewrite SBE. eauto with hahn. }
          { left. right. split; auto.
            red. rewrite IRF. eauto with hahn. }
          { rewrite SBW. eauto with hahn. }
          do 2 left. split; auto. by right. }
        unionL.
        { etransitivity.
          2: eapply traversal_mon.
          { apply ETCCOH. }
          all: basic_solver. }
        intros x HH; subst.
        red; simpls. unfold set_inter. splits; auto; red.
        { rewrite fwbob_in_sb. rewrite SBW. eauto with hahn. }
        rewrite PP4. eauto with hahn. }
      { by apply RED. }
      { rewrite (etc_I_in_S ETCCOH). clear. basic_solver. }
      { rewrite dom_sb_S_rfrmw_in_W_ex.
        rewrite !set_minus_union_l. unionL.
        2,3: basic_solver.
        generalize (etc_S_I_in_W_ex ETCCOH). clear. unfold eissued. basic_solver 10. }
      { unionR left -> left.
        all: by rewrite dom_eqv1; rewrite RR; rewrite <- dom_eqv1. }
      2: by rewrite dom_eqv1; rewrite RR; rewrite <- dom_eqv1; try unionR left.
      { do 2 rewrite <- seqA. rewrite <- dom_rel_eqv_dom_rel, RR.
        rewrite dom_rel_eqv_dom_rel, !seqA. by unionR left. }
      { unfold dom_sb_S_rfrmw. simpls.
        rewrite RR. rewrite !seqA. by apply RESRES. }
      { rewrite <- seqA. rewrite <- dom_rel_eqv_dom_rel, RR1.
        rewrite dom_rel_eqv_dom_rel, seqA. by unionR left. }
      { by arewrite (detour ⊆ detour ∪ rfe). }
      rewrite !set_inter_union_l. unionL.
      { rewrite (etc_S_W_ex_rfrmw_I ETCCOH). clear. basic_solver 10. }
      { generalize RFRMW. clear. basic_solver 10. }
      unfold dom_sb_S_rfrmw. arewrite (rfi ⊆ rf). basic_solver 10. }

    assert (E e) as EE.
    { eapply tc_C_in_E.
      2: { apply COVEQ. basic_solver. }
      eauto. }
    assert (eissued T e) as ISS.
    { apply ISSEQ. eapply tc_W_C_in_I; eauto.
      split; auto. apply COVEQ. basic_solver. }
    assert (coverable G sc (etc_TC T) e) as COVERE.
    { red. unfold set_inter. splits; auto.
      do 2 left. split; auto. }
    destruct (classic (Rel e)) as [REL|NREL].
    { exfalso. apply NCOV. apply RELCOV. split; [split|]; auto. }
    destruct (classic (codom_rel rmw e)) as [RMW|NRMW].
    2: { eexists. eexists. eapply ext_rlx_write_cover_step; eauto.
         eapply ext_itrav_step_more.
         4: by eauto.
         { done. }
         { apply same_etc_Reflexive. }
         red. rewrite COVEQ. rewrite ISSEQ. splits; simpls. by symmetry. }
    exfalso. apply NCOV.
    destruct RMW as [r RMW].
    apply (RMWCOV _ _ RMW). eapply SBE.
    eexists. apply seq_eqv_r. split; eauto.
      by apply (rmw_in_sb WF).    

Lemma exists_ext_sim_trav_step:
  exists T'', ext_sim_trav_step T T''.
Proof using WF IMMCON.
  (* destruct TS as [e TS]. *)
  inversion_clear TS as [[a e] TS_]. rename TS_ into TS. 
  (* cdes TS. *)
  inversion TS.
  (* desf. *)
  destruct a.
  3: {
    (* TODO: add propagation step in ext_sim_trav_step *)
    admit. }
  3: { eexists. eexists. eapply ext_reserve_trav_step.
       econstructor; eauto. }

  { assert (dom_rel (sb ⨾ ⦗eq e⦘) ⊆₁ covered (etc_TC T)) as SBE.
    { set (AA:=TCCOHalt').
      apply tc_sb_C in AA.
      unfold ecovered in *. rewrite COVEQ in AA.
      rewrite id_union in AA. rewrite seq_union_r in AA.
      rewrite dom_union in AA.
      apply set_subset_union_l in AA. destruct AA as [_ AA].
      clear -AA. unfolder in *. ins. desf.
      edestruct AA.
      { eauto. }
      { done. }
      subst. exfalso. eapply sb_irr; eauto. }

    assert (coverable G sc (etc_TC T) e) as COVERABLEE.
    { eapply coverable_add_eq_iff; eauto.
      apply covered_in_coverable.
      2: basic_solver.
      eapply tc_coherent_more.
      2: by apply TCCOH'.
      red. simpls. unfold eissued, ecovered in *. by split; symmetry. }

    destruct (lab_rwf lab e) as [RE|[WE|FE]].
    3: { eexists; eexists. eapply ext_fence_trav_step; eauto.
         eapply ext_itrav_step_more.
         4: by eauto.
         { done. }
         { apply same_ext_trav_config_refl. }
         red. unfold ecovered, eissued in *; simpls.
         rewrite COVEQ, ISSEQ, RESEQ. eauto. }
    { destruct (classic (dom_rel rmw e)) as [RMW|NRMW].
      2: { eexists; eexists. eapply ext_read_trav_step; eauto.
           eapply ext_itrav_step_more.
           4: by eauto.
           { done. }
           { apply same_ext_trav_config_refl. }
           red. unfold ecovered, eissued in *; simpls.
           rewrite COVEQ, ISSEQ, RESEQ. eauto. }
      destruct RMW as [w RMW].
      assert (~ ecovered T w) as COVW.
      { intros WCOV. apply NCOV. apply ETCCOH in WCOV.
        apply WCOV. eexists. apply seq_eqv_r. split; eauto.
          by apply rmw_in_sb. }
      assert (is_w lab w) as WW.
      { apply (dom_r (wf_rmwD WF)) in RMW.
        apply seq_eqv_r in RMW. desf. }

      assert (dom_rel (sb ⨾ ⦗eq w⦘) ⊆₁ ecovered T ∪₁ eq e) as SBW.
      { hahn_rewrite (rmw_from_non_init WF) in RMW.
        hahn_rewrite (wf_rmwi WF) in RMW.
        hahn_rewrite (sb_immediate_adjacent WF) in RMW.
        unfold adjacent in *; unfolder in *; ins; desf.
        apply LA_ca in H; desf; eauto.
        eapply tc_sb_C with (T:=mkTC (ecovered T ∪₁ eq e) (eissued T)).
        2: by unfolder; ins; eauto 10.
        eapply tc_coherent_implies_tc_coherent_alt; eauto.
        eapply tc_coherent_more.
        2: by apply ETCCOH'.
        destruct T'; simpls. }

      assert (E e /\ E w) as [ER EW].
      { apply (wf_rmwE WF) in RMW.
        apply seq_eqv_lr in RMW. desf. }
      assert (W_ex w) as WEXW.
      { red. basic_solver. }
      assert (~ (ecovered T ∪₁ eq e) w) as C1.
      { intros [H|H]; desf. type_solver. }

      assert (ext_itrav_step
                G sc e T
                (mkETC (mkTC (ecovered T ∪₁ eq e) (eissued T))
                       (reserved T))) as ST1.
      { red. splits; eauto.
        eapply etc_coherent_more; eauto.
        red. unfold ecovered, eissued in *. simpls.
        splits; by symmetry. }

      destruct (classic (eissued T w)) as [ISS|NISS].
      { eexists; eexists.
        eapply ext_rlx_rmw_cover_step; eauto.
        { intros REL. apply COVW. apply RELCOV.
            by split; [split|]. }
        red. splits; eauto.
        (* TODO: introduce a lemma. *)
        constructor; unfold ecovered, eissued; simpls.
        all: try apply ETCCOH.
        2: by unionR left -> left; apply ETCCOH.
        eapply trav_step_coherence.
        2: apply ETCCOH'.
        red. exists w.
        red. unnw. left; simpls.
        rewrite COVEQ, ISSEQ.
        unfold ecovered, eissued in *.
        splits; simpls.
        { intros HH. apply COVEQ in HH. red in HH. desf. }
        red. split; [split|]; auto.
        { red. by rewrite COVEQ. }
        do 2 left. split.
        2: by apply ISSEQ.
        eapply issuedW with (T:=etc_TC T); eauto. }

      assert (dom_rel (⦗FW⦘ ⨾ sb ⨾ ⦗eq w⦘) ⊆₁ covered (etc_TC T)) as FWSBW.
      { rewrite dom_eqv1. rewrite SBW; unfold ecovered.
        arewrite (eq e ⊆₁ R) by basic_solver.
        type_solver. }

      assert (dom_rel (⦗W⦘ ⨾ sb ⨾ ⦗eq w⦘) ⊆₁ issued (etc_TC T)) as WSBW.
      { rewrite <- seq_eqvK, !seqA, dom_eqv1.
        arewrite (W ⊆₁ FW) at 2. rewrite FWSBW.
        rewrite set_interC. eapply tc_W_C_in_I; eauto. }

      assert (dom_rel (rf ⨾ sb ⨾ ⦗eq w⦘) ⊆₁ issued (etc_TC T)) as RFSB.
      { rewrite <- ISSEQ.
        etransitivity.
        2: eapply tc_rf_C; eauto.
        unfolder. ins. desf.
        eexists. splits; eauto.
        eapply COVEQ. apply SBW. basic_solver 10. }

      assert (dom_rel (detour ⨾ sb ⨾ ⦗eq w⦘) ⊆₁ issued (etc_TC T)) as AA'.
      { rewrite (dom_l (wf_detourD WF)), !seqA.
        rewrite detour_in_sb.
        arewrite (sb ⨾ sb ⊆ sb) by (generalize (@sb_trans G); basic_solver). }
      
      assert (dom_rel ((detour ∪ rfe) ⨾ sb ⨾ ⦗eq w⦘) ⊆₁ issued (etc_TC T)) as AA.
      { rewrite !seq_union_l, dom_union. unionL; auto. by arewrite (rfe ⊆ rf). }
      
      assert (dom_rel ((detour ∪ rfe) ⨾ rmw ⨾
                       ⦗reserved T ∪₁ eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w)⦘) ⊆₁
              issued (etc_TC T) ∪₁ eq w) as AAH.
      { unionR left. rewrite DRFE_EMP.
        rewrite id_union, !seq_union_r, dom_union.
        unionL; [eby eapply etc_rmw_S|]. by rewrite (rmw_in_sb WF). }

      assert (sb e w) as SBEW.
      { apply rmw_in_sb; auto. }
      assert (dom_rel (rf ⨾ ⦗eq e⦘) ⊆₁ issued (etc_TC T)) as IRF.
      { rewrite dom_eqv_seq with (r':= sb ⨾ ⦗eq w⦘).
        2: { exists w. apply seq_eqv_r. split; auto. }
        arewrite_id ⦗eq e⦘. by rewrite seq_id_l. }

      assert (dom_rel ((detour ∪ rfe) ⨾ (data ∪ rfi ∪ rmw)＊ ⨾ rppo G ⨾ ⦗reserved T ∪₁ eq w⦘)
                      ⊆₁ issued (etc_TC T) /\
              (* dom_rel (⦗W_ex⦘ ⨾ sb ⨾ ⦗reserved T ∪₁ eq w⦘) ⊆₁ reserved T /\ *)
              dom_rel (⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗reserved T ∪₁ eq w⦘) ⊆₁ issued (etc_TC T) /\
              dom_rel ((detour ∪ rfe) ⨾ (rmw ⨾ rfi)＊ ⨾
                                      ⦗R ∩₁ Acq⦘ ⨾ sb ⨾ ⦗reserved T ∪₁ eq w⦘)
                      ⊆₁ issued (etc_TC T)) as [PP0 [PP2 PP3]].
      { splits.
        all: rewrite id_union, !seq_union_r, dom_union; unionL.
        all: try by apply ETCCOH.
        { arewrite ((data ∪ rfi ∪ rmw)＊ ⨾ rppo G ⊆ sb); [|done].
          arewrite (rfi ⊆ sb). rewrite (rmw_in_sb WF).
          rewrite (data_in_sb WF), !unionK.
          rewrite rppo_in_sb.
          rewrite rt_of_trans.
          all: generalize (@sb_trans G); auto.
          basic_solver 10. }
(*         { rewrite <- etc_I_in_S; eauto; rewrite (W_ex_in_W WF); auto. } *)
        { arewrite (W_ex_acq ⊆₁ W); auto.
          rewrite (W_ex_in_W WF); basic_solver. }
          by sin_rewrite RMWRFI_ACQ_SB. }
      assert (dom_rel (⦗F ∩₁ Acq/Rel⦘ ⨾ sb ⨾ ⦗reserved T ∪₁ eq w⦘) ⊆₁
                      covered (etc_TC T)) as PP5.
      { rewrite id_union, !seq_union_r, dom_union. unionL.
        { apply ETCCOH. }
        arewrite (F ∩₁ Acq/Rel ⊆₁ FW); [|done].
        type_solver. }

      assert (codom_rel (⦗issued (etc_TC T)⦘ ⨾ rf ⨾ rmw) w) as [wprev RFRMW].
      { cdes IMMCON. red in Comp. specialize (Comp e).
        assert (E e /\ R e) as ERE by (by split).
        apply Comp in ERE. destruct ERE as [wprev ERE].
        exists wprev.
        apply seq_eqv_l. split.
        2: by exists e; split.
        apply ISSEQ.
        eapply tc_rf_C with (T:=etc_TC T').
        { eapply tc_coherent_implies_tc_coherent_alt; eauto. }
        eexists. apply seq_eqv_r. split; eauto.
        apply COVEQ. by right. }

      assert (dom_sb_S_rfrmw G (mkETC (etc_TC T) (reserved T ∪₁ eq w)) (rf ⨾ ⦗R_ex⦘)
                             (issued (etc_TC T)) ⊆₁ reserved T ∪₁ eq w) as DD.
      { unfold dom_sb_S_rfrmw. simpls.
        rewrite id_union, !seq_union_r, dom_union.
        rewrite set_inter_union_l.
        rewrite (etc_sb_S ETCCOH).
        unionL; [basic_solver|].
        rewrite (dom_r (wf_rmwD WF)).
        rewrite <- !seqA. rewrite codom_eqv1.
        rewrite <- !set_interA. rewrite set_interC with (s':=W).
        rewrite <- !set_interA. rewrite <- dom_eqv1.
        rewrite WSBW. rewrite (etc_I_in_S ETCCOH). basic_solver. }

      destruct (classic (reserved T w)) as [RES|NRES].
      2: { eexists. red. eexists.
           apply ext_reserve_trav_step.
           red. splits.
           { do 2 right. splits; eauto. }
           constructor; auto.
           all: unfold eissued, ecovered; simpls.
           { unionL; [by apply ETCCOH|]. basic_solver. }
           { rewrite (etc_I_in_S ETCCOH). eauto with hahn. }
           { rewrite set_minus_union_l. rewrite (etc_S_I_in_W_ex ETCCOH).
             basic_solver. }
           { rewrite id_union, !seq_union_r, dom_union.
             unionL; [by apply ETCCOH|]. by rewrite (rmw_in_sb WF). }
           rewrite set_inter_union_l. unionL; [by apply ETCCOH|].
           generalize RFRMW. clear. basic_solver 10. }

      assert
      (dom_rel ((⦗W⦘ ⨾ (ar G sc ∪ rf ⨾ ppo ∩ same_loc)⁺) ⨾ ⦗eq w⦘) ⊆₁ issued (etc_TC T))
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
        arewrite (sb ⨾ ⦗eq w⦘ ⊆ ⦗coverable G sc (etc_TC T)⦘ ⨾ sb ⨾ ⦗eq w⦘).
        { apply dom_rel_helper.
          rewrite SBW.
          unfold ecovered. rewrite covered_in_coverable; eauto.
          unionL; auto.
          red. by ins; subst. }
        rewrite <- !seqA. do 2 rewrite dom_seq. rewrite !seqA.
          by apply ar_rf_ppo_loc_rt_coverable_in_I. }
      
      assert (covered (etc_TC T) ⊆₁ coverable G sc (mkTC (covered (etc_TC T))
                                                         (issued (etc_TC T) ∪₁ eq w)))
        as COVCOV.
      { etransitivity.
        2: { eapply traversal_mon with (T:=etc_TC T); basic_solver. }
        apply ETCCOH. }

      assert (forall C' (CC : (C' = covered (etc_TC T) /\ issuable G sc (etc_TC T) w) \/
                              C' = covered (etc_TC T) ∪₁ eq e),
        etc_coherent G sc
                     (mkETC (mkTC C' (issued (etc_TC T) ∪₁ eq w))
                            (reserved T ∪₁ eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w))))
        as COHSTEP1.
      { constructor; unfold eissued, ecovered; simpls.
        { red. splits; simpls.
          { desf; [|unionR left]; apply ETCCOH. }
          { desf. unionL.
            { etransitivity.
              2: eapply traversal_mon.
              { apply ETCCOH. }
              all: basic_solver. }
            intros x HH; subst.
            red; simpls. split.
            { split; auto.
              red. rewrite SBE. eauto with hahn. }
            left. right. split; auto.
            red. rewrite IRF. eauto with hahn. }
          desf.
          { etransitivity.
            2: { eapply traversal_mon with (T:=etc_TC T); basic_solver. }
            unionL; auto; [apply ETCCOH|basic_solver]. }
          unionL.
          { etransitivity.
            2: eapply traversal_mon.
            { apply ETCCOH. }
            all: basic_solver. }
          intros x HH; subst.
          red; simpls. unfold set_inter. splits; auto; red.
          { by rewrite fwbob_in_sb. }
          rewrite PP4. eauto with hahn. }
        { by apply RED. }
        { rewrite (etc_I_in_S ETCCOH). clear. basic_solver. }
        { rewrite dom_sb_S_rfrmw_in_W_ex.
          rewrite !set_minus_union_l. unionL.
          2,3: basic_solver.
          generalize (etc_S_I_in_W_ex ETCCOH). clear. unfold eissued. basic_solver 10. }
        { desf; try unionR left.
          all: by rewrite dom_eqv1; rewrite RR; rewrite <- dom_eqv1. }
        2: by rewrite dom_eqv1; rewrite RR; rewrite <- dom_eqv1; try unionR left.
        { do 2 rewrite <- seqA. rewrite <- dom_rel_eqv_dom_rel, RR.
          rewrite dom_rel_eqv_dom_rel, !seqA. by unionR left. }
        { unfold dom_sb_S_rfrmw. simpls.
          rewrite RR. rewrite seqA. by apply RESRES. }
        { rewrite <- seqA. rewrite <- dom_rel_eqv_dom_rel, RR1.
          rewrite dom_rel_eqv_dom_rel, seqA. by unionR left. }
        { by arewrite (detour ⊆ detour ∪ rfe). }
        rewrite !set_inter_union_l. unionL.
        { rewrite (etc_S_W_ex_rfrmw_I ETCCOH). clear. basic_solver 10. }
        { generalize RFRMW. clear. basic_solver 10. }
        unfold dom_sb_S_rfrmw. arewrite (rfi ⊆ rf). basic_solver 10. }

      destruct (classic (Rel w)) as [REL|NREL].
      2: { assert (issuable G sc (etc_TC T) w) as WISS.
           { red. unfold set_inter. splits; auto; red.
             arewrite
               (fwbob ⨾ ⦗eq w⦘ ⊆
                      (⦗W ∩₁ Rel⦘ ⨾ sb ∩ same_loc ⨾ ⦗W⦘ ∪ ⦗F ∩₁ Acq/Rel⦘ ⨾ sb) ⨾ ⦗eq w⦘).
             { unfold imm_bob.fwbob. rewrite !seq_union_l, !seqA.
               unionL; eauto 10 with hahn.
               all: type_solver. }
             arewrite ((⦗W ∩₁ Rel⦘ ⨾ sb ∩ same_loc ⨾ ⦗W⦘ ∪ ⦗F ∩₁ Acq/Rel⦘ ⨾ sb) ⊆ ⦗FW⦘ ⨾ sb).
             2: done.
             basic_solver. }
           eexists; eexists.
           eapply ext_rlx_write_promise_step; eauto.
           red. unfold ecovered, eissued in *.
           splits; eauto 10; simpls. }

      eexists; eexists.
      eapply ext_rel_rmw_step; eauto.
      { red. unfold ecovered, eissued; simpls; splits.
        { right. left. splits; auto. }
        eapply COHSTEP1. eauto. }
      red; unfold ecovered, eissued; simpls.
      splits; eauto.
      constructor; unfold eissued, ecovered; simpls.
      { red. simpls; splits.
        { unionR left -> left. apply ETCCOH. }
        { unionL.
          { etransitivity.
            2: eapply traversal_mon.
            { apply ETCCOH. }
            all: basic_solver. }
          all: intros x HH; subst.
          all: red; simpls; split; [split; auto; red|].
          { rewrite SBE. eauto with hahn. }
          { left. right. split; auto.
            red. rewrite IRF. eauto with hahn. }
          { rewrite SBW. eauto with hahn. }
          do 2 left. split; auto. by right. }
        unionL.
        { etransitivity.
          2: eapply traversal_mon.
          { apply ETCCOH. }
          all: basic_solver. }
        intros x HH; subst.
        red; simpls. unfold set_inter. splits; auto; red.
        { rewrite fwbob_in_sb. rewrite SBW. eauto with hahn. }
        rewrite PP4. eauto with hahn. }
      { by apply RED. }
      { rewrite (etc_I_in_S ETCCOH). clear. basic_solver. }
      { rewrite dom_sb_S_rfrmw_in_W_ex.
        rewrite !set_minus_union_l. unionL.
        2,3: basic_solver.
        generalize (etc_S_I_in_W_ex ETCCOH). clear. unfold eissued. basic_solver 10. }
      { unionR left -> left.
        all: by rewrite dom_eqv1; rewrite RR; rewrite <- dom_eqv1. }
      2: by rewrite dom_eqv1; rewrite RR; rewrite <- dom_eqv1; try unionR left.
      { do 2 rewrite <- seqA. rewrite <- dom_rel_eqv_dom_rel, RR.
        rewrite dom_rel_eqv_dom_rel, !seqA. by unionR left. }
      { unfold dom_sb_S_rfrmw. simpls.
        rewrite RR. rewrite !seqA. by apply RESRES. }
      { rewrite <- seqA. rewrite <- dom_rel_eqv_dom_rel, RR1.
        rewrite dom_rel_eqv_dom_rel, seqA. by unionR left. }
      { by arewrite (detour ⊆ detour ∪ rfe). }
      rewrite !set_inter_union_l. unionL.
      { rewrite (etc_S_W_ex_rfrmw_I ETCCOH). clear. basic_solver 10. }
      { generalize RFRMW. clear. basic_solver 10. }
      unfold dom_sb_S_rfrmw. arewrite (rfi ⊆ rf). basic_solver 10. }

    assert (E e) as EE.
    { eapply tc_C_in_E.
      2: { apply COVEQ. basic_solver. }
      eauto. }
    assert (eissued T e) as ISS.
    { apply ISSEQ. eapply tc_W_C_in_I; eauto.
      split; auto. apply COVEQ. basic_solver. }
    assert (coverable G sc (etc_TC T) e) as COVERE.
    { red. unfold set_inter. splits; auto.
      do 2 left. split; auto. }
    destruct (classic (Rel e)) as [REL|NREL].
    { exfalso. apply NCOV. apply RELCOV. split; [split|]; auto. }
    destruct (classic (codom_rel rmw e)) as [RMW|NRMW].
    2: { eexists. eexists. eapply ext_rlx_write_cover_step; eauto.
         eapply ext_itrav_step_more.
         4: by eauto.
         { done. }
         { apply same_etc_Reflexive. }
         red. rewrite COVEQ. rewrite ISSEQ. splits; simpls. by symmetry. }
    exfalso. apply NCOV.
    destruct RMW as [r RMW].
    apply (RMWCOV _ _ RMW). eapply SBE.
    eexists. apply seq_eqv_r. split; eauto.
      by apply (rmw_in_sb WF). }

  assert (is_w lab e) as WW.
  { eapply issuedW.
    2: { apply ISSEQ. basic_solver. }
    eauto.  }
  assert (issuable G sc (etc_TC T') e) as ISS'.
  { eapply issued_in_issuable; eauto. apply ISSEQ. basic_solver. }
  assert (issuable G sc (etc_TC T) e) as ISS.
  { eapply issuable_add_eq_iff; eauto.
    eapply issuable_more; eauto.
    unfold ecovered, eissued in *.
    red. simpls. splits; by symmetry. }

  assert (~ covered (etc_TC T) e) as NCOV.
  { intros AA. apply NISS. eapply tc_W_C_in_I; eauto. by split. }

  destruct (classic (Rel e)) as [REL|NREL].
  2: { eexists; eexists. eapply ext_rlx_write_promise_step; eauto.
       eapply ext_itrav_step_more.
       4: by eauto.
       { done. }
       { apply same_etc_Reflexive. }
       red. rewrite COVEQ. rewrite ISSEQ. splits; simpls. by symmetry. }
  eexists; eexists.
  apply ext_rel_write_step; eauto.
  { intros [r RMW]. apply NISS.
    eapply w_covered_issued; eauto. split; auto.
    apply (RMWCOV _ _ RMW).
    red in ISS. apply COVEQ. eapply ISS'.
    eexists. apply seq_eqv_r. split; eauto.
    red. repeat left. apply seq_eqv_r. split.
    { by apply rmw_in_sb. }
      by split. }
  { eapply ext_itrav_step_more; eauto.
    { apply same_etc_Reflexive. }
    red. rewrite COVEQ. rewrite ISSEQ. splits; simpls. by symmetry. }
  red; unfold eissued, ecovered; simpls; splits.
  { left. by splits. }

  assert (dom_rel (sb ⨾ ⦗eq e⦘) ⊆₁ covered (etc_TC T)) as SBE.
  { destruct ISS as [[_ ISS] _]. red in ISS.
    arewrite (sb ⨾ ⦗eq e⦘ ⊆ fwbob ⨾ ⦗eq e⦘); auto.
    unfold imm_bob.fwbob.
    basic_solver 10. }
  
  assert (E e) as EE by apply ISS.
  
  assert (coverable G sc (mkTC (covered (etc_TC T)) (issued (etc_TC T) ∪₁ eq e)) e) as CCX.
  { red. split; [split|]; auto.
    do 2 left. split; auto. simpls. basic_solver. }

  assert (dom_rel (⦗W⦘ ⨾ sb ⨾ ⦗eq e⦘) ⊆₁ issued (etc_TC T)) as WSBW.
  { rewrite dom_eqv1. rewrite SBE.
    rewrite set_interC. eapply tc_W_C_in_I; eauto. }

  assert (dom_rel (rf ⨾ sb ⨾ ⦗eq e⦘) ⊆₁ issued (etc_TC T)) as RFSB.
  { etransitivity.
    2: eapply tc_rf_C; eauto.
    unfolder. ins. desf.
    eexists. splits; eauto.
    apply SBE. basic_solver 10. }

  assert (dom_rel ((detour ∪ rfe) ⨾ sb ⨾ ⦗eq e⦘) ⊆₁ issued (etc_TC T)) as DRFSB.
  { rewrite !seq_union_l, dom_union. unionL.
    2: by arewrite (rfe ⊆ rf).
    rewrite (dom_l (wf_detourD WF)), !seqA.
    rewrite detour_in_sb.
    arewrite (sb ⨾ sb ⊆ sb) by (generalize (@sb_trans G); basic_solver). }

  assert (dom_rel ((detour ∪ rfe) ⨾ rmw ⨾ ⦗reserved T ∪₁ eq e⦘) ⊆₁ issued (etc_TC T))
    as DRFSBE.
  { rewrite id_union, !seq_union_r, dom_union.
    unionL.
    { eby eapply etc_rmw_S. }
      by rewrite (rmw_in_sb WF). }

  constructor; unfold eissued, ecovered; simpls.
  { red. splits; simpls.
    { etransitivity.
      { apply TCCOH. }
      eauto with hahn. }
    { unionL.
      { etransitivity.
        2: { eapply traversal_mon with (T:=etc_TC T); basic_solver. }
        apply ETCCOH. }
      red. ins; desf.
      apply coverable_add_eq_iff
        with (T := mkTC (covered (etc_TC T)) (issued (etc_TC T) ∪₁ eq x)); auto. }
    unionL.
    { etransitivity.
      2: { eapply traversal_mon; basic_solver. }
      apply ETCCOH. }
    red. ins. desf.
    eapply traversal_mon with (T:=etc_TC T); basic_solver. }
  { by apply RED. }
  { unionL; [by unionR left -> left; apply ETCCOH|]. basic_solver. }
  { rewrite dom_sb_S_rfrmw_in_W_ex.
    rewrite !set_minus_union_l. unionL.
    3: basic_solver.
    { generalize (etc_S_I_in_W_ex ETCCOH). clear. unfold eissued. basic_solver 10. }
    unfolder. intros x [AA HH]. exfalso. apply HH. eauto. }
  { unionR left.
    rewrite dom_eqv1. rewrite RR. rewrite <- dom_eqv1.
    rewrite id_union, !seq_union_r, dom_union; unionL; [by apply ETCCOH|].
    arewrite_id ⦗F ∩₁ Acq/Rel⦘. by rewrite seq_id_l. }
  { unionR left.
    do 2 rewrite <- seqA. rewrite <- dom_rel_eqv_dom_rel, RR.
    rewrite dom_rel_eqv_dom_rel, seqA.
    rewrite id_union, !seq_union_r, dom_union, !seqA.
    unionL; [by apply ETCCOH|]. by sin_rewrite RMWRFI_ACQ_SB. }
  { unfold dom_sb_S_rfrmw. simpls.
    rewrite dom_eqv1; rewrite RR. rewrite <- dom_eqv1. unionR left.
    rewrite id_union, !seq_union_r, dom_union; unionL; [by apply ETCCOH|].
    arewrite (W_ex_acq ⊆₁ W); auto. rewrite (W_ex_in_W WF); basic_solver. }
  { unfold dom_sb_S_rfrmw. simpls.
    rewrite RR. rewrite !seqA. by apply RESRES. }
  { rewrite <- seqA. rewrite <- dom_rel_eqv_dom_rel, RR1.
    rewrite dom_rel_eqv_dom_rel, seqA.
    unionR left.
    rewrite id_union, !seq_union_r, dom_union; unionL; [by apply ETCCOH|].
    arewrite ((data ∪ rfi ∪ rmw)＊ ⨾ rppo G ⊆ sb); [|done].
    arewrite (rfi ⊆ sb). rewrite (rmw_in_sb WF).
    rewrite (data_in_sb WF), !unionK.
    rewrite (rppo_in_sb WF).
    rewrite rt_of_trans.
    all: generalize (@sb_trans G); auto.
    basic_solver 10. }
  { arewrite (detour ⊆ detour ∪ rfe). rewrite DRFE_EMP. by unionR left. }
  rewrite !set_inter_union_l. unionL.
  { rewrite (etc_S_W_ex_rfrmw_I ETCCOH). clear. basic_solver 10. }
  { rewrite <- ISSEQ.
    arewrite (eq e ∩₁ W_ex ⊆₁ codom_rel (rf ⨾ rmw ⨾ ⦗eissued T'⦘)).
    { intros x [AA [e' WEX]]; subst.
      rename e' into e. rename x into w.
      cdes IMMCON. red in Comp. specialize (Comp e).
      assert (E e /\ R e) as ERE.
      { set (CC:=WEX).
        apply (wf_rmwE WF) in CC. destruct_seq CC as [CC1 CC2].
        apply (wf_rmwD WF) in CC. destruct_seq CC as [CC3 CC4].
        split; auto. }
      apply Comp in ERE. destruct ERE as [wprev ERE].
      exists wprev. apply seqA.
      apply seq_eqv_r. split.
      { by exists e; split. }
      apply ISSEQ. by right. }
    arewrite (codom_rel (rf ⨾ rmw ⨾ ⦗eissued T'⦘) ⊆₁ codom_rel (⦗eissued T'⦘ ⨾ rf ⨾ rmw ⨾ ⦗eissued T'⦘)).
    2: basic_solver 10.
    apply codom_rel_mori.
    apply dom_rel_helper.
    eapply rfrmw_I_in_I; eauto. }
  unfold dom_sb_S_rfrmw. arewrite (rfi ⊆ rf). basic_solver 10.
Qed.

End SimTravStepExistence. 


Lemma ext_sim_trav_step_to_step T T' thread
      (TS : ext_isim_trav_step thread T T') :
  exists e T'', ext_itrav_step G sc e T T'' /\ tid e = thread.
Proof using. destruct TS; eauto. Qed.

End ExtSimTraversal.
