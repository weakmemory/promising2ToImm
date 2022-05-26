
Require Import Setoid.
From hahn Require Import Hahn.
From imm Require Import AuxDef Events Execution Execution_eco
     imm_bob imm_s_ppo imm_s imm_s_hb CombRelations AuxRel2.
Require Import AuxRel.
Require Export ExtTravRelations.
Require Import ExtTraversalConfig.
Require Import Lia.
From imm Require Import FinExecution ImmFair. 
From imm Require Import travorder.SimClosure.
From imm Require Import TLSCoherency.
From imm Require Import IordCoherency.
From imm Require Import TraversalOrder. 
Require Import TlsAux.
Require Import Next.

Set Implicit Arguments.

Section ExtTraversalConfig.
Variable G : execution.

Hypothesis WF : Wf G.
Hypothesis COM : complete G.
Hypothesis sc : relation actid.
Hypothesis IMMCON : imm_consistent G sc.
Hypothesis WFSC : wf_sc G sc.

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
Notation "'rppo'" := (rppo G).
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

  (* (⟪ COVER : *)
  (*      ⟪ NCOV : ~ covered T e ⟫ /\ *)
  (*      ⟪ COVEQ: covered T' ≡₁ covered T ∪₁ eq e ⟫ /\ *)
  (*      ⟪ ISSEQ: issued  T' ≡₁ issued  T ⟫ /\ *)
  (*      ⟪ RESEQ: reserved T' ≡₁ reserved T ⟫ *)
  (*  ⟫ \/ *)
  (*  ⟪ ISSUE : *)
  (*      ⟪ NISS : ~ issued T e ⟫ /\ *)
  (*      ⟪ RES  : W_ex e -> reserved T e ⟫ /\ *)
  (*      ⟪ COVEQ: covered T' ≡₁ covered T ⟫ /\ *)
  (*      ⟪ ISSEQ: issued  T' ≡₁ issued  T ∪₁ eq e ⟫ /\ *)
  (*      ⟪ RESEQ: reserved T' ≡₁ *)
  (*               reserved T ∪₁ eq e ∪₁ *)
  (*               dom_sb_S_rfrmw G T rfi (eq e) ⟫ *)
  (*  ⟫ \/ *)
  (*  ⟪ RESERVE : *)
  (*      ⟪ NISS : ~ reserved T e ⟫ /\ *)
  (*      ⟪ COVEQ: covered T' ≡₁ covered T ⟫ /\ *)
  (*      ⟪ ISSEQ: issued  T' ≡₁ issued  T ⟫ /\ *)
  (*      ⟪ RESEQ: reserved T' ≡₁ reserved T ∪₁ eq e ⟫ *)
  (* ⟫) /\ *)

Definition ets_upd_reserve (ae : trav_label) (T : trav_label -> Prop) : actid -> Prop :=
  match ae with
  | (ta_issue, e) => eq e ∪₁ dom_sb_S_rfrmw G T rfi (eq e)
  | _ => ∅
  end.

Record ext_itrav_step (ae : trav_label) (T T': trav_label -> Prop) :=
  mkETS {
      ets_tls_coh     : tls_coherent     G    T';
      ets_iord_coh    : iord_coherent    G sc T';
      ets_reserve_coh : reserve_coherent G    T';
      ets_new_ta      : ~ T ae;
      ets_issue_W_ex  : W_ex (event ae) -> action ae = ta_issue -> T (ta_reserve, event ae);
      ets_upd         : T' ≡₁ T ∪₁ eq ae ∪₁ (eq ta_reserve) <*> ets_upd_reserve ae T;
    }.

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
  apply (@well_founded_ind _ sb (@wf_sb G) Q).
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
  
Variable T : trav_label -> Prop. 
(* Hypothesis ETCCOH : etc_coherent G sc T. *)
Hypotheses (TCOH: tls_coherent G T)
           (ICOH: iord_coherent G sc T)
           (RCOH: reserve_coherent G T).

Lemma dom_r_sb_new_reserved e r :
  dom_rel (r ⨾ sb ⨾ ⦗reserved T ∪₁ eq e ∪₁
           dom_rel (sb ⨾ ⦗reserved T⦘) ∩₁ codom_rel (⦗eq e⦘ ⨾ rfi ⨾ rmw)⦘) ≡₁
  dom_rel (r ⨾ sb ⨾ ⦗reserved T ∪₁ eq e⦘).
Proof using.
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
Proof using WF TCOH RCOH. 
  split; [|basic_solver 20].
  rewrite id_union. rewrite !seq_union_r, dom_union.
  unionL; [done|].
  arewrite (dom_rel (sb ⨾ ⦗reserved T⦘) ∩₁ codom_rel (⦗eq e⦘ ⨾ rfi ⨾ rmw) ⊆₁
            dom_rel (sb ⨾ ⦗reserved T⦘)) by basic_solver. 
  arewrite (reserved T ⊆₁ W ∩₁ reserved T) at 1.
  { generalize (reservedW WF). basic_solver. }
  generalize (rppo_sb_in_rppo WF).
  basic_solver 20.
Qed.

Lemma dom_sb_new_reserved e :
  dom_rel (sb ⨾ ⦗reserved T ∪₁ eq e ∪₁
           dom_rel (sb ⨾ ⦗reserved T⦘) ∩₁ codom_rel (⦗eq e⦘ ⨾ rfi ⨾ rmw)⦘) ≡₁
  dom_rel (sb ⨾ ⦗reserved T ∪₁ eq e⦘).
Proof using. 
  assert (sb ≡ ⦗ fun _ => True ⦘ ⨾ sb) as AA by basic_solver.
  rewrite AA at 1 3.
  rewrite !seqA. by apply dom_r_sb_new_reserved.
Qed.

Lemma dom_rfe_rppo_S_in_I :
  dom_rel (rfe ⨾ rppo ⨾ ⦗reserved T⦘) ⊆₁ issued T.
Proof using RCOH. 
  rewrite <- rcoh_rppo_S; eauto.
  rewrite <- inclusion_id_rt. rewrite seq_id_l.
  basic_solver 10.
Qed.

(* TODO: move to ImmProperties.v *)
Lemma codom_rfi_rfe_empty : codom_rel rfi ∩₁ codom_rel rfe ⊆₁ ∅.
Proof using WF.
  unfold Execution.rfi, Execution.rfe.
  unfolder. ins. desf. 
  assert (x0 = x1); subst; eauto.
  eapply (wf_rff WF); eauto.
Qed.

(* iord_step *)
(* Lemma iord_step_to_ext_trav_step T' (TS : iord_step G sc T T') : *)
(*   exists T'', ext_trav_step T T''. *)
(* Proof using. *)
(*   inversion TS as [[a e] STEP]. *)
(*   exists (T ∪₁ eq (mkTL a e)). red. exists e. red. *)

(* Lemma trav_step_to_ext_trav_step T' (TS : trav_step G sc T T') : *)
(*   exists T', ext_trav_step T T''. *)
(* Proof using.  *)
(*   unionL. *)
(*   assert (tc_coherent G sc (etc_TC T)) as TCCOH. *)
(*   { apply ETCCOH. } *)
(*   assert (tc_coherent G sc TC') as TCCOH'. *)
(*   { eapply trav_step_coherence; eauto. } *)

(*   red in TS. desf. cdes TS. *)
(*   desf. *)
(*   { exists (mkETC (mkTC (covered T ∪₁ eq e) (issued T)) (reserved T)). *)
(*     eexists e. *)
(*     red. splits. *)
(*     { left. splits; auto. } *)
(*     constructor; unfold issued, covered; simpls. *)
(*     all: try by apply ETCCOH. *)
(*     (* TODO: generalize to a lemma *) *)
(*     eapply trav_step_coherence. *)
(*     2: by apply ETCCOH.  *)
(*     eapply trav_step_more_Proper. *)
(*     3: by eexists; eauto. *)
(*     { apply same_tc_Reflexive. } *)
(*     { red. simpls. split; by symmetry. } *)
(*     unionR left. apply ETCCOH. } *)

(*   assert (E e) as EE. *)
(*   { eapply itrav_stepE with (T:= etc_TC T); eauto. } *)
(*   assert (eq e ⊆₁ E) as EQEE. *)
(*   { basic_solver. } *)
(*   assert (W e) as WE by apply ISS. *)

(*   assert (eq e ⊆₁ issuable G sc (etc_TC T)) as EQEISS by basic_solver. *)
(*   assert (dom_rel (⦗F ∩₁ Acq/Rel⦘ ⨾ sb ⨾ ⦗eq e⦘) ⊆₁ covered (etc_TC T)) as COVSBE. *)
(*   { rewrite EQEISS. arewrite (⦗F ∩₁ Acq/Rel⦘ ⨾ sb ⊆ fwbob). *)
(*     unfold issuable. basic_solver 10. } *)
(*   assert (dom_rel ((detour ∪ rfe) ⨾ (rmw ⨾ rfi)＊ ⨾ ⦗R ∩₁ Acq⦘ ⨾ sb ⨾ ⦗eq e⦘) ⊆₁ issued (etc_TC T)) as ISSSBE. *)
(*   { rewrite EQEISS. by apply dom_detour_rmwrfi_rfe_acq_sb_issuable. } *)
(*   assert (dom_rel (⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗eq e⦘) ⊆₁ issued (etc_TC T)) as WEXACQE. *)
(*   { rewrite EQEISS. by apply dom_wex_sb_issuable. } *)

(*   assert (dom_rel ((detour ∪ rfe) ⨾ (data ∪ rfi ∪ rmw)＊ ⨾ rppo ⨾ ⦗eq e⦘) ⊆₁ *)
(*                   issued (etc_TC T)) as RPPOSBE. *)
(*   { rewrite EQEISS.  *)
(*     sin_rewrite (detour_rfe_data_rfi_rmw_rppo_in_detour_rfe_ppo WF). *)
(*     rewrite !seqA. by apply dom_detour_rfe_ppo_issuable. } *)

(*   destruct *)
(*   (classic (exists w', *)
(*                (dom_rel (sb ⨾ ⦗eq e⦘) ∩₁ *)
(*                 codom_rel (⦗issued T⦘ ⨾ rf ⨾ ⦗R_ex⦘ ⨾ rmw) \₁ reserved T) w')) *)
(*     as [[w' WWB]|NWHH]. *)
(*   { edestruct wf_impl_min_elt *)
(*               with (B := dom_rel (sb ⨾ ⦗eq e⦘) ∩₁ *)
(*                          codom_rel (⦗issued T⦘ ⨾ rf ⨾ ⦗R_ex⦘ ⨾ rmw) \₁ reserved T) *)
(*                    (r := ⦗W_ex⦘ ⨾ sb) as [w [[[WHH WAA] NRES] MIN]]. *)
(*     { arewrite (⦗W_ex⦘ ⨾ sb ⊆ sb). *)
(*       apply wf_sb. } *)
(*     { intros [AA BB]. eapply AA; eauto. } *)

(*     assert (W_ex w) as WEXW. *)
(*     { generalize WAA.  unfold Execution.W_ex. basic_solver. } *)
(*     assert (E w) as EW by (by apply (W_ex_in_E WF)). *)
(*     assert (eq w ⊆₁ E) as EQWE. *)
(*     { basic_solver. } *)
(*     assert (eq w ⊆₁ dom_rel (⦗W_ex⦘ ⨾ sb ⨾ ⦗eq e⦘)) as EQWSB. *)
(*     { generalize WHH. basic_solver 10. }  *)
(*     assert (rmw ⨾ ⦗eq w⦘ ⊆ rppo ⨾ ⦗eq w⦘) as RPPO_RMW_W. *)
(*     { destruct WAA as [y AA]. destruct_seq_l AA as BB. *)
(*       destruct AA as [z [_ AA]]. destruct_seq_l AA as DD. *)
(*       intros v u HH. destruct_seq_r HH as CC; subst. *)
(*       assert (v = z); subst. *)
(*       { eapply (wf_rmw_invf WF); eauto. } *)
(*       apply seq_eqv_r. split; auto. *)
(*       apply R_ex_sb_W_in_rppo. *)
(*       apply seq_eqv_lr. splits; auto. *)
(*       { apply rmw_in_sb; auto. } *)
(*         by apply (W_ex_in_W WF). } *)
(*     assert (rppo ⨾ ⦗W_ex⦘ ⨾ sb ⨾ ⦗eq e⦘ ⊆ rppo ⨾ ⦗eq e⦘) as RPPO_WEX_SB. *)
(*     { arewrite (⦗eq e⦘ ⊆ ⦗W⦘ ⨾ ⦗eq e⦘) at 1. *)
(*       { generalize WE. basic_solver. } *)
(*       arewrite_id ⦗W_ex⦘. rewrite seq_id_l. *)
(*         by sin_rewrite (rppo_sb_in_rppo WF). } *)

(*     exists (mkETC (mkTC (covered T) (issued T)) *)
(*                   (reserved T ∪₁ eq w)). *)
(*     exists w. *)
(*     constructor; unfold issued, covered; simpls. *)
(*     { do 2 right. splits; eauto. } *)
(*     unnw. constructor; unfold issued, covered; simpls. *)
(*     { by unionL; [by apply ETCCOH|]. } *)
(*     { unionR left. apply ETCCOH. } *)
(*     { rewrite set_minus_union_l. *)
(*       unionL; [by apply ETCCOH|]. *)
(*       basic_solver. } *)
(*     4: { unionR left. *)
(*          unfold dom_sb_S_rfrmw. simpls. *)
(*          rewrite id_union, !seq_union_r, dom_union, set_inter_union_l. *)
(*          unionL; [by apply ETCCOH|]. *)
(*          rewrite <- set_interK with (s:=dom_rel (sb ⨾ ⦗eq w⦘)). *)
(*          rewrite set_interA. *)
(*          rewrite EQWSB at 2. *)
(*          rewrite <- !seqA, dom_rel_eqv_dom_rel, !seqA. *)
(*          arewrite (sb ⨾ ⦗W_ex⦘ ⨾ sb ⊆ sb) by (generalize (@sb_trans G); basic_solver). *)
(*          intros b [AA BB]. *)
(*          apply NNPP. intros CC. *)
(*          eapply MIN. *)
(*          { split; [apply BB|apply CC]. } *)
(*          destruct AA as [y AA]. *)
(*          apply seq_eqv_r in AA. desf. *)
(*          apply seq_eqv_l. split; auto. generalize BB. unfold Execution.W_ex. basic_solver. } *)
(*     1-5: rewrite id_union, !seq_union_r, dom_union. *)
(*     1-5: unionL; [by apply ETCCOH|]. *)
(*     5: rewrite RPPO_RMW_W. *)
(*     1-5: rewrite EQWSB. *)
(*     1-5: rewrite <- !seqA, dom_rel_eqv_dom_rel, !seqA. *)
(*     1-3: by arewrite (sb ⨾ ⦗W_ex⦘ ⨾ sb ⊆ sb) by (generalize (@sb_trans G); basic_solver). *)
(*     1,2: rewrite RPPO_WEX_SB; auto. *)
(*     { etransitivity; [|by apply RPPOSBE]. *)
(*       clear. rewrite rtE. basic_solver 15. } *)
(*     rewrite set_inter_union_l. *)
(*     unionL; [by apply ETCCOH|]. *)
(*     generalize WAA. unfold issued. basic_solver 10. } *)
(*   destruct (classic (reserved T e \/ ~ W_ex e)) as [RES|NRES]. *)
(*   { exists (mkETC (mkTC (covered T) (issued T ∪₁ eq e)) *)
(*                   (reserved T ∪₁ eq e ∪₁ *)
(*                    dom_rel (sb ⨾ ⦗reserved T⦘) ∩₁ codom_rel (⦗eq e⦘ ⨾ rfi ⨾ rmw))). *)

(*     exists e. *)
(*     constructor; unfold issued, covered; simpls. *)
(*     { right. left. splits; eauto. intuition. } *)
(*     unnw. constructor; unfold issued, covered; simpls. *)
(*     { eapply trav_step_coherence. *)
(*       2: by apply ETCCOH. *)
(*       eapply trav_step_more_Proper. *)
(*       3: by eexists; eauto. *)
(*       { apply same_tc_Reflexive. } *)
(*       red. simpls. split; by symmetry. } *)
(*     { unionL; auto. *)
(*       { apply ETCCOH. } *)
(*       rewrite (wf_rmwE WF). *)
(*       basic_solver. } *)
(*     { unionL; [|basic_solver]. *)
(*       unionR left -> left. apply ETCCOH. } *)
(*     { rewrite !set_minus_union_l. unionL. *)
(*       3: { rewrite rmw_W_ex. basic_solver. } *)
(*       { rewrite <- (etc_S_I_in_W_ex ETCCOH). basic_solver. } *)
(*       rewrite set_minus_union_r. *)
(*       basic_solver. } *)
(*     2: do 2 rewrite <- seqA. *)
(*     1-3: rewrite dom_r_sb_new_reserved; auto. *)
(*     1-3: rewrite id_union, !seq_union_r, dom_union. *)
(*     1-3: try unionR left. *)
(*     1-3: try rewrite !seqA. *)
(*     1-3: by unionL; [by apply ETCCOH|]. *)
(*     { unfold dom_sb_S_rfrmw. simpls. *)
(*       rewrite dom_sb_new_reserved; auto. *)
(*       rewrite !id_union, !seq_union_l, !seq_union_r. *)
(*       rewrite dom_union, codom_union, set_inter_union_r. *)
(*       rewrite !set_inter_union_l. *)
(*       unionL. *)
(*       1,2: unionR left -> left. *)
(*       { apply ETCCOH. } *)
(*       { intros w' BB. apply NNPP. intros AA. *)
(*         apply NWHH. exists w'. split; auto. *)
(*         generalize BB. clear. basic_solver 10. } *)
(*       { unionR right. *)
(*         rewrite !seqA. *)
(*         rewrite rfi_union_rfe. *)
(*         rewrite !seq_union_l, !seq_union_r, codom_union, set_inter_union_r. *)
(*         arewrite (rfi ⨾ ⦗R_ex⦘ ⊆ rfi). *)
(*         arewrite (dom_rel (sb ⨾ ⦗reserved T⦘) ∩₁ codom_rel (⦗eq e⦘ ⨾ rfe ⨾ ⦗R_ex⦘ ⨾ rmw) ⊆₁ ∅). *)
(*         2: { unionL; [done|]. basic_solver. } *)
(*         rewrite set_interC. *)
(*         apply seq_codom_dom_inter_iff. *)
(*         split; [|basic_solver]. *)
(*         rewrite !seqA. *)
(*         arewrite (reserved T ⊆₁ W ∩₁ reserved T). *)
(*         { generalize (reservedW WF ETCCOH). basic_solver. } *)
(*         rewrite id_inter. *)
(*         arewrite (rmw ⨾ sb ⊆ sb). *)
(*         { rewrite (rmw_in_sb WF). generalize (@sb_trans G). *)
(*           clear. basic_solver. } *)
(*         sin_rewrite R_ex_sb_W_in_rppo. *)
(*         generalize dom_rfe_rppo_S_in_I. unfold issued. *)
(*         generalize NISS. basic_solver 10. } *)
(*       arewrite_id ⦗R_ex⦘. rewrite seq_id_l. *)
(*       intros w [[y AA] [z BB]]. *)
(*       exfalso. *)
(*       destruct_seq_l BB as CC; subst. *)
(*       destruct_seq_r AA as DD; subst. *)
(*       eapply rfrmw_sb_irr; eauto. *)
(*       apply seqA. eexists. eauto. } *)
(*     { unionR left. *)
(*       rewrite <- seqA at 1. *)
(*       rewrite dom_r_rppo_new_reserved; auto. *)
(*       rewrite !seqA. *)
(*       rewrite id_union, !seq_union_r, dom_union. *)
(*       unionL; [by apply ETCCOH|]. *)
(*       sin_rewrite (detour_rfe_data_rfi_rmw_rppo_in_detour_rfe_ppo WF). *)
(*       arewrite (eq e ⊆₁ issuable G sc (etc_TC T)) by basic_solver. *)
(*       eapply dom_detour_rfe_ppo_issuable; eauto. } *)
(*     { rewrite !id_union, !seq_union_r, !dom_union. unionL. *)
(*       { unionR left. apply ETCCOH. } *)
(*       { unionR left. *)
(*         destruct RES as [RES|RES]. *)
(*         { arewrite (eq e ⊆₁ reserved T) by (generalize RES; basic_solver). *)
(*           apply ETCCOH. } *)
(*         transitivity (fun _ : actid => False); [|basic_solver]. *)
(*         generalize RES. unfold Execution.W_ex. clear. basic_solver. } *)
(*       transitivity (fun _ : actid => False); [|basic_solver]. *)
(*       unfold Execution.detour. *)
(*       clear RES. unfolder. ins. desf. *)
(*       all: assert (z2 = z) by (eapply (wf_rmw_invf WF); eauto); subst. *)
(*       all: eapply codom_rfi_rfe_empty; basic_solver. } *)
(*     rewrite id_union, !seq_union_l, codom_union. *)
(*     rewrite set_inter_union_l. *)
(*     apply set_union_mori. *)
(*     2: arewrite (rfi ⊆ rf); basic_solver 10. *)
(*     rewrite set_inter_union_l. unionL; [by apply ETCCOH|]. *)
(*     rewrite <- issuable_W_ex_in_codom_I_rfrmw; eauto. *)
(*     basic_solver. } *)
(*   assert (W_ex e) as WEXE. *)
(*   { apply NNPP. intuition. } *)
(*   assert (~ reserved T e) as NRESE by intuition. *)

(*   exists (mkETC (mkTC (covered T) (issued T)) *)
(*                 (reserved T ∪₁ eq e)). *)
(*   exists e. *)
(*   constructor; unfold issued, covered; simpls. *)
(*   { do 2 right. splits; eauto. } *)
(*   unnw. constructor; unfold issued, covered; simpls. *)
(*   { by unionL; [by apply ETCCOH|]. } *)
(*   { unionR left. apply ETCCOH. } *)
(*   { rewrite !set_minus_union_l. unionL; [by apply ETCCOH|]. *)
(*     generalize WEXE. basic_solver. } *)
(*   4: { unfold dom_sb_S_rfrmw. simpls. *)
(*        unionR left. *)
(*        rewrite id_union, !seq_union_r, dom_union. *)
(*        rewrite set_inter_union_l. *)
(*        unionL; [by apply ETCCOH|]. *)
(*        intros w' BB. apply NNPP. intros AA. *)
(*        apply NWHH. exists w'. split; auto. *)
(*        unfold issued. generalize BB. clear. basic_solver 20. } *)
(*   6: { rewrite !set_inter_union_l. *)
(*        unionL; [by apply ETCCOH|]. *)
(*        rewrite EQEISS. by apply issuable_W_ex_in_codom_I_rfrmw. } *)
(*   1-5: rewrite id_union, !seq_union_r, dom_union. *)
(*   1-4: by unionL; [by apply ETCCOH|]. *)
(*   unionL; [by apply ETCCOH|]. *)
(*   rewrite (rmw_in_ppo WF). *)
(*   rewrite EQEISS. arewrite (detour ⊆ detour ∪ rfe). by apply dom_detour_rfe_ppo_issuable. *)
(* Qed. *)

End Props.

(* Lemma exists_ext_trav_step e (T: ext_trav_config) *)
(*       (N_FIN : next G (covered T) e) *)
(*       (ETCCOH : etc_coherent G sc T) *)
(*       (FINDOM : fin_exec G): *)
(*   exists T', ext_trav_step T T'. *)
(* Proof using WF WFSC IMMCON COM. *)
(*   edestruct exists_trav_step; eauto. *)
(*   { apply ETCCOH. } *)
(*   2: { eapply trav_step_to_ext_trav_step; eauto. } *)
(*   apply imm_s_rfppo.fsupp_ar_rf_ppo_loc_fin; auto.  *)
(* Qed. *)

(* Definition same_ext_trav_config (T T' : ext_trav_config) := *)
(*   covered T ≡₁ covered T' /\ issued T ≡₁ issued T' /\ *)
(*   reserved T ≡₁ reserved T'. *)

(* Lemma same_ext_trav_config_refl : reflexive same_ext_trav_config. *)
(* Proof using. split; basic_solver. Qed. *)

(* Lemma same_ext_trav_config_sym : symmetric same_ext_trav_config. *)
(* Proof using. *)
(*   unfold same_ext_trav_config; split; splits; ins; desf; symmetry; auto. *)
(* Qed. *)

(* Lemma same_ext_trav_config_trans : transitive same_ext_trav_config. *)
(* Proof using. *)
(*   unfold same_ext_trav_config; split; splits; ins; desf; etransitivity; eauto. *)
(* Qed. *)

(* Global Add Parametric Relation : ext_trav_config same_ext_trav_config *)
(*     reflexivity proved by same_ext_trav_config_refl *)
(*     symmetry proved by same_ext_trav_config_sym *)
(*     transitivity proved by same_ext_trav_config_trans *)
(*       as same_etc. *)

(* Global Add Parametric Morphism : etc_coherent with signature *)
(*     eq ==> eq ==> same_ext_trav_config ==> iff as etc_coherent_more. *)
(* Proof using. *)
(*   intros G' sc' T T' EQT. cdes EQT. *)
(*   split. *)
(*   symmetry in EQT0. *)
(*   symmetry in EQT1. *)
(*   symmetry in EQT2. *)
(*   (* TODO: introduce a morphism for dom_sb_S_rfrmw instead. *) *)
(*   all: intros HH; constructor; try unfold dom_sb_S_rfrmw. *)
(*   all: try rewrite EQT0. *)
(*   all: try rewrite EQT1. *)
(*   all: try rewrite EQT2. *)
(*   all: try apply HH. *)
(*   all: eapply tc_coherent_more; eauto; [|by apply HH]. *)
(*   all: red; unfold covered, issued in *; eauto. *)
(* Qed. *)

Global Add Parametric Morphism : ets_upd_reserve with signature
    eq ==> set_equiv ==> set_equiv as
         ets_upd_reserve_more.
Proof using.
  intros x T T' EQ. unfold ets_upd_reserve. destruct x; desf.
  now rewrite EQ.
Qed.

Global Add Parametric Morphism : ext_itrav_step with signature
    eq ==> set_equiv ==> set_equiv ==> iff as
        ext_itrav_step_more.
Proof using.
  intros x TA TB EQ TA' TB' EQ'.
  split.
  symmetry in EQ.
  symmetry in EQ'.
  all: intros HH; split.
  all: try now rewrite EQ'; apply HH.
  all: try now intros AA; eapply ets_new_ta; eauto; apply EQ.
  all: try now ins; destruct x; ins; subst; apply EQ; apply HH.
  all: rewrite EQ', EQ; apply HH.
Qed.

(* Lemma ext_trav_step_in_trav_step : *)
(*   ext_trav_step ⊆ etc_TC ⋄ (same_trav_config ∪ trav_step G sc). *)
(* Proof using WF IMMCON. *)
(*   unfold ext_trav_step, ext_itrav_step, map_rel. *)
(*   intros T T'. ins. desf. *)
(*   3: { left. red. by split; symmetry. } *)
(*   all: right; exists e; red; unnw. *)
(*   all: unfold covered, issued in *. *)
(*   2: right. *)
(*   left. *)
(*   all: splits; auto. *)
(*   { apply coverable_add_eq_iff; auto. *)
(*     apply covered_in_coverable; [|basic_solver]. *)
(*     eapply tc_coherent_more. *)
(*     2: apply ETCCOH'. *)
(*     red; splits; simpls; by symmetry. } *)
(*   apply issuable_add_eq_iff; auto.  *)
(*   eapply issued_in_issuable; [|basic_solver]. *)
(*   eapply tc_coherent_more. *)
(*   2: apply ETCCOH'. *)
(*   red; splits; simpls; by symmetry. *)
(* Qed. *)

Lemma ext_itrav_stepE lbl T T' (STEP : ext_itrav_step lbl T T'):
  E (event lbl).
Proof using WF.
  inversion STEP.
  apply tlsc_E with (tc := T'); auto.
  apply ets_upd0. basic_solver. 
Qed.

Lemma ext_itrav_step_reserveW w T
      (STEP : ext_itrav_step (mkTL ta_reserve w) T (T ∪₁ eq (mkTL ta_reserve w))):
  W w.
Proof using WF.
  inversion STEP.
  eapply reservedW; [| by apply ets_tls_coh0 | ..]; auto.
  apply reserved_union. right. red. vauto. 
Qed.

Lemma ext_itrav_step_reserve_nS e T
      (STEP : ext_itrav_step (mkTL ta_reserve e) T (T ∪₁ eq (mkTL ta_reserve e))):
  ~ reserved T e.
Proof using.
  inversion STEP. intros RES. apply ets_new_ta0.
  red in RES. unfolder in RES. desc. destruct y; ins; vauto. 
Qed.

(* Not true anymore due to propagations *)
(* Lemma ext_itrav_step_nC lbl T T' *)
(*       (TCOH: tls_coherent G T) (ICOH: iord_coherent G sc T) *)
(*       (STEP : ext_itrav_step lbl T T'): *)
(*   ~ covered T (event lbl). *)

Lemma ext_itrav_step_ninit lbl T T'
      (TCOH : tls_coherent G T)      
      (STEP : ext_itrav_step lbl T T') : ~ is_init (event lbl).
Proof using WF.
  (* assert (tc_coherent G sc (etc_TC T)) as TCCOH by apply ETCCOH. *)
  intros II. inv STEP.
  apply ets_new_ta0. pose proof TCOH as [INIT _]. apply INIT.
  assert (T' lbl) as T'lbl by (apply ets_upd0; basic_solver). 
  eapply tls_coh_exec in T'lbl; eauto. red in T'lbl. des; auto.
  apply exec_tls_ENI in T'lbl. do 2 red in T'lbl. by desc. 
Qed. 

(* TODO: move to Next *)
Lemma iord_coherent_extend_singleton T lbl
      (ICOH: iord_coherent G sc (T ∪₁ eq lbl)):
  dom_rel (iord G sc ⨾ ⦗eq lbl⦘) ⊆₁ T.
Proof using WF IMMCON.
  red in ICOH. rewrite id_union, seq_union_r, dom_union in ICOH.
  apply set_subset_union_l in ICOH as [_ ICOH].
  eapply dom_rel_union_r1; eauto. 
  red. intros x y REL%seq_eqv_lr. desc. subst. 
  clear COM WFSC. edestruct iord_irreflexive; eauto; apply IMMCON.
Qed. 

Lemma ext_itrav_step_cov_coverable T T' e
      (TSTEP : ext_itrav_step (mkTL ta_cover e) T T') :
  coverable G sc T e.
Proof using WF IMMCON.
  inversion TSTEP. red.
  assert (T' (mkTL ta_cover e)) as T'lbl by (apply ets_upd0; basic_solver). 
  split.
  { eapply tlsc_E in T'lbl; eauto. }
  exists (mkTL ta_cover e). do 2 split; vauto. red.
  ins. rewrite set_pair_alt, set_inter_empty_r, set_union_empty_r in ets_upd0.
  rewrite ets_upd0 in ets_iord_coh0. 
  apply iord_coherent_extend_singleton; eauto. 
Qed. 

Lemma ext_itrav_step_cov_next T T' e
      (TCOH: tls_coherent G T)
      (TSTEP : ext_itrav_step (mkTL ta_cover e) T T'):
  next G (covered T) e.
Proof using WF IMMCON.
  split; [split|].  
  { apply ext_itrav_stepE in TSTEP; eauto. }
  { apply ext_itrav_step_cov_coverable in TSTEP; eauto.
    red. rewrite <- (@dom_sb_coverable G sc); eauto. basic_solver. }
  inversion TSTEP. intros COV. apply ets_new_ta0.
  red in COV. unfolder in COV. desc. destruct y; ins; vauto. 
Qed.

Lemma ext_itrav_step_iss_issuable T T' e
      (* (TSTEP : ext_itrav_step (mkTL ta_issue e) T (T ∪₁ eq (mkTL ta_issue e))) : *)
      (TSTEP : ext_itrav_step (mkTL ta_issue e) T T') :
  issuable G sc T e.
Proof using WF IMMCON.
  inversion TSTEP. red.
  assert (T' (mkTL ta_issue e)) as T'lbl by (apply ets_upd0; basic_solver). 
  split.
  { split. 
    { eapply tlsc_E in T'lbl; eauto. }
    eapply issuedW; vauto. } 
  exists (mkTL ta_issue e). do 2 split; vauto. red.
  rewrite ets_upd0 in ets_iord_coh0. red in ets_iord_coh0.
  apply dom_rel_union_r1 in ets_iord_coh0; [| iord_dom_solver].
  rewrite id_union, seq_union_r, dom_union in ets_iord_coh0.
  apply set_subset_union_l in ets_iord_coh0 as [ICOH _].
  eapply iord_coherent_extend_singleton; eauto. 
Qed. 

Lemma ext_itrav_step_iss_nI T T' e
      (TSTEP : ext_itrav_step (mkTL ta_issue e) T T') :
  ~ issued T e.
Proof using.
  inversion TSTEP. intros ISS. apply ets_new_ta0. 
  red in ISS. unfolder in ISS. desc. destruct y; ins; vauto. 
Qed.

Lemma dom_sb_S_rfrmw_same_tid T w (NINIT : ~ is_init w) :
  dom_sb_S_rfrmw G T rfi (eq w) ⊆₁ (fun x => tid x = (tid w)).
Proof using WF.
  unfold dom_sb_S_rfrmw.
  arewrite (rfi ⊆ sb).
  rewrite (rmw_in_sb WF).
  arewrite (sb ⨾ sb ⊆ sb).
  { generalize (@sb_trans G). basic_solver. }
  arewrite (⦗eq w⦘ ⊆ ⦗eq w⦘ ⨾ ⦗ set_compl is_init ⦘).
  { basic_solver. }
  rewrite ninit_sb_same_tid.
  basic_solver.
Qed.

End ExtTraversalConfig.
