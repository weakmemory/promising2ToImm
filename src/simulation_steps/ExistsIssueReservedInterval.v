Require Import Setoid PArith.
From hahn Require Import Hahn.
Require Import PromisingLib.
From Promising2 Require Import TView View Time Event Cell Thread Memory Configuration Local.

From imm Require Import Events.
From imm Require Import Execution.
From imm Require Import Execution_eco.
From imm Require Import imm_s_hb.
From imm Require Import imm_s.
From imm Require Import imm_common.
From imm Require Import CombRelations.
From imm Require Import AuxDef.

Require Import AuxRel2.
Require Import TraversalConfig.
Require Import SimulationRel.
Require Import SimState.
Require Import MemoryAux.
Require Import MaxValue.
Require Import ViewRel.
Require Import ViewRelHelpers.
Require Import Event_imm_promise.
Require Import ExtTraversal.
Require Import ExtTraversalProperties.
Require Import TraversalProperties.
Require Import FtoCoherent.
Require Import SimulationRelProperties.
Require Import ImmProperties.

Set Implicit Arguments.

Section Aux.

Variable G : execution.
Variable WF : Wf G.
Variable sc : relation actid.

Notation "'acts'" := G.(acts).
Notation "'co'" := G.(co).
Notation "'sw'" := G.(sw).
Notation "'hb'" := G.(hb).
Notation "'sb'" := G.(sb).
Notation "'rf'" := G.(rf).
Notation "'rfi'" := G.(rfi).
Notation "'rfe'" := G.(rfe).
Notation "'rmw'" := G.(rmw).
Notation "'lab'" := G.(lab).
Notation "'msg_rel'" := (msg_rel G sc).
Notation "'urr'" := (urr G sc).
Notation "'release'" := G.(release).

Notation "'E'" := G.(acts_set).
Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'Loc_' l" := (fun x => loc lab x = Some l) (at level 1).
Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'W_'" := (fun l => W ∩₁ Loc_ l).
Notation "'FR'" := (fun x => F x \/ R x).
Notation "'FW'" := (fun x => F x \/ W x).

Notation "'W_ex'" := (W_ex G).
Notation "'W_ex_acq'" := (W_ex ∩₁ (fun a => is_true (is_xacq lab a))).

Notation "'Pln'" := (fun a => is_true (is_only_pln lab a)).
Notation "'Rlx'" := (is_rlx lab).
Notation "'Rel'" := (is_rel lab).
Notation "'Acq'" := (is_acq lab).
Notation "'Acqrel'" := (is_acqrel lab).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

Hypothesis IMMCON : imm_consistent G sc.

Variable T : trav_config.
Variable S : actid -> Prop.
Hypothesis ETCCOH : etc_coherent G sc (mkETC T S).

Hypothesis RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T.

Variable f_to f_from : actid -> Time.t.
Hypothesis FCOH : f_to_coherent G S f_to f_from.

Variable thread : thread_id.
Variable PC : Configuration.t.
Variable local : Local.t.

Hypothesis SIM_TVIEW : sim_tview G sc (covered T) f_to local.(Local.tview) thread.
Hypothesis SIM_MEM : sim_mem G sc T f_to f_from thread local PC.(Configuration.memory).
Hypothesis INHAB : Memory.inhabited PC.(Configuration.memory).
Hypothesis PLN_RLX_EQ : pln_rlx_eq local.(Local.tview).
Hypothesis MEM_CLOSE : memory_close local.(Local.tview) PC.(Configuration.memory).

Hypothesis SIM_RES_MEM :
  sim_res_mem G T S f_to f_from thread local (Configuration.memory PC).

Hypothesis PROM_IN_MEM :
  forall thread' langst local
         (TID : IdentMap.find thread' PC.(Configuration.threads) =
                Some (langst, local)),
    Memory.le local.(Local.promises) PC.(Configuration.memory).

(* TODO: move to a more appropriate place. *)
Definition rfrmw_prev_rel w locw p_rel := 
  (⟪ REL_PLN_RLX : View.pln p_rel.(View.unwrap) = View.rlx p_rel.(View.unwrap) ⟫ /\
   ⟪ P_MEM_CLOS : Memory.closed_timemap (View.rlx p_rel.(View.unwrap))
                                        PC.(Configuration.memory) ⟫) /\
  ((⟪ NINRMW : ~ codom_rel (⦗ issued T ⦘ ⨾ rf ⨾ rmw) w ⟫ /\
    ⟪ PREL : p_rel = None ⟫) \/
   (exists p,
       ⟪ EP  : E p ⟫ /\
       ⟪ ISSP  : issued T p ⟫ /\
       ⟪ INRMW : (rf ⨾ rmw) p w ⟫ /\
       ⟪ P_LOC : loc lab p = Some locw ⟫ /\
       ⟪ P_MSG : sim_msg G sc f_to p p_rel.(View.unwrap) ⟫  /\
       exists p_v,
         ⟪ P_VAL : val lab p = Some p_v ⟫ /\
         ⟪ P_INMEM : Memory.get locw (f_to p) PC.(Configuration.memory) =
                     Some (f_from p, Message.full p_v p_rel) ⟫)).

(* TODO: move to a more appropriate place. *)
Lemma exists_wprev_rel w locw
      (WW : W w)
      (LOC : loc lab w = Some locw)
      (WTID : thread = tid w) :
  exists p_rel, rfrmw_prev_rel w locw p_rel.
Proof using WF SIM_MEM INHAB.
  clear SIM_RES_MEM SIM_TVIEW.
  subst.
  destruct (classic (codom_rel (⦗ issued T ⦘ ⨾ rf ⨾ rmw) w)) as [[wprev PRMWE]|].
  2: { eexists; split; [|by left; splits; eauto].
       simpls. splits; auto. by apply Memory.closed_timemap_bot. }
  destruct_seq_l PRMWE as ISSPREV.
  assert (E wprev) as EPREV.
  { apply WF.(wf_rfrmwE) in PRMWE. by destruct_seq PRMWE as [AA BB]. }
  assert (W wprev) as WPREV.
  { apply WF.(wf_rfrmwD) in PRMWE. by destruct_seq PRMWE as [AA BB]. }
  assert (loc lab wprev = Some locw) as PREVLOC.
  { rewrite <- LOC. by apply wf_rfrmwl. }
  assert (exists vprev, val lab wprev = Some vprev) as [vprev PREVVAL].
  { by apply is_w_val. }
  edestruct SIM_MEM as [p_rel REL]; simpls; desc.
  all: eauto.
  exists p_rel; red; splits; auto.
  right; exists wprev; splits; eauto.
  apply HELPER.
Qed.

(* TODO: move to a more appropriate place. *)
Lemma sim_helper_issue w locw valw f_to' f_from' (S' : actid -> Prop) p_rel
      (WLOC : loc lab w = Some locw)
      (WVAL : val lab w = Some valw)
      (WTID : thread = tid w)
      (ISSUABLE : issuable G sc T w)
      (WNCOV : ~ covered T w)
      (ISSEQ_TO : forall e (ISS: issued T e), f_to' e = f_to e)
      (SW : S' w)
      (IS : issued T ⊆₁ S')
      (FCOH' : f_to_coherent G S' f_to' f_from')
      (PREL : rfrmw_prev_rel w locw p_rel) :
  sim_mem_helper
    G sc f_to' w (f_from' w) valw
    (View.join (View.join (if is_rel lab w
                           then (TView.cur (Local.tview local))
                           else (TView.rel (Local.tview local) locw))
                          p_rel.(View.unwrap))
               (View.singleton_ur locw (f_to' w))).
Proof using WF IMMCON RELCOV ETCCOH SIM_MEM SIM_RES_MEM SIM_TVIEW.
  assert (tc_coherent G sc T) as TCCOH by apply ETCCOH.
  assert (E w /\ W w) as [EW WW].
  { split; apply ISSUABLE. }
  assert (~ is_init w) as NINIT.
  { intros HH. apply WNCOV. eapply init_covered; eauto. by split. }
  ins. red; splits; auto.
  { left. apply FCOH'; auto. }
  red; ins.
  eapply sim_tview_f_issued in SIM_TVIEW; eauto.
  cdes SIM_TVIEW. red in REL.
  unfold LocFun.find, TimeMap.join in *.
  eapply (@max_value_le_join
            _ _ _
            (if Loc.eq_dec l locw
             then W ∩₁ (fun x => loc lab x = Some locw)
                    ∩₁ Tid_ (tid w) ∩₁ covered T
             else ∅)).
  { intros x XX; destruct (Loc.eq_dec l locw); [subst|by desf].
    destruct XX as [[[WX LOCX] TIDX] COVX].
    eapply TimeFacts.lt_le_lt; [|apply Time.join_r].
    unfold TimeMap.singleton, LocFun.add; rewrite Loc.eq_dec_eq.
    assert (co x w) as COXW.
    { apply coi_union_coe; left.
      apply w_sb_loc_w_in_coi; auto.
      { apply coherence_sc_per_loc. apply IMMCON. }
      apply seq_eqv_l; split; [done|].
      apply seq_eqv_r; split; [|done].
      split; [|by red; rewrite LOCX].
      edestruct same_thread as [[EQ|SB]|SB].
      { apply EW. }
      { apply TCCOH in COVX. apply COVX. }
      all: auto.
      { desf. }
      exfalso. apply TCCOH in COVX. destruct COVX as [[_ C] _].
      apply WNCOV. apply C. eexists; apply seq_eqv_r; eauto. }
    eapply f_to_co_mon; eauto.
    apply IS. eapply w_covered_issued; eauto. by split. }
  eapply max_value_same_set.
  2: { arewrite ((fun a => msg_rel l a w \/
                           loc lab w = Some l /\ a = w) ≡₁
                  dom_rel (msg_rel l ⨾ ⦗ eq w ⦘) ∪₁
                  (fun x => loc lab x = Some l) ∩₁ eq w).
       { rewrite <- dom_rel_fun_alt. basic_solver. }
       rewrite set_unionA.
       rewrite (set_unionC ((fun x => loc lab x = Some l) ∩₁ eq w)).
       rewrite <- set_unionA.
       reflexivity. }
  cdes IMMCON.
  eapply max_value_same_set.
  2: by rewrite (msg_rel_alt2 WF TCCOH); eauto.
  eapply max_value_same_set.
  2: { arewrite ((if Rel w
                  then t_cur G sc (tid w) l (covered T)
                  else t_rel G sc (tid w) l locw (covered T)) ∪₁
                       dom_rel (msg_rel l ⨾ (rf ⨾ rmw) ⨾ ⦗eq w⦘) ∪₁
                       Rel ∩₁ Loc_ l ∩₁ eq w ∪₁
                       (if Loc.eq_dec l locw
                        then W ∩₁ Loc_ locw ∩₁ Tid_ (tid w) ∩₁ covered T
                        else ∅) ∪₁
                       Loc_ l ∩₁ eq w ≡₁
                       (if Rel w
                        then t_cur G sc (tid w) l (covered T)
                        else t_rel G sc (tid w) l locw (covered T)) ∪₁
                       dom_rel (msg_rel l ⨾ (rf ⨾ rmw) ⨾ ⦗eq w⦘) ∪₁
                       (if Loc.eq_dec l locw
                        then W ∩₁ Loc_ locw ∩₁ Tid_ (tid w) ∩₁ covered T
                        else ∅) ∪₁
                       Loc_ l ∩₁ eq w).
       2: reflexivity.
       basic_solver 40. }
  assert (max_value
            f_to' ((if Rel w
                    then t_cur G sc (tid w) l (covered T)
                    else t_rel G sc (tid w) l locw (covered T)) ∪₁
                         (if Loc.eq_dec l locw
                          then W ∩₁ Loc_ locw ∩₁ Tid_ (tid w) ∩₁ covered T
                          else ∅))
            (View.rlx (if Rel w
                       then TView.cur (Local.tview local)
                       else TView.rel (Local.tview local) locw) l)) as JJ.
  { rewrite !WTID in *.
    destruct (Rel w); simpls.
    eapply max_value_same_set; eauto.
    apply set_union_absorb_r.
    destruct (Loc.eq_dec l locw) as [EQ|NEQ]; simpls; subst.
    unfold t_cur, c_cur.
    generalize (@urr_refl G sc locw).
    basic_solver 40. }
  assert (max_value f_to' (Loc_ l ∩₁ eq w)
                    (TimeMap.singleton locw (f_to' w) l)) as KK.
  { unfold TimeMap.singleton, LocFun.add, LocFun.find.
    destruct (Loc.eq_dec l locw) as [|NEQ]; [subst|].
    { eapply max_value_same_set.
      { apply max_value_singleton; eauto. }
      basic_solver. }
    eapply max_value_same_set.
    { apply max_value_empty.
      intros x H. apply H. }
    basic_solver. }

  red in PREL. desc.
  destruct PREL0 as [PP|PP]; desc; subst. 
  { eapply max_value_join; [ | by apply KK | reflexivity].
    assert (rf ⨾ rmw ⨾ ⦗eq w⦘ ≡ ∅₂) as TT.
    { split; [|done].
      arewrite (⦗eq w⦘ ⊆ ⦗issuable G sc T⦘ ;; ⦗eq w⦘).
      { generalize ISSUABLE. clear. basic_solver. }
      arewrite (rf ⨾ rmw ⨾ ⦗issuable G sc T⦘ ⊆ ⦗issued T⦘ ;; rf ⨾ rmw ⨾ ⦗issuable G sc T⦘).
      { eapply dom_rel_helper_in. by apply dom_rfrmw_issuable_in_I. }
      generalize NINRMW. clear. basic_solver 10. }
    assert ((if Rel w
             then t_cur G sc (tid w) l (covered T)
             else t_rel G sc (tid w) l locw (covered T)) ∪₁
                  dom_rel (msg_rel l ⨾ (rf ⨾ rmw) ⨾ ⦗eq w⦘) ≡₁
                  (if Rel w
                   then t_cur G sc (tid w) l (covered T)
                   else t_rel G sc (tid w) l locw (covered T))) as SS.
    { rewrite !seqA. seq_rewrite TT.
      arewrite (dom_rel (msg_rel l ⨾ ∅₂) ≡₁ ∅).
      { basic_solver. }
      apply set_union_empty_r. }
    eapply max_value_same_set.
    2: { rewrite !seqA in SS. by rewrite SS. }
    simpls. unfold TimeMap.bot.
    rewrite time_join_bot_r.
    apply JJ. }
  edestruct SIM_MEM as [p_rel' H]; simpls; desc.
  { apply ISSP. }
  all: eauto.
  assert (dom_rel (msg_rel l ⨾ (rf ⨾ rmw) ⨾ ⦗eq w⦘) ≡₁
                  dom_rel (msg_rel l ⨾ ⦗eq p⦘)) as YY.
  { rewrite <- dom_rel_eqv_dom_rel.
    arewrite (dom_rel ((rf ⨾ rmw) ⨾ ⦗eq w⦘) ≡₁ eq p); [|done].
    split.
    2: { generalize INRMW. basic_solver 30. }
    intros x [y H]. apply seq_eqv_r in H.
    eapply wf_rfrmwf; eauto; desf. }
  eapply max_value_same_set.
  2: { rewrite seqA in YY; by rewrite YY. }
  apply (@max_value_le_join _ _ _ (Loc_ l ∩₁ (eq p))).
  { intros x [XL]; subst. apply time_lt_join_r.
    unfold TimeMap.singleton, LocFun.add.
    assert (l = locw); subst.
    { erewrite wf_rfrmwl in XL; eauto.
      rewrite WLOC in XL. by inv XL. }
    rewrite Loc.eq_dec_eq. eapply f_to_co_mon; eauto.
    eapply rfrmw_in_im_co; eauto. }
  assert
  ((if Rel w then
      t_cur G sc (tid w) l (covered T)
    else t_rel G sc (tid w) l locw (covered T)) ∪₁
          dom_rel (msg_rel l ⨾ ⦗eq p⦘) ∪₁
          (if Loc.eq_dec l locw
           then W ∩₁ Loc_ locw ∩₁ Tid_ (tid w) ∩₁ covered T else ∅) ∪₁
          Loc_ l ∩₁ eq w ∪₁ Loc_ l ∩₁ eq p ≡₁
          (if Rel w then
             t_cur G sc (tid w) l (covered T)
           else t_rel G sc (tid w) l locw (covered T)) ∪₁
          (if Loc.eq_dec l locw then W ∩₁ Loc_ locw ∩₁ Tid_ (tid w) ∩₁ covered T else ∅) ∪₁
          (dom_rel (msg_rel l ⨾ ⦗eq p⦘) ∪₁ Loc_ l ∩₁ eq p) ∪₁
          Loc_ l ∩₁ eq w) as YYY.
  { basic_solver 40. }
  eapply max_value_same_set; [| by apply YYY].
  eapply max_value_join; [ | by apply KK | reflexivity].
  eapply max_value_join; [by apply JJ | | reflexivity].
  rewrite INMEM in P_INMEM; inv P_INMEM.
  eapply sim_mem_helper_f_issued in HELPER; eauto.
  cdes HELPER. red in SIMMSG. unfold LocFun.find in SIMMSG.
  eapply max_value_same_set; [by apply SIMMSG|].
  basic_solver 10.
Qed.

(* TODO: move to more appropriate place. *)
Lemma le_cur_f_to_wprev w locw wprev
      (WNISS : ~ issued T w)
      (ISSUABLE : issuable G sc T w)
      (SW : S w)
      (PRMWE : (rf ;; rmw) wprev w)
      (LOC : loc lab w = Some locw)
      (WTID : thread = tid w) :
  let promises := local.(Local.promises) in
  let memory   := PC.(Configuration.memory) in
  DenseOrder.le (View.rlx (TView.cur (Local.tview local)) locw) (f_to wprev).
Proof using WF SIM_TVIEW SIM_RES_MEM SIM_MEM RELCOV IMMCON FCOH ETCCOH.
  assert (sc_per_loc G) as SPL.
  { apply coherence_sc_per_loc. apply IMMCON. }
  assert (complete G) as COMPL by apply IMMCON.
  assert (tc_coherent G sc T) as TCCOH by apply ETCCOH.

  assert (E w) as EW.
  { by apply ETCCOH.(etc_S_in_E). }
  assert (W w) as WW.
  { by apply (reservedW WF ETCCOH). }
  
  assert (~ covered T w) as WNCOV.
  { intros HH. apply WNISS.
    eapply w_covered_issued; [by apply ETCCOH|by split]. }
  assert (~ is_init w) as WNINIT.
  { intros HH. apply WNCOV. eapply init_covered; [by apply ETCCOH| by split]. }

  assert (W_ex w) as WEXW.
  { apply ETCCOH. by split. }

  assert ((E ∩₁ W ∩₁ Loc_ locw) w) as WEW.
  { split; [split|]; auto. }

  assert (E wprev) as EPREV.
  { apply WF.(wf_rfrmwE) in PRMWE. by destruct_seq PRMWE as [AA BB]. }
  assert (W wprev) as WPREV.
  { apply WF.(wf_rfrmwD) in PRMWE. by destruct_seq PRMWE as [AA BB]. }
  
  assert (wprev <> w) as NEQPREV.
  { intros HH; subst. eapply wf_rfrmw_irr; eauto. }

  assert (loc lab wprev = Some locw) as PREVLOC.
  { rewrite <- LOC. by apply WF.(wf_rfrmwl). }

  assert (issued T wprev) as ISSPREV.
  { eapply dom_rf_rmw_S_in_I with (T:=mkETC T S); eauto.
    generalize PRMWE SW. clear. basic_solver 10. }

  assert (S wprev) as SPREV.
  { by apply ETCCOH.(etc_I_in_S). }
  
  assert (dom_rel (rf ⨾ rmw ⨾ ⦗eq w⦘) ⊆₁ S) as DRFRMWS.
  { intros x [y HH]. apply seqA in HH. destruct_seq_r HH as AA; subst.
    assert (x = wprev); desf.
    eapply wf_rfrmwf; eauto. }
  assert (immediate (⦗S⦘ ⨾ co) wprev w) as IMMSPREV.
  { eapply (rfrmwP_in_immPco WF IMMCON) with (P':=eq w); auto.
    apply seqA. basic_solver. }

  cdes SIM_TVIEW. cdes CUR.
  eapply max_value_leS with (w:=w).
  9: by apply CUR0.
  all: eauto.
  { intros HH. apply WNISS. eapply t_cur_covered; eauto. }
  { unfold t_cur, c_cur, CombRelations.urr.
    rewrite !seqA. rewrite dom_eqv1.
      by intros x [[_ YY]]. }
  { erewrite t_cur_covered; eauto. apply ETCCOH. }
  split; [|basic_solver].
  intros x y QQ. apply seq_eqv_l in QQ. destruct QQ as [QQ' QQ]; subst.
  apply seq_eqv_r in QQ. destruct QQ as [COXY TCUR].
  red in TCUR. destruct TCUR as [z CCUR]. red in CCUR.
  hahn_rewrite <- seqA in CCUR.
  apply seq_eqv_r in CCUR. destruct CCUR as [URR COVZ].
  apply seq_eqv_r in URR. destruct URR as [URR II].
  eapply eco_urr_irr with (sc:=sc); eauto.
  1-3: by apply IMMCON.
  exists y. split.
  { apply co_in_eco. apply COXY. }
  apply urr_hb. exists z. split; eauto.
  right. apply sb_in_hb.
  assert (E z) as EZ.
  { apply TCCOH in COVZ. apply COVZ. }
  destruct II as [TIDZ|INITZ].
  2: by apply init_ninit_sb; auto.
  destruct (@same_thread G x z) as [[|SB]|SB]; auto.
  { desf. }
  exfalso. apply WNCOV. apply TCCOH in COVZ.
  apply COVZ. eexists. apply seq_eqv_r; eauto.
Qed.

(* TODO: move to more appropriate place. *)
Lemma le_p_rel_f_to_wprev w locw wprev p_rel
      (WNISS : ~ issued T w)
      (ISSUABLE : issuable G sc T w)
      (SW : S w)
      (PRMWE : (rf ;; rmw) wprev w)
      (LOC : loc lab w = Some locw)
      (WTID : thread = tid w)
      (PRELSPEC : rfrmw_prev_rel w locw p_rel) :
  let promises := local.(Local.promises) in
  let memory   := PC.(Configuration.memory) in
  DenseOrder.le (View.rlx (View.unwrap p_rel) locw) (f_to wprev).
Proof using WF SIM_TVIEW SIM_RES_MEM SIM_MEM RELCOV IMMCON FCOH ETCCOH.
  assert (sc_per_loc G) as SPL.
  { apply coherence_sc_per_loc. apply IMMCON. }
  assert (complete G) as COMPL by apply IMMCON.
  assert (tc_coherent G sc T) as TCCOH by apply ETCCOH.

  assert (issued T wprev) as ISSPREV.
  { eapply dom_rf_rmw_S_in_I with (T:=mkETC T S); eauto.
    generalize PRMWE SW. clear. basic_solver 10. }

  assert (S wprev) as SPREV.
  { by apply ETCCOH.(etc_I_in_S). }

  assert (co wprev w) as COWPREV.
  { eapply rf_rmw_in_co; eauto. }

  assert (dom_rel (rf ⨾ rmw ⨾ ⦗eq w⦘) ⊆₁ S) as DRFRMWS.
  { intros x [y HH]. apply seqA in HH. destruct_seq_r HH as AA; subst.
    assert (x = wprev); desf.
    eapply wf_rfrmwf; eauto. }
  assert (immediate (⦗S⦘ ⨾ co) wprev w) as IMMSPREV.
  { eapply (rfrmwP_in_immPco WF IMMCON) with (P':=eq w); auto.
    apply seqA. basic_solver. }

  red in PRELSPEC.
  set (rel'' :=
         if Rel w
         then TView.cur (Local.tview local)
         else TView.rel (Local.tview local) locw).
  set (rel' := View.join (View.join rel'' (View.unwrap p_rel))
                         (View.singleton_ur locw (f_to w))).
  desc.
  destruct PRELSPEC0; desc.
  { exfalso. apply NINRMW. generalize PRMWE ISSPREV. clear. basic_solver 10. }
  assert (p = wprev); subst.
  { eapply wf_rfrmwf; eauto. }
  cdes SIM_TVIEW. cdes CUR.
  eapply max_value_leS with (w:=w).
  9: by apply P_MSG.
  all: eauto.
  { intros [AA|AA].
    2: { desc. subst. eapply co_irr; eauto. }
    eapply msg_rel_co_irr; eauto.
    eexists; eauto. }
  { unionL; [|clear; basic_solver].
    (* TODO: introduce msg_relD lemma. *)
    unfold CombRelations.msg_rel.
    intros x [y [HH _]]. eapply wf_urrD in HH.
    destruct_seq_l HH as AA. apply AA. }
  { unionL.
    2: { generalize SPREV. clear. basic_solver. }
    (* TODO: introduce a lemma *)
    etransitivity.
    2: by apply ETCCOH.(etc_I_in_S).
    intros x HH.
    eapply msg_rel_issued; eauto.
    eexists. apply seq_eqv_r. split; eauto. }
  split; [|basic_solver].
  intros x y QQ. destruct_seq QQ as [COXY TCUR].
  destruct TCUR as [TCUR|[AA TCUR]]; subst.
  2: { eapply co_irr; eauto. eapply co_trans; eauto. }
  eapply msg_rel_co_irr; eauto.
  eexists; split; eauto.
  eapply co_trans; eauto.
Qed.

(* In the correspoding case, we don't reserve new events
   so the simulation may proceed with the same timestamp mapping functions,
   i.e. f_to' = f_to /\ f_from' = f_from *)
Lemma exists_time_interval_for_issue_reserved_no_next
      w locw valw langst smode
      (TSTEP : ext_itrav_step
                 G sc w (mkETC T S)
                 (mkETC
                    (mkTC (covered T) (issued T ∪₁ eq w))
                    (S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G (mkETC T S) rfi (eq w))))
      (SW : S w)
      (NONEXT : dom_sb_S_rfrmw G (mkETC T S) rfi (eq w) ⊆₁ ∅)
      (LOC : loc lab w = Some locw)
      (VAL : val lab w = Some valw)
      (WTID : thread = tid w)
      (RESERVED_TIME: reserved_time G T S f_to f_from smode PC.(Configuration.memory))
      (TID : IdentMap.find (tid w) PC.(Configuration.threads) = Some (langst, local)) :
  let promises := local.(Local.promises) in
  let memory   := PC.(Configuration.memory) in
  let T'       := mkTC (covered T) (issued T ∪₁ eq w) in
  let S'       := S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G (mkETC T S) rfi (eq w) in
  exists p_rel, rfrmw_prev_rel w locw p_rel /\
    let rel'' :=
        if is_rel lab w
        then (TView.cur (Local.tview local))
        else (TView.rel (Local.tview local) locw)
    in
    let rel' := (View.join (View.join rel'' p_rel.(View.unwrap))
                           (View.singleton_ur locw (f_to w))) in
    << RELWFEQ : View.pln rel' = View.rlx rel' >> /\
    ⟪ REL_VIEW_LT : Time.lt (View.rlx rel'' locw) (f_to w) ⟫ /\
    ⟪ REL_VIEW_LE : Time.le (View.rlx rel' locw) (f_to w) ⟫ /\


    exists promises_cancel memory_cancel,
      ⟪ PCANCEL :
          Memory.remove promises locw (f_from w) (f_to w)
                        Message.reserve promises_cancel ⟫ /\
      ⟪ MCANCEL :
          Memory.remove memory locw (f_from w) (f_to w)
                        Message.reserve memory_cancel ⟫ /\

      exists promises_add memory_add,
        ⟪ PADD :
            Memory.add promises_cancel locw (f_from w) (f_to w)
                       (Message.full valw (Some rel')) promises_add ⟫ /\
        ⟪ MADD :
            Memory.add memory_cancel locw (f_from w) (f_to w)
                       (Message.full valw (Some rel')) memory_add ⟫ /\

        << INHAB : Memory.inhabited memory_add >> /\
        << RELMCLOS : Memory.closed_timemap (View.rlx rel') memory_add >> /\
        << RELVCLOS : Memory.closed_view rel' memory_add >> /\

        ⟪ FCOH : f_to_coherent G S' f_to f_from ⟫ /\

        ⟪ HELPER :
            sim_mem_helper
              G sc f_to w (f_from w) valw
              (View.join (View.join (if is_rel lab w
                                     then (TView.cur (Local.tview local))
                                     else (TView.rel (Local.tview local) locw))
                                    p_rel.(View.unwrap))
                         (View.singleton_ur locw (f_to w))) ⟫ /\

        ⟪ RESERVED_TIME :
            reserved_time G T' S' f_to f_from smode memory_add ⟫.
Proof using WF IMMCON ETCCOH RELCOV FCOH SIM_TVIEW SIM_RES_MEM SIM_MEM INHAB PLN_RLX_EQ MEM_CLOSE PROM_IN_MEM.
  assert (sc_per_loc G) as SPL.
  { apply coherence_sc_per_loc. apply IMMCON. }
  assert (complete G) as COMPL by apply IMMCON.
  assert (tc_coherent G sc T) as TCCOH by apply ETCCOH.

  set (AA:=TSTEP).
  destruct AA as [_ ETCCOH'].

  assert (E w) as EW.
  { by apply ETCCOH.(etc_S_in_E). }
  assert (W w) as WW.
  { by apply (reservedW WF ETCCOH). }
  
  assert (~ issued T w) as WNISS.
  { eapply ext_itrav_step_iss_nI with (T:=mkETC T S); eauto. }
  assert (~ covered T w) as WNCOV.
  { intros HH. apply WNISS.
    eapply w_covered_issued; [by apply ETCCOH|by split]. }
  assert (~ is_init w) as WNINIT.
  { intros HH. apply WNCOV. eapply init_covered; [by apply ETCCOH| by split]. }

  assert (issuable G sc T w) as ISSUABLE.
  { eapply ext_itrav_step_iss_issuable with (T:=mkETC T S); eauto. }

  assert (W_ex w) as WEXW.
  { apply ETCCOH. by split. }

  assert ((E ∩₁ W ∩₁ Loc_ locw) w) as WEW.
  { split; [split|]; auto. }

  assert (codom_rel (rf ⨾ rmw) w) as [wprev PRMWE].
  { eapply W_ex_in_codom_rfrmw; eauto. }
  
  assert (E wprev) as EPREV.
  { apply WF.(wf_rfrmwE) in PRMWE. by destruct_seq PRMWE as [AA BB]. }
  assert (W wprev) as WPREV.
  { apply WF.(wf_rfrmwD) in PRMWE. by destruct_seq PRMWE as [AA BB]. }
  
  assert (wprev <> w) as NEQPREV.
  { intros HH; subst. eapply wf_rfrmw_irr; eauto. }

  assert (loc lab wprev = Some locw) as PREVLOC.
  { rewrite <- LOC. by apply WF.(wf_rfrmwl). }

  assert (issued T wprev) as ISSPREV.
  { assert ((issued T ∪₁ eq w) wprev) as AA.
    2: by destruct AA; desf.
    eapply (dom_rf_rmw_S_in_I WF ETCCOH').
    exists w. apply seqA. apply seq_eqv_r. split; auto.
    basic_solver. }
  assert (S wprev) as SPREV.
  { by apply ETCCOH.(etc_I_in_S). }
  
  assert (dom_rel (rf ⨾ rmw ⨾ ⦗eq w⦘) ⊆₁ S) as DRFRMWS.
  { intros x [y HH]. apply seqA in HH. destruct_seq_r HH as AA; subst.
    assert (x = wprev); desf.
    eapply wf_rfrmwf; eauto. }
  assert (immediate (⦗S⦘ ⨾ co) wprev w) as IMMSPREV.
  { eapply (rfrmwP_in_immPco WF IMMCON) with (P':=eq w); auto.
    apply seqA. basic_solver. }

  assert (exists vprev, val lab wprev = Some vprev) as [vprev PREVVAL] by (by apply is_w_val).

  edestruct exists_wprev_rel with (w:=w) as [p_rel PRELSPEC]; eauto.
  
  exists p_rel. split.
  { apply PRELSPEC. }

  red in PRELSPEC.
  set (rel'' :=
         if Rel w
         then TView.cur (Local.tview local)
         else TView.rel (Local.tview local) locw).
  
  assert (co wprev w) as COWPREV.
  { eapply rf_rmw_in_co; eauto. }
  assert (Time.lt (f_to wprev) (f_to w)) as PREVNLT.
  { eapply f_to_co_mon; eauto. }

  assert (Time.le (View.rlx rel'' locw)
                  (View.rlx (TView.cur (Local.tview local)) locw)) as GG.
  { unfold rel''. destruct (Rel w).
    { reflexivity. }
    subst. eapply rel_le_cur; eauto. }

  assert (Time.lt (View.rlx rel'' locw) (f_to w)) as REL_VIEW_LT.
  { eapply TimeFacts.le_lt_lt; [by apply GG|].
    eapply TimeFacts.le_lt_lt; [|by apply PREVNLT].
    eapply le_cur_f_to_wprev; eauto. }

  set (rel' := View.join (View.join rel'' (View.unwrap p_rel))
                         (View.singleton_ur locw (f_to w))).
  assert (Time.le (View.rlx (View.unwrap p_rel) locw) (f_to wprev)) as PREL_LE'.
  { eapply le_p_rel_f_to_wprev; eauto. }
  assert (Time.le (View.rlx (View.unwrap p_rel) locw) (f_to w)) as PREL_LE.
  { desc.
    destruct PRELSPEC0; desc.
    { rewrite PREL. apply Time.bot_spec. }
    assert (p = wprev); subst.
    { eapply wf_rfrmwf; eauto. }
    apply Time.le_lteq. left.
    eapply TimeFacts.le_lt_lt.
    2: by apply PREVNLT.
    done. }

  assert (Time.le (View.rlx rel' locw) (f_to w)) as REL_VIEW_LE.
  { unfold rel'.
    unfold View.join, TimeMap.join. simpls.
    unfold TimeMap.singleton, LocFun.add.
    rewrite Loc.eq_dec_eq.
    apply Time.join_spec; [|reflexivity].
    apply Time.join_spec; auto.
    apply Time.le_lteq; auto. }
    
  assert (Memory.get locw (f_to w) (Local.promises local) =
          Some (f_from w, Message.reserve)) as PMSG.
  { eapply SIM_RES_MEM; eauto. }
  assert (exists promises_cancel,
             Memory.remove (Local.promises local) locw
                           (f_from w) (f_to w) Message.reserve promises_cancel)
    as [promises_cancel PCANCEL].
  { by apply Memory.remove_exists. }

  assert (Memory.get locw (f_to w) (Configuration.memory PC) =
          Some (f_from w, Message.reserve)) as MMSG.
  { eapply SIM_RES_MEM; eauto. }
  assert (exists memory_cancel,
             Memory.remove
               PC.(Configuration.memory) locw (f_from w) (f_to w)
                                         Message.reserve memory_cancel)
    as [memory_cancel MCANCEL].
  { by apply Memory.remove_exists. }

  assert (Time.lt (f_from w) (f_to w)) as WFLT by (by apply FCOH).

  assert (View.pln rel' = View.rlx rel') as RELWFEQ.
  { unfold rel'. simpls. desc. rewrite REL_PLN_RLX.
    arewrite (View.pln rel'' = View.rlx rel'').
    2: reflexivity.
    unfold rel''. destruct (Rel w); apply PLN_RLX_EQ. }
  assert (View.opt_wf (Some rel')) as RELWF.
  { apply opt_wf_unwrap. simpls.
    constructor. 
    arewrite (View.pln rel' = View.rlx rel').
    apply TimeMap.le_PreOrder. }
  
  simpls. splits; eauto.
  do 2 eexists. splits; eauto.

  assert (Message.wf (Message.full valw (Some rel'))) as MWF by (by constructor).

  assert (exists promises_add,
             Memory.add promises_cancel locw
                        (f_from w) (f_to w) (Message.full valw (Some rel'))
                        promises_add)
    as [promises_add PADD].
  { apply Memory.add_exists; auto.
    (* TODO: generalize to a lemma. *)
    ins.
    erewrite Memory.remove_o in GET2; eauto.
    destruct (loc_ts_eq_dec (locw, to2) (locw, f_to w)) as [LTEQ|LTNEQ].
    { simpls. desc; subst.
      rewrite (loc_ts_eq_dec_eq locw (f_to w)) in GET2. inv GET2. }
    rewrite loc_ts_eq_dec_neq in GET2; eauto.
    edestruct Memory.get_disjoint with (t1:=f_to w) (t2:=to2)
                                       (m:=Local.promises local); eauto.
    desf. }
  assert (exists memory_add,
             Memory.add memory_cancel locw
                        (f_from w) (f_to w) (Message.full valw (Some rel'))
                        memory_add)
    as [memory_add MADD].
  { apply Memory.add_exists; auto.
    (* TODO: generalize to a lemma. *)
    ins.
    erewrite Memory.remove_o in GET2; eauto.
    destruct (loc_ts_eq_dec (locw, to2) (locw, f_to w)) as [LTEQ|LTNEQ].
    { simpls. desc; subst.
      rewrite (loc_ts_eq_dec_eq locw (f_to w)) in GET2. inv GET2. }
    rewrite loc_ts_eq_dec_neq in GET2; eauto.
    edestruct Memory.get_disjoint with (t1:=f_to w) (t2:=to2)
                                       (m:=PC.(Configuration.memory)); eauto.
    desf. }

  assert (Memory.inhabited memory_add) as INHABADD.
  { red. ins.
    erewrite Memory.add_o; eauto.
    erewrite Memory.remove_o; eauto.
    destruct (loc_ts_eq_dec (loc, Time.bot) (locw, f_to w)) as [AA|LL]; simpls; desc; subst.
    { exfalso. eapply time_lt_bot. rewrite AA0. by apply FCOH. }
    rewrite !(loc_ts_eq_dec_neq LL).
    apply INHAB. }

  assert (S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G (mkETC T S) rfi (eq w) ≡₁ S) as NEWS.
  { arewrite (dom_sb_S_rfrmw G (mkETC T S) rfi (eq w) ≡₁ ∅).
    generalize SW. basic_solver. }

  assert (reserved_time G (mkTC (covered T) (issued T ∪₁ eq w))
                        S f_to f_from smode memory_add) as REST.
  { destruct smode; [|by apply RESERVED_TIME].
    red. splits.
    3: by apply RESERVED_TIME.
    all: red; ins; erewrite Memory.add_o in MSG; eauto.
    all: destruct (loc_ts_eq_dec (l, to) (locw, f_to w)) as [LTEQ|LTNEQ].
    { simpls. desc; subst. right. exists w. splits; eauto.
      { clear. basic_solver. }
      rewrite (loc_ts_eq_dec_eq locw (f_to w)) in MSG. inv MSG. }
    { rewrite loc_ts_eq_dec_neq in MSG; eauto.
      erewrite Memory.remove_o in MSG; eauto.
      rewrite loc_ts_eq_dec_neq in MSG; eauto.
      eapply RESERVED_TIME in MSG.
      generalize MSG. clear. basic_solver 10. }
    { simpls. desc; subst. 
      rewrite (loc_ts_eq_dec_eq locw (f_to w)) in MSG. inv MSG. }
    rewrite loc_ts_eq_dec_neq in MSG; eauto.
    erewrite Memory.remove_o in MSG; eauto.
    rewrite loc_ts_eq_dec_neq in MSG; eauto.
    eapply RESERVED_TIME in MSG.
    desc. exists b. splits; eauto.
    intros [|AA]; [by desf|subst].
    simpls. destruct LTNEQ as [AA|AA]; apply AA; auto.
    rewrite LOC0 in LOC. inv LOC. }

  assert (forall tmap (MCLOS : Memory.closed_timemap tmap PC.(Configuration.memory)),
             Memory.closed_timemap tmap memory_add) as MADDCLOS.
  { ins. eapply Memory.add_closed_timemap; eauto.
    eapply Memory.cancel_closed_timemap; eauto. }

  assert (Memory.closed_timemap (View.rlx rel') memory_add) as RELMCLOS.
  { unfold rel'. simpls.
    apply Memory.join_closed_timemap.
    2: { unfold TimeMap.singleton, LocFun.add, LocFun.find.
         red. ins. destruct (Loc.eq_dec loc locw) as [|LNEQ]; subst.
         { erewrite Memory.add_o; eauto. rewrite loc_ts_eq_dec_eq. eauto. }
         unfold LocFun.init.
         exists Time.bot, 0, None. apply INHABADD. }
    apply MADDCLOS.
    desc. apply Memory.join_closed_timemap; auto.
    unfold rel''.
    destruct (Rel w); simpls.
    all: apply MEM_CLOSE. }
  do 2 eexists. splits; eauto.
  { constructor; auto. simpls. by rewrite RELWFEQ. }
  { by rewrite NEWS. }
  { eapply sim_helper_issue with (S':=S); eauto. apply ETCCOH. }
  eapply reserved_time_more.
  3: by apply NEWS.
  all: eauto.
  apply same_trav_config_refl.
Qed.

Lemma exists_time_interval_for_issue_reserved_with_next
      w locw valw langst wnext smode
      (TSTEP : ext_itrav_step
                 G sc w (mkETC T S)
                 (mkETC
                    (mkTC (covered T) (issued T ∪₁ eq w))
                    (S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G (mkETC T S) rfi (eq w))))
      (SW : S w)
      (WNEXT : dom_sb_S_rfrmw G (mkETC T S) rfi (eq w) wnext)
      (LOC : loc lab w = Some locw)
      (VAL : val lab w = Some valw)
      (WTID : thread = tid w)
      (RESERVED_TIME: reserved_time G T S f_to f_from smode PC.(Configuration.memory))
      (TID : IdentMap.find (tid w) PC.(Configuration.threads) = Some (langst, local)) :
  let promises := local.(Local.promises) in
  let memory   := PC.(Configuration.memory) in
  let T'       := mkTC (covered T) (issued T ∪₁ eq w) in
  let S'       := S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G (mkETC T S) rfi (eq w) in
  let n_to     := Time.middle (f_from w) (f_to w) in
  let f_to'    := upd (upd f_to w n_to) wnext (f_to w) in
  let f_from'  := upd f_from wnext n_to in

  exists p_rel, rfrmw_prev_rel w locw p_rel /\
    let rel'' :=
        if is_rel lab w
        then (TView.cur (Local.tview local))
        else (TView.rel (Local.tview local) locw)
    in
    let rel' := (View.join (View.join rel'' p_rel.(View.unwrap))
                           (View.singleton_ur locw (f_to' w))) in
    << RELWFEQ : View.pln rel' = View.rlx rel' >> /\
    ⟪ REL_VIEW_LT : Time.lt (View.rlx rel'' locw) (f_to' w) ⟫ /\
    ⟪ REL_VIEW_LE : Time.le (View.rlx rel'  locw) (f_to' w) ⟫ /\

    exists promises_split memory_split,
      ⟪ PSPLIT :
          Memory.split local.(Local.promises) locw (f_from' w) (f_to' w) (f_to' wnext)
                       (Message.full valw (Some rel')) Message.reserve promises_split ⟫ /\
      ⟪ MSPLIT :
          Memory.split memory locw (f_from' w) (f_to' w) (f_to' wnext)
                       (Message.full valw (Some rel')) Message.reserve memory_split ⟫ /\

      << INHAB : Memory.inhabited memory_split >> /\
      << RELMCLOS : Memory.closed_timemap (View.rlx rel') memory_split >> /\
      << RELVCLOS : Memory.closed_view rel' memory_split >> /\

      ⟪ FCOH : f_to_coherent G S' f_to' f_from' ⟫ /\

      ⟪ HELPER :
          sim_mem_helper
            G sc f_to' w (f_from' w) valw
            (View.join (View.join (if is_rel lab w
                                   then (TView.cur (Local.tview local))
                                   else (TView.rel (Local.tview local) locw))
                                  p_rel.(View.unwrap))
                       (View.singleton_ur locw (f_to' w))) ⟫ /\

      ⟪ RESERVED_TIME :
          reserved_time G T' S' f_to' f_from' smode memory_split ⟫.
Proof using WF IMMCON ETCCOH RELCOV FCOH SIM_TVIEW SIM_RES_MEM SIM_MEM INHAB PLN_RLX_EQ MEM_CLOSE PROM_IN_MEM.
  assert (sc_per_loc G) as SPL.
  { apply coherence_sc_per_loc. apply IMMCON. }
  assert (complete G) as COMPL by apply IMMCON.
  assert (tc_coherent G sc T) as TCCOH by apply ETCCOH.

  set (AA:=TSTEP).
  destruct AA as [_ ETCCOH'].

  assert (E w) as EW.
  { by apply ETCCOH.(etc_S_in_E). }
  assert (W w) as WW.
  { by apply (reservedW WF ETCCOH). }
  
  assert (~ issued T w) as WNISS.
  { eapply ext_itrav_step_iss_nI with (T:=mkETC T S); eauto. }
  assert (~ covered T w) as WNCOV.
  { intros HH. apply WNISS.
    eapply w_covered_issued; [by apply ETCCOH|by split]. }
  assert (~ is_init w) as WNINIT.
  { intros HH. apply WNCOV. eapply init_covered; [by apply ETCCOH| by split]. }

  assert (issuable G sc T w) as ISSUABLE.
  { eapply ext_itrav_step_iss_issuable with (T:=mkETC T S); eauto. }

  assert (W_ex w) as WEXW.
  { apply ETCCOH. by split. }

  assert ((E ∩₁ W ∩₁ Loc_ locw) w) as WEW.
  { split; [split|]; auto. }

  assert (codom_rel (rf ⨾ rmw) w) as [wprev PRMWE].
  { eapply W_ex_in_codom_rfrmw; eauto. }
  
  assert (E wprev) as EPREV.
  { apply WF.(wf_rfrmwE) in PRMWE. by destruct_seq PRMWE as [AA BB]. }
  assert (W wprev) as WPREV.
  { apply WF.(wf_rfrmwD) in PRMWE. by destruct_seq PRMWE as [AA BB]. }
  
  assert (wprev <> w) as NEQPREV.
  { intros HH; subst. eapply wf_rfrmw_irr; eauto. }

  assert (loc lab wprev = Some locw) as PREVLOC.
  { rewrite <- LOC. by apply WF.(wf_rfrmwl). }

  assert (issued T wprev) as ISSPREV.
  { assert ((issued T ∪₁ eq w) wprev) as AA.
    2: by destruct AA; desf.
    eapply (dom_rf_rmw_S_in_I WF ETCCOH').
    exists w. apply seqA. apply seq_eqv_r. split; auto.
    basic_solver. }
  assert (S wprev) as SPREV.
  { by apply ETCCOH.(etc_I_in_S). }
  
  assert (dom_rel (rf ⨾ rmw ⨾ ⦗eq w⦘) ⊆₁ S) as DRFRMWS.
  { intros x [y HH]. apply seqA in HH. destruct_seq_r HH as AA; subst.
    assert (x = wprev); desf.
    eapply wf_rfrmwf; eauto. }
  assert (immediate (⦗S⦘ ⨾ co) wprev w) as IMMSPREV.
  { eapply (rfrmwP_in_immPco WF IMMCON) with (P':=eq w); auto.
    apply seqA. basic_solver. }

  assert (exists vprev, val lab wprev = Some vprev) as [vprev PREVVAL] by (by apply is_w_val).

  edestruct exists_wprev_rel with (w:=w) as [p_rel PRELSPEC]; eauto.
  
  exists p_rel. split.
  { apply PRELSPEC. }

  red in PRELSPEC.
  set (rel'' :=
         if Rel w
         then TView.cur (Local.tview local)
         else TView.rel (Local.tview local) locw).
  
  assert (co wprev w) as COWPREV.
  { eapply rf_rmw_in_co; eauto. }
  assert (Time.lt (f_to wprev) (f_to w)) as PREVNLT_OLD.
  { eapply f_to_co_mon; eauto. }

  assert ((rf ⨾ rmw) w wnext) as RFRMWNEXT.
  { destruct WNEXT as [_ BB]. generalize BB. unfold Execution.rfi.
    clear. basic_solver. }
  assert (w <> wnext) as NEQ.
  { intros HH; subst. eapply wf_rfrmw_irr; eauto. }
  assert (co w wnext) as COWNEXT.
  { by apply rf_rmw_in_co. }
  assert (~ is_init wnext) as NINITNEXT.
  { apply no_co_to_init in COWNEXT; auto. by destruct_seq_r COWNEXT as AA. }
  assert (E wnext) as EWNEXT.
  { apply WF.(wf_coE) in COWNEXT. by destruct_seq COWNEXT as [AA BB]. }
  assert (~ S wnext) as NSNEXT.
  { intros HH. apply WNISS. eapply dom_rf_rmw_S_in_I with (T:=mkETC T S); eauto.
    exists wnext. apply seqA. apply seq_eqv_r. by split. }
  assert (~ issued T wnext) as NINEXT.
  { intros HH. apply NSNEXT. by apply ETCCOH.(etc_I_in_S). }
  assert (loc lab wnext = Some locw) as NLOC.
  { rewrite <- LOC. symmetry. by apply wf_rfrmwl. }

  set (n_to := Time.middle (f_from w) (f_to w)).
  set (f_to'   := upd (upd f_to w n_to) wnext (f_to w)).
  set (f_from' := upd f_from wnext n_to).

  assert (Time.lt (f_from w) (f_to w)) as WFLT by (by apply FCOH).
  assert (Time.lt (f_from w) (Time.middle (f_from w) (f_to w))) as FROMNTOLT.
  { by apply Time.middle_spec. }
  assert (Time.lt (Time.middle (f_from w) (f_to w)) (f_to w)) as NTOTOLT.
  { by apply Time.middle_spec. }

  assert (f_to wprev = f_from w) as PREVFEQ by (by apply FCOH).
  assert (Time.lt (f_to wprev) (f_to' w)) as PREVNLT.
  { unfold f_to'. rewrite updo; auto. rewrite upds.
    unfold n_to. eapply TimeFacts.le_lt_lt with (b:=f_from w); auto.
    rewrite PREVFEQ. apply DenseOrder_le_PreOrder. }

  assert (Time.le (View.rlx rel'' locw)
                  (View.rlx (TView.cur (Local.tview local)) locw)) as GG.
  { unfold rel''. destruct (Rel w).
    { reflexivity. }
    subst. eapply rel_le_cur; eauto. }

  assert (Time.lt (View.rlx rel'' locw) (f_to' w)) as REL_VIEW_LT.
  { eapply TimeFacts.le_lt_lt; [by apply GG|].
    eapply TimeFacts.le_lt_lt; [|by apply PREVNLT].
    eapply le_cur_f_to_wprev; eauto. }

  set (rel' := View.join (View.join rel'' (View.unwrap p_rel))
                         (View.singleton_ur locw (f_to' w))).
  assert (Time.le (View.rlx (View.unwrap p_rel) locw) (f_to wprev)) as PREL_LE'.
  { eapply le_p_rel_f_to_wprev; eauto. }
  assert (Time.le (View.rlx (View.unwrap p_rel) locw) (f_to' w)) as PREL_LE.
  { desc.
    destruct PRELSPEC0; desc.
    { rewrite PREL. apply Time.bot_spec. }
    assert (p = wprev); subst.
    { eapply wf_rfrmwf; eauto. }
    apply Time.le_lteq. left.
    eapply TimeFacts.le_lt_lt.
    2: by apply PREVNLT.
    done. }

  assert (Time.le (View.rlx rel' locw) (f_to' w)) as REL_VIEW_LE.
  { unfold rel'.
    unfold View.join, TimeMap.join. simpls.
    unfold TimeMap.singleton, LocFun.add.
    rewrite Loc.eq_dec_eq.
    apply Time.join_spec; [|reflexivity].
    apply Time.join_spec; auto.
    apply Time.le_lteq; auto. }

  assert (View.pln rel' = View.rlx rel') as RELWFEQ.
  { unfold rel'. simpls. desc. rewrite REL_PLN_RLX.
    arewrite (View.pln rel'' = View.rlx rel'').
    2: reflexivity.
    unfold rel''. destruct (Rel w); apply PLN_RLX_EQ. }
  assert (View.opt_wf (Some rel')) as RELWF.
  { apply opt_wf_unwrap. simpls.
    constructor. 
    arewrite (View.pln rel' = View.rlx rel').
    apply TimeMap.le_PreOrder. }

  assert (Message.wf (Message.full valw (Some rel'))) as MWF by (by constructor).

  assert (Memory.get locw (f_to w) (Local.promises local) =
          Some (f_from w, Message.reserve)) as PMSG.
  { eapply SIM_RES_MEM; eauto. }
  assert (exists promises_split,
             Memory.split (Local.promises local) locw
                          (f_from' w) (f_to' w) (f_to' wnext)
                          (Message.full valw (Some rel'))
                          Message.reserve promises_split)
    as [promises_split PSPLIT].
  { unfold f_from'. rewrite updo; auto.
    unfold f_to'. rewrite upds. rewrite updo; auto. rewrite upds.
      by apply Memory.split_exists. }
  
  assert (Memory.get locw (f_to w) (Configuration.memory PC) =
          Some (f_from w, Message.reserve)) as MMSG.
  { eapply SIM_RES_MEM; eauto. }
  assert (exists memory_split,
             Memory.split PC.(Configuration.memory) locw
                          (f_from' w) (f_to' w) (f_to' wnext)
                          (Message.full valw (Some rel'))
                          Message.reserve memory_split)
    as [memory_split MSPLIT].
  { unfold f_from'. rewrite updo; auto.
    unfold f_to'. rewrite upds. rewrite updo; auto. rewrite upds.
      by apply Memory.split_exists. }

  assert (forall tmap (MCLOS : Memory.closed_timemap tmap PC.(Configuration.memory)),
             Memory.closed_timemap tmap memory_split) as MSPLITCLOS.
  { ins. eapply Memory.split_closed_timemap; eauto. }

  assert (Memory.inhabited memory_split) as INHABSPLIT.
  { red. ins.
    erewrite Memory.split_o; eauto.
    destruct (loc_ts_eq_dec (loc, Time.bot) (locw, Time.middle (f_from w) (f_to w)))
      as [AA|LL]; simpls; desc; subst.
    { exfalso. eapply time_lt_bot. rewrite AA0.
        by do 2 (apply Time.middle_spec with (lhs:=f_from w)). }
    unfold f_to'. rewrite upds. rewrite updo; auto. rewrite upds.
    rewrite !(loc_ts_eq_dec_neq LL).
    destruct (loc_ts_eq_dec (loc, Time.bot) (locw, f_to w))
      as [AA|LL']; simpls; desc; subst.
    { exfalso. eapply time_lt_bot. rewrite AA0. by apply FCOH. }
    rewrite !(loc_ts_eq_dec_neq LL').
    apply INHAB. }

  assert (dom_sb_S_rfrmw G (mkETC T S) rfi (eq w) ≡₁ eq wnext) as NEWS'.
  { eapply dom_sb_S_rfrmw_single; eauto. }

  assert (S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G (mkETC T S) rfi (eq w) ≡₁ S ∪₁ eq wnext) as NEWS.
  { rewrite NEWS'. generalize SW. clear. basic_solver. }

  splits; eauto. eexists promises_split, memory_split.
  
  (* TODO: generalize to a lemma. *)
  assert (f_to_coherent
            G (S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G {| etc_TC := T; reserved := S |} rfi (eq w))
            f_to' f_from') as FCOH'.
  { eapply f_to_coherent_more.
    2: by apply NEWS.
    all: eauto.
    red. splits; unfold f_to', f_from', n_to.
    1,2: intros x [IE EX].
    1,2: repeat (rewrite updo; [|by intros HH; desf]).
    1,2: by apply FCOH; split.
    { intros x [SX|] IE; subst.
      2: by rewrite !upds.
      do 2 (rewrite updo; [|by intros HH; desf]).
      destruct (classic (x = w)); subst.
      { by rewrite upds. }
      rewrite updo; auto. by apply FCOH. }
    { intros x y SX SY CO; subst.
      assert (x <> y) as NEQXY.
      { intros HH; subst. eapply co_irr; eauto. }
      destruct SX as [SX|]; destruct SY as [SY|]; subst.
      4: by exfalso; eapply co_irr; eauto.
      3: { rewrite upds. rewrite updo; auto.
           apply FCOH; eauto. eapply co_trans; eauto. }
      { rewrite updo; [|by intros HH; desf].
        rewrite updo with (a:=wnext); [|by intros HH; desf].
        destruct (classic (x = w)); subst.
        { rewrite upds.
          etransitivity.
          { apply Time.le_lteq.
            left. by apply Time.middle_spec with (lhs:=f_from w) (rhs:=f_to w). }
            by apply FCOH. }
        rewrite updo; auto. by apply FCOH. }
      rewrite upds. rewrite updo; auto.
      destruct (classic (x = w)); subst.
      { rewrite upds. apply DenseOrder_le_PreOrder. }
      rewrite updo; auto.
      etransitivity.
      2: { apply Time.le_lteq.
           left. by apply Time.middle_spec with (lhs:=f_from w) (rhs:=f_to w). }
      apply FCOH; auto.
      admit. }
    intros x y SX SY CO; subst.
    assert (x <> y) as NEQXY.
    { intros HH; subst. eapply wf_rfrmw_irr; eauto. }
    cdes FCOH.
    destruct SX as [SX|]; destruct SY as [SY|]; subst; try done.
    3: { rewrite upds. rewrite updo; auto.
         exfalso. apply NSNEXT. eapply dom_rf_rmw_S with (T:=mkETC T S); eauto.
         exists y. apply seqA. apply seq_eqv_r. by split. }
    { rewrite updo; [|by intros HH; desf].
      rewrite updo with (a:=wnext); [|by intros HH; desf].
      destruct (classic (x = w)); subst.
      2: by rewrite updo; auto.
      exfalso.
      assert (y = wnext); [|by desf].
      eapply wf_rfrmwsf; eauto. }
    rewrite upds. rewrite updo; auto.
    assert (x = w); [|by subst; rewrite upds].
    eapply wf_rfrmwf; eauto. }

  (* TODO: generalize to a lemma. *)
  assert (reserved_time G (mkTC (covered T) (issued T ∪₁ eq w))
                        (S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G (mkETC T S) rfi (eq w))
                        f_to' f_from' smode memory_split) as REST.
  { eapply reserved_time_more.
    3: by apply NEWS.
    all: eauto.
    { apply same_tc. }
    destruct smode; simpls; desc.
    2: { splits.
         { generalize FOR_SPLIT. clear. basic_solver 10. }
         rewrite RMW_BEF_S. clear. basic_solver 10. }
    splits.
    3: { intros x y SX SY CO; subst.
         assert (x <> y) as NEQXY.
         { intros HH; subst. eapply co_irr; eauto. }
         unfold f_to', f_from'.
         destruct SX as [SX|]; destruct SY as [SY|]; subst; try done.
         { repeat (rewrite updo with (a:=wnext); [|by intros HH; desf]).
           destruct (classic (x = w)) as [|NEQXW]; subst;
             [rewrite upds|by rewrite updo; auto].
           unfold n_to. intros HH.
           exfalso.
           admit. }
         { rewrite upds. rewrite updo; auto.
           destruct (classic (x = w)) as [|NEQXW]; subst; auto.
           rewrite updo; auto. intros HH.
           exfalso.
           admit. }
         rewrite upds. rewrite updo; auto.
         intros HH.
         exfalso.
         apply TFRMW in HH; auto.
         2: { eapply co_trans; eauto. }
         apply NEQXY. eapply wf_rfrmwsf; eauto. }
    all: red; ins; erewrite Memory.split_o in MSG; eauto; unfold f_to', f_from' in *.
    all: rewrite updo in MSG; auto; rewrite upds in MSG.
    all: destruct (loc_ts_eq_dec (l, to) (locw, n_to)) as [LTEQ|LTNEQ].
    { simpls. desc; subst. right.
      rewrite (loc_ts_eq_dec_eq locw n_to) in MSG. inv MSG.
      exists w. splits; eauto.
      { by right. }
      rewrite updo; auto. by rewrite upds. }
    { rewrite loc_ts_eq_dec_neq in MSG; eauto.
      rewrite upds in MSG.
      destruct (loc_ts_eq_dec (l, to) (locw, f_to w)) as [LTEQ|LTNEQ'].
      { simpls. desc; subst.
        rewrite (loc_ts_eq_dec_eq locw (f_to w)) in MSG. inv MSG. }
      rewrite loc_ts_eq_dec_neq in MSG; auto.
      apply MEM in MSG. destruct MSG as [|MSG]; [left|right]; auto.
      desc. exists b.
      assert (S b) as SB by (by apply ETCCOH.(etc_I_in_S)).
      splits; eauto.
      { by left. }
      { by rewrite updo; [|by intros HH; desf]. }
        by repeat (rewrite updo; [|by intros HH; desf]). }
    { simpls. desc; subst. 
      rewrite (loc_ts_eq_dec_eq locw n_to) in MSG. inv MSG. }
    rewrite loc_ts_eq_dec_neq in MSG; eauto.
    rewrite upds in MSG.
    destruct (loc_ts_eq_dec (l, to) (locw, f_to w)) as [LTEQ|LTNEQ'].
    { simpls. desc; subst.
      rewrite (loc_ts_eq_dec_eq locw (f_to w)) in MSG. inv MSG.
      exists wnext. rewrite !upds. splits; auto.
      { by right. }
      intros [A|A]; desf. }
    rewrite loc_ts_eq_dec_neq in MSG; auto. simpls.
    apply HMEM in MSG.
    desc.
    assert (b <> wnext) as BNEQ by (intros HH; desf).
    exists b. rewrite !updo with (a:=wnext); auto. splits; auto.
    { by left. }
    { intros [A|A]; desf. }
    destruct (classic (w = b)); subst.
    2: by rewrite updo; auto.
    exfalso. rewrite LOC in LOC0. inv LOC0. inv LTNEQ'. }

  assert (Memory.closed_timemap (View.rlx rel') memory_split) as RELMCLOS.
  { unfold rel'. simpls.
    apply Memory.join_closed_timemap.
    2: { unfold TimeMap.singleton, LocFun.add, LocFun.find.
         red. ins. destruct (Loc.eq_dec loc locw) as [|LNEQ]; subst.
         { erewrite Memory.split_o; eauto. rewrite loc_ts_eq_dec_eq. eauto. }
         unfold LocFun.init.
         exists Time.bot, 0, None. apply INHABSPLIT. }
    apply MSPLITCLOS.
    desc. apply Memory.join_closed_timemap; auto.
    unfold rel''.
    destruct (Rel w); simpls.
    all: apply MEM_CLOSE. }
  
  splits; eauto.
  { constructor; auto. simpls. unfold rel''0. by rewrite RELWFEQ. }
  eapply sim_helper_issue with
      (S':=S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G {| etc_TC := T; reserved := S |} rfi (eq w)); eauto.
  3: { etransitivity; [by apply ETCCOH.(etc_I_in_S)|]. basic_solver. }
  2: basic_solver.
  unfold f_to'. ins. by repeat (rewrite updo; [|by intros HH; desf]).
Admitted.

End Aux.
