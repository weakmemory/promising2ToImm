Require Import Setoid PArith.
From hahn Require Import Hahn.
Require Import PromisingLib.
From Promising2 Require Import TView View Time Event Cell Thread Memory Configuration Local.

From imm Require Import Events.
From imm Require Import Execution.
From imm Require Import Execution_eco.
From imm Require Import imm_s_hb.
From imm Require Import imm_s.
From imm Require Import imm_bob imm_s_ppo.
From imm Require Import CombRelations.
From imm Require Import AuxDef.
From imm Require Import SimClosure.

From imm Require Import AuxRel2.
Require Import AuxRel.
Require Import SimulationRel.
Require Import SimState.
Require Import MemoryAux.
Require Import MaxValue.
Require Import ViewRel.
Require Import ViewRelHelpers.
From imm Require Import TraversalOrder. 
From imm Require Import TLSCoherency.
From imm Require Import IordCoherency.
Require Import TlsEventSets.
Require Import EventsTraversalOrder.
Require Import Event_imm_promise.
Require Import ExtTraversalConfig.
Require Import ExtTraversal.
Require Import ExtTraversalProperties.
Require Import FtoCoherent.
Require Import SimulationRelProperties.

(* TODO: Essentially, it is a set of properties about the simulation relation.
   Move to simulation/ ? *)

Set Implicit Arguments.

Section Aux.

Variable G : execution.
Variable WF : Wf G.
Variable sc : relation actid.

(* Notation "'acts'" := (acts G). *)
Notation "'co'" := (co G).
Notation "'sw'" := (sw G).
Notation "'hb'" := (hb G).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'rfi'" := (rfi G).
Notation "'rfe'" := (rfe G).
Notation "'rmw'" := (rmw G).
Notation "'lab'" := (lab G).
Notation "'msg_rel'" := (msg_rel G sc).
Notation "'urr'" := (urr G sc).
Notation "'release'" := (release G).

Notation "'E'" := (acts_set G).
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

Variable T : trav_label -> Prop.
Hypothesis TCOH : tls_coherent G T. 
Hypothesis ICOH : iord_coherent G sc T. 
Hypothesis RCOH : reserve_coherent G T. 

Hypothesis RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T.

Variable f_to f_from : actid -> Time.t.
Hypothesis FCOH : f_to_coherent G (reserved T) f_to f_from.

Variable thread : thread_id.
Variable threads : Threads.t.
Variable memory : Memory.t.
Variable local : Local.t.

Hypothesis SIM_TVIEW : sim_tview G sc (covered T) f_to (Local.tview local) thread.
Hypothesis SIM_MEM : sim_mem G sc T f_to f_from thread local memory.
Hypothesis INHAB : Memory.inhabited memory.
Hypothesis PLN_RLX_EQ : pln_rlx_eq (Local.tview local).
Hypothesis MEM_CLOSE : memory_close (Local.tview local) memory.

Hypothesis SIM_RES_MEM :
  sim_res_mem G T f_to f_from thread local memory.

Hypothesis PROM_IN_MEM :
  forall thread' langst local
         (TID : IdentMap.find thread' threads = Some (langst, local)),
    Memory.le (Local.promises local) memory.

Variable smode : sim_mode.
Hypothesis RESERVED_TIME: reserved_time G T f_to f_from smode memory.

Definition rfrmw_prev_rel w locw p_rel := 
  (⟪ REL_PLN_RLX : View.pln (View.unwrap p_rel) = View.rlx (View.unwrap p_rel) ⟫ /\
   ⟪ P_MEM_CLOS : Memory.closed_timemap (View.rlx (View.unwrap p_rel))
                                        memory ⟫) /\
  ((⟪ NINRMW : ~ codom_rel (⦗ issued T ⦘ ⨾ rf ⨾ rmw) w ⟫ /\
    ⟪ PREL : p_rel = None ⟫) \/
   (exists p,
       ⟪ EP  : E p ⟫ /\
       ⟪ ISSP  : issued T p ⟫ /\
       ⟪ INRMW : (rf ⨾ rmw) p w ⟫ /\
       ⟪ P_LOC : loc lab p = Some locw ⟫ /\
       ⟪ P_MSG : sim_msg G sc f_to p (View.unwrap p_rel) ⟫  /\
       exists p_v,
         ⟪ P_VAL : val lab p = Some p_v ⟫ /\
         ⟪ P_INMEM : Memory.get locw (f_to p) memory =
                     Some (f_from p, Message.full p_v p_rel) ⟫)).

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
  { apply (wf_rfrmwE WF) in PRMWE. by destruct_seq PRMWE as [AA BB]. }
  assert (W wprev) as WPREV.
  { apply (wf_rfrmwD WF) in PRMWE. by destruct_seq PRMWE as [AA BB]. }
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

Lemma sim_helper_issue w locw valw f_to' f_from' (S' : actid -> Prop) p_rel
      (EW : E w) (WW : W w)
      (WLOC : loc lab w = Some locw)
      (WVAL : val lab w = Some valw)
      (WTID : thread = tid w)
      (ISSUABLE : issuable G sc T w)
      (RFRMWISS : dom_rel (rf ⨾ rmw ⨾ ⦗eq w⦘) ⊆₁ issued T)
      (WNCOV : ~ covered T w)
      (ISSEQ_TO : forall e (ISS: issued T e), f_to' e = f_to e)
      (SW : S' w)
      (IS : issued T ⊆₁ S')
      (FCOH' : f_to_coherent G S' f_to' f_from')
      (PREL : rfrmw_prev_rel w locw p_rel)
      (SIM_MEM' : ~ W_ex w \/
                  sim_mem G sc T f_to f_from thread local memory) :
  sim_mem_helper
    G sc f_to' w (f_from' w) valw
    (View.join (View.join (if is_rel lab w
                           then (TView.cur (Local.tview local))
                           else (TView.rel (Local.tview local) locw))
                          (View.unwrap p_rel))
               (View.singleton_ur locw (f_to' w))).
Proof using WF IMMCON RELCOV SIM_TVIEW TCOH ICOH.
  clear SIM_MEM SIM_RES_MEM.
  (* assert (tc_coherent G sc T) as TCCOH by apply ETCCOH. *)
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
      { eapply coveredE; eauto. }
      all: auto.
      { desf. }
      destruct WNCOV. eapply dom_sb_covered; eauto.
      eexists. basic_solver. }
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
  (* 2: by rewrite (msg_rel_alt2 WF TCCOH); eauto. *)
  2: { erewrite msg_rel_alt2; eauto. } 
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
      rewrite <- seqA. clear -RFRMWISS NINRMW.
      rewrite <- seqA in RFRMWISS.
      unfolder in *. ins. desf. eapply NINRMW. do 2 eexists. splits; eauto.
      apply RFRMWISS. eauto. }
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
  destruct SIM_MEM' as [AA|SIM_MEM'].
  { exfalso. apply AA. red. generalize INRMW. clear. basic_solver. }
  edestruct SIM_MEM' as [p_rel' H]; simpls; desc.
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

Lemma le_cur_f_to_wprev w locw wprev
      (WNISS : ~ issued T w)
      (SW : reserved T w)
      (PRMWE : (rf ⨾ rmw) wprev w)
      (LOC : loc lab w = Some locw)
      (WTID : thread = tid w) :
  let promises := (Local.promises local) in
  DenseOrder.le (View.rlx (TView.cur (Local.tview local)) locw) (f_to wprev).
Proof using WF SIM_TVIEW SIM_RES_MEM SIM_MEM RELCOV IMMCON FCOH TCOH RCOH ICOH.
  assert (sc_per_loc G) as SPL.
  { apply coherence_sc_per_loc. apply IMMCON. }
  assert (complete G) as COMPL by apply IMMCON.
  assert (wf_sc G sc) as WFSC by apply IMMCON. 

  assert (E w) as EW.
  { eapply rcoh_S_in_E; eauto. }
  assert (W w) as WW.
  { eapply reservedW; eauto. }
  
  assert (~ covered T w) as WNCOV.
  { intros HH. apply WNISS.
    eapply w_covered_issued; vauto. }
  assert (~ is_init w) as WNINIT.
  { intros HH. apply WNCOV. eapply init_covered; vauto. }

  assert (W_ex w) as WEXW.
  { red in PRMWE. red. basic_solver 10. }

  assert ((E ∩₁ W ∩₁ Loc_ locw) w) as WEW.
  { split; [split|]; auto. }

  assert (E wprev) as EPREV.
  { apply (wf_rfrmwE WF) in PRMWE. by destruct_seq PRMWE as [AA BB]. }
  assert (W wprev) as WPREV.
  { apply (wf_rfrmwD WF) in PRMWE. by destruct_seq PRMWE as [AA BB]. }
  
  assert (wprev <> w) as NEQPREV.
  { intros HH; subst. eapply wf_rfrmw_irr; eauto. }

  assert (loc lab wprev = Some locw) as PREVLOC.
  { rewrite <- LOC. by apply (wf_rfrmwl WF). }

  assert (issued T wprev) as ISSPREV.
  { eapply dom_rf_rmw_S_in_I; eauto.
    generalize PRMWE SW. clear. basic_solver 10. }

  assert (reserved T wprev) as SPREV.
  { eapply rcoh_I_in_S; eauto. }
  
  assert (dom_rel (rf ⨾ rmw ⨾ ⦗eq w⦘) ⊆₁ reserved T) as DRFRMWS.
  { intros x [y HH]. apply seqA in HH. destruct_seq_r HH as AA; subst.
    assert (x = wprev); desf.
    eapply wf_rfrmwf; eauto. }
  assert (immediate (⦗reserved T⦘ ⨾ co) wprev w) as IMMSPREV.
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
  { erewrite t_cur_covered; eauto. eapply rcoh_I_in_S; eauto. }
  split; [|basic_solver].
  intros x y QQ. apply seq_eqv_l in QQ. destruct QQ as [QQ' QQ]; subst.
  apply seq_eqv_r in QQ. destruct QQ as [COXY TCUR].
  red in TCUR. destruct TCUR as [z CCUR]. red in CCUR.
  hahn_rewrite <- seqA in CCUR.
  apply seq_eqv_r in CCUR. destruct CCUR as [URR COVZ].
  apply seq_eqv_r in URR. destruct URR as [URR II].
  eapply eco_urr_irr with (sc:=sc); eauto.
  1-2: by apply IMMCON.
  exists y. split.
  { apply co_in_eco. apply COXY. }
  apply urr_hb. exists z. split; eauto.
  right. apply sb_in_hb.
  assert (E z) as EZ.
  { eapply coveredE; eauto. }
  destruct II as [TIDZ|INITZ].
  2: by apply init_ninit_sb; auto.
  destruct (@same_thread G x z) as [[|SB]|SB]; auto.
  { desf. }
  destruct WNCOV. eapply dom_sb_covered; eauto. basic_solver 10.
Qed.

Lemma le_p_rel_f_to_wprev w locw wprev p_rel
      (WNISS : ~ issued T w)
      (SW : reserved T w)
      (PRMWE : (rf ⨾ rmw) wprev w)
      (LOC : loc lab w = Some locw)
      (WTID : thread = tid w)
      (PRELSPEC : rfrmw_prev_rel w locw p_rel) :
  let promises := (Local.promises local) in
  DenseOrder.le (View.rlx (View.unwrap p_rel) locw) (f_to wprev).
Proof using WF SIM_TVIEW SIM_RES_MEM SIM_MEM RELCOV IMMCON FCOH TCOH RCOH ICOH.
  assert (sc_per_loc G) as SPL.
  { apply coherence_sc_per_loc. apply IMMCON. }
  assert (complete G) as COMPL by apply IMMCON.

  assert (issued T wprev) as ISSPREV.
  { eapply dom_rf_rmw_S_in_I; eauto.
    generalize PRMWE SW. clear. basic_solver 10. }

  assert (reserved T wprev) as SPREV.
  { eapply rcoh_I_in_S; eauto. }

  assert (co wprev w) as COWPREV.
  { eapply rf_rmw_in_co; eauto. }

  assert (dom_rel (rf ⨾ rmw ⨾ ⦗eq w⦘) ⊆₁ reserved T) as DRFRMWS.
  { intros x [y HH]. apply seqA in HH. destruct_seq_r HH as AA; subst.
    assert (x = wprev); desf.
    eapply wf_rfrmwf; eauto. }
  assert (immediate (⦗reserved T⦘ ⨾ co) wprev w) as IMMSPREV.
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
    2: by (eapply rcoh_I_in_S; eauto). 
    intros x HH.
    eapply msg_rel_issued; eauto.
    { by apply IMMCON. }
    eexists. apply seq_eqv_r. split; eauto. }
  split; [|basic_solver].
  intros x y QQ. destruct_seq QQ as [COXY TCUR].
  destruct TCUR as [TCUR|[AA TCUR]]; subst.
  2: { eapply co_irr; eauto. eapply co_trans; eauto. }
  eapply msg_rel_co_irr; eauto.
  eexists; split; eauto.
  eapply co_trans; eauto.
Qed.

Notation "'S'" := (reserved T). 

Lemma f_to_coherent_add_S_middle w wprev wnext n_to n_from
      (FFNEQ : f_to wprev <> f_from wnext)
      (NSW : ~ reserved T w)
      (NIMMCO : immediate (co ⨾ ⦗S⦘) w wnext)
      (PIMMCO : immediate (⦗S⦘ ⨾ co) wprev w)
      (NTO    : (n_to = f_from wnext /\
                 ⟪ NRFRMW : (rf ⨾ rmw) w wnext ⟫) \/
                (n_to = Time.middle (f_to wprev) (f_from wnext) /\
                 ⟪ NNRFRMW : ~ (rf ⨾ rmw) w wnext ⟫))
      (NFROM  : (n_from = f_to wprev /\
                 ⟪ PRFRMW : (rf ⨾ rmw) wprev w ⟫) \/
                (n_from = Time.middle (f_to wprev) n_to /\
                 ⟪ NPRFRMW : ~ (rf ⨾ rmw) wprev w ⟫)) :
  ⟪ FCOH' : f_to_coherent G (S ∪₁ eq w) (upd f_to w n_to) (upd f_from w n_from) ⟫ /\
  ⟪ INTLE : Interval.le (n_from, n_to) (f_to wprev, f_from wnext) ⟫ /\
  ⟪ NFROMTOLT : Time.lt n_from n_to ⟫.
Proof using WF IMMCON FCOH TCOH RCOH.
  assert (S ⊆₁ E) as SinE by (eapply rcoh_S_in_E; eauto). 
  assert (S ⊆₁ W) as SinW by (eapply reservedW; eauto). 
  assert (sc_per_loc G) as SPL.
  { apply coherence_sc_per_loc. apply IMMCON. }

  assert (S wnext /\ co w wnext) as [ISSNEXT CONEXT].
  { destruct NIMMCO as [AA _]. by destruct_seq_r AA as BB. }

  assert (E wnext) as ENEXT.
  { eapply rcoh_S_in_E; eauto. } 
  assert (W wnext) as WNEXT.
  { eapply reservedW; eauto. }

  assert (S wprev /\ co wprev w) as [ISSPREV COPREV].
  { destruct PIMMCO as [H _]. apply seq_eqv_l in H; desf. }
  assert (E wprev) as EPREV.
  { eapply rcoh_S_in_E; eauto. }
  assert (W wprev) as WPREV.
  { eapply reservedW; eauto. }

  assert (E w) as EW.
  { apply (wf_coE WF) in CONEXT. by destruct_seq CONEXT as [AA BB]. }
  assert (W w) as WW.
  { apply (wf_coD WF) in CONEXT. by destruct_seq CONEXT as [AA BB]. }

  assert (~ is_init w) as WNINIT.
  { apply no_co_to_init in COPREV; auto. by destruct_seq_r COPREV as AA. }

  assert (~ is_init wnext) as NINITWNEXT.
  { apply no_co_to_init in CONEXT; auto.
    apply seq_eqv_r in CONEXT. desf. }

  assert (co wprev wnext) as COPN.
  { eapply (co_trans WF); eauto. }

  assert (Time.lt (f_to wprev) (f_from wnext)) as NPLT.
  { assert (Time.le (f_to wprev) (f_from wnext)) as H.
    { apply FCOH; auto. }
    apply Time.le_lteq in H. destruct H as [|H]; [done|desf]. }
  
  assert (Time.le n_from (Time.middle (f_to wprev) (f_from wnext))) as LEFROMTO1.
  { desf; try reflexivity.
    all: apply Time.le_lteq; left.
    all: repeat (apply Time.middle_spec; auto). }

  assert (Time.lt (f_to wprev) n_to) as LTPREVTO.
  { desf; by apply Time.middle_spec. }

  assert (Time.le (f_to wprev) n_from) as PREVFROMLE.
  { destruct NFROM as [[N1 N2]|[N1 N2]]; subst; [reflexivity|].
    apply Time.le_lteq; left. by apply Time.middle_spec. }

  assert (Time.lt n_from n_to) as LTFROMTO.
  { desf.
    { by apply Time.middle_spec. }
    eapply TimeFacts.lt_le_lt.
    2: reflexivity.
      by do 2 apply Time.middle_spec. }
  
  assert (Time.le (Time.middle (f_to wprev) (f_from wnext)) n_to) as LETO1.
  { desf; try reflexivity.
    all: by apply Time.le_lteq; left; apply Time.middle_spec. }

  assert (Time.le n_to (f_from wnext)) as LETONEXT.
  { desf; try reflexivity.
    all: by apply Time.le_lteq; left; apply Time.middle_spec. }
  
  splits; auto.
  2: { by constructor. }

  red; splits.
  { ins; rewrite updo; [by apply FCOH|].
    intros Y; subst. destruct H. desf. }
  { ins; rewrite updo; [by apply FCOH|].
    intros Y; subst. destruct H. desf. }
  { intros x [ISS|]; subst.
    { rewrite !updo; [by apply FCOH | |].
      all: by intros Y; subst. }
    ins. by rewrite !upds in *. }
  { intros x y [ISSX|EQX] [ISSY|EQY] CO; subst.
    all: try rewrite !upds.
    all: try rewrite !updo.
    all: try by intros H; subst.
    { by apply FCOH. }
    { etransitivity; [|by apply PREVFROMLE].
      assert (co^? x wprev) as COXP.
      { apply P_co_immediate_P_co_transp_in_co_cr with (P:=S); auto.
        exists y. split; auto. basic_solver. }
      eapply co_S_f_to_le; eauto. }
    2: by apply (co_irr WF) in CO.
    etransitivity; [by apply LETONEXT|].
    assert (co^? wnext y) as COXP.
    { apply immediate_co_P_transp_co_P_in_co_cr with (P:=S); auto.
      exists x. split; auto. basic_solver. }
    eapply co_S_f_from_le; eauto. }
  intros x y [ISSX|EQX] [ISSY|EQY] RFRMW; subst.
  all: try rewrite !upds.
  all: try rewrite !updo.
  all: try by intros H; subst.
  { by apply FCOH. }
  3: { exfalso. eapply (co_irr WF).
       eapply rfrmw_in_im_co in RFRMW; eauto.
       apply RFRMW. }
  2: { set (CC:=RFRMW).
       eapply rfrmw_in_im_co in CC; eauto.
       destruct CC as [AA BB].
       assert (co^? wnext y) as [|COY]; subst.
       { apply immediate_co_P_transp_co_P_in_co_cr with (P:=S); auto.
         exists x. split; auto. basic_solver. }
       { destruct NTO as [[NN1 NN2]|[NN1 NN2]]; desf. }
       exfalso. by apply BB with (c:=wnext). }
  set (CC:=RFRMW).
  eapply rfrmw_in_im_co in CC; eauto.
  destruct CC as [AA BB].
  assert (co^? x wprev) as [|COY]; subst.
  { apply P_co_immediate_P_co_transp_in_co_cr with (P:=S); auto.
    exists y. split; auto. basic_solver. }
  { destruct NFROM as [[NN1 NN2]|[NN1 NN2]]; desf. }
  exfalso. by apply BB with (c:=wprev).
Qed.

Lemma f_to_coherent_add_S_after locw w wprev n_from
      (* TODO: fix it after taking into account capped messages. *)
      (SMODE : smode = sim_normal \/ ~ W_ex w)
      (TID : tid w = thread)
      (WLOC : loc lab w = Some locw)
      (NSW : ~ S w)
      (DRES : dom_rel (rf ⨾ rmw ⨾ ⦗eq w⦘) ⊆₁ S)
      (NCO : ~ exists wnext, (co ⨾ ⦗S⦘) w wnext)
      (PIMMCO : immediate (⦗S⦘ ⨾ co) wprev w)
      (NFROM  : (n_from = Memory.max_ts locw memory /\
                 ⟪ PRFRMW : (rf ⨾ rmw) wprev w ⟫) \/
                (n_from = Time.incr (Memory.max_ts locw memory) /\
                 ⟪ NPRFRMW : ~ (rf ⨾ rmw) wprev w ⟫)) :
  (* ⟪ FCOH' : *)
    f_to_coherent
      G (S ∪₁ eq w)
      (upd f_to w (Time.incr (Time.incr (Memory.max_ts locw memory))))
      (upd f_from w n_from).
(* ⟫ /\ *)
(*   ⟪ NFROMTOLT : Time.lt n_from n_to ⟫. *)
Proof using WF IMMCON FCOH RESERVED_TIME SIM_MEM SIM_RES_MEM TCOH RCOH.
  clear SIM_TVIEW.
  assert (S ⊆₁ E) as SinE by (eapply rcoh_S_in_E; eauto). 
  assert (S ⊆₁ W) as SinW by (eapply reservedW; eauto). 
  assert (sc_per_loc G) as SPL.
  { apply coherence_sc_per_loc. apply IMMCON. }

  assert (S wprev /\ co wprev w) as [ISSPREV COPREV].
  { destruct PIMMCO as [H _]. apply seq_eqv_l in H; desf. }
  assert (E wprev) as EPREV.
  { eapply rcoh_S_in_E; eauto. }
  assert (W wprev) as WPREV.
  { eapply reservedW; eauto. }

  assert (E w) as EW.
  { apply (wf_coE WF) in COPREV. by destruct_seq COPREV as [AA BB]. }
  assert (W w) as WW.
  { apply (wf_coD WF) in COPREV. by destruct_seq COPREV as [AA BB]. }

  assert (~ is_init w) as WNINIT.
  { apply no_co_to_init in COPREV; auto. by destruct_seq_r COPREV as AA. }
  
  set (ts := Memory.max_ts locw memory).
  set (f_to' := upd f_to w (Time.incr (Time.incr (Memory.max_ts locw memory)))).

  assert (Time.le ts n_from) as LENFROM_R.
  { destruct NFROM as [[N _]|[N _]]; subst; [reflexivity|].
    apply Time.le_lteq; left. apply DenseOrder.incr_spec. }

  assert (Time.le n_from (Time.incr ts)) as LENFROM_L.
  { destruct NFROM as [[N _]|[N _]]; subst; [|reflexivity].
    apply Time.le_lteq; left. apply DenseOrder.incr_spec. }
  set (f_from' := upd f_from w n_from).

  assert (Time.lt (f_from' w) (f_to' w)) as NLT.
  { unfold f_to', f_from', ts; rewrite !upds.
    eapply TimeFacts.le_lt_lt.
    { apply LENFROM_L. }
    apply DenseOrder.incr_spec. }

  assert (Time.lt n_from (Time.incr (Time.incr ts))) as NNLT.
  { eapply TimeFacts.le_lt_lt.
    2: by apply Time.incr_spec.
    done. }

  red; splits; unfold f_from'.
  { ins; rewrite updo; [by apply FCOH|].
    intros Y; subst. by destruct H. }
  { ins; rewrite updo; [by apply FCOH|].
    intros Y; subst. by destruct H. }
  { intros x [ISS|]; subst.
    { rewrite !updo; [by apply FCOH | |].
      all: by intros Y; subst. }
    unfold f_to', f_from', ts in *.
      by rewrite !upds in *. }
  { intros x y [ISSX|EQX] [ISSY|EQY] CO; subst.
    all: try rewrite !upds.
    all: try rewrite !updo.
    all: try by intros H; subst.
    { by apply FCOH. }
    { etransitivity; [|by apply LENFROM_R].
      eapply S_le_max_ts; eauto.
      rewrite <- WLOC. by apply (wf_col WF). }
    { exfalso. eapply NCO. eexists; apply seq_eqv_r; eauto. }
    exfalso. by apply co_irr in CO. }
  intros x y [ISSX|EQX] [ISSY|EQY] RFRMW; subst.
  all: try rewrite !upds.
  all: try rewrite !updo.
  all: try by intros H; subst.
  { by apply FCOH. }
  { (* TODO: extract some reasoning *)
    destruct NFROM as [[EQ HH]|[EQ NWPREV]]; subst; unnw.
    2: { exfalso.
         clear SMODE.
         assert (x = wprev); desf.
         eapply wf_immcoPtf; eauto; red.
         eapply rfrmwP_in_immPco with (P':=eq y); eauto.
         apply seqA. basic_solver. }
    desf.
    { cdes RESERVED_TIME.
      eapply no_next_S_max_ts; eauto. }
    exfalso. generalize SMODE, RFRMW. unfold Execution.W_ex. clear. basic_solver. }

  all: exfalso; eapply rfrmw_in_im_co in RFRMW; eauto.
  { eapply NCO. eexists; apply seq_eqv_r; split; eauto.
    apply RFRMW. }
  eapply (co_irr WF). apply RFRMW.
Qed.

Lemma f_to_coherent_split w wnext locw n_to
      (NWEX : ~ W_ex w)
      (EW : E w)
      (WW : W w)
      (LOC : loc lab w = Some locw)
      (NSW : ~ S w)
      (NCOIMM : immediate (co ⨾ ⦗S⦘) w wnext)
      (NCOVNEXT : ~ covered T wnext)
      (LLFROMN : Time.lt (f_from wnext) n_to)
      (LLTON : Time.lt n_to (f_to wnext)) :
  f_to_coherent G (S ∪₁ eq w) (upd f_to w n_to)
                (upd (upd f_from wnext n_to) w (f_from wnext)).
Proof using WF IMMCON FCOH TCOH RCOH.
  assert (WNISS : ~ issued T w).
  { intros HH. apply NSW. eapply rcoh_I_in_S; eauto. }
  assert (WNINIT : ~ is_init w).
  { intros HH. apply WNISS. eapply init_issued; eauto. by split. }
  assert (co w wnext /\ S wnext) as [CONEXT ISSNEXT].
  { destruct NCOIMM as [HH]. apply seq_eqv_r in HH. apply HH. }
  assert (E wnext /\ W wnext) as [ENEXT WNEXT].
  { apply (dom_r (wf_coE WF)) in CONEXT. destruct_seq_r CONEXT as AA.
    apply (dom_r (wf_coD WF)) in CONEXT. destruct_seq_r CONEXT as BB.
      by split. }
  assert (NEQNEXT : wnext <> w).
  { intros HH. subst. eapply (co_irr WF); eauto. }
  assert (LOCNEXT : loc lab wnext = Some locw).
  { rewrite <- LOC. symmetry. by apply (wf_col WF). }

  red; splits; ins.
  { rewrite updo.
    { by apply FCOH. }
    intros HH; subst. by destruct H. }
  { rewrite updo.
    rewrite updo.
    { by apply FCOH. }
    all: intros HH; subst.
    { apply NCOVNEXT. eapply init_covered; eauto. }
    destruct H; desf. } 
  { destruct H as [H|]; subst.
    2: by rewrite !upds.
    rewrite updo.
    2: by intros HH; subst.
    destruct (classic (wnext = x)) as [|NEQ]; subst;
      [rewrite upds | rewrite updo; auto];
      rewrite updo; auto; try by intros HH; subst.
      by apply FCOH. }
  { assert (x <> y) as HXY.
    { by intros HH; subst; apply (co_irr WF) in H1. }
    destruct H as [H|]; destruct H0 as [H0|]; subst.
    all: try (rewrite !upds).
    { rewrite updo; [|by intros HH; subst].
      rewrite updo; [|by intros HH; subst].
      destruct (classic (wnext = y)) as [|NEQ]; subst;
        [rewrite upds | rewrite updo; auto].
      { etransitivity; eauto.
        2: by apply Time.le_lteq; left; eauto.
          by apply FCOH. }
        by apply FCOH. }
    { rewrite updo; auto.
      apply FCOH; auto.
      eapply (co_trans WF); eauto. }
    { rewrite updo; auto.
      destruct (classic (wnext = y)) as [|NEQ]; subst;
        [by rewrite upds; apply DenseOrder_le_PreOrder | rewrite updo; auto].
      etransitivity.
      { apply Time.le_lteq; left. apply LLTON. }
      apply FCOH; auto.
      eapply tot_ex.
      { by eapply WF. }
      { unfolder; splits; eauto.
        hahn_rewrite (dom_r (wf_coE WF)) in H1; unfolder in H1; basic_solver 12.
        hahn_rewrite (dom_r (wf_coD WF)) in H1; unfolder in H1; basic_solver 12. }
      { unfolder; splits; eauto.
        hahn_rewrite (wf_col WF) in H1; unfold same_loc in *; congruence. }
      { unfold immediate in NCOIMM; desc; intro; eapply NCOIMM0; basic_solver 21. }
        by intro; subst. }
      by apply (co_irr WF) in H1. }
  destruct H as [H|]; subst.
  { assert (x <> w) as NXW.
    { intros YY. desf. }
    rewrite updo; auto.
    destruct H0 as [H0|]; subst.
    2: { exfalso. generalize H1, NWEX. unfold Execution.W_ex. clear. basic_solver. }
    assert (y <> w) as NXY.
    { intros YY. desf. }
    rewrite updo; auto.
    assert (y <> wnext) as NYN.
    2: { rewrite updo; auto. by apply FCOH. }
    intros UU; subst.
    assert (loc lab x = Some locw) as XLOC.
    { rewrite <- LOCNEXT. by apply (wf_rfrmwl WF). }
    edestruct (wf_co_total WF) with (a:=w) (b:=x) as [CO|CO]; auto.
    1,2: split; [split|]; auto.
    { eapply rcoh_S_in_E; eauto. }
    { eapply reservedW; eauto. }
    { by rewrite XLOC. }
    { eapply NCOIMM.
      all: apply seq_eqv_r; split; eauto.
      eapply rfrmw_in_im_co; eauto. }
    eapply rfrmw_in_im_co in H1; eauto. eapply H1; eauto. }
  rewrite upds. rewrite updo.
  2: { intros HH; subst. eapply wf_rfrmw_irr; eauto. }
  destruct H0 as [H0|]; subst.
  2: { exfalso. eapply wf_rfrmw_irr; eauto. }
  assert (y = wnext); subst.
  2: by rewrite upds.
  exfalso. apply WNISS. eapply dom_rf_rmw_S_in_I; eauto. 
  exists y. 
  apply seqA. apply seq_eqv_r. by split.
Qed.

Lemma message_to_event_add_S l w memory' n_to n_from T' msg v rel
      (EW : E w)
      (LOC : loc lab w = Some l)
      (VAL : val lab w = Some v)
      (NIW : ~ issued T w)
      (RESERVED_TIME': reserved_time G T f_to f_from sim_normal memory)
      (TMSG : T' ≡₁ T /\ msg = Message.reserve \/
              (* T' = mkTC (covered T) (issued T ∪₁ eq w) /\ msg = Message.full v rel *)
              T' ≡₁ T ∪₁ eq (mkTL ta_issue w) /\ msg = Message.full v rel
      )
      (MADD :
        Memory.add memory l
                   ((upd f_from w n_from) w)
                   ((upd f_to w n_to) w)
                   msg memory') :
  message_to_event G T' (upd f_to w n_to) (upd f_from w n_from) memory'.
Proof using.
  cdes RESERVED_TIME'.
  set (f_to':= upd f_to w n_to).
  set (f_from':= upd f_from w n_from).

  red; ins. erewrite Memory.add_o in MSG; eauto.
  destruct (loc_ts_eq_dec (l0, to) (l, f_to' w)) as [[EQ1 EQ2]|NEQ].
  { simpls; subst.
    rewrite (loc_ts_eq_dec_eq l (f_to' w)) in MSG.
    inv MSG. desf. right. exists w. splits; eauto.
    eapply issued_more, issued_union; eauto.
    right. by apply issued_singleton. }
  rewrite loc_ts_eq_dec_neq in MSG; simpls; auto.
  apply MEM in MSG. destruct MSG as [MSG|MSG]; [by left|right].
  destruct MSG as [b H]; desc.
  assert (b <> w) as BNEQ.
  { by intros H; subst. }
  unfold f_to', f_from'.
  exists b; splits; auto.
  { destruct TMSG; desc; eapply issued_more; eauto.
    apply issued_union. by left. } 
  all: by rewrite updo.
Qed.

Local Ltac caseT' TMSG := destruct TMSG as [[-> _] | [-> _]]; try rewrite !reserved_union.

Lemma reserved_time_add_S_middle l w wprev wnext memory' n_to n_from T' msg v rel
      (SEW : S ⊆₁ E ∩₁ W)
      (IS  : issued T ⊆₁ S)
      (FFNEQ : f_to wprev <> f_from wnext)
      (LOC : loc lab w = Some l)
      (VAL : val lab w = Some v)
      (EW  : E w)
      (NSW : ~ S w)
      (NIMMCO : immediate (co ⨾ ⦗S⦘) w wnext)
      (PIMMCO : immediate (⦗S⦘ ⨾ co) wprev w)
      (NTO    : (n_to = f_from wnext /\
                 ⟪ NRFRMW : (rf ⨾ rmw) w wnext ⟫) \/
                (n_to = Time.middle (f_to wprev) (f_from wnext) /\
                 ⟪ NNRFRMW : ~ (rf ⨾ rmw) w wnext ⟫))
      (NFROM  : (n_from = f_to wprev /\
                 ⟪ PRFRMW : (rf ⨾ rmw) wprev w ⟫) \/
                (n_from = Time.middle (f_to wprev) n_to /\
                 ⟪ NPRFRMW : ~ (rf ⨾ rmw) wprev w ⟫))
      (TMSG : T' ≡₁ T /\ msg = Message.reserve \/
              (* T' = mkTC (covered T) (issued T ∪₁ eq w) /\ msg = Message.full v rel *)
              T' ≡₁ T ∪₁ eq (mkTL ta_issue w) /\ msg = Message.full v rel
      )
      (MADD :
        Memory.add memory l
                   ((upd f_from w n_from) w)
                   ((upd f_to w n_to) w)
                   msg memory') :
  (* reserved_time *)
  (*   G T' (S ∪₁ eq w) (upd f_to w n_to) (upd f_from w n_from) *)
  (*   smode memory' *)
  reserved_time
    G (T' ∪₁ eq (mkTL ta_reserve w)) (upd f_to w n_to) (upd f_from w n_from)
    smode memory'
.
Proof using WF IMMCON FCOH RESERVED_TIME.  
  clear SIM_MEM RELCOV. 
  assert (sc_per_loc G) as SPL.
  { apply coherence_sc_per_loc. apply IMMCON. }

  assert (~ issued T w) as NIW.
  { intros II. apply NSW. by apply IS. }

  set (f_to':= upd f_to w n_to).
  set (f_from':= upd f_from w n_from).

  assert (S wnext /\ co w wnext) as [ISSNEXT CONEXT].
  { destruct NIMMCO as [AA _]. by destruct_seq_r AA as BB. }
  assert (E wnext /\ W wnext) as [ENEXT WNEXT].
  { by apply SEW. }

  assert (S wprev /\ co wprev w) as [ISSPREV COPREV].
  { destruct PIMMCO as [H _]. apply seq_eqv_l in H; desf. }
  assert (E wprev /\ W wprev) as [EPREV WPREV].
  { by apply SEW. }

  assert (~ is_init w) as WNINIT.
  { apply no_co_to_init in COPREV; auto. by destruct_seq_r COPREV as AA. }

  assert (~ is_init wnext) as NINITWNEXT.
  { apply no_co_to_init in CONEXT; auto.
    apply seq_eqv_r in CONEXT. desf. }

  assert (co wprev wnext) as COPN.
  { eapply (co_trans WF); eauto. }

  assert (Time.lt (f_to wprev) (f_from wnext)) as NPLT.
  { assert (Time.le (f_to wprev) (f_from wnext)) as H.
    { apply FCOH; auto. }
    apply Time.le_lteq in H. destruct H as [|H]; [done|desf]. }
  
  assert (Time.le n_from (Time.middle (f_to wprev) (f_from wnext))) as LEFROMTO1.
  { desf; try reflexivity.
    all: apply Time.le_lteq; left.
    all: repeat (apply Time.middle_spec; auto). }

  assert (Time.lt (f_to wprev) n_to) as LTPREVTO.
  { desf; by apply Time.middle_spec. }

  assert (Time.le (f_to wprev) n_from) as PREVFROMLE.
  { destruct NFROM as [[N1 N2]|[N1 N2]]; subst; [reflexivity|].
    apply Time.le_lteq; left. by apply Time.middle_spec. }

  assert (Time.lt n_from n_to) as LTFROMTO.
  { clear TMSG. desf.
    { by apply Time.middle_spec. }
    eapply TimeFacts.lt_le_lt.
    2: reflexivity.
      by do 2 apply Time.middle_spec. }

  assert (Time.le (Time.middle (f_to wprev) (f_from wnext)) n_to) as LETO1.
  { desf; try reflexivity.
    all: by apply Time.le_lteq; left; apply Time.middle_spec. }

  assert (Time.le n_to (f_from wnext)) as LETONEXT.
  { desf; try reflexivity.
    all: by apply Time.le_lteq; left; apply Time.middle_spec. }

  (* assert (T' ⊆₁ T ∪₁ eq (mkTL ta_issue w)) as T'_IN. *)
  (* { destruct TMSG as [[-> _] | [-> _]]; basic_solver. } *)

  cdes RESERVED_TIME. red.
  destruct smode eqn:SMODE; desc; unnw.
  2: { split.
       2: { rewrite RMW_BEF_S. 
            caseT' TMSG; basic_solver 10. }
       rewrite <- FOR_SPLIT.
       hahn_frame.
       clear -TMSG. apply eqv_rel_mori.
       apply set_compl_mori. red.
       caseT' TMSG; basic_solver 10. }

  (* TODO: Extract to a separate lemma. *)
  assert (half_message_to_event G (T' ∪₁ eq (mkTL ta_reserve w)) f_to' f_from' memory') as HMTE.
  { red; ins. erewrite Memory.add_o in MSG; eauto.
    destruct (loc_ts_eq_dec (l0, to) (l, f_to' w)) as [[EQ1 EQ2]|NEQ].
    { simpls; subst.
      rewrite (loc_ts_eq_dec_eq l (f_to' w)) in MSG.
      inv MSG.
      clear MSG. exists w. splits; auto.
      { apply reserved_union. right. by apply reserved_singleton. }
      apply set_disjoint_eq_r. destruct TMSG as [[-> _] | [-> [=]]].
      simplify_tls_events. basic_solver. }
    rewrite loc_ts_eq_dec_neq in MSG; simpls; auto.
    pose proof MSG as MSG_. apply HMEM in MSG. desc.
    assert (b <> w) as BNEQ.
    { intros H; subst. by apply NSW. }
    exists b.
    splits; eauto.
    { apply hahn_subset_exp with (s := S); [| done]. 
      caseT' TMSG; basic_solver 10. }
    { apply set_disjoint_eq_r. destruct TMSG as [[-> _] | [-> FOO]].
      all: simplify_tls_events; basic_solver. }
    1,2: by unfold f_from', f_to'; rewrite updo. }
  splits; auto.
  { apply message_to_event_same_issued with (T := T').
    2: { simplify_tls_events. basic_solver. }
    eapply message_to_event_add_S with (rel := rel); eauto. }
  unfold f_to', f_from'.
  intros x y.

  assert (reserved T' ≡₁ S) as S'_EQ. 
  { caseT' TMSG; simplify_tls_events; basic_solver. }
  
  (* assert (~ reserved T' w) as NRES'w. *)
  (* { intros RES'w. destruct TMSG as [[T'_ _] | [T'_ _]]. *)
  (*   { eapply reserved_more in RES'w; [| symmetry; apply T'_]; vauto. }  *)
  (*   eapply reserved_more in RES'w; [| symmetry; apply T'_]; eauto. *)
  (*   apply reserved_union in RES'w as [RES'w | RES'w]; vauto. *)
  (*   by apply reserved_issue_empty in RES'w. } *)

  (* [Sx|] [SY|] CO FT; subst. *)
  intros [Sx | ?%reserved_singleton]%reserved_union
         [Sy | ?%reserved_singleton]%reserved_union
         CO FT; subst.   
  4: { exfalso. eapply co_irr; eauto. }
  { do 2 rewrite updo in FT.
    2, 3, 4: intros ->; destruct NSW; by apply S'_EQ.
    apply TFRMW; eauto; apply S'_EQ; auto. }  
  (* all: destruct (classic (x = y)) as [|NEQ]; [by desf|]. *)
  all: destruct (classic (x = y)) as [|NEQ]; [subst; edestruct co_irr; by eauto|].
  { rewrite updo in FT; auto.
    rewrite upds in FT.
    assert (same_loc lab x wprev) as LXPREV.
    { etransitivity.
      { apply (wf_col WF); eauto. }
      symmetry. by apply (wf_col WF). }
    destruct NFROM as [[NFROM BB]|[NFROM BB]]; unnw.
    { desc; subst.
      eapply f_to_eq with (I:=S) in FT; eauto; subst; desc.
      subst. apply BB. by apply S'_EQ. }
    exfalso.
    assert (E x /\ W x) as [EX WX].
    { by apply SEW, S'_EQ. }
    edestruct (wf_co_total WF) with (a:=x) (b:=wprev) as [COWX|COWX].
    1-2: split; [split|]; eauto.
    { intros H; subst.
      eapply Time.lt_strorder with (x:=f_to wprev).
      rewrite FT at 2. by apply Time.middle_spec. }
    { subst.
      assert (Time.lt (f_to x) (f_to wprev)) as DD.
      { eapply f_to_co_mon; eauto. by apply S'_EQ. }
      eapply Time.lt_strorder with (x:=f_to x).
      rewrite FT at 2.
      etransitivity; [by apply DD|]. by apply Time.middle_spec. }
    eapply PIMMCO.
    all: apply seq_eqv_l; split; eauto; by apply S'_EQ. }
  rewrite upds in FT; auto.
  rewrite updo in FT; auto.
  assert (same_loc lab wnext y) as LXPREV.
  { etransitivity.
    { symmetry. apply (wf_col WF). apply CONEXT. }
    apply (wf_col WF); eauto. }
  assert (~ is_init y) as NINITY.
  { apply no_co_to_init in CO; auto. by destruct_seq_r CO as BB. }
  destruct NTO as [[NTO BB]|[NTO BB]]; unnw.
  { desc; subst.
    eapply f_from_eq with (I:=S) in FT; eauto; subst; desc.
    subst. apply BB. by apply S'_EQ. }
  exfalso.
  assert (E y /\ W y) as [EY WY] by (by apply SEW, S'_EQ).
  edestruct (wf_co_total WF) with (a:=wnext) (b:=y) as [COWY|COWY].
  1-2: split; [split|]; eauto.
  { intros H; subst.
    eapply Time.lt_strorder with (x:=f_from y).
    rewrite <- FT at 1. by apply Time.middle_spec. }
  { subst.
    assert (Time.lt (f_from wnext) (f_from y)) as DD.
    { eapply f_from_co_mon; eauto. by apply S'_EQ. }
    eapply Time.lt_strorder with (x:=f_from y).
    rewrite <- FT at 1.
    etransitivity; [|by apply DD]. by apply Time.middle_spec. }
  eapply NIMMCO with (c:=y).
  all: apply seq_eqv_r; split; auto. by apply S'_EQ.
Qed.

Lemma reserved_time_add_S_after locw memory' w wprev n_from T' msg v rel
      (* TODO: fix it after taking into account capped messages. *)
      (SMODE : smode = sim_normal \/ ~ W_ex w)
      (SEW : S ⊆₁ E ∩₁ W)
      (IS  : issued T ⊆₁ S)
      (TID : tid w = thread)
      (WLOC : loc lab w = Some locw)
      (WVAL : val lab w = Some v)
      (NSW : ~ S w)
      (NCO : ~ exists wnext, (co ⨾ ⦗S⦘) w wnext)
      (PIMMCO : immediate (⦗S⦘ ⨾ co) wprev w)
      (NFROM  : (n_from = Memory.max_ts locw memory /\
                 ⟪ PRFRMW : (rf ⨾ rmw) wprev w ⟫) \/
                (n_from = Time.incr (Memory.max_ts locw memory) /\
                 ⟪ NPRFRMW : ~ (rf ⨾ rmw) wprev w ⟫))
      (TMSG : T' ≡₁ T /\ msg = Message.reserve \/
              (* T' = mkTC (covered T) (issued T ∪₁ eq w) /\ msg = Message.full v rel *)
              T' ≡₁ T ∪₁ eq (mkTL ta_issue w) /\ msg = Message.full v rel
      )
      (MADD :
        Memory.add memory locw
                   ((upd f_from w n_from) w)
                   ((upd f_to w (Time.incr (Time.incr (Memory.max_ts locw memory)))) w)
                   msg memory') :     
  reserved_time
    G (T' ∪₁ eq (mkTL ta_reserve w)) (upd f_to w (Time.incr (Time.incr (Memory.max_ts locw memory))))
    (upd f_from w n_from)
    smode memory'.
Proof using WF IMMCON FCOH RESERVED_TIME SIM_RES_MEM SIM_MEM TCOH RCOH.  
  clear SIM_TVIEW RELCOV. 
  assert (sc_per_loc G) as SPL.
  { apply coherence_sc_per_loc. apply IMMCON. }

  assert (~ issued T w) as NIW.
  { intros II. apply NSW. by apply IS. }

  set (f_to':= upd f_to w (Time.incr (Time.incr (Memory.max_ts locw memory)))).
  set (f_from':= upd f_from w n_from).

  assert (S wprev /\ co wprev w) as [ISSPREV COPREV].
  { destruct PIMMCO as [H _]. apply seq_eqv_l in H; desf. }
  assert (E wprev /\ W wprev) as [EPREV WPREV].
  { by apply SEW. }

  assert (~ is_init w) as WNINIT.
  { apply no_co_to_init in COPREV; auto. by destruct_seq_r COPREV as AA. }
  
  assert (E w) as EW.
  { apply (wf_coE WF) in COPREV. by destruct_seq COPREV as [AA BB]. }

  cdes RESERVED_TIME. red.
  destruct smode; desc; unnw.
  2: { split.
       2: { rewrite RMW_BEF_S. caseT' TMSG; basic_solver 10. }  
       rewrite <- FOR_SPLIT.
       hahn_frame.
       clear -TMSG. apply eqv_rel_mori.
       apply set_compl_mori. red.
       caseT' TMSG; basic_solver 10. }

  (* TODO: Extract to a separate lemma. *)
  assert (half_message_to_event G (T' ∪₁ eq (mkTL ta_reserve w)) f_to' f_from' memory') as HMTE.
  { red; ins. erewrite Memory.add_o in MSG; eauto.
    destruct (loc_ts_eq_dec (l, to) (locw, f_to' w)) as [[EQ1 EQ2]|NEQ].
    { simpls; subst.
      rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in MSG.
      inv MSG.
      clear MSG. exists w. splits; auto.
      { apply reserved_union. right. by apply reserved_singleton. }
      apply set_disjoint_eq_r. destruct TMSG as [[-> _] | [-> FOO]].
      all: simplify_tls_events; basic_solver. }
    rewrite loc_ts_eq_dec_neq in MSG; simpls; auto.
    apply HMEM in MSG. desc.
    assert (b <> w) as BNEQ.
    { intros H; subst. by apply NSW. }
    exists b.
    splits; eauto.
    { apply hahn_subset_exp with (s := S); [| done]. 
      caseT' TMSG; basic_solver 10. }
    (* { destruct TMSG; desc; subst; auto. ins. *)
    (*   intros [HH|HH]; auto. } *)
    { apply set_disjoint_eq_r. destruct TMSG as [[-> _] | [-> FOO]].
      all: simplify_tls_events; basic_solver. }
    1,2: by unfold f_from', f_to'; rewrite updo. }
  splits; auto.
  { apply message_to_event_same_issued with (T := T').
    2: { simplify_tls_events; basic_solver. }
    eapply message_to_event_add_S with (rel := rel); eauto. }
  unfold f_to', f_from'.
  (* intros x y [SX|] [SY|] CO FT; subst. *)
  (* 4: { exfalso. eapply co_irr; eauto. } *)
  (* { rewrite updo in FT; [|by intros AA; desf]. *)
  (*   rewrite updo in FT; [|by intros AA; desf]. *)
  (*     by apply TFRMW. } *)
  assert (reserved T' ≡₁ S) as S'_EQ. 
  { caseT' TMSG; simplify_tls_events; basic_solver. }
  
  intros x y. 
  intros [Sx | ?%reserved_singleton]%reserved_union
         [Sy | ?%reserved_singleton]%reserved_union
         CO FT; subst.   
  4: { exfalso. eapply co_irr; eauto. }
  { do 2 rewrite updo in FT.
    2, 3, 4: intros ->; destruct NSW; by apply S'_EQ.
    apply TFRMW; eauto; apply S'_EQ; auto. }  

  all: destruct (classic (x = y)) as [|NEQ]; [subst; edestruct co_irr; by eauto|].
  { rewrite updo in FT; auto.
    rewrite upds in FT.
    assert (same_loc lab x wprev) as LXPREV.
    { etransitivity.
      { apply (wf_col WF); eauto. }
      symmetry. by apply (wf_col WF). }
    destruct NFROM as [[NFROM BB]|[NFROM BB]]; unnw.
    { desc; subst.
      assert (f_to x = f_to wprev) as FF.
      2: { eapply f_to_eq with (I:=S) in FF; eauto; desf; apply S'_EQ; auto. }
      rewrite FT. symmetry.
      destruct SMODE as [|HH].
      { eapply no_next_S_max_ts; eauto. }
      exfalso. generalize BB HH. unfold Execution.W_ex. clear. basic_solver. }
    exfalso. eapply Time.lt_strorder.
    eapply TimeFacts.le_lt_lt.
    2: by apply DenseOrder.incr_spec.
    subst. rewrite <- FT.
    eapply S_le_max_ts; eauto.
    { by apply S'_EQ. }
    rewrite <- WLOC. by apply (wf_col WF). }
  rewrite upds in FT.
  rewrite updo in FT; auto.
  exfalso. eapply Time.lt_strorder.
  etransitivity; [|by apply DenseOrder.incr_spec].
  etransitivity; [|by apply DenseOrder.incr_spec].
  rewrite FT.
  eapply TimeFacts.lt_le_lt.
  2: { eapply S_le_max_ts with (x:=y); eauto.
       { by apply S'_EQ. }
       rewrite <- WLOC. symmetry. by apply (wf_col WF). }
  apply FCOH; auto.
  apply no_co_to_init in CO; auto.
  { by apply S'_EQ. }
  apply no_co_to_init, seq_eqv_r in CO; auto. by desc.  
Qed.

End Aux.
