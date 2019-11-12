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
Require Import Event_imm_promise.
Require Import ExtTraversal.
Require Import ExtTraversalProperties.
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

(* TODO: move to a more appropriate place. *)
Lemma exists_wprev_rel w locw valw
      (WW : W w)
      (LOC : loc lab w = Some locw)
      (VAL : val lab w = Some valw)
      (WTID : thread = tid w) :
  exists p_rel,
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
Proof using WF SIM_MEM INHAB.
  clear SIM_RES_MEM SIM_TVIEW.
  subst.
  destruct (classic (codom_rel (⦗ issued T ⦘ ⨾ rf ⨾ rmw) w)) as [[wprev PRMWE]|].
  2: { eexists; split; [|by left; splits; eauto].
       simpls. split; auto. by apply Memory.closed_timemap_bot. }
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
  exists p_rel; split; [auto|right; exists wprev; splits; eauto].
  apply HELPER.
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
      (PROM_IN_MEM :
         forall thread' langst local
                (TID : IdentMap.find thread' PC.(Configuration.threads) =
                       Some (langst, local)),
           Memory.le local.(Local.promises) PC.(Configuration.memory))
      (RESERVED_TIME:
         reserved_time G T S f_to f_from smode PC.(Configuration.memory))
      (TID : IdentMap.find (tid w) PC.(Configuration.threads) = Some (langst, local)) :
  let promises := local.(Local.promises) in
  let memory   := PC.(Configuration.memory) in
  let S'       := S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G (mkETC T S) rfi (eq w) in
  exists p_rel,
    (* TODO: introduce a definition *)
    (⟪ REL_PLN_RLX : View.pln p_rel.(View.unwrap) = View.rlx p_rel.(View.unwrap) ⟫ /\
     ⟪ P_MEM_CLOS : Memory.closed_timemap (View.rlx p_rel.(View.unwrap)) memory ⟫ /\
     ⟪ P_REL_CH :
         (⟪ NINRMW : ~ codom_rel (⦗ issued T ⦘ ⨾ rf ⨾ rmw) w ⟫ /\
          ⟪ PREL : p_rel = None ⟫) \/
         (exists p,
             ⟪ EP  : E p ⟫ /\
             ⟪ ISSP  : issued T p ⟫ /\
             ⟪ INRMW : (rf ⨾ rmw) p w ⟫ /\
             ⟪ P_LOC : loc lab p = Some locw ⟫ /\
             ⟪ P_MSG : sim_msg G sc f_to p p_rel.(View.unwrap) ⟫  /\
             exists p_v,
               ⟪ P_VAL : val lab p = Some p_v ⟫ /\
               ⟪ P_INMEM : Memory.get locw (f_to p) memory =
                           Some (f_from p, Message.full p_v p_rel) ⟫)⟫) /\

    let rel'' :=
        if is_rel lab w
        then (TView.cur (Local.Local.tview local))
        else (TView.rel (Local.Local.tview local) locw)
    in
    let rel' := (View.join (View.join rel'' p_rel.(View.unwrap))
                           (View.singleton_ur locw (f_to w))) in

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
                       (Message.full valw p_rel) promises_add ⟫ /\
        ⟪ MADD :
            Memory.add memory_cancel locw (f_from w) (f_to w)
                       (Message.full valw p_rel) memory_add ⟫ /\

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
            reserved_time G T S' f_to f_from smode memory_add ⟫.
Proof using WF IMMCON ETCCOH FCOH.
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
  
  assert (~ covered T w) as WNCOV.
  { admit. }
  assert (~ issued T w) as WNISS.
  { admit. }
  assert (~ is_init w) as WNINIT.
  { admit. }

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
  
  assert (immediate (⦗S⦘ ⨾ co) wprev w) as IMMSPREV.
  { admit. }

  assert (exists vprev, val lab wprev = Some vprev) as [vprev PREVVAL] by (by apply is_w_val).

  edestruct exists_wprev_rel with (w:=w) as [p_rel PRELSPEC]; eauto.
  
  exists p_rel. split.
  { clear -PRELSPEC. desf.
    splits; eauto. splits; eauto.
    right. exists p. splits; eauto. }

  set (rel'' :=
         if Rel w
         then TView.cur (Local.tview local)
         else TView.rel (Local.tview local) locw).
  
  assert (co wprev w) as COWPREV.
  { eapply rf_rmw_in_co; eauto. }
  assert (Time.lt (f_to wprev) (f_to w)) as PREVNLT.
  { eapply f_to_co_mon; eauto. }

  assert (Time.le (View.rlx rel'' locw)
                  (View.rlx (TView.cur (Local.Local.tview local)) locw)) as GG.
  { unfold rel''. destruct (Rel w).
    { reflexivity. }
    subst. eapply rel_le_cur; eauto. }

  assert (Time.lt (View.rlx rel'' locw) (f_to w)) as REL_VIEW_LT.
  { eapply TimeFacts.le_lt_lt; [by apply GG|].
    eapply TimeFacts.le_lt_lt; [|by apply PREVNLT].
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
    apply COVZ. eexists. apply seq_eqv_r; eauto. }

  set (rel' := View.join (View.join rel'' (View.unwrap p_rel))
                         (View.singleton_ur locw (f_to w))).
  assert (Time.le (View.rlx rel' locw) (f_to w)) as REL_VIEW_LE.
  { unfold rel'.
    unfold View.join, TimeMap.join. simpls.
    unfold TimeMap.singleton, LocFun.add.
    rewrite Loc.eq_dec_eq.
    apply Time.join_spec; [|reflexivity].
    apply Time.join_spec.
    { apply Time.le_lteq; auto. }
    admit. }

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

  simpls. splits; eauto.
  do 2 eexists. splits; eauto.

  assert (Time.lt (f_from w) (f_to w)) as WFLT by (by apply FCOH).
  assert (Message.wf (Message.full valw p_rel)) as MWF.
  { admit. }

  assert (exists promises_add,
             Memory.add promises_cancel locw
                        (f_from w) (f_to w) (Message.full valw p_rel)
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
                        (f_from w) (f_to w) (Message.full valw p_rel)
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
  
  do 2 eexists. splits; eauto.
  { admit. }
  { red. splits; eauto.
    red. admit. }
  admit.
Admitted.

End Aux.
