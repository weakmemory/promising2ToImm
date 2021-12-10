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
From imm Require Import AuxRel2.

From imm Require Import TraversalConfig.
Require Import SimulationRel.
Require Import SimState.
Require Import MemoryAux.
Require Import MaxValue.
Require Import ViewRel.
From imm Require Import ViewRelHelpers.
Require Import Event_imm_promise.
Require Import ExtTraversalConfig.
Require Import ExtTraversal.
Require Import ExtTraversalProperties.
From imm Require Import TraversalProperties.
Require Import FtoCoherent.
Require Import SimulationRelProperties.
Require Import IntervalHelper.
Require Import AuxTime.

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

Variable T : trav_config.
Variable S : actid -> Prop.
Hypothesis ETCCOH : etc_coherent G sc (mkETC T S).

Hypothesis RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T.

Variable f_to f_from : actid -> Time.t.
Hypothesis FCOH : f_to_coherent G S f_to f_from.

Variable thread : thread_id.
Variable PC : Configuration.t.
Variable local : Local.t.

Hypothesis SIM_TVIEW : sim_tview G sc (covered T) f_to (Local.tview local) thread.
Hypothesis SIM_MEM : sim_mem G sc T f_to f_from thread local (Configuration.memory PC).
Hypothesis INHAB : Memory.inhabited (Configuration.memory PC).
Hypothesis PLN_RLX_EQ : pln_rlx_eq (Local.tview local).
Hypothesis MEM_CLOSE : memory_close (Local.tview local) (Configuration.memory PC).

Hypothesis SIM_RES_MEM :
  sim_res_mem G T S f_to f_from thread local (Configuration.memory PC).

Hypothesis PROM_IN_MEM :
  forall thread' langst local
         (TID : IdentMap.find thread' (Configuration.threads PC) =
                Some (langst, local)),
    Memory.le (Local.promises local) (Configuration.memory PC).

(* In the correspoding case, we don't reserve new events
   so the simulation would be able to proceed with the same timestamp mapping functions,
   i.e. f_to' = f_to /\ f_from' = f_from, but we need to guarantee that
   the new message is not immediately before others
   (specifically, reservations introduced by the capped memory).
 *)
Lemma exists_time_interval_for_issue_reserved_no_next
      w locw valw langst smode
      (WNISS : ~ issued T w)
      (ISSUABLE : issuable G sc T w)
      (SW : S w)
      (NONEXT : dom_sb_S_rfrmw G (mkETC T S) rfi (eq w) ⊆₁ ∅)
      (LOC : loc lab w = Some locw)
      (VAL : val lab w = Some valw)
      (WTID : thread = tid w)
      (RESERVED_TIME: reserved_time G T S f_to f_from smode (Configuration.memory PC))
      (TID : IdentMap.find (tid w) (Configuration.threads PC) = Some (langst, local)) :
  let promises := (Local.promises local) in
  let memory   := (Configuration.memory PC) in
  let T'       := mkTC (covered T) (issued T ∪₁ eq w) in
  let S'       := S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G (mkETC T S) rfi (eq w) in
  exists p_rel, rfrmw_prev_rel G sc T f_to f_from (Configuration.memory PC) w locw p_rel /\
    let f_to' := upd f_to w (Time.middle (f_from w) (f_to w)) in
    let rel'' :=
        if is_rel lab w
        then (TView.cur (Local.tview local))
        else (TView.rel (Local.tview local) locw)
    in
    let rel' := (View.join (View.join rel'' (View.unwrap p_rel))
                           (View.singleton_ur locw (f_to' w))) in
    ⟪ RELWFEQ : View.pln rel' = View.rlx rel' ⟫ /\
    ⟪ REL_VIEW_LT : Time.lt (View.rlx rel'' locw) (f_to' w) ⟫ /\
    ⟪ REL_VIEW_LE : Time.le (View.rlx rel'  locw) (f_to' w) ⟫ /\

    ⟪ REQ_TO   : forall e (NEQ : e <> w), f_to' e = f_to e ⟫ /\
    ⟪ ISSEQ_TO : forall e (ISS : issued T e), f_to' e = f_to e ⟫ /\

    exists promises_cancel memory_cancel,
      ⟪ PCANCEL :
          Memory.remove promises locw (f_from w) (f_to w)
                        Message.reserve promises_cancel ⟫ /\
      ⟪ MCANCEL :
          Memory.remove memory locw (f_from w) (f_to w)
                        Message.reserve memory_cancel ⟫ /\

      exists promises_add memory_add,
        ⟪ PADD :
            Memory.add promises_cancel locw (f_from w) (f_to' w)
                       (Message.full valw (Some rel')) promises_add ⟫ /\
        ⟪ MADD :
            Memory.add memory_cancel locw (f_from w) (f_to' w)
                       (Message.full valw (Some rel')) memory_add ⟫ /\

        ⟪ INHAB : Memory.inhabited memory_add ⟫ /\
        ⟪ RELMCLOS : Memory.closed_timemap (View.rlx rel') memory_add ⟫ /\
        ⟪ RELVCLOS : Memory.closed_view rel' memory_add ⟫ /\

        ⟪ FCOH : f_to_coherent G S' f_to' f_from ⟫ /\

        ⟪ HELPER :
            sim_mem_helper
              G sc f_to' w (f_from w) valw
              (View.join (View.join (if is_rel lab w
                                     then (TView.cur (Local.tview local))
                                     else (TView.rel (Local.tview local) locw))
                                    (View.unwrap p_rel))
                         (View.singleton_ur locw (f_to' w))) ⟫ /\

        ⟪ RESERVED_TIME :
            reserved_time G T' S' f_to' f_from smode memory_add ⟫.
Proof using WF IMMCON ETCCOH RELCOV FCOH SIM_TVIEW SIM_RES_MEM SIM_MEM INHAB PLN_RLX_EQ MEM_CLOSE PROM_IN_MEM.
  assert (sc_per_loc G) as SPL.
  { apply coherence_sc_per_loc. apply IMMCON. }
  assert (complete G) as COMPL by apply IMMCON.
  assert (tc_coherent G sc T) as TCCOH by apply ETCCOH.

  (* set (AA:=TSTEP). *)
  (* destruct AA as [_ ETCCOH']. *)

  assert (E w) as EW.
  { by apply (etc_S_in_E ETCCOH). }
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

  assert (codom_rel (rf ⨾ rmw) w) as [wprev PRMWE].
  { eapply W_ex_in_codom_rfrmw; eauto. }
  
  assert (E wprev) as EPREV.
  { apply (wf_rfrmwE WF) in PRMWE. by destruct_seq PRMWE as [AA BB]. }
  assert (W wprev) as WPREV.
  { apply (wf_rfrmwD WF) in PRMWE. by destruct_seq PRMWE as [AA BB]. }
  
  assert (wprev <> w) as NEQPREV.
  { intros HH; subst. eapply wf_rfrmw_irr; eauto. }

  assert (loc lab wprev = Some locw) as PREVLOC.
  { rewrite <- LOC. by apply (wf_rfrmwl WF). }

  assert (issued T wprev) as ISSPREV.
  { assert ((issued T ∪₁ eq w) wprev) as AA.
    2: by destruct AA; desf.
    left. eapply (dom_rf_rmw_S_in_I WF ETCCOH).
    exists w. apply seqA. apply seq_eqv_r. split; auto. }
  assert (S wprev) as SPREV.
  { by apply (etc_I_in_S ETCCOH). }

  assert (dom_rel (rf ⨾ rmw ⨾ ⦗eq w⦘) ⊆₁ issued T) as RFRMWISS.
  { rewrite <- seqA. intros a [b HH]. apply seq_eqv_r in HH. desc; subst.
    assert (a = wprev); subst; auto.
    eapply wf_rfrmwf; eauto. }
  
  assert (dom_rel (rf ⨾ rmw ⨾ ⦗eq w⦘) ⊆₁ S) as DRFRMWS.
  { rewrite RFRMWISS. apply ETCCOH. }
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

  assert (Time.lt (f_from w) (f_to w)) as FFT by (by apply FCOH).
  assert (co wprev w) as COWPREV.
  { eapply rf_rmw_in_co; eauto. }
  
  set (f_to' := upd f_to w (Time.middle (f_from w) (f_to w))).
  assert (REQ_TO : forall e (NEQ : e <> w), f_to' e = f_to e).
  { ins. unfold f_to'. rewrite updo; auto. }
  assert (ISSEQ_TO : forall e (ISS : issued T e), f_to' e = f_to e).
  { ins. unfold f_to'. rewrite updo; auto. by intros HH; subst. }

  assert (Time.lt (f_to' wprev) (f_to w)) as PREVNLT.
  { rewrite REQ_TO; auto. eapply f_to_co_mon; eauto. }
  assert (Time.le (f_to' wprev) (f_from w)) as PREVNEF.
  { rewrite REQ_TO; auto. apply FCOH; eauto. }
  assert (Time.lt (f_to' wprev) (f_to' w)) as PREVNLT'.
  { unfold f_to' at 2. rewrite upds.
    eapply TimeFacts.le_lt_lt with (b:=f_from w); auto.
      by apply Time.middle_spec. }

  assert (Time.le (View.rlx rel'' locw)
                  (View.rlx (TView.cur (Local.tview local)) locw)) as GG.
  { unfold rel''. destruct (Rel w).
    { reflexivity. }
    subst. eapply rel_le_cur; eauto. }

  assert (Time.lt (View.rlx rel'' locw) (f_to' w)) as REL_VIEW_LT.
  { eapply TimeFacts.le_lt_lt; [by apply GG|].
    eapply TimeFacts.le_lt_lt; [|by apply PREVNLT'].
    rewrite REQ_TO; auto. eapply le_cur_f_to_wprev; eauto. }

  set (rel' := View.join (View.join rel'' (View.unwrap p_rel))
                         (View.singleton_ur locw (f_to' w))).
  assert (Time.le (View.rlx (View.unwrap p_rel) locw) (f_to' wprev)) as PREL_LE'.
  { rewrite REQ_TO; auto.
    eapply le_p_rel_f_to_wprev; eauto. }
  assert (Time.le (View.rlx (View.unwrap p_rel) locw) (f_to' w)) as PREL_LE.
  { desc.
    destruct PRELSPEC0; desc.
    { rewrite PREL. apply Time.bot_spec. }
    assert (p = wprev); subst.
    { eapply wf_rfrmwf; eauto. }
    apply Time.le_lteq. left.
    eapply TimeFacts.le_lt_lt.
    2: by apply PREVNLT'.
    done. }

  assert (Time.le (View.rlx rel' locw) (f_to' w)) as REL_VIEW_LE.
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
               (Configuration.memory PC) locw (f_from w) (f_to w)
                                         Message.reserve memory_cancel)
    as [memory_cancel MCANCEL].
  { by apply Memory.remove_exists. }

  assert (Time.lt (f_from w) (f_to' w)) as WFLT.
  { unfold f_to'. rewrite upds. by apply Time.middle_spec. }

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

  assert (Interval.le (f_from w, f_to' w) (f_from w, f_to w)) as LENIOI.
  { unfold f_to'. rewrite upds. constructor; simpls.
    { reflexivity. }
    apply Time.le_lteq. left. by apply Time.middle_spec. }

  assert (exists promises_add,
             Memory.add promises_cancel locw
                        (f_from w) (f_to' w) (Message.full valw (Some rel'))
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
    apply Interval.le_disjoint with (b:=(f_from w, f_to w)); auto.
    edestruct Memory.get_disjoint with (t1:=f_to w) (t2:=to2)
                                       (m:=Local.promises local); eauto.
    desf. }
  assert (exists memory_add,
             Memory.add memory_cancel locw
                        (f_from w) (f_to' w) (Message.full valw (Some rel'))
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
    apply Interval.le_disjoint with (b:=(f_from w, f_to w)); auto.
    edestruct Memory.get_disjoint with (t1:=f_to w) (t2:=to2)
                                       (m:=(Configuration.memory PC)); eauto.
    desf. }

  assert (Memory.inhabited memory_add) as INHABADD.
  { red. ins.
    erewrite Memory.add_o; eauto.
    erewrite Memory.remove_o; eauto.
    destruct (loc_ts_eq_dec (loc, Time.bot) (locw, f_to' w)) as [AA|LL']; simpls; desc; subst.
    { exfalso. eapply time_lt_bot with (a:=f_from w). rewrite AA0; auto. }
    rewrite !(loc_ts_eq_dec_neq LL').
    destruct (loc_ts_eq_dec (loc, Time.bot) (locw, f_to w)) as [AA|LL]; simpls; desc; subst.
    { exfalso. eapply time_lt_bot with (a:=f_from w). rewrite AA0; auto. }
    rewrite !(loc_ts_eq_dec_neq LL).
    apply INHAB. }

  assert (S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G (mkETC T S) rfi (eq w) ≡₁ S) as NEWS.
  { arewrite (dom_sb_S_rfrmw G (mkETC T S) rfi (eq w) ≡₁ ∅).
    generalize SW. basic_solver. }

  assert (reserved_time G (mkTC (covered T) (issued T ∪₁ eq w))
                        S f_to' f_from smode memory_add) as REST.
  { destruct smode; [|by apply RESERVED_TIME].
    unfold f_to'.
    red. splits.
    3: { intros x y SX SY CO FF.
         destruct (classic (x = w)); subst.
         2: { rewrite REQ_TO in FF; auto. by apply RESERVED_TIME. }
         exfalso. rewrite upds in FF.
         eapply Time.lt_strorder with (x:=Time.middle (f_from w) (f_to w)).
         rewrite FF at 2.
         apply TimeFacts.lt_le_lt with (b:=f_to w).
         2: by apply FCOH.
           by apply Time.middle_spec. }
    all: red; ins; erewrite Memory.add_o in MSG; eauto.
    all: destruct (loc_ts_eq_dec (l, to) (locw, f_to' w)) as [LTEQ|LTNEQ'].
    { simpls. desc; subst. right. exists w. splits; eauto.
      { clear. basic_solver. }
      rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in MSG. inv MSG. }
    { rewrite loc_ts_eq_dec_neq in MSG; eauto.
      erewrite Memory.remove_o in MSG; eauto.
      destruct (loc_ts_eq_dec (l, to) (locw, f_to w)) as [LTEQ|LTNEQ].
      { simpls. desc. subst. rewrite (loc_ts_eq_dec_eq locw (f_to w)) in MSG. inv MSG. }
      rewrite loc_ts_eq_dec_neq in MSG; eauto.
      eapply RESERVED_TIME in MSG. destruct MSG as [|MSG]; desc; subst; auto.
      right. exists b. splits; eauto.
        by left. }
    { simpls. desc; subst. 
      rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in MSG. inv MSG. }
    rewrite loc_ts_eq_dec_neq in MSG; eauto.
    erewrite Memory.remove_o in MSG; eauto.
    destruct (loc_ts_eq_dec (l, to) (locw, f_to w)) as [LTEQ|LTNEQ].
    { simpls. desc. subst. rewrite (loc_ts_eq_dec_eq locw (f_to w)) in MSG. inv MSG. }
    rewrite loc_ts_eq_dec_neq in MSG; eauto.
    eapply RESERVED_TIME in MSG.
    desc. subst.
    assert (b <> w) as NEQBW.
    { intros HH. subst. simpls.
      rewrite LOC0 in LOC. inv LOC.
      clear -LTNEQ. desf. }
    exists b. splits; eauto.
    intros [|AA]; desf. }

  assert (f_to_coherent G S f_to' f_from) as FCOH_NEW.
  { unfold f_to' in *.
    red. splits.
    { intros x []. rewrite REQ_TO; [|by intros HH; subst]. by apply FCOH. }
    { by apply FCOH. }
    all: ins; destruct (classic (x = w)); subst; [rewrite upds|rewrite updo; auto; by apply FCOH].
    { by apply Time.middle_spec. }
    { apply Time.le_lteq. left. apply TimeFacts.lt_le_lt with (b:=f_to w).
      { by apply Time.middle_spec. }
        by apply FCOH. }
    exfalso. apply WNISS. eapply dom_rf_rmw_S_in_I with (T:=mkETC T S); eauto.
    exists y. apply seqA. apply seq_eqv_r. by split. }

  assert (forall tmap (MCLOS : Memory.closed_timemap tmap (Configuration.memory PC)),
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
  { eapply sim_helper_issue with (S':=S); eauto. by apply ETCCOH. }
  eapply reserved_time_more.
  3: by apply NEWS.
  all: eauto.
  apply same_trav_config_refl.
Qed.

Lemma exists_time_interval_for_issue_reserved_with_next
      w locw valw langst wnext smode
      (SW : S w)
      (WNISS : ~ issued T w)
      (ISSUABLE : issuable G sc T w)
      (WNEXT : dom_sb_S_rfrmw G (mkETC T S) rfi (eq w) wnext)
      (LOC : loc lab w = Some locw)
      (VAL : val lab w = Some valw)
      (WTID : thread = tid w)
      (RESERVED_TIME: reserved_time G T S f_to f_from smode (Configuration.memory PC))
      (TID : IdentMap.find (tid w) (Configuration.threads PC) = Some (langst, local)) :
  let promises := (Local.promises local) in
  let memory   := (Configuration.memory PC) in
  let T'       := mkTC (covered T) (issued T ∪₁ eq w) in
  let S'       := S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G (mkETC T S) rfi (eq w) in
  let n_to     := Time.middle (f_from w) (f_to w) in
  let f_to'    := upd (upd f_to w n_to) wnext (f_to w) in
  let f_from'  := upd f_from wnext n_to in

  exists p_rel, rfrmw_prev_rel G sc T f_to f_from (Configuration.memory PC) w locw p_rel /\
    let rel'' :=
        if is_rel lab w
        then (TView.cur (Local.tview local))
        else (TView.rel (Local.tview local) locw)
    in
    let rel' := (View.join (View.join rel'' (View.unwrap p_rel))
                           (View.singleton_ur locw (f_to' w))) in
    ⟪ RELWFEQ : View.pln rel' = View.rlx rel' ⟫ /\
    ⟪ REL_VIEW_LT : Time.lt (View.rlx rel'' locw) (f_to' w) ⟫ /\
    ⟪ REL_VIEW_LE : Time.le (View.rlx rel'  locw) (f_to' w) ⟫ /\

    exists promises_split memory_split,
      ⟪ PSPLIT :
          Memory.split (Local.promises local) locw (f_from' w) (f_to' w) (f_to' wnext)
                       (Message.full valw (Some rel')) Message.reserve promises_split ⟫ /\
      ⟪ MSPLIT :
          Memory.split memory locw (f_from' w) (f_to' w) (f_to' wnext)
                       (Message.full valw (Some rel')) Message.reserve memory_split ⟫ /\

      ⟪ INHAB : Memory.inhabited memory_split ⟫ /\
      ⟪ RELMCLOS : Memory.closed_timemap (View.rlx rel') memory_split ⟫ /\
      ⟪ RELVCLOS : Memory.closed_view rel' memory_split ⟫ /\

      ⟪ FCOH : f_to_coherent G S' f_to' f_from' ⟫ /\

      ⟪ HELPER :
          sim_mem_helper
            G sc f_to' w (f_from' w) valw
            (View.join (View.join (if is_rel lab w
                                   then (TView.cur (Local.tview local))
                                   else (TView.rel (Local.tview local) locw))
                                  (View.unwrap p_rel))
                       (View.singleton_ur locw (f_to' w))) ⟫ /\

      ⟪ RESERVED_TIME :
          reserved_time G T' S' f_to' f_from' smode memory_split ⟫.
Proof using WF IMMCON ETCCOH RELCOV FCOH SIM_TVIEW SIM_RES_MEM SIM_MEM INHAB PLN_RLX_EQ MEM_CLOSE PROM_IN_MEM.
  assert (sc_per_loc G) as SPL.
  { apply coherence_sc_per_loc. apply IMMCON. }
  assert (complete G) as COMPL by apply IMMCON.
  assert (tc_coherent G sc T) as TCCOH by apply ETCCOH.

  assert (E w) as EW.
  { by apply (etc_S_in_E ETCCOH). }
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

  assert (codom_rel (rf ⨾ rmw) w) as [wprev PRMWE].
  { eapply W_ex_in_codom_rfrmw; eauto. }
  
  assert (E wprev) as EPREV.
  { apply (wf_rfrmwE WF) in PRMWE. by destruct_seq PRMWE as [AA BB]. }
  assert (W wprev) as WPREV.
  { apply (wf_rfrmwD WF) in PRMWE. by destruct_seq PRMWE as [AA BB]. }
  
  assert (wprev <> w) as NEQPREV.
  { intros HH; subst. eapply wf_rfrmw_irr; eauto. }

  assert (loc lab wprev = Some locw) as PREVLOC.
  { rewrite <- LOC. by apply (wf_rfrmwl WF). }

  assert (issued T wprev) as ISSPREV.
  { assert ((issued T ∪₁ eq w) wprev) as AA.
    2: by destruct AA; desf.
    left. eapply (dom_rf_rmw_S_in_I WF ETCCOH).
    exists w. apply seqA. apply seq_eqv_r. split; auto. }
  assert (S wprev) as SPREV.
  { by apply (etc_I_in_S ETCCOH). }

  assert (dom_rel (rf ⨾ rmw ⨾ ⦗eq w⦘) ⊆₁ issued T) as RFRMWISS.
  { rewrite <- seqA. intros a [b HH]. apply seq_eqv_r in HH. desc; subst.
    assert (a = wprev); subst; auto.
    eapply wf_rfrmwf; eauto. }
  
  assert (dom_rel (rf ⨾ rmw ⨾ ⦗eq w⦘) ⊆₁ S) as DRFRMWS.
  { rewrite RFRMWISS. apply ETCCOH. }
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
  { apply (wf_coE WF) in COWNEXT. by destruct_seq COWNEXT as [AA BB]. }
  assert (~ S wnext) as NSNEXT.
  { intros HH. apply WNISS. eapply dom_rf_rmw_S_in_I with (T:=mkETC T S); eauto.
    exists wnext. apply seqA. apply seq_eqv_r. by split. }
  assert (~ issued T wnext) as NINEXT.
  { intros HH. apply NSNEXT. by apply (etc_I_in_S ETCCOH). }
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
    eapply le_cur_f_to_wprev with (w:=w) (wprev:=wprev); eauto. }

  set (rel' := View.join (View.join rel'' (View.unwrap p_rel))
                         (View.singleton_ur locw (f_to' w))).
  assert (Time.le (View.rlx (View.unwrap p_rel) locw) (f_to wprev)) as PREL_LE'.
  { eapply le_p_rel_f_to_wprev with (w:=w) (wprev:=wprev); eauto. }
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
             Memory.split (Configuration.memory PC) locw
                          (f_from' w) (f_to' w) (f_to' wnext)
                          (Message.full valw (Some rel'))
                          Message.reserve memory_split)
    as [memory_split MSPLIT].
  { unfold f_from'. rewrite updo; auto.
    unfold f_to'. rewrite upds. rewrite updo; auto. rewrite upds.
      by apply Memory.split_exists. }

  assert (forall tmap (MCLOS : Memory.closed_timemap tmap (Configuration.memory PC)),
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
      edestruct (wf_co_total WF) with (a:=x) (b:=w); eauto.
      2: by exfalso; eapply rfrmw_in_im_co; eauto.
      split; [split|].
      { by apply (etc_S_in_E ETCCOH). }
      { by apply (reservedW WF ETCCOH). }
      apply (wf_col WF) in CO. rewrite CO.
      rewrite <- LOC. symmetry. by apply wf_rfrmwl. }
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

  assert (S ⊆₁ E ∩₁ W) as SEW.
  { apply set_subset_inter_r. split; [by apply ETCCOH|].
    apply (reservedW WF ETCCOH). }
  
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
         2: rewrite RMW_BEF_S; basic_solver 10.
         rewrite <- FOR_SPLIT.
         hahn_frame.
         clear. apply eqv_rel_mori.
         apply AuxRel.set_compl_mori. red.
         basic_solver 10. }
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
           apply no_co_to_init in CO; auto. destruct_seq_r CO as BB.
           edestruct to_from_disjoint_from with (w:=w) (w':=y) (I:=S) as [AA|AA]; eauto.
           { by apply wf_col. }
           { rewrite <- HH in AA. by eapply time_middle_lt_lhs; [|apply AA]. }
           rewrite <- HH in AA. by eapply time_middle_le_rhs; [|apply AA]. }
         { rewrite upds. rewrite updo; auto.
           destruct (classic (x = w)) as [|NEQXW]; subst; auto.
           rewrite updo; auto.
           unfold n_to. intros HH.
           exfalso.
           edestruct to_from_disjoint_to with (w:=w) (w':=x) (I:=S) as [AA|AA]; eauto.
           { red. rewrite LOC. symmetry. rewrite <- NLOC. by apply (wf_col WF). }
           { rewrite HH in AA. by eapply time_middle_le_lhs; [|apply AA]. }
           rewrite HH in AA. by eapply time_middle_lt_rhs; [|apply AA]. }
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
      assert (S b) as SB by (by apply (etc_I_in_S ETCCOH)).
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
  3: { etransitivity; [by apply (etc_I_in_S ETCCOH)|]. basic_solver. }
  2: basic_solver.
  unfold f_to'. ins. by repeat (rewrite updo; [|by intros HH; desf]).
Qed.

End Aux.
