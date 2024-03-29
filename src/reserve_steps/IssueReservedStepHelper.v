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
From hahnExt Require Import HahnExt.
From imm Require Import SimClosure.

From imm Require Import TraversalOrder.
From imm Require Import TLSCoherency.
From imm Require Import IordCoherency.
From imm Require Import TlsEventSets.
From imm Require Import TlsViewRelHelpers.
Require Import SimulationRel.
Require Import SimState.
Require Import MemoryAux.
Require Import MaxValue.
Require Import ViewRel.
Require Import Event_imm_promise.
Require Import ExtTraversalConfig.
Require Import ExtTraversal.
Require Import ExtTraversalProperties.
Require Import FtoCoherent.
Require Import SimulationRelProperties.
Require Import ExistsIssueReservedInterval.
Require Import IntervalHelper.
From imm Require Import EventsTraversalOrder. 

Set Implicit Arguments.

Section IssueReservedStepHelper.

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
(* Notation "'RW'" := (fun x => R x \/ W x). *)
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

Variable IMMCON : imm_consistent G sc.

Variable T : trav_label -> Prop.
Hypothesis TCOH : tls_coherent G T.
Hypothesis ICOH : iord_coherent G sc T.
Hypothesis RCOH : reserve_coherent G T.

Notation "'C'" := (covered T). 
Notation "'I'" := (issued T). 
Notation "'S'" := (reserved T). 

Variable RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T.

Variable f_to f_from : actid -> Time.t.
Variable FCOH : f_to_coherent G S f_to f_from.

Variable PC : Configuration.t.
Hypothesis THREAD : forall t (IN : (threads_set G \₁ eq tid_init) t), IdentMap.In t (Configuration.threads PC).

Variable smode : sim_mode.
Hypothesis SC_REQ :
  smode = sim_normal -> 
  forall (l : Loc.t),
    max_value f_to (S_tm G l (covered T)) (LocFun.find l (Configuration.sc PC)).

Variable thread : thread_id.
Variable local : Local.t.
Hypothesis SIM_PROM     : sim_prom     G sc T   f_to f_from thread (Local.promises local).
Hypothesis SIM_RES_PROM : sim_res_prom G    T f_to f_from thread (Local.promises local).

Hypothesis CLOSED_SC : Memory.closed_timemap (Configuration.sc PC) (Configuration.memory PC).

Hypothesis PROM_DISJOINT :
  forall thread' langst' local'
         (TNEQ : thread <> thread')
         (TID' : IdentMap.find thread' (Configuration.threads PC) =
                 Some (langst', local')),
  forall loc to,
    Memory.get loc to local .(Local.promises) = None \/
    Memory.get loc to local'.(Local.promises) = None.

Hypothesis PROM_IN_MEM :
  forall thread' langst local
         (TID : IdentMap.find thread' (Configuration.threads PC) =
                Some (langst, local)),
    Memory.le (Local.promises local) (Configuration.memory PC).

Hypothesis INHAB      : Memory.inhabited (Configuration.memory PC).
Hypothesis CLOSED_MEM : Memory.closed (Configuration.memory PC).
Hypothesis PLN_RLX_EQ : pln_rlx_eq (Local.tview local).
Hypothesis MEM_CLOSE : memory_close (Local.tview local) (Configuration.memory PC).

Hypothesis RESERVED_TIME:
  reserved_time G T f_to f_from smode (Configuration.memory PC).

Hypothesis SIM_RES_MEM :
  sim_res_mem G T f_to f_from thread local (Configuration.memory PC).

Hypothesis SIM_MEM : sim_mem G sc T f_to f_from thread local (Configuration.memory PC).
Hypothesis SIM_TVIEW : sim_tview G sc (covered T) f_to (Local.tview local) thread.

Lemma issue_reserved_step_helper_no_next r w valw locw ordw langst
      (TID : IdentMap.find (tid w) (Configuration.threads PC) = Some (langst, local))
      (RMW : rmw r w) (SW : S w)
      (NISSB : ~ issued T w)
      (ISSUABLE : issuable G sc T w)
      (NONEXT : dom_sb_S_rfrmw G T rfi (eq w) ⊆₁ ∅)
      (LOC : loc lab w = Some locw)
      (VAL : val lab w = Some valw)
      (ORD : mod lab w = ordw)
      (WTID : thread = tid w) :
  let promises := (Local.promises local) in
  let memory   := (Configuration.memory PC) in
  let sc_view  := (Configuration.sc PC) in
  (* let covered' := if Rel w then covered T ∪₁ eq w else covered T in *)
  (* let T'       := mkTC covered' (issued T ∪₁ eq w) in *)
  (* let S'       := S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G (mkETC T S) rfi (eq w) in *)
  let T' := T ∪₁ (if Rel w then eq (mkTL ta_cover w) else ∅) ∪₁ eq (mkTL ta_issue w) ∪₁ (eq ta_reserve <*> (eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w))) in
  exists p_rel, rfrmw_prev_rel G sc T f_to f_from (Configuration.memory PC) w locw p_rel /\
    let f_to' := upd f_to w (Time.middle (f_from w) (f_to w)) in
    let rel'' :=
        if is_rel lab w
        then (TView.cur (Local.tview local))
        else (TView.rel (Local.tview local) locw)
    in
    let rel' := (View.join (View.join rel'' (View.unwrap p_rel))
                           (View.singleton_ur locw (f_to' w))) in

    ⟪ REL_VIEW_LT : Time.lt (View.rlx rel'' locw) (f_to' w) ⟫ /\
    ⟪ REL_VIEW_LE : Time.le (View.rlx rel' locw) (f_to' w) ⟫ /\

    << NINMEM : Memory.get locw (f_to' w) (Configuration.memory PC) = None >> /\

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

        ⟪ FCOH : f_to_coherent G (reserved T') f_to' f_from ⟫ /\

      exists promises',
        ⟪ PEQ :
            if Rel w
            then Memory.remove promises_add locw (f_from w) (f_to' w)
                               (Message.full valw (Some rel')) promises'
            else promises' = promises_add ⟫ /\

        ⟪ NEW_PROM_IN_MEM : Memory.le promises' memory_add ⟫ /\

        ⟪ HELPER :
            sim_mem_helper
              G sc f_to' w (f_from w) valw
              (View.join (View.join (if is_rel lab w
                                     then (TView.cur (Local.tview local))
                                     else (TView.rel (Local.tview local) locw))
                                    (View.unwrap p_rel))
                         (View.singleton_ur locw (f_to' w))) ⟫ /\

        ⟪ RESERVED_TIME :
            reserved_time G T' f_to' f_from smode memory_add ⟫ /\

        let tview' := if is_rel lab w
                      then TView.write_tview
                             (Local.tview local) sc_view locw
                             (f_to' w) (Event_imm_promise.wmod ordw)
                      else (Local.tview local) in
        let local' := Local.Local.mk tview' promises' in
        let threads' :=
            IdentMap.add (tid w)
                         (langst, local')
                         (Configuration.threads PC) in

        ⟪ THREAD : forall t (IN : (threads_set G \₁ eq tid_init) t), IdentMap.In t threads' ⟫ /\

        ⟪ SC_REQ : smode = sim_normal -> 
                   forall (l : Loc.t),
                     max_value f_to' (S_tm G l (covered T)) (LocFun.find l sc_view) ⟫ /\
        ⟪ CLOSED_SC : Memory.closed_timemap sc_view memory_add ⟫ /\

        ⟪ MEM_CANCEL :
            Memory.promise (Local.promises local) memory locw (f_from w) (f_to w)
                           Message.reserve
                           promises_cancel memory_cancel Memory.op_kind_cancel ⟫ /\

        ⟪ MEM_PROMISE :
            Memory.promise promises_cancel memory_cancel locw (f_from w) (f_to' w)
                           (Message.full valw (Some rel'))
                           promises_add memory_add Memory.op_kind_add ⟫ /\
        ⟪ PROM_IN_MEM :
            forall thread' langst local
                   (TID : IdentMap.find thread' threads' = Some (langst, local)),
              Memory.le (Local.promises local) memory_add ⟫ /\

        ⟪ SIM_PROM     : sim_prom G sc T' f_to' f_from (tid w) promises'  ⟫ /\
        ⟪ SIM_RES_PROM : sim_res_prom G T' f_to' f_from (tid w) promises'  ⟫ /\

        ⟪ PROM_DISJOINT :
            forall thread' langst' local'
                   (TNEQ : tid w <> thread')
                   (TID' : IdentMap.find thread' threads' =
                           Some (langst', local')),
            forall loc to,
              Memory.get loc to promises' = None \/
              Memory.get loc to local'.(Local.promises) = None ⟫ /\

        ⟪ SIM_MEM     : sim_mem G sc T' f_to' f_from (tid w) local' memory_add ⟫ /\
        ⟪ SIM_RES_MEM : sim_res_mem G T' f_to' f_from (tid w) local' memory_add ⟫ /\
        ⟪ NOWLOC : Rel w -> Memory.nonsynch_loc locw (Local.promises local) ⟫.
Proof using All.
  assert (complete G) as COMPL by apply IMMCON.
  assert (sc_per_loc G) as SPL by (apply coherence_sc_per_loc; apply IMMCON).

  subst.
  edestruct exists_time_interval_for_issue_reserved_no_next as [p_rel [PREL HH]]; eauto.
  simpls; desc.
  
  assert (S ⊆₁ E ∩₁ W) as SEW.
  { apply set_subset_inter_r. split; [by apply RCOH|].
    eapply reservedW; eauto. }
  assert (E w /\ W w) as [EW WW] by (by apply SEW).
  assert (~ covered T w) as NCOVB.
  { intros AA. apply NISSB. eapply w_covered_issued; eauto. by split. }

  assert (W_ex w) as WEW.
  { apply RCOH. by split. }
  assert (codom_rel (⦗issued T⦘ ⨾ rf ⨾ rmw) w) as CDRFRMW.
  { eapply W_ex_in_codom_rfrmw in WEW; eauto.
    destruct WEW as [u WEW].
    exists u. apply seq_eqv_l. split; auto.
    eapply ExtTraversalProperties.dom_rf_rmw_S_in_I; eauto.
    exists w. apply seqA. apply seq_eqv_r. split; auto. }
  
  assert (R r) as RR.
  { apply (wf_rmwD WF) in RMW. by destruct_seq RMW as [AA BB]. }

  assert (Memory.le promises_add memory_add) as PP.
  { eapply memory_le_add2 with (mem1:=promises_cancel) (mem2:=memory_cancel); eauto.
    eapply memory_le_remove2; eauto. }

  assert (Memory.le promises_cancel memory_add) as PPC.
  { etransitivity; [|by apply PP].
    eapply memory_add_le; eauto. }

  assert (Memory.get locw (f_to w) (Local.promises local) =
          Some (f_from w, Message.reserve)) as INPROM.
  { eapply SIM_RES_MEM; eauto. }
  assert (Memory.get locw (f_to w) (Configuration.memory PC) =
          Some (f_from w, Message.reserve)) as INMEM.
  { eapply PROM_IN_MEM in INPROM; eauto. }

  assert (forall thread' langst' local' (TNEQ : tid w <> thread')
                 (TID' : IdentMap.find thread' (Configuration.threads PC) =
                         Some (langst', local')),
             Memory.get locw (f_to w) (Local.promises local') = None) as NINTER.
  { ins. eapply PROM_DISJOINT with (loc:=locw) (to:=f_to w) in TID'; eauto. desf. }

  set (S':=S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w)).
  assert (S' ⊆₁ E ∩₁ W) as SEW'.
  { subst S'. rewrite SEW at 1. unionL; eauto with hahn.
    { unfolder. ins. desf. }
    intros x HH. apply NONEXT in HH. inv HH. }

  assert (~ is_init w) as NINIT.
  { intros AA. apply NCOVB. eby eapply init_covered. }
  assert (Time.lt (f_from w) (f_to w)) as FLT by (by apply FCOH).
  
  set (f_to' := upd f_to w (Time.middle (f_from w) (f_to w))).
  assert (f_to' w <> Time.bot) as FNNBOT.
  { intros AA.
    eapply Time.lt_strorder with (x:=f_to' w). rewrite AA at 1.
    unfold f_to'. rewrite upds.
    apply TimeFacts.le_lt_lt with (b:=f_from w); auto.
    { apply Time.bot_spec. }
      by apply Time.middle_spec. }

  assert (forall thread' langst' local' (TNEQ : tid w <> thread')
                 (TID' : IdentMap.find thread' (Configuration.threads PC) =
                         Some (langst', local')),
             Memory.get locw (f_to' w) (Local.promises local') = None) as NINTER'.
  { ins.
    destruct (Memory.get locw (f_to' w) (Local.promises local')) eqn:HH; auto.
    exfalso.
    destruct p as [from msg]. eapply PROM_IN_MEM in HH; eauto.
    edestruct Memory.get_disjoint as [AA|AA].
    { apply HH. }
    { apply INMEM. }
    { desc; subst. unfold f_to' in AA. rewrite upds in AA.
      eapply Time.lt_strorder with (x:=f_to w). rewrite <- AA at 1.
        by apply Time.middle_spec. }
    apply Memory.get_ts in HH. destruct HH as [HH|HH]; desc; eauto.
    apply AA with (x:=f_to' w); constructor; simpls; try reflexivity.
    all: unfold f_to'; rewrite upds.
    2: apply Time.le_lteq; left.
    all: by apply Time.middle_spec. }

  assert (forall tmap (MCLOS : Memory.closed_timemap tmap (Configuration.memory PC)),
             Memory.closed_timemap tmap memory_add) as MADDCLOS.
  { ins. eapply Memory.add_closed_timemap; eauto.
    eapply Memory.cancel_closed_timemap; eauto. }

  set (rel'' :=
        if is_rel lab w
        then (TView.cur (Local.tview local))
        else (TView.rel (Local.tview local) locw)).
  set (rel' := (View.join (View.join rel'' (View.unwrap p_rel))
                          (View.singleton_ur locw (f_to' w)))).

  assert (exists promises',
             ⟪ PEQ :
                 if Rel w
                 then Memory.remove promises_add locw (f_from w) (f_to' w)
                                    (Message.full valw (Some rel')) promises'
                 else promises' = promises_add ⟫).
  { destruct (is_rel lab w) eqn:REL; eauto.
    edestruct Memory.remove_exists as [promises'].
    2: { exists promises'. eauto. }
    erewrite Memory.add_o; eauto. rewrite loc_ts_eq_dec_eq; auto. }
  desc.
  
  assert (Memory.le promises' promises_add) as LEPADD.
  { destruct (Rel w) eqn:RELB; subst; [|reflexivity].
    eapply memory_remove_le; eauto. }

  assert (Memory.le promises' memory_add) as NEW_PROM_IN_MEM.
  { etransitivity; eauto. }

  assert (forall l to from msg 
                 (NEQ : l <> locw \/ to <> f_to w),
             Memory.get l to promises_cancel = Some (from, msg) <->
             Memory.get l to (Local.promises local) = Some (from, msg))
    as NOTNEWC.
  { ins. erewrite Memory.remove_o; eauto. by rewrite loc_ts_eq_dec_neq. }

  assert (forall l to from msg 
                 (NEQ  : l <> locw \/ to <> f_to  w)
                 (NEQ' : l <> locw \/ to <> f_to' w),
             Memory.get l to memory_add = Some (from, msg) <->
             Memory.get l to (Configuration.memory PC) = Some (from, msg))
    as NOTNEWM.
  { ins. erewrite Memory.add_o; eauto.
    rewrite loc_ts_eq_dec_neq; auto.
    erewrite Memory.remove_o; eauto. by rewrite loc_ts_eq_dec_neq. }

  assert (forall l to from msg 
                 (NEQ  : l <> locw \/ to <> f_to  w)
                 (NEQ' : l <> locw \/ to <> f_to' w),
             Memory.get l to promises_add = Some (from, msg) <->
             Memory.get l to (Local.promises local) = Some (from, msg))
    as NOTNEWA.
  { ins. erewrite Memory.add_o; eauto.
    rewrite loc_ts_eq_dec_neq; auto. }

  assert (forall l to from msg 
                 (NEQ  : l <> locw \/ to <> f_to  w)
                 (NEQ' : l <> locw \/ to <> f_to' w),
             Memory.get l to promises' = Some (from, msg) <->
             Memory.get l to (Local.promises local) = Some (from, msg))
    as NOTNEWP.
  { ins. destruct (Rel w); subst; auto.
    erewrite Memory.remove_o; eauto. rewrite loc_ts_eq_dec_neq; auto. }

  assert (~ Rel w ->
          Memory.get locw (f_to' w) promises' =
          Some (f_from w, Message.full valw (Some rel')))
    as INP''.
  { ins. destruct (Rel w); subst; [by desf|].
    erewrite Memory.add_o; eauto. by rewrite loc_ts_eq_dec_eq. }

  assert (Time.lt (f_to' w) (f_to w)) as FTLT.
  { unfold f_to'; rewrite upds. by apply Time.middle_spec. }
  assert (Time.le (f_to' w) (f_to w)) as FTLE.
  { apply Time.le_lteq. eauto. }
  assert (Time.lt (f_from w) (f_to' w)) as FFLT.
  { unfold f_to'; rewrite upds. by apply Time.middle_spec. }

  assert (NEQT : f_to' w <> f_to w).
  { intros HH. apply Time.lt_strorder with (x:=f_to w). rewrite <- HH at 1; auto. }

  assert (Memory.get locw (f_to' w) (Configuration.memory PC) = None) as NINMEM.
  { destruct (Memory.get locw (f_to' w) (Configuration.memory PC)) eqn:HH; auto.
    exfalso.
    destruct p as [from msg].
    set (BB:=HH). apply Memory.get_ts in BB. destruct BB as [|BB]; desc; subst; auto.
    edestruct Memory.get_disjoint as [AA|AA].
    { apply HH. }
    { apply INMEM. }
    { desf. }
    apply AA with (x:=f_to' w); constructor; simpls; auto. reflexivity. }

  
  assert (covered
            (T ∪₁ (if Rel w then eq (mkTL ta_cover w) else ∅)
                 ∪₁ eq (mkTL ta_issue w)
                 ∪₁ eq ta_reserve <*> (eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w))) ≡₁
            C ∪₁ (if Rel w then eq w else ∅)) as COV'.
  { clear. simplify_tls_events.
    unfold is_rel. destruct (mode_le Orel (mod lab w)); [rewrite set_collect_eq| ]; basic_solver. }
  assert (issued
            (T ∪₁ (if Rel w then eq (mkTL ta_cover w) else ∅)
                 ∪₁ eq (mkTL ta_issue w)
                 ∪₁ eq ta_reserve <*> (eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w))) ≡₁
            I ∪₁ eq w) as ISS'.
  { clear. simplify_tls_events. basic_solver. }
  assert (reserved
            (T ∪₁ (if Rel w then eq (mkTL ta_cover w) else ∅)
                 ∪₁ eq (mkTL ta_issue w)
                 ∪₁ eq ta_reserve <*> (eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w))) ≡₁
            S') as RES'.
  { clear. simplify_tls_events. subst S'. basic_solver. }
  assert (f_to_coherent G S' f_to' f_from) as FCOH'.
  { eapply f_to_coherent_more; [..| apply FCOH0]; eauto.
    subst S'. clear. simplify_tls_events. basic_solver. }

  exists p_rel. splits; eauto.
  do 2 eexists. splits; eauto.
  do 2 eexists. splits; eauto.
  { eapply f_to_coherent_more; [..| apply FCOH']; eauto. }
  exists promises'. splits; eauto.
  { eapply reserved_time_same_issued_reserved; eauto.
    all: clear; simplify_tls_events; basic_solver. }    
  { intros e' EE. 
    apply IdentMap.Facts.add_in_iff.
    destruct (Ident.eq_dec e' (tid w)) as [|NEQ]; subst; auto. }
  { ins. eapply sc_view_f_issued with (f_to:=f_to); eauto. }
  { apply Memory.promise_add; auto; ins.
    erewrite Memory.remove_o in GET; eauto.
    destruct (classic (to' = f_to w)) as [|NEQ]; subst.
    { rewrite loc_ts_eq_dec_eq in GET. inv GET. }
    rewrite loc_ts_eq_dec_neq in GET; eauto.
    edestruct Memory.get_disjoint as [AA|AA].
    { apply GET. }
    { apply INMEM. }
    { desc; subst. unfold f_to' in AA0. rewrite upds in AA0.
      eapply Time.lt_strorder with (x:=f_from w). rewrite <- AA0 at 2.
        by apply Time.middle_spec. }
    apply Memory.get_ts in GET. destruct GET as [HH|HH]; desc; eauto.
    destruct (TimeFacts.le_lt_dec to' (f_to w)) as [LE|LT].
    { apply AA with (x:=to'); constructor; simpls; try reflexivity.
      transitivity (f_to' w); auto. }
    apply AA with (x:=f_to w); constructor; simpls; auto; try reflexivity.
      by apply Time.le_lteq; eauto. }
  { ins.
    destruct (Ident.eq_dec thread' (tid w)) as [EQ|NEQ].
    { subst. rewrite IdentMap.gss in TID0.
      inv TID0; simpls; clear TID0. }
    red; ins; rewrite IdentMap.gso in TID0; auto.
    erewrite Memory.add_o; eauto.
    destruct (loc_ts_eq_dec (loc, to) (locw, f_to' w)) as [[A B]|LL'].
    { simpls; rewrite A in *; rewrite B in *; subst.
      exfalso. erewrite NINTER' in LHS; eauto. inv LHS. }
    rewrite (loc_ts_eq_dec_neq LL').
    destruct (loc_ts_eq_dec (loc, to) (locw, f_to w)) as [[A B]|LL].
    { simpls; rewrite A in *; rewrite B in *; subst.
      exfalso. erewrite NINTER in LHS; eauto. inv LHS. }
    erewrite Memory.remove_o; eauto.
    rewrite (loc_ts_eq_dec_neq LL).
    eapply PROM_IN_MEM in LHS; eauto. }
  { simpls. red. ins.
    destruct (loc_ts_eq_dec (l, to) (locw, f_to' w)) as [[A' B']|LL'].
    { simpls; rewrite A' in *; rewrite B' in *.
      destruct (Rel w) eqn:RELB; subst.
      { erewrite Memory.remove_o in PROM; eauto.
        rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in PROM. inv PROM. }
      erewrite Memory.add_o in PROM; eauto.
      rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in PROM.
      inv PROM. exists w. splits; eauto.
      { clear. find_event_set. }
      clear -NCOVB. separate_set_event. }
    destruct (loc_ts_eq_dec (l, to) (locw, f_to w)) as [[A' B']|LL].
    { simpls; rewrite A' in *; rewrite B' in *. exfalso.
      enough (Memory.get locw (f_to w) promises_add = Some (from, Message.full v rel) ->
              False).
      { by destruct (Rel w) eqn:RELB; subst; eauto. }
      intros AA.
      erewrite Memory.add_o in AA; eauto.
      rewrite loc_ts_eq_dec_neq in AA; auto.
      erewrite Memory.remove_o in AA; eauto.
      rewrite loc_ts_eq_dec_eq in AA. inv AA. }
    eapply NOTNEWP in PROM; eauto.
    edestruct SIM_PROM as [b H]; eauto; desc.
    exists b; splits; auto.
    { clear -ISS. find_event_set. }
    { clear -NCOV NISSB ISS. separate_set_event. }
    { by rewrite ISSEQ_TO. }
    eapply sim_mem_helper_f_issued; eauto. }
  { simpls. red. ins.
    destruct (loc_ts_eq_dec (l, to) (locw, f_to' w)) as [[A' B']|LL'].
    { simpls; rewrite A' in *; rewrite B' in *.
      destruct (Rel w) eqn:RELB; subst.
      { erewrite Memory.remove_o in RES; eauto.
        rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in RES. inv RES. }
      erewrite Memory.add_o in RES; eauto.
      rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in RES. inv RES. }
    destruct (loc_ts_eq_dec (l, to) (locw, f_to w)) as [[A' B']|LL].
    { simpls; rewrite A' in *; rewrite B' in *. exfalso.
      enough (Memory.get locw (f_to w) promises_add = Some (from, Message.reserve) ->
              False).
      { destruct (Rel w) eqn:RELB; subst; auto. }
      intros AA.
      erewrite Memory.add_o in AA; eauto.
      rewrite loc_ts_eq_dec_neq in AA; auto.
      erewrite Memory.remove_o in AA; eauto.
      rewrite loc_ts_eq_dec_eq in AA; auto. inv AA. }
    apply NOTNEWP in RES; auto.
    edestruct SIM_RES_PROM as [b H]; eauto; desc.
    exists b. splits; auto.
    { clear - RES0. find_event_set. }
    { separate_set_event. }
    rewrite REQ_TO; auto. simpls. intros HH; subst.
    rewrite LOC0 in LOC. inv LOC. desf. }
  { ins.
    rewrite IdentMap.gso in TID'; auto.
    destruct (loc_ts_eq_dec (loc, to) (locw, (f_to' w))) as [EQ|NEQ']; simpls.
    { desc. subst. right.
      destruct (Memory.get locw (f_to' w) (Local.promises local')) eqn: HH; auto.
      exfalso.
      erewrite NINTER' in HH; eauto. inv HH. }
    destruct (loc_ts_eq_dec (loc, to) (locw, (f_to w))) as [EQ|NEQ]; simpls.
    { desc. subst. right.
      destruct (Memory.get locw (f_to w) (Local.promises local')) eqn: HH; auto.
      exfalso.
      erewrite NINTER in HH; eauto. inv HH. }
    edestruct (PROM_DISJOINT TNEQ TID') as [HH|HH]; eauto.
    left.
    destruct (Memory.get loc to promises') eqn:BB; auto.
    destruct p. eapply NOTNEWP in BB; eauto. desf. }
  { red. ins. apply ISS' in ISSB. 
    destruct ISSB as [ISSB|]; subst.
    { edestruct SIM_MEM as [rel_opt HH]; eauto. simpls. desc.
      exists rel_opt. unnw.
      assert (b <> w) as BNEQ by (by intros HH; subst).
      destruct (loc_ts_eq_dec (l, f_to b) (locw, f_to w)) as [EQ|NEQ]; simpls; desc; subst.
      { exfalso.
        apply BNEQ.
        eapply f_to_eq with (I:=S); eauto.
        { red. by rewrite LOC. }
          eapply rcoh_I_in_S; eauto. }
      destruct (loc_ts_eq_dec (l, f_to b) (locw, (f_to' w))) as [EQ|NEQ']; simpls; desc; subst.
      { exfalso. rewrite <- REQ_TO in EQ0; auto.
        eapply f_to_eq in EQ0; (try by apply FCOH0); eauto.
        { clear -SEW'. simplify_tls_events. rewrite <- SEW'. subst S'. basic_solver. } 
        { red. by rewrite LOC. }
        { eapply rcoh_I_in_S in ISSB; eauto. clear -ISSB.
          find_event_set. }
        clear -SW. find_event_set. }
      unfold f_to' in *. rewrite REQ_TO with (e:=b); auto.
      erewrite Memory.add_o with (mem2:=memory_add); eauto.
      erewrite Memory.remove_o with (mem2:=memory_cancel); eauto.
      rewrite !loc_ts_eq_dec_neq; auto.
      splits; eauto.
      { eapply sim_mem_helper_f_issued with (f_to:=f_to); eauto. }
      intros AA BB.
      assert (~ covered T b) as NCOVBB.
      { intros HH. apply BB. clear -HH. find_event_set. }
      specialize (HH1 AA NCOVBB).
      desc. splits; auto.
      { apply NOTNEWP; auto. }
      eexists. splits; eauto.
      2: { destruct HH2 as [[CC DD]|CC]; [left|right].
           { split; eauto. intros [y HH]. destruct_seq_l HH as OO.
             apply ISS' in OO. 
             destruct OO as [OO|]; subst.
             { apply CC. exists y. apply seq_eqv_l. by split. }
             apply NISSB. eapply rfrmw_I_in_I; eauto. exists b.
             apply seqA. apply seq_eqv_r. by split. }
           desc.
           assert (loc lab p = Some l) as PLOC.
           { rewrite <- LOC0. by apply (wf_rfrmwl WF). }
           assert (p <> w) as PNEQ by (by intros HH; subst).
           assert (S p) by (eapply rcoh_I_in_S; eauto).
           exists p. splits; auto.
           { clear -CC. find_event_set. }
           eexists. splits; eauto.
           rewrite updo; [|by intros HH; subst].
           apply NOTNEWM; auto.
           all: destruct (classic (l = locw)) as [|LNEQ]; subst; auto.
           all: right; intros HH.
           { eapply f_to_eq with (I:=S) in HH; eauto; subst; auto.
             red. by rewrite LOC. }
           rewrite <- REQ_TO with (e:=p) in HH; auto.
           eapply f_to_eq in HH; (try by apply FCOH0); eauto.
           { clear -SEW'. simplify_tls_events. rewrite <- SEW'. subst S'. basic_solver. } 
           { red. by rewrite LOC. }
           all: clear -H SW; find_event_set. }
      destruct (Rel w) eqn:RELW; auto.
      assert (wmod (mod lab w) = Ordering.acqrel) as MM.
      { clear -RELW. mode_solver. }
      rewrite MM.
      unfold TView.rel, TView.write_tview. 
      arewrite (Ordering.le Ordering.acqrel Ordering.acqrel = true) by reflexivity.
      destruct (classic (l = locw)) as [|LNEQ]; subst.
      2: { unfold LocFun.add. rewrite Loc.eq_dec_neq; auto. }
      exfalso.
      assert (E b) as EB by (eapply issuedE; eauto).
      assert (W b) as WB by (eapply issuedW; eauto).
      assert ((⦗E⦘ ⨾ same_tid ⨾ ⦗E⦘) w b) as ST.
      { apply seq_eqv_lr. by splits. }
      apply tid_sb in ST. destruct ST as [[[|ST]|ST]|[AI BI]]; subst; auto.
      2: { apply NCOVBB. eapply fwbob_issuable_in_C; eauto.
           exists w. apply seq_eqv_r. split; eauto. 
           apply sb_to_w_rel_in_fwbob. apply seq_eqv_r. split; auto. by split. }
      apply NCOVB. eapply fwbob_I_in_C; eauto.
      exists b. apply seq_eqv_r. split; eauto. 
      apply sb_from_w_rel_in_fwbob. apply seq_eqv_l. splits; eauto.
      { by split. }
      apply seq_eqv_r. split; auto. split; auto. vauto. 
      red. by rewrite LOC. }
    assert (Some l = Some locw) as QQ.
    { by rewrite <- LOC0. }
    inv QQ.
    eexists. splits; eauto.
    { erewrite Memory.add_o; eauto. rewrite loc_ts_eq_dec_eq; eauto. }
    { apply HELPER. }
    { apply RELWFEQ. }
    { apply RELMCLOS. }
    intros _ NT.
    destruct (Rel b); desf.
    { exfalso. apply NT. clear. find_event_set. }
    splits.
    { erewrite Memory.add_o; eauto. rewrite loc_ts_eq_dec_eq; eauto. }
    exists p_rel. splits; eauto. right.
    cdes PREL. destruct PREL1; desc.
    { exfalso. eauto. }
    assert (S p) as SP.
    { eapply rcoh_I_in_S; eauto. }
    exists p. splits; eauto.
    { clear -ISSP. find_event_set. }
    eexists. splits; eauto.
    eapply memory_add_le; eauto.
    rewrite REQ_TO; [|by intros HH; subst].
    erewrite Memory.remove_o; eauto.
    destruct (classic (f_to p = f_to b)) as [EQ|NEQ].
    2: { rewrite loc_ts_eq_dec_neq; auto. }
    exfalso. eapply f_to_eq with (I:=S) in EQ; eauto; subst.
    2: by apply (wf_rfrmwl WF).
    eapply wf_rfrmw_irr; eauto. }
  { red. ins.
    assert (b <> w /\ ~ issued T b) as [BNEQ NISSBB].
    { contra BB. destruct NISSB0. apply not_and_or in BB.
      clear -BB. destruct BB as [?%NNPP | ?%NNPP]; find_event_set. }
    apply RES' in RESB.
    destruct RESB as [[SB|]|HH]; subst.
    3: { exfalso. eapply NONEXT; eauto. }
    2: by desf.
    unnw.
    erewrite Memory.add_o with (mem2:=memory_add); eauto.
    erewrite Memory.remove_o with (mem2:=memory_cancel); eauto.
    destruct (loc_ts_eq_dec (l, f_to b) (locw, f_to w)) as [PEQ'|PNEQ];
      simpls; desc; subst.
    { exfalso. apply BNEQ.
      eapply f_to_eq with (I:=S); eauto. red. by rewrite LOC. }
    destruct (loc_ts_eq_dec (l, f_to b) (locw, f_to' w)) as [PEQ'|PNEQ'];
      simpls; desc; subst.
    { exfalso. apply BNEQ.
      rewrite <- REQ_TO in PEQ'0; auto.
      eapply f_to_eq; (try by apply FCOH0); eauto.
      { clear -SEW'. simplify_tls_events. rewrite <- SEW'. subst S'. basic_solver. }
      { red. by rewrite LOC. }
      all: clear -SB SW; find_event_set. }
    edestruct SIM_RES_MEM with (b:=b); eauto; unnw.
    rewrite REQ_TO; auto.
    rewrite !(loc_ts_eq_dec_neq PNEQ'); auto.
    rewrite !(loc_ts_eq_dec_neq PNEQ); auto.
    splits; ins.
    apply NOTNEWP; auto. }
  intros WREL. red. ins. destruct msg; auto.
  exfalso. eapply SIM_PROM in GET. desc; subst.
  assert (E b) as EB.
  { eapply issuedE; eauto. }
  assert (W b) as WB.
  { eapply issuedW; eauto. }
  assert ((⦗E⦘ ⨾ same_tid ⨾ ⦗E⦘) b w) as HH.
  { apply seq_eqv_lr. splits; auto. }
  apply tid_sb in HH. destruct HH as [[[HH|HH]|HH]|[AA BB]]; subst; auto.
  2: { apply NCOVB. eapply dom_W_Rel_sb_loc_I_in_C; eauto.
       exists b. apply seq_eqv_l. split; [by split|].
       apply seqA.
       do 2 (apply seq_eqv_r; split; auto).
       split; auto. red. rewrite LOC. auto. }
  apply NCOV. eapply fwbob_issuable_in_C; eauto.
  exists w. apply seq_eqv_r. split; eauto. 
  apply sb_to_w_rel_in_fwbob. apply seq_eqv_r. 
  do 2 (split; auto).
Qed.

Lemma issue_reserved_step_helper_with_next r w valw locw ordw langst wnext
      (TID : IdentMap.find (tid w) (Configuration.threads PC) = Some (langst, local))
      (RMW : rmw r w) (SW : S w)
      (NISSB : ~ issued T w)
      (ISSUABLE : issuable G sc T w)
      (WNEXT : dom_sb_S_rfrmw G T rfi (eq w) wnext)
      (LOC : loc lab w = Some locw)
      (VAL : val lab w = Some valw)
      (ORD : mod lab w = ordw)
      (WTID : thread = tid w) :
  let promises := (Local.promises local) in
  let memory   := (Configuration.memory PC) in
  let sc_view  := (Configuration.sc PC) in
  (* let covered' := if Rel w then covered T ∪₁ eq w else covered T in *)
  (* let T'       := mkTC covered' (issued T ∪₁ eq w) in *)
  (* let S'       := S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G (mkETC T S) rfi (eq w) in *)
  let T' := T ∪₁ (if Rel w then eq (mkTL ta_cover w) else ∅) ∪₁ eq (mkTL ta_issue w) ∪₁ (eq ta_reserve <*> (eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w))) in
  let n_to     := Time.middle (f_from w) (f_to w) in
  let f_to'    := upd (upd f_to w n_to) wnext (f_to w) in
  let f_from'  := upd f_from wnext n_to in

  ⟪ REQ_TO : forall e (SE : S e) (NEQ : e <> w), f_to' e = f_to e ⟫ /\
  ⟪ REQ_FROM : forall e  (SE : S e) (NEQ : e <> w), f_from' e = f_from e ⟫ /\
  ⟪ ISSEQ_TO : forall e (ISS: issued T e), f_to' e = f_to e ⟫ /\
  ⟪ ISSEQ_FROM : forall e (ISS: issued T e), f_from' e = f_from e ⟫ /\

  exists p_rel, rfrmw_prev_rel G sc T f_to f_from (Configuration.memory PC) w locw p_rel /\
    let rel'' :=
        if is_rel lab w
        then (TView.cur (Local.tview local))
        else (TView.rel (Local.tview local) locw)
    in
    let rel' := (View.join (View.join rel'' (View.unwrap p_rel))
                           (View.singleton_ur locw (f_to' w))) in

    ⟪ REL_VIEW_LT : Time.lt (View.rlx rel'' locw) (f_to' w) ⟫ /\
    ⟪ REL_VIEW_LE : Time.le (View.rlx rel' locw) (f_to' w) ⟫ /\

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

      ⟪ FCOH : f_to_coherent G (reserved T') f_to' f_from' ⟫ /\

      ⟪ HELPER :
          sim_mem_helper
            G sc f_to' w (f_from' w) valw
            (View.join (View.join (if is_rel lab w
                                   then (TView.cur (Local.tview local))
                                   else (TView.rel (Local.tview local) locw))
                                  (View.unwrap p_rel))
                       (View.singleton_ur locw (f_to' w))) ⟫ /\

      ⟪ RESERVED_TIME :
          reserved_time G T' f_to' f_from' smode memory_split ⟫ /\

      exists promises',
        ⟪ PEQ :
            if Rel w
            then Memory.remove promises_split locw (f_from' w) (f_to' w)
                               (Message.full valw (Some rel')) promises'
            else promises' = promises_split ⟫ /\

        ⟪ NEW_PROM_IN_MEM : Memory.le promises' memory_split ⟫ /\

        let tview' := if is_rel lab w
                      then TView.write_tview
                             (Local.tview local) sc_view locw
                             (f_to' w) (Event_imm_promise.wmod ordw)
                      else (Local.tview local) in
        let local' := Local.Local.mk tview' promises' in
        let threads' :=
            IdentMap.add (tid w)
                         (langst, local')
                         (Configuration.threads PC) in

        ⟪ THREAD : forall t (IN : (threads_set G \₁ eq tid_init) t), IdentMap.In t threads' ⟫ /\

        ⟪ SC_REQ : smode = sim_normal -> 
                   forall (l : Loc.t),
                     max_value f_to' (S_tm G l (covered T)) (LocFun.find l sc_view) ⟫ /\
        ⟪ CLOSED_SC : Memory.closed_timemap sc_view memory_split ⟫ /\

        ⟪ MEM_SPLIT :
            Memory.promise (Local.promises local) memory locw (f_from' w) (f_to' w)
                           (Message.full valw (Some rel'))
                           promises_split memory_split
                           (Memory.op_kind_split (f_to' wnext) Message.reserve) ⟫ /\

        ⟪ PROM_IN_MEM :
            forall thread' langst local
                   (TID : IdentMap.find thread' threads' = Some (langst, local)),
              Memory.le (Local.promises local) memory_split ⟫ /\

        ⟪ SIM_PROM     : sim_prom G sc T' f_to' f_from' (tid w) promises'  ⟫ /\
        ⟪ SIM_RES_PROM : sim_res_prom G T' f_to' f_from' (tid w) promises'  ⟫ /\

        ⟪ PROM_DISJOINT :
            forall thread' langst' local'
                   (TNEQ : tid w <> thread')
                   (TID' : IdentMap.find thread' threads' =
                           Some (langst', local')),
            forall loc to,
              Memory.get loc to promises' = None \/
              Memory.get loc to local'.(Local.promises) = None ⟫ /\

        ⟪ SIM_MEM     : sim_mem G sc T' f_to' f_from' (tid w) local' memory_split ⟫ /\
        ⟪ SIM_RES_MEM : sim_res_mem G T' f_to' f_from' (tid w) local' memory_split ⟫ /\
        ⟪ SIM_TVIEW   : sim_tview G sc (covered T') f_to' local'.(Local.tview) (tid w) ⟫ /\
        ⟪ NOWLOC : Rel w -> Memory.nonsynch_loc locw (Local.promises local) ⟫.
Proof using All.
  assert (sc_per_loc G) as SPL.
  { apply coherence_sc_per_loc. apply IMMCON. }
  assert (complete G) as COMPL by apply IMMCON.

  subst.
  edestruct exists_time_interval_for_issue_reserved_with_next as [p_rel [PREL HH]]; eauto.
  simpls; desc.
  
  assert (S ⊆₁ E ∩₁ W) as SEW.
  { apply set_subset_inter_r. split; [by apply RCOH|].
    eapply reservedW; eauto. }
  assert (E w /\ W w) as [EW WW] by (by apply SEW).
  assert (~ covered T w) as NCOVB.
  { intros AA. apply NISSB. eapply w_covered_issued; eauto. by split. }

  assert (W_ex w) as WEW.
  { apply RCOH. by split. }
  assert (codom_rel (⦗issued T⦘ ⨾ rf ⨾ rmw) w) as CDRFRMW.
  { eapply W_ex_in_codom_rfrmw in WEW; eauto.
    destruct WEW as [u WEW].
    exists u. apply seq_eqv_l. split; auto.
    eapply ExtTraversalProperties.dom_rf_rmw_S_in_I; eauto.
    exists w. apply seqA. apply seq_eqv_r. split; auto. }
  
  assert (tid r = tid w) as TIDRW by (by apply (wf_rmwt WF)).

  assert (Memory.le promises_split memory_split) as PP.
  { eapply memory_le_split2; eauto. }

  set (n_to     := Time.middle (f_from w) (f_to w)).
  set (f_to'    := upd (upd f_to w n_to) wnext (f_to w)).
  set (f_from'  := upd f_from wnext n_to).
  set (rel'' :=
        if is_rel lab w
        then (TView.cur (Local.tview local))
        else (TView.rel (Local.tview local) locw)).
  set (rel' := (View.join (View.join rel'' (View.unwrap p_rel))
                          (View.singleton_ur locw (f_to' w)))).

  assert (exists promises',
             ⟪ PEQ : if Rel w
                     then
                       Memory.remove promises_split locw
                                     (f_from' w) (f_to' w)
                                     (Message.full valw (Some rel'))
                                     promises'
                     else promises' = promises_split ⟫).
  { destruct (is_rel lab w) eqn:REL; eauto.
    unnw. apply Memory.remove_exists. erewrite Memory.split_o; eauto.
      by rewrite loc_ts_eq_dec_eq. }
  desc.

  assert (Memory.le promises' memory_split) as PPC.
  { etransitivity; [|by apply PP].
    destruct (Rel w); subst.
    2: by apply Memory.le_PreOrder.
    eapply memory_remove_le; eauto. }

  assert (Memory.get locw (f_to w) (Local.promises local) =
          Some (f_from w, Message.reserve)) as INPROM.
  { eapply SIM_RES_MEM; eauto. }
  assert (Memory.get locw (f_to w) (Configuration.memory PC) =
          Some (f_from w, Message.reserve)) as INMEM.
  { eapply PROM_IN_MEM in INPROM; eauto. }

  assert (forall thread' langst' local' (TNEQ : tid w <> thread')
                 (TID' : IdentMap.find thread' (Configuration.threads PC) =
                         Some (langst', local')),
             Memory.get locw (f_to w) (Local.promises local') = None) as NINTER.
  { ins. eapply PROM_DISJOINT with (loc:=locw) (to:=f_to w) in TID'; eauto. desf. }

  assert (forall tmap (MCLOS : Memory.closed_timemap tmap (Configuration.memory PC)),
             Memory.closed_timemap tmap memory_split) as MSPLITCLOS.
  { ins. eapply Memory.split_closed_timemap; eauto. }
  desc.

  assert (~ covered T w) as WNCOV.
  { intros HH. apply NISSB.
    eapply w_covered_issued; vauto. }
  assert (~ is_init w) as WNINIT.
  { intros HH. apply WNCOV. eapply init_covered; vauto. }

  assert ((rf ⨾ rmw) w wnext) as RFRMWNEXT.
  { destruct WNEXT as [_ BB]. generalize BB. unfold Execution.rfi.
    clear. basic_solver. }
  assert (w <> wnext) as NEQNEXT.
  { intros HH; subst. eapply wf_rfrmw_irr; eauto. }
  assert (co w wnext) as COWNEXT.
  { apply rf_rmw_in_co; auto. }
  assert (~ is_init wnext) as NINITNEXT.
  { apply no_co_to_init in COWNEXT; auto. by destruct_seq_r COWNEXT as AA. }
  assert (E wnext) as EWNEXT.
  { apply (wf_coE WF) in COWNEXT. by destruct_seq COWNEXT as [AA BB]. }
  assert (W wnext) as WWNEXT.
  { apply (wf_coD WF) in COWNEXT. by destruct_seq COWNEXT as [AA BB]. }
  assert (~ S wnext) as NSNEXT.
  { intros HH. apply NISSB. eapply dom_rf_rmw_S_in_I; eauto.
    exists wnext. apply seqA. apply seq_eqv_r. by split. }
  assert (~ issued T wnext) as NINEXT.
  { intros HH. apply NSNEXT. eapply rcoh_I_in_S; eauto. }
  assert (loc lab wnext = Some locw) as NLOC.
  { rewrite <- LOC. symmetry. by apply wf_rfrmwl. }

  assert (forall l to omsg 
                 (NEQ  : l <> locw \/ to <> f_to' w)
                 (NEQ' : l <> locw \/ to <> f_to' wnext),
             Memory.get l to memory_split = omsg <->
             Memory.get l to (Configuration.memory PC) = omsg)
    as NOTNEWM.
  { ins. erewrite Memory.split_o; eauto.
    by repeat (rewrite loc_ts_eq_dec_neq; auto). }

  assert (REQ_TO : forall e (SE : S e) (NEQ : e <> w), f_to' e = f_to e).
  { ins. unfold f_to'. by repeat (rewrite updo; [|by intros HH; desf]). }
  assert (REQ_FROM : forall e  (SE : S e) (NEQ : e <> w), f_from' e = f_from e).
  { ins. unfold f_from'. by rewrite updo; [|by intros HH; desf]. }

  assert (ISSEQ_TO : forall e (ISS: issued T e), f_to' e = f_to e).
  { ins. apply REQ_TO; [|intros HH; desf]. eapply rcoh_I_in_S; eauto. }
  assert (ISSEQ_FROM : forall e (ISS: issued T e), f_from' e = f_from e).
  { ins. apply REQ_FROM; [|intros HH; desf]. eapply rcoh_I_in_S; eauto. }

  assert (forall l to omsg 
                 (NEQ  : l <> locw \/ to <> f_to' w)
                 (NEQ' : l <> locw \/ to <> f_to' wnext),
             Memory.get l to promises_split = omsg <->
             Memory.get l to (Local.promises local) = omsg)
    as NOTNEWA.
  { ins. erewrite Memory.split_o; eauto.
    by repeat (rewrite loc_ts_eq_dec_neq; auto). }

  assert (forall l to omsg 
                 (NEQ : l <> locw \/ to <> f_to' w)
                 (NEQ' : l <> locw \/ to <> f_to' wnext),
             Memory.get l to promises' = omsg <->
             Memory.get l to (Local.promises local) = omsg)
    as NOTNEWP.
  { ins. destruct (Rel w); subst; auto.
    erewrite Memory.remove_o; eauto. rewrite (loc_ts_eq_dec_neq NEQ); auto. }

  assert (f_to' wnext = f_to w) as FTOWNEXT.
  { unfold f_to'. by rewrite upds. }

  assert (dom_sb_S_rfrmw G T rfi (eq w) ≡₁ eq wnext) as DOMSBEQ.
  { eapply dom_sb_S_rfrmw_single; eauto. }

  assert (S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w) ⊆₁ E ∩₁ W) as SDEW.
  { rewrite DOMSBEQ. rewrite SEW. generalize EW WW EWNEXT WWNEXT.
    clear. basic_solver. }

  assert (tid wnext = tid w) as TIDEQNEXT.
  { eapply dom_sb_S_rfrmw_same_tid; eauto. }

  assert (Time.lt (f_from w) (f_to w)) as FTFW by (by apply FCOH).
  splits; eauto.

  exists p_rel. splits; eauto.
  do 2 eexists. splits; eauto.
  { eapply f_to_coherent_more; [..| apply FCOH0]; eauto.
    clear. simplify_tls_events. basic_solver. }
  { eapply reserved_time_same_issued_reserved; [apply RESERVED_TIME0| ..]. 
    all: clear; simplify_tls_events; basic_solver. }
  eexists. splits; eauto.
  { intros e' EE. 
    apply IdentMap.Facts.add_in_iff.
    destruct (Ident.eq_dec e' (tid w)) as [|NEQ]; subst; auto. }
  { ins. apply max_value_new_f with (f:=f_to); auto.
    ins. apply ISSEQ_TO. eapply S_tm_covered; eauto. }
  { ins.
    destruct (Ident.eq_dec thread' (tid w)) as [EQ|NEQ].
    { subst. rewrite IdentMap.gss in TID0.
      inv TID0; simpls; clear TID0. }
    red; ins; rewrite IdentMap.gso in TID0; auto.
    assert (Memory.get loc to (Configuration.memory PC) = Some (from, msg)) as INMEMM.
    { eapply PROM_IN_MEM; eauto. }
    destruct (classic (loc = locw)) as [|LNEQ]; subst.
    2: by apply NOTNEWM; auto.
    apply NOTNEWM; auto; right; unfold f_to', n_to;
      [rewrite updo; auto|]; rewrite upds.
    all: intros HH; subst.
    2: { edestruct PROM_DISJOINT as [HH|HH].
         { intros HH. apply NEQ. by rewrite HH. }
         { eauto. }
         { rewrite INPROM in HH. inv HH. }
         rewrite HH in LHS. inv LHS. }
    eapply Memory.get_disjoint in INMEMM; [|by apply INMEM].
    destruct INMEMM as [AA|AA]; desc.
    { eapply Time.lt_strorder with (x:=f_to w).
      rewrite AA at 1. by apply DenseOrder.middle_spec. }
    eapply AA with (x:=Time.middle (f_from w) (f_to w)).
    2: { apply Interval.mem_ub.
         eapply Memory.get_ts in LHS. destruct LHS as [BB|BB]; desc; subst; auto.
         eapply TimeFacts.le_lt_lt with (b:=f_from w).
         { apply DenseOrder.bot_spec. }
           by apply Time.middle_spec. }
    constructor; simpls; [|apply Time.le_lteq; left].
    all: by apply Time.middle_spec. }
  { simpls. red. ins.
    destruct (loc_ts_eq_dec (l, to) (locw, f_to' w)) as [[A' B']|LL].
    { simpls; rewrite A' in *; rewrite B' in *.
      destruct (Rel w) eqn:RELB; subst.
      { erewrite Memory.remove_o in PROM; eauto.
        rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in PROM. inv PROM. }
      erewrite Memory.split_o in PROM; eauto.
      rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in PROM.
      inv PROM. exists w. splits; eauto. 
      { clear. find_event_set. }
      clear -NCOVB. separate_set_event. }
    destruct (loc_ts_eq_dec (l, to) (locw, f_to' wnext)) as [[A' B']|LL'].
    { simpls; rewrite A' in *; rewrite B' in *; subst.
      destruct (Rel w) eqn:RELB; subst.
      erewrite Memory.remove_o in PROM; eauto.
      rewrite (loc_ts_eq_dec_neq LL) in PROM.
      all: erewrite Memory.split_o in PROM; eauto.
      all: rewrite (loc_ts_eq_dec_neq LL) in PROM.
      all: rewrite (loc_ts_eq_dec_eq locw (f_to' wnext)) in PROM.
      all: inv PROM. }
    apply NOTNEWP in PROM; auto.
    edestruct SIM_PROM as [b H]; eauto; desc.
    exists b; splits; auto.
    { clear -ISS. find_event_set. }
    { assert (W b) as WB by (eapply issuedW; eauto).
      destruct (Rel w) eqn:RELB; auto.
      all: clear -NISSB ISS NCOV; separate_set_event. }
    { by rewrite ISSEQ_FROM; auto. }
    { by rewrite ISSEQ_TO; auto. }
    eapply sim_mem_helper_f_issued; eauto. }
  { simpls. red. ins.
    destruct (loc_ts_eq_dec (l, to) (locw, f_to' w)) as [[A' B']|LL].
    { simpls; rewrite A' in *; rewrite B' in *.
      destruct (Rel w) eqn:RELB; subst.
      { erewrite Memory.remove_o in RES; eauto.
        rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in RES. inv RES. }
      erewrite Memory.split_o in RES; eauto.
      rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in RES. inv RES. }
    destruct (loc_ts_eq_dec (l, to) (locw, f_to' wnext)) as [[A' B']|LL'].
    { simpls; rewrite A' in *; rewrite B' in *.
      exists wnext. splits; eauto.
      { clear -DOMSBEQ.
        eapply set_equiv_exp; [simplify_tls_events; reflexivity| ].
        repeat right. by apply DOMSBEQ. } 
      { clear -NINEXT NEQNEXT. separate_set_event. }
      destruct (Rel w) eqn:RELB; subst.
      erewrite Memory.remove_o in RES; eauto.
      rewrite (loc_ts_eq_dec_neq LL) in RES.
      all: erewrite Memory.split_o in RES; eauto.
      all: rewrite (loc_ts_eq_dec_eq locw (f_to' wnext)) in RES.
      all: rewrite (loc_ts_eq_dec_neq LL) in RES.
      all: inv RES; rewrite updo; auto; rewrite upds.
      all: unfold f_from'; rewrite upds; auto. }
    apply NOTNEWP in RES; auto.
    edestruct SIM_RES_PROM as [b H]; eauto; desc.
    simpls.
    assert (b <> w) as NEQ.
    { intros A; subst. rewrite LOC in LOC0. inv LOC0.
      rewrite FTOWNEXT in LL'. clear -LL'. desf. }
    assert (b <> wnext) as NEQ'.
    { intros A; desf. }
    exists b. splits; auto.
    { clear -RES0. find_event_set. }
    { clear -NOISS NEQ. separate_set_event. }
    { unfold f_from'. rewrite updo; auto. }
    unfold f_to'. repeat (rewrite updo; auto). }
  { ins.
    rewrite IdentMap.gso in TID'; auto.
    destruct (loc_ts_eq_dec (loc, to) (locw, (f_to' w))) as [EQ|NEQ]; simpls.
    { desc. subst. right.
      destruct (Memory.get locw (f_to' w) (Local.Local.promises local')) eqn: HH; auto.
      exfalso.
      destruct p as [from msg].
      eapply PROM_IN_MEM in HH; eauto.
      edestruct Memory.split_get0 as [Y1 Y2].
      { apply MSPLIT. }
      red in Y1. unfold f_to', n_to in HH. rewrite Y1 in HH.
      inv HH. }
    destruct (loc_ts_eq_dec (loc, to) (locw, (f_to' wnext))) as [EQ|NEQ2]; simpls.
    { desc. subst. right. rewrite FTOWNEXT.
      edestruct (PROM_DISJOINT TNEQ TID') as [HH|HH]; eauto. }
    rewrite NOTNEWP; auto. eapply PROM_DISJOINT; eauto. }
  { red. ins.
    assert (issued
              (T ∪₁ (if Rel w then eq (mkTL ta_cover w) else ∅)
                 ∪₁ eq (mkTL ta_issue w)
                 ∪₁ eq ta_reserve <*> (eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w))) ≡₁
              I ∪₁ eq w) as ISS'.
    { clear. simplify_tls_events. basic_solver. }
    (* assert (f_to_coherent G (S ∪₁ eq b ∪₁ dom_sb_S_rfrmw G T rfi (eq b)) f_to' *)
    (*                       (upd f_from wnext (Time.middle (f_from b) (f_to b)))) as FCOH'.  *)
    (* { eapply f_to_coherent_more; [..| apply FCOH0]; auto. *)
    (*   clear -DOMSBEQ. simplify_tls_events. rewrite DOMSBEQ. basic_solver. } *)

    destruct (loc_ts_eq_dec (l, f_to' b) (locw, (f_to' wnext))) as [EQ|NEQ]; simpls; desc; subst.
    { assert (b = wnext); subst.
      2: { exfalso. generalize ISSB.
           clear -NINEXT NEQNEXT. separate_set_event. }
      eapply f_to_eq
        with (f_to:=f_to')
             (I:=S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w)); eauto.
      { eapply f_to_coherent_more; [.. | apply FCOH0]; eauto.
        clear. simplify_tls_events. basic_solver. }
      { red. by rewrite NLOC. }
      { do 2 left. apply ISS' in ISSB. destruct ISSB; subst; auto. eapply rcoh_I_in_S; eauto. }
        by right. }
    apply ISS' in ISSB. destruct ISSB as [ISSB|]; subst.
    2: { assert (Some l = Some locw) as QQ.
         { by rewrite <- LOC0. }
         inv QQ.
         eexists. splits; eauto.
         { erewrite Memory.split_o; eauto. rewrite loc_ts_eq_dec_eq; eauto. }
         { apply HELPER. }
         { apply RELWFEQ. }
         { apply RELMCLOS. }
         intros _ NT.
         destruct (Rel b); desf.
         { exfalso. apply NT. clear -SW. find_event_set. }
         erewrite Memory.split_o; eauto. rewrite loc_ts_eq_dec_eq; eauto.
         splits; vauto.
         exists p_rel. splits; eauto. right.
         cdes PREL. destruct PREL1; desc.
         { exfalso. eauto. }
         assert (S p) as SP.
         { eapply rcoh_I_in_S; eauto. }
         exists p. splits; eauto.
         { clear -ISSP. find_event_set. }
         eexists. splits; eauto.
         apply NOTNEWM; auto.
         3: { rewrite ISSEQ_TO; auto. rewrite ISSEQ_FROM; auto. }
         all: right; intros HH.
         all: eapply f_to_eq with 
             (I:=S ∪₁ eq b ∪₁ dom_sb_S_rfrmw G T rfi (eq b)) in HH; eauto.
         all: try by subst.
         all: try (generalize SP WNEXT; clear; basic_solver).
         { eapply f_to_coherent_more; [..| apply FCOH0]; auto.
           clear -DOMSBEQ. simplify_tls_events. rewrite DOMSBEQ. basic_solver. }
         { red. by rewrite LOC0. }
         { eapply f_to_coherent_more; [..| apply FCOH0]; auto.
           clear -DOMSBEQ. simplify_tls_events. rewrite DOMSBEQ. basic_solver. }
         red. by rewrite NLOC. }
    edestruct SIM_MEM as [rel_opt HH]; eauto. simpls. desc.
    exists rel_opt. unnw.
    destruct (loc_ts_eq_dec (l, f_to' b) (locw, (f_to' w))) as [EQ|NEQ']; simpls; desc; subst.
    { exfalso.
      assert (b = w); [|by desf].
      eapply f_to_eq with 
          (I:=S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w)); eauto.
      { eapply f_to_coherent_more; [..| apply FCOH0]; auto.
        clear -DOMSBEQ. simplify_tls_events. rewrite DOMSBEQ. basic_solver. }
      { red. by rewrite LOC. }
      { do 2 left. eapply rcoh_I_in_S; eauto. }
      clear. basic_solver. }
    split.
    { apply NOTNEWM; auto.
      rewrite ISSEQ_FROM; auto. rewrite ISSEQ_TO; auto. }
    rewrite ISSEQ_TO with (e:=b); auto. 
    rewrite ISSEQ_FROM with (e:=b); auto. 
    splits; auto.
    { eapply sim_mem_helper_f_issued; eauto. }
    intros TIDEQ NCOV.
    destruct HH1 as [AA BB]; auto.
    { intros CB. destruct NCOV. clear -CB. find_event_set. }
    splits.
    { apply NOTNEWP; auto.
      all: rewrite <- ISSEQ_TO with (e:=b); auto. }
    desc.
    eexists. splits; eauto.
    2: { destruct BB0 as [[CC DD]|CC]; [left|right].
         { split; eauto. intros [y HH]. destruct_seq_l HH as OO.
           apply ISS' in OO. 
           destruct OO as [OO|]; subst.
           { apply CC. exists y. apply seq_eqv_l. by split. }
           apply NISSB. eapply rfrmw_I_in_I; eauto. exists b.
           apply seqA. apply seq_eqv_r. by split. }
         desc. exists p. splits; auto.
         { clear -CC. find_event_set. }
         eexists. splits; eauto.
         destruct (classic (l = locw)) as [|LNEQ]; subst; auto.
         2: { apply NOTNEWM; auto. rewrite ISSEQ_TO; auto. rewrite ISSEQ_FROM; auto. }
         assert (loc lab p = Some locw) as PLOC.
         { rewrite <- LOC0. by apply (wf_rfrmwl WF). }
         assert (S p) as SP by (eapply rcoh_I_in_S; eauto).
         apply NOTNEWM.
         3: { rewrite ISSEQ_TO; auto. rewrite ISSEQ_FROM; auto. }
         all: right; intros HH; eapply f_to_eq in HH; eauto; subst; auto.
         all: try by red; rewrite PLOC.
         1, 4: eapply f_to_coherent_more; [..| apply FCOH0]; auto;
         clear -DOMSBEQ; simplify_tls_events; rewrite DOMSBEQ; basic_solver.
         all: generalize SP, WNEXT; clear; basic_solver. }
    destruct (Rel w) eqn:RELW; auto.
    assert (wmod (mod lab w) = Ordering.acqrel) as MM.
    { clear -RELW. mode_solver. }
    rewrite MM.
    unfold TView.rel, TView.write_tview. 
    arewrite (Ordering.le Ordering.acqrel Ordering.acqrel = true) by reflexivity.
    destruct (classic (l = locw)) as [|LNEQ]; subst.
    2: { unfold LocFun.add. rewrite Loc.eq_dec_neq; auto. }
    exfalso.
    assert (E b) as EB by (eapply issuedE; eauto).
    assert (W b) as WB by (eapply issuedW; eauto).
    assert ((⦗E⦘ ⨾ same_tid ⨾ ⦗E⦘) w b) as ST.
    { apply seq_eqv_lr. by splits. }
    apply tid_sb in ST. destruct ST as [[[|ST]|ST]|[AI BI]]; subst; auto.
    { assert (issuable G sc T b) as IB by (eapply issued_in_issuable; eauto).
      apply NCOVB. eapply fwbob_I_in_C; eauto.
      exists b. apply seq_eqv_r. split; eauto. 
      apply sb_from_w_rel_in_fwbob. apply seq_eqv_l. splits; eauto.
      { by split. }
      apply seq_eqv_r. split; auto. split; auto. vauto.
      red. by rewrite LOC. }    
    apply NCOV. enough (C b).
    { clear -H. find_event_set. }
    eapply fwbob_issuable_in_C; eauto.
    exists w. apply seq_eqv_r. splits; eauto.
    apply sb_to_w_rel_in_fwbob. apply seq_eqv_r. split; auto. by split. }
  2: { desf.
       (* 2: by eapply sim_tview_f_issued with (f_to:=f_to); eauto. *)
       2: {
         (* eapply sim_tview_more; [.. | apply SIM_TVIEW]; eauto.  *)
         eapply sim_tview_more.
         3: { clear. simplify_tls_events. reflexivity. }
         1-5: reflexivity. 
         eapply sim_tview_f_issued with (T := T) (f_to:=f_to); eauto. } 
       cdes IMMCON.
       destruct (lab w) eqn:LL.
       1,3: clear -LL WW; type_solver.
       
       eapply sim_tview_more.
       3: { clear. simplify_tls_events. reflexivity. }
       1-5: reflexivity. 
       
       eapply sim_tview_write_step
         with (C:=covered T) (w:=w) (f_from:=f_from')
              (valw:=valw) (rel:=Some rel') (mem:=memory_split); eauto.
       7: by erewrite Memory.split_o; eauto; rewrite loc_ts_eq_dec_eq. 
       3: { eapply sim_tview_f_issued; eauto. }
       { eapply coveredE; eauto. }
       { red. ins. eapply dom_sb_covered; eauto.
         eexists; eauto. }
       { intros y [COVY TIDY].
         assert (E y) as EY.
         { eapply coveredE; eauto. }
         apply tid_ext_sb in TIDY. destruct TIDY as [[[AA|AA]|]|[_ AA]]; subst.
         4: { clear -AA WNINIT. desf. }
         { clear -NCOVB COVY; desf. }
         { red. apply seq_eqv_lr. splits; auto. }
         exfalso. apply NCOVB. eapply dom_sb_covered; eauto.
         exists y. apply seq_eqv_r. split; eauto.
         apply seq_eqv_lr. splits; auto. }
       { apply doma_alt.
         intros e [w' [SB <-]%seq_eqv_r]. 
         eapply fwbob_issuable_in_C; eauto.
         eexists. apply seq_eqv_r. split; eauto.
         apply sb_to_w_rel_in_fwbob. apply seq_eqv_r. do 2 (split; auto). }
       unfold mod. rewrite LL.
       assert (locw = l); subst.
       { clear -LOC LL. unfold loc in LOC. rewrite LL in LOC. inv LOC. }
       assert (valw = v); subst.
       { clear -VAL LL. unfold val in VAL. rewrite LL in VAL. inv VAL. }
       eauto. }
  { red. ins.
    assert (b <> w /\ ~ issued T b) as [BNEQ NISSBB].
    { contra BB. destruct NISSB0. apply not_and_or in BB.
      clear -BB. destruct BB as [?%NNPP | ?%NNPP]; find_event_set. }
    assert (f_to' wnext <> f_to' w) as FTOWNEXTNEQ.
    { intros HH. 
      eapply f_to_eq with 
          (I:=S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w)) in HH; eauto.
      { eapply f_to_coherent_more; [..| apply FCOH0]; auto.
        clear -DOMSBEQ. simplify_tls_events. rewrite DOMSBEQ. basic_solver. }
      { red. by rewrite LOC. }
      all: generalize WNEXT; clear; basic_solver. }
    assert (reserved
               (T ∪₁ (if Rel w then eq (mkTL ta_cover w) else ∅)
            ∪₁ eq (mkTL ta_issue w)
            ∪₁ eq ta_reserve <*> (eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w))) ≡₁
            S ∪₁ eq w ∪₁ eq wnext) as RES'.
    { clear -DOMSBEQ. simplify_tls_events. rewrite DOMSBEQ. basic_solver. }

    apply RES' in RESB. 
    destruct RESB as [[SB|]|HH]; subst.
    3: {
      (* assert (b = wnext); subst. *)
      (*    { eapply dom_sb_S_rfrmwf; eauto. } *)
         rewrite NLOC in LOC0. inv LOC0.
         splits.
         { erewrite Memory.split_o; eauto.
           rewrite loc_ts_eq_dec_neq.
           2: by right.
           rewrite loc_ts_eq_dec_eq.
           rewrite updo; auto. by unfold f_from', n_to; rewrite !upds. }
         intros _.
         destruct (Rel w); simpls; subst.
         erewrite Memory.remove_o; eauto.
         rewrite loc_ts_eq_dec_neq; [|by right].
         all: erewrite Memory.split_o; eauto.
         all: rewrite loc_ts_eq_dec_neq; [|by right].
         all: rewrite loc_ts_eq_dec_eq.
         all: by rewrite updo; auto; unfold f_from', n_to; rewrite !upds. }
    2: by desf.
    unnw.
    edestruct SIM_RES_MEM with (b:=b); eauto; unnw.
    destruct (classic (l = locw)) as [|LNEQ]; subst.
    2: { rewrite REQ_TO; eauto. rewrite REQ_FROM; eauto.
         split; ins; [apply NOTNEWM|apply NOTNEWP]; auto. }
    assert (f_to' b <> f_to' w) as FTONEQ.
    { intros HH.
      eapply f_to_eq with 
          (I:=S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w)) in HH; eauto.
      { eapply f_to_coherent_more; [..| apply FCOH0]; auto.
        clear -DOMSBEQ. simplify_tls_events. rewrite DOMSBEQ. basic_solver. }
      { red. by rewrite LOC. }
      all: generalize SB; clear; basic_solver. }
    assert (f_to' b <> f_to' wnext) as FTONEQ'.
    { intros HH.
      eapply f_to_eq with 
          (I:=S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w)) in HH; eauto.
      { by subst. }
      { eapply f_to_coherent_more; [..| apply FCOH0]; auto.
        clear -DOMSBEQ. simplify_tls_events. rewrite DOMSBEQ. basic_solver. }
      { red. by rewrite NLOC. }
      all: generalize SB WNEXT; clear; basic_solver. }
    splits.
    { apply NOTNEWM; auto.
      rewrite REQ_TO; eauto. rewrite REQ_FROM; eauto. }
    ins. apply NOTNEWP; auto.
    rewrite REQ_TO; eauto. rewrite REQ_FROM; eauto. }
  intros WREL. red. ins. destruct msg; auto.
  exfalso. eapply SIM_PROM in GET. desc; subst.
  assert (E b) as EB.
  { eapply issuedE; eauto. }
  assert (W b) as WB.
  { eapply issuedW; eauto. }
  assert ((⦗E⦘ ⨾ same_tid ⨾ ⦗E⦘) b w) as HH.
  { apply seq_eqv_lr. splits; auto. }
  apply tid_sb in HH. destruct HH as [[[HH|HH]|HH]|[AA BB]]; subst; auto.
  2: { apply NCOVB. eapply dom_W_Rel_sb_loc_I_in_C; eauto.
       exists b. apply seq_eqv_l. split; [by split|].
       apply seqA.
       do 2 (apply seq_eqv_r; split; auto).
       split; auto. red. rewrite LOC. auto. }
    apply NCOV. eapply fwbob_issuable_in_C; eauto.
  exists w. apply seq_eqv_r. split; eauto. 
  apply sb_to_w_rel_in_fwbob. apply seq_eqv_r. 
  do 2 (split; auto).
  Unshelve. all: eauto. 
Qed.

End IssueReservedStepHelper.
