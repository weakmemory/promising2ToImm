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
From imm Require Import CombRelationsMore.
From imm Require Import AuxDef.
From imm Require Import FairExecution.

From imm Require Import TraversalOrder.
From imm Require Import TLSCoherency.
From imm Require Import IordCoherency.
From imm Require Import SimClosure. 
From imm Require Import AuxDef. 
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
Require Import IntervalHelper.
Require Import ExistsIssueInterval.
From imm Require Import TlsEventSets.
From imm Require Import EventsTraversalOrder.

Set Implicit Arguments.

Section IssueStepHelper.

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
Variable FCOH : f_to_coherent G (reserved T) f_to f_from.

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

Lemma issue_step_helper_no_next w valw locw ordw langst
      (TID : IdentMap.find (tid w) (Configuration.threads PC) = Some (langst, local))
      (NWEX : ~ W_ex w)
      (NISSB : ~ issued T w)
      (ISSUABLE : issuable G sc T w)
      (NONEXT : dom_sb_S_rfrmw G T rfi (eq w) ⊆₁ ∅)
      (LOC : loc lab w = Some locw)
      (VAL : val lab w = Some valw)
      (ORD : mod lab w = ordw)
      (WTID : thread = tid w)
      (FAIR: mem_fair G)
  :
  let promises := (Local.promises local) in
  let memory   := (Configuration.memory PC) in
  let sc_view  := (Configuration.sc PC) in

  (* let covered' := if Rel w then covered T ∪₁ eq w else covered T in *)
  (* let T'       := mkTC covered' (issued T ∪₁ eq w) in *)
  (* let S'       := S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G (mkETC T S) rfi (eq w) in *)
  let T' := T ∪₁ (if Rel w then eq (mkTL ta_cover w) else ∅) ∪₁ eq (mkTL ta_issue w) ∪₁ (eq ta_reserve <*> (eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w))) in
  exists p_rel,
    rfrmw_prev_rel G sc T f_to f_from (Configuration.memory PC) w locw p_rel /\
    (⟪ FOR_ISSUE :
         exists f_to' f_from',
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

           ⟪ REQ_TO : forall e (SE : S e) (NEQ : e <> w), f_to' e = f_to e ⟫ /\
           ⟪ REQ_FROM : forall e (SE : S e) (NEQ : e <> w), f_from' e = f_from e ⟫ /\
           ⟪ ISSEQ_TO   : forall e (ISS: issued T e), f_to' e = f_to e ⟫ /\
           ⟪ ISSEQ_FROM : forall e (ISS: issued T e), f_from' e = f_from e ⟫ /\
           ⟪ FTOWNBOT : f_to' w <> Time.bot ⟫ /\

           exists promises_add memory',
             ⟪ PADD :
                 Memory.add (Local.promises local) locw (f_from' w) (f_to' w)
                            (Message.full valw (Some rel')) promises_add ⟫ /\
             ⟪ MADD :
                 Memory.add memory locw (f_from' w) (f_to' w)
                            (Message.full valw (Some rel')) memory' ⟫ /\

             ⟪ INHAB : Memory.inhabited memory' ⟫ /\
             ⟪ RELMCLOS : Memory.closed_timemap (View.rlx rel') memory' ⟫ /\
             ⟪ RELVCLOS : Memory.closed_view rel' memory' ⟫ /\

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
                 reserved_time G T' f_to' f_from' smode memory' ⟫ /\

             ⟪ MEM_PROMISE :
                 Memory.promise (Local.promises local) memory locw (f_from' w) (f_to' w)
                                (Message.full valw (Some rel'))
                                promises_add memory' Memory.op_kind_add ⟫ /\

             exists promises',
               ⟪ PEQ :
                   if Rel w
                   then Memory.remove promises_add locw (f_from' w) (f_to' w)
                                      (Message.full valw (Some rel')) promises'
                   else promises' = promises_add ⟫ /\

               ⟪ NEW_PROM_IN_MEM : Memory.le promises' memory' ⟫ /\

               let tview' := if is_rel lab w
                             then TView.write_tview
                                    (Local.tview local) sc_view locw
                                    (f_to' w) (Event_imm_promise.wmod ordw)
                             else (Local.tview local) in
               let local' := Local.mk tview' promises' in
               let threads' :=
                   IdentMap.add (tid w)
                                (langst, local')
                                (Configuration.threads PC) in

               ⟪ THREAD : forall t (IN : (threads_set G \₁ eq tid_init) t), IdentMap.In t threads' ⟫ /\

               ⟪ SC_REQ : smode = sim_normal -> 
                          forall (l : Loc.t),
                            max_value
                              f_to' (S_tm G l (covered T')) (LocFun.find l sc_view) ⟫ /\
               ⟪ CLOSED_SC : Memory.closed_timemap sc_view memory' ⟫ /\

               ⟪ PROM_IN_MEM :
                   forall thread' langst local
                          (TID : IdentMap.find thread' threads' = Some (langst, local)),
                     Memory.le (Local.promises local) memory' ⟫ /\

               ⟪ SIM_PROM     : sim_prom G sc T' f_to' f_from' (tid w) promises'  ⟫ /\
               ⟪ SIM_RES_PROM : sim_res_prom G T' f_to' f_from' (tid w) promises'  ⟫ /\

               ⟪ PROM_DISJOINT :
                   forall thread' langst' local'
                          (TNEQ : tid w <> thread')
                          (TID' : IdentMap.find thread' threads' =
                                  Some (langst', local')),
                   forall loc to,
                     Memory.get loc to promises' = None \/
                     Memory.get loc to (Local.promises local') = None ⟫ /\

               ⟪ SIM_MEM     : sim_mem G sc T' f_to' f_from' (tid w) local' memory' ⟫ /\
               ⟪ SIM_RES_MEM : sim_res_mem G T' f_to' f_from' (tid w) local' memory' ⟫ /\
               ⟪ NOWLOC : Rel w -> Memory.nonsynch_loc locw (Local.promises local') ⟫
     ⟫ \/
     ⟪ FOR_SPLIT :
         ⟪ SMODE : smode = sim_certification ⟫ /\
         exists ws wsv wsrel f_to' f_from',
           let rel'' :=
               if is_rel lab w
               then (TView.cur (Local.tview local))
               else (TView.rel (Local.tview local) locw)
           in
           let rel' := (View.join (View.join rel'' (View.unwrap p_rel))
                                  (View.singleton_ur locw (f_to' w))) in
           let wsmsg := Message.full wsv wsrel in
           ⟪ NREL    : ~ Rel w ⟫ /\
           ⟪ EWS     : E ws ⟫ /\
           ⟪ WSS     : S ws ⟫ /\
           ⟪ WSISS  : issued T ws ⟫ /\
           ⟪ NWEXWS : ~ W_ex ws ⟫ /\
           ⟪ WSNCOV  : ~ covered T ws ⟫ /\
           ⟪ WSNINIT : ~ is_init ws ⟫ /\
           ⟪ WSTID   : tid ws = tid w ⟫ /\
           ⟪ WSVAL   : val lab ws = Some wsv ⟫ /\
           ⟪ WSSMSG : sim_msg G sc f_to ws (View.unwrap wsrel) ⟫ /\ 

           ⟪ SBWW : sb w ws ⟫ /\
           ⟪ SAME_LOC : Loc_ locw ws ⟫ /\
           ⟪ COWW : co w ws ⟫ /\

           ⟪ FEQ1 : f_to' w = f_from' ws ⟫ /\
           ⟪ FEQ2 : f_from' w = f_from ws ⟫ /\

           ⟪ WSPROM : Memory.get locw (f_to ws) (Local.promises local) =
                      Some (f_from ws, wsmsg)⟫ /\
           ⟪ WSMEM : Memory.get locw (f_to ws) memory =
                     Some (f_from ws, wsmsg)⟫ /\

           ⟪ RELWFEQ : View.pln rel' = View.rlx rel' ⟫ /\
           ⟪ REL_VIEW_LT : Time.lt (View.rlx rel'' locw) (f_to' w) ⟫ /\
           ⟪ REL_VIEW_LE : Time.le (View.rlx rel'  locw) (f_to' w) ⟫ /\
           ⟪ FCOH : f_to_coherent G (reserved T') f_to' f_from' ⟫ /\

           ⟪ REQ_TO : forall e (SE : S e) (NEQ : e <> w), f_to' e = f_to e ⟫ /\
           ⟪ ISSEQ_TO   : forall e (ISS: issued T e), f_to' e = f_to e ⟫ /\
           ⟪ FTOWNBOT : f_to' w <> Time.bot ⟫ /\

           exists promises_add memory',
             ⟪ PADD :
                 Memory.split (Local.promises local)
                              locw (f_from' w) (f_to' w) (f_to' ws)
                              (Message.full valw (Some rel'))
                              wsmsg
                              promises_add ⟫ /\
             ⟪ MADD :
                 Memory.split memory locw (f_from' w) (f_to' w) (f_to' ws)
                              (Message.full valw (Some rel'))
                              wsmsg
                              memory' ⟫ /\

             ⟪ INHAB : Memory.inhabited memory' ⟫ /\
             ⟪ RELMCLOS : Memory.closed_timemap (View.rlx rel') memory' ⟫ /\
             ⟪ RELVCLOS : Memory.closed_view rel' memory' ⟫ /\


             ⟪ HELPER :
                 sim_mem_helper
                   G sc f_to' w (f_from' w) valw
                   (View.join (View.join (if is_rel lab w
                                          then (TView.cur (Local.tview local))
                                          else (TView.rel (Local.tview local) locw))
                                         (View.unwrap p_rel))
                              (View.singleton_ur locw (f_to' w))) ⟫ /\

             ⟪ RESERVED_TIME :
                 reserved_time G T' f_to' f_from' smode memory' ⟫ /\

             exists promises',
               ⟪ PEQ :
                   if Rel w
                   then Memory.remove promises_add locw (f_from' w) (f_to' w)
                                      (Message.full valw (Some rel')) promises'
                   else promises' = promises_add ⟫ /\

               ⟪ NEW_PROM_IN_MEM : Memory.le promises' memory' ⟫ /\

               let tview' := if is_rel lab w
                             then TView.write_tview
                                    (Local.tview local) sc_view locw
                                    (f_to' w) (Event_imm_promise.wmod ordw)
                             else (Local.tview local) in
               let local' := Local.mk tview' promises' in
               let threads' :=
                   IdentMap.add (tid w)
                                (langst, local')
                                (Configuration.threads PC) in

               ⟪ THREAD : forall t (IN : (threads_set G \₁ eq tid_init) t), IdentMap.In t threads' ⟫ /\

               ⟪ SC_REQ : smode = sim_normal -> 
                          forall (l : Loc.t),
                            max_value
                              f_to' (S_tm G l (covered T')) (LocFun.find l sc_view) ⟫ /\
               ⟪ CLOSED_SC : Memory.closed_timemap sc_view memory' ⟫ /\

               ⟪ MEM_PROMISE :
                   ~ Rel w ->
                   Memory.promise (Local.promises local) memory locw (f_from' w) (f_to' w)
                                  (Message.full valw (Some rel'))
                                  promises' memory'
                                  (Memory.op_kind_split (f_to' ws) wsmsg) ⟫ /\

               ⟪ PROM_IN_MEM :
                   forall thread' langst local
                          (TID : IdentMap.find thread' threads' = Some (langst, local)),
                     Memory.le (Local.promises local) memory' ⟫ /\

               ⟪ SIM_PROM     : sim_prom G sc T' f_to' f_from' (tid w) promises'  ⟫ /\
               ⟪ SIM_RES_PROM : sim_res_prom G T' f_to' f_from' (tid w) promises'  ⟫ /\

               ⟪ PROM_DISJOINT :
                   forall thread' langst' local'
                          (TNEQ : tid w <> thread')
                          (TID' : IdentMap.find thread' threads' =
                                  Some (langst', local')),
                   forall loc to,
                     Memory.get loc to promises' = None \/
                     Memory.get loc to (Local.promises local') = None ⟫ /\

               ⟪ SIM_MEM     : sim_mem G sc T' f_to' f_from' (tid w) local' memory' ⟫ /\
               ⟪ SIM_RES_MEM : sim_res_mem G T' f_to' f_from' (tid w) local' memory' ⟫ /\
               ⟪ NOWLOC : Rel w -> Memory.nonsynch_loc locw (Local.promises local') ⟫ ⟫).
Proof using All.
  assert (complete G) as COMPL by apply IMMCON.
  assert (sc_per_loc G) as SPL by (apply coherence_sc_per_loc; apply IMMCON).
 
  assert (NSW : ~ S w).
  { intros HH. apply NWEX. apply RCOH. by split. }

  assert (S ⊆₁ E ∩₁ W) as SEW.
  { apply set_subset_inter_r. split; [by apply RCOH|].
    eapply reservedW; eauto. }
  assert (E w /\ W w) as [EW WW] by (by apply ISSUABLE).
  assert (~ covered T w) as NCOVB.
  { intros AA. apply NISSB. eapply w_covered_issued; eauto. by split. }
  assert (~ is_init w) as WNINIT.
  { intros HH. apply NCOVB. eapply init_covered; eauto. by split. }

  subst.

  remember (T ∪₁ (if Rel w then eq (mkTL ta_cover w) else ∅) ∪₁ eq (mkTL ta_issue w) ∪₁ eq ta_reserve <*> (eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w))) as T'. 

  assert (covered T' ≡₁ C ∪₁ (if Rel w then eq w else ∅)) as COV'.
  { subst T'. clear. simplify_tls_events. basic_solver 10. }
  assert (issued T' ≡₁ I ∪₁ eq w) as ISS'.
  { subst T'. clear. simplify_tls_events. basic_solver 10. }
  assert (reserved T' ≡₁ S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w)) as RES'.
  { subst T'. clear. simplify_tls_events. basic_solver 10. }

  edestruct exists_time_interval_for_issue_no_next as [p_rel [PREL [SEW' [HH|HH]]]]; eauto.
  2: { red in HH. desc. exists p_rel. splits; eauto.
       right. splits; eauto.
       set (wsmsg := Message.full wsv wsrel).
       exists ws, wsv, wsrel. exists f_to', f_from'.

       assert (f_to_coherent G (reserved T') f_to' f_from') as FCOH'. 
       { eapply f_to_coherent_more; [..| apply FCOH0]; eauto.
         subst T'. clear. simplify_tls_events. basic_solver. }
       assert (reserved_time G T' f_to' f_from' smode memory') as RT'.
       { eapply reserved_time_same_issued_reserved; [apply RESERVED_TIME0| ..]; eauto.
         all: subst T'; clear; simplify_tls_events; basic_solver. }

       splits; eauto.
       exists promises', memory'. splits; eauto.

       assert (ws <> w) as WSNEQ by (by intros HH; subst).
       assert (sim_msg G sc f_to' ws (View.unwrap wsrel)) as WSMSG'.
       { eapply sim_msg_f_issued; eauto. }

       set (rel'' :=
              if is_rel lab w
              then (TView.cur (Local.tview local))
              else (TView.rel (Local.tview local) locw)).
       set (rel' := (View.join (View.join rel'' (View.unwrap p_rel))
                               (View.singleton_ur locw (f_to' w)))).

       assert (exists promises'',
                  ⟪ PEQ :
                      if Rel w
                      then Memory.remove promises' locw (f_from' w) (f_to' w)
                                         (Message.full valw (Some rel')) promises''
                      else promises'' = promises' ⟫).
       { destruct (is_rel lab w) eqn:REL; eauto.
         edestruct Memory.remove_exists as [promises''].
         2: { exists promises''. eauto. }
         erewrite Memory.split_o; eauto. rewrite loc_ts_eq_dec_eq; auto. }
       desc.
       exists promises''. simpls.
       
       assert (Memory.le promises' memory') as PP.
       { eapply memory_le_split2; eauto. }

       assert (forall tmap (MCLOS : Memory.closed_timemap tmap (Configuration.memory PC)),
                  Memory.closed_timemap tmap memory') as MADDCLOS.
       { ins. eapply Memory.split_closed_timemap; eauto. }
       
       assert (Memory.le promises'' promises') as LEPADD.
       { destruct (Rel w) eqn:RELB; subst; [|reflexivity].
         eapply memory_remove_le; eauto. }

       assert (Memory.le promises'' memory') as NEW_PROM_IN_MEM.
       { etransitivity; eauto. }

       assert (forall l to from msg
                      (NEQ  : l <> locw \/ to <> f_to' w)
                      (NEQ' : l <> locw \/ to <> f_to' ws),
                  Memory.get l to memory' = Some (from, msg) <->
                  Memory.get l to (Configuration.memory PC) = Some (from, msg))
         as NOTNEWM.
       { ins. erewrite Memory.split_o; eauto. by rewrite !loc_ts_eq_dec_neq. }

       assert (forall l to from msg
                      (NEQ  : l <> locw \/ to <> f_to' w)
                      (NEQ' : l <> locw \/ to <> f_to' ws),
                  Memory.get l to promises' = Some (from, msg) <->
                  Memory.get l to (Local.promises local) = Some (from, msg))
         as NOTNEWA.
       { ins. erewrite Memory.split_o; eauto. by rewrite !loc_ts_eq_dec_neq. }

       assert (forall l to from msg
                      (NEQ  : l <> locw \/ to <> f_to' w)
                      (NEQ' : l <> locw \/ to <> f_to' ws),
                  Memory.get l to promises'' = Some (from, msg) <->
                  Memory.get l to (Local.promises local) = Some (from, msg))
         as NOTNEWP.
       { ins. arewrite (promises'' = promises') by desf. by apply NOTNEWA. }

       assert (~ Rel w ->
               Memory.get locw (f_to' w) promises'' =
               Some (f_from' w, Message.full valw (Some rel')))
         as INP''.
       { ins. destruct (Rel w); subst; [by desf|].
         erewrite Memory.split_o; eauto. by rewrite loc_ts_eq_dec_eq. }

       assert (f_to' ws <> f_to' w) as WWSFTONEQ.
       { intros HH. eapply f_to_eq in HH; eauto.
         { red. by rewrite LOC. }
         all: clear -WSS; find_event_set. }

       assert (Memory.get locw (f_to' ws) promises' =
               Some (f_from' ws, Message.full wsv wsrel)) as WSMSGGET'.
       { erewrite Memory.split_o; eauto. rewrite loc_ts_eq_dec_neq; eauto.
         rewrite loc_ts_eq_dec_eq. by rewrite FEQ1. }

       assert (Memory.get locw (f_to' ws) promises'' =
               Some (f_from' ws, Message.full wsv wsrel)) as WSMSGGET'' by desf.

       splits; eauto.
       { intros e' EE. 
         apply IdentMap.Facts.add_in_iff.
         destruct (Ident.eq_dec e' (tid w)) as [|NEQ]; subst; auto. }
       { intros QQ l.
         assert (max_value f_to' (S_tm G l (covered T)) (LocFun.find l (Configuration.sc PC))) as BB.
         { eapply sc_view_f_issued; eauto. }
         destruct (Rel w).
         2: { rewrite COV'. basic_solver. }
         eapply max_value_same_set.
         { apply BB. }
         eapply s_tm_n_f_steps.
         { by apply init_covered. }
         { subst T'. clear. simplify_tls_events. basic_solver. }
         intros a [HB|HB]%COV' HH AA.
         { eauto. }
         subst. clear -WW AA. type_solver. }
       { intros HH. arewrite (promises'' = promises') by desf. }
       { ins.
         destruct (Ident.eq_dec thread' (tid w)) as [EQ|NEQ].
         { subst. rewrite IdentMap.gss in TID0.
           inv TID0; simpls; clear TID0. }
         red; ins; rewrite IdentMap.gso in TID0; auto.
         erewrite Memory.split_o; eauto.
         destruct (loc_ts_eq_dec (loc, to) (locw, f_to' w)) as [[A B]|LL].
         { simpls; rewrite A in *; rewrite B in *; subst.
           exfalso. erewrite NINTER in LHS; eauto. inv LHS. }
         rewrite (loc_ts_eq_dec_neq LL).
         set (AA:=LHS).
         eapply PROM_IN_MEM in AA; eauto.
         destruct (loc_ts_eq_dec (loc, to) (locw, f_to' ws)) as [[A B]|LL'].
         2: by rewrite (loc_ts_eq_dec_neq LL').
         simpls; subst.
         rewrite (loc_ts_eq_dec_eq locw (f_to' ws)).
         rewrite REQ_TO in LHS; auto.
         rewrite REQ_TO in AA; auto.
         rewrite WSMEM in AA. inv AA.
         exfalso.
         edestruct PROM_DISJOINT with (local':=local0) as [BB|BB]; eauto.
         2: { rewrite BB in LHS. inv LHS. }
         rewrite WSPROM in BB. inv BB. }
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
         simpls.
         assert (PROM' :
                   Memory.get l to promises' = Some (from, Message.full v rel)).
         { destruct (Rel w) eqn:RELB; subst; auto. }
         erewrite Memory.split_o in PROM'; eauto.
         rewrite (loc_ts_eq_dec_neq LL) in PROM'.
         destruct (loc_ts_eq_dec (l, to) (locw, f_to' ws)) as [[A' B']|LL'].
         { simpls; rewrite A' in *; rewrite B' in *.
           rewrite (loc_ts_eq_dec_eq locw (f_to' ws)) in PROM'.
           inv PROM'. exists ws. splits; eauto.
           { clear -WSISS. find_event_set. }
           { clear -WSNCOV WSNEQ. separate_set_event. }
           red. splits; eauto.
           left. eapply f_to_co_mon; eauto.
           all: clear -WSS WSS; find_event_set. }
         simpls. rewrite (loc_ts_eq_dec_neq LL') in PROM'.
         edestruct SIM_PROM as [b H]; eauto; desc.
         exists b; splits; auto.
         { apply ISS'. clear -ISS. find_event_set. } 
         { intros [? | ?]%COV'; auto. 
           destruct (Rel w) eqn:RELB; auto. }
         { rewrite ISSEQ_FROM; auto. intros HH. subst.
           assert (Some l = Some locw) as BB.
           { rewrite <- LOC0. by rewrite <- SAME_LOC. }
           inv BB. destruct LL' as [|LL']; [done|].
           rewrite ISSEQ_TO in LL'; auto. }
         { by rewrite ISSEQ_TO. }
         eapply sim_mem_helper_f_issued with (f_to:=f_to); eauto. }
       { simpls. red. ins.
         destruct (loc_ts_eq_dec (l, to) (locw, f_to' w)) as [[A' B']|LL].
         { simpls; rewrite A' in *; rewrite B' in *.
           destruct (Rel w) eqn:RELB; subst.
           { erewrite Memory.remove_o in RES; eauto.
             rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in RES. inv RES. }
           erewrite Memory.split_o in RES; eauto.
           rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in RES. inv RES. }
         simpls.
         assert (PROM' :
                   Memory.get l to promises' = Some (from, Message.reserve)).
         { destruct (Rel w) eqn:RELB; subst; auto. }
         erewrite Memory.split_o in PROM'; eauto.
         rewrite (loc_ts_eq_dec_neq LL) in PROM'.
         destruct (loc_ts_eq_dec (l, to) (locw, f_to' ws)) as [[A' B']|LL'].
         { simpls; rewrite A' in *; rewrite B' in *.
           rewrite (loc_ts_eq_dec_eq locw (f_to' ws)) in PROM'.
           inv PROM'. }
         simpls. rewrite (loc_ts_eq_dec_neq LL') in PROM'.
         edestruct SIM_RES_PROM as [b H]; eauto; desc.
         exists b. splits; auto.
         { subst T'. clear -RES0. find_event_set. }
         { intros [A|A]%ISS'; desf. }
         { rewrite REQ_FROM; auto. intros HH; subst.
           assert (Some l = Some locw) as BB.
           { rewrite <- LOC0. by rewrite <- SAME_LOC. }
           inv BB. }
         rewrite REQ_TO; auto. by intros HH; subst. }
       { ins.
         rewrite IdentMap.gso in TID'; auto.
         destruct (loc_ts_eq_dec (loc, to) (locw, (f_to' w))) as [EQ|NEQ]; simpls.
         { desc. subst. right.
           destruct (Memory.get locw (f_to' w) (Local.promises local')) eqn: HH; auto.
           exfalso.
           erewrite NINTER in HH; eauto. inv HH. }
         edestruct (PROM_DISJOINT TNEQ TID') as [HH|HH]; eauto.
         left.
         enough (Memory.get loc to promises' = None).
         { destruct (Rel w) eqn:RELB; subst; auto.
           erewrite Memory.remove_o; eauto. by rewrite (loc_ts_eq_dec_neq NEQ). }
         erewrite Memory.split_o; eauto.
         rewrite (loc_ts_eq_dec_neq NEQ).
         destruct (loc_ts_eq_dec (loc, to) (locw, (f_to' ws))) as [[A' B']|NEQ'].
         2: by rewrite (loc_ts_eq_dec_neq NEQ').
         simpls; rewrite A' in *; rewrite B' in *.
         exfalso. rewrite REQ_TO in HH; auto.
         rewrite HH in WSPROM. inv WSPROM. }
       { red. ins. 
         apply ISS' in ISSB. destruct ISSB as [ISSB|]; subst.
         { edestruct SIM_MEM as [rel_opt HH]; eauto. simpls. desc.
           exists rel_opt. unnw.
           destruct (loc_ts_eq_dec (l, f_to' b) (locw, (f_to' w))) as [EQ|NEQ]; simpls; desc; subst.
           { exfalso.
             assert (b = w); [|by desf].
             eapply f_to_eq; try apply FCOH0; eauto.
             { red. by rewrite LOC. }
             { eapply rcoh_I_in_S in ISSB; eauto. clear -ISSB. find_event_set. }
             clear. find_event_set. }
           destruct (loc_ts_eq_dec (l, f_to' b) (locw, (f_to' ws))) as [EQ|NEQ']; simpls; desc; subst.
           { assert (b = ws); subst.
             { eapply f_to_eq; try apply FCOH0; eauto.
               { red. by rewrite SAME_LOC. }
               { eapply rcoh_I_in_S in ISSB; eauto. clear -ISSB. find_event_set. }
               clear -WSS. find_event_set. }
             rewrite INMEM in WSMEM. inv WSMEM.
             splits; eauto.
             { red. splits; eauto. left. apply FCOH0; auto.
               clear -WSS. find_event_set. }
             ins. destruct HH1 as [HH1 HH2]; auto.
             split; auto.
             desc. exists p_rel0. split.
             { rewrite ISSEQ_TO with (e:=ws); auto. desf. }
             destruct HH0 as [AA|]; desc; [left; split; auto|right].
             { intros HH. apply NWEXWS. red. generalize HH. clear. basic_solver. }
             exfalso. apply NWEXWS. red. generalize H2. clear. basic_solver. }

           assert (b <> ws) as NWSNEQ.
           { intros SUBST; subst.
             destruct NEQ' as [AA|]; eauto. rewrite LOC0 in SAME_LOC. inv SAME_LOC. }
           erewrite Memory.split_o with (mem2:=memory'); eauto.
           rewrite !loc_ts_eq_dec_neq; auto.
           splits; eauto.
           { rewrite ISSEQ_TO; auto. rewrite ISSEQ_FROM; auto. }
           { rewrite ISSEQ_FROM; auto. eapply sim_mem_helper_f_issued; eauto. }
           intros AA BB.
           assert (~ covered T b) as NCOVBB.
           { intros HH. apply BB. clear -HH. find_event_set. }
           specialize (HH1 AA NCOVBB).
           desc. splits; auto.
           { apply NOTNEWP; auto.
             rewrite ISSEQ_TO; auto. rewrite ISSEQ_FROM; auto. }
           eexists. splits; eauto.
           2: { destruct HH2 as [[CC DD]|CC]; [left|right].
                { split; eauto. intros [y HH]. destruct_seq_l HH as OO.
                  apply ISS' in OO. destruct OO as [OO|]; subst.
                  { apply CC. exists y. apply seq_eqv_l. by split. }
                  apply NISSB. eapply rfrmw_I_in_I; eauto. exists b.
                  apply seqA. apply seq_eqv_r. by split. }
                desc. exists p. splits; auto.
                { clear -CC. find_event_set. }
                assert (loc lab p = Some l) as PLOC.
                { rewrite <- LOC0. by apply wf_rfrmwl. }
                eexists. splits; eauto.
                assert (l <> locw \/ f_to' p <> f_to' w) as NEQ''.
                { destruct (classic (l = locw)); subst; [right|left]; auto.
                  intros HH. eapply f_to_eq in HH; eauto; subst; auto.
                  { red. by rewrite PLOC. }
                  { eapply rcoh_I_in_S in CC; eauto.
                    clear -CC. find_event_set. }
                  clear. find_event_set. }
                destruct (classic (p = ws)) as [|NEQPWS]; subst.
                2: { apply NOTNEWM; auto.
                     2: by rewrite ISSEQ_TO; auto; rewrite ISSEQ_FROM.
                     destruct (classic (l = locw)) as [|LNEQ]; subst; auto.
                     right. intros HH. eapply f_to_eq in HH; eauto.
                     { red. by rewrite PLOC. }
                     all: eapply rcoh_I_in_S in CC, WSISS; eauto.
                     all: clear -CC WSISS; find_event_set. }
                rewrite PLOC in SAME_LOC. inv SAME_LOC.
                erewrite Memory.split_o; eauto.
                rewrite loc_ts_eq_dec_neq; auto.
                rewrite loc_ts_eq_dec_eq; auto. by rewrite FEQ1. }
           destruct (Rel w) eqn:RELW; eauto.
           { by desf. }
             by rewrite ISSEQ_TO. }

         assert (Some l = Some locw) as QQ.
         { by rewrite <- LOC0. }
         inv QQ.
         eexists. splits; eauto.
         intros _ NT.
         destruct (Rel b); desf.
         splits.
         { erewrite Memory.split_o; eauto. rewrite loc_ts_eq_dec_eq; eauto. }
         exists p_rel. splits; eauto. left.
         cdes PREL. destruct PREL1; desc.
         2: { exfalso. apply NWEX. red. generalize INRMW. clear. basic_solver. }
         split; auto.
         intros [a HH].
         eapply same_relation_exp in HH.
         2: { simplify_tls_events. reflexivity. }
         apply seq_eqv_l in HH. destruct HH as [[HH|] RFRMW]; subst; eauto.
         { apply NINRMW. generalize HH RFRMW. clear. basic_solver 10. }
         eapply wf_rfrmw_irr; eauto. }
       { red. ins.
         assert (b <> w /\ ~ issued T b) as [BNEQ NISSBB].
         { contra BB. apply NISSB0. apply ISS'.
           apply not_and_or in BB. destruct BB as [->%NNPP | ?%NNPP].
           all: unfolder; auto. }
         assert (b <> ws) as BNEQ'.
         { intros HH; subst. eauto. }
         apply RES' in RESB. destruct RESB as [[SB|]|HH]; subst.
         3: { exfalso. eapply NONEXT; eauto. }
         2: by desf.
         unnw.
         erewrite Memory.split_o with (mem2:=memory'); eauto.
         destruct (loc_ts_eq_dec (l, f_to' b) (locw, (f_to' w))) as [PEQ'|PNEQ];
           simpls; desc; subst.
         { exfalso. apply BNEQ.
           eapply f_to_eq with (f_to:=f_to'); eauto. red.
           { by rewrite LOC. }
           { clear -SB. find_event_set. }
           clear. find_event_set. }
         rewrite (loc_ts_eq_dec_neq PNEQ).
         destruct (loc_ts_eq_dec (l, f_to' b) (locw, (f_to' ws))) as [PEQ''|PNEQ'];
           simpls; desc; subst.
         { exfalso. apply BNEQ'.
           eapply f_to_eq with (f_to:=f_to'); eauto. red.
           { by rewrite LOC0. }
           { clear -SB. find_event_set. }
           clear -WSS. find_event_set. }
         rewrite (loc_ts_eq_dec_neq PNEQ').
         edestruct SIM_RES_MEM with (b:=b); eauto; unnw.
         rewrite REQ_TO; auto. rewrite REQ_FROM; auto.
         splits; ins.
         apply NOTNEWP; auto.
         all: rewrite <- REQ_TO; auto. }
       intros WREL. clear -WREL NREL. vauto. }
  red in HH. desc. exists p_rel. splits; eauto.
  assert (f_to_coherent G (reserved T') f_to' f_from') as FCOH'. 
  { eapply f_to_coherent_more; [..| apply FCOH0]; eauto.
    subst T'. clear. simplify_tls_events. basic_solver. }
  assert (reserved_time G T' f_to' f_from' smode memory') as RT'.
  { eapply reserved_time_same_issued_reserved; [apply RESERVED_TIME0| ..]; eauto.
    all: subst T'; clear; simplify_tls_events; basic_solver. }
  
  left. exists f_to', f_from'. splits; eauto.
  exists promises', memory'. splits; eauto.

  set (rel'' :=
        if is_rel lab w
        then (TView.cur (Local.tview local))
        else (TView.rel (Local.tview local) locw)).
  set (rel' := (View.join (View.join rel'' (View.unwrap p_rel))
                          (View.singleton_ur locw (f_to' w)))).

  assert (exists promises'',
             ⟪ PEQ :
                 if Rel w
                 then Memory.remove promises' locw (f_from' w) (f_to' w)
                                    (Message.full valw (Some rel')) promises''
                 else promises'' = promises' ⟫).
  { destruct (is_rel lab w) eqn:REL; eauto.
    edestruct Memory.remove_exists as [promises''].
    2: { exists promises''. eauto. }
    erewrite Memory.add_o; eauto. rewrite loc_ts_eq_dec_eq; auto. }
  desc.
  exists promises''. simpls.
  
  assert (Memory.le promises' memory') as PP.
  { eapply memory_le_add2; eauto. }

  assert (forall thread' langst' local' (TNEQ : tid w <> thread')
                 (TID' : IdentMap.find thread' (Configuration.threads PC) =
                         Some (langst', local')),
             Memory.get locw (f_to' w) (Local.promises local') = None) as NINTER.
  { ins.
    destruct (Memory.get locw (f_to' w) (Local.promises local')) eqn:HH; auto.
    exfalso. destruct p as [from].
    eapply PROM_IN_MEM in HH; eauto.
    set (AA := HH). apply Memory.get_ts in AA.
    destruct AA as [|AA]; desc; eauto.
    apply DISJOINT in HH.
    apply HH with (x:=f_to' w); constructor; simpls; try reflexivity.
    apply FCOH0; auto. clear. find_event_set.  }

  assert (forall tmap (MCLOS : Memory.closed_timemap tmap (Configuration.memory PC)),
             Memory.closed_timemap tmap memory') as MADDCLOS.
  { ins. eapply Memory.add_closed_timemap; eauto. }
  
  assert (Memory.le promises'' promises') as LEPADD.
  { destruct (Rel w) eqn:RELB; subst; [|reflexivity].
    eapply memory_remove_le; eauto. }

  assert (Memory.le promises'' memory') as NEW_PROM_IN_MEM.
  { etransitivity; eauto. }

  (* assert (forall l to from msg  *)
  (*                (NEQ : l <> locw \/ to <> f_to w), *)
  (*            Memory.get l to promises_cancel = Some (from, msg) <-> *)
  (*            Memory.get l to (Local.promises local) = Some (from, msg)) *)
  (*   as NOTNEWC. *)
  (* { ins. erewrite Memory.remove_o; eauto. *)
  (*   rewrite loc_ts_eq_dec_neq; auto. } *)

  assert (forall l to from msg
                 (NEQ : l <> locw \/ to <> f_to' w),
             Memory.get l to memory' = Some (from, msg) <->
             Memory.get l to (Configuration.memory PC) = Some (from, msg))
    as NOTNEWM.
  { ins. erewrite Memory.add_o; eauto. by rewrite loc_ts_eq_dec_neq. }

  assert (forall l to from msg
                 (NEQ : l <> locw \/ to <> f_to' w),
             Memory.get l to promises' = Some (from, msg) <->
             Memory.get l to (Local.promises local) = Some (from, msg))
    as NOTNEWA.
  { ins. erewrite Memory.add_o; eauto. by rewrite loc_ts_eq_dec_neq. }

  assert (forall l to from msg
                 (NEQ : l <> locw \/ to <> f_to' w),
             Memory.get l to promises'' = Some (from, msg) <->
             Memory.get l to (Local.promises local) = Some (from, msg))
    as NOTNEWP.
  { ins. destruct (Rel w); subst; auto.
    erewrite Memory.remove_o; eauto. rewrite loc_ts_eq_dec_neq; eauto. }

  assert (~ Rel w ->
          Memory.get locw (f_to' w) promises'' =
          Some (f_from' w, Message.full valw (Some rel')))
    as INP''.
  { ins. destruct (Rel w); subst; [by desf|].
    erewrite Memory.add_o; eauto. by rewrite loc_ts_eq_dec_eq. }

  splits; eauto.
  { intros e' EE. 
    apply IdentMap.Facts.add_in_iff.
    destruct (Ident.eq_dec e' (tid w)) as [|NEQ]; subst; auto. }
  { intros QQ l.
    assert (max_value f_to' (S_tm G l (covered T)) (LocFun.find l (Configuration.sc PC))) as BB.
    { eapply sc_view_f_issued; eauto. }
    destruct (Rel w); auto.
    2: { rewrite COV', set_union_empty_r. auto. }
    eapply max_value_same_set.
    { apply BB. }
    eapply s_tm_n_f_steps.
    { by apply init_covered. }
    { subst T'. clear. simplify_tls_events. basic_solver. }
    intros a [HB|HB]%COV' HH AA.
    { eauto. }
    subst. clear -WW AA. type_solver. }
  { ins.
    destruct (Ident.eq_dec thread' (tid w)) as [EQ|NEQ].
    { subst. rewrite IdentMap.gss in TID0.
      inv TID0; simpls; clear TID0. }
    red; ins; rewrite IdentMap.gso in TID0; auto.
    erewrite Memory.add_o; eauto.
    destruct (loc_ts_eq_dec (loc, to) (locw, f_to' w)) as [[A B]|LL].
    { simpls; rewrite A in *; rewrite B in *; subst.
      exfalso. erewrite NINTER in LHS; eauto. inv LHS. }
    rewrite (loc_ts_eq_dec_neq LL).
    eapply PROM_IN_MEM in LHS; eauto. }
  { simpls. red. ins.
    destruct (loc_ts_eq_dec (l, to) (locw, f_to' w)) as [[A' B']|LL].
    { simpls; rewrite A' in *; rewrite B' in *.
      destruct (Rel w) eqn:RELB; subst.
      { erewrite Memory.remove_o in PROM; eauto.
        rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in PROM. inv PROM. }
      erewrite Memory.add_o in PROM; eauto.
      rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in PROM.
      inv PROM. exists w. splits; eauto.
      { clear. find_event_set. }
      clear -NCOVB. separate_set_event. }
    eapply NOTNEWP in PROM; eauto.
    edestruct SIM_PROM as [b H]; eauto; desc.
    exists b; splits; auto.
    { apply ISS'. clear -ISS. find_event_set. }
    { assert (W b) as WB by (eapply issuedW; eauto).
      intros [? | ?]%COV'; auto.  
      destruct (Rel w) eqn:RELB; vauto. }
    { by rewrite ISSEQ_FROM. }
    { by rewrite ISSEQ_TO. }
    eapply sim_mem_helper_f_issued with (f_to:=f_to); eauto. }
  { simpls. red. ins.
    destruct (loc_ts_eq_dec (l, to) (locw, f_to' w)) as [[A' B']|LL].
    { simpls; rewrite A' in *; rewrite B' in *.
      destruct (Rel w) eqn:RELB; subst.
      { erewrite Memory.remove_o in RES; eauto.
        rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in RES. inv RES. }
      erewrite Memory.add_o in RES; eauto.
      rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in RES. inv RES. }
    apply NOTNEWP in RES; auto.
    edestruct SIM_RES_PROM as [b H]; eauto; desc.
    exists b. splits; auto.
    { subst T'. clear -RES0. find_event_set. }
    { intros [A|A]%ISS'; desf. }
    { rewrite REQ_FROM; auto. by intros HH; subst. }
      rewrite REQ_TO; auto. by intros HH; subst. }
  { ins.
    rewrite IdentMap.gso in TID'; auto.
    destruct (loc_ts_eq_dec (loc, to) (locw, (f_to' w))) as [EQ|NEQ]; simpls.
    { desc. subst. right.
      destruct (Memory.get locw (f_to' w) (Local.promises local')) eqn: HH; auto.
      exfalso.
      erewrite NINTER in HH; eauto. inv HH. }
    edestruct (PROM_DISJOINT TNEQ TID') as [HH|HH]; eauto.
    left.
    destruct (Memory.get loc to promises'') eqn:BB; auto.
    destruct p. eapply NOTNEWP in BB; eauto. desf. }
  { red. ins.
    apply ISS' in ISSB. destruct ISSB as [ISSB|]; subst.
    { edestruct SIM_MEM as [rel_opt HH]; eauto. simpls. desc.
      exists rel_opt. unnw.
      destruct (loc_ts_eq_dec (l, f_to' b) (locw, (f_to' w))) as [EQ|NEQ]; simpls; desc; subst.
      { exfalso.
        assert (b = w); [|by desf].
        eapply f_to_eq; try apply FCOH0; eauto.
        { red. by rewrite LOC. }
        { eapply rcoh_I_in_S in ISSB; eauto. clear -ISSB. find_event_set. }
        clear. find_event_set. }
      erewrite Memory.add_o with (mem2:=memory'); eauto.
      rewrite !loc_ts_eq_dec_neq; auto.
      splits; eauto.
      { rewrite ISSEQ_TO; auto. rewrite ISSEQ_FROM; auto. }
      { rewrite ISSEQ_FROM; auto. eapply sim_mem_helper_f_issued; eauto. }
      intros AA BB.
      assert (~ covered T b) as NCOVBB.
      { intros HH. apply BB. clear -HH. find_event_set. }
      specialize (HH1 AA NCOVBB).
      desc. splits; auto.
      { apply NOTNEWP; auto.
        rewrite ISSEQ_TO; auto. rewrite ISSEQ_FROM; auto. }
      eexists. splits; eauto.
      2: { destruct HH2 as [[CC DD]|CC]; [left|right].
           { split; eauto. intros [y HH]. destruct_seq_l HH as OO.
             apply ISS' in OO. destruct OO as [OO|]; subst.
             { apply CC. exists y. apply seq_eqv_l. by split. }
             apply NISSB. eapply rfrmw_I_in_I; eauto. exists b.
             apply seqA. apply seq_eqv_r. by split. }
           desc. exists p. splits; auto.
           { clear -CC. find_event_set. }
           eexists. splits; eauto.
           rewrite ISSEQ_TO; auto. rewrite ISSEQ_FROM; auto.
           apply NOTNEWM; auto.
           destruct (classic (l = locw)) as [|LNEQ]; subst; auto.
           right. intros HH.
           rewrite <- ISSEQ_TO in HH; auto.
           eapply f_to_eq in HH; eauto; subst; auto.
           { red. rewrite LOC. rewrite <- LOC0. by apply (wf_rfrmwl WF). }
           { eapply rcoh_I_in_S in CC; eauto. clear -CC. find_event_set. }
           clear. find_event_set. }
      destruct (Rel w) eqn:RELW; auto.
      2: by rewrite ISSEQ_TO.
      assert (wmod (mod lab w) = Ordering.acqrel) as MM.
      { clear -RELW. mode_solver. }
      rewrite MM.
      unfold TView.rel, TView.write_tview. 
      arewrite (Ordering.le Ordering.acqrel Ordering.acqrel = true) by reflexivity.
      destruct (classic (l = locw)) as [|LNEQ]; subst.
      2: { unfold LocFun.add. rewrite Loc.eq_dec_neq; auto. by rewrite ISSEQ_TO. }
      exfalso.
      assert (E b) as EB by (eapply issuedE; eauto).
      assert (W b) as WB by (eapply issuedW; eauto).
      assert ((⦗E⦘ ⨾ same_tid ⨾ ⦗E⦘) w b) as ST.
      { apply seq_eqv_lr. by splits. }
      apply tid_sb in ST. destruct ST as [[[|ST]|ST]|[AI BI]]; subst; auto.
      2: { apply NCOVBB. eapply fwbob_issuable_in_C; eauto.
           eexists. apply seq_eqv_r. split; eauto.
           apply sb_to_w_rel_in_fwbob. apply seq_eqv_r. split; auto. by split. }
      assert (issuable G sc T b) as IB by (eapply issued_in_issuable; eauto).
      apply NCOVB. eapply fwbob_issuable_in_C; eauto.
      eexists. apply seq_eqv_r. split; eauto.
      apply sb_from_w_rel_in_fwbob; auto. apply seq_eqv_lr. splits; auto.
      all: split; auto. red. by rewrite LOC. }
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
    exists p_rel. splits; eauto. left.
    cdes PREL. destruct PREL1; desc.
    2: { exfalso. apply NWEX. red. generalize INRMW. clear. basic_solver. }
    split; auto.
    intros [a HH].
    eapply same_relation_exp in HH.
    2: { clear. simplify_tls_events. reflexivity. }
    apply seq_eqv_l in HH. destruct HH as [[HH|] RFRMW]; subst; eauto.
    { apply NINRMW. generalize HH RFRMW. clear. basic_solver 10. }
    eapply wf_rfrmw_irr; eauto. }
  { red. ins.
    assert (b <> w /\ ~ issued T b) as [BNEQ NISSBB].
    { contra BB. apply NISSB0. apply ISS'.
      apply not_and_or in BB. destruct BB as [->%NNPP | ?%NNPP].
      all: unfolder; auto. }
    apply RES' in RESB. destruct RESB as [[SB|]|HH]; subst.
    3: { exfalso. eapply NONEXT; eauto. }
    2: by desf.
    unnw.
    erewrite Memory.add_o with (mem2:=memory'); eauto.
    destruct (loc_ts_eq_dec (l, f_to' b) (locw, (f_to' w))) as [PEQ'|PNEQ];
      simpls; desc; subst.
    { exfalso. apply BNEQ.
      eapply f_to_eq with (f_to:=f_to'); eauto. red.
      { by rewrite LOC. }
      { clear -SB. find_event_set. }
      clear. find_event_set. }
    edestruct SIM_RES_MEM with (b:=b); eauto; unnw.
    rewrite !(loc_ts_eq_dec_neq PNEQ); auto.
    rewrite REQ_TO; auto. rewrite REQ_FROM; auto.
    splits; ins.
    apply NOTNEWP; auto. rewrite <- REQ_TO; auto. }
  intros WREL. red. ins. destruct msg; auto.
  rewrite WREL in PEQ.
  exfalso. 
  erewrite Memory.remove_o in GET; eauto.
  destruct (loc_ts_eq_dec (locw, t) (locw, f_to' w)) as [AA|NEQ]; simpls.
  { desc; subst. rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in GET.
    inv GET. }
  rewrite (loc_ts_eq_dec_neq NEQ) in GET.
  erewrite Memory.add_o in GET; eauto.
  rewrite (loc_ts_eq_dec_neq NEQ) in GET.
  eapply SIM_PROM in GET. desc; subst.
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
  eexists. apply seq_eqv_r. split; eauto.
  apply sb_to_w_rel_in_fwbob. apply seq_eqv_r. split; auto. by split. 
Qed.

End IssueStepHelper.
