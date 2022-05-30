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

From imm Require Import TraversalConfig.
From imm Require Import ViewRelHelpers.
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
Require Import ExistsIssueNextInterval.

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

Variable T : trav_config.
Variable S : actid -> Prop.
Variable ETCCOH : etc_coherent G sc (mkETC T S).

Variable RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T.

Variable f_to f_from : actid -> Time.t.
Variable FCOH : f_to_coherent G S f_to f_from.

Variable PC : Configuration.t.
Hypothesis THREAD : forall e (ACT : E e) (NINIT : ~ is_init e),
    exists langst, IdentMap.find (tid e) (Configuration.threads PC) = Some langst.

Variable smode : sim_mode.
Hypothesis SC_REQ :
  smode = sim_normal -> 
  forall (l : Loc.t),
    max_value f_to (S_tm G l (covered T)) (LocFun.find l (Configuration.sc PC)).

Variable thread : thread_id.
Variable local : Local.t.
Hypothesis SIM_PROM     : sim_prom     G sc T   f_to f_from thread (Local.promises local).
Hypothesis SIM_RES_PROM : sim_res_prom G    T S f_to f_from thread (Local.promises local).

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
  reserved_time G T S f_to f_from smode (Configuration.memory PC).

Hypothesis SIM_RES_MEM :
  sim_res_mem G T S f_to f_from thread local (Configuration.memory PC).

Hypothesis SIM_MEM : sim_mem G sc T f_to f_from thread local (Configuration.memory PC).
Hypothesis SIM_TVIEW : sim_tview G sc (covered T) f_to (Local.tview local) thread.
Hypothesis RMWREX : dom_rel rmw ⊆₁ R_ex lab.

Lemma issue_step_helper_next w wnext valw locw ordw langst
      (TID : IdentMap.find (tid w) (Configuration.threads PC) = Some (langst, local))
      (NWEX : ~ W_ex w)
      (NISSB : ~ issued T w)
      (ISSUABLE : issuable G sc T w)
      (NEXT : dom_sb_S_rfrmw G (mkETC T S) rfi (eq w) wnext)
      (LOC : loc lab w = Some locw)
      (VAL : val lab w = Some valw)
      (ORD : mod lab w = ordw)
      (WTID : thread = tid w)
      (FAIR: mem_fair G):
  let promises := (Local.promises local) in
  let memory   := (Configuration.memory PC) in
  let sc_view  := (Configuration.sc PC) in
  let covered' := if Rel w then covered T ∪₁ eq w else covered T in
  let T'       := mkTC covered' (issued T ∪₁ eq w) in
  let S'       := S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G (mkETC T S) rfi (eq w) in
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

           ⟪ REQ_TO : forall e (SE : S e), f_to' e = f_to e ⟫ /\
           ⟪ REQ_FROM : forall e (SE : S e), f_from' e = f_from e ⟫ /\
           ⟪ ISSEQ_TO   : forall e (ISS: issued T e), f_to' e = f_to e ⟫ /\
           ⟪ ISSEQ_FROM : forall e (ISS: issued T e), f_from' e = f_from e ⟫ /\
           ⟪ FTOWNBOT     : f_to' w <> Time.bot ⟫ /\
           ⟪ FTOWNEXTNBOT : f_to' wnext <> Time.bot ⟫ /\
           << FTONEXTNEQ  : f_to' w <> f_to' wnext >> /\

           exists promises_add memory_add promises_rel promises_add2 memory',
             ⟪ PADD :
                 Memory.add (Local.promises local) locw (f_from' w) (f_to' w)
                            (Message.full valw (Some rel')) promises_add ⟫ /\
             ⟪ MADD :
                 Memory.add memory locw (f_from' w) (f_to' w)
                            (Message.full valw (Some rel')) memory_add ⟫ /\

             ⟪ PEQ :
                 if Rel w
                 then Memory.remove promises_add locw (f_from' w) (f_to' w)
                                    (Message.full valw (Some rel')) promises_rel
                 else promises_rel = promises_add ⟫ /\

             ⟪ PADD2 :
                 Memory.add promises_rel locw (f_from' wnext) (f_to' wnext)
                            Message.reserve promises_add2 ⟫ /\
             ⟪ MADD2 :
                 Memory.add memory_add locw (f_from' wnext) (f_to' wnext)
                            Message.reserve memory' ⟫ /\


             ⟪ INHAB : Memory.inhabited memory' ⟫ /\
             ⟪ RELMCLOS : Memory.closed_timemap (View.rlx rel') memory_add ⟫ /\
             ⟪ RELVCLOS : Memory.closed_view rel' memory_add ⟫ /\

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
                 reserved_time G T' S' f_to' f_from' smode memory' ⟫ /\

             ⟪ MEM_PROMISE :
                 Memory.promise (Local.promises local) memory locw (f_from' w) (f_to' w)
                                (Message.full valw (Some rel'))
                                promises_add memory_add Memory.op_kind_add ⟫ /\

             ⟪ MEM_PROMISE2 :
                 Memory.promise promises_rel memory_add locw (f_from' wnext) (f_to' wnext)
                                Message.reserve
                                promises_add2 memory' Memory.op_kind_add ⟫ /\

             ⟪ OLD_PROM_IN_NEW_PROM : Memory.le (Local.promises local) promises_add2 ⟫ /\
             ⟪ NEW_PROM_IN_MEM      : Memory.le promises_add2 memory' ⟫ /\

             let tview' := if is_rel lab w
                           then TView.write_tview
                                  (Local.tview local) sc_view locw
                                  (f_to' w) (Event_imm_promise.wmod ordw)
                           else (Local.tview local) in
             let local' := Local.mk tview' promises_add2 in
             let threads' :=
                 IdentMap.add (tid w)
                              (langst, local')
                              (Configuration.threads PC) in

             ⟪ THREAD : forall e (ACT : E e) (NINIT : ~ is_init e),
                 exists langst, IdentMap.find (tid e) threads' = Some langst ⟫ /\

             ⟪ SC_REQ : smode = sim_normal -> 
                        forall (l : Loc.t),
                          max_value
                            f_to' (S_tm G l covered') (LocFun.find l sc_view) ⟫ /\
             ⟪ CLOSED_SC : Memory.closed_timemap sc_view memory' ⟫ /\

             ⟪ PROM_IN_MEM :
                 forall thread' langst local
                        (TID : IdentMap.find thread' threads' = Some (langst, local)),
                   Memory.le (Local.promises local) memory' ⟫ /\

             ⟪ SIM_PROM     : sim_prom G sc T' f_to' f_from' (tid w) promises_add2  ⟫ /\
             ⟪ SIM_RES_PROM : sim_res_prom G T' S' f_to' f_from' (tid w) promises_add2  ⟫ /\

             ⟪ PROM_DISJOINT :
                 forall thread' langst' local'
                        (TNEQ : tid w <> thread')
                        (TID' : IdentMap.find thread' threads' =
                                Some (langst', local')),
                 forall loc to,
                   Memory.get loc to promises_add2 = None \/
                   Memory.get loc to (Local.promises local') = None ⟫ /\

             ⟪ SIM_MEM     : sim_mem G sc T' f_to' f_from' (tid w) local' memory' ⟫ /\
             ⟪ SIM_RES_MEM : sim_res_mem G T' S' f_to' f_from' (tid w) local' memory' ⟫ /\
             ⟪ NOWLOC : Rel w -> Memory.nonsynch_loc locw (Local.promises local') ⟫
     ⟫).
Proof using All.
  assert (tc_coherent G sc T) as TCCOH by apply ETCCOH.
  assert (complete G) as COMPL by apply IMMCON.
  assert (sc_per_loc G) as SPL by (apply coherence_sc_per_loc; apply IMMCON).
 
  assert (NSW : ~ S w).
  { intros HH. apply NWEX. apply ETCCOH. by split. }

  assert (S ⊆₁ E ∩₁ W) as SEW.
  { apply set_subset_inter_r. split; [by apply ETCCOH|].
    apply (reservedW WF ETCCOH). }
  assert (E w /\ W w) as [EW WW] by (by apply ISSUABLE).
  assert (~ covered T w) as NCOVB.
  { intros AA. apply NISSB. eapply w_covered_issued; eauto. by split. }
  assert (~ is_init w) as WNINIT.
  { intros HH. apply NCOVB. eapply init_covered; eauto. by split. }

  forward (eapply dom_sb_S_rfrmw_single_props with (w:=w) (wnext:=wnext)); eauto.
  intros HH. desc.
  assert (w <> wnext) as WNEXTNEQ.
  { intros HH. subst. eapply (co_irr WF); eauto. }

  subst.
  edestruct exists_time_interval_for_issue_next as [p_rel [PREL HH]]; eauto.
  red in HH. desc. exists p_rel. splits; eauto.
  exists f_to', f_from'. splits; eauto.
  exists promises_add, memory_add, promises_rel.
  exists promises', memory'.

  assert (Time.lt (f_to' w) (f_to' wnext)) as FLT.
  { eapply f_to_co_mon; eauto; basic_solver. }

  set (rel'' :=
        if is_rel lab w
        then (TView.cur (Local.tview local))
        else (TView.rel (Local.tview local) locw)).
  set (rel' := (View.join (View.join rel'' (View.unwrap p_rel))
                          (View.singleton_ur locw (f_to' w)))).

  set (S':=S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G (mkETC T S) rfi (eq w)).
  assert (S ⊆₁ S') as SINS by (unfold S'; eauto with hahn).
  assert (S' ⊆₁ E ∩₁ W) as SEW'.
  { subst S'. rewrite SEW at 1. unionL; eauto with hahn.
    { unfolder. ins. desf. }
    intros x HH.
    assert (x = wnext); subst.
    2: by split.
    eapply dom_sb_S_rfrmwf; eauto. }
  assert (S' w) as SW'.
  { red. basic_solver. }
  assert (S' wnext) as SWNEXT'.
  { red. basic_solver. }

  assert (Memory.le promises_add memory_add) as PP'.
  { eapply memory_le_add2; eauto. }
  assert (Memory.le promises' memory') as PP.
  { eapply memory_le_add2. 2,3: by eauto.
    destruct (Rel w); subst; auto.
    etransitivity; [|by apply PP'].
    eapply memory_remove_le; eauto. }

  foobar. use lemmas from IssueInterval.
  (* assert (forall thread' langst' local' (TNEQ : tid w <> thread') *)
  (*                (TID' : IdentMap.find thread' (Configuration.threads PC) = *)
  (*                        Some (langst', local')), *)
  (*            Memory.get locw (f_to' w) (Local.promises local') = None) as NINTER. *)
  (* { ins. *)
  (*   destruct (Memory.get locw (f_to' w) (Local.promises local')) eqn:HH; auto. *)
  (*   exfalso. destruct p as [from]. *)
  (*   eapply PROM_IN_MEM in HH; eauto. *)
  (*   set (AA := HH). apply Memory.get_ts in AA. *)
  (*   destruct AA as [|AA]; desc; eauto. *)
  (*   apply DISJOINT in HH. *)
  (*   apply HH with (x:=f_to' w); constructor; simpls; try reflexivity. *)
  (*   apply FCOH0; auto. } *)

  foobar. use lemmas from IssueInterval.
  (* assert (forall thread' langst' local' (TNEQ : tid w <> thread') *)
  (*                (TID' : IdentMap.find thread' (Configuration.threads PC) = *)
  (*                        Some (langst', local')), *)
  (*            Memory.get locw (f_to' wnext) (Local.promises local') = None) as NINTER'. *)
  (* { ins. *)
  (*   destruct (Memory.get locw (f_to' wnext) (Local.promises local')) eqn:HH; auto. *)
  (*   exfalso. destruct p as [from]. *)
  (*   eapply PROM_IN_MEM in HH; eauto. *)
  (*   set (AA := HH). apply Memory.get_ts in AA. *)
  (*   destruct AA as [|AA]; desc; eauto. *)
  (*   apply DISJOINT' in HH. *)
  (*   apply HH with (x:=f_to' wnext); constructor; simpls; try reflexivity. *)
  (*   apply FCOH0; auto. } *)

  assert (forall tmap (MCLOS : Memory.closed_timemap tmap (Configuration.memory PC)),
             Memory.closed_timemap tmap memory') as MADDCLOS.
  { ins. repeat (eapply Memory.add_closed_timemap; eauto). }
  
  (* assert (Memory.le promises'' promises') as LEPADD. *)
  (* { destruct (Rel w) eqn:RELB; subst; [|reflexivity]. *)
  (*   eapply memory_remove_le; eauto. } *)

  (* assert (Memory.le promises'' memory') as NEW_PROM_IN_MEM. *)
  (* { etransitivity; eauto. } *)

  (* assert (forall l to from msg  *)
  (*                (NEQ : l <> locw \/ to <> f_to w), *)
  (*            Memory.get l to promises_cancel = Some (from, msg) <-> *)
  (*            Memory.get l to (Local.promises local) = Some (from, msg)) *)
  (*   as NOTNEWC. *)
  (* { ins. erewrite Memory.remove_o; eauto. *)
  (*   rewrite loc_ts_eq_dec_neq; auto. } *)

  assert (forall l to from msg
                 (NEQ  : l <> locw \/ to <> f_to' w)
                 (NEQ' : l <> locw \/ to <> f_to' wnext),
             Memory.get l to memory' = Some (from, msg) <->
             Memory.get l to (Configuration.memory PC) = Some (from, msg))
    as NOTNEWM.
  { ins. by repeat (erewrite Memory.add_o; eauto; rewrite loc_ts_eq_dec_neq; auto). }

  assert (forall l to from msg
                 (NEQ  : l <> locw \/ to <> f_to' w)
                 (NEQ' : l <> locw \/ to <> f_to' wnext),
             Memory.get l to promises_rel = Some (from, msg) <->
             Memory.get l to (Local.promises local) = Some (from, msg))
    as NOTNEWR.
  { ins.
    destruct (Rel w); subst.
    erewrite Memory.remove_o; eauto; rewrite loc_ts_eq_dec_neq; auto.
    all: by erewrite Memory.add_o; eauto; rewrite loc_ts_eq_dec_neq; auto. }

  assert (forall l to from msg
                 (NEQ  : l <> locw \/ to <> f_to' w)
                 (NEQ' : l <> locw \/ to <> f_to' wnext),
             Memory.get l to promises' = Some (from, msg) <->
             Memory.get l to (Local.promises local) = Some (from, msg))
    as NOTNEWA.
  { ins.
    erewrite Memory.add_o; eauto; rewrite loc_ts_eq_dec_neq; auto. }

  assert (~ Rel w ->
          Memory.get locw (f_to' w) promises' =
          Some (f_from' w, Message.full valw (Some rel')))
    as INP''.
  { ins. destruct (Rel w); subst; [by desf|].
    erewrite Memory.add_o; eauto. rewrite loc_ts_eq_dec_neq; eauto.
    erewrite Memory.add_o; eauto. by rewrite loc_ts_eq_dec_eq. }

  assert (RESGET' :
            Memory.get locw (f_to' wnext) promises' =
            Some (f_from' wnext, Message.reserve)).
  { by erewrite Memory.add_o; eauto; rewrite loc_ts_eq_dec_eq. }

  (* assert (RESGET : *)
  (*           Memory.get locw (f_to' wnext) promises'' = *)
  (*           Some (f_from' wnext, Message.reserve)). *)
  (* { destruct (Rel w) eqn:RELB; subst. *)
  (*   erewrite Memory.remove_o; eauto. rewrite loc_ts_eq_dec_neq; eauto. *)
  (*   all: by erewrite Memory.add_o; eauto; rewrite loc_ts_eq_dec_eq. } *)

  assert (PROMGET :
            Memory.get locw (f_to' w) promises' = None \/
            exists rel,
              Memory.get locw (f_to' w) promises' =
              Some (f_from' w, Message.full valw rel)).
  { erewrite Memory.add_o; eauto. rewrite loc_ts_eq_dec_neq; eauto.
    destruct (Rel w) eqn:RELB; subst.
    { erewrite Memory.remove_o; eauto. rewrite loc_ts_eq_dec_eq; eauto. }
    erewrite Memory.add_o; eauto. rewrite loc_ts_eq_dec_eq; eauto. }

  assert (Memory.le (Local.promises local) promises_add) as OLD_PROM_IN_PROM_ADD.
  { eapply memory_add_le; eauto. }

  assert (Memory.le (Local.promises local) promises') as OLD_PROM_IN_PROM_REL.
  { etransitivity; [|by eapply memory_add_le; eauto].
    destruct (Rel w); subst; auto.
    red. ins. erewrite Memory.remove_o; eauto.
    destruct (loc_ts_eq_dec (loc, to) (locw, f_to' w)) as [|NN].
    2: { rewrite loc_ts_eq_dec_neq; auto. }
    desc. simpls. subst. exfalso.
    apply Memory.add_get0 in PADD.
    clear -PADD LHS. desc. rewrite PADD in LHS. inv LHS. }

  splits; eauto.
  1,2: econstructor; eauto; ins.
  { inv MSG. clear MSG.
    set (AA:=GET). apply DISJOINT' in AA.
    rewrite FWWNEXTEQ in AA.
    set (BB:=GET). apply Memory.get_ts in BB.
    destruct BB as [|BB]; desc; eauto.
    destruct (TimeFacts.le_lt_dec (f_to' wnext) to').
    { eapply AA with (x:=f_to' wnext); constructor; simpls; auto. reflexivity. }
    eapply AA with (x:=to'); constructor; simpls; auto; try reflexivity.
    apply Time.le_lteq. eauto. }
  { rewrite FWWNEXTEQ.
    erewrite Memory.add_o; eauto. rewrite loc_ts_eq_dec_eq. eauto. }
  { ins.
    destruct (Ident.eq_dec (tid e) (tid w)) as [EQ|NEQ].
    { rewrite EQ. rewrite IdentMap.gss.
      eexists. eauto. }
    rewrite IdentMap.gso; auto. }
  { intros QQ l.
    assert (max_value f_to' (S_tm G l (covered T)) (LocFun.find l (Configuration.sc PC))) as BB.
    { eapply sc_view_f_issued; eauto. }
    destruct (Rel w); auto.
    eapply max_value_same_set.
    { apply BB. }
    eapply s_tm_n_f_steps.
    { apply TCCOH. }
    { clear. basic_solver. }
    intros a [HB|HB] HH AA.
    { eauto. }
    subst. clear -WW AA. type_solver. }
  { ins.
    destruct (Ident.eq_dec thread' (tid w)) as [EQ|NEQ].
    { subst. rewrite IdentMap.gss in TID0.
      inv TID0; simpls; clear TID0. }
    red; ins; rewrite IdentMap.gso in TID0; auto.
    erewrite Memory.add_o; eauto.
    destruct (loc_ts_eq_dec (loc, to) (locw, f_to' wnext)) as [[A B]|LL'].
    { simpls; rewrite A in *; rewrite B in *; subst.
      exfalso. erewrite NINTER' in LHS; eauto. inv LHS. }
    rewrite (loc_ts_eq_dec_neq LL').
    erewrite Memory.add_o; eauto.
    destruct (loc_ts_eq_dec (loc, to) (locw, f_to' w)) as [[A B]|LL].
    { simpls; rewrite A in *; rewrite B in *; subst.
      exfalso. erewrite NINTER in LHS; eauto. inv LHS. }
    rewrite (loc_ts_eq_dec_neq LL).
    eapply PROM_IN_MEM in LHS; eauto. }
  { simpls. red. ins.
    destruct (loc_ts_eq_dec (l, to) (locw, f_to' wnext)) as [[A' B']|LL'].
    { simpls; rewrite A' in *; rewrite B' in *.
      exfalso. rewrite RESGET' in PROM. inv PROM. }
    erewrite Memory.add_o in PROM; eauto. rewrite (loc_ts_eq_dec_neq LL') in PROM.
    destruct (loc_ts_eq_dec (l, to) (locw, f_to' w)) as [[A' B']|LL].
    { simpls; rewrite A' in *; rewrite B' in *.
      destruct (Rel w) eqn:RELB; subst.
      { erewrite Memory.remove_o in PROM; eauto.
        rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in PROM. inv PROM. }
      erewrite Memory.add_o in PROM; eauto.
      rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in PROM.
      inv PROM. exists w. splits; eauto. by right. }
    eapply NOTNEWR in PROM; eauto.
    edestruct SIM_PROM as [b H]; eauto; desc.
    exists b; splits; auto.
    { by left. }
    { assert (W b) as WB by (eapply issuedW; eauto).
      destruct (Rel w) eqn:RELB; auto.
      intros [HH|HH]; desf. }
    { by rewrite ISSEQ_FROM. }
    { by rewrite ISSEQ_TO. }
    eapply sim_mem_helper_f_issued with (f_to:=f_to); eauto. }
  { simpls. red. ins.
    destruct (loc_ts_eq_dec (l, to) (locw, f_to' wnext)) as [[A' B']|LL'].
    { simpls; rewrite A' in *; rewrite B' in *.
      rewrite RESGET' in RES. inv RES.
      exists wnext. splits; eauto.
      intros [HH|HH]; subst; eauto. }
    erewrite Memory.add_o in RES; eauto. rewrite (loc_ts_eq_dec_neq LL') in RES.
    destruct (loc_ts_eq_dec (l, to) (locw, f_to' w)) as [[A' B']|LL].
    { simpls; rewrite A' in *; rewrite B' in *.
      destruct (Rel w) eqn:RELB; subst.
      erewrite Memory.remove_o in RES; eauto.
      2: erewrite Memory.add_o in RES; eauto.
      all: rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in RES; inv RES. }
    apply NOTNEWR in RES; auto.
    edestruct SIM_RES_PROM as [b H]; eauto; desc.
    exists b. splits; auto.
    { intros [A|A]; desf. }
    { rewrite REQ_FROM; auto. }
    rewrite REQ_TO; auto. }
  { ins.
    rewrite IdentMap.gso in TID'; auto.
    destruct (loc_ts_eq_dec (loc, to) (locw, (f_to' w))) as [EQ|NEQ]; simpls.
    { desc. subst. right.
      destruct (Memory.get locw (f_to' w) (Local.promises local')) eqn: HH; auto.
      exfalso.
      erewrite NINTER in HH; eauto. inv HH. }
    destruct (loc_ts_eq_dec (loc, to) (locw, (f_to' wnext))) as [EQ|NEQ']; simpls.
    { desc. subst. right.
      destruct (Memory.get locw (f_to' wnext) (Local.promises local')) eqn: HH; auto.
      exfalso.
      erewrite NINTER' in HH; eauto. inv HH. }
    edestruct (PROM_DISJOINT TNEQ TID') as [HH|HH]; eauto.
    left.
    destruct (Memory.get loc to promises') eqn:BB; auto.
    destruct p. eapply NOTNEWA in BB; eauto. desf. }
  { red. ins.
    destruct ISSB as [ISSB|]; subst.
    { edestruct SIM_MEM as [rel_opt HH]; eauto. simpls. desc.
      exists rel_opt. unnw.
      destruct (loc_ts_eq_dec (l, f_to' b) (locw, (f_to' w))) as [EQ|NEQ]; simpls; desc; subst.
      { exfalso.
        assert (b = w); [|by desf].
        eapply f_to_eq; try apply FCOH0; eauto.
        { red. by rewrite LOC. }
        do 2 left. by apply (etc_I_in_S ETCCOH). }
      destruct (loc_ts_eq_dec (l, f_to' b) (locw, (f_to' wnext))) as [EQ|NEQ'];
        simpls; desc; subst.
      { exfalso.
        assert (b = wnext); [|by desf].
        eapply f_to_eq; try apply FCOH0; eauto.
        { red. by rewrite WNEXTLOC. }
        do 2 left. by apply (etc_I_in_S ETCCOH). }
      erewrite Memory.add_o with (mem2:=memory'); eauto.
      erewrite Memory.add_o with (mem2:=memory_add); eauto.
      rewrite !loc_ts_eq_dec_neq; auto.
      splits; eauto.
      { rewrite ISSEQ_TO; auto. rewrite ISSEQ_FROM; auto. }
      { rewrite ISSEQ_FROM; auto. eapply sim_mem_helper_f_issued; eauto. }
      intros AA BB.
      assert (~ covered T b) as NCOVBB.
      { intros HH. apply BB. generalize HH. clear. basic_solver. }
      specialize (HH1 AA NCOVBB).
      desc. splits; auto.
      { apply NOTNEWA; auto.
        rewrite ISSEQ_TO; auto. rewrite ISSEQ_FROM; auto. }
      eexists. splits; eauto.
      2: { destruct HH2 as [[CC DD]|CC]; [left|right].
           { split; eauto. intros [y HH]. destruct_seq_l HH as OO.
             destruct OO as [OO|]; subst.
             { apply CC. exists y. apply seq_eqv_l. by split. }
             apply NISSB. eapply rfrmw_I_in_I; eauto. exists b.
             apply seqA. apply seq_eqv_r. by split. }
           desc. exists p. splits; auto.
           { by left. }
           eexists. splits; eauto.
           destruct (classic (l = locw)) as [|LNEQ]; subst; auto.
           2: { apply NOTNEWM.
                1,2: by left.
                rewrite ISSEQ_TO; auto. rewrite ISSEQ_FROM; auto. }
           assert (S' p) as SPP.
           { do 2 left. by apply (etc_I_in_S ETCCOH). }
           assert (loc lab p = Some locw) as PLOC.
           { rewrite <- LOC0. by apply (wf_rfrmwl WF). }
           apply NOTNEWM.
           3: { rewrite ISSEQ_TO; auto. rewrite ISSEQ_FROM; auto. }
           all: right; intros HH.
           all: eapply f_to_eq in HH; eauto; subst; auto.
           { red. by rewrite LOC. }
           red. by rewrite WNEXTLOC. }
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
      2: { apply NCOVBB. apply ISSUABLE. exists w. apply seq_eqv_r. split; auto.
           apply sb_to_w_rel_in_fwbob. apply seq_eqv_r. split; auto. by split. }
      assert (issuable G sc T b) as IB by (eapply issued_in_issuable; eauto).
      apply NCOVB. apply IB. exists b. apply seq_eqv_r. split; auto.
      apply sb_from_w_rel_in_fwbob; auto. apply seq_eqv_lr. splits; auto.
      all: split; auto. red. by rewrite LOC. }
    assert (Some l = Some locw) as QQ.
    { by rewrite <- LOC0. }
    inv QQ.
    eexists. splits; eauto.
    { erewrite Memory.add_o; eauto; rewrite loc_ts_eq_dec_neq; eauto.
      erewrite Memory.add_o; eauto. rewrite loc_ts_eq_dec_eq; eauto. }
    { apply HELPER. }
    { apply RELWFEQ. }
    { eapply Memory.add_closed_timemap; eauto. }
    intros _ NT.
    clear PROMGET.
    destruct (Rel b); desf.
    { exfalso. apply NT. by right. }
    splits.
    { erewrite Memory.add_o; eauto; rewrite loc_ts_eq_dec_neq; eauto.
      erewrite Memory.add_o; eauto. rewrite loc_ts_eq_dec_eq; eauto. }
    exists p_rel. splits; eauto. left.
    cdes PREL. destruct PREL1; desc.
    2: { exfalso. apply NWEX. red. generalize INRMW. clear. basic_solver. }
    split; auto.
    intros [a HH].
    apply seq_eqv_l in HH. destruct HH as [[HH|] RFRMW]; subst; eauto.
    { apply NINRMW. generalize HH RFRMW. clear. basic_solver 10. }
    eapply wf_rfrmw_irr; eauto. }
  { red. ins.
    assert (b <> w /\ ~ issued T b) as [BNEQ NISSBB].
    { generalize NISSB0. clear. basic_solver. }
    destruct RESB as [[SB|]|HH]; subst.
    2: by desf.
    { unnw.
      erewrite Memory.add_o with (mem2:=memory'); eauto.
      destruct (loc_ts_eq_dec (l, f_to' b) (locw, (f_to' w))) as [PEQ'|PNEQ];
        simpls; desc; subst.
      { exfalso. apply BNEQ.
        eapply f_to_eq with (f_to:=f_to'); eauto. red.
          by rewrite LOC. }
      destruct (loc_ts_eq_dec (l, f_to' b) (locw, (f_to' wnext))) as [PEQ'|PNEQ'];
        simpls; desc; subst.
      { exfalso. eapply f_to_eq with (I:=S') in PEQ'0; subst; eauto.
          by red; rewrite WNEXTLOC. }
      edestruct SIM_RES_MEM with (b:=b); eauto; unnw.
      rewrite (loc_ts_eq_dec_neq PNEQ').
      erewrite Memory.add_o with (mem2:=memory_add); eauto.
      rewrite (loc_ts_eq_dec_neq PNEQ).
      rewrite REQ_TO; auto. rewrite REQ_FROM; auto. }
    assert (b = wnext); subst.
    { eapply dom_sb_S_rfrmw_single; eauto. }
    assert (Some l = Some locw) as LL.
    { by rewrite <- LOC0. }
    inv LL.
    splits; ins.
    erewrite Memory.add_o; eauto. by rewrite loc_ts_eq_dec_eq. }
  intros WREL. red. ins. destruct msg; auto.
  rewrite WREL in PEQ.
  exfalso.
  erewrite Memory.add_o in GET; eauto.
  destruct (loc_ts_eq_dec (locw, t) (locw, f_to' wnext)) as [AA|NEQ']; simpls.
  { desc; subst.
    rewrite (loc_ts_eq_dec_eq locw (f_to' wnext)) in GET. inv GET. }
  rewrite (loc_ts_eq_dec_neq NEQ') in GET.
  destruct (loc_ts_eq_dec (locw, t) (locw, f_to' w)) as [AA|NEQ]; simpls.
  { desc; subst.
    erewrite Memory.remove_o in GET; eauto.
    rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in GET. inv GET. }
  apply NOTNEWR in GET; auto.
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
  apply NCOV. apply ISSUABLE. exists w. apply seq_eqv_r. split; auto.
  apply sb_to_w_rel_in_fwbob. apply seq_eqv_r. 
  do 2 (split; auto).
Qed.

End IssueStepHelper.
