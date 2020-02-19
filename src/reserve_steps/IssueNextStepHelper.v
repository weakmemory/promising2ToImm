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

Require Import ImmProperties.
Require Import TraversalConfig.
Require Import ViewRelHelpers.
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
    exists langst, IdentMap.find (tid e) PC.(Configuration.threads) = Some langst.

Variable smode : sim_mode.
Hypothesis SC_REQ :
  smode = sim_normal -> 
  forall (l : Loc.t),
    max_value f_to (S_tm G l (covered T)) (LocFun.find l PC.(Configuration.sc)).

Variable thread : thread_id.
Variable local : Local.t.
Hypothesis SIM_PROM     : sim_prom     G sc T   f_to f_from thread local.(Local.promises).
Hypothesis SIM_RES_PROM : sim_res_prom G    T S f_to f_from thread local.(Local.promises).

Hypothesis CLOSED_SC : Memory.closed_timemap PC.(Configuration.sc) PC.(Configuration.memory).

Hypothesis PROM_DISJOINT :
  forall thread' langst' local'
         (TNEQ : thread <> thread')
         (TID' : IdentMap.find thread' PC.(Configuration.threads) =
                 Some (langst', local')),
  forall loc to,
    Memory.get loc to local .(Local.promises) = None \/
    Memory.get loc to local'.(Local.promises) = None.

Hypothesis PROM_IN_MEM :
  forall thread' langst local
         (TID : IdentMap.find thread' PC.(Configuration.threads) =
                Some (langst, local)),
    Memory.le local.(Local.promises) PC.(Configuration.memory).

Hypothesis INHAB      : Memory.inhabited (Configuration.memory PC).
Hypothesis CLOSED_MEM : Memory.closed (Configuration.memory PC).
Hypothesis PLN_RLX_EQ : pln_rlx_eq local.(Local.tview).
Hypothesis MEM_CLOSE : memory_close local.(Local.tview) PC.(Configuration.memory).

Hypothesis RESERVED_TIME:
  reserved_time G T S f_to f_from smode PC.(Configuration.memory).

Hypothesis SIM_RES_MEM :
  sim_res_mem G T S f_to f_from thread local (Configuration.memory PC).

Hypothesis SIM_MEM : sim_mem G sc T f_to f_from thread local PC.(Configuration.memory).
Hypothesis SIM_TVIEW : sim_tview G sc (covered T) f_to local.(Local.tview) thread.
Hypothesis WEXRES : smode = sim_certification -> W_ex ⊆₁ S.

Lemma issue_step_helper_next w wnext valw locw ordw langst
      (TID : IdentMap.find (tid w) PC.(Configuration.threads) = Some (langst, local))
      (NWEX : ~ W_ex w)
      (NISSB : ~ issued T w)
      (ISSUABLE : issuable G sc T w)
      (NEXT : dom_sb_S_rfrmw G (mkETC T S) rfi (eq w) wnext)
      (LOC : loc lab w = Some locw)
      (VAL : val lab w = Some valw)
      (ORD : mod lab w = ordw)
      (WTID : thread = tid w) :
  let promises := local.(Local.promises) in
  let memory   := PC.(Configuration.memory) in
  let sc_view  := PC.(Configuration.sc) in
  let covered' := if Rel w then covered T ∪₁ eq w else covered T in
  let T'       := mkTC covered' (issued T ∪₁ eq w) in
  let S'       := S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G (mkETC T S) rfi (eq w) in
  exists p_rel,
    rfrmw_prev_rel G sc T f_to f_from PC.(Configuration.memory) w locw p_rel /\
    (⟪ FOR_ISSUE :
         exists f_to' f_from',
           let rel'' :=
               if is_rel lab w
               then (TView.cur (Local.tview local))
               else (TView.rel (Local.tview local) locw)
           in
           let rel' := (View.join (View.join rel'' p_rel.(View.unwrap))
                                  (View.singleton_ur locw (f_to' w))) in
           ⟪ RELWFEQ : View.pln rel' = View.rlx rel' ⟫ /\
           ⟪ REL_VIEW_LT : Time.lt (View.rlx rel'' locw) (f_to' w) ⟫ /\
           ⟪ REL_VIEW_LE : Time.le (View.rlx rel'  locw) (f_to' w) ⟫ /\

           ⟪ REQ_TO : forall e (SE : S e), f_to' e = f_to e ⟫ /\
           ⟪ REQ_FROM : forall e (SE : S e), f_from' e = f_from e ⟫ /\
           ⟪ ISSEQ_TO   : forall e (ISS: issued T e), f_to' e = f_to e ⟫ /\
           ⟪ ISSEQ_FROM : forall e (ISS: issued T e), f_from' e = f_from e ⟫ /\
           ⟪ FTOWNBOT : f_to' w <> Time.bot ⟫ /\

           exists promises_add memory_add promises_add2 memory',
             ⟪ PADD :
                 Memory.add local.(Local.promises) locw (f_from' w) (f_to' w)
                            (Message.full valw (Some rel')) promises_add ⟫ /\
             ⟪ MADD :
                 Memory.add memory locw (f_from' w) (f_to' w)
                            (Message.full valw (Some rel')) memory_add ⟫ /\

             ⟪ PADD2 :
                 Memory.add promises_add locw (f_from' wnext) (f_to' wnext)
                            Message.reserve promises_add2 ⟫ /\
             ⟪ MADD2 :
                 Memory.add memory_add locw (f_from' wnext) (f_to' wnext)
                            Message.reserve memory' ⟫ /\


             ⟪ INHAB : Memory.inhabited memory' ⟫ /\
             ⟪ RELMCLOS : Memory.closed_timemap (View.rlx rel') memory' ⟫ /\
             ⟪ RELVCLOS : Memory.closed_view rel' memory' ⟫ /\

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
                 reserved_time G T' S' f_to' f_from' smode memory' ⟫ /\

             ⟪ MEM_PROMISE :
                 Memory.promise (Local.promises local) memory locw (f_from' w) (f_to' w)
                                (Message.full valw (Some rel'))
                                promises_add memory_add Memory.op_kind_add ⟫ /\

             ⟪ MEM_PROMISE2 :
                 Memory.promise promises_add memory_add locw (f_from' wnext) (f_to' wnext)
                                Message.reserve
                                promises_add2 memory' Memory.op_kind_add ⟫ /\

             exists promises',
               ⟪ PEQ :
                   if Rel w
                   then Memory.remove promises_add2 locw (f_from' w) (f_to' w)
                                      (Message.full valw (Some rel')) promises'
                   else promises' = promises_add2 ⟫ /\

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

               ⟪ SIM_PROM     : sim_prom G sc T' f_to' f_from' (tid w) promises'  ⟫ /\
               ⟪ SIM_RES_PROM : sim_res_prom G T' S' f_to' f_from' (tid w) promises'  ⟫ /\

               ⟪ PROM_DISJOINT :
                   forall thread' langst' local'
                          (TNEQ : tid w <> thread')
                          (TID' : IdentMap.find thread' threads' =
                                  Some (langst', local')),
                   forall loc to,
                     Memory.get loc to promises' = None \/
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
  { intros HH. subst. eapply WF.(co_irr); eauto. }

  subst.
  edestruct exists_time_interval_for_issue_next as [p_rel [PREL HH]]; eauto.
  red in HH. desc. exists p_rel. splits; eauto.
  exists f_to', f_from'. splits; eauto.
  exists promises_add, memory_add.
  exists promises', memory'.
  splits; eauto.
  1,2: constructor; eauto; ins.
  { inv MSG. clear MSG. admit. }
  { admit. }

  set (rel'' :=
        if is_rel lab w
        then (TView.cur (Local.tview local))
        else (TView.rel (Local.tview local) locw)).
  set (rel' := (View.join (View.join rel'' p_rel.(View.unwrap))
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

  assert (f_to' w <> f_to' wnext) as FTONEXTNEQ.
  { intros HH. eapply f_to_eq with (I:=S') in HH; eauto.
    { red. by rewrite LOC. }
    all: red; basic_solver. }

  assert (exists promises'',
             ⟪ PEQ :
                 if Rel w
                 then Memory.remove promises' locw (f_from' w) (f_to' w)
                                    (Message.full valw (Some rel')) promises''
                 else promises'' = promises' ⟫).
  { destruct (is_rel lab w) eqn:REL; eauto.
    edestruct Memory.remove_exists as [promises''].
    2: { exists promises''. eauto. }
    erewrite Memory.add_o; eauto.
    rewrite loc_ts_eq_dec_neq; auto.
    erewrite Memory.add_o; eauto.
    rewrite loc_ts_eq_dec_eq; auto. }
  desc.
  exists promises''. simpls.
  
  assert (Memory.le promises' memory') as PP.
  { eapply memory_le_add2. 2,3: by eauto.
    eapply memory_le_add2; eauto. }

  assert (forall thread' langst' local' (TNEQ : tid w <> thread')
                 (TID' : IdentMap.find thread' (Configuration.threads PC) =
                         Some (langst', local')),
             Memory.get locw (f_to' w) (Local.promises local') = None) as NINTER.
  (* TODO: Move to IssueInterval.v? *)
  { ins.
    destruct (Memory.get locw (f_to' w) (Local.promises local')) eqn:HH; auto.
    exfalso. destruct p as [from].
    eapply PROM_IN_MEM in HH; eauto.
    set (AA := HH). apply Memory.get_ts in AA.
    destruct AA as [|AA]; desc; eauto.
    apply DISJOINT in HH.
    apply HH with (x:=f_to' w); constructor; simpls; try reflexivity.
    apply FCOH0; auto. }

  assert (forall thread' langst' local' (TNEQ : tid w <> thread')
                 (TID' : IdentMap.find thread' (Configuration.threads PC) =
                         Some (langst', local')),
             Memory.get locw (f_to' wnext) (Local.promises local') = None) as NINTER'.
  (* TODO: Move to IssueInterval.v? *)
  { ins.
    destruct (Memory.get locw (f_to' wnext) (Local.promises local')) eqn:HH; auto.
    exfalso. destruct p as [from].
    eapply PROM_IN_MEM in HH; eauto.
    set (AA := HH). apply Memory.get_ts in AA.
    destruct AA as [|AA]; desc; eauto.
    apply DISJOINT' in HH.
    apply HH with (x:=f_to' wnext); constructor; simpls; try reflexivity.
    apply FCOH0; auto. }

  assert (forall tmap (MCLOS : Memory.closed_timemap tmap PC.(Configuration.memory)),
             Memory.closed_timemap tmap memory') as MADDCLOS.
  { ins. repeat (eapply Memory.add_closed_timemap; eauto). }
  
  assert (Memory.le promises'' promises') as LEPADD.
  { destruct (Rel w) eqn:RELB; subst; [|reflexivity].
    eapply memory_remove_le; eauto. }

  assert (Memory.le promises'' memory') as NEW_PROM_IN_MEM.
  { etransitivity; eauto. }

  (* assert (forall l to from msg  *)
  (*                (NEQ : l <> locw \/ to <> f_to w), *)
  (*            Memory.get l to promises_cancel = Some (from, msg) <-> *)
  (*            Memory.get l to local.(Local.promises) = Some (from, msg)) *)
  (*   as NOTNEWC. *)
  (* { ins. erewrite Memory.remove_o; eauto. *)
  (*   rewrite loc_ts_eq_dec_neq; auto. } *)

  assert (forall l to from msg
                 (NEQ  : l <> locw \/ to <> f_to' w)
                 (NEQ' : l <> locw \/ to <> f_to' wnext),
             Memory.get l to memory' = Some (from, msg) <->
             Memory.get l to PC.(Configuration.memory) = Some (from, msg))
    as NOTNEWM.
  { ins. repeat (erewrite Memory.add_o; eauto; rewrite loc_ts_eq_dec_neq; auto). }

  assert (forall l to from msg
                 (NEQ  : l <> locw \/ to <> f_to' w)
                 (NEQ' : l <> locw \/ to <> f_to' wnext),
             Memory.get l to promises' = Some (from, msg) <->
             Memory.get l to local.(Local.promises) = Some (from, msg))
    as NOTNEWA.
  { ins. repeat (erewrite Memory.add_o; eauto; rewrite loc_ts_eq_dec_neq; auto). }

  assert (forall l to from msg
                 (NEQ  : l <> locw \/ to <> f_to' w)
                 (NEQ' : l <> locw \/ to <> f_to' wnext),
             Memory.get l to promises'' = Some (from, msg) <->
             Memory.get l to local.(Local.promises) = Some (from, msg))
    as NOTNEWP.
  { ins. destruct (Rel w); subst; auto.
    erewrite Memory.remove_o; eauto. rewrite loc_ts_eq_dec_neq; auto. }

  assert (~ Rel w ->
          Memory.get locw (f_to' w) promises'' =
          Some (f_from' w, Message.full valw (Some rel')))
    as INP''.
  { ins. destruct (Rel w); subst; [by desf|].
    erewrite Memory.add_o; eauto. rewrite loc_ts_eq_dec_neq; eauto.
    erewrite Memory.add_o; eauto. by rewrite loc_ts_eq_dec_eq. }

  assert (RESGET' :
            Memory.get locw (f_to' wnext) promises' =
            Some (f_from' wnext, Message.reserve)).
  { by erewrite Memory.add_o; eauto; rewrite loc_ts_eq_dec_eq. }

  assert (RESGET :
            Memory.get locw (f_to' wnext) promises'' =
            Some (f_from' wnext, Message.reserve)).
  { destruct (Rel w) eqn:RELB; subst.
    erewrite Memory.remove_o; eauto. rewrite loc_ts_eq_dec_neq; eauto.
    all: by erewrite Memory.add_o; eauto; rewrite loc_ts_eq_dec_eq. }

  assert (PROMGET :
            Memory.get locw (f_to' w) promises'' = None \/
            exists rel,
              Memory.get locw (f_to' w) promises'' =
              Some (f_from' w, Message.full valw rel)).
  { destruct (Rel w) eqn:RELB; subst.
    erewrite Memory.remove_o; eauto. rewrite loc_ts_eq_dec_eq; eauto.
    erewrite Memory.add_o; eauto. rewrite loc_ts_eq_dec_neq; eauto.
    erewrite Memory.add_o; eauto. rewrite loc_ts_eq_dec_eq; eauto. }

  splits; eauto.
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
    destruct (loc_ts_eq_dec (l, to) (locw, f_to' w)) as [[A' B']|LL].
    { simpls; rewrite A' in *; rewrite B' in *.
      destruct (Rel w) eqn:RELB; subst.
      { erewrite Memory.remove_o in PROM; eauto.
        rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in PROM. inv PROM. }
      erewrite Memory.add_o in PROM; eauto.
      rewrite loc_ts_eq_dec_neq in PROM; eauto.
      erewrite Memory.add_o in PROM; eauto.
      rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in PROM.
      inv PROM. exists w. splits; eauto. by right. }
    destruct (loc_ts_eq_dec (l, to) (locw, f_to' wnext)) as [[A' B']|LL'].
    { simpls; rewrite A' in *; rewrite B' in *.
      exfalso. rewrite RESGET in PROM. inv PROM. }
    eapply NOTNEWP in PROM; eauto.
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
    destruct (loc_ts_eq_dec (l, to) (locw, f_to' w)) as [[A' B']|LL].
    { simpls; rewrite A' in *; rewrite B' in *.
      exfalso. clear -PROMGET RES. desf. }
    destruct (loc_ts_eq_dec (l, to) (locw, f_to' wnext)) as [[A' B']|LL'].
    { simpls; rewrite A' in *; rewrite B' in *.
      rewrite RESGET in RES. inv RES.
      exists wnext. splits; eauto.
      intros [HH|HH]; subst; eauto. }
    apply NOTNEWP in RES; auto.
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
    destruct (Memory.get loc to promises'') eqn:BB; auto.
    destruct p. eapply NOTNEWP in BB; eauto. desf. }
  { red. ins.
    destruct ISSB as [ISSB|]; subst.
    { edestruct SIM_MEM as [rel_opt HH]; eauto. simpls. desc.
      exists rel_opt. unnw.
      destruct (loc_ts_eq_dec (l, f_to' b) (locw, (f_to' w))) as [EQ|NEQ]; simpls; desc; subst.
      { exfalso.
        assert (b = w); [|by desf].
        eapply f_to_eq; try apply FCOH0; eauto.
        { red. by rewrite LOC. }
        do 2 left. by apply ETCCOH.(etc_I_in_S). }
      destruct (loc_ts_eq_dec (l, f_to' b) (locw, (f_to' wnext))) as [EQ|NEQ'];
        simpls; desc; subst.
      { exfalso.
        assert (b = wnext); [|by desf].
        eapply f_to_eq; try apply FCOH0; eauto.
        { red. by rewrite WNEXTLOC. }
        do 2 left. by apply ETCCOH.(etc_I_in_S). }
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
      { apply NOTNEWP; auto.
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
           { do 2 left. by apply ETCCOH.(etc_I_in_S). }
           assert (loc lab p = Some locw) as PLOC.
           { rewrite <- LOC0. by apply WF.(wf_rfrmwl). }
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
    { apply RELMCLOS. }
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
      rewrite REQ_TO; auto. rewrite REQ_FROM; auto.
      splits; ins.
      apply NOTNEWP; auto; rewrite <- REQ_TO; auto. }
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
  erewrite Memory.remove_o in GET; eauto.
  destruct (loc_ts_eq_dec (locw, t) (locw, f_to' w)) as [AA|NEQ]; simpls.
  { desc; subst. rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in GET.
    inv GET. }
  destruct (loc_ts_eq_dec (locw, t) (locw, f_to' wnext)) as [AA|NEQ']; simpls.
  { desc; subst.
    rewrite @loc_ts_eq_dec_neq with (l:=locw) (l':=locw)
                                    (ts:=f_to' wnext) (ts':=f_to' w)
      in GET; eauto.
    rewrite RESGET' in GET. inv GET. }
  rewrite (loc_ts_eq_dec_neq NEQ) in GET.
  erewrite Memory.add_o in GET; eauto.
  rewrite (loc_ts_eq_dec_neq NEQ') in GET.
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
  apply NCOV. apply ISSUABLE. exists w. apply seq_eqv_r. split; auto.
  apply sb_to_w_rel_in_fwbob. apply seq_eqv_r. 
  do 2 (split; auto).
Admitted.

End IssueStepHelper.
