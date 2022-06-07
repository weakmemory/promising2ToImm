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
From imm Require Import FairExecution.

From imm Require Import TraversalOrder.
From imm Require Import TLSCoherency.
From imm Require Import IordCoherency.
From imm Require Import SimClosure. 
Require Import ViewRelHelpers.
Require Import SimulationRel.
Require Import SimState.
Require Import MemoryAux.
Require Import MaxValue.
Require Import ViewRel.
Require Import Event_imm_promise.
Require Import ExtTraversalConfig.
Require Import ExtTraversal.
Require Import FtoCoherent.
Require Import SimulationRelProperties.
Require Import ExistsReserveInterval.
Require Import TlsEventSets. 

Set Implicit Arguments.

Section ReserveStepHelper.

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
Hypothesis SIM_RES_PROM : sim_res_prom G    T f_to f_from thread (Local.promises local).

Hypothesis CLOSED_SC : Memory.closed_timemap (Configuration.sc PC) (Configuration.memory PC).

Hypothesis PROM_DISJOINT :
  forall thread' langst' local'
         (TNEQ : thread <> thread')
         (TID' : IdentMap.find thread' (Configuration.threads PC) =
                 Some (langst', local')),
  forall loc to,
    Memory.get loc to local .(Local.Local.promises) = None \/
    Memory.get loc to local'.(Local.Local.promises) = None.

Hypothesis PROM_IN_MEM :
  forall thread' langst local
         (TID : IdentMap.find thread' (Configuration.threads PC) =
                Some (langst, local)),
    Memory.le (Local.Local.promises local) (Configuration.memory PC).

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
Hypothesis RMWREX : dom_rel rmw ⊆₁ R_ex lab.

Lemma reserve_step_helper w locw langst
      (TID : IdentMap.find (tid w) (Configuration.threads PC) = Some (langst, local))
      (TSTEP : ext_itrav_step
                 G sc (mkTL ta_reserve w) T (T ∪₁ eq (mkTL ta_reserve w)))
      (LOC : loc lab w = Some locw)
      (WTID : thread = tid w)
      (FAIR: mem_fair G)
  :
  let memory := (Configuration.memory PC) in
  let sc_view := (Configuration.sc PC) in
  exists f_to' f_from' promises' memory',
    let local' := Local.mk (Local.tview local) promises' in
    let threads' :=
        IdentMap.add (tid w)
                     (langst, local')
                     (Configuration.threads PC) in
    ⟪ PADD :
        Memory.add (Local.promises local) locw (f_from' w) (f_to' w)
                                          Message.reserve promises' ⟫ /\
    ⟪ MADD :
        Memory.add memory locw (f_from' w) (f_to' w)
                   Message.reserve memory' ⟫ /\
    
    ⟪ REQ_TO   : forall e (SE: S e), f_to'   e = f_to   e ⟫ /\
    ⟪ REQ_FROM : forall e (SE: S e), f_from' e = f_from e ⟫ /\
    ⟪ FCOH : f_to_coherent G (S ∪₁ eq w) f_to' f_from' ⟫ /\
    ⟪ RESERVED_TIME :
        reserved_time G (T ∪₁ eq (mkTL ta_reserve w)) f_to' f_from' smode memory' ⟫ /\
    ⟪ THREAD : forall e (ACT : E e) (NINIT : ~ is_init e),
        exists langst, IdentMap.find (tid e) threads' = Some langst ⟫ /\

    ⟪ SC_REQ : smode = sim_normal -> 
               forall (l : Loc.t),
                 max_value f_to' (S_tm G l (covered T)) (LocFun.find l sc_view) ⟫ /\
    ⟪ CLOSED_SC : Memory.closed_timemap sc_view memory' ⟫ /\

    ⟪ MEM_PROMISE :
        Memory.promise (Local.promises local) memory locw (f_from' w) (f_to' w)
                       Message.reserve promises' memory' Memory.op_kind_add ⟫ /\
    ⟪ PROM_IN_MEM :
        forall thread' langst local
               (TID : IdentMap.find thread' threads' = Some (langst, local)),
          Memory.le (Local.Local.promises local) memory' ⟫ /\

    ⟪ SIM_PROM     : sim_prom     G sc T             f_to' f_from' (tid w) promises'  ⟫ /\
    ⟪ SIM_RES_PROM : sim_res_prom G    (T ∪₁ eq (mkTL ta_reserve w)) f_to' f_from' (tid w) promises'  ⟫ /\

    ⟪ PROM_DISJOINT :
        forall thread' langst' local'
               (TNEQ : tid w <> thread')
               (TID' : IdentMap.find thread' threads' =
                       Some (langst', local')),
        forall loc to,
          Memory.get loc to promises' = None \/
          Memory.get loc to local'.(Local.Local.promises) = None ⟫ /\

    ⟪ SIM_MEM     : sim_mem G sc T f_to' f_from' (tid w) local' memory' ⟫ /\
    ⟪ SIM_RES_MEM : sim_res_mem G (T ∪₁ eq (mkTL ta_reserve w)) f_to' f_from' (tid w) local' memory' ⟫.
Proof using All.

  subst.
  edestruct exists_time_interval_for_reserve as [f_to']; eauto.
  desc.
  
  assert (~ S w) as NSW.
  { eapply ext_itrav_step_reserve_nS; eauto. }

  assert (~ issued T w) as NISSB.
  { intros AA. apply NSW. eapply rcoh_I_in_S; eauto. }

  assert (forall e, issued T e -> f_to' e = f_to e) as ISSEQ_TO.
  { ins. apply REQ_TO. eapply rcoh_I_in_S; eauto. }
  assert (forall e, issued T e -> f_from' e = f_from e) as ISSEQ_FROM.
  { ins. apply REQ_FROM. eapply rcoh_I_in_S; eauto. }

  assert (W w) as WW.
  { eapply ext_itrav_step_reserveW; eauto. }

  assert (E w) as EW.
  { apply ext_itrav_stepE in TSTEP; eauto. }

  assert (forall l b (SB : S b) (BLOC : loc lab b = Some l),
             l <> locw \/ f_to b <> f_to' w) as SNEQ.
  { ins.
    arewrite (f_to b = f_to' b).
    { symmetry. by apply REQ_TO. }
    (* TODO: generalize to a lemma *)
    destruct (classic (l = locw)); [right|by left]; subst.
    intros HH.
    assert (b = w); desf.
    eapply f_to_eq with (I:=S ∪₁ eq w) (f_to:=f_to'); eauto.
    4: by right.
    3: by left.
    2: by red; rewrite BLOC; desf.
    apply set_subset_union_l. split.  
    { apply set_subset_inter_r; split.
      { apply RCOH. }
      eapply reservedW; eauto. }
    basic_solver. }

  assert (forall l b (ISSB : issued T b) (BLOC : loc lab b = Some l),
             l <> locw \/ f_to b <> f_to' w) as INEQ.
  { ins. apply SNEQ; auto. eapply rcoh_I_in_S; eauto. }

  assert (Memory.le (Configuration.memory PC) memory') as MM.
  { eapply memory_add_le; eauto. }

  assert (Memory.le promises' memory') as PP.
  { red; ins.
    erewrite Memory.add_o; eauto.
    erewrite Memory.add_o in LHS; [|by apply PADD].
    destruct (loc_ts_eq_dec (loc, to) (locw, f_to' w)) as [[A B]|LL].
    { simpls; rewrite A in *; rewrite B in *.
      rewrite (loc_ts_eq_dec_eq locw (f_to' w)).
        by rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in LHS. }
    rewrite (loc_ts_eq_dec_neq LL).
    rewrite (loc_ts_eq_dec_neq LL) in LHS.
    eapply PROM_IN_MEM; eauto. }

  eexists f_to', f_from', promises', memory'.
  splits; eauto; unfold threads'.
  { ins.
    destruct (Ident.eq_dec (tid e) (tid w)) as [EQ|NEQ].
    { rewrite EQ. rewrite IdentMap.gss.
      eexists. eauto. }
    rewrite IdentMap.gso; auto. }
  { ins. eapply sc_view_f_issued with (f_to:=f_to); eauto. }
  { eapply Memory.add_closed_timemap; eauto. }
  { apply Memory.promise_add; eauto; ins.
    assert (codom_rel (⦗issued T⦘ ⨾ rf ⨾ rmw) w) as [b HH].
    { eapply set_equiv_exp. 
      { arewrite (I ≡₁ issued (T ∪₁ eq (mkTL ta_reserve w))).
        { clear. simplify_tls_events. basic_solver. }
        reflexivity. }
      eapply rcoh_S_W_ex_rfrmw_I with (T:= T ∪₁ eq (mkTL ta_reserve w)).
      { apply TSTEP. }
      split; [clear; find_event_set|].
      eapply TSTEP. split; [clear; find_event_set|]; simpls.
      separate_set_event. }
    destruct_seq_l HH as AA.
    assert (W b) as WB.
    { eapply issuedW; eauto. }
    set (VB:=WB).
    eapply is_w_val in VB. desc.
    assert (loc lab b = Some locw) as BLOC.
    { rewrite <- LOC. by apply wf_rfrmwl. }
    set (BB:=AA).
    edestruct SIM_MEM; eauto. simpls. desc.
    do 3 eexists.
    arewrite (f_from' w = f_to b); eauto.
    arewrite (f_to b = f_to' b).
    { symmetry. by apply ISSEQ_TO. }
    symmetry.
    eapply FCOH0; eauto.
    2: by right.
    left. eapply rcoh_I_in_S; eauto. }
 { ins.
    destruct (Ident.eq_dec thread' (tid w)) as [EQ|NEQ].
    { subst. rewrite IdentMap.gss in TID0.
      inv TID0; simpls; clear TID0. }
    red; ins; rewrite IdentMap.gso in TID0; auto.
    eapply PROM_IN_MEM in LHS; eauto. }
  { (* TODO: generalize to a lemma *)
    simpls. red. ins.
    erewrite Memory.add_o in PROM; eauto.
    destruct (loc_ts_eq_dec (l, to) (locw, f_to' w)) as [[A' B']|LL].
    { simpls; rewrite A' in *; rewrite B' in *.
      rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in PROM.
      destruct (is_rel lab w); simpls. }
    rewrite (loc_ts_eq_dec_neq LL) in PROM.
    edestruct SIM_PROM as [b H]; eauto; desc.
    assert (S b) as SB by (by eapply rcoh_I_in_S; eauto). 
    rewrite <- REQ_TO in TO; auto.
    rewrite <- REQ_FROM in FROM; auto.
    exists b; splits; auto.
    cdes IMMCON.
    eapply sim_mem_helper_f_issued with (TLS:=T) (f_to:=f_to); eauto. }
  { red. ins.
    erewrite Memory.add_o in RES; eauto.
    destruct (loc_ts_eq_dec (l, to) (locw, f_to' w)) as [[A' B']|LL].
    { simpls; rewrite A' in *; rewrite B' in *.
      rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in RES.
      inv RES. exists w. splits; auto.
      { clear. find_event_set. }
      clear -NISSB. separate_set_event. }
    rewrite (loc_ts_eq_dec_neq LL) in RES.
    edestruct SIM_RES_PROM as [b H]; eauto; desc.
    exists b. splits; auto.
    { clear -RES0. find_event_set. }
    { clear -NOISS. separate_set_event. }
    2: { by rewrite REQ_TO. }
    by rewrite REQ_FROM. }
  { ins.
    rewrite IdentMap.gso in TID'; auto.
    destruct (loc_ts_eq_dec (loc, to) (locw, (f_to' w))) as [EQ|NEQ]; simpls.
    { desc. subst. right.
      destruct (Memory.get locw (f_to' w) (Local.promises local'0)) eqn: HH; auto.
      exfalso.
      destruct p as [from msg].
      eapply PROM_IN_MEM in HH; eauto.
      eapply Memory.add_get0 in MADD; eauto. destruct MADD as [DD DD'].
      red in DD. rewrite DD in HH. inv HH. }
    edestruct (PROM_DISJOINT TNEQ TID') as [HH|HH]; eauto.
    left.
    erewrite Memory.add_o; eauto.
    rewrite loc_ts_eq_dec_neq; auto. }
  { red. ins.
    edestruct SIM_MEM as [rel_opt HH]; eauto. simpls. desc.
    exists rel_opt. unnw.
    arewrite (f_to' b = f_to b).
    arewrite (f_from' b = f_from b).
    splits; eauto.
    { eapply sim_mem_helper_f_issued; eauto. }
    { eapply Memory.add_closed_timemap; eauto. }
    assert (l <> locw \/ f_to b <> f_to' w) as NEQ by (by apply INEQ).
    intros AA BB. apply HH1 in BB; auto. desc.
    splits.
    { erewrite Memory.add_o; eauto. by rewrite loc_ts_eq_dec_neq. }
    eexists. splits; eauto.
    destruct BB1 as [|CC]; [by left|right].
    desc.
    assert (l <> locw \/ f_to p <> f_to' w) as PNEQ.
    { apply INEQ; auto. rewrite <- LOC0. by apply (wf_rfrmwl WF). }
    exists p. splits; auto.
    exists p_v. splits; auto.
    arewrite (f_to' p = f_to p).
    arewrite (f_from' p = f_from p).
    erewrite Memory.add_o; eauto. rewrite loc_ts_eq_dec_neq; auto. }
  red. ins.
  eapply set_equiv_exp in RESB. 2: { clear. by simplify_tls_events. } 
  destruct RESB as [SB|]; subst.
  { unnw.
    arewrite (f_to' b = f_to b).
    arewrite (f_from' b = f_from b).
    assert (l <> locw \/ f_to b <> f_to' w) as NEQ by (by apply SNEQ).
    edestruct SIM_RES_MEM with (b:=b); eauto; unnw.
    { intros ?. apply NISSB0. clear -H. find_event_set. }
    splits.
    all: erewrite Memory.add_o; eauto; by rewrite loc_ts_eq_dec_neq. }
  splits.
  all: erewrite Memory.add_o; eauto.
  all: assert (l = locw) by (rewrite LOC0 in LOC; inv LOC); subst.
  all: by rewrite loc_ts_eq_dec_eq.
Qed.

End ReserveStepHelper.
