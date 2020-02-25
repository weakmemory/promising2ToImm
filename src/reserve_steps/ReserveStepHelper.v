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
Require Import FtoCoherent.
Require Import SimulationRelProperties.
Require Import ExistsReserveInterval.

Set Implicit Arguments.

Section ReserveStepHelper.

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
    Memory.get loc to local .(Local.Local.promises) = None \/
    Memory.get loc to local'.(Local.Local.promises) = None.

Hypothesis PROM_IN_MEM :
  forall thread' langst local
         (TID : IdentMap.find thread' PC.(Configuration.threads) =
                Some (langst, local)),
    Memory.le local.(Local.Local.promises) PC.(Configuration.memory).

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
Hypothesis RMWREX : dom_rel rmw ⊆₁ R_ex lab.

Lemma reserve_step_helper w locw langst
      (TID : IdentMap.find (tid w) PC.(Configuration.threads) = Some (langst, local))
      (TSTEP : ext_itrav_step
                 G sc w (mkETC T S) (mkETC T (S ∪₁ eq w)))
      (LOC : loc lab w = Some locw)
      (WTID : thread = tid w) :
  let memory := PC.(Configuration.memory) in
  let sc_view := PC.(Configuration.sc) in
  exists f_to' f_from' promises' memory',
    let local' := Local.mk local.(Local.tview) promises' in
    let threads' :=
        IdentMap.add (tid w)
                     (langst, local')
                     (Configuration.threads PC) in
    ⟪ PADD :
        Memory.add local.(Local.promises) locw (f_from' w) (f_to' w)
                                          Message.reserve promises' ⟫ /\
    ⟪ MADD :
        Memory.add memory locw (f_from' w) (f_to' w)
                   Message.reserve memory' ⟫ /\
    
    ⟪ REQ_TO   : forall e (SE: S e), f_to'   e = f_to   e ⟫ /\
    ⟪ REQ_FROM : forall e (SE: S e), f_from' e = f_from e ⟫ /\
    ⟪ FCOH : f_to_coherent G (S ∪₁ eq w) f_to' f_from' ⟫ /\
    ⟪ RESERVED_TIME :
        reserved_time G T (S ∪₁ eq w) f_to' f_from' smode memory' ⟫ /\
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
          Memory.le local.(Local.Local.promises) memory' ⟫ /\

    ⟪ SIM_PROM     : sim_prom     G sc T             f_to' f_from' (tid w) promises'  ⟫ /\
    ⟪ SIM_RES_PROM : sim_res_prom G    T (S ∪₁ eq w) f_to' f_from' (tid w) promises'  ⟫ /\

    ⟪ PROM_DISJOINT :
        forall thread' langst' local'
               (TNEQ : tid w <> thread')
               (TID' : IdentMap.find thread' threads' =
                       Some (langst', local')),
        forall loc to,
          Memory.get loc to promises' = None \/
          Memory.get loc to local'.(Local.Local.promises) = None ⟫ /\

    ⟪ SIM_MEM     : sim_mem G sc T f_to' f_from' (tid w) local' memory' ⟫ /\
    ⟪ SIM_RES_MEM : sim_res_mem G T (S ∪₁ eq w) f_to' f_from' (tid w) local' memory' ⟫.
Proof using All.
  assert (tc_coherent G sc T) as TCCOH by apply ETCCOH.

  subst.
  edestruct exists_time_interval_for_reserve as [f_to']; eauto.
  desc.
  
  assert (~ S w) as NSW.
  { eapply ext_itrav_step_reserve_nS with (T:=mkETC T S); eauto. }

  assert (~ issued T w) as NISSB.
  { intros AA. apply NSW. by apply ETCCOH.(etc_I_in_S). }

  assert (forall e, issued T e -> f_to' e = f_to e) as ISSEQ_TO.
  { ins. apply REQ_TO. by apply ETCCOH.(etc_I_in_S). }
  assert (forall e, issued T e -> f_from' e = f_from e) as ISSEQ_FROM.
  { ins. apply REQ_FROM. by apply ETCCOH.(etc_I_in_S). }

  assert (W w) as WW.
  { eapply ext_itrav_step_reserveW with (T := mkETC T S); eauto. }

  assert (E w) as EW.
  { eapply ext_itrav_stepE with (T := mkETC T S); eauto. }

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
    unionL.
    { apply set_subset_inter_r; split; [by apply ETCCOH|].
      apply (reservedW WF ETCCOH). }
    basic_solver. }

  assert (forall l b (ISSB : issued T b) (BLOC : loc lab b = Some l),
             l <> locw \/ f_to b <> f_to' w) as INEQ.
  { ins. apply SNEQ; auto. by apply ETCCOH.(etc_I_in_S). }

  assert (Memory.le PC.(Configuration.memory) memory') as MM.
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
    { eapply etc_S_W_ex_rfrmw_I with (T:=mkETC T (S ∪₁ eq w)).
      { apply TSTEP. }
      split; [by right|].
      eapply TSTEP. split; [by right|]; simpls. }
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
    left. by apply ETCCOH.(etc_I_in_S). }
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
    assert (S b) as SB by (by apply ETCCOH.(etc_I_in_S)).
    rewrite <- REQ_TO in TO; auto.
    rewrite <- REQ_FROM in FROM; auto.
    exists b; splits; auto.
    cdes IMMCON.
    eapply sim_mem_helper_f_issued with (T:=T) (f_to:=f_to); eauto. }
  { red. ins.
    erewrite Memory.add_o in RES; eauto.
    destruct (loc_ts_eq_dec (l, to) (locw, f_to' w)) as [[A' B']|LL].
    { simpls; rewrite A' in *; rewrite B' in *.
      rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in RES.
      inv RES. exists w. splits; auto. by right. }
    rewrite (loc_ts_eq_dec_neq LL) in RES.
    edestruct SIM_RES_PROM as [b H]; eauto; desc.
    exists b. splits; auto.
    { by left. }
    { by rewrite REQ_FROM. }
      by rewrite REQ_TO. }
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
    { apply INEQ; auto. rewrite <- LOC0. by apply WF.(wf_rfrmwl). }
    exists p. splits; auto.
    exists p_v. splits; auto.
    arewrite (f_to' p = f_to p).
    arewrite (f_from' p = f_from p).
    erewrite Memory.add_o; eauto. rewrite loc_ts_eq_dec_neq; auto. }
  red. ins. destruct RESB as [SB|]; subst.
  { unnw.
    arewrite (f_to' b = f_to b).
    arewrite (f_from' b = f_from b).
    assert (l <> locw \/ f_to b <> f_to' w) as NEQ by (by apply SNEQ).
    edestruct SIM_RES_MEM with (b:=b); eauto; unnw.
    splits.
    all: erewrite Memory.add_o; eauto; by rewrite loc_ts_eq_dec_neq. }
  splits.
  all: erewrite Memory.add_o; eauto.
  all: assert (l = locw) by (rewrite LOC0 in LOC; inv LOC); subst.
  all: by rewrite loc_ts_eq_dec_eq.
Qed.

End ReserveStepHelper.
