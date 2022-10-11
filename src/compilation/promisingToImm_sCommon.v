(******************************************************************************)
(** * Common lemmas for infinite and finite cases of the correctness proof of
      compilation from the Promising2 memory model to the IMM memory model. *)
(******************************************************************************)
Require Import Lia.
Require Import PromisingLib.
From Promising2 Require Import TView View Time Event Cell Thread Memory Configuration Local.
From imm Require Import Prog.
From imm Require Import ProgToExecution.
From imm Require Import Events.
From imm Require Import Execution.
From imm Require Import imm_s.
From imm Require Import CombRelations.
From imm Require Import ProgToExecutionProperties.
From imm Require Import RMWinstrProps.
From imm Require Import AuxRel2.
From imm Require Import FairExecution.
From imm Require Import FinExecution.
From imm Require Import FinThreads.

Require Import SimulationRel.
Require Import PlainStepBasic.
Require Import SimulationPlainStep.
Require Import MaxValue.
Require Import SimState.
Require Import Event_imm_promise.
Require Import PromiseOutcome.
Require Import CertGraphInit.
Require Import MemoryAux.
Require Import PromiseLTS.
Require Import ExtSimTraversal.
Require Import ExtSimTraversalProperties.
Require Import ExtTraversalConfig.
Require Import ExtTraversal.
Require Import ExtTraversalCounting.
Require Import SimulationPlainStepAux.
Require Import FtoCoherent.
Require Import AuxTime.
Require Import IndefiniteDescription.
From imm Require Import ImmFair. 
Require Import Coq.Program.Basics.
Require Import FinTravConfigs.
Require Import ChoiceFacts.
Require Import AuxRel. 
Require Import ImmProperties. 
From hahn Require Import Hahn.

From imm Require Import SimTraversal.
From imm Require Import SimTraversalProperties.
(* From imm Require Import SimTravClosure. *)
From imm Require Import TraversalConfigAlt.
From imm Require Import SetSize.
From imm Require Import SimClosure.

From imm Require Import TLSCoherency.
From imm Require Import IordCoherency. 
Require Import TlsEventSets.
From imm Require Import AuxDef.
From imm Require Import TraversalOrder.

Set Implicit Arguments.

Lemma istep_nil_eq_silent thread :
  istep thread nil ≡
  lts_step thread ProgramEvent.silent.
Proof using.
  unfold lts_step. unfold lab_imm_promise.
  split; [|basic_solver].
  unfolder. ins. exists nil. eauto.
Qed.

Definition execution_final_memory (G : execution) final_memory :=
  forall l,
    (⟪ NO : forall e (EE : acts_set G e), loc (lab G) e <> Some l ⟫ /\
     ⟪ ZERO : final_memory l = 0 ⟫) \/
    exists w,
      ⟪ ACTS : (acts_set G) w ⟫ /\
      ⟪ WW   : is_w (lab G) w ⟫ /\
      ⟪ LOC  : loc  (lab G) w = Some l ⟫ /\
      ⟪ VAL  : val  (lab G) w = Some (final_memory l) ⟫ /\
      ⟪ LAST : ~ (exists w', (co G) w w') ⟫.

Notation "'NTid_' t" := (fun x => tid x <> t) (at level 1).
Notation "'Tid_' t"  := (fun x => tid x =  t) (at level 1).

Lemma cert_sim_step G sc thread PC T T' f_to f_from smode
      (WF : Wf G) (IMMCON : imm_consistent G sc)
      (STEP : ext_isim_trav_step G sc thread T T')
      (SIMREL : simrel_thread G sc PC T f_to f_from thread smode)
      (NCOV : NTid_ thread ∩₁ (acts_set G) ⊆₁ covered T)
      (FAIR: mem_fair G):
    exists PC' f_to' f_from',
      ⟪ PSTEP : (plain_step MachineEvent.silent thread)＊ PC PC' ⟫ /\
      ⟪ SIMREL : simrel_thread G sc PC' T' f_to' f_from' thread smode ⟫.
Proof using.
  eapply plain_sim_step in STEP; eauto.
  desf. eexists. eexists. eexists. splits; eauto.
Qed.

Lemma cert_sim_steps G sc thread PC T T' f_to f_from smode
      (WF : Wf G) (IMMCON : imm_consistent G sc)
      (STEPS : (ext_isim_trav_step G sc thread)⁺ T T')
      (SIMREL : simrel_thread G sc PC T f_to f_from thread smode)
      (NCOV : NTid_ thread ∩₁ (acts_set G) ⊆₁ covered T)
      (FAIR: mem_fair G):
    exists PC' f_to' f_from',
      ⟪ PSTEP : (plain_step MachineEvent.silent thread)＊ PC PC' ⟫ /\
      ⟪ SIMREL : simrel_thread G sc PC' T' f_to' f_from' thread  smode ⟫.
Proof using.
  generalize dependent f_from.
  generalize dependent f_to.
  generalize dependent PC.
  induction STEPS.
  { ins. eapply cert_sim_step in H; eauto. }
  ins.
  apply IHSTEPS1 in SIMREL; auto.
  desf.
  apply IHSTEPS2 in SIMREL0; auto.
  { desf. eexists. eexists. eexists. splits.
    2: by eauto.
    eapply rt_trans; eauto. }
  etransitivity; eauto.
  eapply ext_sim_trav_steps_covered_le with (G:=G) (sc:=sc).
  apply inclusion_t_rt.
  generalize STEPS1. clear.
  generalize dependent y. generalize dependent x.
  apply inclusion_t_t.
  unfold ext_sim_trav_step.
  basic_solver.
Qed.

Lemma cert_simulation G sc thread PC T f_to f_from
      (WF : Wf G) (IMMCON : imm_consistent G sc)
      (SIMREL : simrel_thread G sc PC T f_to f_from thread sim_certification)
      (NCOV : NTid_ thread ∩₁ (acts_set G) ⊆₁ covered T)
      (FIN: fin_exec G)
      (FIN_THREADS: fin_threads G)
      (FAIR: mem_fair G)
      (IMM_FAIR: imm_s_fair G sc):
  exists T' PC' f_to' f_from',
    ⟪ FINALT : (acts_set G) ⊆₁ covered T' ⟫ /\
    ⟪ PSTEP  : (plain_step MachineEvent.silent thread)＊ PC PC' ⟫ /\
    ⟪ SIMREL : simrel_thread G sc PC' T' f_to' f_from' thread sim_certification⟫.
Proof using.
  assert (complete G) as CG by apply IMMCON.
  assert (wf_sc G sc) as WFSC by apply IMMCON.  
 
  forward eapply sim_step_cov_full_traversal as H; eauto.
  all: try by apply SIMREL. 
    
  destruct H as [T']. desc.
  exists T'. apply rtE in H.
  destruct H as [H|H].
  { red in H. desf.
    eexists. eexists. eexists.
    splits; eauto.
    apply rtE. left. red. eauto. }
  eapply cert_sim_steps in H; auto.
  2: by eauto.
  desf. eexists. eexists. eexists. splits; eauto.
Qed.

Lemma simrel_thread_bigger_sc_memory G sc T thread f_to f_from threads memory
      sc_view memory' sc_view'
      lang state local
      (WF : Wf G) (IMMCON : imm_consistent G sc)
      (THREAD     : IdentMap.find thread threads = Some (existT _ lang state, local))
      (INHAB      : Memory.inhabited memory' )
      (CLOSED_MEM : Memory.closed memory')
      (MEM_LE : Memory.le memory memory')
      (SС_CLOSED  : Memory.closed_timemap sc_view' memory')
      (SIMREL : simrel_thread G sc (Configuration.mk threads sc_view memory )
                              T f_to f_from thread  sim_certification) :
  simrel_thread G sc (Configuration.mk threads sc_view' memory') T f_to f_from
                thread sim_certification.
Proof using.
  cdes SIMREL. cdes COMMON. cdes LOCAL.
  red; splits; red; splits; eauto; ins.
  { ins. etransitivity.
    { eapply PROM_IN_MEM; eauto. }
    done. }
  eexists. eexists. eexists; eauto. splits; eauto.
  3: by eapply memory_close_le; eauto.
  2: { red. ins. edestruct SIM_RES_MEM as [rel_opt H]; eauto. }
  red. ins.
  edestruct SIM_MEM as [rel_opt H]; eauto.
  simpls. desf.
  exists rel_opt; splits; eauto.
  { eapply memory_closed_timemap_le; eauto. }
  ins. destruct H1; eauto. unnw. desc.
  splits; auto.
  exists p_rel. splits; auto.
  desf; [by left| right].
  apply MEM_LE in H5.
  exists p; splits; auto.
  exists p_v; splits; auto.
Qed.

Section PromisingToIMM.
  
Variable prog : Prog.t.
Hypothesis TNONULL : ~ IdentMap.In tid_init prog.

Variable G : execution.
Variable final_memory : location -> value.

Hypothesis ALLRLX  : (acts_set G) \₁ is_init ⊆₁ (fun a => is_true (is_rlx (lab G) a)).
Hypothesis FRELACQ : (acts_set G) ∩₁ (fun a => is_true (is_f (lab G) a)) ⊆₁ (fun a => is_true (is_ra (lab G) a)).

Hypothesis EFM : execution_final_memory G final_memory.

Hypothesis PROG_EX : program_execution prog G.
Hypothesis RMWREX  : forall thread linstr
                            (IN : Some linstr = IdentMap.find thread prog),
    rmw_is_rex_instrs linstr.
Hypothesis WF : Wf G.
Variable sc : relation actid.
Hypothesis IMMCON : imm_consistent G sc.
Variable (tb: thread_id).

(* TODO: doesn't it follow from PROG_EX? *)
Hypothesis (FIN_THREADS : fin_threads G).
Hypothesis (GTHREADSPROG : forall t (IN : threads_set G t), IdentMap.In t prog).

Lemma conf_steps_preserve_thread tid PC PC'
      (STEPS : (plain_step MachineEvent.silent tid)＊ PC PC') :
  forall lang state local
         (THREAD  : IdentMap.find tid (Configuration.threads PC) =
                    Some (existT _ lang  state , local)),
  exists lang' state' local',
    IdentMap.find tid PC'.(Configuration.threads) =
    Some (existT _ lang' state', local').
Proof using.
  induction STEPS.
  2: { ins. eauto. }
  { destruct H.
    simpls. rewrite IdentMap.gss. eauto. }
  ins. edestruct IHSTEPS1; eauto. desc.
  eapply IHSTEPS2; eauto.
Qed.

Lemma conf_steps_preserve_lang tid PC PC'
      (STEPS : (plain_step MachineEvent.silent tid)＊ PC PC') :
  forall lang  state  local lang' state' local'
         (THREAD  : IdentMap.find tid (Configuration.threads PC) =
                    Some (existT _ lang  state , local))
         (THREAD' : IdentMap.find tid PC'.(Configuration.threads) =
                    Some (existT _ lang' state', local')),
    lang = lang'.
Proof using.
  induction STEPS.
  2: { ins. rewrite THREAD' in THREAD. inv THREAD. }
  { destruct H.
    simpls. rewrite IdentMap.gss.
    ins. desf. }
  ins.
  edestruct conf_steps_preserve_thread with (PC':=y); eauto. desc.
  etransitivity.
  { eapply IHSTEPS1; eauto. }
  eapply IHSTEPS2; eauto.
Qed.

Lemma conf_steps_to_thread_steps tid PC PC'
      (STEPS : (plain_step MachineEvent.silent tid)＊ PC PC') :
  forall lang state local
         state' local' ts ts' 
         (THREAD  : IdentMap.find tid (Configuration.threads PC) =
                    Some (existT _ lang state, local))
         (THREAD' : IdentMap.find tid PC'.(Configuration.threads) =
                    Some (existT _ lang state', local'))
         (TS  : ts  = Thread.mk lang state local
                                (Configuration.sc PC) (Configuration.memory PC))
         (TS' : ts' = Thread.mk lang state' local'
                                PC'.(Configuration.sc) PC'.(Configuration.memory)),
    rtc (Thread.tau_step (lang:=lang)) ts ts'.
Proof using.
  induction STEPS.
  2: { ins. apply rtc_refl.
       rewrite TS, TS'.
       rewrite THREAD' in THREAD. inv THREAD. }
  { set (pe := MachineEvent.silent) in H.
    assert (pe = MachineEvent.silent) as HH.
    { done. }
    destruct H.
    simpls. rewrite IdentMap.gss.
    ins. desf. eapply rtc_n1; eauto.
    red. econstructor.
    { econstructor; eauto. }
    done. }
  ins.
  edestruct conf_steps_preserve_thread with (PC':=y); eauto. desc.
  assert (x0 = lang); subst.
  { eapply conf_steps_preserve_lang; eauto. }
  etransitivity.
  { eapply IHSTEPS1; eauto. }
  eapply IHSTEPS2; eauto.
Qed.

Lemma event_to_prog_thread e (ACT : acts_set G e) (NINIT : ~ is_init e) :
  IdentMap.In (tid e) prog.
Proof using PROG_EX.
  red in PROG_EX.
  destruct PROG_EX as [HH OO].
  destruct (HH e ACT) as [|AA]; [by desf|done].
Qed.

Lemma dom_rmw_in_R_ex : dom_rel (rmw G) ⊆₁ (fun a : actid => R_ex (lab G) a).
Proof using PROG_EX RMWREX WF.
  red in PROG_EX.
  intros x H.
  destruct H as [y RMW].
  assert (acts_set G x) as EX.
  { apply (dom_l (wf_rmwE WF)) in RMW.
    apply seq_eqv_l in RMW. desf. }
  rename PROG_EX into HH. destruct HH as [PROG_EX PEX].
  specialize (PROG_EX x EX).
  destruct PROG_EX as [INIT|TH]. 
  { exfalso. apply (rmw_from_non_init WF) in RMW.
    apply seq_eqv_l in RMW. desf. }
  apply IdentMap.Facts.in_find_iff in TH.
  destruct (IdentMap.find (tid x) prog) eqn: INP.
  2: done.
  symmetry in INP.
  set (PP:=INP).
  apply PEX in PP. desc. subst.
  red in PP. desc.
  rewrite <- PEQ in *.
  assert (acts_set (ProgToExecution.G s) x) as SX.
  { apply (tr_acts_set PP0). by split. }
  unfold R_ex.
  assert (lab G x = lab (ProgToExecution.G s) x) as LL.
  { eapply lab_thread_eq_thread_restricted_lab; eauto. }
  assert ((ProgToExecution.G s).(rmw) x y) as SRMW.
  { apply (tr_rmw PP0).
    simpls. apply seq_eqv_l; split; auto.
    apply seq_eqv_r. split; auto.
    apply (wf_rmwt WF) in RMW. symmetry. apply RMW. }
  assert (dom_rmw_in_rex s) as YY.
  2: { specialize (YY x). rewrite LL.
       apply YY. by exists y. }
  apply RMWREX in INP.
  eapply dom_rmw_in_rex_thread_steps; eauto.
  { unfold init; simpls. }
  { apply wf_thread_state_init. }
  red. unfold init. simpls. clear. basic_solver.
Qed.

Lemma simrel_init :
  simrel G sc (conf_init prog)
         (init_tls G) 
         (fun _ => tid_init) (fun _ => tid_init).
Proof using ALLRLX IMMCON PROG_EX TNONULL WF FRELACQ RMWREX.
  assert (covered (init_tls G) ≡₁ acts_set G ∩₁ is_init /\
            issued (init_tls G) ≡₁ acts_set G ∩₁ is_init /\
          reserved (init_tls G) ≡₁ acts_set G ∩₁ is_init )
    as (COVI & ISSI & RESI).
  { unfold init_tls. rewrite !set_pair_union_l.
    simplify_tls_events. basic_solver. }

  red; splits; red; splits; auto.
  { apply init_tls_tls_coherent. }
  { apply init_tls_iord_coherent. }
  { by apply init_tls_reserve_coherent. }
  { rewrite ISSI, COVI. basic_solver. }
  { intros r w (NIr & RMW & NIw)%rmw_non_init_lr%seq_eqv_lr; auto.
    split; by intros COV%COVI%proj2. }  
  { ins.
    unfold Threads.init.
    rewrite IdentMap.Facts.map_o.
    unfold init_threads.
    rewrite IdentMap.gmapi.
    assert (IdentMap.In (tid e) prog) as INE.
    { by apply event_to_prog_thread. }
    assert (exists linstr, IdentMap.find (tid e) prog = Some linstr)
      as [linstr LI].
    { apply IdentMap.Facts.in_find_iff in INE.
      destruct (IdentMap.find (tid e) prog) eqn: H; desf.
      eauto. }
    rewrite LI. simpls. eauto. }
  { ins. unfold init_threads, Threads.init in *.
    rewrite IdentMap.Facts.map_o in TID.
    rewrite IdentMap.gmapi in TID.
    destruct (IdentMap.find thread' prog) eqn: HH; simpls.
    inv TID. unfold Local.init. simpls.
    apply Memory.bot_le. }
  { assert (complete G) as CG.
    { apply IMMCON. }
    assert (Execution_eco.sc_per_loc G) as ESC.
    { apply imm_s_hb.coherence_sc_per_loc. apply IMMCON. }
    red. splits; simpls.
    { ins. apply RESI, proj2 in H. vauto. }
    all: ins; exfalso.
    apply Execution_eco.no_co_to_init in H1; auto.
    apply seq_eqv_r in H1.
    apply RESI, proj2 in H0. by desc. }
  { ins. }
  { ins.
    unfold LocFun.find, TimeMap.bot.
    apply max_value_empty.
    unfold S_tm, S_tmr.
    ins. intros HH.
    destruct HH as [y HH].
    apply seq_eqv_l in HH. destruct HH as [_ HH].
    destruct HH as [z [_ HH]].
    destruct HH as [w [_ HH]].
    apply id_inter in HH as [-> [[F _] C]].
    apply COVI, proj2 in C. 
    apply (init_w WF) in C.
    type_solver. }
  { apply dom_rmw_in_R_ex. }
  { red. splits; ins.
    3: { match goal with
         | H : co _ _ _ |- _ => rename H into CO
         end.
         apply Execution_eco.no_co_to_init in CO as [CO NI]%seq_eqv_r; auto.
         2: { apply imm_s_hb.coherence_sc_per_loc. apply IMMCON. }
         apply RESI, proj2 in H0. vauto. }
    2: { red. ins. apply memory_init_o in MSG. desf. }
    red; ins. unfold Memory.init in MSG.
    unfold Memory.get in MSG.
    unfold Cell.init in MSG.
    unfold Cell.get in MSG; simpls.
    unfold Cell.Raw.init in MSG.
    destruct (classic (to = Time.bot)) as [|NEQ]; subst.
    2: { rewrite DenseOrder.DOMap.singleton_neq in MSG; auto.
         inv MSG. }
    rewrite DenseOrder.DOMap.singleton_eq in MSG. inv MSG.
    left. by split. }
  { unfold conf_init, Configuration.init.
    simpls.
    edestruct TView.bot_closed.
    unfold TView.bot, View.bot in *; simpls.
    destruct CUR. simpls. }
  { simpls. apply Memory.init_closed. }
  simpls.
  apply IdentMap.Facts.in_find_iff in TP.
  destruct (IdentMap.find thread (Threads.init (init_threads prog))) eqn: HH; simpls.
  clear TP.
  unfold Threads.init in *.
  rewrite IdentMap.Facts.map_o in *.
  unfold init_threads in *.
  rewrite IdentMap.gmapi in *.
  destruct (IdentMap.find thread prog) eqn: UU; simpls.
  inv HH. clear HH.
  simpls.
  exists (init l), (Local.init); splits; auto.
  { red; ins; desf; apply TNONULL, IdentMap.Facts.in_find_iff; congruence. }
  { apply wf_thread_state_init. }
  { symmetry in UU. apply RMWREX in UU. unfold init. simpls. }
  { ins. left. apply Memory.bot_get. }
  { red. ins.
    unfold Local.init in *. simpls. 
    rewrite Memory.bot_get in PROM. inv PROM. }
  { red. ins. rewrite Memory.bot_get in RES. inv RES. }
  { red; simpls.
    unfold Memory.init. unfold Memory.get. unfold Cell.init.
    unfold Cell.get; simpls. unfold Cell.Raw.init.
    rewrite DenseOrder.DOMap.singleton_eq.
    exists None. splits; ins.
    { unfold Message.elt.
      assert (v = 0); [|by desf].
      apply ISSI, proj2 in ISSB.
      destruct b; [| by vauto]. 
      unfold val in VAL.
      rewrite (wf_init_lab WF) in VAL.
      inv VAL. }
    { red. splits; auto.
      { right. splits; auto. by apply ISSI. }
      red. ins. unfold LocFun.find, TimeMap.bot.
      apply max_value_bot_f. }
    { red. unfold View.unwrap, View.bot, TimeMap.bot. simpls.
      ins. eexists. eexists. eexists.
      unfold Memory.get, Cell.get. simpls. }
    destruct H0. by apply COVI, ISSI. }
  { red; simpls. ins.
    destruct NISSB. by apply ISSI, RESI. }
  { unfold Local.init. simpls.
    unfold TView.bot. red; simpls.
    unfold View.bot.
    splits; simpls; red.
    all: unfold LocFun.find, TimeMap.bot; simpls.
    all: ins.
    all: apply max_value_bot_f. }
  { unfold Local.init. simpls. }
  { unfold Local.init. simpls. red.
    unfold TView.bot; simpls. splits; ins.
    all: apply Memory.closed_timemap_bot.
    all: red; ins. }
  red. splits.
  { ins. split; ins; [|lia].
    apply COVI, proj2 in H. vauto. }
  unfold sim_state_helper.
  red in PROG_EX. destruct PROG_EX as [HH YY].
  symmetry in UU. apply YY in UU.
  desc. red in UU. desc.
  eexists. splits; eauto. by subst.
Qed.

Definition thread_is_terminal ths tid :=
  forall (lang : Language.t ProgramEvent.t) st lc
         (LLH : IdentMap.find tid ths =
                Some (existT (fun lang => Language.state lang) lang st, lc)),
    ⟪ NOTS : Language.is_terminal lang st ⟫ /\
    ⟪ NOPROM : Local.is_terminal lc ⟫.

Lemma sim_thread_covered_exists_terminal PC thread T f_to f_from
      (FINALT : Tid_ thread ∩₁ acts_set G ⊆₁ covered T)
      (SIMREL : simrel G sc PC T f_to f_from) :
  exists PC',
    ⟪ STEP : (conf_step)^? PC PC' ⟫ /\
    ⟪ SIMREL : simrel G sc PC' T f_to f_from ⟫ /\
    ⟪ SAMENUM : Permutation (map fst (IdentMap.elements (Configuration.threads PC))) 
                            (map fst (IdentMap.elements (Configuration.threads PC'))) ⟫ /\ 
    ⟪ TERMINAL  : thread_is_terminal PC'.(Configuration.threads) thread ⟫ /\
    ⟪ PTERMINAL :
      forall thread' (TT : thread_is_terminal (Configuration.threads PC) thread'),
        thread_is_terminal PC'.(Configuration.threads) thread' ⟫.
Proof using All.
  cdes SIMREL.
  destruct (IdentMap.find thread (Configuration.threads PC)) as [j|] eqn: QQ.
  2: { exists PC. splits; auto.
       red. ins.
       clear -QQ LLH.
       (* This trick is needed due to an implicit parameter which could be seen
          by `Set Printing All.` *)
       match goal with
       | H1 : ?A = None,
         H2 : ?B = Some _ |- _ =>
         assert (A = B) as AA
       end.
       { unfold language. done. }
       rewrite AA in QQ.
       destruct (IdentMap.find thread (Configuration.threads PC)); desf. }
  assert (IdentMap.In thread (Configuration.threads PC)) as YY.
  { apply IdentMap.Facts.in_find_iff. by rewrite QQ. }
  apply THREADS in YY. cdes YY.
  cdes STATE. cdes STATE1.
  assert (Local.promises local = Memory.bot) as PBOT.
  { red in SIM_PROM.
    eapply Memory.ext. ins.
    rewrite Memory.bot_get.
    destruct (Memory.get loc ts (Local.promises local)) eqn: H; auto.
    destruct p as [from msg].
    destruct msg as [v msg|].
    { eapply SIM_PROM in H; eauto.
      desc.
      exfalso. apply NCOV. by apply FINALT. }
    eapply SIM_RPROM in H; eauto. desc.
    exfalso.
    apply NOISS. eapply w_covered_issued.
    1, 2: by apply COMMON.
    split.
    { eapply reservedW; auto.
      1, 2: by apply COMMON.
      done. }
    apply FINALT. by split. }
  assert (Local.is_terminal local) as LCTR by (constructor; auto).
  assert (wf_thread_state thread state') as GPC'.
  { eapply wf_thread_state_steps; eauto. }
  assert (acts_set (ProgToExecution.G state') ⊆₁
          acts_set (ProgToExecution.G state)) as PP.
  { intros x HH. set (HH' := HH).
    apply GPC'.(acts_rep) in HH'.
    desc. rewrite REP in *. clear x REP.
    assert (covered T (ThreadEvent thread index)) as CC.
    { apply FINALT. split; auto.
      apply TEH in HH. apply HH. }
    apply PCOV in CC. by apply (acts_clos GPC). }
  assert ((istep thread nil)＊ state state') as KK.
  { apply steps_same_E_empty_in; auto. }
  assert ((lts_step thread ProgramEvent.silent)＊ state state') as HH.
  { by hahn_rewrite <- istep_nil_eq_silent. }
  assert (state'.(eindex) = (eindex state)) as EII.
  { eapply steps_same_eindex; eauto. }
  rename STEPS into STEPSAA.
  rename HH into STEPS.

  assert (forall A (a b : A), Some a = Some b -> a = b) as XBB.
  { ins. inv H. }
  assert (forall A (a b : A) B (c : B), (a, c) = (b, c) -> a = b) as XBB1.
  { ins. inv H. }

  apply rtE in STEPS. destruct STEPS as [EQ|STEPS].
  { red in EQ. desf. exists PC. splits; auto.
    red. ins.
    destruct (IdentMap.find thread (Configuration.threads PC)) eqn: HH.
    2: { clear -LLH0 LLH HH.
         unfold language in *.
         desf. }
    inv LLH.
    unfold language in *; simpls.
    rewrite HH in LLH0. inv LLH0.
    assert (state' = st); subst.
    { clear -LLH0 XBB XBB1. simpl in *.
      apply XBB in LLH0.
      apply XBB1 in LLH0. desf. }
    splits; auto. red. simpls.
      by apply TERMINAL. }
  assert 
  (thread_is_terminal
     (IdentMap.add thread (existT (@Language.state ProgramEvent.t) (thread_lts thread) state', local)
                   (Configuration.threads PC)) thread) as TT.
  { red. ins. rewrite IdentMap.gss in LLH0. inv LLH0.
    assert (state' = st); subst.
    { clear -LLH0 XBB XBB1. simpl in *.
      apply XBB in LLH0.
      apply XBB1 in LLH0. desf. }
    splits; auto. red. simpls.
      by apply TERMINAL. }

  eexists. splits.
  { apply r_step. eexists. exists thread.
    apply ct_end in STEPS.
    destruct STEPS as [state'' [STEPS STEP]].
    eapply Configuration.step_normal.
    { eauto. }
    { eapply rtc_lang_tau_step_rtc_thread_tau_step.
      unfold Language.Language.step. simpls.
      apply clos_rt_rt1n. apply STEPS. }
    { apply Thread.step_program.
      constructor. simpls.
      2: by apply Local.step_silent. 
      apply STEP. }
    { done. }
    red. ins. splits; eauto.
    unfold sflib.NW. eauto. }
  2: { ins; clear - QQ. 
       apply NoDup_Permutation; eauto using NoDup_map_NoDupA, IdentMap.elements_3w.
       ins; rewrite !in_map_iff; split; intros ([i v] & <- & IN); ins;
         apply IdentMap.elements_complete in IN;
       destruct (Loc.eq_dec i thread); desf; rewrite ?IdentMap.gss, ?IdentMap.gso in *; ins; desf.
         by eexists (_, _); split; ins; apply IdentMap.elements_correct, IdentMap.gss.
         eby eexists (_, _); split; ins; apply IdentMap.elements_correct; rewrite IdentMap.gso.
       all: eexists (_, _); split; ins; eauto using IdentMap.elements_correct.
     }
  2: done. 
  2: { ins. red. destruct (classic (thread' = thread)) as [|NEQ]; subst; ins.
       rewrite IdentMap.gso in *; auto. }
  cdes COMMON. simpls.
  red. splits; red; splits; auto.
  { ins. destruct (classic (thread = tid e)); subst.
    2: by rewrite IdentMap.gso; auto.
    rewrite IdentMap.gss. eauto. }
  { ins. destruct (classic (thread' = thread)); subst.
    { rewrite IdentMap.gss in *. inv TID.
      eapply PROM_IN_MEM; eauto. }
    rewrite IdentMap.gso in *; auto.
    eapply PROM_IN_MEM; eauto. }
  simpls.
  destruct (classic (thread0 = thread)) as [|NEQ]; subst.
  { rewrite IdentMap.gss. 
    eexists; eexists. splits.
    1,4: done.
    all: eauto.
    { erewrite steps_preserve_instrs; eauto. }
    { ins. left. rewrite PBOT. apply Memory.bot_get. }
    red. splits.
    { by rewrite EII. }
    eexists. red. splits; eauto. apply rt_refl. }
  apply IdentMap.Facts.in_find_iff in TP.
  rewrite IdentMap.gso in *; auto.
  destruct (IdentMap.find thread0 (Configuration.threads PC)) as [k|] eqn:AA; [|done].
  assert (IdentMap.In thread0 (Configuration.threads PC)) as BB.
  { apply IdentMap.Facts.in_find_iff. by rewrite AA. }
  apply THREADS in BB.
  destruct k.  destruct s.
  cdes BB. eexists. eexists. splits; eauto.
  { by rewrite <- AA. }
  ins. destruct (classic (thread' = thread)) as [|NN].
  { subst. rewrite IdentMap.gss in *. inv TID'.
    right. rewrite PBOT. apply Memory.bot_get. }
  rewrite IdentMap.gso in TID'; auto.
  eapply PROM_DISJOINT0; eauto.
Qed. 

Lemma sim_covered_exists_terminal T PC f_to f_from
      (FINALT : acts_set G ⊆₁ covered T)
      (SIMREL : simrel G sc PC T f_to f_from) :
  exists PC',
    ⟪ STEPS : conf_step＊ PC PC' ⟫ /\
    ⟪ SIMREL : simrel G sc PC' T f_to f_from ⟫ /\
    ⟪ TERMINAL : Configuration.is_terminal PC' ⟫.
Proof using All.
  assert
    (exists l, 
         length (filterP (fun x => ~ thread_is_terminal ((Configuration.threads PC)) x)
                   (map fst (IdentMap.elements (Configuration.threads PC))))
         = l)
     as [l LL] by eauto.
  generalize dependent PC.
  induction l using (well_founded_ind Wf_nat.lt_wf); ins; desf.
  destruct (classic (
      forall x (ELEM: In x (IdentMap.elements (Configuration.threads PC))), 
        Language.is_terminal (projT1 (fst (snd x))) (projT2 (fst (snd x))) /\
        Local.is_terminal (snd (snd x))
    )) as [Y|Y].
     eexists; splits; eauto using rt_refl.
     by repeat red; ins; apply IdentMap.elements_correct, Y in FIND; ins. 
  apply not_all_ex_not in Y; destruct Y as ([i v] & Y).
  apply imply_to_and in Y; destruct Y as (FIND & Y); ins.
  assert (IN:=FIND); apply IdentMap.elements_complete in FIND.
  forward eapply sim_thread_covered_exists_terminal with (thread := i) as X; desc; eauto.
    by rewrite FINALT; unfolder; ins; desf.
  eapply H in SIMREL0; ins; desc.
    by eexists; splits; eauto; apply cr_rt; red; eauto.

  
  clear - STEP SAMENUM IN FIND Y TERMINAL PTERMINAL.
  assert (L: forall l, length (filterP (fun x => ~ thread_is_terminal (Configuration.threads PC') x) l)
          <= length (filterP (fun x => ~ thread_is_terminal (Configuration.threads PC) x) l)).
    clear - PTERMINAL; induction l; ins; desf; ins; eauto; try lia.
    exfalso; specialize (PTERMINAL a); tauto.
  rewrite SAMENUM.
  apply in_split_perm in IN; desc; rewrite IN in SAMENUM; ins; rewrite <- SAMENUM; ins. 
  desf; ins. 
  2: by destruct v as ((lang,st),lc); destruct Y; apply NNPP in n0; apply n0 in FIND; ins.
  clear Y.
  auto using Lt.le_lt_n_Sm.
Qed.

Lemma same_final_memory T PC f_to f_from
      (FINALT : acts_set G ⊆₁ covered T)
      (SIMREL : simrel G sc PC T f_to f_from) :
  forall l,
    final_memory_state (Configuration.memory PC) l = Some (final_memory l).
Proof using All.
  (* assert (etc_coherent G sc (mkETC T S)) as ETCCOH by apply SIMREL. *)
  (* assert (tc_coherent G sc T) as TCCOH by apply ETCCOH. *)
  ins. unfold final_memory_state.
  cdes SIMREL. cdes COMMON.
  edestruct (Memory.max_ts_spec l) as [AA _].
  { apply INHAB. }
  red in AA. desc.
  rewrite AA. simpls.
  destruct msg as [val msg|].
  2: { desc. eapply HMEM in AA. desc.
       exfalso.
       apply NOISS. eapply w_covered_issued; eauto.
       split.
       { eapply reservedW; eauto. }
       by apply FINALT. }
  assert (val = final_memory l); [|by subst].
  desc. red in MEM.
  set (BB := AA).
  apply MEM in BB.
  destruct BB as [[BB YY]|].
  { rewrite BB in *. specialize (INHAB l).
    rewrite INHAB in AA. inv AA.
    destruct (EFM l); desc; auto.
    assert (is_init w) as II.
    2: { unfold val in VAL.
         destruct w; [|by desf].
         rewrite (wf_init_lab WF) in VAL.
         inv VAL. }
    assert (issued T w) as WISS.
    { eapply w_covered_issued; eauto.
      split; auto. }
    assert (reserved T w) as WS.
    { eapply rcoh_I_in_S; eauto. }
    destruct (classic (is_init w)) as [|NINIT]; auto.
    exfalso.
    destruct (THREAD w) as [langst TT]; auto.
    assert (IdentMap.In (tid w) (Configuration.threads PC)) as NN.
    { destruct (THREAD w); auto.
      apply IdentMap.Facts.in_find_iff.
        by rewrite H. }
    apply THREADS in NN. cdes NN.
    assert (SS := SIM_MEM).
    edestruct SS as [rel_opt]; eauto.
    simpls. desc.
    destruct (classic (f_to w = Time.bot)) as [FEQ|FNEQ].
    { rewrite FEQ in *. rewrite INMEM in INHAB.
      inv INHAB. cdes FCOH.
      apply TTOFROM in NINIT; auto. 
      rewrite FEQ in NINIT. rewrite H0 in NINIT.
        by apply Time.lt_strorder in NINIT. }
    apply Memory.max_ts_spec in INMEM.
    destruct INMEM as [_ CC].
    rewrite BB in CC. apply Time.le_lteq in CC.
    destruct CC as [CC|]; [|by desf].
      by apply time_lt_bot in CC. }
  desc. edestruct (@EFM l); desc.
  { by apply NO in LOC. }
  destruct (classic (is_init w)) as [INIT|NINIT].
  { assert (f_to w = Time.bot) as BB.
    { apply FCOH. by split. }
    destruct (classic (b = w)) as [|NEQ]; subst.
    2: { edestruct (wf_co_total WF) as [CO|CO]; eauto.
         1,2: split; [split|]; auto.
         { eapply issuedW; eauto. }
         { by rewrite LOC. }
         { exfalso. apply Execution_eco.no_co_to_init in CO; auto.
           2: { apply imm_s_hb.coherence_sc_per_loc. apply IMMCON. }
           apply seq_eqv_r in CO. desf. }
         exfalso. apply LAST. eauto. }
    rewrite BB in *. rewrite <- TO in *.
    rewrite INHAB in AA. inv AA.
    destruct w; simpls.
    unfold val in VAL. rewrite (wf_init_lab WF) in VAL.
    inv VAL. }
  assert (IdentMap.In (tid w) (Configuration.threads PC)) as NN.
  { destruct (THREAD w); auto.
    apply IdentMap.Facts.in_find_iff.
      by rewrite H. }
  apply THREADS in NN. cdes NN.
  assert (SS := SIM_MEM).
  assert (issued T w) as IIW.
  { eapply w_covered_issued; eauto. split; auto. }
  edestruct SS with (b:=w) as [rel_opt]; eauto.
  simpls. desc. clear H1.
  destruct (classic (b = w)) as [|NEQ]; subst.
  { rewrite <- TO in *. rewrite INMEM in AA. inv AA. }
  edestruct (wf_co_total WF) as [CO|CO]; eauto.
  1,2: split; [split|]; auto.
  { eapply issuedW; eauto. }
  { by rewrite LOC. }
  2: { exfalso. apply LAST. eauto. }
  assert (reserved T b) as BS.
  { eapply rcoh_I_in_S; eauto. }
  assert (reserved T w) as WS.
  { eapply rcoh_I_in_S; eauto. }
  eapply f_to_co_mon with (I:=reserved T) in CO; eauto.
  apply Memory.max_ts_spec in INMEM.
  destruct INMEM as [_ CC].
  rewrite <- TO in CC.
  exfalso. eapply Time.lt_strorder.
  eapply TimeFacts.lt_le_lt; eauto.
Qed.

Lemma sim_step PC T T' f_to f_from
      (STEP : ext_sim_trav_step G sc T T')
      (T_FIN: tls_fin T)
      (SIMREL : simrel G sc PC T f_to f_from)
      (FAIR: mem_fair G) :
    exists PC' f_to' f_from',
      ⟪ PSTEP : (conf_step)^? PC PC' ⟫ /\
      ⟪ SIMREL : simrel G sc PC' T' f_to' f_from' ⟫.
Proof using All.
  destruct STEP as [thread STEP].
  forward eapply isim_step_preserves_fin with (t := thread) as FIN'; eauto. 
  cdes SIMREL. cdes COMMON.
  eapply plain_sim_step in STEP; eauto.
  2: { split; eauto. apply THREADS.
       cdes COMMON. subst.

       (* enough (threads_set G thread ) as DD. *)
       (* { eapply GTHREADSPROG. *)
       assert (exists e, thread = tid e /\ acts_set G e /\ ~ is_init e) as [e].
       { move STEP at bottom.
         apply ext_sim_trav_step_to_step in STEP. desc. 
         destruct lbl as [a e].
         assert (acts_set G e) as EE.
         { eapply ext_itrav_stepE in STEP; eauto. }
         destruct a.

         (* propagation step *)
         3: { destruct STEP. subst.
              rename ets_tls_coh into AA.
              rewrite ets_upd in AA.
              apply tls_coh_exec in AA.
              assert (eq (ta_propagate thread, e) ⊆₁ init_tls G ∪₁ exec_tls G) as BB.
              { rewrite <- AA. clear. basic_solver. }
              rewrite set_subset_single_l in BB. destruct BB as [BB|BB].
              { exfalso. apply ets_new_ta. eapply tls_coh_init; eauto. }
              destruct BB as [BB|BB]; [red in BB; desf| ].
              destruct BB as [BB _].
              destruct BB as [BB|BB]; [red in BB; desf| ].
              do 2 red in BB. desf. destruct BB as [BB CC]. red in BB.
              admit. }
         all: exists e.
         all: splits; auto. 
         all: eapply ext_itrav_step_ninit in STEP; eauto.

       desc. 
       cdes COMMON. subst.
       destruct (THREAD e); auto.
       apply IdentMap.Facts.in_find_iff.
       by rewrite H. }
  desf. exists PC'. exists f_to'. exists f_from'. splits.
  2: { apply SIMREL0; eauto. }

  apply rtE in PSTEP.
  destruct PSTEP as [[HH]|PSTEP]; subst.
  { by constructor. }
  apply plain_step_ct_in_plain_step in PSTEP.
  right.
  red. exists MachineEvent.silent. exists thread.
  destruct PSTEP. econstructor; eauto.
  red; simpls. ins. right.
  
  edestruct cert_graph_init as [G' [sc'' [T'' [S'' HH]]]]; eauto.
  desc.

  set (PC := (Configuration.mk (IdentMap.add
                                  tid (existT _ lang st3, lc3)
                                  (Configuration.threads c1))
                               sc1 mem1)).

  edestruct (@cert_simulation G' sc'' tid PC T'' f_to' f_from') as [T''' HH].
  all: try by desf; eauto.
  { unfold PC. eapply simrel_thread_bigger_sc_memory; eauto.
    { rewrite IdentMap.gss; eauto. }
    { eapply inhabited_le.
      { apply CAP. }
      apply SIMREL_THREAD. }
    { eapply Memory.cap_closed; eauto. apply SIMREL_THREAD. }
    { apply CAP. }
      by apply Memory.max_full_timemap_closed. }  
  { apply fin_exec_imm_s_fair; auto. apply IMMCON0. }
  desc.

  assert
    (exists langst local,
        ⟪ THREAD :
            Basic.IdentMap.find tid PC'.(Configuration.threads) =
            Some (langst, local)
        ⟫ /\
        ⟪ EMPTY : Local.promises local = Memory.bot ⟫)
    as HH.
  { cdes SIMREL2. cdes LOCAL.
    exists (existT _ (thread_lts tid) state). exists local.
    splits; auto.
    red in SIM_PROM. apply Memory.ext.
    ins. rewrite Memory.bot_get.
    destruct (Memory.get loc ts (Local.promises local)) eqn: HH; auto.
    exfalso.
    destruct p as [from msg]. destruct msg.
    { eapply SIM_PROM in HH; eauto.
      desc. apply NCOV. by apply FINALT. }
    eapply SIM_RPROM in HH; eauto.
    desc.
    apply NOISS. eapply w_covered_issued.
    1, 2: by apply COMMON0.    
    split.
    { eapply reservedW; auto.
      1, 2: by apply COMMON0.
      done. }
    apply FINALT. eapply rcoh_S_in_E.
    { apply COMMON0. }
    done. }

  desc.
  destruct langst as [lang' state'].
  assert (lang' = lang); subst.
  { symmetry.
    eapply conf_steps_preserve_lang; eauto.
    unfold PC.
    simpls. rewrite IdentMap.gss. eauto. }
  eapply conf_steps_to_thread_steps in PSTEP; eauto.
  2: { unfold PC. simpls. rewrite IdentMap.gss. eauto. }
  eexists. splits.
  { apply PSTEP. }
  simpls.
Admitted. 
  
Lemma sim_steps PC TS TS' f_to f_from
      (TCSTEPS : (ext_sim_trav_step G sc)^* TS TS')
      (T_FIN: tls_fin TS)
      (SIMREL  : simrel G sc PC TS f_to f_from)
      (FAIR: mem_fair G) :
    exists PC' f_to' f_from',
      ⟪ PSTEP : conf_step＊ PC PC' ⟫ /\
      ⟪ SIMREL : simrel G sc PC' TS' f_to' f_from' ⟫.
Proof using All.
  generalize dependent f_from.
  generalize dependent f_to.
  generalize dependent PC.
  induction TCSTEPS.
  { ins. desf.
    eapply sim_step in H; eauto. desf.
    do 3 eexists. splits; eauto. by eapply inclusion_r_rt; eauto. }
  { ins. exists PC, f_to, f_from. splits; eauto. apply rt_refl. }
  ins.
  eapply IHTCSTEPS1 in SIMREL; auto. 
  desc.
  eapply IHTCSTEPS2 in SIMREL0.
  2: { eapply sim_steps_preserves_fin; eauto. }
  desf. eexists. eexists. eexists. splits.
  2: eauto.
  eapply rt_trans; eauto. 
Qed.
  
(* TODO: rename *)
Lemma reserved_rewrite_helper etc w
      (TCOH : tls_coherent G etc)
      (RCOH : reserve_coherent G etc)
      (IORDCOH : iord_coherent G sc etc)
      (RES  : reserved etc ⊆₁ issued etc ∪₁ eq w)
      (w_ex_is_xacq : W_ex G ⊆₁ W_ex G ∩₁ is_xacq (lab G))
      (ISS'w: issuable G sc etc w):
  reserved etc ∪₁ eq w ∪₁ dom_sb_S_rfrmw G etc (rfi G) (eq w) ≡₁ issued etc ∪₁ eq w.
Proof using WF.
  split.
  2: { rewrite rcoh_I_in_S; eauto. basic_solver. }
  rewrite RES.
  rewrite dom_sb_S_rfrmw_issuable; auto. 
  { basic_solver. }
  rewrite RES. apply set_subset_union_l. split; [| basic_solver].
  apply issued_in_issuable; auto.
Qed. 

Ltac liaW no := destruct no; [by vauto| simpl in *; lia].

Lemma simulation_enum (FAIR: mem_fair G) (IMM_FAIR: imm_s_fair G sc) 
      (w_ex_is_xacq : W_ex G ⊆₁ W_ex G ∩₁ is_xacq (lab G)):
  exists (len: nat_omega)
    (TCtr : nat -> (trav_label -> Prop)),
    << LENP : NOmega.lt_nat_l 0 len >> /\
    ⟪ TRAV: acts_set G ≡₁ ⋃₁ i ∈ (flip NOmega.lt_nat_l len),
                             covered (TCtr i) ⟫ /\

  exists (PRtr : nat -> Configuration.t),
    ⟪ PINIT: PRtr 0 = conf_init prog ⟫ /\
    ⟪ PSTEP: forall i (DOM: NOmega.lt_nat_l (1 + i) len),
        conf_step^* (PRtr i) (PRtr (1 + i)) ⟫ /\

    ⟪ SIMREL: forall i (DOM: NOmega.lt_nat_l i len),
        exists (f_to f_from: actid -> Time.t),
          simrel G sc
                 (PRtr i)
                 (TCtr i)
                 f_to f_from ⟫. 
Proof using All.
  assert (complete G) as CG by apply IMMCON.
  assert (wf_sc G sc) as WFSC by apply IMMCON.

  assert (exists (len : nat_omega)
                 (TCtr : nat -> (trav_label -> Prop)),
             << LENP : NOmega.lt_nat_l 0 len >> /\
             << TCINIT : TCtr 0 = init_tls G >> /\
             << TCSTEP : forall n, NOmega.lt_nat_l (1 + n) len ->
                                   (ext_sim_trav_step G sc)^* (TCtr n) (TCtr (1 + n)) >> /\
             ⟪ TRAV: acts_set G ≡₁ ⋃₁ i ∈ (flip NOmega.lt_nat_l len),
                 covered (TCtr i) ⟫); desc.
  { destruct (classic (fin_exec G)) as [FIN|NFIN].
    { admit. }
    (* { destruct (sim_traversal_trace WF WFSC CG FIN IMMCON) as [lst [TCtr HH]]; desc. *)
    (*   assert (forall n, n < S lst -> etc_coherent G sc (TCtr n)) as ETCN. *)
    (*   { induction n; ins.  *)
    (*     { rewrite TCINIT. now apply ext_init_trav_coherent. } *)
    (*     eapply ext_sim_trav_step_coherence. *)
    (*     apply TCSTEP. lia. } *)
    (*   exists (NOnum (1 + lst)), TCtr. splits; auto. *)
    (*   { ins. lia. } *)
    (*   { ins. apply rt_step. apply TCSTEP. lia. } *)
    (*   split. *)
    (*   { etransitivity; [now apply TCLAST|]. *)
    (*     unfold set_bunion. *)
    (*     red; ins. exists lst. splits; ins. } *)
    (*   apply set_subset_bunion_l. ins. *)
    (*   red in COND. red in COND. *)
    (*   erewrite <- etc_dom with (sc:=sc) (T:=TCtr x); eauto with hahn. } *)

    forward eapply sim_traversal_inf' with (T:=init_tls G);
      eauto using init_tls_fin, init_tls_tls_coherent, init_tls_iord_coherent.
    intros. desc.
    remember (NOmega.add (set_size (exec_tls G)) (NOnum 1)) as len.
    exists len.
    exists sim_enum. (* TODO: composition of reserve_clos and sim_enum? *)
    (* exists (fun i => let (C, I) := sim_enum i in [C # I # I]). *)
    rename i into iq.

    assert (NOmega.lt_nat_l 0 len) as LENn0.
    { subst len. liaW (set_size (exec_tls G)). }
    splits; auto.
    { now rewrite INIT. }
    { intros i DOMi.
      specialize (STEPS i). specialize_full STEPS.
      { subst len. liaW (set_size (exec_tls G)). }
      remember (sim_enum (1 + i)) as etc'. clear Heqetc'.
      apply rtEE in STEPS as [n [_ STEPS]].
      generalize dependent etc'. induction n.
      { ins. simpl in STEPS. destruct STEPS as [-> _]. apply rt_refl. }
      intros etc'' [etc' [STEPS' STEP]].
      eapply rt_trans; [by apply IHn; eauto | ].

      (* cdes STEP. unfolder in STEP0. desc. *)
      (* eapply sim_clos_step2ext_isim_trav_step in STEP. *)

      (* TODO: OLD PROOF *)
      (* =============== *)
      (* forward eapply (@sim_trav_step2ext_sim_trav_step etc' etc'') *)
      (*   as EXT_STEPS; eauto. *)
      (* 2: { by destruct etc', etc''. } *)
      (* eapply sim_trav_steps_coherence; [by eapply pow_rt; eauto| ]. *)
      (* apply COH. *)
      (* subst len. liaW (set_size (graph_steps G)). } *)

      admit. }
    split.
    2: { apply set_subset_bunion_l. intros.
         specialize (COH x). specialize_full COH.
         { red in COND.
           subst len. liaW (set_size (exec_tls G)). }
         apply coveredE in COH; auto. }
    rewrite AuxRel.set_split_comlete with (s' := acts_set G) (s := is_init).
    apply set_subset_union_l. split.
    { red. ins. exists 0. split; auto.
      red. unfolder. eexists (mkTL _ _); ins. splits; eauto.
      apply INIT. do 2 red; ins. split; auto.
      basic_solver. }
    intros e ENIe. specialize (ENUM e). specialize_full ENUM.
    { generalize ENIe. basic_solver. }
    desc. exists i. splits.
    { red. subst len. liaW (set_size (exec_tls G)). }
    red. unfolder. eauto. }
      
  exists len, TCtr. splits; auto.

  assert (FDC : FunctionalDependentChoice).
  { apply functional_choice_imp_functional_dependent_choice.
    red. apply functional_choice. }
  
  set (ntc_pred := fun ntc : nat * Configuration.t =>
                     match ntc with
                     | (n, conf) =>
                         << NLT : NOmega.lt_nat_l n len >> /\
                         << SIMREL : exists f_to f_from,
                             simrel G sc conf (TCtr n) f_to f_from >>
                     end).
  set (ntc_type := { ntc : nat * Configuration.t | ntc_pred ntc}).
  
  assert (ntc_pred (0, conf_init prog)) as NTC_PRED.
  { red. splits; auto.
    do 2 eexists.
    rewrite TCINIT.
    eapply simrel_init. }
  assert (exists start : ntc_type, proj1_sig start = (0, conf_init prog))
    as [start STNTC].
  { unfold ntc_type. exists (exist _ _ NTC_PRED). ins. }

  
  assert (forall n (NLT : NOmega.lt_nat_l n len), tls_fin (TCtr n)) as TCtr_etcfin.
  { clear -WF TCINIT TCSTEP LENP.
    induction n; ins.
    { rewrite TCINIT. apply init_tls_fin. }
    specialize (TCSTEP n NLT).
    eapply sim_steps_preserves_fin; eauto.
    apply IHn. eapply NOmega.lt_lt_nat; eauto. }

  edestruct FDC 
    with (R := fun (ntc ntc' : ntc_type) =>
                 match proj1_sig ntc, proj1_sig ntc' with
                 | (n, conf), (n', conf') =>
                     (NOmega.eqb (NOnum (1 + n)) len -> (n, conf) = (n', conf')) /\
                     (NOmega.lt  (NOnum (1 + n)) len -> 
                      << NEXT    : n'  = 1 + n   >> /\
                      << SIMREL2 : exists f_to' f_from',
                           simrel G sc conf'
                                  (TCtr (1 + n)) f_to' f_from' >> /\
                     << STEPS : conf_step＊ conf conf' >>)
                 end)
         (x0:=start)
    as [TR AA].
  { ins. destruct x as [[n conf] NTCx].
    cdes NTCx. 
    destruct (NOmega.eqb (NOnum (1 + n)) len) eqn:NLST.
    { apply NOmega.eqb_eq in NLST; subst.
      exists (exist _ _ NTCx); ins. split; ins. lia. }


    edestruct sim_steps with (TS:=TCtr n) (TS':=TCtr (1 + n))
      as [conf']; eauto.
    { apply TCSTEP.
      destruct len; ins. destruct n0.
      { lia. }
      apply EqNat.beq_nat_false in NLST. lia. }
    desc.
    enough (exists y : ntc_type, proj1_sig y = (S n, conf')) as [y NTCy].
    { exists y. ins. rewrite NTCy. splits; ins.
      { desf. }
      splits; eauto. }
    enough (ntc_pred (S n, conf')) as BB.
    { exists (exist _ _ BB); ins. }
    red. splits; eauto. ins.
    destruct len; ins. destruct n0.
    { lia. }
    apply EqNat.beq_nat_false in NLST. lia. }
  desf; ins.
  assert (forall n, NOmega.lt_nat_l n len -> fst (proj1_sig (TR n)) = n) as NNTR.
  { clear -AA0 STNTC. induction n.
    { now rewrite STNTC. }
    intros LT.
    specialize (AA0 n).
    assert (NOmega.lt_nat_l n len) as JJ.
    { destruct len; ins. lia. }
    specialize (IHn JJ).
    remember (TR    n)  as tt . destruct tt  as [[i  conf ] NTCtt ]; ins.
    remember (TR (S n)) as tt'. destruct tt' as [[i' conf'] NTCtt']; ins; subst.
    apply AA0. destruct len; auto. }
  exists (fun n => snd (proj1_sig (TR n))).
  splits.
  { now rewrite STNTC. }
  { ins. specialize (AA0 i).
    remember (TR    i)  as tt . destruct tt  as [[n  conf ] NTCtt ]; ins.
    remember (TR (S i)) as tt'. destruct tt' as [[n' conf'] NTCtt']; ins.
    enough (i = n); subst.
    { apply AA0. destruct len; auto. }
    specialize (NNTR i). rewrite <- Heqtt in NNTR. ins.
    rewrite NNTR; auto.
    eapply NOmega.lt_lt_nat; eauto. }
  ins.
  remember (TR    i)  as tt . destruct tt  as [[n  conf ] NTCtt ]; ins.
  enough (i = n); subst.
  { apply NTCtt. }
  specialize (NNTR i). rewrite <- Heqtt in NNTR. ins.
  rewrite NNTR; auto.
Admitted. 

(* Theorem promise2imm_finite *)
(*         (FIN: fin_exec G) : *)
(*   promise_allows prog final_memory. *)
(* Proof using All. *)
(*   assert (FAIR: mem_fair G). *)
(*   { (* TODO: should follow from FIN *) admit. } *)
(*   assert (IMM_FAIR: imm_fair G sc). *)
(*   { (* TODO: should follow from FIN *) admit. } *)
(*   red. *)
(*   destruct simulation as [T [PC H]]; eauto. desc. *)
(*   edestruct sim_covered_exists_terminal as [PC']; eauto. *)
(*   desc. *)
(*   exists PC'. splits; eauto. *)
(*   { eapply rt_trans; eauto. } *)
(*   eapply same_final_memory; eauto.  *)
(* Admitted. *)
  
End PromisingToIMM.
