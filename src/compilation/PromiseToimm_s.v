(******************************************************************************)
(** * A compilation correctness proof from the Promising2 memory model to
      the IMM memory model. *)
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
From imm Require Import ThreadBoundedExecution. 

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
From imm Require Import Traversal.
From imm Require Import TraversalConfig.
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
From hahn Require Import Hahn.


Set Implicit Arguments.
Remove Hints plus_n_O.

Lemma istep_nil_eq_silent thread :
  istep thread nil ≡
  lts_step thread ProgramEvent.silent.
Proof using.
  unfold lts_step. unfold lab_imm_promise.
  split; [|basic_solver].
  unfolder. ins. exists nil. eauto.
Qed.

(* TODO: move *)
Lemma InAE A x (l : list A) : SetoidList.InA eq x l <-> In x l.
Proof using.
  split; [by induction 1; desf; ins; eauto|].
  induction l; ins; desf; eauto using SetoidList.InA.
Qed.

(* TODO: move *)
Lemma NoDupAE A (l : list A) : SetoidList.NoDupA eq l <-> NoDup l.
Proof using.
  split; induction 1; constructor; eauto; rewrite InAE in *; eauto.
Qed.

(* TODO: move *)
Lemma NoDup_map_NoDupA A B (f : A -> B) l :
  SetoidList.NoDupA (fun p p' => f p = f p') l ->
  NoDup (map f l).
Proof using.
  induction 1; ins; constructor; eauto.
  clear -H; intro M; destruct H; induction l; ins; desf;
    eauto using SetoidList.InA.
Qed.

(* TODO: move *)
Lemma etc_dom G sc T (ETCCOH : etc_coherent G sc T):
  ecovered T ∪₁ eissued T ∪₁ reserved T ⊆₁ acts_set G.
Proof.
  destruct T.
  unfold ecovered, eissued; ins.
  assert (tc_coherent G sc etc_TC) by apply ETCCOH.
  unionL; eauto using coveredE, issuedE.
  apply ETCCOH.
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
      (SIMREL : simrel_thread G sc PC (etc_TC T) (reserved T) f_to f_from thread smode)
      (NCOV : NTid_ thread ∩₁ (acts_set G) ⊆₁ ecovered T)
      (FAIR: mem_fair G):
    exists PC' f_to' f_from',
      ⟪ PSTEP : (plain_step MachineEvent.silent thread)＊ PC PC' ⟫ /\
      ⟪ SIMREL : simrel_thread G sc PC' (etc_TC T') (reserved T') f_to' f_from' thread smode ⟫.
Proof using.
  destruct T as [T S].
  destruct T' as [T' S'].
  unfold ecovered in *. simpls.
  eapply plain_sim_step in STEP; eauto.
  desf. eexists. eexists. eexists. splits; eauto.
Qed.

Lemma cert_sim_steps G sc thread PC T T' f_to f_from smode
      (WF : Wf G) (IMMCON : imm_consistent G sc)
      (STEPS : (ext_isim_trav_step G sc thread)⁺ T T')
      (SIMREL : simrel_thread G sc PC (etc_TC T) (reserved T) f_to f_from thread smode)
      (NCOV : NTid_ thread ∩₁ (acts_set G) ⊆₁ ecovered T)
      (FAIR: mem_fair G):
    exists PC' f_to' f_from',
      ⟪ PSTEP : (plain_step MachineEvent.silent thread)＊ PC PC' ⟫ /\
      ⟪ SIMREL : simrel_thread G sc PC' (etc_TC T') (reserved T') f_to' f_from' thread  smode ⟫.
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

Lemma cert_simulation G sc thread PC T S f_to f_from
      (WF : Wf G) (IMMCON : imm_consistent G sc)
      (SIMREL : simrel_thread G sc PC T S f_to f_from thread sim_certification)
      (NCOV : NTid_ thread ∩₁ (acts_set G) ⊆₁ covered T)
      (FIN: fin_exec G)
      (FAIR: mem_fair G)
      (IMM_FAIR: imm_s_fair G sc):
  exists T' S' PC' f_to' f_from',
    ⟪ FINALT : (acts_set G) ⊆₁ covered T' ⟫ /\
    ⟪ PSTEP  : (plain_step MachineEvent.silent thread)＊ PC PC' ⟫ /\
    ⟪ SIMREL : simrel_thread G sc PC' T' S' f_to' f_from' thread sim_certification⟫.
Proof using.
  assert (etc_coherent G sc (mkETC T S)) as ETCCOH.
  { apply SIMREL. }
  assert (complete G) as CG by apply IMMCON.
  assert (wf_sc G sc) as WFSC by apply IMMCON.  

  generalize (sim_step_cov_full_traversal WF WFSC CG FIN IMMCON ETCCOH NCOV); intros H.
  destruct H as [T'].
  1,2: by apply SIMREL.
  desc.
  destruct T' as [T' S'].
  exists T', S'. apply rtE in H.
  destruct H as [H|H].
  { red in H. desf.
    eexists. eexists. eexists.
    splits; eauto.
    apply rtE. left. red. eauto. }
  eapply cert_sim_steps in H; auto.
  2: by eauto.
  desf. eexists. eexists. eexists. splits; eauto.
Qed.

Lemma simrel_thread_bigger_sc_memory G sc T S thread f_to f_from threads memory
      sc_view memory' sc_view'
      lang state local
      (WF : Wf G) (IMMCON : imm_consistent G sc)
      (THREAD     : IdentMap.find thread threads = Some (existT _ lang state, local))
      (INHAB      : Memory.inhabited memory' )
      (CLOSED_MEM : Memory.closed memory')
      (MEM_LE : Memory.le memory memory')
      (SС_CLOSED  : Memory.closed_timemap sc_view' memory')
      (SIMREL : simrel_thread G sc (Configuration.mk threads sc_view memory )
                              T S f_to f_from thread  sim_certification) :
  simrel_thread G sc (Configuration.mk threads sc_view' memory') T S f_to f_from
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

Section PromiseToIMM.
  
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
Hypothesis (THREADS_BOUND : threads_bound G tb).

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
         (init_trav G) (is_init ∩₁ acts_set G)
         (fun _ => tid_init) (fun _ => tid_init).
Proof using ALLRLX IMMCON PROG_EX TNONULL WF FRELACQ RMWREX.
  red; splits; red; splits; auto.
  { by apply ext_init_trav_coherent. }
  { simpls. basic_solver. }
  { ins. split; intros [INIT GG]; exfalso.
    { apply (init_w WF) in INIT.
      apply (dom_l (wf_rmwD WF)) in RMW.
      apply seq_eqv_l in RMW.
      type_solver. }
    apply (rmw_in_sb WF) in RMW.
    apply no_sb_to_init in RMW.
    apply seq_eqv_r in RMW. desf. }
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
    { ins. destruct H. desf. }
    all: ins; exfalso.
    apply Execution_eco.no_co_to_init in H1; auto.
    apply seq_eqv_r in H1.
    destruct H0. desf. }
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
    apply seq_eqv_r in HH. destruct HH as [HH [AA BB]].
    red in HH. destruct HH as [CC [HH _]]. subst.
    apply (init_w WF) in AA.
    type_solver. }
  { apply dom_rmw_in_R_ex. }
  { red. splits; ins.
    3: { match goal with
         | H : co _ _ _ |- _ => rename H into CO
         end.
         apply Execution_eco.no_co_to_init in CO; auto.
         2: { apply imm_s_hb.coherence_sc_per_loc.
              apply IMMCON. }
         unfolder in *. desf. }
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
      destruct ISSB as [II _].
      destruct b.
      2: by inv II.
      unfold val in VAL.
      rewrite (wf_init_lab WF) in VAL.
      inv VAL. }
    { red. splits; auto.
      { right. splits; auto. apply ISSB. }
      red. ins. unfold LocFun.find, TimeMap.bot.
      apply max_value_bot_f. }
    red. unfold View.unwrap, View.bot, TimeMap.bot. simpls.
    ins. eexists. eexists. eexists.
    unfold Memory.get, Cell.get. simpls. }
  { red; simpls. }
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
    destruct H as [H _]. simpls. }
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

Lemma sim_thread_covered_exists_terminal PC thread T S f_to f_from
      (FINALT : Tid_ thread ∩₁ acts_set G ⊆₁ covered T)
      (SIMREL : simrel G sc PC T S f_to f_from) :
  exists PC',
    ⟪ STEP : (conf_step)^? PC PC' ⟫ /\
    ⟪ SIMREL : simrel G sc PC' T S f_to f_from ⟫ /\
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
    { apply COMMON. }
    split.
    { eapply reservedW; auto.
      { apply COMMON. }
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

Lemma sim_covered_exists_terminal T S PC f_to f_from
      (FINALT : acts_set G ⊆₁ covered T)
      (SIMREL : simrel G sc PC T S f_to f_from) :
  exists PC',
    ⟪ STEPS : conf_step＊ PC PC' ⟫ /\
    ⟪ SIMREL : simrel G sc PC' T S f_to f_from ⟫ /\
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

Lemma same_final_memory T S PC f_to f_from
      (FINALT : acts_set G ⊆₁ covered T)
      (SIMREL : simrel G sc PC T S f_to f_from) :
  forall l,
    final_memory_state (Configuration.memory PC) l = Some (final_memory l).
Proof using All.
  assert (etc_coherent G sc (mkETC T S)) as ETCCOH by apply SIMREL.
  assert (tc_coherent G sc T) as TCCOH by apply ETCCOH.
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
       { by apply (reservedW WF ETCCOH). }
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
    assert (S w) as WS.
    { by apply (etc_I_in_S ETCCOH). }
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
         { apply TCCOH in ISS. apply ISS. }
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
  { apply TCCOH in ISS. apply ISS. }
  { by rewrite LOC. }
  2: { exfalso. apply LAST. eauto. }
  assert (S b) as BS.
  { by apply (etc_I_in_S ETCCOH). }
  assert (S w) as WS.
  { by apply (etc_I_in_S ETCCOH). }
  eapply f_to_co_mon with (I:=S) in CO; eauto.
  apply Memory.max_ts_spec in INMEM.
  destruct INMEM as [_ CC].
  rewrite <- TO in CC.
  exfalso. eapply Time.lt_strorder.
  eapply TimeFacts.lt_le_lt; eauto.
Qed.

Lemma sim_step PC T S T' S' f_to f_from
      (STEP : ext_sim_trav_step G sc (mkETC T S) (mkETC T' S'))
      (ETC_FIN: etc_fin (mkETC T S))
      (SIMREL : simrel G sc PC T S f_to f_from)
      (FAIR: mem_fair G) :
    exists PC' f_to' f_from',
      ⟪ PSTEP : (conf_step)^? PC PC' ⟫ /\
      ⟪ SIMREL : simrel G sc PC' T' S' f_to' f_from' ⟫.
Proof using All.
  destruct STEP as [thread STEP].
  forward eapply isim_step_preserves_fin as FIN'; eauto. 
  cdes SIMREL. cdes COMMON.
  eapply plain_sim_step in STEP; eauto.
  2: { split; eauto. apply THREADS.
       assert (exists e, thread = tid e /\ acts_set G e /\ ~ is_init e) as [e].
       { apply ext_sim_trav_step_to_step in STEP.
         desc. exists e.
         assert (acts_set G e) as EE.
         { eapply ext_itrav_stepE; eauto. }
         splits; auto.
         eapply ext_itrav_step_ninit; eauto. }
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

  edestruct (@cert_simulation G' sc'' tid PC T'' S'' f_to' f_from') as [T''' HH].
  all: try by desf; eauto.
  { unfold PC. eapply simrel_thread_bigger_sc_memory; eauto.
    { rewrite IdentMap.gss; eauto. }
    { eapply inhabited_le.
      { apply CAP. }
      apply SIMREL_THREAD. }
    { eapply Memory.cap_closed; eauto. apply SIMREL_THREAD. }
    { apply CAP. }
      by apply Memory.max_full_timemap_closed. }
  { (* TODO: follows from FIN'0 : fin_exec G' *)
    admit. }
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
    { apply COMMON0. }
    split.
    { eapply reservedW; auto.
      { apply COMMON0. }
      done. }
    apply FINALT. eapply etc_S_in_E.
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
      (ETC_FIN: etc_fin TS)
      (SIMREL  : simrel G sc PC (etc_TC TS) (reserved TS) f_to f_from)
      (FAIR: mem_fair G) :
    exists PC' f_to' f_from',
      ⟪ PSTEP : conf_step＊ PC PC' ⟫ /\
      ⟪ SIMREL : simrel G sc PC' (etc_TC TS') (reserved TS') f_to' f_from' ⟫.
Proof using All.
  generalize dependent f_from.
  generalize dependent f_to.
  generalize dependent PC.
  induction TCSTEPS.
  { ins. desf.
    destruct x as [T S].
    destruct y as [T' S'].
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
  
Lemma simulation 
      (FAIR: mem_fair G)
      (FIN: fin_exec G) :
  exists T S PC f_to f_from,
    ⟪ FINALT : (acts_set G) ⊆₁ covered T ⟫ /\
    ⟪ PSTEP  : conf_step＊ (conf_init prog) PC ⟫ /\
    ⟪ SIMREL : simrel G sc PC T S f_to f_from ⟫.
Proof using All.
      (*  *)
      (* (IMM_FAIR: imm_fair G sc): *)
  assert (complete G) as CG by apply IMMCON.
  assert (wf_sc G sc) as WFSC by apply IMMCON.
  generalize (sim_traversal WF WFSC CG FIN IMMCON); ins; desc.
  destruct T as [T S].
  exists T, S.
  apply rtE in H.
  destruct H as [H|H].
  { red in H. desf.
    eexists. eexists. eexists.
    splits; auto.
    { apply rtE. left. red. eauto. }
    unfold ext_init_trav in *. inv H.
    apply simrel_init. }
  apply inclusion_t_rt in H.
  eapply sim_steps in H; eauto.
  3: { by apply simrel_init. }
  2: { by apply init_etc_fin. }
  desf.
  eexists. eexists. eexists.
  splits; eauto.
Qed.

From imm Require Import SimTraversal.
From imm Require Import SimTraversalProperties.
From imm Require Import SimTravClosure.
From imm Require Import TraversalConfigAlt.

Lemma tc_coh2etc_coh tc (COH: tc_coherent G sc tc)
      (w_ex_is_xacq : W_ex G ⊆₁ W_ex G ∩₁ is_xacq (lab G)):
  etc_coherent G sc (mkETC tc (issued tc)). 
Proof using WF IMMCON.
  forward eapply tc_coherent_implies_tc_coherent_alt as COH_ALT; eauto.
  { apply IMMCON. }
  inversion COH_ALT.
  destruct tc as [C I]. simpl in *. 
  split; auto; unfold ecovered, eissued; simpl.
  { basic_solver. }
  { etransitivity; [| by apply tc_fwbob_I]. apply dom_rel_mori.
    rewrite <- !seqA. hahn_frame. apply imm_bob.sb_from_f_in_fwbob. }
  { forward eapply dom_detour_rmwrfi_rfe_acq_sb_issued as IN; eauto. }
  { forward eapply dom_wex_sb_issued as IN; eauto. }
  { unfold dom_sb_S_rfrmw. simpl.
    rewrite rmw_W_ex. repeat rewrite codom_seq. rewrite codom_eqv.
    rewrite set_interC, <- dom_eqv1.
    rewrite w_ex_is_xacq. forward eapply dom_wex_sb_issued as IN; eauto. }
  { sin_rewrite detour_rfe_data_rfi_rmw_rppo_in_detour_rfe_ppo; auto.
    rewrite seqA. forward eapply dom_detour_rfe_ppo_issued as IN; eauto. }
  { rewrite (dom_l (wf_detourD WF)); auto. 
    rewrite detour_in_ar, imm_s_ppo.rmw_in_ar_int, ar_int_in_ar; eauto.
    etransitivity; [| by apply tc_I_ar_rf_ppo_loc_I]. apply dom_rel_mori.
    hahn_frame. rewrite <- ct_unit, <- ct_step. apply seq_mori; basic_solver 10. }
  forward eapply TraversalProperties.issuable_W_ex_in_codom_I_rfrmw as IN; eauto.
  rewrite <- IN, <- issued_in_issuable; auto.
Qed.

Lemma dom_sb_S_rfrmw_issuable etc r' S'
      (COH: tc_coherent G sc (etc_TC etc))
      (RES_ISS': reserved etc ⊆₁ issuable G sc (etc_TC etc))
      (w_ex_is_xacq : W_ex G ⊆₁ W_ex G ∩₁ is_xacq (lab G)):
  dom_sb_S_rfrmw G etc r' S' ⊆₁ eissued etc.
Proof.
  unfold dom_sb_S_rfrmw.
  rewrite rmw_W_ex, w_ex_is_xacq. repeat rewrite codom_seq.
  rewrite codom_eqv, set_interC. rewrite <- dom_eqv1.
  simpl. rewrite RES_ISS'. by apply dom_wex_sb_issuable. 
Qed.


Lemma itrav_step2ext_itrav_step_cover (C I: actid -> Prop) (e: actid)
      (COH: tc_coherent G sc (mkTC C I))
      (w_ex_is_xacq : W_ex G ⊆₁ W_ex G ∩₁ is_xacq (lab G))
      (STEP: itrav_step G sc e (mkTC C I) (mkTC (C ∪₁ eq e) I)):
  ext_itrav_step G sc e (mkETC (mkTC C I) I) (mkETC (mkTC (C ∪₁ eq e) I) I).
Proof.
  forward eapply trav_step_coherence as COH2; [by red; eauto| done |]. 
  inversion STEP.
  2: { red in H. desc. simpl in *. destruct NISS. apply ISSEQ. basic_solver. }
  red in H. desc. red. splits; unfold ecovered, eissued; simpl in *; eauto. 
  by apply tc_coh2etc_coh.
Qed.

Lemma etc_coh_extend_reserved tc w
      (w_ex_is_xacq : W_ex G ⊆₁ W_ex G ∩₁ is_xacq (lab G))
      (WEXw: W_ex G w)
      (NISS: ~ issued tc w)
      (ISS'w: issuable G sc tc w)
      (COH: etc_coherent G sc (mkETC tc (issued tc))):
  etc_coherent G sc (mkETC tc (issued tc ∪₁ eq w)). 
Proof using WF IMMCON.
  pose proof COH as COH'. destruct COH'.
  destruct tc as [C I] eqn:TC. 
  split; auto; unfold ecovered, eissued in *; simpl in *.
  { apply W_ex_in_E in WEXw; auto. basic_solver. }
  { basic_solver. }
  { basic_solver. }
  { rewrite id_union. repeat rewrite seq_union_r. rewrite dom_union. 
    apply set_subset_union_l. split; auto.
    etransitivity; [| by apply ISS'w]. apply dom_rel_mori. hahn_frame.
    apply imm_bob.sb_from_f_in_fwbob. }
  { rewrite id_union. repeat rewrite seq_union_r. rewrite dom_union. 
    apply set_subset_union_l. split; auto.
    replace I with (issued tc) by vauto.
    etransitivity; [| by eapply dom_detour_rmwrfi_rfe_acq_sb_issuable; eauto].
    apply dom_rel_mori. repeat hahn_frame_l. basic_solver. }
  { rewrite id_union. repeat rewrite seq_union_r. rewrite dom_union. 
    apply set_subset_union_l. split; auto.
    replace I with (issued tc) by vauto.
    etransitivity; [| by eapply dom_wex_sb_issuable; eauto].
    apply dom_rel_mori. repeat hahn_frame_l. basic_solver. }
  { rewrite dom_sb_S_rfrmw_issuable; auto.
    { simpl. basic_solver. }
    simpl. replace I with (issued tc) by vauto.
    rewrite issued_in_issuable at 1; vauto. basic_solver. }
  { rewrite id_union. repeat rewrite seq_union_r. rewrite dom_union.
    apply set_subset_union_l. split; auto.
    sin_rewrite detour_rfe_data_rfi_rmw_rppo_in_detour_rfe_ppo; auto.
    replace I with (issued tc) by vauto.
    etransitivity; [| by apply dom_detour_rfe_ppo_issuable; eauto].
    apply dom_rel_mori. hahn_frame. basic_solver. }
  { rewrite id_union. repeat rewrite seq_union_r. rewrite dom_union.
    apply set_subset_union_l. split; auto.
    rewrite (dom_l (wf_detourD WF)); auto. 
    rewrite detour_in_ar, imm_s_ppo.rmw_in_ar_int, ar_int_in_ar; eauto.
    etransitivity; [| by apply ISS'w]. apply dom_rel_mori.
    hahn_frame. rewrite <- ct_unit, <- ct_step. apply seq_mori; basic_solver. }
  rewrite set_inter_union_l. apply set_subset_union_l. split; auto.
  replace I with (issued tc) by vauto.
  rewrite <- TraversalProperties.issuable_W_ex_in_codom_I_rfrmw; try by vauto.
  basic_solver. 
Qed. 

Lemma etc_coh_extend_reserved_rmw tc r w
      (w_ex_is_xacq : W_ex G ⊆₁ W_ex G ∩₁ is_xacq (lab G))
      (WEXw: W_ex G w)
      (NISS: ~ issued tc w)
      (COV'r: coverable G sc tc r)
      (COH: etc_coherent G sc (mkETC tc (issued tc))):
  etc_coherent G sc (mkETC tc (issued tc ∪₁ eq w)). 
Proof using WF IMMCON.
  pose proof COH as COH'. destruct COH'.
  destruct tc as [C I] eqn:TC. 
  split; auto; unfold ecovered, eissued in *; simpl in *.
  { apply W_ex_in_E in WEXw; auto. basic_solver. }
  { basic_solver. }
  { basic_solver. }
  { rewrite id_union. repeat rewrite seq_union_r. rewrite dom_union. 
    apply set_subset_union_l. split; auto.
    (* etransitivity; [| by apply ISS'w]. apply dom_rel_mori. hahn_frame. *)
    (* apply imm_bob.sb_from_f_in_fwbob.  *)
    admit. }
  { rewrite id_union. repeat rewrite seq_union_r. rewrite dom_union. 
    apply set_subset_union_l. split; auto.
    replace I with (issued tc) by vauto.
    etransitivity; [| by eapply dom_detour_rmwrfi_rfe_acq_sb_issuable; eauto].
    apply dom_rel_mori. repeat hahn_frame_l. 
    (* basic_solver.  *)
    admit. 
  }
  { rewrite id_union. repeat rewrite seq_union_r. rewrite dom_union. 
    apply set_subset_union_l. split; auto.
    admit. 
    (* replace I with (issued tc) by vauto. *)
    (* etransitivity; [| by eapply dom_wex_sb_issuable; eauto]. *)
    (* apply dom_rel_mori. repeat hahn_frame_l. basic_solver.  *)
}
  { unfold dom_sb_S_rfrmw. simpl. 
    (* rewrite dom_sb_S_rfrmw_issuable; auto. *)
    (* { simpl. basic_solver. } *)
    (* simpl. replace I with (issued tc) by vauto. *)
    (* rewrite issued_in_issuable at 1; vauto. basic_solver.  *)
    admit. 
  }
  { rewrite id_union. repeat rewrite seq_union_r. rewrite dom_union.
    apply set_subset_union_l. split; auto.
    admit. 
    (* sin_rewrite detour_rfe_data_rfi_rmw_rppo_in_detour_rfe_ppo; auto. *)
    (* replace I with (issued tc) by vauto. *)
    (* etransitivity; [| by apply dom_detour_rfe_ppo_issuable; eauto]. *)
    (* apply dom_rel_mori. hahn_frame. basic_solver.  *)
}
  { rewrite id_union. repeat rewrite seq_union_r. rewrite dom_union.
    apply set_subset_union_l. split; auto.
    (* rewrite (dom_l (wf_detourD WF)); auto.  *)
    (* rewrite detour_in_ar, imm_s_ppo.rmw_in_ar_int, ar_int_in_ar; eauto. *)
    (* etransitivity; [| by apply ISS'w]. apply dom_rel_mori. *)
    (* hahn_frame. rewrite <- ct_unit, <- ct_step. apply seq_mori; basic_solver. *)
    admit. 
  }
  admit. 
  (* rewrite set_inter_union_l. apply set_subset_union_l. split; auto. *)
  (* replace I with (issued tc) by vauto. *)
  (* rewrite <- TraversalProperties.issuable_W_ex_in_codom_I_rfrmw; try by vauto. *)
  (* basic_solver.  *)
Admitted. 


Notation "'[' C '#' I '#' R ']'" := (mkETC (mkTC C I) R). 
  
Lemma itrav_step2ext_itrav_step_issue (C I: actid -> Prop) (e: actid)
      (w_ex_is_xacq : W_ex G ⊆₁ W_ex G ∩₁ is_xacq (lab G))
      (COH: tc_coherent G sc (mkTC C I))
      (STEP: itrav_step G sc e (mkTC C I) (mkTC C (I ∪₁ eq e))):
  ((ext_itrav_step G sc e ⨾ ⦗eq [C # I # I ∪₁ eq e]⦘)^? ⨾ 
                  ⦗etc_coherent G sc⦘ ⨾ (ext_itrav_step G sc e))
                         [C # I # I]
                         [C # I ∪₁ eq e # I ∪₁ eq e].
Proof.
  forward eapply trav_step_coherence as COH2; [by red; eauto| done |]. 
  inversion STEP.
  { red in H. desc. simpl in *. destruct NEXT. apply COVEQ. basic_solver. }
  red in H. desc. unfold ecovered, eissued; simpl in *.
  destruct (classic (W_ex G e)) as [WEXe | NWEXe].
  2: { eexists. splits; [by apply r_refl| ].
       apply seq_eqv_l. split; [by apply tc_coh2etc_coh| ]. 
       red. splits.
       2: { apply tc_coh2etc_coh; eauto. }
       right. left. unfold ecovered, eissued; simpl in *. splits; eauto.
       { tauto. }
       rewrite set_unionA, set_unionC with (s := eq e), <- set_unionA.
       rewrite set_union_absorb_r with (s := dom_sb_S_rfrmw _ _ _ _); auto.
       rewrite dom_sb_S_rfrmw_issuable; auto.
       rewrite <- issued_in_issuable; auto. }
  forward eapply (@etc_coh_extend_reserved (mkTC C I) e) as COH'; eauto.
  { apply tc_coh2etc_coh; auto. }
  simpl in COH'. remember [C # I # I ∪₁ eq e] as tc'.
  exists tc'. split.
  { apply r_step, seq_eqv_r. split; auto. 
    red. splits; auto. 
    do 2 right. subst tc'. splits; eauto. }
  apply seq_eqv_l. split; auto. 
  red. splits; [| subst tc'; vauto]. 
  2: { apply tc_coh2etc_coh; auto. }
  right. left. splits; vauto. simpl. split; [basic_solver| ]. 
  rewrite dom_sb_S_rfrmw_issuable; auto.
  { basic_solver. }
  apply set_subset_union_l. split; [| basic_solver].
  rewrite <- issued_in_issuable; auto.
Qed.

(* (* TODO: move morphisms from that file *) *)
(* From imm Require Import IordTraversal. *)
(* (* TODO: move upper *) *)
(* From imm Require Import SimTravClosure. *)

Lemma eits_helper C I e
      (COH: tc_coherent G sc (mkTC C I))
      (w_ex_is_xacq : W_ex G ⊆₁ W_ex G ∩₁ is_xacq (lab G))
      (STEPS: (ext_isim_trav_step G sc (tid e))＊ (mkETC (mkTC C I) (I ∪₁ eq e))
                                               (mkETC (mkTC C (I ∪₁ eq e)) (I ∪₁ eq e)))
  : (ext_isim_trav_step G sc (tid e))＊ (mkETC (mkTC C I) I)
                                       (mkETC (mkTC C (I ∪₁ eq e)) (I ∪₁ eq e)).
Proof.  
  eapply transitive_rt; [| by apply STEPS].
  destruct (classic (I e)).
  { replace (I ∪₁ eq e) with I by admit. 
    apply rt_refl. }
  apply rt_step. apply ext_reserve_trav_step. red. splits.
  2: { apply etc_coh_extend_reserved; auto. 
Abort. 


(* TODO: move to ExtTraversal *)
Global Add Parametric Morphism : mkETC with signature
       same_trav_config ==> (@set_equiv actid) ==> same_ext_trav_config as mkETC_more.
Proof using. by unfold same_trav_config; ins; split; ins; desf; apply H. Qed.

Global Add Parametric Morphism : (ext_itrav_step G sc) with signature
    eq ==> same_ext_trav_config ==> same_ext_trav_config ==> iff as
        ext_itrav_step_more.
Proof using. Admitted.


(* TODO: move to ExtTraversalConfig? *)
Lemma same_etc_extensionality (tc1 tc2: ext_trav_config)
      (EQUIV: same_ext_trav_config tc1 tc2):
  tc1 = tc2.
Proof.
  destruct tc1, tc2, etc_TC, etc_TC0. red in EQUIV. desc. simpl in *.
  f_equal; [f_equal| ]; apply IordTraversal.set_extensionality; vauto.
Qed. 

Lemma ext_isim_trav_step_more_helper:
  forall (y : thread_id) (x y0 : ext_trav_config),
  same_ext_trav_config x y0 ->
  forall x0 y1 : ext_trav_config,
  same_ext_trav_config x0 y1 ->
  ext_isim_trav_step G sc y x x0 -> ext_isim_trav_step G sc y y0 y1. 
Proof.
  intros t tc1 tc2 SAME tc1' tc2' SAME' STEP.
  apply same_etc_extensionality in SAME, SAME'. congruence. 
Qed.

Global Add Parametric Morphism : (ext_isim_trav_step G sc) with signature
    eq ==> same_ext_trav_config ==> same_ext_trav_config ==> iff as
        ext_isim_trav_step_more.
Proof using.
  ins; split; apply ext_isim_trav_step_more_helper.
  3, 4: symmetry. all: done. 
Qed. 


(* Lemma dom_sb_S_rfrmw_issuable' etc r' S' *)
(*       (COH: tc_coherent G sc (etc_TC etc)) *)
(*       (RES_ISS': reserved etc ⊆₁ issuable G sc (etc_TC etc)) *)
(*       (w_ex_is_xacq : W_ex G ⊆₁ W_ex G ∩₁ is_xacq (lab G)): *)
(*   dom_sb_S_rfrmw G etc r' S' ≡₁ eissued etc. *)
(* Proof. *)
(*   rewrite rmw_W_ex, w_ex_is_xacq. repeat rewrite codom_seq. *)
(*   rewrite codom_eqv, set_interC. rewrite <- dom_eqv1. *)
(*   simpl. rewrite RES_ISS'. by apply dom_wex_sb_issuable.  *)
(* Qed. *)

(* TODO: rename *)
Lemma reserved_rewrite_helper etc w
      (COH: etc_coherent G sc etc)
      (RES: reserved etc ⊆₁ eissued etc ∪₁ eq w)
      (w_ex_is_xacq : W_ex G ⊆₁ W_ex G ∩₁ is_xacq (lab G))
      (ISS'w: issuable G sc (etc_TC etc) w):
  reserved etc ∪₁ eq w ∪₁ dom_sb_S_rfrmw G etc (rfi G) (eq w) ≡₁ eissued etc ∪₁ eq w.
Proof using WF.
  split.
  2: { rewrite etc_I_in_S; basic_solver. }
  rewrite RES.
  rewrite dom_sb_S_rfrmw_issuable; auto. 
  { basic_solver. }
  { apply COH. }
  rewrite RES. apply set_subset_union_l. split; [| basic_solver].
  unfold eissued. apply issued_in_issuable, COH.
Qed. 

  
  (* ext_itrav_step G sc w [C # I # I] *)
  (*   [ecovered [C # I # I] # eissued [C # I # I] ∪₁ eq w *)
  (*   # I ∪₁ eq w ∪₁ dom_sb_S_rfrmw G [C # I # I] (rfi G) (eq w)] *)

    (* assert (R' ∪₁ eq w ∪₁ dom_sb_S_rfrmw G [C # I # R'] (rfi G) (eq w) ≡₁ I ∪₁ eq w) as RES'_ALT. *)
    (* { arewrite (R' ∪₁ eq w ≡₁ I ∪₁ eq w). *)
    (*   { destruct RES'; rewrite H; basic_solver. } *)
    (*   split; [| basic_solver]. rewrite dom_sb_S_rfrmw_issuable; auto. *)
    (*   { basic_solver. } *)
    (*   simpl. rewrite RES'_. apply set_subset_union_l. split. *)
    (*   { rewrite <- issued_in_issuable; auto. } *)
    (*   basic_solver. } *)

(* Lemma eis_add_res (tc: trav_config) (C I C' I' R': actid -> Prop) *)
(*       (e: actid) (r w: actid) *)
(*       (RMWrw: rmw G r w) *)
(*       (COV'r: coverable G sc (mkTC C I) r) *)
(*       (NCOVr: ~ C r) *)
(*       (w_ex_is_xacq : W_ex G ⊆₁ W_ex G ∩₁ is_xacq (lab G)) *)
(*       (STEP: ext_itrav_step G sc e [C # I # I] [C' # I' # I']) *)
(*       (COH: tc_coherent G sc (mkTC C I)): *)
(*   ext_itrav_step G sc e [C # I # I ∪₁ eq w] [C' # I' # I' ∪₁ eq w]. *)
(* Proof. *)
(*   assert (~ I w) as NIw. *)
(*   { intros Iw. admit. } *)
(*   red. splits. *)
(*   2: { eapply etc_coh_extend_reserved; auto. *)
(*        { eexists. eauto. } *)
(*        {  *)


Lemma isim_trav_step2ext_isim_trav_step (tc1 tc2: trav_config) t
      (COH1: tc_coherent G sc tc1)
      (STEP: isim_trav_step G sc t tc1 tc2)
      (w_ex_is_xacq : W_ex G ⊆₁ W_ex G ∩₁ is_xacq (lab G)):
  (ext_isim_trav_step G sc t)^* (mkETC tc1 (issued tc1)) (mkETC tc2 (issued tc2)).
Proof.
  forward eapply sim_trav_step_coherence as COH2; [by red; eauto| done |]. 

  inversion STEP; subst.
  { apply rt_step. destruct tc1. simpl in *.
    eapply ext_fence_trav_step, itrav_step2ext_itrav_step_cover; eauto. }
  { apply rt_step. destruct tc1. simpl in *.
    eapply ext_read_trav_step, itrav_step2ext_itrav_step_cover; eauto. }
  { destruct tc1 as [C I] eqn:TC1. simpl in *.
    assert (issuable G sc tc1 w) as ISS'w.
    { inversion TS; red in H; desc; simpl in *.
      2: congruence. 
      destruct NEXT. apply COVEQ. basic_solver. }
    apply itrav_step2ext_itrav_step_issue in TS as [tc' [STEPres STEP']]; auto.
    apply seq_eqv_l in STEP' as [COH' STEP'].

    destruct tc' as [[C' I'] R'].
    assert (C' = C /\ I' = I /\ (R' = I \/ R' = I ∪₁ eq w)) as [-> [-> RES']].
    { destruct STEPres.
      { inversion H. auto. }
      apply seq_eqv_r in H. desc. inversion H0. auto. }
    assert (R' ⊆₁ I ∪₁ eq w) as RES'_.
    { destruct RES'; basic_solver. } 
        
    apply rt_unit. exists [C # I # R']. split.
    { destruct RES' as [-> | ->]; [by apply rt_refl| ]. 
      apply rt_step. apply ext_reserve_trav_step. red. splits; vauto. }
  
    forward eapply ext_rlx_write_promise_step 
      with (T := [C # I # R']) (sc := sc) as WSTEP; eauto.
    { eapply ext_itrav_step_more; try by vauto.
      rewrite reserved_rewrite_helper; vauto. }
    rewrite reserved_rewrite_helper in WSTEP; vauto. }
  { apply rt_step. destruct tc1. simpl in *.
    eapply ext_rlx_write_cover_step, itrav_step2ext_itrav_step_cover; eauto. }
  { destruct tc1 as [C I] eqn:TC1. simpl in *.

    assert (tc_coherent G sc (mkTC C (I ∪₁ eq w))) as COH1'. 
    { simpl. eapply trav_step_coherence; [| by apply COH1]. red. eauto. }

    apply itrav_step2ext_itrav_step_issue in TS1 as [tc' [STEPres STEP']]; auto.
    apply seq_eqv_l in STEP' as [COH' STEP'].
    destruct tc' as [[C' I'] R'].
    assert (C' = C /\ I' = I /\ (R' = I \/ R' = I ∪₁ eq w)) as [-> [-> RES']].
    { destruct STEPres.
      { inversion H. auto. }
      apply seq_eqv_r in H. desc. inversion H0. auto. }
    assert (R' ⊆₁ I ∪₁ eq w) as RES'_.
    { destruct RES'; basic_solver. } 

    apply rt_unit. exists [C # I # R']. split.
    { destruct RES' as [-> | ->]; [by apply rt_refl| ]. 
      apply rt_step. apply ext_reserve_trav_step. red. splits; vauto. }

    assert (issuable G sc (mkTC C I) w) as ISS'w.
    { apply issuable_add_eq_iff; auto.
      apply issued_in_issuable; basic_solver. }
  
    forward eapply ext_rel_write_step with (T := [C # I # R']) (sc := sc)
                                           as WSTEP; eauto.
    { rewrite reserved_rewrite_helper; vauto. }
    { rewrite reserved_rewrite_helper; try by vauto.
      unfold ecovered, eissued. simpl.
      apply itrav_step2ext_itrav_step_cover; auto. }
    rewrite reserved_rewrite_helper in WSTEP; vauto. }  
  { destruct tc1 as [C I] eqn:TC1. simpl in *.
    apply rt_step. apply ext_rlx_rmw_cover_step; auto. 
    { apply itrav_step2ext_itrav_step_cover; auto. }
    apply itrav_step2ext_itrav_step_cover; auto.
    unfold ecovered. simpl.
    eapply trav_step_coherence; [| by apply COH1]. red. eauto. }

  { 

    (* destruct tc1 as [C I] eqn:TC1. simpl in *. *)
    (* apply rt_unit. eexists. split. *)
    (* { replace (tid r) with (tid w). *)
    (*   2: { symmetry. erewrite wf_rmwt; eauto. } *)
    (*   apply rt_step. apply ext_reserve_trav_step. red. splits; vauto. *)
    (*   apply etc_coh_extend_reserved; eauto. *)
    (*   { vauto. } *)
    admit. }

Admitted. 



Lemma simulation_enum (FAIR: mem_fair G) (IMM_FAIR: imm_s_fair G sc) :
  exists (len: nat_omega)
    (TCtr : nat -> ext_trav_config),
    << LENP : NOmega.lt_nat_l 0 len >> /\
    ⟪ TRAV: acts_set G ≡₁ ⋃₁ i ∈ (flip NOmega.lt_nat_l len),
                             ecovered (TCtr i) ⟫ /\

  exists (PRtr : nat -> Configuration.t),
    ⟪ PINIT: PRtr 0 = conf_init prog ⟫ /\
    ⟪ PSTEP: forall i (DOM: NOmega.lt_nat_l (1 + i) len),
        conf_step^* (PRtr i) (PRtr (1 + i)) ⟫ /\

    ⟪ SIMREL: forall i (DOM: NOmega.lt_nat_l i len),
        exists (f_to f_from: actid -> Time.t),
          simrel G sc
                 (PRtr i)
                 (etc_TC (TCtr i))
                 (reserved (TCtr i))
                 f_to f_from ⟫. 
Proof using All.
  assert (complete G) as CG by apply IMMCON.
  assert (wf_sc G sc) as WFSC by apply IMMCON.

  assert (exists (len : nat_omega)
                 (TCtr : nat -> ext_trav_config),
             << LENP : NOmega.lt_nat_l 0 len >> /\
             << TCINIT : TCtr 0 = ext_init_trav G >> /\
             << TCSTEP : forall n, NOmega.lt_nat_l (1 + n) len ->
                                   (ext_sim_trav_step G sc)^* (TCtr n) (TCtr (1 + n)) >> /\
             ⟪ TRAV: acts_set G ≡₁ ⋃₁ i ∈ (flip NOmega.lt_nat_l len),
                 ecovered (TCtr i) ⟫); desc.
  { destruct (classic (fin_exec G)) as [FIN|NFIN].
    { destruct (sim_traversal_trace WF WFSC CG FIN IMMCON) as [lst [TCtr HH]]; desc.
      assert (forall n, n < S lst -> etc_coherent G sc (TCtr n)) as ETCN.
      { induction n; ins. 
        { rewrite TCINIT. now apply ext_init_trav_coherent. }
        eapply ext_sim_trav_step_coherence.
        apply TCSTEP. lia. }
      exists (NOnum (1 + lst)), TCtr. splits; auto.
      { ins. lia. }
      { ins. apply rt_step. apply TCSTEP. lia. }
      split.
      { etransitivity; [now apply TCLAST|].
        unfold set_bunion.
        red; ins. exists lst. splits; ins. }
      apply set_subset_bunion_l. ins.
      red in COND. red in COND.
      erewrite <- etc_dom with (sc:=sc) (T:=TCtr x); eauto with hahn. }

    
    
    (* TODO: Infinite case *)
    admit. }
  
  exists len, TCtr. splits; auto.

  assert (FDC : FunctionalDependentChoice).
  { apply functional_choice_imp_functional_dependent_choice.
    red. apply functional_choice. }
  
  set (ntc_pred := fun ntc : nat * Configuration.t =>
                     match ntc with
                     | (n, conf) =>
                         << NLT : NOmega.lt_nat_l n len >> /\
                         << SIMREL : exists f_to f_from,
                             simrel G sc conf
                                    (etc_TC (TCtr n)) (reserved (TCtr n)) f_to f_from >>
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

  
  assert (forall n (NLT : NOmega.lt_nat_l n len), etc_fin (TCtr n)) as TCtr_etcfin.
  { clear -WF TCINIT TCSTEP LENP.
    induction n; ins.
    { rewrite TCINIT. apply init_etc_fin. }
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
                                  (etc_TC (TCtr (1 + n)))
                                  (reserved (TCtr (1 + n))) f_to' f_from' >> /\
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

  (* 
     1. Does TRAV condition denote what we need? 
     2. This is too technical; we need something similar to promise2imm theorem
     3. Currently I see two ways to proving this lemma:
        - Prove ExtTraversalCountingSet.simulation_enum_impl lemma
          to construct an infinite sequence of traversal configurations 
          and then convert it to sequence of configurations
        - Construct an infinite sequence of po-prefix-closed finite subgraphs,
          apply the finite case 'simulation' theorem to them
          and declare the sequence of their final states as the one needed here
    
     Some results we may need at some point:
     - ImmFair.wf_ar_rf_ppo_loc_ct_inf states that
       (ar | rf ;; ppo ∩ same_loc)^+ is well founded in infinite fair graphs;
       in finite case this fact is used to pick the 'next' event
     - ExtTraversalInf.exists_trav_step states that 'next' event can be used
       to advance the current traversal configuration in infinite case

     Also, there are some admits left in cert_graph/ files. 
     They are related to proving various fsupp properties 
     in (possibly) infinite graphs.
     Despite they could be (?) proved as is, 
     we instead can explicitly require certification to be finite 
     (which should continue to hold even for infinite executions),
     which will allow us to simply reuse previous cert_graph results.      

*)
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
  
End PromiseToIMM.
