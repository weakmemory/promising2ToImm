(******************************************************************************)
(** * A compilation correctness proof from the Promising2 memory model to
      the IMM memory model. *)
(******************************************************************************)
Require Import Omega.
From hahn Require Import Hahn.
Require Import PromisingLib.
From Promising2 Require Import TView View Time Event Cell Thread Memory Configuration Local.
From imm Require Import Prog.
From imm Require Import ProgToExecution.
From imm Require Import Events.
From imm Require Import Execution.
From imm Require Import imm_s.
From imm Require Import CombRelations.
From imm Require Import ProgToExecutionProperties.

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
Require Import Traversal.
Require Import TraversalConfig.
Require Import ExtSimTraversal.
Require Import ExtSimTraversalProperties.
Require Import ExtTraversalConfig.
Require Import ExtTraversal.
Require Import ExtTraversalCounting.
Require Import SimulationPlainStepAux.
Require Import FtoCoherent.
Require Import AuxRel2.

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

Lemma InAE A x (l : list A) : SetoidList.InA eq x l <-> In x l.
Proof using.
  split; [by induction 1; desf; ins; eauto|].
  induction l; ins; desf; eauto using SetoidList.InA.
Qed.

Lemma NoDupAE A (l : list A) : SetoidList.NoDupA eq l <-> NoDup l.
Proof using.
  split; induction 1; constructor; eauto; rewrite InAE in *; eauto.
Qed.

Lemma NoDup_map_NoDupA A B (f : A -> B) l :
  SetoidList.NoDupA (fun p p' => f p = f p') l ->
  NoDup (map f l).
Proof using.
  induction 1; ins; constructor; eauto.
  clear -H; intro M; destruct H; induction l; ins; desf;
    eauto using SetoidList.InA.
Qed.


Definition execution_final_memory (G : execution) final_memory :=
  forall l,
    (⟪ NO : forall e (EE : acts_set G e), loc G.(lab) e <> Some l ⟫ /\
     ⟪ ZERO : final_memory l = 0 ⟫) \/
    exists w,
      ⟪ ACTS : G.(acts_set) w ⟫ /\
      ⟪ WW   : is_w G.(lab) w ⟫ /\
      ⟪ LOC  : loc  G.(lab) w = Some l ⟫ /\
      ⟪ VAL  : val  G.(lab) w = Some (final_memory l) ⟫ /\
      ⟪ LAST : ~ (exists w', G.(co) w w') ⟫.

Notation "'NTid_' t" := (fun x => tid x <> t) (at level 1).
Notation "'Tid_' t"  := (fun x => tid x =  t) (at level 1).

Lemma cert_sim_step G sc thread PC T T' f_to f_from smode
      (WF : Wf G) (IMMCON : imm_consistent G sc)
      (STEP : ext_isim_trav_step G sc thread T T')
      (SIMREL : simrel_thread G sc PC (etc_TC T) (reserved T) f_to f_from thread smode)
      (NCOV : NTid_ thread ∩₁ G.(acts_set) ⊆₁ ecovered T) :
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
      (NCOV : NTid_ thread ∩₁ G.(acts_set) ⊆₁ ecovered T) :
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
      (NCOV : NTid_ thread ∩₁ G.(acts_set) ⊆₁ covered T) :
  exists T' S' PC' f_to' f_from',
    ⟪ FINALT : G.(acts_set) ⊆₁ covered T' ⟫ /\
    ⟪ PSTEP  : (plain_step MachineEvent.silent thread)＊ PC PC' ⟫ /\
    ⟪ SIMREL : simrel_thread G sc PC' T' S' f_to' f_from' thread sim_certification⟫.
Proof using.
  assert (etc_coherent G sc (mkETC T S)) as ETCCOH.
  { apply SIMREL. }
  generalize (sim_step_cov_full_traversal WF IMMCON ETCCOH NCOV); intros H.
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

Hypothesis ALLRLX  : G.(acts_set) \₁ is_init ⊆₁ (fun a => is_true (is_rlx G.(lab) a)).
(* All fences in the program are at least release or acquire ones. *)
Hypothesis FRELACQ : G.(acts_set) ∩₁ (fun a => is_true (is_f G.(lab) a)) ⊆₁ (fun a => is_true (is_ra G.(lab) a)).
Hypothesis RMWREX  : dom_rel G.(rmw) ⊆₁ (fun a => is_true (R_ex G.(lab) a)).

Hypothesis EFM : execution_final_memory G final_memory.

Hypothesis PROG_EX : program_execution prog G.
Hypothesis WF : Wf G.
Variable sc : relation actid.
Hypothesis IMMCON : imm_consistent G sc.

Lemma conf_steps_preserve_thread tid PC PC'
      (STEPS : (plain_step MachineEvent.silent tid)＊ PC PC') :
  forall lang state local
         (THREAD  : IdentMap.find tid PC.(Configuration.threads) =
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
         (THREAD  : IdentMap.find tid PC.(Configuration.threads) =
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
         (THREAD  : IdentMap.find tid PC.(Configuration.threads) =
                    Some (existT _ lang state, local))
         (THREAD' : IdentMap.find tid PC'.(Configuration.threads) =
                    Some (existT _ lang state', local'))
         (TS  : ts  = Thread.mk lang state local
                                PC.(Configuration.sc) PC.(Configuration.memory))
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

Lemma simrel_init :
  simrel G sc (conf_init prog)
         (init_trav G) (is_init ∩₁ acts_set G)
         (fun _ => tid_init) (fun _ => tid_init).
Proof using ALLRLX IMMCON PROG_EX TNONULL WF FRELACQ RMWREX.
  red; splits; red; splits; auto.
  { by apply ext_init_trav_coherent. }
  { simpls. basic_solver. }
  { ins. split; intros [INIT GG]; exfalso.
    { apply WF.(init_w) in INIT.
      apply (dom_l WF.(wf_rmwD)) in RMW.
      apply seq_eqv_l in RMW.
      type_solver. }
    apply WF.(rmw_in_sb) in RMW.
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
    apply WF.(init_w) in AA.
    type_solver. }
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
      rewrite WF.(wf_init_lab) in VAL.
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
  { ins. split; ins; [|omega].
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
      forall thread' (TT : thread_is_terminal PC.(Configuration.threads) thread'),
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
    apply PCOV in CC. by apply GPC.(acts_clos). }
  assert ((istep thread nil)＊ state state') as KK.
  { apply steps_same_E_empty_in; auto. }
  assert ((lts_step thread ProgramEvent.silent)＊ state state') as HH.
  { by hahn_rewrite <- istep_nil_eq_silent. }
  assert (state'.(eindex) = state.(eindex)) as EII.
  { eapply steps_same_eindex; eauto. }
  clear STEPS. rename HH into STEPS.

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
    red. ins. splits; eauto. }
  2: { ins; clear - QQ.
       apply NoDup_Permutation; eauto using NoDup_map_NoDupA, IdentMap.elements_3w.
       ins; rewrite !in_map_iff; split; intros ([i v] & <- & IN); ins;
         apply IdentMap.elements_complete in IN;
       destruct (positive_eq_dec i thread); desf; rewrite ?IdentMap.gss, ?IdentMap.gso in *; ins; desf.
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
    1,3: done.
    all: eauto.
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
         length (filterP (fun x => ~ thread_is_terminal (PC.(Configuration.threads)) x)
                   (map fst (IdentMap.elements PC.(Configuration.threads))))
         = l)
     as [l LL] by eauto.
  generalize dependent PC.
  induction l using (well_founded_ind lt_wf); ins; desf.
  destruct (classic (
      forall x (ELEM: In x (IdentMap.elements PC.(Configuration.threads))), 
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
    clear - PTERMINAL; induction l; ins; desf; ins; eauto; try omega.
    exfalso; specialize (PTERMINAL a); tauto.
  rewrite SAMENUM.
  apply in_split_perm in IN; desc; rewrite IN in SAMENUM; ins; rewrite <- SAMENUM; ins. 
  desf; ins. 
  2: by destruct v as ((lang,st),lc); destruct Y; apply NNPP in n0; apply n0 in FIND; ins.
  clear Y.
  auto using le_lt_n_Sm, plus_le_compat.
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
         rewrite WF.(wf_init_lab) in VAL.
         inv VAL. }
    assert (issued T w) as WISS.
    { eapply w_covered_issued; eauto.
      split; auto. }
    assert (S w) as WS.
    { by apply ETCCOH.(etc_I_in_S). }
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
    2: { edestruct WF.(wf_co_total) as [CO|CO]; eauto.
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
    unfold val in VAL. rewrite WF.(wf_init_lab) in VAL.
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
  edestruct WF.(wf_co_total) as [CO|CO]; eauto.
  1,2: split; [split|]; auto.
  { apply TCCOH in ISS. apply ISS. }
  { by rewrite LOC. }
  2: { exfalso. apply LAST. eauto. }
  assert (S b) as BS.
  { by apply ETCCOH.(etc_I_in_S). }
  assert (S w) as WS.
  { by apply ETCCOH.(etc_I_in_S). }
  eapply f_to_co_mon with (I:=S) in CO; eauto.
  apply Memory.max_ts_spec in INMEM.
  destruct INMEM as [_ CC].
  rewrite <- TO in CC.
  exfalso. eapply Time.lt_strorder.
  eapply TimeFacts.lt_le_lt; eauto.
Qed.

Lemma sim_step PC T S T' S' f_to f_from
      (STEP : ext_sim_trav_step G sc (mkETC T S) (mkETC T' S'))
      (SIMREL : simrel G sc PC T S f_to f_from) :
    exists PC' f_to' f_from',
      ⟪ PSTEP : (conf_step)^? PC PC' ⟫ /\
      ⟪ SIMREL : simrel G sc PC' T' S' f_to' f_from' ⟫.
Proof using All.
  destruct STEP as [thread STEP].
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
Qed.

Lemma sim_steps PC TS TS' f_to f_from
      (TCSTEPS : (ext_sim_trav_step G sc)⁺ TS TS')
      (SIMREL  : simrel G sc PC (etc_TC TS) (reserved TS) f_to f_from) :
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
  ins.
  eapply IHTCSTEPS1 in SIMREL.
  desc.
  eapply IHTCSTEPS2 in SIMREL0.
  desf. eexists. eexists. eexists. splits.
  2: eauto.
  eapply rt_trans; eauto. 
Qed.

Lemma simulation :
  exists T S PC f_to f_from,
    ⟪ FINALT : G.(acts_set) ⊆₁ covered T ⟫ /\
    ⟪ PSTEP  : conf_step＊ (conf_init prog) PC ⟫ /\
    ⟪ SIMREL : simrel G sc PC T S f_to f_from ⟫.
Proof using All.
  generalize (sim_traversal WF IMMCON); ins; desc.
  destruct T as [T S].
  exists T, S. apply rtE in H.
  destruct H as [H|H].
  { red in H. desf.
    eexists. eexists. eexists.
    splits; auto.
    { apply rtE. left. red. eauto. }
    unfold ext_init_trav in *. inv H.
    apply simrel_init. }
  eapply sim_steps in H.
  2: by apply simrel_init.
  desf.
  eexists. eexists. eexists.
  splits; eauto.
Qed.

Theorem promise2imm : promise_allows prog final_memory.
Proof using All.
  red.
  destruct simulation as [T [PC H]]. desc.
  edestruct sim_covered_exists_terminal as [PC']; eauto.
  desc.
  exists PC'. splits; eauto.
  { eapply rt_trans; eauto. }
  eapply same_final_memory; eauto. 
Qed.

End PromiseToIMM.
