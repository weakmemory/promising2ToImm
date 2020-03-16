Require Import PArith.
From hahn Require Import Hahn.
Require Import PromisingLib.
From Promising2 Require Import Configuration TView View Time Event Cell Thread Memory Local.

From imm Require Import Events.
From imm Require Import Execution.
From imm Require Import Execution_eco.
From imm Require Import imm_s_hb.
From imm Require Import imm_s.
From imm Require Import imm_bob imm_s_ppo.
From imm Require Import CombRelations.
From imm Require Import CombRelationsMore.
From imm Require Import RMWinstrProps.

From imm Require Import AuxRel2.
Require Import ViewRelHelpers.
Require Import TraversalConfig.
Require Import Traversal.
Require Import MemoryClosedness.
Require Import MaxValue.
Require Import ViewRel.
Require Import SimulationRel.
Require Import MemoryAux.
Require Import SimState.
Require Import SimulationPlainStepAux.

Set Implicit Arguments.

(* It's a version of Configuration.step which doesn't require
   consistency of the new configuration. *)
Inductive plain_step :
  forall (e:MachineEvent.t) (tid:Ident.t)
         (c1 c2:Configuration.t), Prop :=
| plain_step_intro
    pf e tid c1 lang st1 lc1 e2 st3 lc3 sc3 memory3
    (TID: IdentMap.find tid c1.(Configuration.threads) = Some (existT _ lang st1, lc1))
    (STEPS: rtc (@Thread.tau_step _) (Thread.mk _ st1 lc1 c1.(Configuration.sc) c1.(Configuration.memory)) e2)
    (STEP: Thread.step pf e e2 (Thread.mk _ st3 lc3 sc3 memory3))
    (EVENT: e <> ThreadEvent.failure) :
    plain_step (ThreadEvent.get_machine_event e) tid c1 (Configuration.mk (IdentMap.add tid (existT _ _ st3, lc3) c1.(Configuration.threads)) sc3 memory3).

Section PlainStepBasic.

Variable G : execution.
Variable WF : Wf G.
Variable sc : relation actid.
Variable CON : imm_consistent G sc.

Notation "'E'" := G.(acts_set).
Notation "'sb'" := G.(sb).
Notation "'rf'" := G.(rf).
Notation "'co'" := G.(co).
Notation "'rmw'" := G.(rmw).
Notation "'data'" := G.(data).
Notation "'addr'" := G.(addr).
Notation "'ctrl'" := G.(ctrl).

Notation "'fr'" := G.(fr).
Notation "'coe'" := G.(coe).
Notation "'coi'" := G.(coi).
Notation "'deps'" := G.(deps).
Notation "'rfi'" := G.(rfi).
Notation "'rfe'" := G.(rfe).
Notation "'detour'" := G.(detour).
Notation "'hb'" := G.(hb).
Notation "'sw'" := G.(sw).

Notation "'lab'" := G.(lab).
(* Notation "'loc'" := (loc lab). *)
(* Notation "'val'" := (val lab). *)
(* Notation "'mod'" := (mod lab). *)
(* Notation "'same_loc'" := (same_loc lab). *)

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'RW'" := (R ∪₁ W).
Notation "'FR'" := (F ∪₁ R).
Notation "'FW'" := (F ∪₁ W).

Notation "'Pln'" := (fun a => is_true (is_only_pln lab a)).
Notation "'Rlx'" := (fun a => is_true (is_rlx lab a)).
Notation "'Rel'" := (fun a => is_true (is_rel lab a)).
Notation "'Acq'" := (fun a => is_true (is_acq lab a)).
Notation "'Acqrel'" := (fun a => is_true (is_acqrel lab a)).
Notation "'Acq/Rel'" := (fun a => is_true (is_ra lab a)).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

Notation "'Loc_' l" := (fun x => loc lab x = Some l) (at level 1).
Notation "'W_ex'" := G.(W_ex).
Notation "'W_ex_acq'" := (W_ex ∩₁ (fun a => is_true (is_xacq lab a))).

Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).

Lemma same_thread_modify_for_step thread x y
      (STEP : plain_step MachineEvent.silent thread x y) :
  forall tt, IdentMap.add thread tt y.(Configuration.threads) =
             IdentMap.add thread tt x.(Configuration.threads).
Proof using. ins. inv STEP; simpls. by rewrite IdentMap.add_add_eq. Qed.

Lemma same_thread_modify_for_steps thread x y
      (STEP : (plain_step MachineEvent.silent thread)＊ x y) :
  forall tt, IdentMap.add thread tt y.(Configuration.threads) =
             IdentMap.add thread tt x.(Configuration.threads).
Proof using.
  induction STEP; eauto.
  { by apply same_thread_modify_for_step. }
  ins. by rewrite IHSTEP2.
Qed.

Lemma plain_step_seq_plain_step_in_plain_step thread :
  plain_step MachineEvent.silent thread ⨾ plain_step MachineEvent.silent thread ⊆
             plain_step MachineEvent.silent thread.
Proof using.
  intros x z [y [AA BB]].
  assert (forall tt, IdentMap.add thread tt y.(Configuration.threads) =
                     IdentMap.add thread tt x.(Configuration.threads)) as HH.
  { by apply same_thread_modify_for_step. }
  set (pe := MachineEvent.silent).
  assert (pe = MachineEvent.silent) as EQ by done.
  inv AA. inv BB. simpls. rewrite HH.
  rewrite IdentMap.gss in TID0. inv TID0.
  rewrite EQ. rewrite <- H1.
  econstructor.
  3: edone.
  all: eauto.
  apply clos_rt_rt1n.
  eapply rt_rt. eexists. split; eauto.
  apply rt_begin. right. eexists. split.
  { red. econstructor.
    { econstructor; eauto. }
    done. }
    by apply clos_rt1n_rt.
Qed.

Lemma plain_step_ct_in_plain_step thread :
  (plain_step MachineEvent.silent thread)⁺ ⊆ plain_step MachineEvent.silent thread.
Proof using.
  apply ct_of_trans. apply transitiveI. apply plain_step_seq_plain_step_in_plain_step.
Qed.

Lemma same_other_threads_step thread label PC PC' 
      (PCSTEP : plain_step label thread PC PC')
      thread' (TNEQ : thread' <> thread) langst local :
  IdentMap.find thread' PC .(Configuration.threads) = Some (langst, local) <->
  IdentMap.find thread' PC'.(Configuration.threads) = Some (langst, local).
Proof using. destruct PCSTEP. simpls. rewrite IdentMap.gso; auto. Qed.

Lemma same_other_threads_steps thread label PC PC' 
      (PCSTEPS : (plain_step label thread)⁺ PC PC')
      thread' (TNEQ : thread' <> thread) langst local :
  IdentMap.find thread' PC .(Configuration.threads) = Some (langst , local) <->
  IdentMap.find thread' PC'.(Configuration.threads) = Some (langst, local).
Proof using.
  induction PCSTEPS.
  { eapply same_other_threads_step; eauto. }
  etransitivity; eauto.
Qed.

Lemma simrel_thread_local_step thread PC PC' T S T' S' label f_to f_from
      (TCCOH  : tc_coherent G sc T)
      (COVE   : covered T' ⊆₁ E)
      (ISSE   : issued  T' ⊆₁ E)
      (COVIN  : covered T  ⊆₁ covered T')
      (ISSIN  : issued  T  ⊆₁ issued  T')
      (SIN    :         S  ⊆₁         S')
      (NINCOV : covered T' \₁ covered T ⊆₁ Tid_ thread)
      (NINISS : issued  T' \₁ issued  T ⊆₁ Tid_ thread)
      (NINS   :         S' \₁         S ⊆₁ Tid_ thread)
      (SOT    : forall thread' (TNEQ : thread' <> thread) langst local,
          IdentMap.find thread' PC .(Configuration.threads) = Some (langst, local) <->
          IdentMap.find thread' PC'.(Configuration.threads) = Some (langst, local))
      (PCSTEP : (plain_step label thread)⁺ PC PC')
      (CLOSED_PRES :
         closedness_preserved PC.(Configuration.memory) PC'.(Configuration.memory))
      (MSG_PRES :
         msg_preserved PC.(Configuration.memory) PC'.(Configuration.memory))
      (TPEQ : forall thread,
          IdentMap.In thread PC.(Configuration.threads) <->
          IdentMap.In thread PC'.(Configuration.threads))
      (SIMREL_THREAD : simrel_thread G sc PC' T' S' f_to f_from thread sim_normal)
      thread' (NEQ : thread <> thread')
      (TP' : IdentMap.In thread' (Configuration.threads PC'))
      (TP0 : IdentMap.In thread' (Configuration.threads PC))
      (state : Language.state (PromiseLTS.thread_lts thread')) local
      (RMWREX : rmw_is_rex_instrs (ProgToExecution.instrs state))
      (TNNULL : thread' <> tid_init)
      (GPC : ProgToExecutionProperties.wf_thread_state thread' state)
      (LLH : IdentMap.find thread' (Configuration.threads PC) =
             Some
               (existT (fun lang : language => Language.state lang)
                       (PromiseLTS.thread_lts thread') state, local))
      (PROM_DISJOINT : forall (thread'0 : thread_id)
                              (langst' : {lang : language & Language.state lang}) 
                              (local' : Local.t),
          thread' <> thread'0 ->
          IdentMap.find thread'0 (Configuration.threads PC) = Some (langst', local') ->
          forall (loc : Loc.t) (to : Time.t),
            Memory.get loc to (Local.promises local) = None \/
            Memory.get loc to (Local.promises local') = None)
      (SIM_PROM : sim_prom G sc T f_to f_from thread' (Local.promises local))
      (SIM_RPROM : sim_res_prom G T S f_to f_from thread' (Local.promises local))
      (SIM_MEM : sim_mem G sc T f_to f_from thread' local (Configuration.memory PC))
      (SIM_RES_MEM_LCL : forall l b (RESB: S b) (NISSB: ~ issued T b) (LOC: Loc_ l b)
                                (TID : tid b = thread'),
          Memory.get l (f_to b) local.(Local.promises) =
          Some (f_from b, Message.reserve))
      (SIM_TVIEW : sim_tview G sc (covered T) f_to (Local.tview local) thread')
      (PLN_RLX_EQ : pln_rlx_eq (Local.tview local))
      (MEM_CLOSE : memory_close (Local.tview local) (Configuration.memory PC))
      (STATE : sim_state G sim_normal (covered T) state) :
  simrel_thread_local G sc PC' T' S' f_to f_from thread' sim_normal.
Proof using WF.
  assert (IdentMap.In thread' PC.(Configuration.threads)) as TP.
  { by apply TPEQ. }
  assert (IdentMap.find thread' (Configuration.threads PC') =
          Some (existT _ (PromiseLTS.thread_lts thread') state,
                local)) as TID by (apply SOT; auto).
  assert
  (forall a : actid, tid a = thread' -> covered T' a -> covered T a) as PP.
  { intros a TT YY.
    destruct (classic (covered T a)) as [GG|GG]; [done|].
    exfalso.
    assert (tid a = thread) as RR; [|by subst].
    by apply NINCOV; split. }
  cdes SIMREL_THREAD. cdes COMMON. cdes LOCAL.
  red; splits; simpls.
  rewrite TID.
  exists state; exists local; splits; auto.
  2: { red. ins.
       edestruct SIM_PROM as [w H]; eauto.
       des. exists w; splits; auto. }
  7: { eapply sim_state_other_thread_step with (C:=covered T); eauto. }
  6: { by red; splits; ins; apply CLOSED_PRES; apply MEM_CLOSE. }
  5: { destruct T as [C I]. destruct T' as [C' I'].
       eapply sim_tview_other_thread_step.
       3: by apply COVIN.
       all: eauto.
       etransitivity; [by apply TCCOH|]. done. }
  { clear TNNULL0 TNNULL.
    ins. destruct (classic (thread'0 = thread)) as [|TNEQ']; subst.
    { apply or_comm. cdes SIMREL_THREAD.
      rewrite LLH0 in TID'. inv TID'. clear TID'.
      eapply PROM_DISJOINT0; eauto. }
    assert (IdentMap.find thread'0 (Configuration.threads PC) = Some (langst', local'))
      as TT by (by apply SOT in TID').
    eapply PROM_DISJOINT; eauto. }
  { red. ins. unnw. (* sim_res_prom *)
    edestruct SIM_RPROM as [b AA]; eauto.
    desf.
    exists b. splits; auto.
    intros HH.
    apply NEQ. symmetry. apply NINISS. by split. }
  2: { red. ins. unnw.
       split.
       { by apply SIM_RES_MEM. }
       intros HH. apply SIM_RES_MEM_LCL; eauto.
       apply NNPP. intros AA. apply NEQ. rewrite <- HH. symmetry.
       apply NINS. by split. }
  red. ins. unnw.
  edestruct SIM_MEM0 as [rel]; eauto.
  simpls; desc.
  exists rel; splits; auto.
  intros BTID.
  assert (~ covered T' b <-> ~ covered T b) as CCB.
  { split; intros CC1 CC2.
      by apply COVIN in CC2.
      assert (tid b = thread) as TT.
      2: by subst; desf.
        by apply NINCOV; split. }
  assert (issued T' b <-> issued T b) as IIB.
  { split; auto.
    intros II.
    destruct (classic (issued T b)) as [|NN]; [done|].
    assert (tid b = thread) as TT.
    2: by subst; desf.
      by apply NINISS; split. }
  rewrite CCB.
  edestruct SIM_MEM as [rel']; eauto.
  { by apply IIB. }
  simpls; desc.
  intros CC.
  destruct H2; auto.
  assert (rel' = rel); [|subst; split; vauto].
  { cdes COMMON. eapply PROM_IN_MEM0 in H; eauto.
    rewrite INMEM in H. inv H. }
  destruct H0 as [p_rel H0]; desc.
  eexists; split; eauto.
  desf.
  { left; splits; auto.
    intros [y HH]. apply NINRMW.
    exists y. apply seq_eqv_l in HH; destruct HH as [ISSY HH]. 
    apply seq_eqv_l; split; auto.
    destruct (classic (issued T y)) as [|NISS]; [done|exfalso].
    assert (W y) as WY.
    { eapply issuedW; [|by apply ISSY]. apply TCCOH0. }
    destruct (classic (tid y = thread)) as [|TNEQ]; subst.
    2: by apply TNEQ; apply NINISS; split.
    apply NISS.
    apply IIB in ISSB. apply TCCOH in ISSB.
    apply ISSB.
    exists b; apply seq_eqv_r; split; auto.
    apply seq_eqv_l. split; auto.
    apply ct_step. right.
    destruct HH as [z [AA BB]].
    exists z. split; auto. by apply WF.(rmw_in_ppo_loc). }
  right. exists p; splits; auto.
  assert (issued T' p) as ISSP'.
  { apply ISSIN. apply ISSP. }
  assert (loc lab p = Some l) as LOCP.
  { simpls. erewrite wf_rfrmwl; eauto. }
  assert (exists p_v', val lab p = Some p_v') as [p_v' VALP].
  { apply WF.(wf_rfrmwD) in INRMW.
    unfold val, is_w in *. desf.
    all: eexists; eauto. }
  eapply MSG_PRES in P_INMEM. desc.
  edestruct (SIM_MEM0 l) with (b:=p) as [p_rel'' HH]; eauto.
  simpls. desc.
  rewrite P_INMEM in INMEM1. inv INMEM1.
  eexists; eexists; splits; eauto.
Qed.

Lemma full_simrel_step thread PC PC' T S T' S' label f_to f_from
      (COVE   : covered T' ⊆₁ E)
      (ISSE   : issued  T' ⊆₁ E)
      (COVIN  : covered T  ⊆₁ covered T')
      (ISSIN  : issued  T  ⊆₁ issued  T')
      (SIN    :         S  ⊆₁         S')
      (NINCOV : covered T' \₁ covered T ⊆₁ Tid_ thread)
      (NINISS : issued  T' \₁ issued  T ⊆₁ Tid_ thread)
      (NINS   :         S' \₁         S ⊆₁ Tid_ thread)
      (SOT    : forall thread' (TNEQ : thread' <> thread) langst local,
          IdentMap.find thread' PC .(Configuration.threads) = Some (langst, local) <->
          IdentMap.find thread' PC'.(Configuration.threads) = Some (langst, local))
      (PCSTEP : (plain_step label thread)⁺ PC PC')
      (CLOSED_PRES :
         closedness_preserved PC.(Configuration.memory) PC'.(Configuration.memory))
      (MSG_PRES :
         msg_preserved PC.(Configuration.memory) PC'.(Configuration.memory))
      (TPEQ : forall thread,
          IdentMap.In thread PC.(Configuration.threads) <->
          IdentMap.In thread PC'.(Configuration.threads))
      (SIMREL_THREAD : simrel_thread G sc PC' T' S' f_to f_from thread sim_normal)
      (SIMREL : simrel G sc PC T S f_to f_from) :
  simrel G sc PC' T' S' f_to f_from.
Proof using WF.
  red. splits; auto.
  { apply SIMREL_THREAD. }
  cdes SIMREL.
  intros thread' TP'.
  destruct (Ident.eq_dec thread thread') as [|NEQ]; subst.
  { apply SIMREL_THREAD. }
  assert (simrel_thread_local G sc PC T S f_to f_from thread' sim_normal) as AA.
  { apply SIMREL. by apply TPEQ. }
  cdes AA.
  eapply simrel_thread_local_step; eauto.
  { cdes COMMON. apply TCCOH. }
  { by apply TPEQ. }
  ins.
  edestruct SIM_RES_MEM with (b:=b) as [_ HH]; eauto.
    by apply HH.
Qed.

Lemma max_event_cur PC T S f_to f_from l e thread foo local smode
      (SIMREL_THREAD : simrel_thread G sc PC T S f_to f_from thread smode)
      (NEXT : next G (covered T) e)
      (TID_E : tid e = thread)
      (LOC : loc lab e = Some l)
      (TID: IdentMap.find thread PC.(Configuration.threads) = Some (foo, local)):
  exists p_max,
    ⟪ NEQ : p_max <> e ⟫ /\
    ⟪ CCUR : urr G sc l p_max e ⟫ /\
    ⟪ LB : Time.le
      (View.rlx (TView.cur (Local.tview local)) l)
      (f_to p_max) ⟫.
Proof using WF CON.
  cdes SIMREL_THREAD. cdes COMMON. cdes LOCAL.
  red in SIM_TVIEW; desf.
  red in CUR; desf.
  specialize (CUR l); red in CUR; desc.
  
  assert (E e) as EE.
  { apply NEXT. }
  assert (~ is_init e) as NINE.
  { intros HH. apply NEXT. by apply TCCOH. }

  destruct MAX as [[MAX MAX'] | MAX].
  { unfold LocFun.find in MAX'.
    rewrite MAX'; ins.
    exists (InitEvent l); splits; [ | | by apply Time.bot_spec].
    { intros H; subst; simpls. }
    apply hb_in_urr.
    apply seq_eqv_l; split; red; [|right].
    { by unfold is_w, loc; rewrite WF.(wf_init_lab). }
    apply sb_in_hb.
    apply init_ninit_sb; auto.
    apply WF.(wf_init). eexists; eauto. }
  desf.
  exists a_max. apply and_assoc; split; auto.
  red in INam; red in INam.
  destruct INam as [y CCUR].
  red in CCUR; hahn_rewrite <- seqA in CCUR.
  apply seq_eqv_r in CCUR; destruct CCUR as [CCUR Y'].
  apply seq_eqv_r in CCUR; destruct CCUR as [CCUR Y].
  assert (hb y e) as HBYE.
  { apply sb_in_hb.
    assert (E y) as EY.
    { eapply (@coveredE G) in Y'; eauto.
      apply COMMON. }
    destruct Y as [Y | Y].
    2: by apply init_ninit_sb.
    destruct (same_thread G e y) as [[ZZ|ZZ]|ZZ]; subst; auto.
    { by apply NEXT in Y'. }
    exfalso.
    assert (covered T e) as Z.
    { apply TCCOH in Y'.
      apply Y'. eexists; apply seq_eqv_r; split; eauto. }
      by apply NEXT in Z. }
  assert ((urr G sc l ⨾ hb) a_max e) as UH.
  { exists y; split; auto. }
  splits.
  { intros H; subst; eapply urr_hb_irr; eauto.
    all: apply CON. }
  apply urr_hb.
  destruct UH as [z [UH HH]].
  eexists; split; eauto.
Qed.

End PlainStepBasic.
