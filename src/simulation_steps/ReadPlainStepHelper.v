Require Import PArith Arith.
From hahn Require Import Hahn.
Require Import PromisingLib.
From Promising2 Require Import Configuration TView View Time Event Cell Thread Memory Local.

From imm Require Import Events.
From imm Require Import Execution.
From imm Require Import Execution_eco.
From imm Require Import imm_s.
From imm Require Import imm_s_hb.
From imm Require Import imm_bob imm_s_ppo.
From imm Require Import ProgToExecution.
From imm Require Import CombRelations CombRelationsMore.
From imm Require Import Prog.
From imm Require Import ProgToExecution.
From imm Require Import SimClosure.

From hahnExt Require Import HahnExt.
From hahnExt Require Import HahnExt.
From imm Require Import TlsViewRelHelpers.
Require Import PlainStepBasic.
Require Import MemoryAux.
Require Import SimulationRel.
Require Import SimState.
Require Import SimStateHelper.
Require Import PromiseLTS.
Require Import MaxValue.
Require Import ViewRel.
Require Import SimulationPlainStepAux.
Require Import FtoCoherent.
From imm Require Import TraversalOrder.
From imm Require Import TLSCoherency.
From imm Require Import IordCoherency.
From imm Require Import SimClosure. 
Require Import ExtTraversalConfig.
From imm Require Import TlsEventSets.
From imm Require Import Next. 
Require Import SimulationRelProperties.
From imm Require Import EventsTraversalOrder.

Set Implicit Arguments.
  

Section ReadPlainStepHelper.

Variable G : execution.
Variable WF : Wf G.
Variable sc : relation actid.
Variable CON : imm_consistent G sc.

Notation "'E'" := (acts_set G).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'rmw'" := (rmw G).
Notation "'data'" := (data G).
Notation "'addr'" := (addr G).
Notation "'ctrl'" := (ctrl G).

Notation "'fr'" := (fr G).
Notation "'coe'" := (coe G).
Notation "'coi'" := (coi G).
Notation "'deps'" := (deps G).
Notation "'rfi'" := (rfi G).
Notation "'rfe'" := (rfe G).
Notation "'detour'" := (detour G).
Notation "'hb'" := (hb G).
Notation "'sw'" := (sw G).

Notation "'lab'" := (lab G).
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
Notation "'W_ex'" := (W_ex G).
Notation "'W_ex_acq'" := (W_ex ∩₁ (fun a => is_true (is_xacq lab a))).

Lemma read_step_helper PC T f_to f_from r w locr valr rel smode
      state local state' 
      (SIMREL_THREAD : simrel_thread G sc PC T f_to f_from (tid r) smode)
      (NEXT : next G (covered T) r) (COV : coverable G sc T r)
      (RR : R r)
      (LOC : loc lab r = Some locr) (VAL : val lab r = Some valr)
      (WW : W w) (RF : rf w r)
      (INMEM : Memory.get locr (f_to w) (Configuration.memory PC) =
               Some (f_from w, Message.full valr rel))
      (TIDMAP : IdentMap.find (tid r) (Configuration.threads PC) =
                Some (existT _ (thread_lts (tid r)) state, local)) :
  let T' := T ∪₁ eq (mkTL ta_cover r) in
  let tview' := TView.read_tview (Local.tview local) locr
                                 (f_to w) rel (Event_imm_promise.rmod (Events.mod lab r)) in
  let langst' := existT _ (thread_lts (tid r)) state' in
  let local' := Local.mk tview' (Local.promises local) in
  let threads' :=
      IdentMap.add (tid r) (langst', local')
                   (Configuration.threads PC) in
  let PC' := Configuration.mk threads' (Configuration.sc PC) (Configuration.memory PC) in
  (* ⟪ TCCOH : etc_coherent G sc (mkETC T' S) ⟫ /\ *)
  ⟪TCOH: tls_coherent G T'⟫ /\
  ⟪ICOH: iord_coherent G sc T'⟫ /\
  ⟪RCOH: reserve_coherent G T' ⟫ /\

  ⟪ RELCOV : W ∩₁ Rel ∩₁ issued T' ⊆₁ covered T' ⟫ /\

  ⟪ THREAD : forall t (IN : (threads_set G \₁ eq tid_init) t), IdentMap.In t threads'⟫ /\

  ⟪ PROM_IN_MEM :
      forall thread' langst local
             (TID : IdentMap.find thread' threads' = Some (langst, local)),
        Memory.le (Local.promises local) (Configuration.memory PC) ⟫ /\

  ⟪ SC_COV : smode = sim_certification -> E∩₁F∩₁Sc ⊆₁ covered T' ⟫ /\ 
  ⟪ SC_REQ : smode = sim_normal -> 
         forall (l : Loc.t),
           max_value f_to (S_tm G l (covered T')) (LocFun.find l (Configuration.sc PC)) ⟫ /\

  ⟪ SIM_PROM : sim_prom G sc T' f_to f_from (tid r) (Local.promises local) ⟫ /\
  ⟪ RESERVED_TIME :
      reserved_time G T' f_to f_from smode (Configuration.memory PC) ⟫ /\
  
  ⟪ SIM_MEM : sim_mem G sc T' f_to f_from (tid r) local' (Configuration.memory PC) ⟫ /\
  ⟪ SIM_TVIEW : sim_tview G sc (covered T') f_to tview' (tid r) ⟫ /\
  ⟪ PLN_RLX_EQ : pln_rlx_eq tview' ⟫ /\
  ⟪ MEM_CLOSE : memory_close tview' (Configuration.memory PC) ⟫.
Proof using WF CON.
  simpls.
  cdes SIMREL_THREAD. cdes COMMON. cdes LOCAL.
  set (X := STATE).
  
  (* assert (tc_coherent G sc T) as sTCCOH by apply TCCOH. *)

  assert (~ covered T r) as RNCOV.
  { apply NEXT. }

  assert (E r) as RACT.
  { apply NEXT. }
  assert (~ is_init r) as RNINIT.
  { intros H; apply (init_w WF) in H. type_solver. }
  assert (Rlx r) as RRLX.
  { apply ALLRLX. by split. }

  assert (issued T w) as WISS.
  { eapply dom_rf_coverable; vauto.  }

   assert (exists xrmw, rmwmod lab r = Some xrmw) as RXRMW.
   { unfold rmwmod. unfold is_r in *. desf. eauto. }

  assert (loc lab w = Some locr) as WPLOC.
  { assert (loc lab w = loc lab r) as HH.
    { by apply (wf_rfl WF). }
      by rewrite HH. }
  assert (val lab w = Some valr) as WPVAL.
  { assert (val lab w = val lab r) as HH.
    { by apply wf_rfv. }
      by rewrite HH. }

  assert (E w) as WPACT.
  { apply (wf_rfE WF) in RF. apply seq_eqv_l in RF; desf. }

  edestruct SIM_MEM as [rel' DOM].
  { by apply WISS. }
  all: eauto.
  simpls. desc.
  rewrite INMEM in INMEM0. inv INMEM0. clear INMEM0.
  rename rel' into rel.

  assert (Ordering.le Ordering.relaxed (Event_imm_promise.rmod (Events.mod lab r))) as RLX_ORDR.
  { unfold is_rlx, mode_le, Events.mod, is_r in *.
    destruct (lab r); desf. }
  
  assert (forall y : actid, covered T y /\ tid y = tid r -> sb y r) as COVSB.
  { intros y [COVY TIDY].
    destruct (same_thread G r y) as [[ST|ST]|ST]; subst; auto.
    { eapply coveredE; eauto. }
    { done. }
    destruct RNCOV. eapply dom_sb_covered; vauto. }
  
  splits; simpls.
  { constructor.
    all: try apply TCCOH.
    { erewrite (@tls_coh_init G T); basic_solver. }
    unionL; [by apply tls_coh_exec| ].
    unionR right. apply set_subset_eq. vauto. }
  { eapply iord_coherent_extend; eauto.
    apply coverable_iord_dom_cond; auto. }
  { apply reserve_coherent_add_cover; auto. }
  { clear -RELCOV. simplify_tls_events. rewrite RELCOV. basic_solver. }
  { intros e' EE. 
    apply IdentMap.Facts.add_in_iff.
    destruct (Ident.eq_dec e' (tid r)) as [|NEQ]; subst; auto. }
  { ins.
    destruct (Ident.eq_dec thread' (tid r)) as [EQ|NEQ].
    { subst. rewrite IdentMap.gss in TID.
      assert (Local.promises local0 = Local.promises local) as H.
      { inv TID. }
      rewrite H.
      eapply PROM_IN_MEM; eauto. }
    red; ins. rewrite IdentMap.gso in TID; auto.
    eapply PROM_IN_MEM; eauto. }
  { intros H. apply SC_COV in H. etransitivity; [apply H|].
    rewrite covered_union. basic_solver. }
  { intros NFSC l; subst.
    eapply max_value_same_set.
    { apply SC_REQ; auto. }
    rewrite covered_union, s_tm_union.
    unfold CombRelations.S_tm.
    split; unionL; try basic_solver 3.
    rewrite (wf_S_tmrD). unfold S_tmr. rewrite covered_singleton.  
    type_solver 21. }
  { red. ins.
    (* TODO: generalize the proof! It's used a couple of times. *)
    edestruct SIM_PROM as [w']; eauto.
    exists w'; splits; desc; auto.
    { clear -ISS. find_event_set. }
    assert (r <> w') as NEQ.
    { eapply issuedW in ISS; eauto. intros ->. type_solver. }  
    clear -NEQ NCOV. separate_set_event. }
  { eapply reserved_time_same_issued_reserved; eauto.
    all: clear; simplify_tls_events; basic_solver. }
  { eapply sim_mem_covered_mori with (T:=T); eauto.
    all: clear; simplify_tls_events; basic_solver. }
  { simplify_tls_events. eapply sim_tview_read_step; eauto.
    1,2: by apply CON.
    { red; intros x y H. apply NEXT. by exists y. }
    unfold is_r, loc, val, Events.mod, rmwmod in *. desf. }
  { cdes PLN_RLX_EQ. 
    unfold View.singleton_ur_if.
    red; splits; simpls.
    all: desf; simpls.
    all: try rewrite REL_PLN_RLX.
    all: try rewrite EQ_SIN.
    all: try rewrite EQ_CUR.
    all: try rewrite EQ_ACQ.
    all: reflexivity. }
  unfold TView.read_tview; simpls.
  red; splits; simpls.
  all: desf; ins.
  all: repeat (apply Memory.join_closed_timemap).
  all: try apply MEM_CLOSE.
  all: auto.
  all: try by apply Memory.closed_timemap_bot.
  all: try by eapply Memory.singleton_closed_timemap; eauto.
Qed.

End ReadPlainStepHelper.
