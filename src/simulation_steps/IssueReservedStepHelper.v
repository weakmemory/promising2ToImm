Require Import Setoid PArith.
From hahn Require Import Hahn.
Require Import PromisingLib.
From Promising2 Require Import TView View Time Event Cell Thread Memory Configuration Local.

From imm Require Import Events.
From imm Require Import Execution.
From imm Require Import Execution_eco.
From imm Require Import imm_s_hb.
From imm Require Import imm_s.
From imm Require Import imm_common.
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
Require Import ExtTraversal.
Require Import FtoCoherent.
Require Import SimulationRelProperties.
Require Import ExistsIssueReservedInterval.

Set Implicit Arguments.

Section IssueReservedStepHelper.

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

Lemma issue_reserved_step_helper w valw locw langst
      (TID : IdentMap.find (tid w) PC.(Configuration.threads) = Some (langst, local))
      (TSTEP : ext_itrav_step
                 G sc w (mkETC T S)
                 (mkETC
                    (mkTC (covered T) (issued T ∪₁ eq w))
                    (S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G (mkETC T S) rfi (eq w))))
      (SW : S w)
      (NONEXT : dom_sb_S_rfrmw G (mkETC T S) rfi (eq w) ⊆₁ ∅)
      (LOC : loc lab w = Some locw)
      (VAL : val lab w = Some valw)
      (WTID : thread = tid w) :
  let promises := local.(Local.promises) in
  let memory   := PC.(Configuration.memory) in
  let sc_view  := PC.(Configuration.sc) in
  let covered' := if Rel w then covered T ∪₁ eq w else covered T in
  let T'       := mkTC covered' (issued T ∪₁ eq w) in
  let S'       := S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G (mkETC T S) rfi (eq w) in
  exists p_rel, rfrmw_prev_rel G sc T f_to f_from PC w locw p_rel /\
    let rel'' :=
        if is_rel lab w
        then (TView.cur (Local.tview local))
        else (TView.rel (Local.tview local) locw)
    in
    let rel' := (View.join (View.join rel'' p_rel.(View.unwrap))
                           (View.singleton_ur locw (f_to w))) in

    ⟪ REL_VIEW_LT : Time.lt (View.rlx rel'' locw) (f_to w) ⟫ /\
    ⟪ REL_VIEW_LE : Time.le (View.rlx rel' locw) (f_to w) ⟫ /\


    exists promises_cancel memory_cancel,
      ⟪ PCANCEL :
          Memory.remove promises locw (f_from w) (f_to w)
                        Message.reserve promises_cancel ⟫ /\
      ⟪ MCANCEL :
          Memory.remove memory locw (f_from w) (f_to w)
                        Message.reserve memory_cancel ⟫ /\

      exists promises_add memory_add,
        ⟪ PADD :
            Memory.add promises_cancel locw (f_from w) (f_to w)
                       (Message.full valw (Some rel')) promises_add ⟫ /\
        ⟪ MADD :
            Memory.add memory_cancel locw (f_from w) (f_to w)
                       (Message.full valw (Some rel')) memory_add ⟫ /\

        ⟪ FCOH : f_to_coherent G S' f_to f_from ⟫ /\

      exists promises',
        ⟪ PEQ :
            promises' = if Rel w
                        then promises_cancel  
                        else  promises_add ⟫ /\

        ⟪ HELPER :
            sim_mem_helper
              G sc f_to w (f_from w) valw
              (View.join (View.join (if is_rel lab w
                                     then (TView.cur (Local.tview local))
                                     else (TView.rel (Local.tview local) locw))
                                    p_rel.(View.unwrap))
                         (View.singleton_ur locw (f_to w))) ⟫ /\

        ⟪ RESERVED_TIME :
            reserved_time G T' S' f_to f_from smode memory_add ⟫ /\

        let local' := Local.mk local.(Local.tview) promises' in
        let threads' :=
            IdentMap.add (tid w)
                         (langst, local')
                         (Configuration.threads PC) in

        ⟪ THREAD : forall e (ACT : E e) (NINIT : ~ is_init e),
            exists langst, IdentMap.find (tid e) threads' = Some langst ⟫ /\

        ⟪ SC_REQ : smode = sim_normal -> 
                   forall (l : Loc.t),
                     max_value f_to (S_tm G l (covered T)) (LocFun.find l sc_view) ⟫ /\
        ⟪ CLOSED_SC : Memory.closed_timemap sc_view memory_add ⟫ /\

        ⟪ MEM_CANCEL :
            Memory.promise local.(Local.promises) memory locw (f_from w) (f_to w)
                           Message.reserve
                           promises_cancel memory_cancel Memory.op_kind_cancel ⟫ /\

        ⟪ MEM_PROMISE :
            Memory.promise promises_cancel memory_cancel locw (f_from w) (f_to w)
                           (Message.full valw (Some rel'))
                           promises_add memory_add Memory.op_kind_add ⟫ /\
        ⟪ PROM_IN_MEM :
            forall thread' langst local
                   (TID : IdentMap.find thread' threads' = Some (langst, local)),
              Memory.le local.(Local.promises) memory_add ⟫ /\

        ⟪ SIM_PROM     : sim_prom G sc T' f_to f_from (tid w) promises'  ⟫ /\
        ⟪ SIM_RES_PROM : sim_res_prom G T' (S ∪₁ eq w) f_to f_from (tid w) promises'  ⟫ /\

        ⟪ PROM_DISJOINT :
            forall thread' langst' local'
                   (TNEQ : tid w <> thread')
                   (TID' : IdentMap.find thread' threads' =
                           Some (langst', local')),
            forall loc to,
              Memory.get loc to promises' = None \/
              Memory.get loc to local'.(Local.promises) = None ⟫ /\

        ⟪ SIM_MEM     : sim_mem G sc T' f_to f_from (tid w) local' memory_add ⟫ /\
        ⟪ SIM_RES_MEM : sim_res_mem G T' (S ∪₁ eq w) f_to f_from (tid w) local' memory_add ⟫.
Proof using All.
  assert (tc_coherent G sc T) as TCCOH by apply ETCCOH.

  subst.
  edestruct exists_time_interval_for_issue_reserved_no_next as [p_rel [PREL HH]]; eauto.
  simpls; desc.
  
  assert (~ issued T w) as NISSB.
  { admit. }
  assert (~ covered T w) as NCOVB.
  { admit. }
  assert (S ⊆₁ E ∩₁ W) as SEW.
  { admit. }

  (* assert (forall e, issued T e -> f_to' e = f_to e) as ISSEQ_TO. *)
  (* { ins. apply REQ_TO. by apply ETCCOH.(etc_I_in_S). } *)
  (* assert (forall e, issued T e -> f_from' e = f_from e) as ISSEQ_FROM. *)
  (* { ins. apply REQ_FROM. by apply ETCCOH.(etc_I_in_S). } *)

  assert (W w) as WW by (by apply (reservedW WF ETCCOH)).
  assert (E w) as EW by (by apply ETCCOH.(etc_S_in_E)).

  (* assert (forall l b (SB : S b) (BLOC : loc lab b = Some l), *)
  (*            l <> locw \/ f_to b <> f_to' w) as SNEQ. *)
  (* { ins. *)
  (*   arewrite (f_to b = f_to' b). *)
  (*   { symmetry. by apply REQ_TO. } *)
  (*   (* TODO: generalize to a lemma *) *)
  (*   destruct (classic (l = locw)); [right|by left]; subst. *)
  (*   intros HH. *)
  (*   assert (b = w); desf. *)
  (*   eapply f_to_eq with (I:=S ∪₁ eq w) (f_to:=f_to'); eauto. *)
  (*   4: by right. *)
  (*   3: by left. *)
  (*   2: by red; rewrite BLOC; desf. *)
  (*   unionL. *)
  (*   { apply set_subset_inter_r; split; [by apply ETCCOH|]. *)
  (*     apply (reservedW WF ETCCOH). } *)
  (*   basic_solver. } *)

  (* assert (forall l b (ISSB : issued T b) (BLOC : loc lab b = Some l), *)
  (*            l <> locw \/ f_to b <> f_to' w) as INEQ. *)
  (* { ins. apply SNEQ; auto. by apply ETCCOH.(etc_I_in_S). } *)

  assert (Memory.le promises_add memory_add) as PP.
  { red; ins.
    erewrite Memory.add_o; eauto.
    erewrite Memory.add_o in LHS; [|by apply PADD].
    destruct (loc_ts_eq_dec (loc, to) (locw, f_to w)) as [[A B]|LL].
    { simpls; rewrite A in *; rewrite B in *.
      rewrite (loc_ts_eq_dec_eq locw (f_to w)).
        by rewrite (loc_ts_eq_dec_eq locw (f_to w)) in LHS. }
    rewrite (loc_ts_eq_dec_neq LL).
    rewrite (loc_ts_eq_dec_neq LL) in LHS.
    erewrite Memory.remove_o; eauto.
    erewrite Memory.remove_o in LHS; [|by apply PCANCEL].
    rewrite (loc_ts_eq_dec_neq LL).
    rewrite (loc_ts_eq_dec_neq LL) in LHS.
    eapply PROM_IN_MEM; eauto. }

  assert (Memory.le promises_cancel memory_add) as PPC.
  { etransitivity; [|by apply PP].
    eapply memory_add_le; eauto. }

  assert (Memory.get locw (f_to w) (Local.promises local) =
          Some (f_from w, Message.reserve)) as INPROM.
  { eapply SIM_RES_MEM; eauto. }
  assert (Memory.get locw (f_to w) PC.(Configuration.memory) =
          Some (f_from w, Message.reserve)) as INMEM.
  { eapply PROM_IN_MEM in INPROM; eauto. }

  assert (forall thread' langst' local' (TNEQ : tid w <> thread')
                 (TID' : IdentMap.find thread' (Configuration.threads PC) =
                         Some (langst', local')),
             Memory.get locw (f_to w) (Local.promises local') = None) as NINTER.
  { ins. eapply PROM_DISJOINT with (loc:=locw) (to:=f_to w) in TID'; eauto. desf. }

  assert (forall tmap (MCLOS : Memory.closed_timemap tmap PC.(Configuration.memory)),
             Memory.closed_timemap tmap memory_add) as MADDCLOS.
  { ins. eapply Memory.add_closed_timemap; eauto.
    eapply Memory.cancel_closed_timemap; eauto. }

  set (rel'' :=
        if is_rel lab w
        then (TView.cur (Local.tview local))
        else (TView.rel (Local.tview local) locw)).
  set (rel' := (View.join (View.join rel'' p_rel.(View.unwrap))
                          (View.singleton_ur locw (f_to w)))).

  assert (exists promises',
             ⟪ PEQ : promises' = if Rel w
                                 then promises_cancel
                                 else promises_add ⟫).
  { destruct (is_rel lab w) eqn:REL; eauto. }
  desc.
  
  assert (Memory.le promises' promises_add) as LEPADD.
  { destruct (Rel w) eqn:RELB; subst; [|reflexivity].
    eapply memory_add_le; eauto. }

  assert (forall l to from msg 
                 (INP' : Memory.get l to promises' =
                         Some (from, msg))
                 (NEQ : l <> locw \/ to <> f_to w),
             Memory.get l to local.(Local.promises) = Some (from, msg))
    as NOTNEWP.
  { ins.
    assert (Memory.get l to promises_add = Some (from, msg)) as TT0.
    { by apply LEPADD. }
    assert (Memory.get l to promises_cancel = Some (from, msg)) as TT1.
    { erewrite Memory.add_o in TT0; eauto.
      rewrite loc_ts_eq_dec_neq in TT0; auto. }
    assert (Memory.get l to local.(Local.promises) = Some (from, msg)) as TT.
    { erewrite Memory.remove_o in TT1; eauto.
      rewrite loc_ts_eq_dec_neq in TT1; auto. }
    destruct msg.
    { edestruct SIM_PROM as [b H]; eauto; desc. }
    edestruct SIM_RES_PROM as [b H]; eauto; desc. }

  exists p_rel. splits; eauto.
  do 2 eexists. splits; eauto.
  do 2 eexists. splits; eauto.
  exists promises'. splits; eauto.
  { ins.
    destruct (Ident.eq_dec (tid e) (tid w)) as [EQ|NEQ].
    { rewrite EQ. rewrite IdentMap.gss.
      eexists. eauto. }
    rewrite IdentMap.gso; auto. }
  { apply Memory.promise_add; eauto; ins. }
  { ins.
    destruct (Ident.eq_dec thread' (tid w)) as [EQ|NEQ].
    { subst. rewrite IdentMap.gss in TID0.
      inv TID0; simpls; clear TID0. desf. }
    red; ins; rewrite IdentMap.gso in TID0; auto.
    erewrite Memory.add_o; eauto.
    destruct (loc_ts_eq_dec (loc, to) (locw, f_to w)) as [[A B]|LL].
    { simpls; rewrite A in *; rewrite B in *; subst.
      exfalso.
      erewrite NINTER in LHS; eauto. inv LHS. }
    rewrite (loc_ts_eq_dec_neq LL).
    erewrite Memory.remove_o; eauto.
    rewrite (loc_ts_eq_dec_neq LL).
    eapply PROM_IN_MEM in LHS; eauto. }
  { simpls. red. ins.
    destruct (loc_ts_eq_dec (l, to) (locw, f_to w)) as [[A' B']|LL].
    { simpls; rewrite A' in *; rewrite B' in *.
      destruct (Rel w) eqn:RELB; subst.
      { erewrite Memory.remove_o in PROM; eauto.
        rewrite (loc_ts_eq_dec_eq locw (f_to w)) in PROM. inv PROM. }
      erewrite Memory.add_o in PROM; eauto.
      rewrite (loc_ts_eq_dec_eq locw (f_to w)) in PROM.
      inv PROM. exists w. splits; eauto. by right. }
    eapply NOTNEWP in LL; eauto.
    edestruct SIM_PROM as [b H]; eauto; desc.
    exists b; splits; auto.
    { by left. }
    destruct (Rel w) eqn:RELB; auto.
    intros [HH|HH]; desf. }
  { simpls. red. ins.
    destruct (loc_ts_eq_dec (l, to) (locw, f_to w)) as [[A' B']|LL].
    { simpls; rewrite A' in *; rewrite B' in *.
      destruct (Rel w) eqn:RELB; subst.
      { erewrite Memory.remove_o in RES; eauto.
        rewrite (loc_ts_eq_dec_eq locw (f_to w)) in RES. inv RES. }
      erewrite Memory.add_o in RES; eauto.
      rewrite (loc_ts_eq_dec_eq locw (f_to w)) in RES. inv RES. }
    apply NOTNEWP in RES; auto.
    edestruct SIM_RES_PROM as [b H]; eauto; desc.
    exists b. splits; auto.
    { by left. }
    intros [A|A]; desf. }
  { ins.
    rewrite IdentMap.gso in TID'; auto.
    destruct (loc_ts_eq_dec (loc, to) (locw, (f_to w))) as [EQ|NEQ]; simpls.
    { desc. subst. right.
      destruct (Memory.get locw (f_to w) (Local.promises local')) eqn: HH; auto.
      exfalso.
      erewrite NINTER in HH; eauto. inv HH. }
    edestruct (PROM_DISJOINT TNEQ TID') as [HH|HH]; eauto.
    left.
    destruct (Memory.get loc to promises') eqn:BB; auto.
    destruct p. eapply NOTNEWP in BB; eauto. desf. }
  { red. ins.
    destruct ISSB as [ISSB|]; subst.
    { edestruct SIM_MEM as [rel_opt HH]; eauto. simpls. desc.
      exists rel_opt. unnw.
      destruct (loc_ts_eq_dec (l, f_to b) (locw, (f_to w))) as [EQ|NEQ]; simpls; desc; subst.
      { exfalso.
        assert (b = w); [|by desf].
        eapply f_to_eq with (I:=S); eauto.
        { red. by rewrite LOC. }
          by apply ETCCOH.(etc_I_in_S). }
      erewrite Memory.add_o with (mem2:=memory_add); eauto.
      erewrite Memory.remove_o with (mem2:=memory_cancel); eauto.
      rewrite !loc_ts_eq_dec_neq; auto.
      splits; eauto.
      (* TODO: continue from here. *)
      intros AA BB. specialize (HH1 AA BB).
      desc. splits; auto. eexists. splits; eauto.
      destruct HH2 as [[CC DD]|CC]; eauto.
      { left. split; auto.
        intros [u QQ]. destruct_seq_l QQ as UISS. destruct UISS as [UISS|]; subst.
        { apply CC. clear -QQ UISS. basic_solver 10. }
        apply NISSB. eapply rfrmw_I_in_I; eauto.
        clear -QQ ISSB. exists b. apply seqA. basic_solver 10. }
      right. desc.
      eexists. splits; eauto.
      { by left. }
      eexists; splits; eauto.
      erewrite Memory.add_o with (mem2:=memory_add); eauto.
      erewrite Memory.remove_o with (mem2:=memory_cancel); eauto.
      assert (loc lab p = loc lab b) as LOCPB by (by apply wf_rfrmwl). 
      destruct (loc_ts_eq_dec (l, f_to p) (locw, (f_to w))) as [PEQ|PNEQ];
        simpls; desc; subst.
      2: by rewrite !(loc_ts_eq_dec_neq PNEQ); auto.
      exfalso. assert (p = w); [|by desf].
      eapply f_to_eq with (I:=S); eauto.
      { red. rewrite LOC. by rewrite <- LOC0. }
        by apply ETCCOH.(etc_I_in_S). }
    assert (Some l = Some locw) as QQ.
    { by rewrite <- LOC0. }
    inv QQ.
    eexists. splits; eauto.
    { erewrite Memory.add_o; eauto. rewrite loc_ts_eq_dec_eq; eauto. }
    { apply HELPER. }
    { (* TODO: extend exists_time_interval_for_issue_reserved_no_next  *)
      admit. }
    { (* TODO: extend exists_time_interval_for_issue_reserved_no_next  *)
      admit. }
    ins. splits.
    { erewrite Memory.add_o; eauto. rewrite loc_ts_eq_dec_eq; eauto. }
    exists p_rel. splits; eauto.
    {
      (* destruct (Rel b) eqn:RELB; [|done]. *)
      (* exfalso. *)
      (* assert (covered T b); desf. *)
      (* apply RELCOV. split; [split|]; auto. *)
      admit. }
    admit. }
  red. ins.
  assert (b <> w /\ ~ issued T b) as [BNEQ NISSBB].
  { generalize NISSB0. clear. basic_solver. }
  destruct RESB as [SB|]; subst.
  2: by desf.
  unnw.
  erewrite Memory.add_o with (mem2:=memory_add); eauto.
  erewrite Memory.add_o with (mem2:=promises_add); eauto.
  erewrite Memory.remove_o with (mem2:=memory_cancel); eauto.
  erewrite Memory.remove_o with (mem2:=promises_cancel); eauto.
  destruct (loc_ts_eq_dec (l, f_to b) (locw, (f_to w))) as [PEQ|PNEQ];
    simpls; desc; subst.
  { exfalso. apply BNEQ.
    eapply f_to_eq with (I:=S); eauto. red. by rewrite LOC. }
  edestruct SIM_RES_MEM with (b:=b); eauto; unnw.
  splits; ins; rewrite (loc_ts_eq_dec_neq PNEQ).
  all: rewrite (loc_ts_eq_dec_neq PNEQ); auto.
Qed.

End IssueReservedStepHelper.
