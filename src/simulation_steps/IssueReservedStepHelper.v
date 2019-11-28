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

Require Import ImmProperties.
Require Import TraversalConfig.
Require Import ViewRelHelpers.
Require Import SimulationRel.
Require Import SimState.
Require Import MemoryAux.
Require Import MaxValue.
Require Import ViewRel.
Require Import Event_imm_promise.
Require Import ExtTraversal.
Require Import ExtTraversalProperties.
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

Lemma issue_reserved_step_helper_no_next w valw locw langst
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

        << INHAB : Memory.inhabited memory_add >> /\
        << RELMCLOS : Memory.closed_timemap (View.rlx rel') memory_add >> /\
        << RELVCLOS : Memory.closed_view rel' memory_add >> /\

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
        ⟪ SIM_RES_PROM : sim_res_prom G T' S' f_to f_from (tid w) promises'  ⟫ /\

        ⟪ PROM_DISJOINT :
            forall thread' langst' local'
                   (TNEQ : tid w <> thread')
                   (TID' : IdentMap.find thread' threads' =
                           Some (langst', local')),
            forall loc to,
              Memory.get loc to promises' = None \/
              Memory.get loc to local'.(Local.promises) = None ⟫ /\

        ⟪ SIM_MEM     : sim_mem G sc T' f_to f_from (tid w) local' memory_add ⟫ /\
        ⟪ SIM_RES_MEM : sim_res_mem G T' S' f_to f_from (tid w) local' memory_add ⟫.
Proof using All.
  assert (tc_coherent G sc T) as TCCOH by apply ETCCOH.

  subst.
  edestruct exists_time_interval_for_issue_reserved_no_next as [p_rel [PREL HH]]; eauto.
  simpls; desc.
  
  assert (~ issued T w) as NISSB.
  { eapply ext_itrav_step_iss_nI with (T:=mkETC T S); eauto. }
  assert (S ⊆₁ E ∩₁ W) as SEW.
  { apply set_subset_inter_r. split; [by apply ETCCOH|].
    apply (reservedW WF ETCCOH). }
  assert (E w /\ W w) as [EW WW] by (by apply SEW).
  assert (~ covered T w) as NCOVB.
  { intros AA. apply NISSB. eapply w_covered_issued; eauto. by split. }

  assert (W_ex w) as WEW.
  { apply ETCCOH. by split. }
  assert (codom_rel (⦗issued T⦘ ⨾ rf ⨾ rmw) w) as CDRFRMW.
  { eapply W_ex_in_codom_rfrmw in WEW; eauto.
    destruct WEW as [u WEW].
    exists u. apply seq_eqv_l. split; auto.
    eapply ExtTraversalProperties.dom_rf_rmw_S_in_I with (T:=mkETC T S); eauto.
    exists w. apply seqA. apply seq_eqv_r. split; auto. }

  assert (Memory.le promises_add memory_add) as PP.
  { eapply memory_le_add2 with (mem1:=promises_cancel) (mem2:=memory_cancel); eauto.
    eapply memory_le_remove2; eauto. }

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
                 (NEQ : l <> locw \/ to <> f_to w),
             Memory.get l to promises_cancel = Some (from, msg) <->
             Memory.get l to local.(Local.promises) = Some (from, msg))
    as NOTNEWC.
  { ins. erewrite Memory.remove_o; eauto.
    rewrite loc_ts_eq_dec_neq; auto. }

  assert (forall l to from msg 
                 (NEQ : l <> locw \/ to <> f_to w),
             Memory.get l to promises_add = Some (from, msg) <->
             Memory.get l to local.(Local.promises) = Some (from, msg))
    as NOTNEWA.
  { ins. erewrite Memory.add_o; eauto.
    rewrite loc_ts_eq_dec_neq; auto. }

  assert (forall l to from msg 
                 (NEQ : l <> locw \/ to <> f_to w),
             Memory.get l to promises' = Some (from, msg) <->
             Memory.get l to local.(Local.promises) = Some (from, msg))
    as NOTNEWP.
  { ins. destruct (Rel w); subst; auto. }

  assert (~ Rel w -> Memory.get locw (f_to w) promises' =
          Some (f_from w, Message.full valw (Some rel')))
    as INP''.
  { ins. destruct (Rel w); subst; [by desf|].
    erewrite Memory.add_o; eauto. by rewrite loc_ts_eq_dec_eq. }

  exists p_rel. splits; eauto.
  do 2 eexists. splits; eauto.
  do 2 eexists. splits; eauto.
  exists promises'. splits; eauto.
  { ins.
    destruct (Ident.eq_dec (tid e) (tid w)) as [EQ|NEQ].
    { rewrite EQ. rewrite IdentMap.gss.
      eexists. eauto. }
    rewrite IdentMap.gso; auto. }
  { apply Memory.promise_add; auto; ins.
    admit. }
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
    eapply NOTNEWP in PROM; eauto.
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
    { generalize RES0. basic_solver. }
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
      intros AA BB.
      assert (~ covered T b) as NCOVBB.
      { generalize BB. basic_solver. }
      specialize (HH1 AA NCOVBB).
      desc. splits; auto.
      { apply NOTNEWP; auto. }
      eexists. splits; eauto.
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
    { apply RELWFEQ. }
    { apply RELMCLOS. }
    intros _ NT.
    destruct (Rel b); desf.
    { exfalso. apply NT. by right. }
    splits.
    { erewrite Memory.add_o; eauto. rewrite loc_ts_eq_dec_eq; eauto. }
    exists p_rel. splits; eauto. right.
    cdes PREL. destruct PREL1; desc.
    { exfalso. eauto. }
    assert (S p) as SP.
    { by apply ETCCOH.(etc_I_in_S). }
    exists p. splits; eauto.
    { by left. }
    eexists. splits; eauto.
    eapply memory_add_le; eauto.
    erewrite Memory.remove_o; eauto.
    destruct (classic (f_to p = f_to b)) as [EQ|NEQ].
    2: { rewrite loc_ts_eq_dec_neq; auto. }
    exfalso. eapply f_to_eq with (I:=S) in EQ; eauto; subst.
    2: by apply WF.(wf_rfrmwl).
    eapply wf_rfrmw_irr; eauto. }
  red. ins.
  assert (b <> w /\ ~ issued T b) as [BNEQ NISSBB].
  { generalize NISSB0. clear. basic_solver. }
  destruct RESB as [[SB|]|HH]; subst.
  3: { exfalso. eapply NONEXT; eauto. }
  2: by desf.
  unnw.
  erewrite Memory.add_o with (mem2:=memory_add); eauto.
  erewrite Memory.remove_o with (mem2:=memory_cancel); eauto.
  destruct (loc_ts_eq_dec (l, f_to b) (locw, (f_to w))) as [PEQ|PNEQ];
    simpls; desc; subst.
  { exfalso. apply BNEQ.
    eapply f_to_eq with (I:=S); eauto. red. by rewrite LOC. }
  edestruct SIM_RES_MEM with (b:=b); eauto; unnw.
  rewrite !(loc_ts_eq_dec_neq PNEQ); auto.
  splits; ins.
  apply NOTNEWP; auto.
Admitted.

Lemma issue_reserved_step_helper_with_next w valw locw langst wnext
      (TID : IdentMap.find (tid w) PC.(Configuration.threads) = Some (langst, local))
      (TSTEP : ext_itrav_step
                 G sc w (mkETC T S)
                 (mkETC
                    (mkTC (covered T) (issued T ∪₁ eq w))
                    (S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G (mkETC T S) rfi (eq w))))
      (SW : S w)
      (WNEXT : dom_sb_S_rfrmw G (mkETC T S) rfi (eq w) wnext)
      (LOC : loc lab w = Some locw)
      (VAL : val lab w = Some valw)
      (WTID : thread = tid w) :
  let promises := local.(Local.promises) in
  let memory   := PC.(Configuration.memory) in
  let sc_view  := PC.(Configuration.sc) in
  let covered' := if Rel w then covered T ∪₁ eq w else covered T in
  let T'       := mkTC (covered T) (issued T ∪₁ eq w) in
  let S'       := S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G (mkETC T S) rfi (eq w) in
  let n_to     := Time.middle (f_from w) (f_to w) in
  let f_to'    := upd (upd f_to w n_to) wnext (f_to w) in
  let f_from'  := upd f_from wnext n_to in

  exists p_rel, rfrmw_prev_rel G sc T f_to f_from PC w locw p_rel /\
    let rel'' :=
        if is_rel lab w
        then (TView.cur (Local.tview local))
        else (TView.rel (Local.tview local) locw)
    in
    let rel' := (View.join (View.join rel'' p_rel.(View.unwrap))
                           (View.singleton_ur locw (f_to' w))) in

    ⟪ REL_VIEW_LT : Time.lt (View.rlx rel'' locw) (f_to' w) ⟫ /\
    ⟪ REL_VIEW_LE : Time.le (View.rlx rel' locw) (f_to' w) ⟫ /\

    exists promises_split memory_split,
      ⟪ PSPLIT :
          Memory.split local.(Local.promises) locw (f_from' w) (f_to' w) (f_to' wnext)
                       (Message.full valw (Some rel')) Message.reserve promises_split ⟫ /\
      ⟪ MSPLIT :
          Memory.split memory locw (f_from' w) (f_to' w) (f_to' wnext)
                       (Message.full valw (Some rel')) Message.reserve memory_split ⟫ /\

      << INHAB : Memory.inhabited memory_split >> /\
      << RELMCLOS : Memory.closed_timemap (View.rlx rel') memory_split >> /\
      << RELVCLOS : Memory.closed_view rel' memory_split >> /\

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
          reserved_time G T' S' f_to' f_from' smode memory_split ⟫ /\

      exists promises',
        ⟪ PEQ :
            if Rel w
            then Memory.remove promises_split locw (f_from' w) (f_to' w)
                               (Message.full valw (Some rel')) promises'
            else promises' = promises_split ⟫ /\

        let local' := Local.mk local.(Local.tview) promises' in
        let threads' :=
            IdentMap.add (tid w)
                         (langst, local')
                         (Configuration.threads PC) in

        ⟪ THREAD : forall e (ACT : E e) (NINIT : ~ is_init e),
            exists langst, IdentMap.find (tid e) threads' = Some langst ⟫ /\

        ⟪ SC_REQ : smode = sim_normal -> 
                   forall (l : Loc.t),
                     max_value f_to' (S_tm G l (covered T)) (LocFun.find l sc_view) ⟫ /\
        ⟪ CLOSED_SC : Memory.closed_timemap sc_view memory_split ⟫ /\

        ⟪ MEM_SPLIT :
            Memory.promise local.(Local.promises) memory locw (f_from' w) (f_to' w)
                           (Message.full valw (Some rel'))
                           promises_split memory_split
                           (Memory.op_kind_split (f_to' wnext) Message.reserve) ⟫ /\

        ⟪ PROM_IN_MEM :
            forall thread' langst local
                   (TID : IdentMap.find thread' threads' = Some (langst, local)),
              Memory.le local.(Local.promises) memory_split ⟫ /\

        ⟪ SIM_PROM     : sim_prom G sc T' f_to' f_from' (tid w) promises'  ⟫ /\
        ⟪ SIM_RES_PROM : sim_res_prom G T' S' f_to' f_from' (tid w) promises'  ⟫ /\

        ⟪ PROM_DISJOINT :
            forall thread' langst' local'
                   (TNEQ : tid w <> thread')
                   (TID' : IdentMap.find thread' threads' =
                           Some (langst', local')),
            forall loc to,
              Memory.get loc to promises' = None \/
              Memory.get loc to local'.(Local.promises) = None ⟫ /\

        ⟪ SIM_MEM     : sim_mem G sc T' f_to' f_from' (tid w) local' memory_split ⟫ /\
        ⟪ SIM_RES_MEM : sim_res_mem G T' S' f_to' f_from' (tid w) local' memory_split ⟫.
Proof using All.
  assert (sc_per_loc G) as SPL.
  { apply coherence_sc_per_loc. apply IMMCON. }
  assert (complete G) as COMPL by apply IMMCON.
  assert (tc_coherent G sc T) as TCCOH by apply ETCCOH.

  subst.
  edestruct exists_time_interval_for_issue_reserved_with_next as [p_rel [PREL HH]]; eauto.
  simpls; desc.
  
  assert (~ issued T w) as NISSB.
  { eapply ext_itrav_step_iss_nI with (T:=mkETC T S); eauto. }
  assert (S ⊆₁ E ∩₁ W) as SEW.
  { apply set_subset_inter_r. split; [by apply ETCCOH|].
    apply (reservedW WF ETCCOH). }
  assert (E w /\ W w) as [EW WW] by (by apply SEW).
  assert (~ covered T w) as NCOVB.
  { intros AA. apply NISSB. eapply w_covered_issued; eauto. by split. }

  assert (W_ex w) as WEW.
  { apply ETCCOH. by split. }
  assert (codom_rel (⦗issued T⦘ ⨾ rf ⨾ rmw) w) as CDRFRMW.
  { eapply W_ex_in_codom_rfrmw in WEW; eauto.
    destruct WEW as [u WEW].
    exists u. apply seq_eqv_l. split; auto.
    eapply ExtTraversalProperties.dom_rf_rmw_S_in_I with (T:=mkETC T S); eauto.
    exists w. apply seqA. apply seq_eqv_r. split; auto. }

  assert (Memory.le promises_split memory_split) as PP.
  { eapply memory_le_split2; eauto. }

  set (n_to     := Time.middle (f_from w) (f_to w)).
  set (f_to'    := upd (upd f_to w n_to) wnext (f_to w)).
  set (f_from'  := upd f_from wnext n_to).
  set (rel'' :=
        if is_rel lab w
        then (TView.cur (Local.tview local))
        else (TView.rel (Local.tview local) locw)).
  set (rel' := (View.join (View.join rel'' p_rel.(View.unwrap))
                          (View.singleton_ur locw (f_to' w)))).

  assert (exists promises',
             ⟪ PEQ : if Rel w
                     then
                       Memory.remove promises_split locw
                                     (f_from' w) (f_to' w)
                                     (Message.full valw (Some rel'))
                                     promises'
                     else promises' = promises_split ⟫).
  { destruct (is_rel lab w) eqn:REL; eauto.
    unnw. apply Memory.remove_exists. erewrite Memory.split_o; eauto.
      by rewrite loc_ts_eq_dec_eq. }
  desc.

  assert (Memory.le promises' memory_split) as PPC.
  { etransitivity; [|by apply PP].
    destruct (Rel w); subst.
    2: by apply Memory.le_PreOrder.
    eapply memory_remove_le; eauto. }

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
             Memory.closed_timemap tmap memory_split) as MSPLITCLOS.
  { ins. eapply Memory.split_closed_timemap; eauto. }
  desc.

  assert (~ issued T w) as WNISS.
  { eapply ext_itrav_step_iss_nI with (T:=mkETC T S); eauto. }
  assert (~ covered T w) as WNCOV.
  { intros HH. apply WNISS.
    eapply w_covered_issued; [by apply ETCCOH|by split]. }
  assert (~ is_init w) as WNINIT.
  { intros HH. apply WNCOV. eapply init_covered; [by apply ETCCOH| by split]. }

  assert (issuable G sc T w) as ISSUABLE.
  { eapply ext_itrav_step_iss_issuable with (T:=mkETC T S); eauto. }

  assert ((rf ⨾ rmw) w wnext) as RFRMWNEXT.
  { destruct WNEXT as [_ BB]. generalize BB. unfold Execution.rfi.
    clear. basic_solver. }
  assert (w <> wnext) as NEQNEXT.
  { intros HH; subst. eapply wf_rfrmw_irr; eauto. }
  assert (co w wnext) as COWNEXT.
  { apply rf_rmw_in_co; auto. }
  assert (~ is_init wnext) as NINITNEXT.
  { apply no_co_to_init in COWNEXT; auto. by destruct_seq_r COWNEXT as AA. }
  assert (E wnext) as EWNEXT.
  { apply WF.(wf_coE) in COWNEXT. by destruct_seq COWNEXT as [AA BB]. }
  assert (~ S wnext) as NSNEXT.
  { intros HH. apply WNISS. eapply dom_rf_rmw_S_in_I with (T:=mkETC T S); eauto.
    exists wnext. apply seqA. apply seq_eqv_r. by split. }
  assert (~ issued T wnext) as NINEXT.
  { intros HH. apply NSNEXT. by apply ETCCOH.(etc_I_in_S). }
  assert (loc lab wnext = Some locw) as NLOC.
  { rewrite <- LOC. symmetry. by apply wf_rfrmwl. }
  
  assert (forall l to from msg 
                 (NEQ  : l <> locw \/ to <> f_to w)
                 (NEQ' : l <> locw \/ to <> f_to' w),
             Memory.get l to promises' = Some (from, msg) <->
             Memory.get l to local.(Local.promises) = Some (from, msg))
    as NOTNEWC.
  { ins.
    destruct (Rel w); subst.
    erewrite Memory.remove_o; eauto.
    rewrite loc_ts_eq_dec_neq; auto.
    all: erewrite Memory.split_o; eauto.
    all: repeat (rewrite loc_ts_eq_dec_neq; auto).
    all: by unfold f_to' in NEQ'; rewrite upds. }

  (* assert (forall l to from msg  *)
  (*                (NEQ : l <> locw \/ to <> f_to w), *)
  (*            Memory.get l to promises_add = Some (from, msg) <-> *)
  (*            Memory.get l to local.(Local.promises) = Some (from, msg)) *)
  (*   as NOTNEWA. *)
  (* { ins. erewrite Memory.add_o; eauto. *)
  (*   rewrite loc_ts_eq_dec_neq; auto. } *)

  (* assert (forall l to from msg  *)
  (*                (NEQ : l <> locw \/ to <> f_to w), *)
  (*            Memory.get l to promises' = Some (from, msg) <-> *)
  (*            Memory.get l to local.(Local.promises) = Some (from, msg)) *)
  (*   as NOTNEWP. *)
  (* { ins. destruct (Rel w); subst; auto. } *)

  (* assert (~ Rel w -> Memory.get locw (f_to w) promises' = *)
  (*         Some (f_from w, Message.full valw (Some rel'))) *)
  (*   as INP''. *)
  (* { ins. destruct (Rel w); subst; [by desf|]. *)
  (*   erewrite Memory.add_o; eauto. by rewrite loc_ts_eq_dec_eq. } *)

  assert (ISSEQ_TO : forall e (ISS: issued T e), f_to' e = f_to e).
  { ins. unfold f_to'. by repeat (rewrite updo; [|by intros HH; desf]). }

  assert (ISSEQ_FROM : forall e (ISS: issued T e), f_from' e = f_from e).
  { ins. unfold f_from'. by rewrite updo; [|by intros HH; desf]. }

  assert (forall l to omsg 
                 (NEQ  : l <> locw \/ to <> f_to' w)
                 (NEQ' : l <> locw \/ to <> f_to' wnext),
             Memory.get l to promises_split = omsg <->
             Memory.get l to local.(Local.promises) = omsg)
    as NOTNEWA.
  { ins. erewrite Memory.split_o; eauto.
    repeat (rewrite loc_ts_eq_dec_neq; auto). }

  assert (forall l to omsg 
                 (NEQ : l <> locw \/ to <> f_to' w)
                 (NEQ' : l <> locw \/ to <> f_to' wnext),
             Memory.get l to promises' = omsg <->
             Memory.get l to local.(Local.promises) = omsg)
    as NOTNEWP.
  { ins. destruct (Rel w); subst; auto.
    erewrite Memory.remove_o; eauto. rewrite (loc_ts_eq_dec_neq NEQ); auto. }
  
  assert (f_to' wnext = f_to w) as FTOWNEXT.
  { unfold f_to'. by rewrite upds. }

  exists p_rel. splits; eauto.
  do 2 eexists. splits; eauto.
  eexists. splits; eauto.
  { ins.
    destruct (Ident.eq_dec (tid e) (tid w)) as [EQ|NEQ].
    { rewrite EQ. rewrite IdentMap.gss.
      eexists. eauto. }
    rewrite IdentMap.gso; auto. }
  { ins. apply max_value_new_f with (f:=f_to); auto.
    ins. apply ISSEQ_TO. eapply S_tm_covered; eauto. }
  { ins.
    destruct (Ident.eq_dec thread' (tid w)) as [EQ|NEQ].
    { subst. rewrite IdentMap.gss in TID0.
      inv TID0; simpls; clear TID0. }
    red; ins; rewrite IdentMap.gso in TID0; auto.
    erewrite Memory.split_o; eauto.
    destruct (loc_ts_eq_dec (loc, to) (locw, f_to' w)) as [[A B]|LL].
    { simpls; rewrite A in *; rewrite B in *; subst.
      exfalso. admit. }
    rewrite (loc_ts_eq_dec_neq LL).
    destruct (loc_ts_eq_dec (loc, to) (locw, f_to' wnext)) as [[A B]|LL'].
    { simpls; rewrite A in *; rewrite B in *; subst.
      exfalso. admit. }
    rewrite (loc_ts_eq_dec_neq LL').
    eapply PROM_IN_MEM in LHS; eauto. }
  { simpls. red. ins.
    destruct (loc_ts_eq_dec (l, to) (locw, f_to' w)) as [[A' B']|LL].
    { simpls; rewrite A' in *; rewrite B' in *.
      destruct (Rel w) eqn:RELB; subst.
      { erewrite Memory.remove_o in PROM; eauto.
        rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in PROM. inv PROM. }
      erewrite Memory.split_o in PROM; eauto.
      rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in PROM.
      inv PROM. exists w. splits; eauto. by right. }
    destruct (loc_ts_eq_dec (l, to) (locw, f_to' wnext)) as [[A' B']|LL'].
    { simpls; rewrite A' in *; rewrite B' in *; subst.
      destruct (Rel w) eqn:RELB; subst.
      erewrite Memory.remove_o in PROM; eauto.
      rewrite (loc_ts_eq_dec_neq LL) in PROM.
      all: erewrite Memory.split_o in PROM; eauto.
      all: rewrite (loc_ts_eq_dec_neq LL) in PROM.
      all: rewrite (loc_ts_eq_dec_eq locw (f_to' wnext)) in PROM.
      all: inv PROM. }
    apply NOTNEWP in PROM; auto.
    edestruct SIM_PROM as [b H]; eauto; desc.
    exists b; splits; auto.
    { by left. }
    { by rewrite ISSEQ_FROM; auto. }
    { by rewrite ISSEQ_TO; auto. }
    eapply sim_mem_helper_f_issued; eauto. }
  { simpls. red. ins.
    destruct (loc_ts_eq_dec (l, to) (locw, f_to' w)) as [[A' B']|LL].
    { simpls; rewrite A' in *; rewrite B' in *.
      destruct (Rel w) eqn:RELB; subst.
      { erewrite Memory.remove_o in RES; eauto.
        rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in RES. inv RES. }
      erewrite Memory.split_o in RES; eauto.
      rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in RES. inv RES. }
    destruct (loc_ts_eq_dec (l, to) (locw, f_to' wnext)) as [[A' B']|LL'].
    { simpls; rewrite A' in *; rewrite B' in *.
      exists wnext. splits; eauto.
      { admit. }
      { by right. }
      { intros [A|A]; desf. }
      destruct (Rel w) eqn:RELB; subst.
      erewrite Memory.remove_o in RES; eauto.
      rewrite (loc_ts_eq_dec_neq LL) in RES.
      all: erewrite Memory.split_o in RES; eauto.
      all: rewrite (loc_ts_eq_dec_eq locw (f_to' wnext)) in RES.
      all: rewrite (loc_ts_eq_dec_neq LL) in RES.
      all: inv RES; rewrite updo; auto; rewrite upds.
      all: unfold f_from'; rewrite upds; auto. }
    apply NOTNEWP in RES; auto.
    edestruct SIM_RES_PROM as [b H]; eauto; desc.
    simpls.
    assert (b <> w) as NEQ.
    { intros A; subst. rewrite LOC in LOC0. inv LOC0.
      rewrite FTOWNEXT in LL'. clear -LL'. desf. }
    assert (b <> wnext) as NEQ'.
    { intros A; desf. }
    exists b. splits; auto.
    { generalize RES0. clear. basic_solver. }
    { intros [A|A]; desf. }
    { unfold f_from'. rewrite updo; auto. }
    unfold f_to'. repeat (rewrite updo; auto). }
  { ins.
    rewrite IdentMap.gso in TID'; auto.
    destruct (loc_ts_eq_dec (loc, to) (locw, (f_to' w))) as [EQ|NEQ]; simpls.
    { desc. subst. right.
      destruct (Memory.get locw (f_to' w) (Local.Local.promises local')) eqn: HH; auto.
      exfalso.
      destruct p as [from msg].
      eapply PROM_IN_MEM in HH; eauto.
      edestruct Memory.split_get0 as [Y1 Y2].
      { apply MSPLIT. }
      red in Y1. unfold f_to', n_to in HH. rewrite Y1 in HH.
      inv HH. }
    destruct (loc_ts_eq_dec (loc, to) (locw, (f_to' wnext))) as [EQ|NEQ2]; simpls.
    { desc. subst. right. rewrite FTOWNEXT.
      edestruct (PROM_DISJOINT TNEQ TID') as [HH|HH]; eauto. }
    rewrite NOTNEWP; auto. eapply PROM_DISJOINT; eauto. }
  (* TODO: continue from here *)
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
      intros AA BB.
      assert (~ covered T b) as NCOVBB.
      { generalize BB. basic_solver. }
      specialize (HH1 AA NCOVBB).
      desc. splits; auto.
      { apply NOTNEWP; auto. }
      eexists. splits; eauto.
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
    { apply RELWFEQ. }
    { apply RELMCLOS. }
    intros _ NT.
    destruct (Rel b); desf.
    { exfalso. apply NT. by right. }
    splits.
    { erewrite Memory.add_o; eauto. rewrite loc_ts_eq_dec_eq; eauto. }
    exists p_rel. splits; eauto. right.
    cdes PREL. destruct PREL1; desc.
    { exfalso. eauto. }
    assert (S p) as SP.
    { by apply ETCCOH.(etc_I_in_S). }
    exists p. splits; eauto.
    { by left. }
    eexists. splits; eauto.
    eapply memory_add_le; eauto.
    erewrite Memory.remove_o; eauto.
    destruct (classic (f_to p = f_to b)) as [EQ|NEQ].
    2: { rewrite loc_ts_eq_dec_neq; auto. }
    exfalso. eapply f_to_eq with (I:=S) in EQ; eauto; subst.
    2: by apply WF.(wf_rfrmwl).
    eapply wf_rfrmw_irr; eauto. }
  red. ins.
  assert (b <> w /\ ~ issued T b) as [BNEQ NISSBB].
  { generalize NISSB0. clear. basic_solver. }
  destruct RESB as [[SB|]|HH]; subst.
  3: { exfalso. eapply NONEXT; eauto. }
  2: by desf.
  unnw.
  erewrite Memory.add_o with (mem2:=memory_add); eauto.
  erewrite Memory.remove_o with (mem2:=memory_cancel); eauto.
  destruct (loc_ts_eq_dec (l, f_to b) (locw, (f_to w))) as [PEQ|PNEQ];
    simpls; desc; subst.
  { exfalso. apply BNEQ.
    eapply f_to_eq with (I:=S); eauto. red. by rewrite LOC. }
  edestruct SIM_RES_MEM with (b:=b); eauto; unnw.
  rewrite !(loc_ts_eq_dec_neq PNEQ); auto.
  splits; ins.
  apply NOTNEWP; auto.
Admitted.

End IssueReservedStepHelper.
