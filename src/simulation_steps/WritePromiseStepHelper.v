Require Import Setoid PArith.
From hahn Require Import Hahn.
Require Import PromisingLib.
From Promising2 Require Import TView View Time Event Cell Thread Memory Configuration.

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
Require Import ExistsTimeInterval.

Set Implicit Arguments.

Section WritePromiseStepHelper.

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


Lemma write_promise_step_helper f_to f_from T PC w locw valw ordw langst local smode
      (IMMCON : imm_consistent G sc)
      (TCCOH : tc_coherent G sc T)
      (WNISS : ~ issued T w)
      (WISSUABLE : issuable G T w)
      (LOC : loc lab w = Some locw)
      (VAL : val lab w = Some valw)
      (ORD : mod lab w = ordw)
      (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
      (THREAD : forall e (ACT : E e) (NINIT : ~ is_init e),
          exists langst, IdentMap.find (tid e) PC.(Configuration.threads) = Some langst)
      (PROM_IN_MEM :
         forall thread' langst local
                (TID : IdentMap.find thread' PC.(Configuration.threads) =
                       Some (langst, local)),
           Memory.le local.(Local.Local.promises) PC.(Configuration.memory))
      (FCOH : f_to_coherent G (issued T) f_to f_from)
      (SC_COV : smode = sim_certification -> E∩₁F∩₁Sc ⊆₁ covered T)
      (SC_REQ : smode = sim_normal -> 
                forall (l : Loc.t),
                  max_value f_to (S_tm G l (covered T)) (LocFun.find l PC.(Configuration.sc)))
      (SIM_PROM : sim_prom G sc (tid w) T f_to f_from local.(Local.Local.promises))
      (RESERVED_TIME: reserved_time G f_to f_from (issued T) PC.(Configuration.memory) smode)
      (CLOSED_SC : Memory.closed_timemap PC.(Configuration.sc) PC.(Configuration.memory))
      (FUTURE : Memory.future Memory.init (Configuration.memory PC))
      (PROM_DISJOINT :
         forall thread' langst' local'
                (TNEQ : tid w <> thread')
                (TID' : IdentMap.find thread' PC.(Configuration.threads) =
                        Some (langst', local')),
         forall loc to,
           Memory.get loc to local .(Local.Local.promises) = None \/
           Memory.get loc to local'.(Local.Local.promises) = None)
      (SIM_MEM : sim_mem G sc T f_to f_from
                         (tid w) local PC.(Configuration.memory))
      (SIM_TVIEW : sim_tview G sc (covered T) f_to local.(Local.Local.tview) (tid w))
      (PLN_RLX_EQ : pln_rlx_eq local.(Local.Local.tview))
      (MEM_CLOSE : memory_close local.(Local.Local.tview) PC.(Configuration.memory))
      (TID : IdentMap.find (tid w) PC.(Configuration.threads) = Some (langst, local)) :
  let memory := PC.(Configuration.memory) in
  let sc_view := PC.(Configuration.sc) in
  exists p_rel,
    (⟪ REL_PLN_RLX : View.pln p_rel.(View.unwrap) = View.rlx p_rel.(View.unwrap) ⟫ /\
     ⟪ P_MEM_CLOS : Memory.closed_timemap (View.rlx p_rel.(View.unwrap)) memory ⟫) /\
     ⟪ P_REL_CH :
         (⟪ NINRMW : ~ codom_rel (⦗ issued T ⦘ ⨾ rf ⨾ rmw) w ⟫ /\
          ⟪ PREL : p_rel = None ⟫) \/
         (exists p,
             ⟪ EP  : E p ⟫ /\
             ⟪ ISSP  : issued T p ⟫ /\
             ⟪ INRMW : (rf ⨾ rmw) p w ⟫ /\
             ⟪ P_LOC : loc lab p = Some locw ⟫ /\
             ⟪ P_MSG : sim_msg G sc f_to p p_rel.(View.unwrap) ⟫  /\
           exists p_v,
             ⟪ P_VAL : val lab p = Some p_v ⟫ /\
             ⟪ P_INMEM : Memory.get locw (f_to p) memory =
                         Some (f_from p, Message.full p_v p_rel) ⟫)⟫ /\
  (⟪ FOR_ISSUE :
     exists f_to' f_from' promises' memory' promises'',
     let rel'' :=
         if is_rel lab w
         then (TView.cur (Local.Local.tview local))
         else (TView.rel (Local.Local.tview local) locw)
     in
     let rel := (View.join (View.join rel'' p_rel.(View.unwrap))
                           (View.singleton_ur locw (f_to' w))) in

     let tview' := if is_rel lab w
                   then TView.write_tview local.(Local.Local.tview) sc_view locw
                                          (f_to' w) (Event_imm_promise.wmod ordw)
                   else local.(Local.Local.tview) in
     let local' := Local.Local.mk tview' promises'' in
     let threads' :=
         IdentMap.add (tid w)
                      (langst, local')
                      (Configuration.threads PC) in

     ⟪ ISSEQ_TO   : forall e (ISS: issued T e), f_to'   e = f_to   e ⟫ /\
     ⟪ ISSEQ_FROM : forall e (ISS: issued T e), f_from' e = f_from e ⟫ /\

     ⟪ REL_VIEW_LT : Time.lt (View.rlx rel'' locw) (f_to' w) ⟫ /\

     ⟪ PEQ :
         if Rel w
         then Memory.remove promises' locw (f_from' w) (f_to' w) valw
                            (Some rel) promises''
         else promises'' = promises' ⟫ /\

     ⟪ PADD :
       Memory.add local.(Local.Local.promises) locw (f_from' w) (f_to' w) valw
                                         (Some rel) promises' ⟫ /\

     ⟪ MADD :
        Memory.add memory locw (f_from' w) (f_to' w) valw
                   (Some rel) memory' ⟫ /\
     ⟪ MFUTURE :
        Memory.future Memory.init memory' ⟫ /\

     ⟪ HELPER :
         sim_mem_helper
           G sc f_to' w (f_from' w) valw
           (View.join (View.join (if is_rel lab w
                                  then (TView.cur (Local.Local.tview local))
                                  else (TView.rel (Local.Local.tview local) locw))
                                 p_rel.(View.unwrap))
                      (View.singleton_ur locw (f_to' w))) ⟫ /\

     ⟪ THREAD : forall e (ACT : E e) (NINIT : ~ is_init e),
         exists langst, IdentMap.find (tid e) threads' = Some langst ⟫ /\
     ⟪ PROM_IN_MEM :
         forall thread' langst local
                (TID : IdentMap.find thread' threads' = Some (langst, local)),
           Memory.le local.(Local.Local.promises) memory' ⟫ /\

     ⟪ FCOH: f_to_coherent G (issued T ∪₁ eq w) f_to' f_from' ⟫ /\
     ⟪ SC_REQ : smode = sim_normal -> 
                forall (l : Loc.t),
                  max_value f_to' (S_tm G l (covered T)) (LocFun.find l sc_view) ⟫ /\
     ⟪ CLOSED_SC : Memory.closed_timemap sc_view memory' ⟫ /\

     let covered' := if Rel w then covered T ∪₁ eq w else covered T in
     ⟪ SIM_PROM : sim_prom G sc (tid w)
                           (mkTC covered' (issued T ∪₁ eq w))
                           f_to' f_from' promises''  ⟫ /\
     ⟪ RESERVED_TIME :
         reserved_time G f_to' f_from' (issued T ∪₁ eq w) memory' smode ⟫ /\

     ⟪ PROM_DISJOINT :
         forall thread' langst' local'
                (TNEQ : tid w <> thread')
                (TID' : IdentMap.find thread' threads' =
                        Some (langst', local')),
         forall loc to,
           Memory.get loc to promises'' = None \/
           Memory.get loc to local'.(Local.Local.promises) = None ⟫ /\

     ⟪ SIM_MEM : sim_mem G sc (mkTC covered' (issued T ∪₁ eq w))
                         f_to' f_from' (tid w) local' memory' ⟫ /\

     ⟪ MEM_PROMISE :
         Memory.promise (Local.Local.promises local) memory locw (f_from' w) (f_to' w)
                        valw (Some rel) promises' memory' Memory.op_kind_add ⟫ /\

     ⟪ REL_CLOSE : Memory.closed_opt_view (Some rel) memory' ⟫ /\
     ⟪ NEW_CLOSE : Memory.closed_timemap (TimeMap.singleton locw (f_to' w)) memory' ⟫ /\
     ⟪ VIEW_CLOSE : memory_close tview' memory' ⟫ /\

     ⟪ NOWLOC : Rel w -> Memory.nonsynch_loc locw (Local.Local.promises local) ⟫
   ⟫ \/
   ⟪ FOR_SPLIT :
     ⟪ NREL : ~ Rel w ⟫ /\
     ⟪ SMODE : smode = sim_certification ⟫ /\

     exists ws valws relws rel f_to' f_from' promises' memory',
     let local' := Local.Local.mk (Local.Local.tview local) promises' in
     let threads' :=
         IdentMap.add (tid w)
                      (langst, local')
                      (Configuration.threads PC) in
     ⟪ ISSEQ_TO   : forall e (ISS: issued T e), f_to' e = f_to e ⟫ /\
     ⟪ ISSEQ_FROM :
        forall e (ISS: (issued T \₁ eq ws) e), f_from' e = f_from e ⟫ /\

     ⟪ PADD :
        Memory.split (Local.Local.promises local)
                     locw (f_from' w) (f_to' w) (f_to' ws) valw valws
                     rel relws promises' ⟫ /\
     ⟪ MADD :
        Memory.split memory locw (f_from' w) (f_to' w) (f_to' ws) valw valws
                     rel relws memory' ⟫ /\
     ⟪ MFUTURE :
        Memory.future Memory.init memory' ⟫ /\
      
     ⟪ WSISS  : issued T ws ⟫ /\
     ⟪ WSNCOV : ~ covered T ws ⟫ /\
     ⟪ WSVAL : val lab ws = Some valws ⟫ /\

     ⟪ SBWW : sb w ws ⟫ /\
     ⟪ SAME_LOC : Loc_ locw ws ⟫ /\
     ⟪ COWW : co w ws ⟫ /\

     ⟪ FEQ1 : f_to' w = f_from' ws ⟫ /\
     ⟪ FEQ2 : f_from' w = f_from ws ⟫ /\

     ⟪ THREAD : forall e (ACT : E e) (NINIT : ~ is_init e),
         exists langst, IdentMap.find (tid e) threads' = Some langst ⟫ /\
     ⟪ PROM_IN_MEM :
         forall thread' langst local
                (TID : IdentMap.find thread' threads' = Some (langst, local)),
           Memory.le local.(Local.Local.promises) memory' ⟫ /\

     ⟪ FCOH : f_to_coherent G (issued T ∪₁ eq w) f_to' f_from' ⟫ /\

     ⟪ CLOSED_SC : Memory.closed_timemap sc_view memory' ⟫ /\

     ⟪ SIM_PROM : sim_prom G sc (tid w)
                           (mkTC (covered T) (issued T ∪₁ eq w))
                           f_to' f_from' promises' ⟫ /\
     ⟪ RESERVED_TIME :
            reserved_time G f_to' f_from' (issued T ∪₁ eq w) memory' sim_certification ⟫ /\

     ⟪ PROM_DISJOINT :
         forall thread' langst' local'
                (TNEQ : tid w <> thread')
                (TID' : IdentMap.find thread' threads' =
                        Some (langst', local')),
         forall loc to,
           Memory.get loc to promises' = None \/
           Memory.get loc to local'.(Local.Local.promises) = None ⟫ /\
     ⟪ SIM_MEM : sim_mem G sc (mkTC (covered T) (issued T ∪₁ eq w))
                         f_to' f_from' (tid w) local' memory' ⟫ /\
     ⟪ MEM_PROMISE :
         Memory.promise (Local.Local.promises local) memory locw (f_from' w) (f_to' w)
                        valw rel promises' memory'
                        (Memory.op_kind_split (f_to' ws) valws relws) ⟫ /\
     ⟪ REL_CLOSE : Memory.closed_opt_view rel memory' ⟫
   ⟫).
Proof.
  assert (Memory.inhabited PC.(Configuration.memory)) as INHAB.
  { by apply inhabited_future_init. }

  assert (W w) as WW.
  { apply WISSUABLE. }

  assert (E w) as EW.
  { apply WISSUABLE. }
  
  assert (~ covered T w) as WNCOV.
  { intros COV. apply WNISS.
      by eapply w_covered_issued; eauto; split. }

  assert (~ is_init w) as WNINIT.
  { intros H. apply WNCOV. apply TCCOH. by split. }

  assert ((E ∩₁ W ∩₁ Loc_ locw) w) as WEW.
  { split; [split|]; auto. }

  assert (tc_coherent G sc (mkTC (covered T) (issued T ∪₁ eq w))) as TCCOH'.
  { eapply trav_step_coherence; eauto. exists w; right. by splits. }

  edestruct exists_time_interval as [p_rel].
  3: by apply TCCOH.
  all: eauto.
  desc.
  exists p_rel; split; auto.
  split; auto.
  destruct H1; desc.
  { red in H; desc. simpls. left.
    assert (Memory.closed_timemap
              (TimeMap.singleton locw (f_to' w)) memory') as NEW_CLOSE.
    { unfold TimeMap.singleton, LocFun.add.
      red. intros loc. erewrite Memory.add_o; eauto.
      destruct (Loc.eq_dec loc locw) as [|NEQ]; subst.
      { eexists; eexists; eexists. 
        rewrite loc_ts_eq_dec_eq. eauto. }
      rewrite loc_ts_eq_dec_neq.
      2: by left.
      unfold LocFun.find, LocFun.init.
      rewrite INHAB. destruct Message.elt.
      eauto. }

    assert (exists promises'', 
               if Rel w
               then Memory.remove promises' locw (f_from' w) (f_to' w) valw
                                  (Some
                                     (View.join
                                        (View.join
                                           (if Rel w
                                            then TView.cur (Local.Local.tview local)
                                            else TView.rel (Local.Local.tview local) locw) 
                                           (View.unwrap p_rel))
                                        (View.singleton_ur locw (f_to' w)))) promises''
               else promises'' = promises')
      as [promises'' PEQ].
    { destruct (is_rel lab w); eauto.
      apply Memory.remove_exists.
      erewrite Memory.add_o; eauto.
        by rewrite loc_ts_eq_dec_eq. }

    assert (Memory.closed_timemap
              (TimeMap.join
                 (TimeMap.join
                    (View.rlx
                       (if Rel w
                        then TView.cur (Local.Local.tview local)
                        else TView.rel (Local.Local.tview local) locw))
                    (View.rlx (View.unwrap p_rel)))
                 (TimeMap.singleton locw (f_to' w))) memory') as YY.
    { apply Memory.join_closed_timemap.
      { eapply closedness_preserved_add; eauto.
        destruct (is_rel lab w); simpls.
        all: apply Memory.join_closed_timemap; auto.
        all: apply MEM_CLOSE. }
      eapply Memory.singleton_closed_timemap.
      2: by eapply Memory.add_inhabited; eauto.
      erewrite Memory.add_o; eauto.
        by rewrite loc_ts_eq_dec_eq. }

    eexists; eexists; exists promises'; exists memory'; exists promises''; splits; eauto.
    { etransitivity; eauto.
      apply clos_rt1n_step.
      econstructor.
      { apply Memory.op_add. eauto. }
      { constructor. constructor; simpls.
        rewrite REL_PLN_RLX.
        cdes PLN_RLX_EQ.
        destruct (Rel w).
        { by rewrite EQ_CUR. }
          by rewrite EQ_REL. }
      eauto. }
    { ins.
      destruct (Ident.eq_dec (tid e) (tid w)) as [EQ|NEQ].
      { rewrite EQ. rewrite IdentMap.gss.
        eexists. eauto. }
      rewrite IdentMap.gso; auto. }
    { ins.
      assert (Memory.le PC.(Configuration.memory) memory') as MM.
      { red; ins.
        erewrite Memory.add_o; eauto.
        destruct (loc_ts_eq_dec (loc, to) (locw, f_to' w)) as [[A B]|LL].
        2: by rewrite (loc_ts_eq_dec_neq LL).
        simpls; rewrite A in *; rewrite B in *.
        exfalso.
        erewrite Memory.add_get0 in LHS; eauto.
        inv LHS. }
      destruct (Ident.eq_dec thread' (tid w)) as [EQ|NEQ].
      { subst. rewrite IdentMap.gss in TID0.
        inv TID0; simpls; clear TID0.
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
        destruct (Rel w); subst; auto.
        etransitivity; eauto.
        eapply memory_remove_le; eauto. }
      red; ins; rewrite IdentMap.gso in TID0; auto.
      eapply PROM_IN_MEM in LHS; eauto. }
    { intros NFSC l; simpls.
      eapply sc_view_f_issued; eauto. }
    { eapply closedness_preserved_add; eauto. }
    { simpls. red. ins.
      destruct (is_rel lab w) eqn:WREL; subst.
      { erewrite Memory.remove_o in PROM; eauto.
        destruct (loc_ts_eq_dec (l, to) (locw, f_to' w)) as [[A' B']|LL].
        { simpls; rewrite A' in *; rewrite B' in *.
          rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in PROM; desf. }
        rewrite (loc_ts_eq_dec_neq LL) in PROM.
        erewrite Memory.add_o in PROM; eauto.
        rewrite (loc_ts_eq_dec_neq LL) in PROM.
        edestruct SIM_PROM as [b H]; eauto; desc.
        rewrite <- ISSEQ_TO in TO; auto.
        rewrite <- ISSEQ_FROM in FROM; auto.
        exists b; splits; auto.
        { by left. }
        { intros [H|H]; desf. }
        cdes IMMCON.
        eapply sim_mem_helper_fS.
        6: by apply HELPER0.
        5: by apply ISSEQ_TO.
        all: auto. }
      erewrite Memory.add_o in PROM; eauto.
      destruct (loc_ts_eq_dec (l, to) (locw, f_to' w)) as [[A' B']|LL].
      { simpls; rewrite A' in *; rewrite B' in *.
        rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in PROM.
        destruct (is_rel lab w); simpls.
        inv PROM. exists w; splits; auto.
          by right. }
      rewrite (loc_ts_eq_dec_neq LL) in PROM.
      edestruct SIM_PROM as [b H]; eauto; desc.
      rewrite <- ISSEQ_TO in TO; auto.
      rewrite <- ISSEQ_FROM in FROM; auto.
      exists b; splits; auto.
      { by left. }
      cdes IMMCON.
      eapply sim_mem_helper_fS.
      6: by apply HELPER0.
      5: by apply ISSEQ_TO.
      all: auto. }
    { ins.
      rewrite IdentMap.gso in TID'; auto.
      destruct (loc_ts_eq_dec (loc, to) (locw, (f_to' w))) as [EQ|NEQ]; simpls.
      { desc. subst. right.
        destruct (Memory.get locw (f_to' w) (Local.Local.promises local')) eqn: HH; auto.
        exfalso.
        destruct p as [from msg].
        eapply PROM_IN_MEM in HH; eauto.
        erewrite Memory.add_get0 in HH; eauto.
        inv HH. }
      edestruct (PROM_DISJOINT thread') as [HH|HH]; eauto.
      left.
      destruct (Rel w); subst.
      erewrite Memory.remove_o; eauto.
      rewrite loc_ts_eq_dec_neq; auto.
      all: erewrite Memory.add_o; eauto.
      all: rewrite loc_ts_eq_dec_neq; auto. }
    { red; ins. 
      destruct ISSB as [ISSB|]; subst.
      { edestruct SIM_MEM as [rel]; eauto.
        simpls; desc.
        rewrite (ISSEQ_TO b); auto. rewrite (ISSEQ_FROM b); auto.
        exists rel; splits; auto.
        { erewrite Memory.add_o; eauto.
          destruct (loc_ts_eq_dec (l, f_to b) (locw, f_to' w)) as [[A' B']|LL].
          2: by rewrite (loc_ts_eq_dec_neq LL).
          simpls; rewrite A' in *; rewrite B' in *.
          exfalso.
          rewrite <- ISSEQ_TO in B'; auto.
          eapply f_to_eq in B'.
          4: by apply TCCOH'.
          all: eauto.
          { by desf. }
          { red. rewrite LOC. desf. }
            by left.
            by right. }
        { eapply sim_mem_helper_fS.
          4: by eauto.
          all: eauto. }
        { eapply closedness_preserved_add; eauto. }
        ins. simpls.
        destruct H1 as [MM [p_rel' RR]]; auto; desc.
        { intros HH. apply H0. by destruct (Rel w); [left|]. }
        split; auto.
        { destruct (Rel w); auto.
          { erewrite Memory.remove_o; eauto.
            destruct (loc_ts_eq_dec (l, f_to b) (locw, f_to' w)) as [[A B]|LL].
            { simpls; rewrite A in *; rewrite B in *.
              exfalso.
              rewrite <- ISSEQ_TO in B; auto.
              eapply f_to_eq in B.
              4: by apply TCCOH'.
              all: eauto.
              { desf. }
              { red. by rewrite LOC. }
                by left.
                by right. }
            rewrite (loc_ts_eq_dec_neq LL).
            erewrite Memory.add_o; eauto. by rewrite (loc_ts_eq_dec_neq LL). }
          subst.
          erewrite Memory.add_o; eauto.
          destruct (loc_ts_eq_dec (l, f_to b) (locw, f_to' w)) as [[A B]|LL].
          2: by rewrite (loc_ts_eq_dec_neq LL).
          simpls; rewrite A in *; rewrite B in *.
          exfalso.
          rewrite <- ISSEQ_TO in B; auto.
          eapply f_to_eq in B.
          4: by apply TCCOH'.
          all: eauto.
          { desf. }
          { red. by rewrite LOC. }
            by left.
            by right. }
        destruct RR0 as [[RR NN]|RR].
        2: { exists p_rel'; split; auto.
             { destruct (Rel w) eqn: WREL; simpls.
               unfold LocFun.add.
               destruct (Loc.eq_dec l locw); subst; auto.
               exfalso.
               destruct (same_thread G w b) as [[EQ|SB]|SB]; subst; auto.
               apply WNCOV. apply TCCOH in ISSB. eapply ISSB.
               2: apply H0; left; apply WISSUABLE.
               all: eexists; apply seq_eqv_r; split; auto.
               all: red; left; left.
               { right. apply seq_eqv_l; split; [by split|].
                 apply seq_eqv_r; split; [split; auto|by apply ISSB].
                 red. by rewrite LOC. }
               left. apply seq_eqv_r. split; [|split]; auto. }
             right. desc. exists p; splits; auto.
             { by left. }
             eexists; splits; eauto.
             rewrite ISSEQ_TO; auto. rewrite ISSEQ_FROM; auto.
             erewrite Memory.add_o; eauto.
             destruct (loc_ts_eq_dec (l, f_to p) (locw, f_to' w)) as [[A B]|NEQ]; simpls. 
             2: by rewrite (loc_ts_eq_dec_neq NEQ).
             exfalso. rewrite <- ISSEQ_TO in B; auto.
             eapply f_to_eq in B.
             4: by apply TCCOH'.
             all: eauto.
             { desf. }
             { red; desc. etransitivity.
               { eapply wf_rfrmwl; eauto. }
                 by rewrite LOC; subst. }
               by left. by right. }
        destruct (classic ((rf ⨾ rmw) w b)) as [RFRMW|].
        2: { exists p_rel'. split; auto.
             { destruct (Rel w) eqn: WREL; simpls.
               unfold LocFun.add.
               destruct (Loc.eq_dec l locw); subst; auto.
               exfalso.
               destruct (same_thread G w b) as [[EQ|SB]|SB]; subst; auto.
               apply WNCOV. apply TCCOH in ISSB. eapply ISSB.
               2: apply H0; left; apply WISSUABLE.
               all: eexists; apply seq_eqv_r; split; auto.
               all: red; left; left.
               { right. apply seq_eqv_l; split; [by split|].
                 apply seq_eqv_r; split; [split; auto|by apply ISSB].
                 red. by rewrite LOC. }
               left. apply seq_eqv_r. split; [|split]; auto. }
             left.
             splits; auto. intros [y UU]; apply RR.
             exists y. apply seq_eqv_l in UU; destruct UU as [[UU1|UU1] UU2]; [|by desf].
               by apply seq_eqv_l; split. }
        assert (Some l = Some locw) as LL.
        { rewrite <- LOC, <- LOC0. by apply wf_rfrmwl in RFRMW. }
        inv LL; clear LL.
        eexists; split.
        2: { intros. right.
             exists w; splits; auto. 
             { by right. }
             eexists; splits; eauto.
             erewrite Memory.add_o; eauto.
             rewrite (loc_ts_eq_dec_eq locw (f_to' w)).
             eauto. }
        simpls.
        rewrite <- ISSEQ_TO; auto. rewrite NN.
        assert ((rfi ⨾ rmw) w b) as RFIRMW.
        { hahn_rewrite rfi_union_rfe in RFRMW. apply seq_union_l in RFRMW.
          destruct RFRMW as [|RFRMW]; auto. exfalso.
          apply WNISS; apply TCCOH in ISSB; destruct ISSB as [A1 A2].
          apply A1. generalize RFRMW. generalize (rmw_in_ppo WF).
          basic_solver 40. }
        assert ((sb ∩ same_loc lab) w b) as SBWB.
        { destruct RFIRMW as [z [RFI RMW]].
          eapply sb_same_loc_trans.
            by apply WF.(rfi_in_sbloc'); eauto.
            apply WF.(rmw_in_sb_loc); eauto. }
        assert (~ Rel w) as NREL.
        { intros REL. apply WNISS; apply TCCOH in ISSB; destruct ISSB as [[[A1 A2] A3] A4].
          eapply w_covered_issued; eauto. split; auto.
          apply A2. unfold fwbob. exists b.
          apply seq_eqv_r; split; auto. left; left; right.
          apply seq_eqv_l; split; [by split|].
          apply seq_eqv_r; split; auto.
          apply (dom_r WF.(wf_rfrmwD)) in RFRMW.
          apply seq_eqv_r in RFRMW. desf. }
        destruct (is_rel lab w); simpls.
        assert (p_rel = None); subst.
        { desf. exfalso. apply WNISS.
          apply TCCOH in ISSB; destruct ISSB as [A1 A2].
          assert (W_ex_acq w) as WEX.
          { apply ACQEX. destruct INRMW as [z [RF RFMW]].
            eexists; eauto. }
          apply A2.
          exists b; apply seq_eqv_r; split; auto.
          apply seq_eqv_l; split; auto.
          apply SBWB. }
        simpls.
        unfold View.unwrap. rewrite !view_join_bot_r.
        rewrite <- !View.join_assoc. rewrite view_join_id.
        rewrite !View.join_assoc.
        assert ((View.join (View.singleton_ur locw (f_to' w))
                           (View.singleton_ur locw (f_to' b))) =
                (View.singleton_ur locw (f_to' b))) as QQ.
        2: by rewrite QQ.
        assert (Time.join (f_to' w) (f_to' b) = f_to' b) as QQ.
        { apply time_join_le_r. apply Time.le_lteq; left.
          eapply f_to_co_mon; eauto.
          { eapply (rfrmw_in_im_co) in RFRMW; eauto. apply RFRMW. }
            by right. by left. }
        unfold View.singleton_ur, View.join, TimeMap.join, TimeMap.singleton,
        LocFun.add; apply View.ext; apply LocFun.ext; simpls.
        all: intros a; unfold LocFun.find; simpls; desf. }
      assert (l = locw); subst.
      { rewrite LOC in LOC0. inv LOC0. }
      assert (v = valw); subst.
      { rewrite VAL in VAL0. inv VAL0. }
      eexists; splits.
      { erewrite Memory.add_o; eauto.
        rewrite (loc_ts_eq_dec_eq locw (f_to' b)); eauto. }
      all: simpls.
      { cdes PLN_RLX_EQ.
        destruct (is_rel lab b); simpls.
        rewrite EQ_CUR.
        2: rewrite EQ_REL.
        all: rewrite REL_PLN_RLX; reflexivity. }
      ins. destruct (Rel b); simpls; subst.
      { by exfalso; apply H0; right. }
      splits; auto.
      { erewrite Memory.add_o; eauto.
        rewrite (loc_ts_eq_dec_eq locw (f_to' b)); eauto. }
      eexists; splits; eauto.
      desf.
      { left; split; auto.
        intros [z HH]. apply seq_eqv_l in HH. destruct HH as [[ISS|]RFRMW]; subst.
        { apply NINRMW. exists z. apply seq_eqv_l. by split. }
        eapply wf_rfrmw_irr in RFRMW; eauto. }
      right. eexists; splits; eauto.
      { by left. }
      eexists; splits; eauto.
      erewrite Memory.add_o; eauto.
      rewrite loc_ts_eq_dec_neq.
      { rewrite ISSEQ_TO; auto. by rewrite ISSEQ_FROM. }
      right. intros HH.
      eapply f_to_eq in HH.
      4: by apply TCCOH'.
      all: eauto.
      { by desf. }
      { red. by rewrite LOC0. }
        by left.
        by right. }
      { apply Memory.promise_add; eauto. }
      { constructor.
        assert ((fun x => View.pln x = View.rlx x)
                  (View.join (View.join (if Rel w
                                         then TView.cur (Local.Local.tview local)
                                         else TView.rel (Local.Local.tview local) locw)
                                        (View.unwrap p_rel))
                             (View.singleton_ur locw (f_to' w)))) as PLN_RLX.
        { unfold View.join; simpls.
          cdes PLN_RLX_EQ.
          destruct (Rel w); simpls.
          rewrite EQ_CUR.
          2: rewrite EQ_REL.
          all: by rewrite REL_PLN_RLX. }
        constructor; simpls. by rewrite PLN_RLX. }
      { destruct (Rel w) eqn: WREL; simpls.
        2: by eapply tview_closedness_preserved_add; eauto.
        unfold TView.write_tview.
        cdes MEM_CLOSE.
        red; splits; simpls.
        1,2: apply Memory.join_closed_timemap; auto.
        1,2: by eapply Memory.add_closed_timemap; eauto.
        intros loc. unfold LocFun.add.
        destruct (Loc.eq_dec loc locw) as [|NEQ]; subst.
        2: by eapply Memory.add_closed_timemap; eauto.
        destruct (Ordering.le Ordering.acqrel (wmod (mod lab w))).
        all: apply Memory.join_closed_timemap; auto.
        all: by eapply Memory.add_closed_timemap; eauto. }
      intros REL. red; ins. exfalso.
      destruct msg as [v rel].
      eapply SIM_PROM in GET; eauto. desc.
      destruct (same_thread G w b) as [[EQ|SB]|SB]; subst; auto.
      apply WNCOV. apply TCCOH in ISS. apply ISS.
      2: apply NCOV; apply WISSUABLE.
      all: eexists; apply seq_eqv_r; split; eauto.
      { red. left; left; right. apply seq_eqv_l; split; [by split|].
        apply seq_eqv_r; split; [split; auto|by apply ISS].
        by red; rewrite LOC. }
      red. repeat left. by  apply seq_eqv_r; split; [|split]. }
  red in H; desc. simpls. right.
  assert (tid w = tid ws) as TWWS.
  { destruct (sb_tid_init SBWW); desf. }
  splits; auto.

  assert (Memory.closed_timemap
            (TimeMap.join
               (TimeMap.join
                  (View.rlx (TView.rel (Local.Local.tview local) locw))
                  (View.rlx (View.unwrap p_rel))) (TimeMap.singleton locw (f_to' w)))
            memory') as YY.
  { apply Memory.join_closed_timemap.
    { eapply closedness_preserved_split; eauto.
      apply Memory.join_closed_timemap; auto.
      apply MEM_CLOSE. }
    eapply Memory.singleton_closed_timemap.
    2: by eapply Memory.split_inhabited; eauto.
    erewrite Memory.split_o; eauto.
      by rewrite loc_ts_eq_dec_eq. }

  exists ws; exists valws; eexists; eexists; exists f_to'; exists f_from'.
  exists promises'; exists memory'.
  splits; eauto.
  { etransitivity; eauto.
    apply clos_rt1n_step.
      econstructor.
      { apply Memory.op_split. eauto. }
      { constructor. constructor; simpls.
        rewrite REL_PLN_RLX.
        cdes PLN_RLX_EQ.
          by rewrite EQ_REL. }
      eauto. }
  { ins.
    destruct (Ident.eq_dec (tid e) (tid w)) as [EQ|NEQ].
    { rewrite EQ. rewrite IdentMap.gss.
      eexists. eauto. }
    rewrite IdentMap.gso; auto. }
  { ins.
    destruct (Ident.eq_dec thread' (tid w)) as [EQ|NEQ].
    { subst. rewrite IdentMap.gss in TID0.
      inv TID0; simpls; clear TID0.
      red; ins.
      erewrite Memory.split_o; eauto.
      erewrite Memory.split_o in LHS; [|by apply PADD].
      destruct (loc_ts_eq_dec (loc, to) (locw, f_to' w)) as [[A B]|LL].
      { simpls; rewrite A in *; rewrite B in *.
        rewrite (loc_ts_eq_dec_eq locw (f_to' w)).
          by rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in LHS. }
      rewrite (loc_ts_eq_dec_neq LL).
      destruct (loc_ts_eq_dec (loc, to) (locw, f_to' ws)) as [[A B]|LL'].
      { simpls; rewrite A in *; rewrite B in *.
        rewrite (loc_ts_eq_dec_eq locw (f_to' ws)).
        rewrite (loc_ts_eq_dec_neq LL) in LHS.
          by rewrite (loc_ts_eq_dec_eq locw (f_to' ws)) in LHS. }
      rewrite (loc_ts_eq_dec_neq LL').
      rewrite (loc_ts_eq_dec_neq LL) in LHS.
      rewrite (loc_ts_eq_dec_neq LL') in LHS.
      eapply PROM_IN_MEM; eauto. }
    red; ins; rewrite IdentMap.gso in TID0; auto.
    assert (loc <> locw \/ to <> f_to' ws) as LL'.
    { destruct (classic (loc = locw)); [subst|by left].
      right. 
      destruct (classic (to = f_to' ws)); [subst|done].
      exfalso.
      rewrite ISSEQ_TO in LHS; auto.
      edestruct PROM_DISJOINT as [H|H].
      { intros H. apply NEQ. by rewrite H. }
      { eauto. }
      { rewrite H in WSPROM. inv WSPROM. }
      rewrite H in LHS. inv LHS. }
    eapply PROM_IN_MEM in LHS; eauto.
    erewrite Memory.split_o; eauto.
    destruct (loc_ts_eq_dec (loc, to) (locw, f_to' w)) as [[A B]|LL].
    { simpls; rewrite A in *; rewrite B in *.
      exfalso.
      edestruct Memory.split_get0 as [H _]; eauto.
      rewrite H in LHS. inv LHS. }
    rewrite (loc_ts_eq_dec_neq LL).
      by rewrite (loc_ts_eq_dec_neq LL'). }
  { eapply closedness_preserved_split; eauto. }
  { simpls. red. ins.
    erewrite Memory.split_o in PROM; eauto.
    destruct (loc_ts_eq_dec (l, to) (locw, f_to' w)) as [[A B]|LL].
    { simpls; rewrite A in *; rewrite B in *.
      rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in PROM.
      inv PROM.
      exists w; splits; auto.
        by right. }
    rewrite (loc_ts_eq_dec_neq LL) in PROM.
    destruct (loc_ts_eq_dec (l, to) (locw, f_to' ws)) as [[A B]|LL'].
    { simpls; rewrite A in *; rewrite B in *.
      rewrite (loc_ts_eq_dec_eq locw (f_to' ws)) in PROM.
      inv PROM.
      exists ws; splits; auto.
      { by apply TCCOH. }
      { by left. }
      red; splits; auto.
      { left. by eapply f_to_co_mon; eauto; [right|left]. }
      edestruct SIM_PROM as [b H]; eauto; desc.
      red in HELPER0; desc.
      destruct (classic (b = ws)) as [|NEQ]; subst. 
      { eapply (@sim_msg_fS f_to (upd f_to w (f_to' w)) _ _ _ TCCOH) in SIMMSG;
          eauto.
        { eapply sim_msg_fS.
          { apply TCCOH'. }
          5: by apply SIMMSG.
          all: eauto.
          { simpls. rewrite set_inter_union_r.
            apply set_subset_union_l; split; auto.
            generalize NREL. basic_solver. }
          { by left. }
          intros e [H|]; subst; [rewrite updo|by rewrite upds].
          { by apply ISSEQ_TO. }
            by intros HH; subst. }
        ins; rewrite updo; [done|].
          by intros HH; subst. }
      exfalso.
      rewrite <- ISSEQ_TO in TO; auto.
      (* TODO: generalize to a lemma! *)
      edestruct WF.(wf_co_total) as [CO|CO].
      3: by apply NEQ.
      1,2: split; [split|]; auto.
      1-3: by apply TCCOH.
      { by rewrite LOC0. }
      all: eapply (f_to_co_mon WF IMMCON FCOH0) in CO; [|by left|by left].
      all: rewrite TO in CO.
      all: rewrite ISSEQ_TO in CO; auto.
      all: by apply Time.lt_strorder in CO. }
    rewrite (loc_ts_eq_dec_neq LL') in PROM.
    eapply SIM_PROM in PROM; eauto.
    destruct PROM as [b H]; desc.
    exists b; splits; auto.
    { by left. }
    { rewrite <- ISSEQ_FROM in FROM; auto.
      split; auto.
      intros H; subst. simpls. desf.
      all: by apply LL'; rewrite ISSEQ_TO. }
    { rewrite <- ISSEQ_TO in TO; auto. }
    eapply sim_mem_helper_fS.
    6: by apply HELPER0.
    5: by apply ISSEQ_TO.
    all: auto. }
  { apply RESERVED_TIME0. }
  { apply RESERVED_TIME0. }
  { ins.
    rewrite IdentMap.gso in TID'; auto.
    destruct (loc_ts_eq_dec (loc, to) (locw, (f_to' w))) as [EQ|NEQ]; simpls.
    { desc. subst. right.
      destruct (Memory.get locw (f_to' w) (Local.Local.promises local')) eqn: HH; auto.
      exfalso.
      destruct p as [from msg].
      eapply PROM_IN_MEM in HH; eauto.
      edestruct Memory.split_get0 as [Y1 Y2].
      { apply MADD. }
      red in Y1. rewrite Y1 in HH.
      inv HH. }
    edestruct (PROM_DISJOINT thread') as [HH|HH]; eauto.
    left.
    erewrite Memory.split_o; eauto.
    rewrite loc_ts_eq_dec_neq; auto.
    destruct (loc_ts_eq_dec (loc, to) (locw, (f_to' ws))) as [EQ|NEQ2]; simpls.
    2: by rewrite (loc_ts_eq_dec_neq NEQ2).
    desc. subst.
    exfalso.
    edestruct Memory.split_get0 as [Y1 Y2].
    { apply PADD. }
    red in Y2. rewrite Y2 in HH.
    inv HH. }
  red; ins.
  destruct ISSB as [ISSB|]; subst.
  { edestruct SIM_MEM as [rel HY]; eauto; simpls.
    desc.
    rewrite (ISSEQ_TO b); auto.
    exists rel; splits; auto. 
    { erewrite Memory.split_o; eauto.
      (* TODO: generalize! *)
      destruct (loc_ts_eq_dec (l, f_to b) (locw, f_to' w)) as [[A B]|LL].
      { simpls; rewrite A in *; rewrite B in *.
        exfalso.
        rewrite <- ISSEQ_TO in B; auto.
        eapply f_to_eq in B.
        4: by apply TCCOH'.
        all: eauto.
        { desf. }
        { red. by rewrite LOC. }
          by left.
          by right. }
      rewrite (loc_ts_eq_dec_neq LL).
      destruct (loc_ts_eq_dec (l, f_to b) (locw, f_to' ws)) as [[A B]|LL'].
      { simpls; rewrite A in *; rewrite B in *.
        rewrite (loc_ts_eq_dec_eq locw (f_to' ws)).
        rewrite FEQ1.
        destruct (classic (b = ws)) as [|NEQ]; subst.
        { edestruct Memory.split_get0 as [_ H].
          { apply MADD. }
          rewrite H in INMEM.
          inv INMEM. }
        exfalso.
        rewrite ISSEQ_TO in B.
        edestruct WF.(wf_co_total) as [CO|CO].
        3: by apply NEQ.
        1,2: split; [split|]; auto.
        1-3: by apply TCCOH.
        { by rewrite LOC0. }
        3: done.
        1,2: eapply (f_to_co_mon WF IMMCON FCOH) in CO; auto.
        1,2: rewrite B in CO.
        1,2: by apply Time.lt_strorder in CO. }
      rewrite (loc_ts_eq_dec_neq LL').
      rewrite ISSEQ_FROM; [done|].
      split; auto.
      intros H; desf; simpls.
      all: apply LL'.
      all: by rewrite ISSEQ_TO. }
    { eapply sim_mem_helper_fS.
      5: by apply ISSEQ_TO.
      all: auto.
      red; splits; auto.
      { destruct (classic (is_init b)) as [BB|BB]; [right|left].
        { splits; auto.
          2: { apply FCOH. by split. }
          rewrite ISSEQ_FROM.
          { apply FCOH. by split. }
          split; auto. intros H; subst.
          apply WSNCOV. apply TCCOH. by split. }
        rewrite <- ISSEQ_TO; auto.
        apply FCOH0; auto. by left. }
      apply HELPER0. }
    { eapply closedness_preserved_split; eauto. }
    ins. simpls.
    destruct HY1 as [MM RR]; auto; unnw; subst.
    split.
    { erewrite Memory.split_o; eauto.
      destruct (loc_ts_eq_dec (l, f_to b) (locw, f_to' w)) as [[A B]|LL].
      { simpls; rewrite A in *; rewrite B in *.
        exfalso.
        rewrite <- ISSEQ_TO in B; auto.
        eapply f_to_eq in B.
        4: apply TCCOH'.
        all: eauto.
        { desf. }
        { red. by rewrite LOC0. }
          by left.
          by right. }
      rewrite (loc_ts_eq_dec_neq LL).
      destruct (loc_ts_eq_dec (l, f_to b) (locw, f_to' ws)) as [[A B]|LL'].
      { simpls; rewrite A in *; rewrite B in *.
        rewrite (loc_ts_eq_dec_eq locw (f_to' ws)).
        rewrite FEQ1.
        destruct (classic (b = ws)) as [|NEQ]; subst.
        { edestruct Memory.split_get0 as [_ HH].
          { apply MADD. }
          rewrite HH in INMEM.
          inv INMEM. }
        exfalso.
        rewrite ISSEQ_TO in B.
        edestruct WF.(wf_co_total) as [CO|CO].
        3: by apply NEQ.
        1,2: split; [split|]; auto.
        1-3: by apply TCCOH.
        { by rewrite LOC0. }
        1,2: eapply (f_to_co_mon WF IMMCON FCOH) in CO; auto.
        1,2: rewrite B in CO.
        1,2: by apply Time.lt_strorder in CO.
        done. }
      rewrite (loc_ts_eq_dec_neq LL').
      rewrite ISSEQ_FROM; [done|].
      split; auto.
      intros HH; subst; simpls.
      destruct LL' as [LL'|LL'].
      2: by apply LL'; rewrite ISSEQ_TO.
      rewrite SAME_LOC in LOC0. inv LOC0. }
    destruct RR as [p_rel' [FF [[RR NN]|RR]]].
    2: { exists p_rel'; split; auto.
         right. desc. exists p; splits; auto.
         { by left. }
         eexists; splits; eauto.
         erewrite Memory.split_o; eauto.
         destruct (loc_ts_eq_dec (l, f_to' p) (locw, f_to' w)) as [[A B]|NEQ]; simpls. 
         2: { rewrite (loc_ts_eq_dec_neq NEQ).
              destruct (loc_ts_eq_dec (l, f_to' p) (locw, f_to' ws)) as [[A B]|NEQ'];
                simpls. 
              2: { intros. rewrite (loc_ts_eq_dec_neq NEQ').
                   rewrite ISSEQ_TO; auto.
                   rewrite ISSEQ_FROM; auto.
                   split; auto. intros HH; subst.
                   destruct NEQ' as [NN|NN]; [|by desf].
                   apply WF.(wf_rfrmwl) in RR0. red in RR0.
                   rewrite LOC0 in RR0. rewrite SAME_LOC in RR0.
                   inv RR0. }
              rewrite A in *; rewrite B in *.
              rewrite (loc_ts_eq_dec_eq locw (f_to' ws)).
              assert (p = ws); subst.
              { eapply f_to_eq.
                3: by apply TCCOH'.
                all: eauto.
                { apply WF.(wf_rfrmwl) in RR0.
                  red. rewrite SAME_LOC. by rewrite RR0. }
                all: by left. }
              rewrite FEQ1. rewrite WSVAL in RR1. inv RR1. }
         rewrite A in *; rewrite B in *.
         rewrite (loc_ts_eq_dec_eq locw (f_to' w)).
         assert (p = w); subst.
         { eapply f_to_eq.
           3: by apply TCCOH'.
           all: eauto.
           { apply WF.(wf_rfrmwl) in RR0.
             red. rewrite LOC. by rewrite RR0. }
             by left. by right. }
         rewrite VAL in RR1. inv RR1. }
    destruct (classic ((rf ⨾ rmw) w b)) as [RFRMW|].
    2: { exists p_rel'. split; auto. left.
         splits; auto. intros [y UU]; apply RR.
         exists y. apply seq_eqv_l in UU; destruct UU as [[UU1|UU1] UU2]; [|by desf].
           by apply seq_eqv_l; split. }
    assert (Some l = Some locw) as LL.
    { rewrite <- LOC, <- LOC0. by apply wf_rfrmwl in RFRMW. }
    inv LL; clear LL.
    eexists; split.
    2: { intros. right.
         exists w; splits; auto. 
         { by right. }
         eexists; splits; eauto.
         erewrite Memory.split_o; eauto.
         rewrite (loc_ts_eq_dec_eq locw (f_to' w)).
         eauto. }
    simpls.
    assert (p_rel = None); subst.
    2: { simpls.
         unfold View.unwrap. rewrite !view_join_bot_r.
         rewrite <- !View.join_assoc. rewrite view_join_id.
         rewrite !View.join_assoc.
         assert ((View.join (View.singleton_ur locw (f_to' w))
                            (View.singleton_ur locw (f_to b))) =
                 (View.singleton_ur locw (f_to b))) as QQ; [|by rewrite QQ].
         rewrite <- ISSEQ_TO; auto. 
         assert (Time.join (f_to' w) (f_to' b) = f_to' b) as QQ.
         { apply time_join_le_r. apply Time.le_lteq; left.
           eapply f_to_co_mon; eauto.
           { eapply rfrmw_in_im_co in RFRMW; eauto. apply RFRMW. }
             by right. by left. }
         unfold View.singleton_ur, View.join, TimeMap.join, TimeMap.singleton,
         LocFun.add; apply View.ext; apply LocFun.ext; simpls.
         all: intros a; unfold LocFun.find; simpls; desf. }
    desf.
    hahn_rewrite rfi_union_rfe in RFRMW. apply seq_union_l in RFRMW.
    destruct RFRMW as [RFRMW|RFRMW]; exfalso.
    all: apply WNISS; apply TCCOH in ISSB; destruct ISSB as [A1 A2]. 
    2: { apply A1. generalize RFRMW. generalize (rmw_in_ppo WF).
         basic_solver 40. }
    apply A2.
    assert (W_ex_acq w) as WEX.
    { apply ACQEX. destruct P_REL_CH1 as [z [RF RFMW]].
      eexists; eauto. }
    exists b; apply seq_eqv_r; split; auto.
    apply seq_eqv_l; split; auto.
    destruct RFRMW as [z [RF RMW]].
    eapply sb_trans. by apply WF.(rfi_in_sbloc'); eauto.
      by apply WF.(wf_rmwi). }
  assert (l = locw); subst.
  { rewrite LOC in LOC0; inv LOC0. }
  assert (v = valw); subst.
  { rewrite VAL in VAL0; inv VAL0. }
  eexists; splits.
  { erewrite Memory.split_o; eauto.
    rewrite (loc_ts_eq_dec_eq locw (f_to' b)); eauto. }
  all: simpls.
  { cdes PLN_RLX_EQ. rewrite EQ_REL. rewrite REL_PLN_RLX. reflexivity. }
  { ins; splits; auto.
    { erewrite Memory.split_o; eauto.
      rewrite (loc_ts_eq_dec_eq locw (f_to' b)); eauto. }
    eexists; split; eauto.
    desf.
    { left; split; auto.
      intros [z HH]. apply seq_eqv_l in HH. destruct HH as [[ISS|]RFRMW]; subst.
      { apply NINRMW. exists z. apply seq_eqv_l. by split. }
      eapply wf_rfrmw_irr in RFRMW; eauto. }
    right. eexists; splits; eauto.
    { by left. }
    eexists; splits; eauto.
    erewrite Memory.split_o; eauto.
    assert (p <> b) as PNEQ.
    { intros HH; subst. eapply wf_rfrmw_irr in INRMW; eauto. }
    assert (p <> ws) as PWNEQ.
    { intros HH; subst.
      cdes IMMCON. eapply Cint.
      exists ws; split.
      { apply sb_in_hb; eauto. }
      edestruct INRMW as [z [RF RMW]].
      apply r_step.
      eapply WF.(eco_trans).
      { apply G.(rf_in_eco); eauto. }
      apply fr_in_eco; auto. apply rmw_in_fr; auto.
        by apply coherence_sc_per_loc. }
    rewrite loc_ts_eq_dec_neq.
    { rewrite loc_ts_eq_dec_neq.
      { rewrite ISSEQ_TO; auto. rewrite ISSEQ_FROM; auto. split; auto. }
      right. intros HH.
      apply PWNEQ. eapply f_to_eq.
      3: by eauto.
      all: eauto.
      { red. by rewrite SAME_LOC. }
      all: by left. }
    right. intros HH.
    apply PNEQ. eapply f_to_eq.
    3: by apply TCCOH'.
    all: eauto.
    { red. by rewrite LOC0. }
      by left.
      by right. }
  { apply Memory.promise_split; eauto. }
  constructor.
  assert ((fun x => View.pln x = View.rlx x)
            (View.join (View.join (TView.rel (Local.Local.tview local) locw)
                                  (View.unwrap p_rel))
                       (View.singleton_ur locw (f_to' w)))) as PLN_RLX.
  { unfold View.join; simpls.
    cdes PLN_RLX_EQ. rewrite EQ_REL. by rewrite REL_PLN_RLX. }
  constructor; simpls. by rewrite PLN_RLX.
Qed.

End WritePromiseStepHelper.
