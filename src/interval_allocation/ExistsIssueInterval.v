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
From hahnExt Require Import HahnExt.
From imm Require Import FairExecution.
From imm Require Import SimClosure.

From hahnExt Require Import HahnExt.
From hahnExt Require Import HahnExt.
Require Import SimulationRel.
Require Import SimState.
Require Import MemoryAux.
Require Import MaxValue.
Require Import ViewRel.
Require Import Event_imm_promise.
Require Import ExtTraversalConfig.
Require Import ExtTraversal.
Require Import ExtTraversalProperties.
Require Import FtoCoherent.
Require Import SimulationRelProperties.
Require Import IntervalHelper.
From imm Require Import TraversalOrder.
From imm Require Import TLSCoherency.
From imm Require Import IordCoherency.
From imm Require Import TlsEventSets.
From imm Require Import EventsTraversalOrder.

Set Implicit Arguments.

Section Aux.

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

Hypothesis IMMCON : imm_consistent G sc.

Variable T : trav_label -> Prop. 
Hypothesis TCOH : tls_coherent G T.
Hypothesis ICOH : iord_coherent G sc T.
Hypothesis RCOH : reserve_coherent G T.

Notation "'C'" := (covered T). 
Notation "'I'" := (issued T). 
Notation "'S'" := (reserved T). 

Hypothesis RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T.

Variable f_to f_from : actid -> Time.t.
Hypothesis FCOH : f_to_coherent G S f_to f_from.

Variable thread : thread_id.
Variable PC : Configuration.t.
Variable local : Local.t.

Hypothesis SIM_TVIEW : sim_tview G sc (covered T) f_to (Local.tview local) thread.
Hypothesis INHAB : Memory.inhabited (Configuration.memory PC).
Hypothesis PLN_RLX_EQ : pln_rlx_eq (Local.tview local).
Hypothesis MEM_CLOSE : memory_close (Local.tview local) (Configuration.memory PC).

Lemma exists_time_interval_for_issue_no_next w locw valw langst smode
      (FAIR: mem_fair G)
      (ISSUABLE : issuable G sc T w)
      (WNISS : ~ issued T w)
      (NWEX : ~ W_ex w)
      (NONEXT : dom_sb_S_rfrmw G T rfi (eq w) ⊆₁ ∅)
      (LOC : loc lab w = Some locw)
      (VAL : val lab w = Some valw)
      (WTID : thread = tid w)
      (PROM_IN_MEM :
         forall thread' langst local
                (TID : IdentMap.find thread' (Configuration.threads PC) =
                       Some (langst, local)),
           Memory.le (Local.promises local) (Configuration.memory PC))
      (RESERVED_TIME:
         reserved_time G T f_to f_from smode (Configuration.memory PC))
      (SIM_RES_MEM :
         sim_res_mem G T f_to f_from (tid w) local (Configuration.memory PC))
      (SIM_MEM : sim_mem G sc T f_to f_from
                         (tid w) local (Configuration.memory PC))
      (TID : IdentMap.find (tid w) (Configuration.threads PC) = Some (langst, local)) :
  let promises := (Local.promises local) in
  let memory   := (Configuration.memory PC) in
  (* let T'       := mkTC (covered T) (issued T ∪₁ eq w) in *)
  (* let S'       := S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G (mkETC T S) rfi (eq w) in *)
  let T' := T ∪₁ eq (mkTL ta_issue w) ∪₁ (eq ta_reserve <*> (eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w))) in
  exists p_rel,
    rfrmw_prev_rel G sc T f_to f_from (Configuration.memory PC) w locw p_rel /\
    ⟪ SEW' : reserved T' ⊆₁ E ∩₁ W ⟫ /\
    (⟪ FOR_ISSUE :
         exists f_to' f_from',
           let rel'' :=
               if is_rel lab w
               then (TView.cur (Local.tview local))
               else (TView.rel (Local.tview local) locw)
           in
           let rel' := (View.join (View.join rel'' (View.unwrap p_rel))
                                  (View.singleton_ur locw (f_to' w))) in
           ⟪ RELWFEQ : View.pln rel' = View.rlx rel' ⟫ /\
           ⟪ REL_VIEW_LT : Time.lt (View.rlx rel'' locw) (f_to' w) ⟫ /\
           ⟪ REL_VIEW_LE : Time.le (View.rlx rel'  locw) (f_to' w) ⟫ /\

           ⟪ REQ_TO : forall e (SE : S e) (NEQ : e <> w), f_to' e = f_to e ⟫ /\
           ⟪ REQ_FROM : forall e (SE : S e) (NEQ : e <> w), f_from' e = f_from e ⟫ /\
           ⟪ ISSEQ_TO   : forall e (ISS: issued T e), f_to' e = f_to e ⟫ /\
           ⟪ ISSEQ_FROM : forall e (ISS: issued T e), f_from' e = f_from e ⟫ /\
           ⟪ FTOWNBOT : f_to' w <> Time.bot ⟫ /\

           ⟪ DISJOINT : forall to from msg
               (INMEM : Memory.get locw to (Configuration.memory PC) = Some (from, msg)),
               Interval.disjoint (f_from' w, f_to' w) (from, to) ⟫ /\

           exists promises' memory',
             ⟪ PADD :
                 Memory.add (Local.promises local) locw (f_from' w) (f_to' w)
                            (Message.full valw (Some rel')) promises' ⟫ /\
             ⟪ MADD :
                 Memory.add memory locw (f_from' w) (f_to' w)
                            (Message.full valw (Some rel')) memory' ⟫ /\

             ⟪ MEMPROM :
               Memory.promise (Local.promises local) (Configuration.memory PC) locw 
                              (f_from' w) (f_to' w) (Message.full valw (Some rel'))
                              promises' memory' Memory.op_kind_add ⟫ /\

             ⟪ INHAB : Memory.inhabited memory' ⟫ /\
             ⟪ RELMCLOS : Memory.closed_timemap (View.rlx rel') memory' ⟫ /\
             ⟪ RELVCLOS : Memory.closed_view rel' memory' ⟫ /\

             ⟪ FCOH : f_to_coherent G (reserved T') f_to' f_from' ⟫ /\

             ⟪ HELPER :
                 sim_mem_helper
                   G sc f_to' w (f_from' w) valw
                   (View.join (View.join (if is_rel lab w
                                          then (TView.cur (Local.tview local))
                                          else (TView.rel (Local.tview local) locw))
                                         (View.unwrap p_rel))
                              (View.singleton_ur locw (f_to' w))) ⟫ /\

             ⟪ RESERVED_TIME :
                 reserved_time G T' f_to' f_from' smode memory' ⟫ ⟫ \/
     ⟪ FOR_SPLIT :
         ⟪ SMODE : smode = sim_certification ⟫ /\
         exists ws wsv wsrel f_to' f_from',
           let wsmsg := Message.full wsv wsrel in
           let rel'' :=
               if is_rel lab w
               then (TView.cur (Local.tview local))
               else (TView.rel (Local.tview local) locw)
           in
           let rel' := (View.join (View.join rel'' (View.unwrap p_rel))
                                  (View.singleton_ur locw (f_to' w))) in
           ⟪ NREL    : ~ Rel w ⟫ /\
           ⟪ EWS     : E ws ⟫ /\
           ⟪ WSS     : S ws ⟫ /\
           ⟪ WSISS  : issued T ws ⟫ /\
           ⟪ NWEXWS : ~ W_ex ws ⟫ /\
           ⟪ WSNCOV  : ~ covered T ws ⟫ /\
           ⟪ WSNINIT : ~ is_init ws ⟫ /\
           ⟪ WSTID   : tid ws = tid w ⟫ /\
           ⟪ WSVAL   : val lab ws = Some wsv ⟫ /\
           ⟪ WSSMSG : sim_msg G sc f_to ws (View.unwrap wsrel) ⟫ /\ 

           ⟪ SBWW : sb w ws ⟫ /\
           ⟪ SAME_LOC : Loc_ locw ws ⟫ /\
           ⟪ COWW : co w ws ⟫ /\

           ⟪ FEQ1 : f_to' w = f_from' ws ⟫ /\
           ⟪ FEQ2 : f_from' w = f_from ws ⟫ /\

           ⟪ WSPROM : Memory.get locw (f_to ws) (Local.promises local) =
                      Some (f_from ws, wsmsg)⟫ /\
           ⟪ WSMEM : Memory.get locw (f_to ws) memory =
                     Some (f_from ws, wsmsg)⟫ /\
           

           ⟪ RELWFEQ : View.pln rel' = View.rlx rel' ⟫ /\
           ⟪ REL_VIEW_LT : Time.lt (View.rlx rel'' locw) (f_to' w) ⟫ /\
           ⟪ REL_VIEW_LE : Time.le (View.rlx rel'  locw) (f_to' w) ⟫ /\

           ⟪ REQ_TO     : forall e (SE : S e) (NEQ : e <> w), f_to' e = f_to e ⟫ /\
           ⟪ REQ_FROM   : forall e (SE : S e) (NEQ : e <> ws), f_from' e = f_from e ⟫ /\
           ⟪ ISSEQ_TO   : forall e (ISS: issued T e), f_to' e = f_to e ⟫ /\
           ⟪ ISSEQ_FROM : forall e (ISS: issued T e) (NEQ : e <> ws), f_from' e = f_from e ⟫ /\
           ⟪ FTOWNBOT : f_to' w <> Time.bot ⟫ /\

           ⟪ FCOH : f_to_coherent G (reserved T') f_to' f_from' ⟫ /\

           ⟪ NINTER :
             forall thread' langst' local' (TNEQ : tid w <> thread')
                    (TID' : IdentMap.find thread' (Configuration.threads PC) =
                            Some (langst', local')),
               Memory.get locw (f_to' w) (Local.promises local') = None ⟫ /\

           exists promises' memory',
             ⟪ PADD :
                 Memory.split (Local.promises local)
                              locw (f_from' w) (f_to' w) (f_to' ws)
                              (Message.full valw (Some rel'))
                              wsmsg
                              promises' ⟫ /\
             ⟪ MADD :
                 Memory.split memory locw (f_from' w) (f_to' w) (f_to' ws)
                              (Message.full valw (Some rel'))
                              wsmsg
                              memory' ⟫ /\

             ⟪ MEMPROM :
               Memory.promise (Local.promises local) (Configuration.memory PC) locw 
                              (f_from' w) (f_to' w) (Message.full valw (Some rel'))
                              promises' memory'
                              (Memory.op_kind_split (f_to' ws) wsmsg) ⟫ /\


             ⟪ INHAB : Memory.inhabited memory' ⟫ /\
             ⟪ RELMCLOS : Memory.closed_timemap (View.rlx rel') memory' ⟫ /\
             ⟪ RELVCLOS : Memory.closed_view rel' memory' ⟫ /\


             ⟪ HELPER :
                 sim_mem_helper
                   G sc f_to' w (f_from' w) valw
                   (View.join (View.join (if is_rel lab w
                                          then (TView.cur (Local.tview local))
                                          else (TView.rel (Local.tview local) locw))
                                         (View.unwrap p_rel))
                              (View.singleton_ur locw (f_to' w))) ⟫ /\

             ⟪ RESERVED_TIME :
                 reserved_time G T' f_to' f_from' smode memory' ⟫ ⟫).
Proof using WF IMMCON RELCOV FCOH SIM_TVIEW PLN_RLX_EQ INHAB MEM_CLOSE TCOH RCOH ICOH.
  assert (sc_per_loc G) as SPL.
  { apply coherence_sc_per_loc. apply IMMCON. }
  assert (S ⊆₁ E ∩₁ W) as SEW.
  { apply set_subset_inter_r. split; [by apply RCOH|].
    eapply reservedW; eauto. }
  assert (issued T ⊆₁ S) as IE by apply RCOH. 
  assert (W w) as WW.
  { eapply issuableW; eauto. }
  assert (E w) as EW.
  { eapply issuableE; eauto. }
  assert (~ covered T w) as WNCOV.
  { intros HH. apply WNISS. eapply w_covered_issued; vauto. }
  assert (~ S w) as NSW.
  { intros HH. apply NWEX. eapply rcoh_S_I_in_W_ex; eauto. by split. }
  assert (~ is_init w) as WNINIT.
  { intros HH. apply WNCOV. eapply init_covered; eauto. by split. }

  set (S':= S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G T rfi (eq w)).
  assert (SEW' : S' ⊆₁ E ∩₁ W).
  { unfold S'. rewrite NONEXT.
    rewrite SEW. unionL; basic_solver. }

  (* TODO: introduce a lemma *)
  assert (forall x (SX : S x), Time.le (f_from x) (f_to x)) as LEFT.
  { ins. assert (EX : E x) by (by apply SEW).
    destruct (classic (is_init x)) as [HH|HH].
    { arewrite (f_to x = tid_init).
      { by apply FCOH; split. }
      arewrite (f_from x = tid_init).
      { by apply FCOH; split. }
      reflexivity. }
    apply Time.le_lteq. left. by apply FCOH. }

  assert ((E ∩₁ W ∩₁ Loc_ locw) w) as WEW.
  { split; [split|]; auto. }

  destruct langst as [lang state].

  edestruct exists_wprev_rel with (w:=w) as [p_rel PRELSPEC]; eauto.
  set (rel'' :=
         if Rel w
         then TView.cur (Local.tview local)
         else TView.rel (Local.tview local) locw).
  exists p_rel. split; auto.

  assert (p_rel = None) as PRELNN.
  { desc.
    red in PRELSPEC. desc.
    destruct PRELSPEC0; desc; auto.
    exfalso.
    generalize INRMW NWEX. clear. unfold Execution.W_ex. basic_solver. }
  assert (Message.wf (Message.full valw p_rel)) as WFMSG.
  { subst. constructor. apply View.opt_wf_none. }

  assert (View.pln rel'' = View.rlx rel'') as RELPLN''.
  { subst rel''. destruct (Rel w); apply PLN_RLX_EQ. }

  edestruct co_prev_to_imm_co_prev with (w:=w) as [wprev]; eauto. desc.
  split; auto.
  { red. simplify_tls_events. rewrite <- set_unionA, <- SEW'. basic_solver. }

  destruct (classic (exists wconext, (co ⨾ ⦗ S ⦘) w wconext)) as [WCONEXT|WNONEXT]; [|left].
  { edestruct co_next_to_imm_co_next with (w:=w) as [wconext]; eauto. clear WCONEXT. desc.
    assert ((co ⨾ ⦗set_compl S⦘ ⨾ co) wprev wconext) as CONS.
    { exists w. split; auto. apply seq_eqv_l. by split. }
    assert (co wprev wconext) as COPN.
    { eapply (co_trans WF); eauto. }

    assert (immediate (⦗S⦘ ⨾ co ⨾ ⦗S⦘) wprev wconext) as COSIMM.
    { apply P_co_nP_co_P_imm; auto.
      { apply RCOH. }
      { eapply reservedW; eauto. }
      exists w. split; auto. apply seq_eqv_l. by split. }

    assert (~ (rf ⨾ rmw) w wconext) as NRFRMWCONEXT.
    { intros AA. apply NSW. eapply dom_rf_rmw_S; eauto. 
      exists wconext. apply seqA. apply seq_eqv_r. by split. }

    assert (Time.le (f_to wprev) (f_from wconext)) as FFLE by (by apply FCOH).
    
    assert (issued T wconext /\ ~ W_ex wconext) as [WSISS NWEXCONEXT].
    { eapply codom_nS_imm_co_S_in_I; eauto.
      simpls. exists w. apply seq_eqv_l. by split. }

    assert (codom_rel (⦗S⦘ ⨾ (rfi ⨾ rmw)＊) wconext) as CCBWCONEXT.
    { exists wconext. apply seq_eqv_l. split; auto. apply rt_refl. }

    assert (~ codom_rel (⦗S⦘ ⨾ (rfi ⨾ rmw)＊) w) as NCCBW.
    { intros [y HH].
      apply seq_eqv_l in HH. destruct HH as [SY RFRMW].
      apply rtE in RFRMW. destruct RFRMW as [HH|RFRMW].
      { red in HH. desf. }
      apply ct_end in RFRMW. destruct RFRMW as [z [AA RFRMW]].
      apply NWEX. red. generalize RFRMW. clear. basic_solver. }
    
    destruct smode eqn:SMODE; [left|right].
    2: { splits; eauto.
         cdes RESERVED_TIME.
         assert (set_compl (W_ex ∪₁ S) w) as WNRMWS.
         { intros [|]; eauto. }

         assert (sb w wconext) as SBNEXT.
         { eapply nS_imm_co_in_sb; auto.
           3: by apply FOR_SPLIT.
           { done. }
           (* all: try done.  *)
           red. split.
           { apply seq_eqv_r. split; auto. }
           ins.
           apply seq_eqv_r in R1. destruct R1 as [COWC [cs CCBC]].
           apply seq_eqv_r in R2. destruct R2 as [COCWCONEXT _].
           apply seq_eqv_l in CCBC. destruct CCBC as [SCS RFIRMWS].
           assert (RFRMWS : (rf ⨾ rmw)＊ cs c).
           { assert ((rfi ⨾ rmw)＊ ⊆ (rf ⨾ rmw)＊) as AA by (by rewrite rfi_in_rf).
               by apply AA. }
           assert (co cs wconext) as COCSWCONEXT.
           { apply rf_rmw_rt_in_co in RFRMWS; auto.
             apply rewrite_trans_seq_cr_l.
             { apply (co_trans WF). }
             eexists; eauto. }
           assert (cs <> w) as NEQCS.
           { intros HH. by subst. }
           apply (dom_l (wf_coD WF)) in COCSWCONEXT. destruct_seq_l COCSWCONEXT as WCS.
           apply (dom_l (wf_coE WF)) in COCSWCONEXT. destruct_seq_l COCSWCONEXT as ECS.
           assert (loc lab cs = Some locw) as CSLOC.
           { rewrite <- LOCNEXT. by apply (wf_col WF). }
           edestruct (wf_co_total WF) with (a:=w) (b:=cs) as [COCSW|COWCS]; eauto.
           { unfolder. by splits. }
           { apply NCOIMM with (c:=cs); basic_solver. }
           
           assert (co^? w cs) as AA.
           { eapply n_Wex_co_rf_rmw_rt_transp_in_co_cr; eauto.
             apply seq_eqv_l. split; auto.
             exists c. split; auto. }
           destruct AA as [|AA]; desf.
           eapply (co_irr WF). eapply (co_trans WF); eauto. }

         assert (~ Rel w) as NREL.
         { intros RR. apply WNCOV.
           eapply dom_W_Rel_sb_loc_I_in_C; eauto.
           exists wconext. unfolder. splits; eauto.
           red. by rewrite LOC. }

         assert (tid wconext = tid w) as TIDNEXT.
         { apply sb_tid_init in SBNEXT. destruct SBNEXT as [H|H]; desf. }
         assert (~ covered T wconext) as NCOVNEXT.
         { intros ?. apply WNCOV. eapply dom_sb_covered; eauto. basic_solver 10. }

         edestruct SIM_MEM with (l:=locw) (b:=wconext)
           as [wconextmsgrel [WCONEXTMEM WCONEXTPROM']]; eauto.
         set (wconextmsg:=Message.full vnext wconextmsgrel).
         assert (Memory.get locw (f_to wconext) (Local.promises local) =
                 Some (f_from wconext, wconextmsg)) as WCONEXTPROM.
         { apply WCONEXTPROM'; auto. }

         set (n_to := Time.middle (f_from wconext) (f_to wconext)).

         assert (~ is_init wconext) as NINITWCONEXT.
         { apply no_co_to_init in CONEXT; auto.
           apply seq_eqv_r in CONEXT. desf. }

         assert (Time.lt (f_from wconext) (f_to wconext)) as LLWCONEXT.
         { by apply FCOH. }
         assert (Time.lt (f_from wconext) n_to) as LLFROMN.
         { unfold n_to. by apply DenseOrder.middle_spec. }
         assert (Time.lt n_to (f_to wconext)) as LLTON.
         { unfold n_to. by apply DenseOrder.middle_spec. }

         set (rel' := View.join
                        (View.join rel'' (View.unwrap p_rel))
                        (View.singleton_ur locw n_to)).
         assert (View.opt_wf (Some rel')) as RELWF.
         { apply View.opt_wf_some.
           apply View.join_wf.
           2: by apply View.singleton_ur_wf.
           constructor.
           unfold View.join; simpls.
           rewrite PRELNN. simpls.
           rewrite RELPLN''. reflexivity. }

         assert (Message.wf (Message.full valw (Some rel'))) as MSGWF.
         { by constructor. }

         assert (f_to_coherent G (S ∪₁ eq w) (upd f_to w n_to)
                               (upd (upd f_from wconext n_to) w (f_from wconext))) as FCOH_NEW.
         { eapply f_to_coherent_split; eauto. }
    
         edestruct (@Memory.split_exists (Local.promises local) locw
                                         (f_from wconext) n_to (f_to wconext)
                                         (Message.full valw (Some rel')) wconextmsg)
           as [promises' PSPLIT]; eauto.

         edestruct (@Memory.split_exists
                      (Configuration.memory PC)
                           locw (f_from wconext) n_to (f_to wconext)
                           (Message.full valw (Some rel')) wconextmsg)
           as [memory' MSPLIT]; eauto.

         exists wconext, vnext, wconextmsgrel.
         exists (upd f_to w n_to).
         exists (upd (upd f_from wconext n_to) w (f_from wconext)).

         assert (Time.le (f_to wprev) (f_from wconext)) as LEWPWTO.
         { destruct (classic (is_init wprev)) as [WPINIT|WPNINIT].
           2: by apply FCOH; eauto.
           assert (f_to wprev = tid_init) as HH.
           { apply FCOH. by split. }
           rewrite HH. apply Time.bot_spec. }

         assert (Time.lt (f_to wprev) n_to) as LEWPNTO.
         { eapply TimeFacts.le_lt_lt; [by apply LEWPWTO|].
           unfold n_to.
           apply Time.middle_spec. by apply FCOH. }

         assert (DenseOrder.lt tid_init n_to) as NTOBOT.
         { unfold n_to.
           eapply TimeFacts.le_lt_lt; eauto.
           apply Time.bot_spec. }
         
         assert (Memory.inhabited memory') as INHAB'.
         { eapply Memory.split_inhabited; eauto. }

         assert (Memory.closed_timemap
                   (View.rlx
                      (View.join (View.join rel'' (View.unwrap p_rel))
                                 (View.singleton_ur locw n_to)))
                   memory') as CLOSTM.
         { unfold View.join; ins.
           apply Memory.join_closed_timemap.
           2: { eapply Memory.singleton_closed_timemap; eauto.
                erewrite Memory.split_o; eauto. rewrite loc_ts_eq_dec_eq; eauto. }
           apply Memory.join_closed_timemap.
           2: { subst. simpls. by apply Memory.closed_timemap_bot. }
           eapply Memory.split_closed_timemap; eauto.
           subst rel''. destruct (Rel w); apply MEM_CLOSE. }

         assert (Time.lt (View.rlx rel'' locw) n_to) as LTNTO.
         { simpls.
           eapply TimeFacts.le_lt_lt.
           2: by apply LEWPNTO.
           eapply le_msg_rel_f_to_wprev; eauto. by subst thread. }

         set (f_to' := upd f_to w n_to).
         assert (forall thread' langst' local' (TNEQ : tid w <> thread')
                        (TID' : IdentMap.find thread' (Configuration.threads PC) =
                                Some (langst', local')),
                    Memory.get locw (f_to' w) (Local.promises local') = None) as NINTER.
         { ins.
           destruct (Memory.get locw (f_to' w) (Local.promises local')) eqn:HH; auto.
           exfalso. destruct p as [from]. 
           eapply PROM_IN_MEM in HH; eauto.
           edestruct Memory.get_disjoint as [AA|AA];
             [by apply WCONEXTMEM|by apply HH | |]; desc; subst.
           { eapply Time.lt_strorder with (x:=f_to wconext).
             rewrite AA at 1. unfold f_to'. rewrite upds; auto. }
           apply AA with (x:=f_to' w); constructor; simpls.
           all: unfold f_to' in *; rewrite upds in *; try reflexivity; auto.
           { apply Time.le_lteq. auto. }
           apply Memory.get_ts in HH. desf. }

         assert (Time.lt (View.rlx rel'' locw) (f_to' w)) as REL_VIEW_LT.
         { unfold f_to'. rewrite upds.
           eapply TimeFacts.le_lt_lt; [|by apply LTNTO].
           reflexivity. }

         assert (Time.le (View.rlx rel'' locw) (f_to' w)) as REL_VIEW_LE.
         { apply Time.le_lteq. eauto. }
         
         assert (Time.le (View.rlx (View.unwrap p_rel) locw) (f_to' w)) as PREL_LE.
         { subst. apply Time.bot_spec. }

         assert (Time.le (Time.join (View.rlx rel'' locw)
                                    (View.rlx (View.unwrap p_rel) locw)) (f_to' w))
           as FREL_VIEW_LE.
         { apply Time.join_spec; auto. }

         assert (Time.le (TimeMap.join (TimeMap.join (View.rlx rel'')
                                                     (View.rlx (View.unwrap p_rel)))
                                       (TimeMap.singleton locw (f_to' w)) locw) (f_to' w))
           as FFREL_VIEW_LE.
         { unfold TimeMap.join. apply Time.join_spec; auto.
           unfold TimeMap.singleton, LocFun.add. desf. reflexivity. }

         unfold f_to' in *.
         splits; eauto.
         { apply WCONEXTPROM'. }
         { by rewrite upds, updo, upds. }
         { by rewrite upds. }
         { subst p_rel; simpls. by rewrite RELPLN''. }
         1-4: by ins; repeat (rewrite updo; [|by intros HH; subst]).
         { rewrite upds. unfold n_to. intros HH.
           eapply Time.lt_strorder with (x:=Time.bot).
           apply TimeFacts.le_lt_lt with (b:=f_from wconext).
           { apply Time.bot_spec. }
             by rewrite <- HH; apply Time.middle_spec. }
         { eapply f_to_coherent_mori; [|by apply FCOH_NEW].
           unfold S'. rewrite NONEXT. clear.
           simplify_tls_events. basic_solver. }

         exists promises'; exists memory'. unfold rel', rel'' in *.
         splits; auto.
         all: try (rewrite upds; (try rewrite (fun x y => updo x y NEQNEXT));
                   (try rewrite upds); auto).
         { rewrite upds in *. constructor; eauto. }
         { constructor; auto.
           unfold View.join. simpls. rewrite RELPLN''.
           subst p_rel. simpls. }
         { arewrite (View.singleton_ur locw n_to =
                     View.singleton_ur locw ((upd f_to w n_to) w)).
           { by rewrite upds. }
           arewrite (f_from wconext = (upd (upd f_from wconext n_to) w (f_from wconext)) w).
           { by rewrite upds. }
           eapply sim_helper_issue with (G:=G) (w:=w) (locw:=locw) (valw:=valw)
                                        (S':=S ∪₁ eq w); eauto.
           { transitivity (fun _ : actid => False); [|clear; basic_solver].
             generalize NWEX. unfold Execution.W_ex. clear. basic_solver 10. }
           { ins. rewrite updo; auto. intros HH. subst. eauto. }
           { clear. basic_solver. }
           rewrite IE. clear. basic_solver. }
         
         red. splits.
         2: { rewrite RMW_BEF_S. clear.
              simplify_tls_events.  basic_solver 10. }
         rewrite <- FOR_SPLIT.
         hahn_frame.
         clear. apply eqv_rel_mori.
         apply set_compl_mori. red.
         clear. simplify_tls_events. basic_solver 10. }

    assert (f_to wprev <> f_from wconext) as FFNEQ.
    { intros HH.
      cdes RESERVED_TIME.
      apply TFRMW in HH; auto.
      eapply rfrmw_in_im_co in HH; eauto.
        by eapply HH; [apply COPREV|]. }

    assert (Time.lt (f_to wprev) (f_from wconext)) as FFLT.
    { clear -FFLE FFNEQ. apply Time.le_lteq in FFLE. desf. }

    cdes RESERVED_TIME. desc.
    set (n_to := Time.middle (f_to wprev) (f_from wconext)).
    set (f_to' := upd f_to w n_to).
    exists f_to'.

    set (B := (rf ⨾ rmw) wprev w).
    assert (exists n_from,
               ⟪ NFROM : (n_from = f_to wprev /\ B) \/
                         (n_from = Time.middle (f_to wprev) n_to /\ ~B) ⟫)
      as [n_from NFROM].
    { by destruct (classic B); eexists; [left|right]. }
    set (f_from' := upd f_from w n_from).
    exists f_from'.

    assert (~ is_init wconext) as NINITWCONEXT.
    { apply no_co_to_init in CONEXT; auto.
      apply seq_eqv_r in CONEXT. desf. }

    assert (forall to from msg,
               Memory.get locw to (Configuration.memory PC) = Some (from, msg) ->
               Interval.disjoint (f_from' w, f_to' w) (from, to)) as DISJOINT.
    { ins. unfold f_to', f_from'; rewrite !upds.
      apply Interval.le_disjoint with (b:= (f_to wprev,f_from wconext)); auto.
      2: { eapply f_to_coherent_add_S_middle; eauto. }
      eapply co_S_memory_disjoint; eauto. }

    assert (Time.lt (f_to wprev) n_to) as LTNTO.
    { subst n_to. by apply DenseOrder.middle_spec. }

    assert (Time.lt (f_to' wprev) (f_to' w)) as PREVNLT.
    { unfold f_to'. rewrite upds, updo; auto. }

    assert (Time.le (View.rlx rel'' locw)
                    (View.rlx (TView.cur (Local.tview local)) locw)) as GG.
    { unfold rel''. destruct (Rel w).
      { reflexivity. }
      subst. eapply rel_le_cur; eauto. }

    assert (Time.lt (View.rlx rel'' locw) (f_to' w)) as REL_VIEW_LT.
    { unfold f_to'. rewrite upds.
      eapply TimeFacts.le_lt_lt; [|by apply LTNTO].
      eapply le_msg_rel_f_to_wprev; eauto. by subst thread. }

    assert (Time.le (View.rlx rel'' locw) (f_to' w)) as REL_VIEW_LE.
    { apply Time.le_lteq. eauto. }
    
    set (rel' := View.join (View.join rel'' (View.unwrap p_rel))
                           (View.singleton_ur locw (f_to' w))).
    assert (Time.le (View.rlx (View.unwrap p_rel) locw) (f_to' w)) as PREL_LE.
    { subst. apply Time.bot_spec. }
 
    assert (Time.le (Time.join (View.rlx rel'' locw)
                               (View.rlx (View.unwrap p_rel) locw)) (f_to' w))
      as FREL_VIEW_LE.
    { apply Time.join_spec; auto. }

    assert (Time.le (TimeMap.join (TimeMap.join (View.rlx rel'')
                                                (View.rlx (View.unwrap p_rel)))
                                  (TimeMap.singleton locw (f_to' w)) locw) (f_to' w))
      as FFREL_VIEW_LE.
    { unfold TimeMap.join. apply Time.join_spec; auto.
      unfold TimeMap.singleton, LocFun.add. desf. reflexivity. }

    assert (f_to_coherent G (S ∪₁ eq w) f_to' f_from') as FCOH_NEW.
    { unfold f_to', f_from'.
      eapply f_to_coherent_add_S_middle; eauto. }

    assert (Time.lt (f_from' w) (f_to' w)) as FTLT.
    { apply FCOH_NEW; auto. red; eauto. }

    assert (Message.wf (Message.full valw (Some rel'))) as WFREL'.
    { do 3 constructor.
      subst rel'. subst. simpls. rewrite RELPLN''. reflexivity. }

    edestruct (@Memory.add_exists (Local.promises local) locw (f_from' w) (f_to' w)
                                  (Message.full valw (Some rel')))
      as [promises' PADD]; eauto.
    { ins. eapply DISJOINT.
      eapply PROM_IN_MEM; eauto. }

    edestruct (@Memory.add_exists (Configuration.memory PC)
                                  locw (f_from' w) (f_to' w)
                                  (Message.full valw (Some rel')))
      as [memory' MADD]; eauto.
    
    (* assert (reserved_time *)
    (*           G (mkTC (covered T) (issued T ∪₁ eq w)) *)
    (*           (S ∪₁ eq w) (upd f_to w n_to) (upd f_from w n_from) *)
    (*           sim_normal memory') as RST. *)
    assert (reserved_time
              G (T ∪₁ eq (mkTL ta_issue w) ∪₁ eq (mkTL ta_reserve w)) (upd f_to w n_to) (upd f_from w n_from)
              sim_normal memory') as RST.
  { eapply reserved_time_add_S_middle; eauto. }
    
    assert (Memory.inhabited memory') as INHAB'. 
    { eapply Memory.add_inhabited; eauto. }

    assert (View.pln
              (View.join
                 (View.join rel'' (View.unwrap p_rel))
                 (View.singleton_ur locw (f_to' w))) =
            View.rlx
              (View.join (View.join rel'' (View.unwrap p_rel))
                         (View.singleton_ur locw (f_to' w)))) as RELPLN.
    { subst. simpls. by rewrite RELPLN''. }

    assert (Memory.closed_timemap
              (View.rlx
                 (View.join (View.join rel'' (View.unwrap p_rel))
                            (View.singleton_ur locw (f_to' w))))
              memory') as CLOSTM.
    { unfold View.join; ins.
      apply Memory.join_closed_timemap.
      2: { eapply Memory.singleton_closed_timemap; eauto.
           erewrite Memory.add_o; eauto. rewrite loc_ts_eq_dec_eq; eauto. }
      apply Memory.join_closed_timemap.
      2: { subst. simpls. by apply Memory.closed_timemap_bot. }
      eapply Memory.add_closed_timemap; eauto.
      subst rel''. destruct (Rel w); apply MEM_CLOSE. }

    assert (f_to' w <> Time.bot) as FTOWNB.
    { unfold f_to'. rewrite upds.
      intros HH.
      eapply Time.lt_strorder with (x:=n_to).
      rewrite HH at 1.
      eapply TimeFacts.le_lt_lt; [|edone].
      apply Time.bot_spec. }

    splits; eauto; subst rel'0; subst rel''0. 
    1-4: by unfold f_to', f_from'; ins; rewrite updo; [|by intros HH; subst].
    
    do 2 eexists. splits; eauto.
    { constructor; auto.
      { intros HH. inv HH. }
      ins. inv MSG.
      (* TODO: introduce a lemma *)
      assert (exists wto,
                 ⟪ SWTO   : S wto ⟫ /\
                 ⟪ WTOLOC : loc lab wto = Some locw ⟫ /\
                 ⟪ FWTO   : f_to   wto = to' ⟫ /\
                 ⟪ FWFROM : f_from wto = f_to' w ⟫).
      { destruct msg'.
        { apply MEM in GET. desf. exists b. splits; eauto. }
        apply HMEM in GET. desf. exists b. splits; eauto. }
      (* TODO: introduce a lemma *)
      desc.
      unfold f_to', n_to in FWFROM. rewrite upds in FWFROM.
      assert (E wto /\ W wto) as [EWTO WWTO] by (by apply SEW).
      assert (Time.lt (f_from wto) (f_from wconext)) as LL1.
      { rewrite FWFROM. apply Time.middle_spec; auto. }
      assert (Time.lt (f_to wprev) (f_from wto)) as LL2.
      { rewrite FWFROM. apply Time.middle_spec; auto. }
      assert (wto <> wconext) as WNEQ1.
      { intros HH. subst. eapply Time.lt_strorder; eauto. }
      assert (wto <> wprev) as WNEQ2.
      { intros HH. subst.
        apply Time.lt_strorder with (x:=f_from wprev).
        apply TimeFacts.le_lt_lt with (b:=f_to wprev); eauto. }
      edestruct (wf_co_total WF) with (a:=wto) (b:=wconext) as [AA|AA]; eauto.
      1,2: by unfolder; eauto.
      2: { eapply f_from_co_mon with (I:=S) in AA; eauto.
           eapply Time.lt_strorder with (x:=f_from wconext).
           etransitivity; eauto. }
      edestruct (wf_co_total WF) with (a:=wto) (b:=wprev) as [BB|BB]; eauto.
      1,2: by unfolder; eauto.
      { eapply f_to_co_mon with (I:=S) in BB; eauto.
        eapply Time.lt_strorder with (x:=f_from wto).
        eapply TimeFacts.le_lt_lt with (b:=f_to wto); eauto. }
      eapply COSIMM with (c:=wto).
      all: apply seq_eqv_lr; splits; eauto. }
    { constructor; auto. by rewrite RELPLN. }
    { eapply f_to_coherent_mori; [|by apply FCOH_NEW].
      subst S'. rewrite NONEXT. clear.
      simplify_tls_events. basic_solver. }
    { subst. eapply sim_helper_issue with (S':=S ∪₁ eq w); eauto.
      { transitivity (fun _ : actid => False); [|clear; basic_solver].
        generalize NWEX. unfold Execution.W_ex. clear; basic_solver. }
      { ins. unfold f_to'. rewrite updo; auto. intros HH; subst. eauto. }
      { by right. }
      rewrite IE. eauto with hahn. }
    eapply reserved_time_more; (try by apply RST); auto.

    apply (proj1 (@set_subset_empty_r actid _)) in NONEXT. rewrite NONEXT.
    rewrite !set_union_empty_r.
    rewrite set_pair_exact. auto. }

  set (ts := Memory.max_ts locw (Configuration.memory PC)).
  set (f_to' := upd f_to w (Time.incr (Time.incr ts))).
  exists f_to'.
 
  set (A :=
         exists wprev, ⟪ WPISS : issued T wprev ⟫ /\
                       ⟪ RFRMW : (rf ⨾ rmw) wprev w ⟫).
  assert (exists n_from,
             ⟪ NFROM_SPEC : ((n_from = ts) /\ A) \/ ((n_from = Time.incr ts) /\ ~ A) ⟫ )
    as [n_from NFROM].
  { destruct (classic A) as [H|H].
    { by exists ts; left. }
    by exists (Time.incr ts); right. }
  assert (Time.le ts n_from) as LENFROM_R.
  { destruct NFROM as [[N _]|[N _]]; subst; [reflexivity|].
    apply Time.le_lteq; left. apply DenseOrder.incr_spec. }

  assert (Time.le n_from (Time.incr ts)) as LENFROM_L.
  { destruct NFROM as [[N _]|[N _]]; subst; [|reflexivity].
    apply Time.le_lteq; left. apply DenseOrder.incr_spec. }

  set (f_from' := upd f_from w n_from).
  exists f_from'.

  assert (Time.lt (f_from' w) (f_to' w)) as NLT.
  { unfold f_to', f_from', ts; rewrite !upds.
    eapply TimeFacts.le_lt_lt.
    { apply LENFROM_L. }
    apply DenseOrder.incr_spec. }

  assert (Time.lt n_from (Time.incr (Time.incr ts))) as NNLT.
  { eapply TimeFacts.le_lt_lt.
    2: by apply Time.incr_spec.
    done. }

  assert (Time.lt (View.rlx (TView.cur (Local.tview local)) locw) (f_to' w))
    as REL_VIEW_HELPER.
  { unfold f_to', ts; rewrite upds.
    etransitivity.
    2: by apply DenseOrder.incr_spec.
    eapply TimeFacts.le_lt_lt.
    2: by apply DenseOrder.incr_spec.
    apply Memory.max_ts_spec2.
    apply MEM_CLOSE. }

  assert (Time.lt (View.rlx rel'' locw) (f_to' w)) as REL_VIEW_LT.
  { subst rel''. destruct (Rel w); auto.
    eapply TimeFacts.le_lt_lt; [|by apply REL_VIEW_HELPER].
    subst. eapply rel_le_cur; eauto.  }
  assert (Time.le (View.rlx rel'' locw) (f_to' w)) as REL_VIEW_LE.
  { by apply Time.le_lteq; left. }

  assert (Time.le (TimeMap.join (TimeMap.join (View.rlx rel'')
                                              (View.rlx (View.unwrap p_rel)))
                                (TimeMap.singleton locw (f_to' w)) locw) (f_to' w))
    as FFREL_VIEW_LE.
  { unfold TimeMap.join. apply Time.join_spec; auto.
    { apply Time.join_spec; auto. subst p_rel. simpls. apply Time.bot_spec. }
    unfold TimeMap.singleton, LocFun.add. desf. reflexivity. }

  assert (forall to from msg,
             Memory.get locw to (Configuration.memory PC) = Some (from, msg) ->
             Interval.disjoint (f_from' w, f_to' w) (from, to)) as DISJOINT.
  { unfold f_to', f_from', ts; rewrite !upds.
    ins; red; ins. destruct LHS. destruct RHS.
    simpls.
    eapply Time.lt_strorder.
    eapply TimeFacts.le_lt_lt.
    2: by apply FROM.
    etransitivity.
    2: by apply LENFROM_R.
    etransitivity.
    { apply TO0. }
    unfold ts.
    apply Memory.max_ts_spec in H. desf. }

  set (rel' := View.join (View.join rel'' (View.unwrap p_rel))
                         (View.singleton_ur locw (f_to' w))).
  assert (Time.le (View.rlx (View.unwrap p_rel) locw) (f_to' w)) as PREL_LE.
  { subst. apply Time.bot_spec. }

  assert (Message.wf (Message.full valw (Some rel'))) as WFREL'.
  { do 3 constructor.
    subst rel'. subst. simpls. rewrite RELPLN''. reflexivity. }

  edestruct (@Memory.add_exists
               (Local.promises local) locw (f_from' w) (f_to' w)
               (Message.full valw (Some rel')))
    as [promises' PADD]; auto.
  { ins. eapply DISJOINT.
    eapply PROM_IN_MEM; eauto. }

  edestruct (@Memory.add_exists
               (Configuration.memory PC) locw (f_from' w) (f_to' w)
               (Message.full valw (Some rel')))
    as [memory' MADD]; auto.

  assert (Memory.inhabited memory') as INHAB'. 
  { eapply Memory.add_inhabited; eauto. }

  assert (n_from = Memory.max_ts locw (Configuration.memory PC) /\ (rf ⨾ rmw) wprev w \/
          n_from = Time.incr (Memory.max_ts locw (Configuration.memory PC)) /\
          ~ (rf ⨾ rmw) wprev w) as FCOH_HELPER.
  { right. splits; auto.
    2: { intros HH. generalize NWEX, HH. unfold Execution.W_ex. clear. basic_solver. }
    subst ts A.
    destruct NFROM as [AA|]; desf.
    exfalso. generalize NWEX, RFRMW. unfold Execution.W_ex. clear. basic_solver. }

  assert (f_to_coherent G (S ∪₁ eq w) f_to' f_from') as FCOH_NEW.
  { unfold f_to', f_from'.
    eapply f_to_coherent_add_S_after; eauto.
    transitivity (fun _ : actid => False); [|clear; basic_solver].
    generalize NWEX. unfold Execution.W_ex. clear. basic_solver. }

  assert (reserved_time
            G (T ∪₁ eq (mkTL ta_issue w) ∪₁ eq (mkTL ta_reserve w)) f_to' f_from'
            smode memory') as RST.
  { unfold f_to', f_from'.
    eapply reserved_time_add_S_after; eauto. }

  assert (View.pln
            (View.join
               (View.join rel'' (View.unwrap p_rel))
               (View.singleton_ur locw (f_to' w))) =
          View.rlx
            (View.join (View.join rel'' (View.unwrap p_rel))
                       (View.singleton_ur locw (f_to' w)))) as RELPLN.
  { subst. simpls. by rewrite RELPLN''. }

  assert (Memory.closed_timemap
            (View.rlx
               (View.join (View.join rel'' (View.unwrap p_rel))
                          (View.singleton_ur locw (f_to' w))))
            memory') as CLOSTM.
  { unfold View.join; ins.
    apply Memory.join_closed_timemap.
    2: { eapply Memory.singleton_closed_timemap; eauto.
         erewrite Memory.add_o; eauto. rewrite loc_ts_eq_dec_eq; eauto. }
    apply Memory.join_closed_timemap.
    2: { subst. simpls. by apply Memory.closed_timemap_bot. }
    eapply Memory.add_closed_timemap; eauto.
    subst rel''. destruct (Rel w); apply MEM_CLOSE. }

  splits; eauto; subst rel'0; subst rel''0.
  1-4: by unfold f_to', f_from'; ins; rewrite updo; [|by intros HH; subst].
  { unfold f_to'. rewrite upds.
    intros HH.
    eapply Time.lt_strorder with (x:=Time.bot).
    rewrite <- HH at 2.
    eapply TimeFacts.le_lt_lt; [|edone].
    apply Time.bot_spec. }

  do 2 eexists. splits; eauto.
  { constructor; auto.
    { intros HH. inv HH. }
    ins. inv MSG.
    unfold f_to', ts in GET. rewrite upds in GET.
    set (AA:=GET).
    apply Memory.get_ts in AA. destruct AA as [[AA BB]|AA].
    { eapply Time.lt_strorder with (x:=Time.bot).
      rewrite <- AA at 2.
      eapply TimeFacts.le_lt_lt.
      2: by apply Time.incr_spec.
      apply Time.bot_spec. }
    apply Memory.max_ts_spec in GET. desc.
    eapply Time.lt_strorder. etransitivity; [|by apply AA].
    eapply TimeFacts.le_lt_lt; [by apply GET0|].
    etransitivity; apply Time.incr_spec. }
  { constructor; auto. by rewrite RELPLN. }
  { eapply f_to_coherent_mori; [|by apply FCOH_NEW].
    subst S'. rewrite NONEXT. clear.
    simplify_tls_events. basic_solver. }
  { subst. eapply sim_helper_issue with (S':=S ∪₁ eq w); eauto.
    { transitivity (fun _ : actid => False); [|clear; basic_solver].
      generalize NWEX. unfold Execution.W_ex. clear; basic_solver. }
    { ins. unfold f_to'. rewrite updo; auto. intros HH; subst. eauto. }
    { by right. }
    rewrite IE. eauto with hahn. }
  eapply reserved_time_more; (try by apply RST); auto.
  apply (proj1 (@set_subset_empty_r actid _)) in NONEXT. rewrite NONEXT.
  rewrite !set_union_empty_r.
  rewrite set_pair_exact. auto.
Qed.

End Aux.
