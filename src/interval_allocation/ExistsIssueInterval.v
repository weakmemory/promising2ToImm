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

Require Import AuxRel2.
Require Import TraversalConfig.
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
Require Import ImmProperties.
Require Import IntervalHelper.

Set Implicit Arguments.

Section Aux.

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

Variable T : trav_config.
Variable S : actid -> Prop.
Hypothesis ETCCOH : etc_coherent G sc (mkETC T S).

Hypothesis RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T.

Variable f_to f_from : actid -> Time.t.
Hypothesis FCOH : f_to_coherent G S f_to f_from.

Variable thread : thread_id.
Variable PC : Configuration.t.
Variable local : Local.t.

Hypothesis SIM_TVIEW : sim_tview G sc (covered T) f_to local.(Local.tview) thread.
Hypothesis INHAB : Memory.inhabited PC.(Configuration.memory).
Hypothesis PLN_RLX_EQ : pln_rlx_eq local.(Local.tview).
Hypothesis MEM_CLOSE : memory_close local.(Local.tview) PC.(Configuration.memory).

Lemma exists_time_interval_for_issue_no_next w locw valw langst smode
      (ISSUABLE : issuable G sc T w)
      (WNISS : ~ issued T w)
      (NWEX : ~ W_ex w)
      (NONEXT : dom_sb_S_rfrmw G (mkETC T S) rfi (eq w) ⊆₁ ∅)
      (LOC : loc lab w = Some locw)
      (VAL : val lab w = Some valw)
      (WTID : thread = tid w)
      (PROM_IN_MEM :
         forall thread' langst local
                (TID : IdentMap.find thread' PC.(Configuration.threads) =
                       Some (langst, local)),
           Memory.le local.(Local.promises) PC.(Configuration.memory))
      (RESERVED_TIME:
         reserved_time G T S f_to f_from smode PC.(Configuration.memory))
      (SIM_RES_MEM :
         sim_res_mem G T S f_to f_from (tid w) local (Configuration.memory PC))
      (SIM_MEM : sim_mem G sc T f_to f_from
                         (tid w) local PC.(Configuration.memory))
      (TID : IdentMap.find (tid w) PC.(Configuration.threads) = Some (langst, local)) :
  let promises := local.(Local.promises) in
  let memory   := PC.(Configuration.memory) in
  let T'       := mkTC (covered T) (issued T ∪₁ eq w) in
  let S'       := S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G (mkETC T S) rfi (eq w) in
  exists p_rel,
    rfrmw_prev_rel G sc T f_to f_from PC.(Configuration.memory) w locw p_rel /\
    (⟪ FOR_ISSUE :
         exists f_to' f_from',
           let rel'' :=
               if is_rel lab w
               then (TView.cur (Local.tview local))
               else (TView.rel (Local.tview local) locw)
           in
           let rel' := (View.join (View.join rel'' p_rel.(View.unwrap))
                                  (View.singleton_ur locw (f_to' w))) in
           ⟪ RELWFEQ : View.pln rel' = View.rlx rel' ⟫ /\
           ⟪ REL_VIEW_LT : Time.lt (View.rlx rel'' locw) (f_to' w) ⟫ /\
           ⟪ REL_VIEW_LE : Time.le (View.rlx rel'  locw) (f_to' w) ⟫ /\

           exists promises' memory',
             ⟪ PADD :
                 Memory.add local.(Local.promises) locw (f_from' w) (f_to' w)
                            (Message.full valw (Some rel')) promises' ⟫ /\
             ⟪ MADD :
                 Memory.add memory locw (f_from' w) (f_to' w)
                            (Message.full valw (Some rel')) memory' ⟫ /\

             ⟪ INHAB : Memory.inhabited memory' ⟫ /\
             ⟪ RELMCLOS : Memory.closed_timemap (View.rlx rel') memory' ⟫ /\
             ⟪ RELVCLOS : Memory.closed_view rel' memory' ⟫ /\

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
                 reserved_time G T' S' f_to' f_from' smode memory' ⟫ ⟫ \/
     ⟪ FOR_SPLIT :
         ⟪ SMODE : smode = sim_certification ⟫ /\
         exists ws wsmsg f_to' f_from',
           let rel'' :=
               if is_rel lab w
               then (TView.cur (Local.tview local))
               else (TView.rel (Local.tview local) locw)
           in
           let rel' := (View.join (View.join rel'' p_rel.(View.unwrap))
                                  (View.singleton_ur locw (f_to' w))) in
           ⟪ WSISS  : S ws ⟫ /\
           ⟪ WSNCOV : ~ covered T ws ⟫ /\

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
           ⟪ FCOH : f_to_coherent G S' f_to' f_from' ⟫ /\

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

             ⟪ INHAB : Memory.inhabited memory' ⟫ /\
             ⟪ RELMCLOS : Memory.closed_timemap (View.rlx rel') memory' ⟫ /\
             ⟪ RELVCLOS : Memory.closed_view rel' memory' ⟫ /\


             ⟪ HELPER :
                 sim_mem_helper
                   G sc f_to' w (f_from' w) valw
                   (View.join (View.join (if is_rel lab w
                                          then (TView.cur (Local.tview local))
                                          else (TView.rel (Local.tview local) locw))
                                         p_rel.(View.unwrap))
                              (View.singleton_ur locw (f_to' w))) ⟫ /\

             ⟪ RESERVED_TIME :
                 reserved_time G T' S' f_to' f_from' smode memory' ⟫ ⟫).
Proof using WF IMMCON ETCCOH RELCOV FCOH SIM_TVIEW PLN_RLX_EQ INHAB MEM_CLOSE.
  assert (tc_coherent G sc T) as TCCOH by apply ETCCOH.
  assert (S ⊆₁ E ∩₁ W) as SEW.
  { apply set_subset_inter_r. split; [by apply ETCCOH|].
    apply (reservedW WF ETCCOH). }
  assert (issued T ⊆₁ S) as IE by apply ETCCOH.
  assert (W w) as WW.
  { eapply issuableW; eauto. }
  assert (E w) as EW.
  { eapply issuableE; eauto. }
  assert (~ covered T w) as WNCOV.
  { intros HH. apply WNISS. eapply w_covered_issued; eauto. by split. }
  assert (~ S w) as NSW.
  { intros HH. apply NWEX. eapply etc_S_I_in_W_ex; eauto. by split. }
  assert (~ is_init w) as WNINIT.
  { intros HH. apply WNCOV. eapply init_covered; eauto. by split. }

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

  destruct (classic (exists wnext, (co ⨾ ⦗ S ⦘) w wnext)) as [WNEXT|WNONEXT]; [|left].
  { edestruct co_next_to_imm_co_next with (w:=w) as [wnext]; eauto. clear WNEXT. desc.
    assert ((co ⨾ ⦗set_compl S⦘ ⨾ co) wprev wnext) as CONS.
    { exists w. split; auto. apply seq_eqv_l. by split. }
    assert (co wprev wnext) as COPN.
    { eapply WF.(co_trans); eauto. }

    assert (immediate (⦗S⦘ ⨾ co ⨾ ⦗S⦘) wprev wnext) as COSIMM.
    { apply P_co_nP_co_P_imm; auto.
      { apply ETCCOH. }
      { apply (reservedW WF ETCCOH). }
      exists w. split; auto. apply seq_eqv_l. by split. }

    assert (~ (rf ⨾ rmw) w wnext) as NRFRMWNEXT.
    { intros AA. apply NSW. eapply (dom_rf_rmw_S WF ETCCOH).
      exists wnext. apply seqA. apply seq_eqv_r. by split. }

    assert (Time.le (f_to wprev) (f_from wnext)) as FFLE by (by apply FCOH).
    
    destruct smode eqn:SMODE; [left|right].
    2: { splits; eauto.
         cdes RESERVED_TIME.
         assert (set_compl (W_ex ∪₁ S) w) as WNRMWS.
         { intros [|]; eauto. }

         assert (sb w wnext) as SBNEXT.
         { eapply nS_imm_co_in_sb with (S:=S); eauto. }

         assert (tid wnext = tid w) as TIDNEXT.
         { apply sb_tid_init in SBNEXT. destruct SBNEXT as [H|H]; desf. }
         assert (~ covered T wnext) as NCOVNEXT.
         { intros H; apply TCCOH in H.
           apply WNCOV. apply H.
           eexists. apply seq_eqv_r; split; eauto. }

         edestruct reserved_to_message with (l:=locw) (b:=wnext)
           as [wnextmsg [WNEXTMEM WNEXTPROM']]; eauto.
         assert (Memory.get locw (f_to wnext) (Local.promises local) =
                 Some (f_from wnext, wnextmsg)) as WNEXTPROM.
         { apply WNEXTPROM'; auto. }

         set (n_to := Time.middle (f_from wnext) (f_to wnext)).

         assert (~ is_init wnext) as NINITWNEXT.
         { apply no_co_to_init in CONEXT; auto.
           2: { apply coherence_sc_per_loc. apply IMMCON. }
           apply seq_eqv_r in CONEXT. desf. }

         assert (Time.lt (f_from wnext) (f_to wnext)) as LLWNEXT.
         { by apply FCOH. }
         assert (Time.lt (f_from wnext) n_to) as LLFROMN.
         { unfold n_to. by apply DenseOrder.middle_spec. }
         assert (Time.lt n_to (f_to wnext)) as LLTON.
         { unfold n_to. by apply DenseOrder.middle_spec. }

         set (rel' := View.join
                        (View.join rel'' p_rel.(View.unwrap))
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
                               (upd (upd f_from wnext n_to) w (f_from wnext))) as FCOH_NEW.
         { eapply f_to_coherent_split; eauto. }
    
         edestruct (@Memory.split_exists (Local.promises local) locw
                                         (f_from wnext) n_to (f_to wnext)
                                         (Message.full valw (Some rel')) wnextmsg)
           as [promises' PSPLIT]; eauto.

         edestruct (@Memory.split_exists
                      PC.(Configuration.memory)
                           locw (f_from wnext) n_to (f_to wnext)
                           (Message.full valw (Some rel')) wnextmsg)
           as [memory' MSPLIT]; eauto.

         exists wnext, wnextmsg.
         exists (upd f_to w n_to).
         exists (upd (upd f_from wnext n_to) w (f_from wnext)).

         assert (Time.le (f_to wprev) (f_from wnext)) as LEWPWTO.
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

         splits; eauto.
         { by rewrite upds, updo, upds. }
         { by rewrite upds. }
         { subst p_rel; simpls. by rewrite RELPLN''. }
         { by rewrite upds. }
         { rewrite upds. subst p_rel; simpls.
           unfold TimeMap.join, TimeMap.singleton, LocFun.add, TimeMap.bot.
           rewrite Loc.eq_dec_eq.
           apply Time.join_spec; [|reflexivity].
           apply Time.join_spec.
           { apply Time.le_lteq. eauto. }
           apply Time.bot_spec. }
         { eapply f_to_coherent_mori; [|by apply FCOH_NEW].
           rewrite NONEXT. clear. basic_solver. }

         exists promises'; exists memory'. unfold rel', rel'' in *.
         splits; auto.
         all: try (rewrite upds; (try rewrite (fun x y => updo x y NEQNEXT));
                   (try rewrite upds); auto).
         { constructor; auto.
           unfold View.join. simpls. rewrite RELPLN''.
           subst p_rel. simpls. }
         { arewrite (View.singleton_ur locw n_to =
                     View.singleton_ur locw ((upd f_to w n_to) w)).
           { by rewrite upds. }
           arewrite (f_from wnext = (upd (upd f_from wnext n_to) w (f_from wnext)) w).
           { by rewrite upds. }
           eapply sim_helper_issue with (G:=G) (w:=w) (locw:=locw) (valw:=valw)
                                        (S':=S ∪₁ eq w); eauto.
           { transitivity (fun _ : actid => False); [|clear; basic_solver].
             generalize NWEX. unfold Execution.W_ex. clear. basic_solver 10. }
           { ins. rewrite updo; auto. intros HH. subst. eauto. }
           { clear. basic_solver. }
           rewrite IE. clear. basic_solver. }
         
         red. split; unnw.
         { etransitivity.
           2: by apply FOR_SPLIT.
           hahn_frame_r. clear. basic_solver 10. }
         rewrite RMW_BEF_S. clear. basic_solver 10. }

    assert (f_to wprev <> f_from wnext) as FFNEQ.
    { intros HH.
      cdes RESERVED_TIME.
      apply TFRMW in HH; auto.
      eapply rfrmw_in_im_co in HH; eauto.
        by eapply HH; [apply COPREV|]. }

    assert (Time.lt (f_to wprev) (f_from wnext)) as FFLT.
    { clear -FFLE FFNEQ. apply Time.le_lteq in FFLE. desf. }

    cdes RESERVED_TIME. desc.
    set (n_to := Time.middle (f_to wprev) (f_from wnext)).
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

    assert (~ is_init wnext) as NINITWNEXT.
    { apply no_co_to_init in CONEXT; auto.
      2: { apply coherence_sc_per_loc. apply IMMCON. }
      apply seq_eqv_r in CONEXT. desf. }

    assert (forall to from msg,
               Memory.get locw to (Configuration.memory PC) = Some (from, msg) ->
               Interval.disjoint (f_from' w, f_to' w) (from, to)) as DISJOINT.
    { ins. unfold f_to', f_from'; rewrite !upds.
      apply Interval.le_disjoint with (b:= (f_to wprev,f_from wnext)); auto.
      2: { eapply f_to_coherent_add_S_middle with (S:=S); eauto. }
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

    assert (Message.wf (Message.full valw (Some rel'))) as WFREL'.
    { do 3 constructor.
      subst rel'. subst. simpls. rewrite RELPLN''. reflexivity. }

    edestruct (@Memory.add_exists (Local.promises local) locw (f_from' w) (f_to' w)
                                  (Message.full valw (Some rel')))
      as [promises' PADD]; eauto.
    { ins. eapply DISJOINT.
      eapply PROM_IN_MEM; eauto. }
    { unfold f_from', f_to'. rewrite !upds.
      eapply f_to_coherent_add_S_middle with (S:=S); eauto. }

    edestruct (@Memory.add_exists PC.(Configuration.memory)
                                  locw (f_from' w) (f_to' w)
                                  (Message.full valw (Some rel')))
      as [memory' MADD]; eauto.
    { unfold f_from', f_to'. rewrite !upds.
      eapply f_to_coherent_add_S_middle with (S:=S); eauto. }
    
    assert (f_to_coherent G (S ∪₁ eq w) f_to' f_from') as FCOH_NEW.
    { unfold f_to', f_from'.
      eapply f_to_coherent_add_S_middle; eauto. }

    assert (reserved_time
              G (mkTC (covered T) (issued T ∪₁ eq w))
              (S ∪₁ eq w) (upd f_to w n_to) (upd f_from w n_from)
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

    splits; eauto; subst rel'0; subst rel''0. 
    { unfold View.join, TimeMap.join; ins. 
      repeat apply DenseOrder.join_spec; auto.
      unfold TimeMap.singleton, LocFun.add. rewrite Loc.eq_dec_eq. reflexivity. }
    do 2 eexists. splits; eauto.
    { constructor; auto. by rewrite RELPLN. }
    { eapply f_to_coherent_mori; [|by apply FCOH_NEW].
      rewrite NONEXT. clear. basic_solver. }
    { subst. eapply sim_helper_issue with (S':=S ∪₁ eq w); eauto.
      { transitivity (fun _ : actid => False); [|clear; basic_solver].
        generalize NWEX. unfold Execution.W_ex. clear; basic_solver. }
      { ins. unfold f_to'. rewrite updo; auto. intros HH; subst. eauto. }
      { by right. }
      rewrite IE. eauto with hahn. }
    eapply reserved_time_more; (try by apply RST); auto.
    { apply same_tc. }
    split; [rewrite NONEXT|]; eauto with hahn.
    clear. basic_solver 10. }

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

  assert (forall to from msg,
             Memory.get locw to (Configuration.memory PC) =
             Some (from, msg) ->
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
               PC.(Configuration.memory) locw (f_from' w) (f_to' w)
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
            G (mkTC (covered T) (issued T ∪₁ eq w))
            (S ∪₁ eq w) f_to' f_from'
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
  { unfold View.join, TimeMap.join; ins. 
    repeat apply DenseOrder.join_spec; auto.
    unfold TimeMap.singleton, LocFun.add. rewrite Loc.eq_dec_eq. reflexivity. }
  do 2 eexists. splits; eauto.
  { constructor; auto. by rewrite RELPLN. }
  { eapply f_to_coherent_mori; [|by apply FCOH_NEW].
    rewrite NONEXT. clear. basic_solver. }
  { subst. eapply sim_helper_issue with (S':=S ∪₁ eq w); eauto.
    { transitivity (fun _ : actid => False); [|clear; basic_solver].
      generalize NWEX. unfold Execution.W_ex. clear; basic_solver. }
    { ins. unfold f_to'. rewrite updo; auto. intros HH; subst. eauto. }
    { by right. }
    rewrite IE. eauto with hahn. }
  eapply reserved_time_more; (try by apply RST); auto.
  { apply same_tc. }
  split; [rewrite NONEXT|]; eauto with hahn.
  clear. basic_solver 10.
Qed.

End Aux.
