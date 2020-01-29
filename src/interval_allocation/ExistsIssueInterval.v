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

(* TODO: reuse in ExistsReserveInterval.v *) 
Lemma co_next_to_imm_co_next w locw
      (LOC : loc lab w = Some locw)
      (WNEXT : exists wnext, (co ⨾ ⦗ S ⦘) w wnext) :
  exists wnext vnext,
    << NCOIMM   : immediate (co ⨾ ⦗ S ⦘) w wnext >> /\
    << ISSNEXT : S wnext >>  /\
    << CONEXT  : co w wnext >>  /\
    << ENEXT   : E wnext >>  /\
    << WNEXT   : W wnext >>  /\
    << LOCNEXT : Loc_ locw wnext >>  /\
    << VNEXT   : val lab wnext = Some vnext >> /\
    << NEQNEXT : wnext <> w >>.
Proof using WF ETCCOH.
  clear RELCOV.
  assert (exists wnext, immediate (co ⨾ ⦗ S ⦘) w wnext) as [wnext NIMMCO].
  { desc; eapply clos_trans_immediate2 in WNEXT.
    apply ct_begin in WNEXT; unfold seq in *; desc; eauto.
    generalize (co_trans WF); unfold transitive; basic_solver 21.
    generalize (co_irr WF); basic_solver 21.
    unfolder; ins; desc; hahn_rewrite (dom_r (wf_coE WF)) in REL.
    unfolder in REL; desc; eauto. }
  clear WNEXT.
  assert (S wnext /\ co w wnext) as [ISSNEXT CONEXT].
  { destruct NIMMCO as [AA _]. by destruct_seq_r AA as BB. }
  assert (E wnext) as ENEXT.
  { by apply ETCCOH.(etc_S_in_E). }
  assert (W wnext) as WNEXT.
  { by apply (reservedW WF ETCCOH). }
  assert (Loc_ locw wnext) as LOCNEXT.
  { apply WF.(wf_col) in CONEXT. by rewrite <- CONEXT. }
  assert (exists vnext, val lab wnext = Some vnext) as [vnext VNEXT].
  { unfold val, is_w in *. desf.
    all: eexists; eauto. }
  exists wnext, vnext. splits; eauto.
  intros H; subst. by apply WF.(co_irr) in CONEXT.
Qed.

(* TODO: reuse in ExistsReserveInterval.v *) 
Lemma co_prev_to_imm_co_prev w locw
      (EW    : E w)
      (WW    : W w)
      (WNCOV : ~ covered T w)
      (LOC   : loc lab w = Some locw) :
  exists wprev vprev,
    << PCOIMM   : immediate (⦗ S ⦘ ⨾ co) wprev w >> /\
    << ISSPREV : S wprev >>  /\
    << COPREV  : co wprev w >>  /\
    << EPREV   : E wprev >>  /\
    << WPREV   : W wprev >>  /\
    << LOCPREV : Loc_ locw wprev >>  /\
    << VPREV   : val lab wprev = Some vprev >> /\
    << NEQPREV : wprev <> w >>.
Proof using WF IMMCON ETCCOH.
  clear RELCOV.
  assert (tc_coherent G sc T) as TCCOH by apply ETCCOH.
  assert (~ is_init w) as WNINIT.
  { intros HH. apply WNCOV. eapply init_covered; eauto. by split. }
  assert (exists wprev, immediate (⦗ S ⦘ ⨾ co) wprev w) as [wprev PIMMCO].
  { assert ((⦗ S ⦘ ⨾ co) (InitEvent locw) w) as WPREV.
    { assert (W (InitEvent locw)) as WI.
      { by apply init_w. }
      assert (E (InitEvent locw)) as EI.
      { apply wf_init; auto. by exists w; split. }
      assert (issued T (InitEvent locw)) as II.
      { apply (init_issued WF TCCOH). by split. }
      assert (S (InitEvent locw)) as IS.
      { by apply ETCCOH.(etc_I_in_S). }
      assert (InitEvent locw <> w) as NEQ.
      { intros H; subst. desf. }
      assert (loc lab (InitEvent locw) = Some locw) as LI.
      { unfold loc. by rewrite WF.(wf_init_lab). }
      apply seq_eqv_l; split; auto.
      edestruct WF.(wf_co_total).
      3: by apply NEQ.
      1,2: split; [split|]; auto.
      { by rewrite LOC. }
      { done. }
      exfalso. cdes IMMCON. eapply Cint.
      eexists; split.
      2: { apply r_step. by apply Execution_eco.co_in_eco; apply H. }
      apply sb_in_hb. apply init_ninit_sb; auto. }
    desc; eapply clos_trans_immediate2 in WPREV.
    apply ct_end in WPREV; unfold seq in *; desc; eauto.
    generalize (co_trans WF); unfold transitive; basic_solver 21.
    generalize (co_irr WF); basic_solver 21.
    unfolder; ins; desc; hahn_rewrite (dom_r (wf_coE WF)) in REL0.
    unfolder in REL0; desc; eauto. }
  assert (S wprev /\ co wprev w) as [ISSPREV COPREV].
  { destruct PIMMCO as [AA _]. by destruct_seq_l AA as BB. }
  assert (E wprev) as EPREV.
  { by apply ETCCOH.(etc_S_in_E). }
  assert (W wprev) as WPREV.
  { by apply (reservedW WF ETCCOH). }
  assert (Loc_ locw wprev) as LOCPREV.
  { apply WF.(wf_col) in COPREV. by rewrite COPREV. }
  assert (exists vprev, val lab wprev = Some vprev) as [vprev VPREV].
  { unfold val, is_w in *. desf.
    all: eexists; eauto. }
  exists wprev, vprev. splits; eauto.
  intros H; subst. by apply WF.(co_irr) in COPREV.
Qed.

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
      (MEM_CLOSE : memory_close local.(Local.tview) PC.(Configuration.memory))
      (TID : IdentMap.find (tid w) PC.(Configuration.threads) = Some (langst, local)) :
  let promises := local.(Local.promises) in
  let memory   := PC.(Configuration.memory) in
  let T'       := mkTC (covered T) (issued T ∪₁ eq w) in
  let S'       := S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G (mkETC T S) rfi (eq w) in
  exists f_to' f_from' p_rel,
    rfrmw_prev_rel G sc T f_to f_from PC.(Configuration.memory) w locw p_rel /\
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
          reserved_time G T' S' f_to' f_from' smode memory' ⟫.
Proof using WF IMMCON ETCCOH RELCOV FCOH SIM_TVIEW.
  assert (tc_coherent G sc T) as TCCOH by apply ETCCOH.
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

  destruct (classic (exists wnext, (co ⨾ ⦗ S ⦘) w wnext)) as [WNEXT|WNONEXT].
  { edestruct co_next_to_imm_co_next with (w:=w) as [wnext]; eauto. desc.
    edestruct co_prev_to_imm_co_prev with (w:=w) as [wprev]; eauto. desc.

    assert ((co ⨾ ⦗set_compl S⦘ ⨾ co) wprev wnext) as CONS.
    { exists w. split; auto. apply seq_eqv_l. by split. }
    assert (co wprev wnext) as COPN.
    { eapply WF.(co_trans); eauto. }

    assert (immediate (⦗S⦘ ⨾ co ⨾ ⦗S⦘) wprev wnext) as COSIMM.
    { apply P_co_nP_co_P_imm; auto.
      { apply ETCCOH. }
      { apply (reservedW WF ETCCOH). }
      exists w. split; auto. apply seq_eqv_l. by split. }
    
    destruct smode eqn:SMODE.
    2: { admit. }

    assert (f_to wprev <> f_from wnext) as FFNEQ.
    { intros HH.
      cdes RESERVED_TIME.
      apply TFRMW in HH; auto.
      eapply rfrmw_in_im_co in HH; eauto.
        by eapply HH; [apply COPREV|]. }
    assert (Time.le (f_to wprev) (f_from wnext)) as FFLE by (by apply FCOH).
    assert (Time.lt (f_to wprev) (f_from wnext)) as FFLT.
    { clear -FFLE FFNEQ. apply Time.le_lteq in FFLE. desf. }

    cdes RESERVED_TIME. desc.
    assert (~ (rf ⨾ rmw) w wnext) as NRFRMWNEXT.
    { intros AA. apply NSW. eapply (dom_rf_rmw_S WF ETCCOH).
      exists wnext. apply seqA. apply seq_eqv_r. by split. }
    
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

    edestruct exists_wprev_rel with (w:=w) as [p_rel PRELSPEC]; eauto.
    exists p_rel. split.
    { apply PRELSPEC. }

    red in PRELSPEC.
    set (rel'' :=
           if Rel w
           then TView.cur (Local.tview local)
           else TView.rel (Local.tview local) locw).
    
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
    { eapply TimeFacts.le_lt_lt; [by apply GG|].
      eapply TimeFacts.le_lt_lt; [|by apply PREVNLT].
      eapply le_cur_f_to_wprev; eauto. }

    set (rel' := View.join (View.join rel'' (View.unwrap p_rel))
                           (View.singleton_ur locw (f_to w))).
    assert (Time.le (View.rlx (View.unwrap p_rel) locw) (f_to wprev)) as PREL_LE'.
    { eapply le_p_rel_f_to_wprev; eauto. }
    assert (Time.le (View.rlx (View.unwrap p_rel) locw) (f_to w)) as PREL_LE.
    { desc.
      destruct PRELSPEC0; desc.
      { rewrite PREL. apply Time.bot_spec. }
      assert (p = wprev); subst.
      { eapply wf_rfrmwf; eauto. }
      apply Time.le_lteq. left.
      eapply TimeFacts.le_lt_lt.
      2: by apply PREVNLT.
      done. }

    assert (Time.le (View.rlx rel' locw) (f_to w)) as REL_VIEW_LE.
    { unfold rel'.
      unfold View.join, TimeMap.join. simpls.
      unfold TimeMap.singleton, LocFun.add.
      rewrite Loc.eq_dec_eq.
      apply Time.join_spec; [|reflexivity].
      apply Time.join_spec; auto.
      apply Time.le_lteq; auto. }

    edestruct (@Memory.add_exists (Local.promises local) locw (f_from' w) (f_to' w)
                                  (Message.full valw p_rel))
      as [promises' PADD].
    { ins. eapply DISJOINT.
      eapply PROM_IN_MEM; eauto. }
    { unfold f_from', f_to'. rewrite !upds.
      eapply f_to_coherent_add_S_middle with (S:=S); eauto. }
    {

    edestruct (@Memory.add_exists PC.(Configuration.memory) locw (f_from' w) (f_to' w) Message.reserve)
      as [memory' MADD].
    3: by apply Message.wf_reserve.
    { apply DISJOINT. }
    { unfold f_from', f_to'. rewrite !upds.
      eapply f_to_coherent_add_S_middle with (S:=S); eauto. }
    
    assert (f_to_coherent G (S ∪₁ eq w) f_to' f_from') as FCOH_NEW.
    { unfold f_to', f_from'.
      eapply f_to_coherent_add_S_middle; eauto. }

    assert (reserved_time
              G T (S ∪₁ eq w) (upd f_to w n_to) (upd f_from w n_from)
              sim_normal memory') as RST.
    { eapply reserved_time_add_S_middle; eauto. }
    
    eexists. splits; eauto.
    all: ins; unfold f_to', f_from'; rewrite updo; auto.
    all: intros HH; desf. }

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

  assert (Time.lt (View.rlx (TView.rel (Local.tview local) locw) locw)
                  (f_to' w))
      as REL_VIEW_LT.
  { unfold f_to', ts. rewrite upds.
    etransitivity.
    2: by apply DenseOrder.incr_spec.
    eapply TimeFacts.le_lt_lt.
    2: by apply DenseOrder.incr_spec.
    apply Memory.max_ts_spec2.
    apply MEM_CLOSE. }
  assert (Time.le (View.rlx (TView.rel (Local.tview local) locw) locw)
                  (f_to' w))
      as REL_VIEW_LE.
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

  edestruct (@Memory.add_exists (Local.promises local) locw (f_from' w) (f_to' w) Message.reserve)
    as [promises' PADD].
  3: by apply Message.wf_reserve.
  { ins. eapply DISJOINT.
    eapply PROM_IN_MEM; eauto. }
  { unfold f_from', f_to'. by rewrite !upds. }

  edestruct (@Memory.add_exists PC.(Configuration.memory) locw (f_from' w) (f_to' w) Message.reserve)
    as [memory' MADD].
  3: by apply Message.wf_reserve.
  { apply DISJOINT. }
  { unfold f_from', f_to'. by rewrite !upds. }
  
  destruct PRMWE as [wprev PRMWE].
  assert (issued T wprev) as IWPREV.
  { eapply dom_rf_rmw_S_in_I with (T:= (mkETC T (S ∪₁ eq w))); eauto.
    eexists. apply seqA.
    apply seq_eqv_r. split; eauto. by right. }
  assert (S wprev) as SWPREV by (by apply ETCCOH.(etc_I_in_S)).
  assert (immediate (⦗S⦘ ⨾ co) wprev w) as PIMMCO.
  { eapply rfrmwP_in_immPco with (P':=eq w); eauto.
    2: { apply seqA. basic_solver. }
    intros x [y HH]. apply seqA in HH. destruct_seq_r HH as AA; subst.
    assert (x = wprev); desf.
    eapply wf_rfrmwf; eauto. }
  
  cdes RESERVED_TIME.
  assert (f_to_coherent G (S ∪₁ eq w) f_to' f_from') as FCOH'.
  { eapply f_to_coherent_add_S_after; eauto.
    { intros x [y HH]. apply seqA in HH. destruct_seq_r HH as AA; subst.
      assert (x = wprev); desf.
      eapply wf_rfrmwf; eauto. }
    left. red in NFROM. desf. exfalso. apply NFROM0.
    red. exists wprev. splits; auto. }

  assert (reserved_time G T (S ∪₁ eq w) f_to' f_from' sim_normal memory') as REST'.
  { eapply reserved_time_add_S_after; eauto.
    red in NFROM. desf.
    2: { exfalso. apply NFROM0. red. eauto. }
    left. desf. }

  exists promises', memory'. splits; auto.
  all: ins; unfold f_to', f_from'; rewrite updo; auto.
  all: intros HH; desf.
Admitted.

End Aux.
