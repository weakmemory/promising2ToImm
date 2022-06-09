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
From imm Require Import FairExecution.

From imm Require Import AuxRel2.
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
Require Import TlsEventSets.

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

Variable f_to f_from : actid -> Time.t.
Hypothesis FCOH : f_to_coherent G S f_to f_from.

Lemma exists_time_interval_for_reserve PC w locw langst local smode
      (TSTEP : ext_itrav_step
                 (* G sc w (mkETC T S) (mkETC T (S ∪₁ eq w)) *)
                 G sc (mkTL ta_reserve w) T (T ∪₁ eq (mkTL ta_reserve w))
      )
      (LOC : loc lab w = Some locw)
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
      (MEM_CLOSE : memory_close (Local.tview local) (Configuration.memory PC))
      (TID : IdentMap.find (tid w) (Configuration.threads PC) = Some (langst, local))
      (RMWREX : dom_rel rmw ⊆₁ R_ex lab)
      (FAIR: mem_fair G)
  :
  let memory := (Configuration.memory PC) in
  exists f_to' f_from' promises' memory',
    ⟪ PADD :
        Memory.add (Local.promises local) locw (f_from' w) (f_to' w)
                                          Message.reserve promises' ⟫ /\
    ⟪ MADD :
        Memory.add memory locw (f_from' w) (f_to' w)
                   Message.reserve memory' ⟫ /\
    
    ⟪ REQ_TO   : forall e (SE: S e), f_to'   e = f_to   e ⟫ /\
    ⟪ REQ_FROM : forall e (SE: S e), f_from' e = f_from e ⟫ /\
    ⟪ FCOH : f_to_coherent G (S ∪₁ eq w) f_to' f_from' ⟫ /\
    ⟪ RESERVED_TIME :
        reserved_time G (T ∪₁ eq (mkTL ta_reserve w)) f_to' f_from' smode memory' ⟫.
Proof using WF IMMCON FCOH TCOH RCOH ICOH.
  (* assert (tc_coherent G sc T) as TCCOH by apply ETCCOH. *)
  assert (reserve_coherent G (T ∪₁ eq (mkTL ta_reserve w))) as RCOH' by apply TSTEP.

  assert (S ⊆₁ E ∩₁ W) as SEW.
  { apply set_subset_inter_r.
    split; eauto using rcoh_S_in_E, reservedW. }
  assert (issued T ⊆₁ S) as IE by (eapply rcoh_I_in_S; eauto).

  assert (W w) as WW.
  { eapply ext_itrav_step_reserveW; eauto. }

  assert (E w) as EW.
  { apply ext_itrav_stepE in TSTEP; eauto. }
  
  assert (exists valw, val lab w = Some valw) as [valw WVAL].
  { by apply is_w_val. }

  assert (~ S w) as NSW.
  { eapply ext_itrav_step_reserve_nS; eauto. }

  assert (~ issued T w) as WNISS.
  { intros AA. apply NSW. eapply rcoh_I_in_S; eauto. }

  assert (~ covered T w) as WNCOV.
  { inversion TSTEP. intros Cw. destruct WNISS.
    eapply w_covered_issued; vauto. }

  assert (~ is_init w) as WNINIT.
  { apply ext_itrav_step_ninit in TSTEP; eauto. }

  assert (W_ex w) as WEXW.
  { eapply rcoh_S_I_in_W_ex; [apply RCOH'| ].
    eapply set_equiv_exp.
    { simplify_tls_events. reflexivity. }
    unfolder. intuition. }

  assert ((E ∩₁ W ∩₁ Loc_ locw) w) as WEW.
  { split; [split|]; auto. }

  assert (codom_rel (rf ⨾ rmw) w) as PRMWE.
  { eapply W_ex_in_codom_rfrmw; eauto. }
  
  assert (smode = sim_normal); subst.
  { destruct smode; auto.
    exfalso. apply NSW.
    cdes RESERVED_TIME.
    assert (dom_rel (sb^? ⨾ ⦗S⦘) w) as [w' AA] by (by apply RMW_BEF_S).
    destruct_seq_r AA as SW'.
    destruct AA as [|AA]; desf.
    eapply rcoh_sb_S; eauto. red. simpls.
    split.
    { basic_solver 10. }
    assert (PRMWE' : codom_rel (rf ;; <|R_ex lab|> ⨾ rmw) w).
    { generalize PRMWE RMWREX. clear. basic_solver 20. }
    destruct PRMWE' as [x PRMWE'].
    exists x. apply seq_eqv_l. split; auto.
    2: by apply seqA.
    forward eapply dom_rf_rmw_S_in_I; [| apply RCOH'| ]; auto.
    simplify_tls_events. intros ISS'. apply ISS'.    
    exists w. apply seqA. apply seq_eqv_r. split; [|clear; basic_solver].
    generalize PRMWE'. clear. basic_solver. }

  destruct langst as [lang state].

  destruct (classic (exists wnext, (co ⨾ ⦗ S ⦘) w wnext)) as [WNEXT|WNONEXT].
  { edestruct co_next_to_imm_co_next with (w:=w) (T:=T) as [wnext]; eauto. desc.
    edestruct co_prev_to_imm_co_prev with (w:=w) (T:=T) as [wprev]; eauto. desc.

    assert ((co ⨾ ⦗set_compl S⦘ ⨾ co) wprev wnext) as CONS.
    { exists w. split; auto. apply seq_eqv_l. by split. }

    assert (co wprev wnext) as COPN.
    { eapply (co_trans WF); eauto. }

    assert (immediate (⦗S⦘ ⨾ co ⨾ ⦗S⦘) wprev wnext) as COSIMM.
    { apply P_co_nP_co_P_imm; auto.
      { apply RCOH. }
      { eapply reservedW; eauto. }
      exists w. split; auto. apply seq_eqv_l. by split. }

    assert (f_to wprev <> f_from wnext) as FFNEQ.
    { intros HH.
      cdes RESERVED_TIME.
      apply TFRMW in HH; auto.
      eapply rfrmw_in_im_co in HH; eauto.
        by eapply HH; [apply COPREV|]. }

    cdes RESERVED_TIME. desc.
    assert (~ (rf ⨾ rmw) w wnext) as NRFRMWNEXT.
    { intros AA. apply NSW. eapply dom_rf_rmw_S; eauto. 
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
      2: { eapply f_to_coherent_add_S_middle; eauto. }
      eapply co_S_memory_disjoint; eauto. }

    edestruct (@Memory.add_exists (Local.promises local) locw (f_from' w) (f_to' w) Message.reserve)
      as [promises' PADD].
    3: by apply Message.wf_reserve.
    { ins. eapply DISJOINT.
      eapply PROM_IN_MEM; eauto. }
    { unfold f_from', f_to'. rewrite !upds.
      eapply f_to_coherent_add_S_middle; eauto. }

    edestruct (@Memory.add_exists (Configuration.memory PC) locw (f_from' w) (f_to' w) Message.reserve)
      as [memory' MADD].
    3: by apply Message.wf_reserve.
    { apply DISJOINT. }
    { unfold f_from', f_to'. rewrite !upds.
      eapply f_to_coherent_add_S_middle; eauto. }
    
    assert (f_to_coherent G (S ∪₁ eq w) f_to' f_from') as FCOH_NEW.
    { unfold f_to', f_from'.
      eapply f_to_coherent_add_S_middle; eauto. }

    assert (reserved_time
              G (T ∪₁ eq (mkTL ta_reserve w)) (upd f_to w n_to) (upd f_from w n_from)
              sim_normal memory') as RST.
    { eapply reserved_time_add_S_middle; eauto. }
    
    do 2 eexists. splits; eauto.
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

  edestruct (@Memory.add_exists (Configuration.memory PC) locw (f_from' w) (f_to' w) Message.reserve)
    as [memory' MADD].
  3: by apply Message.wf_reserve.
  { apply DISJOINT. }
  { unfold f_from', f_to'. by rewrite !upds. }
  
  destruct PRMWE as [wprev PRMWE].
  assert (issued T wprev) as IWPREV.
  { apply dom_rf_rmw_S_in_I in RCOH'; auto. generalize RCOH'.
    simplify_tls_events. intros ISS'. apply ISS'.
    eexists. apply seqA.
    apply seq_eqv_r. split; eauto. by right. }
  assert (S wprev) as SWPREV by (by apply RCOH).
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

  assert (reserved_time G (T ∪₁ eq (mkTL ta_reserve w)) f_to' f_from' sim_normal memory') as REST'.
  { eapply reserved_time_add_S_after; eauto.
    red in NFROM. desf.
    2: { exfalso. apply NFROM0. red. eauto. }
    left. desf. }

  exists promises', memory'. splits; auto.
  all: ins; unfold f_to', f_from'; rewrite updo; auto.
  all: intros HH; desf.
Unshelve.
all: apply None.
Qed.

End Aux.
