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

Require Import AuxRel2.
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
Require Import ImmProperties.

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

Variable IMMCON : imm_consistent G sc.

Variable T : trav_config.
Variable S : actid -> Prop.
Variable ETCCOH : etc_coherent G sc (mkETC T S).

Variable RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T.

Variable f_to f_from : actid -> Time.t.
Variable FCOH : f_to_coherent G S f_to f_from.

(* TODO: move to a more appropriate place. *)
Lemma co_S_f_to_le w w'
      (SW  : S w)
      (SW' : S w')
      (CO  : co^? w w') :
  Time.le (f_to w) (f_to w').
Proof using WF IMMCON FCOH.
  destruct CO as [|CO]; [subst; reflexivity|].
  apply Time.le_lteq; left.
  eapply f_to_co_mon; eauto.
Qed.

(* TODO: move to a more appropriate place. *)
Lemma co_S_f_from_le w w'
      (NINIT : ~ is_init w)
      (SW  : S w)
      (SW' : S w')
      (CO  : co^? w w') :
  Time.le (f_from w) (f_from w').
Proof using WF FCOH.
  destruct CO as [|CO]; [subst; reflexivity|].
  apply Time.le_lteq; left.
  eapply f_from_co_mon; eauto.
Qed.

(* TODO: move to ImmProperties.v. *)
Lemma co_imm : co ≡ (immediate co)⁺.
Proof using WF.
  apply fsupp_imm_t; try apply WF.
  rewrite WF.(wf_coE).
  red. ins. eexists. ins. destruct_seq_l REL as AA.
  apply AA.
Qed.

(* TODO: move to a more appropriate place. *)
Lemma co_S_memory_disjoint memory locw wp wn
      (COIMM  : immediate (⦗S⦘ ⨾ co ⨾ ⦗S⦘) wp wn)
      (CONS   : (co ⨾ ⦗ set_compl S ⦘ ⨾ co) wp wn)
      (LOCP   : loc lab wp = Some locw)
      (RESERVED_TIME:
         reserved_time G T S f_to f_from sim_normal memory) :
  forall (to from : Time.t) (msg : Message.t)
         (IN : Memory.get locw to memory = Some (from, msg)),
    Interval.disjoint (f_to wp, f_from wn) (from, to).
Proof using WF IMMCON ETCCOH FCOH.
  assert (sc_per_loc G) as SPL.
  { apply coherence_sc_per_loc. apply IMMCON. }
  assert (tc_coherent G sc T) as TCCOH by apply ETCCOH.

  assert (S wp /\ co wp wn /\ S wn) as [SWP [COPN SWN]].
  { destruct COIMM as [AA _]. by destruct_seq AA as [BB CC]. }
  assert (E wp /\ E wn) as [EWP EWN].
  { by split; apply ETCCOH.(etc_S_in_E). }
  assert (W wp /\ W wn) as [WWP WWN].
  { by split; apply (reservedW WF ETCCOH). }
  assert (loc lab wn = Some locw) as LOCN.
  { rewrite <- LOCP. symmetry. by apply WF.(wf_col). }

  assert (~ is_init wn) as WNNIN.
  { apply no_co_to_init in COPN; auto.
    destruct_seq_r COPN as AA. desf. }

  red in RESERVED_TIME. desc.
  ins. destruct msg as [v rel|].
  { apply MEM in IN. desf.
    { red. ins. inv RHS. simpls.
      apply Time.le_lteq in TO. destruct TO as [TT|]; subst.
      { by apply time_lt_bot in TT. }
        by apply Time.lt_strorder in FROM. }
    assert (S b) as SB.
    { by apply ETCCOH.(etc_I_in_S). }
    assert (W b) as WB.
    { by apply TCCOH. }
    assert (co^? b wp \/ co^? wn b) as CO.
    { destruct (classic (b = wp)) as [|PNEQ]; subst.
      { by left; left. }
      destruct (classic (b = wn)) as [|NNEQ]; subst.
      { by right; left. }
      edestruct WF.(wf_co_total) as [|LIMM].
      3: by apply PNEQ.
      1,2: split; [split|]; eauto.
      { by left; right. }
      right; right.
      edestruct WF.(wf_co_total) as [LHN|].
      3: by apply NNEQ.
      1,2: split; [split|]; eauto.
      2: done.
      exfalso.
      clear COPN.
      eapply COIMM; apply seq_eqv_lr; eauto. }
    destruct CO as [CO|CO].
    { assert (Time.le (f_to b) (f_to wp)) as HH.
      { eapply co_S_f_to_le; eauto. }
      symmetry. by apply interval_disjoint_imm_le. }
    assert (Time.le (f_from wn) (f_from b)) as HH.
    { eapply co_S_f_from_le; eauto. }
      by apply interval_disjoint_imm_le. }

  apply HMEM in IN. desf.
  assert (E b) as EB.
  { by apply ETCCOH.(etc_S_in_E). }
  assert (W b) as WB.
  { by apply (reservedW WF ETCCOH). }

  assert (co^? b wp \/ co^? wn b) as CO.
  { destruct (classic (b = wp)) as [|PNEQ]; subst.
    { by left; left. }
    destruct (classic (b = wn)) as [|NNEQ]; subst.
    { by right; left. }
    edestruct WF.(wf_co_total) as [|LIMM].
    3: by apply PNEQ.
    1,2: split; [split|]; eauto.
    { by left; right. }
    right; right.
    edestruct WF.(wf_co_total) as [LHN|].
    3: by apply NNEQ.
    1,2: split; [split|]; eauto.
    2: done.
    exfalso.
    eapply COIMM.
    all: apply seq_eqv_lr; splits; eauto. }

  destruct CO as [CO|CO].
  { assert (Time.le (f_to b) (f_to wp)) as HH.
    { eapply co_S_f_to_le; eauto. }
    symmetry. by apply interval_disjoint_imm_le. }
  assert (Time.le (f_from wn) (f_from b)) as HH.
  { eapply co_S_f_from_le; eauto. }
    by apply interval_disjoint_imm_le.
Qed.

(* TODO: move to a more appropriate place. *)
Lemma f_to_coherent_add_S_middle memory local w wprev wnext n_to n_from
      (SIM_MEM : sim_mem G sc T f_to f_from
                         (tid w) local memory)
      (TFRMW : forall x y (SX : S x) (SY : S y) (CO : co x y)
                      (FTOFROM : f_to x = f_from y),
          (rf ⨾ rmw) x y)
      (NSW : ~ S w)
      (NIMMCO : immediate (co ⨾ ⦗S⦘) w wnext)
      (PIMMCO : immediate (⦗S⦘ ⨾ co) wprev w)
      (NTO    : (n_to = f_from wnext /\
                 ⟪ NRFRMW : (rf ⨾ rmw) w wnext ⟫) \/
                (n_to = Time.middle (f_to wprev) (f_from wnext) /\
                 ⟪ NNRFRMW : ~ (rf ⨾ rmw) w wnext ⟫))
      (NFROM  : (n_from = f_to wprev /\
                 ⟪ PRFRMW : (rf ⨾ rmw) wprev w ⟫) \/
                (n_from = Time.middle (f_to wprev) n_to /\
                 ⟪ NPRFRMW : ~ (rf ⨾ rmw) wprev w ⟫)) :
  << FCOH' : f_to_coherent G (S ∪₁ eq w) (upd f_to w n_to) (upd f_from w n_from) >> /\
  << INTLE : Interval.le (n_from, n_to) (f_to wprev, f_from wnext) >> /\
  << NFROMTOLT : Time.lt n_from n_to >>.
Proof using WF IMMCON ETCCOH FCOH.
  assert (tc_coherent G sc T) as TCCOH by apply ETCCOH.
  assert (S ⊆₁ E) as SinE by apply ETCCOH.
  assert (S ⊆₁ W) as SinW by apply (reservedW WF ETCCOH).
  assert (sc_per_loc G) as SPL.
  { apply coherence_sc_per_loc. apply IMMCON. }

  assert (S wnext /\ co w wnext) as [ISSNEXT CONEXT].
  { destruct NIMMCO as [AA _]. by destruct_seq_r AA as BB. }

  assert (E wnext) as ENEXT.
  { by apply ETCCOH.(etc_S_in_E). }
  assert (W wnext) as WNEXT.
  { by apply (reservedW WF ETCCOH). }

  assert (S wprev /\ co wprev w) as [ISSPREV COPREV].
  { destruct PIMMCO as [H _]. apply seq_eqv_l in H; desf. }
  assert (E wprev) as EPREV.
  { by apply ETCCOH.(etc_S_in_E). }
  assert (W wprev) as WPREV.
  { by apply (reservedW WF ETCCOH). }

  assert (E w) as EW.
  { apply WF.(wf_coE) in CONEXT. by destruct_seq CONEXT as [AA BB]. }
  assert (W w) as WW.
  { apply WF.(wf_coD) in CONEXT. by destruct_seq CONEXT as [AA BB]. }

  assert (~ is_init w) as WNINIT.
  { apply no_co_to_init in COPREV; auto. by destruct_seq_r COPREV as AA. }

  assert (~ is_init wnext) as NINITWNEXT.
  { apply no_co_to_init in CONEXT; auto.
    apply seq_eqv_r in CONEXT. desf. }

  assert (co wprev wnext) as COPN.
  { eapply WF.(co_trans); eauto. }

  assert (Time.lt (f_to wprev) (f_from wnext)) as NPLT.
  { assert (Time.le (f_to wprev) (f_from wnext)) as H.
    { apply FCOH; auto. }
    apply Time.le_lteq in H. destruct H as [|H]; [done|exfalso].
    apply TFRMW in H; auto.
    eapply rfrmw_in_im_co in H; eauto.
      by eapply H; [apply COPREV|]. }
  
  assert (Time.le n_from (Time.middle (f_to wprev) (f_from wnext))) as LEFROMTO1.
  { desf; try reflexivity.
    all: apply Time.le_lteq; left.
    all: repeat (apply Time.middle_spec; auto). }

  assert (Time.lt (f_to wprev) n_to) as LTPREVTO.
  { desf; by apply Time.middle_spec. }

  assert (Time.le (f_to wprev) n_from) as PREVFROMLE.
  { destruct NFROM as [[N1 N2]|[N1 N2]]; subst; [reflexivity|].
    apply Time.le_lteq; left. by apply Time.middle_spec. }

  assert (Time.lt n_from n_to) as LTFROMTO.
  { desf.
    { by apply Time.middle_spec. }
    eapply TimeFacts.lt_le_lt.
    2: reflexivity.
      by do 2 apply Time.middle_spec. }
  
  assert (Time.le (Time.middle (f_to wprev) (f_from wnext)) n_to) as LETO1.
  { desf; try reflexivity.
    all: by apply Time.le_lteq; left; apply Time.middle_spec. }

  assert (Time.le n_to (f_from wnext)) as LETONEXT.
  { desf; try reflexivity.
    all: by apply Time.le_lteq; left; apply Time.middle_spec. }
  
  splits; auto.
  2: { by constructor. }

  red; splits.
  { ins; rewrite updo; [by apply FCOH|].
    intros Y; subst. destruct H. desf. }
  { ins; rewrite updo; [by apply FCOH|].
    intros Y; subst. destruct H. desf. }
  { intros x [ISS|]; subst.
    { rewrite !updo; [by apply FCOH | |].
      all: by intros Y; subst. }
    ins. by rewrite !upds in *. }
  { intros x y [ISSX|EQX] [ISSY|EQY] CO; subst.
    all: try rewrite !upds.
    all: try rewrite !updo.
    all: try by intros H; subst.
    { by apply FCOH. }
    { etransitivity; [|by apply PREVFROMLE].
      assert (co^? x wprev) as COXP.
      { apply P_co_immediate_P_co_transp_in_co_cr with (P:=S); auto.
        exists y. split; auto. basic_solver. }
      eapply co_S_f_to_le; eauto. }
    2: by apply WF.(co_irr) in CO.
    etransitivity; [by apply LETONEXT|].
    assert (co^? wnext y) as COXP.
    { apply immediate_co_P_transp_co_P_in_co_cr with (P:=S); auto.
      exists x. split; auto. basic_solver. }
    eapply co_S_f_from_le; eauto. }
  intros x y [ISSX|EQX] [ISSY|EQY] RFRMW; subst.
  all: try rewrite !upds.
  all: try rewrite !updo.
  all: try by intros H; subst.
  { by apply FCOH. }
  3: { exfalso. eapply WF.(co_irr).
       eapply rfrmw_in_im_co in RFRMW; eauto.
       apply RFRMW. }
  2: { set (CC:=RFRMW).
       eapply rfrmw_in_im_co in CC; eauto.
       destruct CC as [AA BB].
       assert (co^? wnext y) as [|COY]; subst.
       { apply immediate_co_P_transp_co_P_in_co_cr with (P:=S); auto.
         exists x. split; auto. basic_solver. }
       { destruct NTO as [[NN1 NN2]|[NN1 NN2]]; desf. }
       exfalso. by apply BB with (c:=wnext). }
  set (CC:=RFRMW).
  eapply rfrmw_in_im_co in CC; eauto.
  destruct CC as [AA BB].
  assert (co^? x wprev) as [|COY]; subst.
  { apply P_co_immediate_P_co_transp_in_co_cr with (P:=S); auto.
    exists y. split; auto. basic_solver. }
  { destruct NFROM as [[NN1 NN2]|[NN1 NN2]]; desf. }
  exfalso. by apply BB with (c:=wprev).
Qed.

(* TODO: move to SimulationRelProperties.v *)
Lemma S_le_max_ts locw memory local thread x
      (SX   : S x)
      (XLOC : loc lab x = Some locw)
      (SIMMEM    : sim_mem     G sc T f_to f_from thread local memory)
      (SIMRESMEM : sim_res_mem G T S f_to f_from thread local memory) :
  Time.le (f_to x) (Memory.max_ts locw memory).
Proof using ETCCOH.
  eapply reserved_to_message in SX; eauto.
  2: by apply ETCCOH.
  desf.
  eapply Memory.max_ts_spec; eauto.
Qed.

(* TODO: move to more appropriate place *)
Lemma rfrmwP_in_immPco P P'
    (DRES : dom_rel (rf ;; rmw ;; <|P'|>) ⊆₁ P) :
  rf ;; rmw ;; <|P'|> ⊆ immediate (⦗P⦘ ⨾ co).
Proof using WF IMMCON.
  assert (sc_per_loc G) as SPL.
  { apply coherence_sc_per_loc. apply IMMCON. }

  rewrite <- immediate_inter_mori with (x:=co).
  2: basic_solver.
  apply inclusion_inter_r.
  2: { rewrite <- seqA. rewrite rfrmw_in_im_co; eauto. basic_solver. }
  rewrite <- rf_rmw_in_co; auto.
  2: by apply IMMCON.
  generalize DRES. basic_solver 10.
Qed.

(* TODO: move to more appropriate place *)
Lemma no_next_S_max_ts locw memory local w x
      (MTE  : message_to_event G T f_to f_from memory)
      (HMTE : half_message_to_event G T S f_to f_from memory)
      (SIM_RES_MEM : sim_res_mem G T S f_to f_from (tid w) local memory)
      (SIM_MEM : sim_mem G sc T f_to f_from (tid w) local memory)
      (WLOC : loc lab w = Some locw)
      (NCO : ~ (exists wnext : actid, (co ⨾ ⦗S⦘) w wnext))
      (NSW : ~ S w)
      (SX : S x)
      (RFRMW : (rf ⨾ rmw) x w) :
  f_to x = Memory.max_ts locw memory.
Proof using WF IMMCON FCOH ETCCOH.
  assert (complete G) as COMPL by apply IMMCON.
  assert (sc_per_loc G) as SPL.
  { apply coherence_sc_per_loc. apply IMMCON. }
  assert (co x w) as COXW by (by apply rf_rmw_in_co).
  assert (loc lab x = Some locw) as XLOC. 
  { rewrite <- WLOC. by apply WF.(wf_col). }

  set (XX:=SX).
  eapply reserved_to_message in XX; eauto.
  2: by apply ETCCOH.
  desf.
  edestruct Memory.max_ts_spec as [[from [msg' HMEM]] TS]; eauto.
  red in TS.
  eapply memory_to_event in HMEM; eauto.
  apply Time.le_lteq in TS; destruct TS as [TS|]; [|by subst].
  desf.
  { rewrite HMEM in TS. by apply time_lt_bot in TS. }
  rename b into wmax.
  exfalso.
  
  assert (E w /\ E x) as [EW EX].
  { apply WF.(wf_coE) in COXW. destruct_seq COXW as [AA BB]. desf. }
  assert (W w /\ W x) as [WW WX].
  { apply WF.(wf_coD) in COXW. destruct_seq COXW as [AA BB]. desf. }
  assert (W wmax) as WWMAX.
  { by apply (reservedW WF ETCCOH). }
  
  assert (wmax <> w) as WWNEQ.
  { intros PP; desf. }
  edestruct WF.(wf_co_total) with (a:=wmax) (b:=w) as [CO|CO]; auto.
  1,2: by split; [split|]; eauto.
  2: { apply NCO. eexists. apply seq_eqv_r. eauto. }

  destruct (classic (wmax = x)) as [|WXNEQ]; subst.
  { rewrite TO in TS. eapply Time.lt_strorder; eauto. }

  edestruct WF.(wf_co_total) with (a:=wmax) (b:=x) as [CO'|CO']; auto.
  1,2: by split; [split|]; eauto.
  2: { eapply rfrmw_in_im_co; eauto. }
  eapply Time.lt_strorder.
  etransitivity; [by apply TS|].
  rewrite <- TO.
  eapply f_to_co_mon; eauto.
Qed.

Lemma f_to_coherent_add_S_after locw memory local w wprev n_from
      (RESERVED_TIME:
         reserved_time G T S f_to f_from sim_normal memory)
      (SIM_MEM : sim_mem G sc T f_to f_from
                         (tid w) local memory)
      (SIM_RES_MEM : sim_res_mem G T S f_to f_from (tid w) local memory)
      (TFRMW : forall x y (SX : S x) (SY : S y) (CO : co x y)
                      (FTOFROM : f_to x = f_from y),
          (rf ⨾ rmw) x y)
      (WLOC : loc lab w = Some locw)
      (NSW : ~ S w)
      (DRES : dom_rel (rf ⨾ rmw ⨾ ⦗eq w⦘) ⊆₁ S)
      (NCO : ~ exists wnext, (co ⨾ ⦗S⦘) w wnext)
      (PIMMCO : immediate (⦗S⦘ ⨾ co) wprev w)
      (NFROM  : (n_from = Memory.max_ts locw memory /\
                 ⟪ PRFRMW : (rf ⨾ rmw) wprev w ⟫) \/
                (n_from = Time.incr (Memory.max_ts locw memory) /\
                 ⟪ NPRFRMW : ~ (rf ⨾ rmw) wprev w ⟫)) :
  (* << FCOH' : *)
    f_to_coherent
      G (S ∪₁ eq w)
      (upd f_to w (Time.incr (Time.incr (Memory.max_ts locw memory))))
      (upd f_from w n_from).
(* >> /\ *)
(*   << NFROMTOLT : Time.lt n_from n_to >>. *)
Proof using WF IMMCON ETCCOH FCOH.
  assert (tc_coherent G sc T) as TCCOH by apply ETCCOH.
  assert (S ⊆₁ E) as SinE by apply ETCCOH.
  assert (S ⊆₁ W) as SinW by apply (reservedW WF ETCCOH).
  assert (sc_per_loc G) as SPL.
  { apply coherence_sc_per_loc. apply IMMCON. }

  assert (S wprev /\ co wprev w) as [ISSPREV COPREV].
  { destruct PIMMCO as [H _]. apply seq_eqv_l in H; desf. }
  assert (E wprev) as EPREV.
  { by apply ETCCOH.(etc_S_in_E). }
  assert (W wprev) as WPREV.
  { by apply (reservedW WF ETCCOH). }

  assert (E w) as EW.
  { apply WF.(wf_coE) in COPREV. by destruct_seq COPREV as [AA BB]. }
  assert (W w) as WW.
  { apply WF.(wf_coD) in COPREV. by destruct_seq COPREV as [AA BB]. }

  assert (~ is_init w) as WNINIT.
  { apply no_co_to_init in COPREV; auto. by destruct_seq_r COPREV as AA. }
  
  set (ts := Memory.max_ts locw memory).
  set (f_to' := upd f_to w (Time.incr (Time.incr (Memory.max_ts locw memory)))).

  assert (Time.le ts n_from) as LENFROM_R.
  { destruct NFROM as [[N _]|[N _]]; subst; [reflexivity|].
    apply Time.le_lteq; left. apply DenseOrder.incr_spec. }

  assert (Time.le n_from (Time.incr ts)) as LENFROM_L.
  { destruct NFROM as [[N _]|[N _]]; subst; [|reflexivity].
    apply Time.le_lteq; left. apply DenseOrder.incr_spec. }
  set (f_from' := upd f_from w n_from).

  assert (Time.lt (f_from' w) (f_to' w)) as NLT.
  { unfold f_to', f_from', ts; rewrite !upds.
    eapply TimeFacts.le_lt_lt.
    { apply LENFROM_L. }
    apply DenseOrder.incr_spec. }

  assert (Time.lt n_from (Time.incr (Time.incr ts))) as NNLT.
  { eapply TimeFacts.le_lt_lt.
    2: by apply Time.incr_spec.
    done. }

  red; splits; unfold f_from'.
  { ins; rewrite updo; [by apply FCOH|].
    intros Y; subst. by destruct H. }
  { ins; rewrite updo; [by apply FCOH|].
    intros Y; subst. by destruct H. }
  { intros x [ISS|]; subst.
    { rewrite !updo; [by apply FCOH | |].
      all: by intros Y; subst. }
    unfold f_to', f_from', ts in *.
      by rewrite !upds in *. }
  { intros x y [ISSX|EQX] [ISSY|EQY] CO; subst.
    all: try rewrite !upds.
    all: try rewrite !updo.
    all: try by intros H; subst.
    { by apply FCOH. }
    { etransitivity; [|by apply LENFROM_R].
      eapply S_le_max_ts; eauto.
      rewrite <- WLOC. by apply WF.(wf_col). }
    { exfalso. eapply NCO. eexists; apply seq_eqv_r; eauto. }
    exfalso. by apply co_irr in CO. }
  intros x y [ISSX|EQX] [ISSY|EQY] RFRMW; subst.
  all: try rewrite !upds.
  all: try rewrite !updo.
  all: try by intros H; subst.
  { by apply FCOH. }
  { (* TODO: extract some reasoning *)
    destruct NFROM as [[EQ HH]|[EQ NWPREV]]; subst; unnw.
    2: { exfalso.
         assert (x = wprev); desf.
         eapply wf_immcoPtf; eauto; red.
         eapply rfrmwP_in_immPco with (P':=eq y); eauto.
         apply seqA. basic_solver. }
    cdes RESERVED_TIME.
    eapply no_next_S_max_ts; eauto. }

  all: exfalso; eapply rfrmw_in_im_co in RFRMW; eauto.
  { eapply NCO. eexists; apply seq_eqv_r; split; eauto.
    apply RFRMW. }
  eapply WF.(co_irr). apply RFRMW.
Qed.

(* TODO: move to a more appropriate place. *)
Lemma message_to_event_add_S memory l w memory' n_to n_from
      (LOC : loc lab w = Some l)
      (NIW : ~ issued T w)
      (RESERVED_TIME:
         reserved_time G T S f_to f_from sim_normal memory)
      (MADD :
        Memory.add memory l
                   ((upd f_from w n_from) w)
                   ((upd f_to w n_to) w)
                   Message.reserve memory') :
  message_to_event G T (upd f_to w n_to) (upd f_from w n_from) memory'.
Proof using.
  red in RESERVED_TIME. desc.
  set (f_to':= upd f_to w n_to).
  set (f_from':= upd f_from w n_from).

  red; ins. erewrite Memory.add_o in MSG; eauto.
  destruct (loc_ts_eq_dec (l0, to) (l, f_to' w)) as [[EQ1 EQ2]|NEQ].
  { simpls; subst.
    rewrite (loc_ts_eq_dec_eq l (f_to' w)) in MSG.
    inv MSG. }
  rewrite loc_ts_eq_dec_neq in MSG; simpls; auto.
  apply MEM in MSG. destruct MSG as [MSG|MSG]; [by left|right].
  destruct MSG as [b H]; desc.
  assert (b <> w) as BNEQ.
  { by intros H; subst. }
  unfold f_to', f_from'.
  exists b; splits; auto.
  all: by rewrite updo.
Qed.

(* TODO: move to a more appropriate place. *)
Lemma reserved_time_add_S_middle smode memory local l w wprev wnext memory' n_to n_from
      (SIM_MEM : sim_mem G sc T f_to f_from
                         (tid w) local memory)
      (TFRMW : forall x y (SX : S x) (SY : S y) (CO : co x y)
                      (FTOFROM : f_to x = f_from y),
          (rf ⨾ rmw) x y)
      (LOC : loc lab w = Some l)
      (EW  : E w)
      (NSW : ~ S w)
      (NIMMCO : immediate (co ⨾ ⦗S⦘) w wnext)
      (PIMMCO : immediate (⦗S⦘ ⨾ co) wprev w)
      (NTO    : (n_to = f_from wnext /\
                 ⟪ NRFRMW : (rf ⨾ rmw) w wnext ⟫) \/
                (n_to = Time.middle (f_to wprev) (f_from wnext) /\
                 ⟪ NNRFRMW : ~ (rf ⨾ rmw) w wnext ⟫))
      (NFROM  : (n_from = f_to wprev /\
                 ⟪ PRFRMW : (rf ⨾ rmw) wprev w ⟫) \/
                (n_from = Time.middle (f_to wprev) n_to /\
                 ⟪ NPRFRMW : ~ (rf ⨾ rmw) wprev w ⟫))
      (RESERVED_TIME:
         reserved_time G T S f_to f_from smode memory)
      (MADD :
        Memory.add memory l
                   ((upd f_from w n_from) w)
                   ((upd f_to w n_to) w)
                   Message.reserve memory') :
  reserved_time
    G T (S ∪₁ eq w) (upd f_to w n_to) (upd f_from w n_from)
    smode memory'.
Proof using WF IMMCON ETCCOH FCOH.
  assert (sc_per_loc G) as SPL.
  { apply coherence_sc_per_loc. apply IMMCON. }

  assert (S ⊆₁ E ∩₁ W) as SEW.
  { generalize ETCCOH.(etc_S_in_E). generalize (reservedW WF ETCCOH). basic_solver. }

  assert (~ issued T w) as NIW.
  { intros II. apply NSW. by apply ETCCOH.(etc_I_in_S). }

  set (f_to':= upd f_to w n_to).
  set (f_from':= upd f_from w n_from).

  assert (S wnext /\ co w wnext) as [ISSNEXT CONEXT].
  { destruct NIMMCO as [AA _]. by destruct_seq_r AA as BB. }
  assert (E wnext) as ENEXT.
  { by apply ETCCOH.(etc_S_in_E). }
  assert (W wnext) as WNEXT.
  { by apply (reservedW WF ETCCOH). }

  assert (S wprev /\ co wprev w) as [ISSPREV COPREV].
  { destruct PIMMCO as [H _]. apply seq_eqv_l in H; desf. }
  assert (E wprev) as EPREV.
  { by apply ETCCOH.(etc_S_in_E). }
  assert (W wprev) as WPREV.
  { by apply (reservedW WF ETCCOH). }

  assert (~ is_init w) as WNINIT.
  { apply no_co_to_init in COPREV; auto. by destruct_seq_r COPREV as AA. }

  assert (~ is_init wnext) as NINITWNEXT.
  { apply no_co_to_init in CONEXT; auto.
    apply seq_eqv_r in CONEXT. desf. }

  assert (co wprev wnext) as COPN.
  { eapply WF.(co_trans); eauto. }

  assert (Time.lt (f_to wprev) (f_from wnext)) as NPLT.
  { assert (Time.le (f_to wprev) (f_from wnext)) as H.
    { apply FCOH; auto. }
    apply Time.le_lteq in H. destruct H as [|H]; [done|exfalso].
    apply TFRMW in H; auto.
    eapply rfrmw_in_im_co in H; eauto.
      by eapply H; [apply COPREV|]. }
  
  assert (Time.le n_from (Time.middle (f_to wprev) (f_from wnext))) as LEFROMTO1.
  { desf; try reflexivity.
    all: apply Time.le_lteq; left.
    all: repeat (apply Time.middle_spec; auto). }

  assert (Time.lt (f_to wprev) n_to) as LTPREVTO.
  { desf; by apply Time.middle_spec. }

  assert (Time.le (f_to wprev) n_from) as PREVFROMLE.
  { destruct NFROM as [[N1 N2]|[N1 N2]]; subst; [reflexivity|].
    apply Time.le_lteq; left. by apply Time.middle_spec. }

  assert (Time.lt n_from n_to) as LTFROMTO.
  { desf.
    { by apply Time.middle_spec. }
    eapply TimeFacts.lt_le_lt.
    2: reflexivity.
      by do 2 apply Time.middle_spec. }

  assert (Time.le (Time.middle (f_to wprev) (f_from wnext)) n_to) as LETO1.
  { desf; try reflexivity.
    all: by apply Time.le_lteq; left; apply Time.middle_spec. }

  assert (Time.le n_to (f_from wnext)) as LETONEXT.
  { desf; try reflexivity.
    all: by apply Time.le_lteq; left; apply Time.middle_spec. }
  
  cdes RESERVED_TIME. red.
  destruct smode; desc; unnw.
  2: { split.
       { rewrite <- FOR_SPLIT. basic_solver. }
       rewrite RMW_BEF_S. basic_solver 10. }

  (* TODO: Extract to a separate lemma. *)
  assert (half_message_to_event G T (S ∪₁ eq w) f_to' f_from' memory') as HMTE.
  { red; ins. erewrite Memory.add_o in MSG; eauto.
    destruct (loc_ts_eq_dec (l0, to) (l, f_to' w)) as [[EQ1 EQ2]|NEQ].
    { simpls; subst.
      rewrite (loc_ts_eq_dec_eq l (f_to' w)) in MSG.
      inv MSG.
      clear MSG. exists w. splits; auto. by right. }
    rewrite loc_ts_eq_dec_neq in MSG; simpls; auto.
    apply HMEM in MSG. desc.
    assert (b <> w) as BNEQ.
    { intros H; subst. by apply NSW. }
    exists b.
    splits; eauto.
    { by left. }
    1,2: by unfold f_from', f_to'; rewrite updo. }
  splits; auto.
  { eapply message_to_event_add_S; eauto. }
  unfold f_to', f_from'.
  intros x y [SX|] [SY|] CO FT; subst.
  4: { exfalso. eapply co_irr; eauto. }
  { rewrite updo in FT; [|by intros AA; desf].
    rewrite updo in FT; [|by intros AA; desf].
      by apply TFRMW0. }
  all: destruct (classic (x = y)) as [|NEQ]; [by desf|].
  { rewrite updo in FT; auto.
    rewrite upds in FT.
    assert (same_loc lab x wprev) as LXPREV.
    { etransitivity.
      { apply WF.(wf_col); eauto. }
      symmetry. by apply WF.(wf_col). }
    destruct NFROM as [[NFROM BB]|[NFROM BB]]; unnw.
    { desc; subst.
      eapply f_to_eq with (I:=S) in FT; eauto; subst; desc.
      subst. apply BB. }
    exfalso.
    assert (E x) as EX by (by apply ETCCOH.(etc_S_in_E)).
    assert (W x) as WX by (by apply (reservedW WF ETCCOH)).
    edestruct WF.(wf_co_total) with (a:=x) (b:=wprev) as [COWX|COWX].
    1-2: split; [split|]; eauto.
    { intros H; subst.
      eapply Time.lt_strorder with (x:=f_to wprev).
      rewrite FT at 2. by apply Time.middle_spec. }
    { subst.
      assert (Time.lt (f_to x) (f_to wprev)) as DD.
      { eapply f_to_co_mon; eauto. }
      eapply Time.lt_strorder with (x:=f_to x).
      rewrite FT at 2.
      etransitivity; [by apply DD|]. by apply Time.middle_spec. }
    eapply PIMMCO.
    all: apply seq_eqv_l; split; eauto. }
  rewrite upds in FT; auto.
  rewrite updo in FT; auto.
  assert (same_loc lab wnext y) as LXPREV.
  { etransitivity.
    { symmetry. apply WF.(wf_col). apply CONEXT. }
    apply WF.(wf_col); eauto. }
  assert (~ is_init y) as NINITY.
  { apply no_co_to_init in CO; auto. by destruct_seq_r CO as BB. }
  destruct NTO as [[NTO BB]|[NTO BB]]; unnw.
  { desc; subst.
    eapply f_from_eq with (I:=S) in FT; eauto; subst; desc.
    subst. apply BB. }
  exfalso.
  assert (E y) as EY by (by apply ETCCOH.(etc_S_in_E)).
  assert (W y) as WY by (by apply (reservedW WF ETCCOH)).
  edestruct WF.(wf_co_total) with (a:=wnext) (b:=y) as [COWY|COWY].
  1-2: split; [split|]; eauto.
  { intros H; subst.
    eapply Time.lt_strorder with (x:=f_from y).
    rewrite <- FT at 1. by apply Time.middle_spec. }
  { subst.
    assert (Time.lt (f_from wnext) (f_from y)) as DD.
    { eapply f_from_co_mon; eauto. }
    eapply Time.lt_strorder with (x:=f_from y).
    rewrite <- FT at 1.
    etransitivity; [|by apply DD]. by apply Time.middle_spec. }
  eapply NIMMCO with (c:=y).
  all: apply seq_eqv_r; split; auto.
Qed.

(* TODO: move to a more appropriate place. *)
Lemma reserved_time_add_S_after smode locw memory memory' local w wprev n_from
      (SIM_MEM : sim_mem G sc T f_to f_from
                         (tid w) local memory)
      (SIM_RES_MEM : sim_res_mem G T S f_to f_from (tid w) local memory)
      (TFRMW : forall x y (SX : S x) (SY : S y) (CO : co x y)
                      (FTOFROM : f_to x = f_from y),
          (rf ⨾ rmw) x y)
      (WLOC : loc lab w = Some locw)
      (NSW : ~ S w)
      (NCO : ~ exists wnext, (co ⨾ ⦗S⦘) w wnext)
      (PIMMCO : immediate (⦗S⦘ ⨾ co) wprev w)
      (NFROM  : (n_from = Memory.max_ts locw memory /\
                 ⟪ PRFRMW : (rf ⨾ rmw) wprev w ⟫) \/
                (n_from = Time.incr (Memory.max_ts locw memory) /\
                 ⟪ NPRFRMW : ~ (rf ⨾ rmw) wprev w ⟫))
      (RESERVED_TIME:
         reserved_time G T S f_to f_from smode memory)
      (MADD :
        Memory.add memory locw
                   ((upd f_from w n_from) w)
                   ((upd f_to w (Time.incr (Time.incr (Memory.max_ts locw memory)))) w)
                   Message.reserve memory') :     
  reserved_time
    G T (S ∪₁ eq w) (upd f_to w (Time.incr (Time.incr (Memory.max_ts locw memory))))
    (upd f_from w n_from)
    smode memory'.
Proof using WF IMMCON ETCCOH FCOH.
  assert (sc_per_loc G) as SPL.
  { apply coherence_sc_per_loc. apply IMMCON. }

  assert (S ⊆₁ E ∩₁ W) as SEW.
  { generalize ETCCOH.(etc_S_in_E). generalize (reservedW WF ETCCOH). basic_solver. }

  assert (~ issued T w) as NIW.
  { intros II. apply NSW. by apply ETCCOH.(etc_I_in_S). }

  set (f_to':= upd f_to w (Time.incr (Time.incr (Memory.max_ts locw memory)))).
  set (f_from':= upd f_from w n_from).

  assert (S wprev /\ co wprev w) as [ISSPREV COPREV].
  { destruct PIMMCO as [H _]. apply seq_eqv_l in H; desf. }
  assert (E wprev) as EPREV.
  { by apply ETCCOH.(etc_S_in_E). }
  assert (W wprev) as WPREV.
  { by apply (reservedW WF ETCCOH). }

  assert (~ is_init w) as WNINIT.
  { apply no_co_to_init in COPREV; auto. by destruct_seq_r COPREV as AA. }
  
  assert (E w) as EW.
  { apply WF.(wf_coE) in COPREV. by destruct_seq COPREV as [AA BB]. }

  (* assert (Time.lt (f_to wprev) n_to) as LTPREVTO. *)
  (* { desf; by apply Time.middle_spec. } *)

  (* assert (Time.le (f_to wprev) n_from) as PREVFROMLE. *)
  (* { destruct NFROM as [[N1 N2]|[N1 N2]]; subst; [reflexivity|]. *)
  (*   apply Time.le_lteq; left. by apply Time.middle_spec. } *)

  (* assert (Time.lt n_from n_to) as LTFROMTO. *)
  (* { desf. *)
  (*   { by apply Time.middle_spec. } *)
  (*   eapply TimeFacts.lt_le_lt. *)
  (*   2: reflexivity. *)
  (*     by do 2 apply Time.middle_spec. } *)

  (* assert (Time.le (Time.middle (f_to wprev) (f_from wnext)) n_to) as LETO1. *)
  (* { desf; try reflexivity. *)
  (*   all: by apply Time.le_lteq; left; apply Time.middle_spec. } *)

  (* assert (Time.le n_to (f_from wnext)) as LETONEXT. *)
  (* { desf; try reflexivity. *)
  (*   all: by apply Time.le_lteq; left; apply Time.middle_spec. } *)
  
  cdes RESERVED_TIME. red.
  destruct smode; desc; unnw.
  2: { split.
       { rewrite <- FOR_SPLIT. basic_solver. }
       rewrite RMW_BEF_S. basic_solver 10. }

  (* TODO: Extract to a separate lemma. *)
  assert (half_message_to_event G T (S ∪₁ eq w) f_to' f_from' memory') as HMTE.
  { red; ins. erewrite Memory.add_o in MSG; eauto.
    destruct (loc_ts_eq_dec (l, to) (locw, f_to' w)) as [[EQ1 EQ2]|NEQ].
    { simpls; subst.
      rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in MSG.
      inv MSG.
      clear MSG. exists w. splits; auto. by right. }
    rewrite loc_ts_eq_dec_neq in MSG; simpls; auto.
    apply HMEM in MSG. desc.
    assert (b <> w) as BNEQ.
    { intros H; subst. by apply NSW. }
    exists b.
    splits; eauto.
    { by left. }
    1,2: by unfold f_from', f_to'; rewrite updo. }
  splits; auto.
  { eapply message_to_event_add_S; eauto. }
  unfold f_to', f_from'.
  intros x y [SX|] [SY|] CO FT; subst.
  4: { exfalso. eapply co_irr; eauto. }
  { rewrite updo in FT; [|by intros AA; desf].
    rewrite updo in FT; [|by intros AA; desf].
      by apply TFRMW0. }
  all: destruct (classic (x = y)) as [|NEQ]; [by desf|].
  { rewrite updo in FT; auto.
    rewrite upds in FT.
    assert (same_loc lab x wprev) as LXPREV.
    { etransitivity.
      { apply WF.(wf_col); eauto. }
      symmetry. by apply WF.(wf_col). }
    destruct NFROM as [[NFROM BB]|[NFROM BB]]; unnw.
    { desc; subst.
      assert (f_to x = f_to wprev) as FF.
      2: { eapply f_to_eq with (I:=S) in FF; eauto; desf. }
      rewrite FT. symmetry.
      eapply no_next_S_max_ts; eauto. }
    exfalso. eapply Time.lt_strorder.
    eapply TimeFacts.le_lt_lt.
    2: by apply DenseOrder.incr_spec.
    subst. rewrite <- FT.
    eapply S_le_max_ts; eauto.
    rewrite <- WLOC. by apply WF.(wf_col). }
  rewrite upds in FT.
  rewrite updo in FT; auto.
  exfalso. eapply Time.lt_strorder.
  etransitivity; [|by apply DenseOrder.incr_spec].
  etransitivity; [|by apply DenseOrder.incr_spec].
  rewrite FT.
  eapply TimeFacts.lt_le_lt.
  2: { eapply S_le_max_ts with (x:=y); eauto.
       rewrite <- WLOC. symmetry. by apply WF.(wf_col). }
  apply FCOH; auto.
  apply no_co_to_init in CO; auto. by destruct_seq_r CO as AA.
Qed.

Lemma exists_time_interval PC w locw valw langst local smode
      (TSTEP : ext_itrav_step
                 G sc w (mkETC T S) (mkETC T (S ∪₁ eq w)))
      (PRMW : ~ codom_rel (⦗S \₁ issued T⦘ ⨾ rfi ⨾ rmw) w)
      (LOC : loc lab w = Some locw)
      (VAL : val lab w = Some valw)
      (PROM_IN_MEM :
         forall thread' langst local
                (TID : IdentMap.find thread' PC.(Configuration.threads) =
                       Some (langst, local)),
           Memory.le local.(Local.promises) PC.(Configuration.memory))
      (RESERVED_TIME:
         reserved_time G T S f_to f_from smode PC.(Configuration.memory))
      (INHAB      : Memory.inhabited (Configuration.memory PC))
      (CLOSED_MEM : Memory.closed (Configuration.memory PC))
      (SIM_RES_MEM :
         sim_res_mem G T S f_to f_from (tid w) local (Configuration.memory PC))
      (SIM_MEM : sim_mem G sc T f_to f_from
                         (tid w) local PC.(Configuration.memory))
      (SIM_TVIEW : sim_tview G sc (covered T) f_to local.(Local.tview) (tid w))
      (PLN_RLX_EQ : pln_rlx_eq local.(Local.tview))
      (MEM_CLOSE : memory_close local.(Local.tview) PC.(Configuration.memory))
      (TID : IdentMap.find (tid w) PC.(Configuration.threads) = Some (langst, local)) :
  let memory := PC.(Configuration.memory) in
  exists f_to' f_from' promises' memory',
    ⟪ PADD :
        Memory.add local.(Local.promises) locw (f_from' w) (f_to' w)
                                          Message.reserve promises' ⟫ /\
    ⟪ MADD :
        Memory.add memory locw (f_from' w) (f_to' w)
                   Message.reserve memory' ⟫ /\
    
    ⟪ REQ_TO   : forall e (SE: S e), f_to'   e = f_to   e ⟫ /\
    ⟪ REQ_FROM : forall e (SE: S e), f_from' e = f_from e ⟫ /\
    ⟪ FCOH : f_to_coherent G (S ∪₁ eq w) f_to' f_from' ⟫ /\
    ⟪ RESERVED_TIME :
        reserved_time G T (S ∪₁ eq w) f_to' f_from' smode memory' ⟫.
Proof using WF IMMCON ETCCOH RELCOV FCOH.
  assert (tc_coherent G sc T) as TCCOH by apply ETCCOH.
  assert (etc_coherent G sc (mkETC T (S ∪₁ eq w))) as ETCCOH' by apply TSTEP.

  assert (W w) as WW.
  { eapply ext_itrav_step_reserveW with (T := mkETC T S); eauto. }

  assert (E w) as EW.
  { eapply ext_itrav_stepE with (T := mkETC T S); eauto. }
  
  assert (~ covered T w) as WNCOV.
  { eapply ext_itrav_step_nC with (T := mkETC T S); eauto. }

  assert (~ S w) as NSW.
  { eapply ext_itrav_step_reserve_nS with (T := mkETC T S); eauto. }

  assert (~ issued T w) as WNISS.
  { intros AA. apply NSW. by apply ETCCOH.(etc_I_in_S). }

  assert (~ is_init w) as WNINIT.
  { eapply ext_itrav_step_ninit with (T := mkETC T S); eauto. }

  assert (W_ex w) as WEXW.
  { apply ETCCOH'. unfold eissued. split; simpls. basic_solver. }

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
    eapply ETCCOH.(etc_sb_S). red. simpls.
    split.
    { basic_solver 10. }
    eapply ETCCOH'.(etc_S_W_ex_rfrmw_I). split; auto.
    basic_solver. }

  destruct langst as [lang state].

  destruct (classic (exists wnext, (co ⨾ ⦗ S ⦘) w wnext)) as [WNEXT|WNONEXT].
  { assert (exists wnext, immediate (co ⨾ ⦗ S ⦘) w wnext) as [wnext NIMMCO].
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

    assert (exists wprev, immediate (⦗ S ⦘ ⨾ co) wprev w) as [wprev PIMMCO].
    { assert ((⦗ S ⦘ ⨾ co) (InitEvent locw) w) as WPREV.
      { assert (W (InitEvent locw)) as WI.
        { by apply init_w. }
        assert (E (InitEvent locw)) as EI.
        { apply wf_init; auto.
            by exists w; split. }
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
    { destruct PIMMCO as [H _]. apply seq_eqv_l in H; desf. }
    assert (E wprev) as EPREV.
    { by apply ETCCOH.(etc_S_in_E). }
    assert (W wprev) as WPREV.
    { by apply (reservedW WF ETCCOH). }

    assert (wnext <> w) as NEQNEXT.
    { intros H; subst. by apply WF.(co_irr) in CONEXT. }
    assert (wprev <> w) as NEQPREV.
    { intros H; subst. by apply WF.(co_irr) in COPREV. }

    assert (loc lab wprev = Some locw) as PLOC.
    { rewrite <- LOC. by apply WF.(wf_col). }
    
    assert ((co ⨾ ⦗set_compl S⦘ ⨾ co) wprev wnext) as CONS.
    { exists w. split; auto. apply seq_eqv_l. by split. }

    assert (co wprev wnext) as COPN.
    { eapply WF.(co_trans); eauto. }

    assert (immediate (⦗S⦘ ⨾ co ⨾ ⦗S⦘) wprev wnext) as COSIMM.
    { admit. }
      (* apply S_co_nS_co_S_imm. *)
      (* { apply ETCCOH. } *)
      (* { apply (reservedW WF ETCCOH). } *)
      (* exists w. split; auto. apply seq_eqv_l. by split. } *)

    (* assert (forall z (RFRMW : (⦗ issued T ⦘ ⨾ rf ⨾ rmw) z w), z = wprev) as PRFRMW. *)
    (* { ins. apply seq_eqv_l in RFRMW; destruct RFRMW as [ISSZ RFRMW]. *)
    (*   eapply rfrmw_in_im_co in RFRMW; eauto. destruct RFRMW as [CO IMM]. *)
    (*   destruct (classic (z = wprev)) as [|NEQ]; auto. *)
    (*   exfalso. *)
    (*   edestruct WF.(wf_co_total). *)
    (*   3: by apply NEQ. *)
    (*   1,2: split; [split|]; eauto. *)
    (*   1,2: by apply TCCOH in ISSZ; apply ISSZ. *)
    (*   { erewrite (WF.(wf_col) z w); [|by apply CO]. *)
    (*       by rewrite LOC. } *)
    (*   { by apply (IMM wprev). } *)
    (*   eapply PIMMCO. all: apply seq_eqv_l; eauto. } *)
    cdes RESERVED_TIME. desc.
    assert (~ (rf ⨾ rmw) w wnext) as NRFRMWNEXT.
    { intros AA. apply NSW. eapply (dom_rf_rmw_S WF ETCCOH).
      exists wnext. apply seq_eqv_l. split; auto.
      apply seqA. apply seq_eqv_r. by split. }
    
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

    edestruct (@Memory.add_exists PC.(Configuration.memory) locw (f_from' w) (f_to' w) Message.reserve)
      as [memory' MADD].
    3: by apply Message.wf_reserve.
    { apply DISJOINT. }
    { unfold f_from', f_to'. rewrite !upds.
      eapply f_to_coherent_add_S_middle; eauto. }
    
    assert (f_to_coherent G (S ∪₁ eq w) f_to' f_from') as FCOH_NEW.
    { unfold f_to', f_from'.
      eapply f_to_coherent_add_S_middle; eauto. }

    assert (reserved_time
              G T (S ∪₁ eq w) (upd f_to w n_to) (upd f_from w n_from)
              sim_normal memory') as RST.
    { eapply reserved_time_add_S_middle; eauto. }
    
    do 2 eexists. splits; eauto.
    all: admit. }

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
  { admit. }
  assert (S wprev) as SWPREV by (by apply ETCCOH.(etc_I_in_S)).
  assert (immediate (⦗S⦘ ⨾ co) wprev w) as PIMMCO.
  { admit. }
  
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
  all: admit.
Admitted.

End Aux.
