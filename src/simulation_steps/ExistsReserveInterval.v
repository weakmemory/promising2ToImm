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

(* TODO: move to ImmProperties.v. *)
Lemma co_P_co_rfrmw_rt_in_rfrmw_ct_P_rfrmw_ct P :
  (co ;; <|P|> ;; co) ∩ (rf ;; rmw)^* ⊆
  (rf ;; rmw)⁺ ;; <|W_ex ∩₁ P|> ;; (rf ;; rmw)⁺.
Proof using.
Admitted.

(* TODO: move to a more appropriate place. *)
Lemma co_S_memory_disjoint memory locw wp wn
      (COIMM  : immediate (<|S|> ;; co ;; <|S|>) wp wn)
      (CONS   : (co ;; <| set_compl S |> ;; co) wp wn)
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
  set (CC:=RFRMWS).
  destruct_seq CC as [AA BB].
  destruct AA as [SB _].
  destruct BB as [SB' _].
  assert (E b /\ E b') as [EB EB'].
  { by split; apply ETCCOH.(etc_S_in_E). }
  assert (W b /\ W b') as [WB WB'].
  { by split; apply (reservedW WF ETCCOH). }
  assert (loc lab b' = Some locw) as LOC'.
  { unfold location in *. rewrite <- LOC.
    symmetry. 
    eapply inclusion_rt_ind with (r := rf ;; rmw) (r' := same_loc lab); eauto.
    { red. by unfold same_loc. }
    { apply WF.(wf_rfrmwl). }
    apply same_loc_trans. }

  assert (co^? b' wp \/ co^? wn b) as CO.
  { destruct (classic (b' = wp)) as [|PNEQ]; subst.
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
    
    (* TODO: generalize to a lemma? *)
    set (YY:=CONS).
    destruct YY as [w [CONS1 CONS2]].
    destruct_seq_l CONS2 as NSW.
   
    apply (dom_r WF.(wf_coD)) in CONS1. destruct_seq_r CONS1 as WW.
    apply (dom_r WF.(wf_coE)) in CONS1. destruct_seq_r CONS1 as EW.
    assert (loc lab w = Some locw) as WLOC.
    { rewrite <- LOCN. by apply WF.(wf_col). }

    assert (w <> b ) as WBNEQ  by (intros HH; desf).
    assert (w <> b') as WBNEQ' by (intros HH; desf).

    edestruct WF.(wf_co_total) as [|COBW].
    3: by apply WBNEQ.
    1,2: split; [split|]; eauto.
    { apply COIMM with (c:=b).
      all: apply seq_eqv_lr; splits; auto.
      eapply WF.(co_trans); eauto. }

    edestruct WF.(wf_co_total) as [COWB'|PP].
    3: by apply WBNEQ'.
    1,2: split; [split|]; eauto.
    2: { apply COIMM with (c:=b').
         all: apply seq_eqv_lr; splits; auto.
         eapply WF.(co_trans); eauto. }
    
    apply NSW.
    eapply (dom_rf_rmw_ct_S WF ETCCOH). simpls.
    assert (((rf ;; rmw)⁺ ;; <|W_ex ∩₁ eq w|> ;; (rf ;; rmw)⁺) b b') as AA.
    2: { destruct AA as [q [_ AA]].
         generalize AA SB'. basic_solver 10. }
    apply co_P_co_rfrmw_rt_in_rfrmw_ct_P_rfrmw_ct.
    split; auto.
    generalize COBW COWB'.
    basic_solver 10. }

  destruct CO as [CO|CO].
  { assert (Time.le (f_to b') (f_to wp)) as HH.
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
                 << NRFRMW : (rf ⨾ rmw) w wnext >>) \/
                (n_to = Time.middle (f_to wprev) (f_from wnext) /\
                 << NNRFRMW : ~ (rf ⨾ rmw) w wnext >>))
      (NFROM  : (n_from = f_to wprev /\
                 << PRFRMW : (rf ⨾ rmw) wprev w >>) \/
                (n_from = Time.middle (f_to wprev) n_to /\
                 << NPRFRMW : ~ (rf ⨾ rmw) wprev w >>)) :
  f_to_coherent G (S ∪₁ eq w) (upd f_to w n_to) (upd f_from w n_from).
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

(* TODO: move to a more appropriate place. *)
Lemma message_to_event_add_S_middle memory l w memory' n_to n_from
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
Lemma reserved_time_add_S_middle memory local l w wprev wnext memory' n_to n_from
      (SIM_MEM : sim_mem G sc T f_to f_from
                         (tid w) local memory)
      (TFRMW : forall x y (SX : S x) (SY : S y) (CO : co x y)
                      (FTOFROM : f_to x = f_from y),
          (rf ⨾ rmw) x y)
      (LOC : loc lab w = Some l)
      (NSW : ~ S w)
      (PRMW : ~ codom_rel (⦗S \₁ issued T⦘ ⨾ rf ⨾ rmw) w)
      (NIMMCO : immediate (co ⨾ ⦗S⦘) w wnext)
      (PIMMCO : immediate (⦗S⦘ ⨾ co) wprev w)
      (NTO    : (n_to = f_from wnext /\
                 << NRFRMW : (rf ⨾ rmw) w wnext >>) \/
                (n_to = Time.middle (f_to wprev) (f_from wnext) /\
                 << NNRFRMW : ~ (rf ⨾ rmw) w wnext >>))
      (NFROM  : (n_from = f_to wprev /\
                 << PRFRMW : (rf ⨾ rmw) wprev w >>) \/
                (n_from = Time.middle (f_to wprev) n_to /\
                 << NPRFRMW : ~ (rf ⨾ rmw) wprev w >>))
      (RESERVED_TIME:
         reserved_time G T S f_to f_from sim_normal memory)
      (MADD :
        Memory.add memory l
                   ((upd f_from w n_from) w)
                   ((upd f_to w n_to) w)
                   Message.reserve memory') :
  reserved_time
    G T (S ∪₁ eq w) (upd f_to w n_to) (upd f_from w n_from)
    sim_normal memory'.
Proof using WF IMMCON ETCCOH FCOH.
  assert (~ issued T w) as NIW.
  { intros II. apply NSW. by apply ETCCOH.(etc_I_in_S). }

  cdes RESERVED_TIME.
  set (f_to':= upd f_to w n_to).
  set (f_from':= upd f_from w n_from).

  (* TODO: Extract to a separate lemma. *)
  assert (message_to_event G T (upd f_to w n_to) (upd f_from w n_from) memory') as MTE.
  { eapply message_to_event_add_S_middle; eauto. }

  assert (half_message_to_events G T (S ∪₁ eq w) f_to' f_from' memory') as HMTE.
  { red; ins. erewrite Memory.add_o in MSG; eauto.
    destruct (loc_ts_eq_dec (l0, to) (l, f_to' w)) as [[EQ1 EQ2]|NEQ].
    { simpls; subst.
      rewrite (loc_ts_eq_dec_eq l (f_to' w)) in MSG.
      inv MSG.
      clear MSG. exists w, w. splits; auto.
      { apply seq_eqv_lr. splits; [basic_solver| |basic_solver].
        apply rt_refl. }
      1,2: admit. }
    rewrite loc_ts_eq_dec_neq in MSG; simpls; auto.
    apply HMEM in MSG. desc.
    set (CC:=RFRMWS).
    destruct_seq CC as [AA BB].
    assert (b <> w) as BNEQ.
    { intros H; subst. apply NSW. apply AA. }
    assert (b' <> w) as BNEQ'.
    { intros H; subst. apply NSW. apply BB. }
    exists b, b'.
    splits; eauto.
    { apply seq_eqv_lr; splits; auto.
      all: generalize AA BB BNEQ BNEQ'; basic_solver. }
    1,2: by unfold f_from', f_to'; rewrite updo.
    intros [z ZZ]. apply seqA in ZZ. destruct_seq_r ZZ as QQ.
    destruct QQ as [QQ|]; subst.
    { apply NOAFT. exists z. apply seqA. basic_solver. }
    apply PRMW. exists b'. apply seq_eqv_l. split; auto. }

  red. splits; auto.

(* { red. splits. *)
(*     intros x y [ISSX|HX]; subst. *)
(*     { assert (x <> w) as XNEQ. *)
(*       { intros H; desf. } *)
(*       rewrite updo; auto. *)
(*       intros [ISSY|HY] JJ CO II; subst. *)
(*       { assert (y <> w) as YNEQ. *)
(*         { intros H; desf. } *)
(*         rewrite updo in II; auto. } *)
(*       rewrite upds in II. *)
(*       assert (loc lab x = Some locw) as XLOC. *)
(*       { rewrite <- LOC. by apply WF.(wf_col). } *)
(*       destruct NFROM as [[NFROM BB]|[NFROM BB]]. *)
(*       { desc; subst. *)
(*         eapply f_to_eq in II; eauto. *)
(*         { subst. apply BB. } *)
(*         red. by rewrite XLOC. } *)
(*       exfalso. *)
(*       edestruct WF.(wf_co_total) with (a:=x) (b:=wprev) as [COWX|COWX]. *)
(*       1-2: split; [split|]; eauto. *)
(*       1-2: by apply TCCOH in ISSX; apply ISSX. *)
(*       { intros H; subst.  *)
(*         edestruct Time.middle_spec as [AA _]. *)
(*         { apply PREVNLT. } *)
(*         rewrite <- II in AA. *)
(*           by apply Time.lt_strorder in AA. } *)
(*       { subst. *)
(*         edestruct Time.middle_spec as [AA CC]. *)
(*         { apply PREVNLT. } *)
(*         assert (Time.lt (f_to x) (f_to wprev)) as DD. *)
(*         { eapply f_to_co_mon; eauto. } *)
(*         rewrite II in DD. *)
(*         eapply Time.lt_strorder. *)
(*           by etransitivity; [by apply DD|]. } *)
(*       eapply PIMMCO. *)
(*       all: apply seq_eqv_l; split; eauto. } *)
(*     intros [ISSY|HY] JJ CO II; subst. *)
(*     2: by apply WF.(co_irr) in CO. *)
(*     assert (y <> x) as YNEQ. *)
(*     { intros H. desf. } *)
(*     rewrite upds in *; auto. rewrite updo in II; auto. *)
(*     assert (loc lab y = Some locw) as XLOC. *)
(*     { rewrite <- LOC. symmetry. by apply WF.(wf_col). } *)
(*     destruct NTO as [[NTO BB]|[NTO BB]]. *)
(*     { desc; subst. *)
(*       eapply f_from_eq in II; eauto. *)
(*       { subst. apply BB. } *)
(*       red. by rewrite XLOC. } *)
(*     exfalso. *)
(*     edestruct WF.(wf_co_total) with (a:=y) (b:=wnext) as [COWX|COWX]. *)
(*     1-2: split; [split|]; eauto. *)
(*     1-2: by apply TCCOH in ISSY; apply ISSY. *)
(*     { intros H; subst.  *)
(*       edestruct Time.middle_spec as [AA CC]. *)
(*       { apply NPLT. } *)
(*       rewrite II in CC. *)
(*         by apply Time.lt_strorder in CC. } *)
(*     { eapply NIMMCO. *)
(*       all: apply seq_eqv_r; split; eauto. } *)
(*     subst. *)
(*     edestruct Time.middle_spec as [AA CC]. *)
(*     { apply NPLT. } *)
(*     assert (Time.lt (f_from wnext) (f_from y)) as DD. *)
(*     { eapply f_from_co_mon; eauto. } *)
(*     rewrite <- II in DD. *)
(*     eapply Time.lt_strorder. *)
(*       by etransitivity; [by apply DD|]. } *)
Admitted.

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

  assert (smode = sim_normal); subst.
  { destruct smode; simpls. exfalso. apply NSW. apply RESERVED_TIME. apply WEXW. }

  assert ((E ∩₁ W ∩₁ Loc_ locw) w) as WEW.
  { split; [split|]; auto. }

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
    { apply S_co_nS_co_S_imm.
      { apply ETCCOH. }
      { apply (reservedW WF ETCCOH). }
      exists w. split; auto. apply seq_eqv_l. by split. }

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
    red in RESERVED_TIME. desc.
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

    assert (Time.lt (f_to wprev) (f_from wnext)) as NPLT.
    { assert (Time.le (f_to wprev) (f_from wnext)) as H.
      { apply FCOH; auto. }
      apply Time.le_lteq in H. destruct H as [|H]; [done|exfalso].
      apply TFRMW in H; auto.
      eapply rfrmw_in_im_co in H; eauto.
        by eapply H; [apply COPREV|]. }

    assert (Time.lt (f_to wprev) n_to) as PREVNLT.
    { subst n_to. by apply Time.middle_spec. }

    assert (Time.le (f_to wprev) n_from) as PREVFROMLE.
    { destruct NFROM as [[N1 N2]|[N1 N2]]; subst; [reflexivity|].
      apply Time.le_lteq; left. by apply Time.middle_spec. }

    assert (Time.le n_to (f_from wnext)) as TONEXTLE.
    { subst n_to. apply Time.le_lteq; left. by apply Time.middle_spec. }

    assert (Time.lt (f_from' w) (f_to' w)) as NLT.
    { unfold f_to', f_from'; rewrite !upds.
      subst n_to.
      destruct NFROM as [[NFROM1 NFROM2]|[NFROM1 NFROM2]]; subst; auto.
      all: by apply Time.middle_spec. }
    
    assert (Interval.le (n_from, n_to) (f_to wprev, f_from wnext)) as ILE.
    { by constructor. }

    assert (forall to from msg,
               Memory.get locw to (Configuration.memory PC) = Some (from, msg) ->
               Interval.disjoint (f_from' w, f_to' w) (from, to)) as DISJOINT.
    { ins. unfold f_to', f_from'; rewrite !upds.
      apply Interval.le_disjoint with (b:= (f_to wprev,f_from wnext)); auto.
      eapply co_S_memory_disjoint with (S:=S); eauto.
      red. by splits. }

    edestruct (@Memory.add_exists (Local.promises local) locw (f_from' w) (f_to' w) Message.reserve)
      as [promises' PADD].
    3: by apply Message.wf_reserve.
    { ins. eapply DISJOINT.
      eapply PROM_IN_MEM; eauto. }
    { done. }

    edestruct (@Memory.add_exists PC.(Configuration.memory) locw (f_from' w) (f_to' w) Message.reserve)
      as [memory' MADD].
    3: by apply Message.wf_reserve.
    { apply DISJOINT. }
    { done. }
    
    assert (f_to_coherent G (S ∪₁ eq w) f_to' f_from') as FCOH_NEW.
    { unfold f_to', f_from'.
      eapply f_to_coherent_add_S_middle; eauto. }

    (* TODO: continue from here. *)
    assert (reserved_time
              G T (S ∪₁ eq w) (upd f_to w n_to) (upd f_from w n_from)
              sim_normal memory') as RST.
    { red.
admit. }
(* { red. splits. *)
(*     { red; ins. erewrite Memory.add_o in MSG; eauto. *)
(*       destruct (loc_ts_eq_dec (l, to) (locw, f_to' w)) as [[EQ1 EQ2]|NEQ]. *)
(*       { simpls; subst. *)
(*         rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in MSG. *)
(*         inv MSG. clear MSG. right. *)
(*         exists w; splits; auto. *)
(*           by right. } *)
(*       rewrite loc_ts_eq_dec_neq in MSG; simpls; auto. *)
(*       apply MEM in MSG. destruct MSG as [MSG|MSG]; [by left|right]. *)
(*       destruct MSG as [b H]; desc. *)
(*       assert (b <> w) as BNEQ. *)
(*       { by intros H; subst. } *)
(*       exists b; splits; auto. *)
(*       { by left. } *)
(*       all: by rewrite updo. } *)
(*     intros x y [ISSX|HX]; subst. *)
(*     { assert (x <> w) as XNEQ. *)
(*       { intros H; desf. } *)
(*       rewrite updo; auto. *)
(*       intros [ISSY|HY] JJ CO II; subst. *)
(*       { assert (y <> w) as YNEQ. *)
(*         { intros H; desf. } *)
(*         rewrite updo in II; auto. } *)
(*       rewrite upds in II. *)
(*       assert (loc lab x = Some locw) as XLOC. *)
(*       { rewrite <- LOC. by apply WF.(wf_col). } *)
(*       destruct NFROM as [[NFROM BB]|[NFROM BB]]. *)
(*       { desc; subst. *)
(*         eapply f_to_eq in II; eauto. *)
(*         { subst. apply BB. } *)
(*         red. by rewrite XLOC. } *)
(*       exfalso. *)
(*       edestruct WF.(wf_co_total) with (a:=x) (b:=wprev) as [COWX|COWX]. *)
(*       1-2: split; [split|]; eauto. *)
(*       1-2: by apply TCCOH in ISSX; apply ISSX. *)
(*       { intros H; subst.  *)
(*         edestruct Time.middle_spec as [AA _]. *)
(*         { apply PREVNLT. } *)
(*         rewrite <- II in AA. *)
(*           by apply Time.lt_strorder in AA. } *)
(*       { subst. *)
(*         edestruct Time.middle_spec as [AA CC]. *)
(*         { apply PREVNLT. } *)
(*         assert (Time.lt (f_to x) (f_to wprev)) as DD. *)
(*         { eapply f_to_co_mon; eauto. } *)
(*         rewrite II in DD. *)
(*         eapply Time.lt_strorder. *)
(*           by etransitivity; [by apply DD|]. } *)
(*       eapply PIMMCO. *)
(*       all: apply seq_eqv_l; split; eauto. } *)
(*     intros [ISSY|HY] JJ CO II; subst. *)
(*     2: by apply WF.(co_irr) in CO. *)
(*     assert (y <> x) as YNEQ. *)
(*     { intros H. desf. } *)
(*     rewrite upds in *; auto. rewrite updo in II; auto. *)
(*     assert (loc lab y = Some locw) as XLOC. *)
(*     { rewrite <- LOC. symmetry. by apply WF.(wf_col). } *)
(*     destruct NTO as [[NTO BB]|[NTO BB]]. *)
(*     { desc; subst. *)
(*       eapply f_from_eq in II; eauto. *)
(*       { subst. apply BB. } *)
(*       red. by rewrite XLOC. } *)
(*     exfalso. *)
(*     edestruct WF.(wf_co_total) with (a:=y) (b:=wnext) as [COWX|COWX]. *)
(*     1-2: split; [split|]; eauto. *)
(*     1-2: by apply TCCOH in ISSY; apply ISSY. *)
(*     { intros H; subst.  *)
(*       edestruct Time.middle_spec as [AA CC]. *)
(*       { apply NPLT. } *)
(*       rewrite II in CC. *)
(*         by apply Time.lt_strorder in CC. } *)
(*     { eapply NIMMCO. *)
(*       all: apply seq_eqv_r; split; eauto. } *)
(*     subst. *)
(*     edestruct Time.middle_spec as [AA CC]. *)
(*     { apply NPLT. } *)
(*     assert (Time.lt (f_from wnext) (f_from y)) as DD. *)
(*     { eapply f_from_co_mon; eauto. } *)
(*     rewrite <- II in DD. *)
(*     eapply Time.lt_strorder. *)
(*       by etransitivity; [by apply DD|]. } *)

    exists promises'; exists memory'; splits; eauto; unfold f_to', f_from'.
    all: by ins; rewrite updo; auto; intros H; subst. }

  left. (* ISSUING *)
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

  edestruct (@Memory.add_exists (Local.promises local) locw (f_from' w) (f_to' w) valw)
    as [promises' PADD].
  3: by apply View.opt_wf_some; apply REL_WF_1.
  { ins. eapply DISJOINT.
    eapply PROM_IN_MEM; eauto. }
  { done. }

  edestruct (@Memory.add_exists PC.(Configuration.memory) locw (f_from' w) (f_to' w) valw)
    as [memory' MADD].
  3: by apply View.opt_wf_some; apply REL_WF_1.
  { apply DISJOINT. }
  { done. }

  assert
  (f_to_coherent G (issued T ∪₁ eq w)
    (upd f_to w (Time.incr (Time.incr (Memory.max_ts locw (Configuration.memory PC)))))
    (upd f_from w n_from)) as N_FCOH.
  { red; splits.
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
      { (* TODO: generalize to lemma! *)
        apply (wf_coD WF) in CO.
        apply seq_eqv_l in CO; destruct CO as [WX CO].
        apply seq_eqv_r in CO; destruct CO as [CO WY].
        unfold is_w in WX; destruct (lab x) eqn:LAB; desc; try by desf.
        edestruct SIM_MEM.
        3,4: by unfold loc, val; rewrite LAB; eauto.
        { apply (wf_coE WF) in CO.
          apply seq_eqv_l in CO; desf. }
        all: eauto.
        desc.
        apply (wf_col WF) in CO; red in CO; unfold loc in *; desf.
        all: etransitivity; [by eapply Memory.max_ts_spec; eauto|].
        all: by apply LENFROM_R. }
      { exfalso. eapply WNONEXT. eexists; apply seq_eqv_r; eauto. }
      exfalso. by apply co_irr in CO. }
    intros x y [ISSX|EQX] [ISSY|EQY] RFRMW; subst.
    all: try rewrite !upds.
    all: try rewrite !updo.
    all: try by intros H; subst.
    { by apply FCOH. }
    { destruct NFROM as [[EQ [wprev HH]]|[EQ NWPREV]]; subst.
      2: by exfalso; apply NWPREV; eexists; split; eauto.
      red in RESERVED_TIME. destruct smode; desc.
      2: { exfalso. apply WNISS. apply RMW_ISSUED.
           destruct RFRMW as [z [RF RMW]].
             by exists z. }
      assert (wprev = x); [|subst].
      eapply wf_rfrmwf; eauto.
      destruct (classic (f_to x = ts)) as [|NEQ]; [done|exfalso].
      unfold ts in *.
      assert (E x) as EX.
      { hahn_rewrite (dom_l (wf_rfE WF)) in RFRMW; revert RFRMW; basic_solver. }
      assert (co x y) as COXY.
      { apply rf_rmw_in_co; cdes IMMCON; eauto using coherence_sc_per_loc. }
      assert (Loc_ locw x) as LOCX.
      { hahn_rewrite (wf_col WF) in COXY; unfold same_loc in COXY; congruence. }
      assert (exists valx, val lab x = Some valx) as [valx VALX].
      { apply is_w_val. hahn_rewrite (dom_l (wf_coD WF)) in COXY; revert COXY; basic_solver. }
      edestruct SIM_MEM as [xrel].
      2: by apply ISSX.
      by eauto.
      by apply LOCX.
      by eauto.
      destruct H as [INMEM H'']; desc.
      edestruct Memory.max_ts_spec as [[from [val [rel HMEM]]] TS].
      { apply INMEM. }
      red in TS. apply Time.le_lteq in TS; destruct TS as [TS|]; [clear NEQ|by subst].
      apply MEM in HMEM. destruct HMEM as [[H1 H2]|HMEM].
      { rewrite H1 in TS. by apply time_lt_bot in TS. }
      destruct HMEM as [wmax H]; desc. rewrite <- TO in TS.
      assert (wmax <> y) as WWNEQ.
      { intros H; desf. }
      assert ((E ∩₁ W ∩₁ (fun x0 => loc lab x0 = Some locw)) wmax) as WWM.
      { split; [split|]; eauto. by apply TCCOH. }
      assert ((E ∩₁ W ∩₁ (fun x0 => loc lab x0 = Some locw)) x) as WXX.
      { split; [split|]; eauto. by apply TCCOH. }
      assert (co wmax y) as COWY.
      { edestruct WF.(wf_co_total).
        3: by apply WWNEQ.
        1-3: by eauto.
        exfalso. apply WNONEXT; eexists; apply seq_eqv_r; eauto. }
      assert (wmax <> x) as WXNEQ.
      { intros H; subst. eapply Time.lt_strorder; eauto. }
      assert (co x wmax) as COXW.
      { edestruct WF.(wf_co_total).
        3: by apply WXNEQ.
        1-2,4: by eauto.
        exfalso. eapply Time.lt_strorder; etransitivity. apply TS.
        eapply f_to_co_mon; eauto. }
      eapply rfrmw_in_im_co; eauto. }
    all: exfalso; eapply rfrmw_in_im_co in RFRMW; eauto.
    { eapply WNONEXT. eexists; apply seq_eqv_r; split; eauto.
      apply RFRMW. }
    eapply WF.(co_irr). apply RFRMW. }

  assert (forall z (ISSZ : issued T z) (LOCZ : loc lab z = Some locw),
             Time.le (f_to z) ts) as YY.
  { ins.
    red in SIM_MEM.
    assert (E z) as EZ.
    { apply TCCOH in ISSZ. apply ISSZ. }
    assert (W z) as WZ.
    { apply TCCOH in ISSZ. apply ISSZ. }
    destruct (is_w_val lab z WZ) as [vz VALZ].
    edestruct SIM_MEM with (b:=z) as [p_rel']; eauto.
    desc.
    apply Memory.max_ts_spec in INMEM.
    destruct INMEM as [_ LE].
    apply LE. }

  assert (forall z (ISSZ : issued T z) (LOCZ : loc lab z = Some locw),
             ~ Time.lt ts (f_to z) ) as XX.
  { ins. intros LL.
    eapply Time.lt_strorder.
    eapply TimeFacts.le_lt_lt; [|apply LL].
      by apply YY. }

  set (rel'' := if Rel w
                then TView.cur (Local.tview local)
                else TView.rel (Local.tview local) locw).

  assert (Time.le (View.rlx rel'' locw)
                  (View.rlx (TView.cur (Local.tview local)) locw)) as GG.
  { unfold rel''. destruct (Rel w).
    { reflexivity. }
    eapply rel_le_cur; eauto. }

  assert (Time.lt (View.rlx rel'' locw)
                  (Time.incr (Time.incr (Memory.max_ts locw (Configuration.memory PC)))))
    as INCRLT.
  { eapply TimeFacts.le_lt_lt; [by apply GG|].
    cdes SIM_TVIEW. specialize (CUR locw). cdes CUR.
    destruct MAX as [[Y1 Y2]|[a_max Y1]].
    { unfold LocFun.find in *.
      rewrite Y2. eapply TimeFacts.le_lt_lt.
      { apply Time.bot_spec. }
      apply Time.incr_spec. }
    desc.
    destruct INam as [z INam].
    red in INam. hahn_rewrite seq_eqvC in INam.
    hahn_rewrite <- seqA in INam.
    apply seq_eqv_r in INam. destruct INam as [INam TINIT].
    assert (ISSA := INam). apply urr_covered in ISSA; auto.
    apply seq_eqv_l in ISSA. destruct ISSA as [ISSA _].
    apply seq_eqv_r in INam. destruct INam as [INam COVA].
    eapply TimeFacts.le_lt_lt; eauto.
    eapply TimeFacts.le_lt_lt.
    2: by apply Time.incr_spec.
    apply Time.le_lteq. left.
    eapply TimeFacts.le_lt_lt.
    2: by apply Time.incr_spec.
    apply wf_urrD in INam.
    apply seq_eqv_l in INam. destruct INam as [[WA LOCA] URR].
    assert (exists aval, val lab a_max = Some aval) as [aval AVAL].
    { unfold val. type_solver. }
    edestruct SIM_MEM with (b:=a_max) as [rel]; eauto.
    eapply issuedE; eauto. }

  exists promises'; exists memory'; splits; eauto; unfold f_to', f_from', ts.
  3,4: by ins; rewrite updo; auto; intros H; subst.
  { rewrite upds; auto. }
  { rewrite upds; auto.
    cdes SIM_TVIEW. clear ACQ REL.
    specialize (CUR locw).
    unfold LocFun.find in *.
    unfold rel'. apply Time.join_spec.
    2: { simpls. unfold TimeMap.singleton, LocFun.add.
         rewrite Loc.eq_dec_eq. unfold f_to', ts.
         rewrite upds. apply DenseOrder_le_PreOrder. }
    apply Time.join_spec.
    { apply Time.le_lteq. by left. }
    destruct PREL0 as [PP|PP]; desc.
    { rewrite PREL. apply Time.bot_spec. }
    specialize (P_MSG locw).
    cdes P_MSG.
    destruct MAX as [[Y1 Y2]|[a_max Y1]].
    { unfold LocFun.find in *. rewrite Y2.
      apply Time.bot_spec. }
    desc.
    destruct INam as [MSG|[U1 U2]].
    2: { subst. etransitivity; eauto.
         etransitivity; [by apply YY|].
         apply Time.le_lteq. left.
         etransitivity; apply Time.incr_spec. }
    etransitivity; eauto.
    etransitivity.
    2: { apply Time.le_lteq. left.
         etransitivity; apply Time.incr_spec. }
    apply YY.
    { eapply msg_rel_issued; eauto.
      exists p. apply seq_eqv_r. split; eauto. }
    destruct MSG as [z [URR _]].
    red in URR. apply seq_eqv_l in URR.
    apply URR. }
  { red. red in RESERVED_TIME. destruct smode; desc; [|splits]; auto.
    2-3: etransitivity; eauto; basic_solver.
    splits.
    { red; ins. erewrite Memory.add_o in MSG; eauto.
      destruct (loc_ts_eq_dec (l, to) (locw, f_to' w)) as [[EQ1 EQ2]|NEQ]; simpls; subst.
      { rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in MSG. inv MSG. clear MSG.
        right. exists w; splits; auto.
          by right. }
      rewrite (loc_ts_eq_dec_neq NEQ) in MSG.
      apply MEM in MSG. destruct MSG as [MSG|MSG]; [by left|right].
      destruct MSG as [b MSG]; desc.
      exists b. assert (b <> w) as BWNEQ; [by intros SS; desf|].
      unnw. rewrite !updo; auto.
      splits; auto.
        by left. }
    intros x y [ISSX|EQX] [ISSY|EQY] NINIT CO; subst.
    all: try rewrite !upds.
    all: try rewrite !updo; auto.
    all: try by intros H; subst.
    3: by apply WF.(co_irr) in CO.
    { intros KK. 
      destruct NFROM as [[NN1 NN2]|[NN1 NN2]].
      { subst. red in NN2. desc.
        destruct (classic (wprev = x)) as [|NEQ]; [by subst|].
        exfalso.
        assert (E x) as EX.
        { apply TCCOH in ISSX. apply ISSX. }
        assert (W x) as WX.
        { apply TCCOH in ISSX. apply ISSX. }
        assert (loc lab x = Some locw) as LOCX.
        { rewrite <- LOC. by apply WF.(wf_col). }
        assert (loc lab wprev = Some locw) as LOCWP.
        { rewrite <- LOC. apply WF.(wf_col). eapply rfrmw_in_im_co; eauto. }
        edestruct WF.(wf_co_total) with (a:=wprev) (b:=x) as [COWX|COWX]; auto.
        1,2: split; [split|]; eauto.
        1,2: by apply TCCOH in WPISS; apply WPISS.
        { eapply rfrmw_in_im_co; eauto. }
        assert (Time.lt (f_to x) (f_to wprev)) as LL.
        { eapply f_to_co_mon; eauto. }
        rewrite KK in LL.
        eapply XX.
        3: by apply LL.
        all: eauto. }
      exfalso. eapply XX.
      { apply ISSX. }
      { rewrite <- LOC. by apply WF.(wf_col). }
      rewrite KK. rewrite NN1. apply Time.incr_spec. }
    intros HH. exfalso.
    assert (Time.lt (f_from y) (f_to y)) as FF by (apply FCOH; auto).
    eapply XX.
    3: { etransitivity; [|by apply FF].
         rewrite <- HH. etransitivity; apply Time.incr_spec. }
    { done. }
    rewrite <- LOC. symmetry. by apply WF.(wf_col). }
  eapply SIM_HELPER; auto. by ins; rewrite updo; auto; intros H; subst.
Qed.

End Aux.
