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
Require Import ViewRelHelpers.
Require Import SimulationRel.
Require Import SimState.
Require Import MemoryAux.
Require Import MaxValue.
Require Import ViewRel.
Require Import Event_imm_promise.
Require Import ExtTraversalConfig.
Require Import FtoCoherent.

Set Implicit Arguments.

Section SimRelProps.

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

Variable T : trav_config.
Variable S : actid -> Prop.
Variables f_to f_from : actid -> Time.t.
Hypothesis FCOH: f_to_coherent G S f_to f_from.

Variables f_to' f_from' : actid -> Time.t.

Variable REQ_TO   : forall e (SS :        S e), f_to'   e = f_to   e.
Variable ISSEQ_TO : forall e (ISS: issued T e), f_to'   e = f_to   e.

Variable REQ_FROM   : forall e (SS :        S e), f_from'   e = f_from   e.
Variable ISSEQ_FROM : forall e (ISS: issued T e), f_from'   e = f_from   e.

Variable IMMCON : imm_consistent G sc.

Variable TCCOH : tc_coherent G sc T.
Variable ETCCOH : etc_coherent G sc (mkETC T S).

Variable RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T.

Lemma sim_msg_f_issued rel b 
      (ISS : issued T b)
      (SIMMEM : sim_msg G sc f_to b rel) :
  sim_msg G sc f_to' b rel.
Proof using WF IMMCON TCCOH RELCOV ISSEQ_TO.
  red; red in SIMMEM.
  intros l; specialize (SIMMEM l).
  eapply max_value_new_f; eauto.
  intros x [H|H].
  2: by desf; apply (ISSEQ_TO  b ISS).
  assert (issued T x) as ISSX.
  2: by apply (ISSEQ_TO  x ISSX).
  eapply (msg_rel_issued WF IMMCON TCCOH); eauto;
      eexists; apply seq_eqv_r; split; eauto.
Qed.

Lemma sim_mem_helper_f_issued rel b from v
      (ISS : issued T b)
      (HELPER : sim_mem_helper G sc f_to b from v rel) :
  sim_mem_helper G sc f_to' b from v rel.
Proof using WF IMMCON TCCOH RELCOV ISSEQ_TO.
  red; red in HELPER; desc.
  rewrite (ISSEQ_TO b ISS).
  splits; auto.
  eapply sim_msg_f_issued; eauto.
Qed.

Lemma sim_mem_covered_mori T' threads thread memory
      (ISSEQ : issued T ≡₁ issued T')
      (COVIN : covered T ⊆₁ covered T')
      (SIMMEM : sim_mem G sc T f_to f_from threads thread memory) :
  sim_mem G sc T' f_to f_from threads thread memory.
Proof using WF.
  red in SIMMEM.
  red; splits.
  edestruct SIMMEM as [rel]; eauto; desc.
  { by apply ISSEQ. }
  exists rel. splits; auto. 
  intros TIDB NCOV.
  destruct H1; auto; split; auto.
  destruct H0 as [p_rel]; desc.
  exists p_rel; splits; auto.
  desf; [left; split; auto|right].
  { intros HH; apply NINRMW. generalize HH.
    generalize ISSEQ. basic_solver 10. }
  exists p; splits; auto.
  { by apply ISSEQ. }
  eexists; split; eauto.
Qed.

Lemma sim_mem_f_issued threads thread memory
      (SIMMEM : sim_mem G sc T f_to f_from threads thread memory) :
  sim_mem G sc T f_to' f_from' threads thread memory.
Proof using WF IMMCON RELCOV TCCOH ISSEQ_TO ISSEQ_FROM.
  red in SIMMEM.
  red; splits.
  edestruct SIMMEM as [rel]; eauto; desc.
  exists rel.
  rewrite (ISSEQ_TO   b ISSB); rewrite (ISSEQ_FROM b ISSB).
  splits; auto. 
  { eapply sim_mem_helper_f_issued; eauto. }
  ins. destruct H1; auto; split; auto.
  destruct H2 as [p_rel]; desc.
  exists p_rel; splits; auto.
  desf; [by left|right].
  exists p; splits; auto.
  eexists; split; eauto.
  rewrite (ISSEQ_TO p); eauto.
  rewrite (ISSEQ_FROM p); eauto.
Qed.

Lemma sim_res_mem_f_issued thread threads memory
      (SIMMEM : sim_res_mem G T S f_to f_from thread threads memory) :
  sim_res_mem G T S f_to' f_from' thread threads memory.
Proof using WF REQ_TO REQ_FROM.
  red in SIMMEM.
  red. unnw. ins.
  rewrite (REQ_TO RESB); rewrite (REQ_FROM RESB). by apply SIMMEM.
Qed.

Lemma rintervals_fS smode memory
      (RINTERVALS : reserved_time G T S f_to f_from smode memory):
  reserved_time G T S f_to' f_from' smode memory.
Proof using ETCCOH REQ_TO REQ_FROM.
  red. red in RINTERVALS.
  desf. desc.
  unnw; splits.
  (* TODO: make a separate lemma. *)
  { red; ins.
    specialize (MEM l to from v rel MSG).
    destruct MEM as [MEM|MEM]; [by left; apply MEM|right].
    destruct MEM as [b H]; desc.
    exists b; splits; auto.
    { rewrite REQ_FROM; auto. by apply ETCCOH.(etc_I_in_S). }
    rewrite REQ_TO; auto. by apply ETCCOH.(etc_I_in_S). }
  { red. ins. specialize (HMEM l to from MSG).
    desc.
    exists b. splits; auto.
    { erewrite REQ_FROM; eauto. }
    erewrite REQ_TO; eauto. }
  intros x y SX SY COXY H.
  apply TFRMW; auto.
  rewrite <- (REQ_FROM SY).
  rewrite <- (REQ_TO   SX).
  done.
Qed.

Lemma sim_prom_f_issued thread promises 
      (SIMPROM : sim_prom G sc T f_to f_from thread promises) :
  sim_prom G sc T f_to' f_from' thread promises.
Proof using WF IMMCON TCCOH RELCOV ISSEQ_TO ISSEQ_FROM.
  red; ins. edestruct SIMPROM as [b]; eauto; desc.
  exists b; splits; auto.
  { by rewrite (ISSEQ_FROM b ISS). }
  { by rewrite (ISSEQ_TO b ISS). }
  eapply sim_mem_helper_f_issued; eauto.
Qed.

Lemma f_to_coherent_fS : f_to_coherent G S f_to' f_from'.
Proof using WF TCCOH ETCCOH FCOH REQ_TO REQ_FROM.
  cdes FCOH. red; splits; ins.
  all: try (rewrite REQ_TO);
    try (rewrite REQ_FROM); try (rewrite REQ_FROM); auto.
  all: apply ETCCOH.(etc_I_in_S); auto.
  all: eapply w_covered_issued; eauto; split.
  2,4: by apply TCCOH.
  all: apply WF.(init_w).
  all: by destruct H.
Qed.

Lemma sim_res_prom_fS thread promises 
      (SIMRESPROM : sim_res_prom G T S f_to f_from thread promises) :
  sim_res_prom G T S f_to' f_from' thread promises.
Proof using REQ_TO REQ_FROM.
  red. ins. apply SIMRESPROM in RES. desc.
  eexists. splits; eauto.
  { erewrite REQ_FROM; eauto. }
  erewrite REQ_TO; eauto.
Qed.

Lemma sc_view_f_issued sc_view
      (SC_REQ : forall l,
          max_value f_to (S_tm G l (covered T)) (LocFun.find l sc_view)):
  forall l,
    max_value f_to' (S_tm G l (covered T)) (LocFun.find l sc_view).
Proof using WF RELCOV TCCOH ISSEQ_TO IMMCON.
  intros l; specialize (SC_REQ l).
  eapply max_value_new_f; eauto.
  intros x H; apply ISSEQ_TO.
  red in H.
  eapply S_tm_covered; eauto.
Qed.

Lemma simrel_common_fS PC smode
      (SIMREL: simrel_common G sc PC T S f_to f_from smode):
  simrel_common G sc PC T S f_to' f_from' smode.
Proof using WF IMMCON RELCOV ETCCOH FCOH TCCOH REQ_TO REQ_FROM ISSEQ_TO ISSEQ_FROM.
  cdes SIMREL.
  red; splits; auto.
  { eapply f_to_coherent_fS; eauto. }
  { ins. eapply sc_view_f_issued; eauto. }
  eapply rintervals_fS; eauto.
Qed.

Lemma simrel_thread_local_fS thread PC smode
      (SIMREL: simrel_thread_local G sc PC T S f_to f_from thread smode):
  simrel_thread_local G sc PC T S f_to' f_from' thread smode.
Proof using WF IMMCON RELCOV ETCCOH TCCOH REQ_TO REQ_FROM ISSEQ_TO ISSEQ_FROM.
  cdes SIMREL.
  red; splits; auto.
  eexists; eexists; eexists; splits; eauto.
  { eapply sim_prom_f_issued; eauto. }
  { eapply sim_res_prom_fS; eauto. }
  { eapply sim_mem_f_issued; eauto. }
  { eapply sim_res_mem_f_issued; eauto. }
  eapply sim_tview_f_issued; eauto.
Qed.

Lemma simrel_thread_fS thread PC smode
      (SIMREL: simrel_thread G sc PC T S f_to f_from thread smode):
  simrel_thread G sc PC T S f_to' f_from' thread smode.
Proof using WF IMMCON RELCOV ETCCOH FCOH TCCOH REQ_TO REQ_FROM ISSEQ_TO ISSEQ_FROM.
  cdes SIMREL. cdes COMMON. cdes LOCAL.
  red; splits; auto.
  { eapply simrel_common_fS; eauto. }
  eapply simrel_thread_local_fS; eauto.
Qed.

Lemma simrel_fS PC
      (SIMREL: simrel G sc PC T S f_to f_from):
  simrel G sc PC T S f_to' f_from'.
Proof using WF IMMCON RELCOV FCOH ETCCOH TCCOH REQ_TO REQ_FROM ISSEQ_TO ISSEQ_FROM.
  cdes SIMREL. red; splits.
  { eapply simrel_common_fS; eauto. }
  ins. eapply simrel_thread_local_fS; eauto.
Qed.

Lemma max_value_leS locw w wprev s ts
      (LOC : loc lab w = Some locw)
      (NS : ~ s w)
      (COIMM : immediate (⦗ S ⦘ ⨾ co) wprev w)
      (MAXVAL : max_value f_to s ts)
      (LOCS : s ⊆₁ Loc_ locw)
      (ISSS : s ⊆₁ S)
      (NOCO : ⦗ eq w ⦘ ⨾ co ⨾ ⦗ s ⦘ ≡ ∅₂) :
  Time.le ts (f_to wprev).
Proof using WF IMMCON ETCCOH FCOH TCCOH.
  red in MAXVAL. desc.
  destruct MAX as [[Y1 Y2]|[a_max Y1]].
  { rewrite Y2. apply Time.bot_spec. }
  desc.
  destruct (classic (a_max = wprev)) as [|NEQ]; [by subst|].
  etransitivity; eauto.
  apply Time.le_lteq. left.
  assert (S wprev) as SWP.
  { destruct COIMM as [CO _].
    apply seq_eqv_l in CO. desf. }
  assert (co wprev w) as COWP.
  { destruct COIMM as [CO _].
    apply seq_eqv_l in CO. desf. }
  assert (E w) as EW.
  { apply (dom_r WF.(wf_coE)) in COWP. 
    apply seq_eqv_r in COWP. desf. }
  assert (W w) as WW.
  { apply (dom_r WF.(wf_coD)) in COWP. 
    apply seq_eqv_r in COWP. desf. }
  assert (E wprev) as EWP.
  { by apply ETCCOH.(etc_S_in_E). }
  assert (W wprev) as WWP.
  { by apply (reservedW WF ETCCOH). }
  assert (loc lab wprev = Some locw) as LOCWP.
  { rewrite <- LOC. by apply WF.(wf_col). }
  assert (S a_max) as ISSA.
  { by apply ISSS. }
  assert (E a_max) as EA.
  { by apply ETCCOH.(etc_S_in_E). }
  assert (is_w lab a_max) as WA.
  { by apply (reservedW WF ETCCOH). }
  eapply f_to_co_mon; eauto.
  edestruct WF.(wf_co_total) as [CO|CO].
  3: by apply NEQ.
  3: done.
  1,2: split; [split|]; auto.
  exfalso.
  assert (w <> a_max) as WANEQ.
  { intros H. desf. }
  assert (co w a_max) as COWA.
  { edestruct WF.(wf_co_total) as [CO'|CO'].
    3: by apply WANEQ.
    3: done.
    1,2: split; [split|]; auto.
    { rewrite LOC. by apply LOCS. }
    exfalso.
    eapply COIMM.
    all: apply seq_eqv_l; split; eauto. }
  eapply NOCO. apply seq_eqv_l. split; eauto.
  apply seq_eqv_r. split; eauto.
Qed.

Notation "'NTid_' t" := (fun x => tid x <> t) (at level 1).
Notation "'Tid_' t"  := (fun x => tid x =  t) (at level 1).

Lemma sim_res_prom_other_thread thread promises S'
      (SNT : S' ⊆₁ NTid_ thread)
      (RPROM : sim_res_prom G T S f_to f_from thread promises) :
  sim_res_prom G T (S ∪₁ S') f_to' f_from' thread promises.
Proof using REQ_TO REQ_FROM.
  red. ins. apply RPROM in RES. desf.
  exists b. splits; auto. by left.
Qed.

Lemma reserved_to_message thread local memory
      (SIMMEM    : sim_mem     G sc T f_to f_from thread local memory)
      (SIMRESMEM : sim_res_mem G T  S f_to f_from thread local memory) :
  forall l b (RESB: S b) (LOC: Loc_ l b),
    exists msg,
      Memory.get l (f_to b) memory = Some (f_from b, msg) /\
      (tid b = thread ->
       ~ covered T b ->
       Memory.get l (f_to b) local.(Local.promises) = Some (f_from b, msg)).
Proof using TCCOH.
  ins. destruct (classic (issued T b)) as [AA|AA].
  2: { eexists. split; ins; apply SIMRESMEM; auto. }
  assert (exists v, val lab b = Some v) as [v BB].
  { apply is_w_val. eapply issuedW; eauto. }
  edestruct SIMMEM as [msg CC]; eauto.
  simpls. desf. eexists. splits; eauto. ins. by apply CC1.
Qed.

Lemma memory_to_event memory
      (MTE  :      message_to_event G T   f_to f_from memory)
      (HMTE : half_message_to_event G T S f_to f_from memory) :
  forall l to from msg
         (MSG : Memory.get l to memory = Some (from, msg)),
    (to = Time.bot /\ from = Time.bot) \/
    exists b,
    ⟪ ACTS : E b ⟫ /\
    ⟪ SB   : S b ⟫ /\
    ⟪ LOC  : Loc_ l b ⟫ /\
    ⟪ FROM : f_from b = from ⟫ /\
    ⟪ TO   : f_to b = to ⟫.
Proof using ETCCOH.
  ins. destruct msg.
  { apply MTE in MSG. desf; eauto.
    right. eexists. splits; eauto. by apply ETCCOH.(etc_I_in_S). }
  right.
  apply HMTE in MSG. desf. eexists. splits; eauto.
Qed.

Lemma S_le_max_ts locw memory local thread x
      (SX   : S x)
      (XLOC : loc lab x = Some locw)
      (SIMMEM    : sim_mem     G sc T f_to f_from thread local memory)
      (SIMRESMEM : sim_res_mem G T S f_to f_from thread local memory) :
  Time.le (f_to x) (Memory.max_ts locw memory).
Proof using TCCOH.
  eapply reserved_to_message in SX; eauto.
  desf.
  eapply Memory.max_ts_spec; eauto.
Qed.

Lemma co_S_memory_disjoint memory locw wp wn
      (COIMM  : immediate (⦗S⦘ ⨾ co ⨾ ⦗S⦘) wp wn)
      (CONS   : (co ⨾ ⦗ set_compl S ⦘ ⨾ co) wp wn)
      (LOCP   : loc lab wp = Some locw)
      (RESERVED_TIME:
         reserved_time G T S f_to f_from sim_normal memory) :
  forall (to from : Time.t) (msg : Message.t)
         (IN : Memory.get locw to memory = Some (from, msg)),
    Interval.disjoint (f_to wp, f_from wn) (from, to).
Proof using WF IMMCON ETCCOH FCOH TCCOH.
  assert (sc_per_loc G) as SPL.
  { apply coherence_sc_per_loc. apply IMMCON. }

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
Proof using WF IMMCON FCOH ETCCOH TCCOH.
  assert (complete G) as COMPL by apply IMMCON.
  assert (sc_per_loc G) as SPL.
  { apply coherence_sc_per_loc. apply IMMCON. }
  assert (co x w) as COXW by (by apply rf_rmw_in_co).
  assert (loc lab x = Some locw) as XLOC. 
  { rewrite <- WLOC. by apply WF.(wf_col). }

  set (XX:=SX).
  eapply reserved_to_message in XX; eauto.
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

Add Parametric Morphism : message_to_event with signature
    eq ==> same_trav_config ==> eq ==> eq ==> eq ==> iff
       as message_to_event_more.
Proof.
  ins. split; intros HH; red.
  all: ins; apply HH in MSG; desf; auto.
  all: right; eexists; splits; eauto; by apply H.
Qed.

Add Parametric Morphism : half_message_to_event with signature
    eq ==> same_trav_config ==> set_equiv ==> eq ==> eq ==> eq ==> iff
       as half_message_to_event_more.
Proof.
  ins. split; intros HH; red.
  all: ins; apply HH in MSG; desf; auto.
  all: eexists; splits; eauto; try by apply H0.
  all: by intros AA; apply NOISS; apply H.
Qed.

Add Parametric Morphism : reserved_time with signature
  eq ==> same_trav_config ==> set_equiv ==> eq ==> eq ==> eq ==> eq ==> iff
      as reserved_time_more.
Proof.
  ins. split; intros HH.
  { match goal with
    | H : sim_mode |- _ => destruct H
    end; [|by red; splits; rewrite <- H0; apply HH].
    red; cdes HH; splits; [by rewrite <- H| |by ins; apply HH; auto; apply H0].
    eapply half_message_to_event_more.
    7: by eauto.
    all: eauto.
    2: by symmetry.
      by apply same_trav_config_sym. }
  match goal with
  | H : sim_mode |- _ => destruct H
  end; [|by red; splits; rewrite H0; apply HH].
  red; cdes HH; splits; [by rewrite H| |by ins; apply HH; auto; apply H0].
  eapply half_message_to_event_more.
  7: by eauto.
  all: eauto.
Qed.

End SimRelProps.
