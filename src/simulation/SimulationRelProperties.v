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

Lemma interval_disjoint_imm_le a b c d (LE : Time.le b c):
  Interval.disjoint (a, b) (c, d).
Proof using.
  red; ins.
  destruct LHS as [LFROM LTO].
  destruct RHS as [RFROM RTO]; simpls.
  eapply Time.lt_strorder.
  eapply TimeFacts.le_lt_lt.
  2: by apply RFROM.
  etransitivity; [by apply LTO|].
  done.
Qed.

Lemma sim_msg_f_issued f_to f_to' T rel b 
      (TCCOH : tc_coherent G sc T)
      (IMMCON : imm_consistent G sc)
      (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
      (ISS : issued T b)
      (ISSEQ_TO   : forall e (ISS: issued T e), f_to'   e = f_to   e)
      (SIMMEM : sim_msg G sc f_to b rel) :
  sim_msg G sc f_to' b rel.
Proof using WF.
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

Lemma sim_mem_helper_f_issued f_to f_to' T rel b from v
      (TCCOH : tc_coherent G sc T)
      (IMMCON : imm_consistent G sc)
      (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
      (ISS : issued T b)
      (ISSEQ_TO   : forall e (ISS: issued T e), f_to'   e = f_to   e)
      (HELPER : sim_mem_helper G sc f_to b from v rel) :
  sim_mem_helper G sc f_to' b from v rel.
Proof using WF.
  red; red in HELPER; desc.
  rewrite (ISSEQ_TO b ISS).
  splits; auto.
  eapply sim_msg_f_issued; eauto.
Qed.

Lemma sim_mem_covered_mori T T' f_to f_from threads thread memory
      (TCCOH : tc_coherent G sc T)
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

Lemma sim_mem_f_issued f_to f_from f_to' f_from' T threads thread memory
      (TCCOH : tc_coherent G sc T)
      (IMMCON : imm_consistent G sc)
      (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
      (ISSEQ_TO   : forall e (ISS: issued T e), f_to'   e = f_to   e)
      (ISSEQ_FROM : forall e (ISS: issued T e), f_from' e = f_from e)
      (SIMMEM : sim_mem G sc T f_to f_from threads thread memory) :
  sim_mem G sc T f_to' f_from' threads thread memory.
Proof using WF.
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

Lemma rintervals_fS f_to f_from f_to' f_from' T (S : actid -> Prop) memory smode
      (ETCCOH : etc_coherent G sc (mkETC T S))
      (REQ_TO   : forall e (SE: S e), f_to'   e = f_to   e)
      (REQ_FROM : forall e (SE: S e), f_from' e = f_from e)
      (RINTERVALS : reserved_time G T S f_to f_from memory smode):
  reserved_time G T S f_to' f_from' memory smode.
Proof using.
  red. red in RINTERVALS.
  desf. desc.
  unnw; splits.
  (* TODO: make a separate lemma. *)
  { red; ins.
    specialize (MEM l to from v rel MSG).
    destruct MEM as [MEM|MEM]; [by left; apply MEM|right].
    destruct MEM as [b H]; desc.
    exists b; splits; auto.
    { rewrite (REQ_FROM b); auto. by apply ETCCOH.(etc_I_in_S). }
    rewrite (REQ_TO b); auto. by apply ETCCOH.(etc_I_in_S). }
  { red. ins. specialize (HMEM l to from MSG).
    desc.
    set (CC:=RFRMWS).
    destruct_seq CC as [AA BB].
    exists b, b'. splits; auto.
    { erewrite REQ_FROM; eauto. apply AA. }
    erewrite REQ_TO; eauto. apply BB. }
  intros x y SX SY COXY H.
  apply TFRMW; auto.
  rewrite <- (REQ_FROM y SY).
  rewrite <- (REQ_TO   x SX).
  done.
Qed.

Lemma sim_prom_f_issued f_to f_from f_to' f_from' T thread promises 
      (TCCOH : tc_coherent G sc T)
      (IMMCON : imm_consistent G sc)
      (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
      (ISSEQ_TO   : forall e (ISS: issued T e), f_to'   e = f_to   e)
      (ISSEQ_FROM : forall e (ISS: issued T e), f_from' e = f_from e)
      (SIMPROM : sim_prom G sc T f_to f_from thread promises) :
  sim_prom G sc T f_to' f_from' thread promises.
Proof using WF.
  red; ins. edestruct SIMPROM as [b]; eauto; desc.
  exists b; splits; auto.
  { by rewrite (ISSEQ_FROM b ISS). }
  { by rewrite (ISSEQ_TO b ISS). }
  eapply sim_mem_helper_f_issued; eauto.
Qed.

Lemma f_to_coherent_fS f_to f_from f_to' f_from' T S
      (ETCCOH : etc_coherent G sc (mkETC T S))
      (REQ_TO   : forall e (SE: S e), f_to'   e = f_to   e)
      (REQ_FROM : forall e (SE: S e), f_from' e = f_from e)
      (FCOH: f_to_coherent G S f_to f_from):
  f_to_coherent G S f_to' f_from'.
Proof using WF.
  assert (tc_coherent G sc T) as TCCOH by apply ETCCOH.
  cdes FCOH. red; splits; ins.
  all: try (rewrite (REQ_TO x));
    try (rewrite (REQ_FROM x)); try (rewrite (REQ_FROM y)); auto.
  all: apply ETCCOH.(etc_I_in_S); auto.
  all: eapply w_covered_issued; eauto; split.
  2,4: by apply TCCOH.
  all: apply WF.(init_w).
  all: by destruct H.
Qed.

Lemma sim_res_prom_fS f_to f_from f_to' f_from' T S thread promises 
      (ETCCOH : etc_coherent G sc (mkETC T S))
      (IMMCON : imm_consistent G sc)
      (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
      (REQ_TO   : forall e (SE: S e), f_to'   e = f_to   e)
      (REQ_FROM : forall e (SE: S e), f_from' e = f_from e)
      (SIMRESPROM : sim_res_prom G T S f_to f_from thread promises) :
  sim_res_prom G T S f_to' f_from' thread promises.
Proof using.
  red. ins. apply SIMRESPROM in RES. desc.
  set (CC:=RFRMWS).
  destruct_seq CC as [AA BB].
  do 2 eexists. splits; eauto.
  { erewrite REQ_FROM; eauto. apply AA. }
  erewrite REQ_TO; eauto. apply BB.
Qed.

Lemma sc_view_f_issued f_to f_to' T sc_view
      (TCCOH : tc_coherent G sc T)
      (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
      (ISSEQ_TO   : forall e (ISS: issued T e), f_to'   e = f_to   e)
      (SC_REQ : forall l,
          max_value f_to (S_tm G l (covered T)) (LocFun.find l sc_view)):
  forall l,
    max_value f_to' (S_tm G l (covered T)) (LocFun.find l sc_view).
Proof using WF.
  intros l; specialize (SC_REQ l).
  eapply max_value_new_f; eauto.
  intros x H; apply ISSEQ_TO.
  red in H.
  eapply S_tm_covered; eauto.
Qed.

Lemma simrel_common_fS T S f_to f_from f_to' f_from' PC smode
      (ETCCOH : etc_coherent G sc (mkETC T S))
      (IMMCON : imm_consistent G sc)
      (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
      (REQ_TO   : forall e (SE: S e), f_to'   e = f_to   e)
      (REQ_FROM : forall e (SE: S e), f_from' e = f_from e)
      (SIMREL: simrel_common G sc PC T S f_to f_from smode):
  simrel_common G sc PC T S f_to' f_from' smode.
Proof using WF.
  assert (ISSEQ_TO   : forall e (ISS: issued T e), f_to'   e = f_to   e).
  { ins. apply REQ_TO. by apply ETCCOH.(etc_I_in_S). }
  assert (ISSEQ_FROM : forall e (ISS: issued T e), f_from' e = f_from e).
  { ins. apply REQ_FROM. by apply ETCCOH.(etc_I_in_S). }
  cdes SIMREL.
  red; splits; auto.
  { eapply f_to_coherent_fS; eauto. }
  { ins. eapply sc_view_f_issued; eauto. apply ETCCOH. }
  eapply rintervals_fS; eauto.
Qed.

Lemma simrel_thread_local_fS thread T S f_to f_from f_to' f_from' PC smode
      (ETCCOH : etc_coherent G sc (mkETC T S))
      (IMMCON : imm_consistent G sc)
      (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
      (REQ_TO   : forall e (SE: S e), f_to'   e = f_to   e)
      (REQ_FROM : forall e (SE: S e), f_from' e = f_from e)
      (SIMREL: simrel_thread_local G sc PC T S f_to f_from thread smode):
  simrel_thread_local G sc PC T S f_to' f_from' thread smode.
Proof using WF.
  assert (ISSEQ_TO   : forall e (ISS: issued T e), f_to'   e = f_to   e).
  { ins. apply REQ_TO. by apply ETCCOH.(etc_I_in_S). }
  assert (ISSEQ_FROM : forall e (ISS: issued T e), f_from' e = f_from e).
  { ins. apply REQ_FROM. by apply ETCCOH.(etc_I_in_S). }
  cdes SIMREL.
  red; splits; auto.
  eexists; eexists; eexists; splits; eauto.
  { eapply sim_prom_f_issued; eauto. apply ETCCOH. }
  { eapply sim_res_prom_fS; eauto. }
  { eapply sim_mem_f_issued; eauto. apply ETCCOH. }
  eapply sim_tview_f_issued; eauto. apply ETCCOH.
Qed.

Lemma simrel_thread_fS thread T S f_to f_from f_to' f_from' PC smode
      (ETCCOH : etc_coherent G sc (mkETC T S))
      (IMMCON : imm_consistent G sc)
      (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
      (REQ_TO   : forall e (SE: S e), f_to'   e = f_to   e)
      (REQ_FROM : forall e (SE: S e), f_from' e = f_from e)
      (SIMREL: simrel_thread G sc PC T S f_to f_from thread smode):
  simrel_thread G sc PC T S f_to' f_from' thread smode.
Proof using WF.
  cdes SIMREL. cdes COMMON. cdes LOCAL.
  red; splits; auto.
  { eapply simrel_common_fS; eauto. }
  eapply simrel_thread_local_fS; eauto.
Qed.

Lemma simrel_fS T S f_to f_from f_to' f_from' PC
      (ETCCOH : etc_coherent G sc (mkETC T S))
      (IMMCON : imm_consistent G sc)
      (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
      (REQ_TO   : forall e (SE: S e), f_to'   e = f_to   e)
      (REQ_FROM : forall e (SE: S e), f_from' e = f_from e)
      (SIMREL: simrel G sc PC T S f_to f_from):
  simrel G sc PC T S f_to' f_from'.
Proof using WF.
  cdes SIMREL. red; splits.
  { eapply simrel_common_fS; eauto. }
  ins. eapply simrel_thread_local_fS; eauto.
Qed.

Lemma max_value_leS locw w wprev s ts T S f_to f_from
      (IMMCOH : imm_consistent G sc)
      (ETCCOH : etc_coherent G sc (mkETC T S))
      (FCOH : f_to_coherent G S f_to f_from)
      (LOC : loc lab w = Some locw)
      (NS : ~ S w)
      (COIMM : immediate (⦗ S ⦘ ⨾ co) wprev w)
      (MAXVAL : max_value f_to s ts)
      (LOCS : s ⊆₁ Loc_ locw)
      (ISSS : s ⊆₁ S)
      (NOCO : ⦗ eq w ⦘ ⨾ co ⨾ ⦗ s ⦘ ≡ ∅₂) :
  Time.le ts (f_to wprev).
Proof using WF.
  assert (tc_coherent G sc T) as TCCOH by apply ETCCOH.
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

Lemma sim_res_prom_other_thread T S f_to f_to' f_from f_from' thread promises S'
      (SNT : S' ⊆₁ NTid_ thread)
      (SEQ_TO   : forall e (SE: Tid_ thread e), f_to'   e = f_to   e)
      (SEQ_FROM : forall e (SE: Tid_ thread e), f_from' e = f_from e)
      (RPROM : sim_res_prom G T S f_to f_from thread promises) :
  sim_res_prom G T (S ∪₁ S') f_to' f_from' thread promises.
Proof using.
  red. ins. apply RPROM in RES. desf.
  destruct_seq RFRMWS as [AA BB].
  assert (~ S' b /\ ~ S' b') as [NSB NSB'].
  { split; intros CC; eapply SNT; eauto.
    { apply AA. }
    apply BB. }
  exists b, b'. splits; auto.
  { apply seq_eqv_lr. splits; auto.
    all: generalize AA BB; basic_solver. }
  { apply SEQ_FROM. apply AA. }
  { apply SEQ_TO. apply BB. }
  intros [x HH]. apply seqA in HH. destruct_seq_r HH as CC.
  destruct CC as [CC DD].
  apply NOAFT. exists x.
  apply seqA. apply seq_eqv_r.
  do 2 (split; auto).
  destruct DD as [|DD]; auto.
  apply SNT in DD. desf.
Qed.

End SimRelProps.
