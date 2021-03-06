Require Import Arith Omega.
From hahn Require Import Hahn.
Require Import PromisingLib.

From imm Require Import Events.
From imm Require Import Execution.
From imm Require Import Execution_eco.
From imm Require Import imm_bob imm_s_ppo.
From imm Require Import imm_s_hb.
From imm Require Import imm_s.
From imm Require Import SubExecution.
From imm Require Import CertCOhelper.
From imm Require Import CombRelations.
From imm Require Import Prog.
From imm Require Import ProgToExecution ProgToExecutionProperties.
From imm Require Import Receptiveness.

Require Import Cert_views.
Require Import Cert_rf.
Require Import Cert_tc.
Require Import Cert_ar.
Require Import Cert_co.
Require Import Cert_D.
Require Import CertExecution2.
From imm Require Import TraversalConfig.
Require Import MaxValue.
Require Import ViewRel.
Require Import SimulationRel.
Require Import SimState.
Require Import ExtTraversalConfig.
Require Import CertExecution1.
Require Import ExtTraversalProperties.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section Cert.

Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'NTid_' t" := (fun x => tid x <> t) (at level 1).

Lemma cert_graph_init Gf sc T S PC f_to f_from thread
      (WF : Wf Gf)
      (IMMCON : imm_consistent Gf sc)
      (SIMREL : simrel_thread Gf sc PC T S f_to f_from thread sim_normal) :
  exists G' sc' T' S',
    ⟪ WF : Wf G' ⟫ /\
    ⟪ IMMCON : imm_consistent G' sc' ⟫ /\
    ⟪ NTID  : NTid_ thread ∩₁ G'.(acts_set) ⊆₁ covered T' ⟫ /\
    ⟪ SIMREL : simrel_thread G' sc' PC T' S' f_to f_from thread sim_certification ⟫.
Proof using All.
assert (exists G, G = rstG Gf T S thread) by eauto; desc.

assert (WF_SC: wf_sc Gf sc).
by apply IMMCON.

assert (ETCCOH: etc_coherent Gf sc (mkETC T S)).
{ by cdes SIMREL; cdes COMMON. }
assert (TCCOH: tc_coherent Gf sc T) by apply ETCCOH.

assert (RELCOV: (fun a : actid => is_w (lab Gf) a) ∩₁ (fun a : actid => is_rel (lab Gf) a) ∩₁ issued T
⊆₁ covered T).
by cdes SIMREL; cdes COMMON.

remember (⦗E0 Gf T S thread⦘ ⨾ sc ⨾ ⦗E0 Gf T S thread⦘) as Gsc.
assert (SUB: sub_execution Gf G sc Gsc).
{ unfold rstG in *; subst.
apply restrict_sub.
done.
rewrite <- E_E0; eauto.
rewrite E_E0; eauto.
rewrite E0_in_Gf; eauto. }

assert (WF_G: Wf G).
by subst; eapply rstWF; edone.

assert (WF_SC_G: wf_sc G Gsc).
by subst; eapply WF_SC_rst; edone.

assert (RELCOV_G : is_w G.(lab) ∩₁ is_rel G.(lab) ∩₁ T.(issued) ⊆₁ T.(covered)).
by rewrite (sub_W SUB), (sub_Rel SUB).

assert (RMWCOV : forall r w : actid, rmw Gf r w -> covered T r <-> covered T w) by apply SIMREL.

assert (TCCOH_G : tc_coherent G Gsc T).
{ subst; eapply TCCOH_rst; try edone. }

assert (TCCOH_rst_new_T : tc_coherent G Gsc (mkTC ( T.(covered) ∪₁ (G.(acts_set) ∩₁ NTid_ thread))  T.(issued))).
{ subst; eapply TCCOH_rst_new_T; eauto. }

assert (IT_new_co: T.(issued) ∪₁ G.(acts_set) ∩₁ is_w G.(lab) ∩₁ Tid_ thread ≡₁ G.(acts_set) ∩₁ is_w G.(lab)).
subst; eapply IT_new_co; edone.

assert (ACYC_EXT_G: acyc_ext G Gsc).
subst; eapply acyc_ext_rst; edone.

assert (CSC_G : coh_sc G Gsc).
subst; eapply coh_sc_rst; edone.

assert (COH_G: coherence G).
subst; eapply coherence_rst; edone.

assert (AT_G: rmw_atomicity G).
subst; eapply rmw_atomicity_rst; edone.

assert (E_to_S: G.(acts_set) ⊆₁ T.(covered) ∪₁ dom_rel (G.(sb)^? ⨾ ⦗S⦘)).
subst; eapply E_to_S; edone.

assert (Grfe_E : dom_rel G.(rfe) ⊆₁ T.(issued)).
subst; eapply Grfe_E; edone.

assert (E_F_AcqRel_in_C: G.(acts_set) ∩₁ (is_f G.(lab)) ∩₁ (is_ra G.(lab)) ⊆₁ T.(covered)).
subst; eapply E_F_AcqRel_in_C; edone.

assert ( COMP_ACQ: forall r (IN: (G.(acts_set) ∩₁ (is_r G.(lab)) ∩₁ (is_acq G.(lab))) r), exists w, G.(rf) w r).
{ subst; eapply COMP_ACQ; edone. }

assert (dom_rel
          ((rmw G ⨾ rfi G)＊ ⨾ ⦗acts_set G ∩₁ (is_r (lab G)) ∩₁
           (is_acq (lab G))⦘) ⊆₁ codom_rel (rf G))
  as RMW_RFI_ACQ.
{ subst; eapply COMP_RMWRFI_ACQ; edone. }

assert ( urr_helper: dom_rel ((G.(hb) ⨾ ⦗(is_f G.(lab)) ∩₁ (is_sc G.(lab))⦘)^? ⨾ Gsc^? ⨾ G.(hb)^? ⨾ G.(release) ⨾ ⦗T.(issued)⦘) ⊆₁ T.(covered)).
subst; eapply urr_helper; edone.

assert ( urr_helper_C: dom_rel ((G.(hb) ⨾ ⦗(is_f G.(lab)) ∩₁ (is_sc G.(lab))⦘)^? ⨾ Gsc^? ⨾ G.(hb)^? ⨾ (G.(release) ⨾ G.(rf))^? ⨾ ⦗T.(covered)⦘) ⊆₁ T.(covered)).
subst; eapply urr_helper_C; edone.

assert ( W_hb_sc_hb_to_I_NTid: dom_rel (⦗(is_w G.(lab))⦘ ⨾ G.(hb) ⨾ (Gsc ⨾ G.(hb))^? ⨾ ⦗T.(issued) ∩₁ NTid_ thread⦘) ⊆₁ T.(issued)).
subst; eapply W_hb_sc_hb_to_I_NTid; edone.

assert ( detour_E : dom_rel (G.(detour) ⨾ ⦗G.(acts_set) ∩₁ NTid_ thread⦘) ⊆₁ T.(issued)).
subst; eapply detour_E; edone.

assert ( detour_Acq_E : dom_rel (G.(detour) ⨾ ⦗G.(acts_set) ∩₁ (is_r G.(lab)) ∩₁ (is_acq G.(lab))⦘) ⊆₁ T.(issued)).
subst; eapply detour_Acq_E; edone.

assert ( hb_sc_hb_de : ⦗(G.(acts_set) \₁ T.(covered)) ∩₁ (G.(acts_set) \₁ T.(issued))⦘ ⨾ G.(hb) ⨾ (Gsc ⨾ G.(hb))^? ⊆ G.(sb)).
subst; eapply hb_sc_hb_de; edone.

assert (COMP_C : T.(covered) ∩₁ (is_r G.(lab)) ⊆₁ codom_rel G.(rf)).
subst; eapply COMP_C; edone.

assert (COMP_NTID : G.(acts_set) ∩₁ NTid_ thread ∩₁ (is_r G.(lab)) ⊆₁ codom_rel G.(rf)).
subst; eapply COMP_NTID; edone.

assert (COMP_PPO : dom_rel (G.(ppo) ⨾ ⦗T.(issued)⦘) ∩₁ (is_r G.(lab)) ⊆₁ codom_rel G.(rf)).
{ subst; eapply COMP_PPO; edone. }
assert (COM_PPO_ALT : dom_rel (ppo G ⨾ ⦗issued T⦘) ⊆₁ codom_rel (rf G)).
{ rewrite (dom_l (wf_ppoD G)), !seqA.
  rewrite dom_eqv1. by rewrite set_interC. }

assert (acts_G_in_acts_Gf : acts_set G ⊆₁ acts_set Gf).
by apply (sub_E_in SUB).

assert (lab_G_eq_lab_Gf : lab G = lab Gf).
{ rewrite H. unfold rstG. by unfold restrict. }

assert (rmw_G_rmw_Gf : rmw G ≡
                       ⦗ E0 Gf T S thread ⦘ ⨾ rmw Gf ⨾ ⦗ E0 Gf T S thread ⦘).
{ rewrite H. unfold rstG. by unfold restrict. }

cdes SIMREL. cdes LOCAL.
red in STATE. desc.
cdes STATE0.

set (CT := E0 Gf T S thread ∩₁ Tid_ thread).
assert (CT ≡₁ (covered T ∪₁ issued T ∪₁ dom_rel ((sb Gf)^? ⨾ ⦗Tid_ thread ∩₁ S⦘))
           ∩₁ Tid_ thread) as CTALT.
{ unfold CT. unfold E0.
  arewrite (rmw Gf ⨾ ⦗NTid_ thread ∩₁ issued T⦘ ≡
            ⦗NTid_ thread⦘ ⨾ rmw Gf ⨾ ⦗NTid_ thread ∩₁ issued T⦘).
  { split; [|basic_solver].
    intros x y HH. apply seq_eqv_l. split; auto.
    apply seq_eqv_r in HH. destruct HH as [RMW [AA BB]].
    intros CC. apply AA. rewrite <- CC. symmetry.
      by apply WF.(wf_rmwt). }
  basic_solver 10. }

assert (CT ⊆₁ acts_set Gf) as CTEE.
{ rewrite CTALT.
  rewrite TCCOH.(coveredE).
  rewrite TCCOH.(issuedE).
  rewrite ETCCOH.(etc_S_in_E).
  rewrite wf_sbE. basic_solver. }

assert (CREP_weak :
          forall e (CTE : CT e),
               exists index : nat,
                 ⟪ EREP : e = ThreadEvent thread index ⟫).
{ ins. apply CTALT in CTE. destruct CTE as [AA BB].
  destruct e; desf. simpls. eauto. }

assert (wf_thread_state thread state') as GPC'.
{ eapply wf_thread_state_steps; eauto. }

assert (exists ctindex,
           ⟪ CCLOS :forall index (LT : index < ctindex),
             CT (ThreadEvent thread index) ⟫ /\
           ⟪ CREP : forall e (CTE : CT e),
               exists index : nat,
                 ⟪ EREP : e = ThreadEvent thread index ⟫ /\
                 ⟪ ILT : index < ctindex ⟫ ⟫).
{ destruct (classic (exists e, CT e)) as [|NCT].
  2: { exists 0. splits.
       { ins. inv LT. }
       ins. exfalso. apply NCT. eauto. }
  desc.
  assert (acyclic (sb Gf ⨾ ⦗ CT ⦘)) as AC.
  { arewrite (sb Gf ⨾ ⦗CT⦘ ⊆ sb Gf). apply sb_acyclic. }
  set (doml := filterP CT Gf.(acts)).
  assert (forall c, (sb Gf ⨾ ⦗CT⦘)＊ e c -> In c doml) as UU.
  { intros c SCC. apply rtE in SCC. destruct SCC as [SCC|SCC].
    { red in SCC. desf. apply in_filterP_iff. split; auto. by apply CTEE. }
    apply inclusion_ct_seq_eqv_r in SCC. apply seq_eqv_r in SCC.
    apply in_filterP_iff. split; auto; [apply CTEE|]; desf. }
  edestruct (last_exists doml AC UU) as [max [MM1 MM2]].
  assert (CT max) as CTMAX.
  { apply rtE in MM1. destruct MM1 as [MM1|MM1].
    { red in MM1. desf. }
    apply inclusion_ct_seq_eqv_r in MM1. apply seq_eqv_r in MM1. desf. }
  assert (Tid_ thread max) as CTTID by apply CTMAX.
  destruct max as [l|mthread mindex]; [by desf|].
  simpls. rewrite CTTID in *.
  assert (acts_set Gf (ThreadEvent thread mindex)) as EEM.
  { by apply CTEE. }
  exists (1 + mindex). splits.
  { ins. apply CTALT in CTMAX.
    apply CTALT. split; auto. 
    apply le_lt_or_eq in LT. destruct LT as [LT|LT].
    2: { inv LT. apply CTMAX. }
    assert ((ProgToExecution.G state').(acts_set) (ThreadEvent thread mindex)) as PP.
    { apply TEH.(tr_acts_set). by split. }
    assert (Gf.(acts_set) (ThreadEvent thread index)) as EEE.
    { apply TEH.(tr_acts_set). eapply acts_rep in PP; eauto. desc.
      eapply GPC'.(acts_clos). inv REP. omega. }
    assert (sb Gf (ThreadEvent thread index) (ThreadEvent thread mindex)) as QQ.
    { red.
      apply seq_eqv_l. split; auto.
      apply seq_eqv_r. split; auto.
      red. split; auto. omega. }
    destruct CTMAX as [[[AA|AA]|[z AA]] _].
    { do 2 left. apply TCCOH in AA. apply AA. eexists.
      apply seq_eqv_r. split; eauto. }
    { right. exists (ThreadEvent thread mindex).
      apply seq_eqv_r. split; auto.
      split; auto. by apply ETCCOH.(etc_I_in_S). }
    right. exists z. apply seq_eqv_r in AA. destruct AA as [AA1 AA2].
    apply seq_eqv_r. split; auto.
    apply rewrite_trans_seq_cr_cr.
    { apply sb_trans. }
    eexists; split; [|by eauto].
      by apply r_step. }
  ins. set (CTE' := CTE).
  apply CREP_weak in CTE'. desc.
  eexists. splits; eauto.
  destruct (le_gt_dec index mindex) as [LL|LL].
  { by apply le_lt_n_Sm. }
  exfalso.
  eapply MM2. apply seq_eqv_r. split; [|by apply CTE].
  red.
  apply seq_eqv_l. split; auto.
  apply seq_eqv_r. split; auto.
  red. rewrite EREP. by split. }
desc.

assert (exists state'',
           ⟪ STEPS'' : (step thread)＊ state state'' ⟫ /\
           ⟪ TEH''   : thread_restricted_execution G thread state''.(ProgToExecution.G) ⟫).
{ edestruct steps_middle_set with (C:=CT) (state0:=state) (state':=state')
    as [state'']; eauto.
  { intros x HH. apply GPC.(acts_rep) in HH.
    desc. 
    apply CTALT. rewrite REP in *. split; auto.
    do 2 left. by apply PCOV. }
  { rewrite CTALT. rewrite TEH.(tr_acts_set).
    apply set_subset_inter; [|done].
    rewrite coveredE with (G:=Gf); eauto.
    rewrite issuedE with (G:=Gf); eauto.
    rewrite ETCCOH.(etc_S_in_E).
    rewrite wf_sbE. basic_solver. }
  { ins.
    apply TEH.(tr_rmw) in RMW.
    apply seq_eqv_l in RMW. destruct RMW as [TIDR RMW].
    apply seq_eqv_r in RMW. destruct RMW as [RMW TIDW].
    apply (dom_l WF.(wf_rmwD)) in RMW.
    apply seq_eqv_l in RMW. destruct RMW as [RREX RMW].
    assert (is_r (lab Gf) r) as RR by type_solver.
    split; intros AA.
    all: apply CTALT; split; auto.
    all: apply CTALT in AA; destruct AA as [[[AA|AA]|AA] _].
    1,4: do 2 left; cdes COMMON; by apply (RMWCOV r w RMW).
    { apply TCCOH.(issuedW) in AA. type_solver. }
    { right. unfolder in AA. desf.
      { apply (reservedW WF ETCCOH) in AA2. type_solver. }
      exists y. apply seq_eqv_r. split; [|split]; auto.
      destruct (classic (w = y)) as [|NEQ]; subst.
      { basic_solver. }
      edestruct (@sb_semi_total_l Gf r y w WF); auto.
      { intros HH. apply WF.(init_w) in HH.
        clear -RR HH. type_solver. }
      { by apply WF.(rmw_in_sb). }
      exfalso. eapply WF.(wf_rmwi); eauto. }
    { right. exists w. apply seq_eqv_r. split; [|split]; auto.
      { right. by apply rmw_in_sb. }
      apply ETCCOH.(etc_I_in_S). apply AA. }
    right. destruct AA as [y AA]. apply seq_eqv_r in AA. destruct AA as [AA BB].
    exists y. apply seq_eqv_r. split; auto.
    right. apply rewrite_trans_seq_cr_r.
    { apply sb_trans. }
    eexists; split; eauto. by apply rmw_in_sb. }
  desc.
  assert (wf_thread_state thread state'') as GPC''.
  { eapply wf_thread_state_steps; [|apply STEP1]; auto. }
  exists state''. splits; auto.
  edestruct steps_old_restrict with (state0:=state'') (state':=state') as [ORMW]; eauto.
  desc. unnw.
  constructor.
  { rewrite CACTS. unfold CT. rewrite H.
    rewrite E_E0; eauto. }
  { ins. rewrite H. unfold rstG, restrict; simpls.
    rewrite <- TEH.(tr_lab); auto.
    2: { eapply steps_preserve_E.
         3: by apply EE.
         all: eauto. }
    assert (tid x = thread) as HH.
    { apply GPC''.(acts_rep) in EE. desc. by subst. }
    rewrite <- HH in *.
    symmetry. eapply steps_preserve_lab; eauto. }
  all: rewrite H; unfold rstG, restrict; simpls.
  { rewrite ORMW. rewrite CACTS. unfold CT.
    rewrite !seqA.
    arewrite (⦗Tid_ thread⦘ ⨾ ⦗E0 Gf T S thread⦘ ⨾ rmw Gf ⨾ ⦗E0 Gf T S thread⦘ ⨾ ⦗Tid_ thread⦘ ≡
              ⦗E0 Gf T S thread⦘ ⨾ ⦗Tid_ thread⦘ ⨾ ⦗Tid_ thread⦘ ⨾ rmw Gf ⨾
              ⦗Tid_ thread⦘ ⨾ ⦗Tid_ thread⦘ ⨾ ⦗E0 Gf T S thread⦘).
    { basic_solver. }
    seq_rewrite <- TEH.(tr_rmw). basic_solver. }
  { rewrite ODATA. rewrite CACTS. unfold CT.
    rewrite !seqA.
    arewrite (⦗Tid_ thread⦘ ⨾ ⦗E0 Gf T S thread⦘ ⨾ data Gf ⨾ ⦗E0 Gf T S thread⦘ ⨾ ⦗Tid_ thread⦘ ≡
              ⦗E0 Gf T S thread⦘ ⨾ ⦗Tid_ thread⦘ ⨾ ⦗Tid_ thread⦘ ⨾ data Gf ⨾
              ⦗Tid_ thread⦘ ⨾ ⦗Tid_ thread⦘ ⨾ ⦗E0 Gf T S thread⦘).
    { basic_solver. }
    seq_rewrite <- TEH.(tr_data). basic_solver. }
  { rewrite OADDR. rewrite CACTS. unfold CT.
    rewrite !seqA.
    arewrite (⦗Tid_ thread⦘ ⨾ ⦗E0 Gf T S thread⦘ ⨾ addr Gf ⨾ ⦗E0 Gf T S thread⦘ ⨾ ⦗Tid_ thread⦘ ≡
              ⦗E0 Gf T S thread⦘ ⨾ ⦗Tid_ thread⦘ ⨾ ⦗Tid_ thread⦘ ⨾ addr Gf ⨾
              ⦗Tid_ thread⦘ ⨾ ⦗Tid_ thread⦘ ⨾ ⦗E0 Gf T S thread⦘).
    { basic_solver. }
    seq_rewrite <- TEH.(tr_addr). basic_solver. }
  { rewrite OCTRL. rewrite CACTS. unfold CT.
    rewrite !seqA.
    arewrite (⦗Tid_ thread⦘ ⨾ ⦗E0 Gf T S thread⦘ ⨾ ctrl Gf ⨾ ⦗E0 Gf T S thread⦘ ⨾ ⦗Tid_ thread⦘ ≡
              ⦗E0 Gf T S thread⦘ ⨾ ⦗Tid_ thread⦘ ⨾ ⦗Tid_ thread⦘ ⨾ ctrl Gf ⨾
              ⦗Tid_ thread⦘ ⨾ ⦗Tid_ thread⦘ ⨾ ⦗E0 Gf T S thread⦘).
    { basic_solver. }
    seq_rewrite <- TEH.(tr_ctrl). basic_solver. }
  rewrite OFAILDEP. rewrite CACTS. unfold CT.
  rewrite !seqA.
  arewrite (⦗Tid_ thread⦘ ⨾ ⦗E0 Gf T S thread⦘ ⨾ rmw_dep Gf ⨾
                          ⦗E0 Gf T S thread⦘ ⨾ ⦗Tid_ thread⦘ ≡
            ⦗E0 Gf T S thread⦘ ⨾ ⦗Tid_ thread⦘ ⨾ ⦗Tid_ thread⦘ ⨾ rmw_dep Gf ⨾
            ⦗Tid_ thread⦘ ⨾ ⦗Tid_ thread⦘ ⨾ ⦗E0 Gf T S thread⦘).
  { basic_solver. }
  seq_rewrite <- TEH.(tr_rmw_dep). basic_solver. }
desc.

assert (acts_set (ProgToExecution.G state) ⊆₁ covered T) as STATECOV.
{ intros x EE. apply GPC.(acts_rep) in EE. desc. subst. by apply PCOV. }

assert (COMP_RPPO : dom_rel (⦗fun a => is_r (lab G) a⦘ ⨾ (data G ∪ rfi G ∪ rmw G)＊ ⨾ rppo G ⨾ ⦗S⦘)
                        ⊆₁ codom_rel (rf G)).
{ subst. eapply COMP_RPPO; edone. }

assert (S_in_W : S ⊆₁ is_w G.(lab)).
{ rewrite (reservedW WF ETCCOH).
  eapply sub_W; eauto. }
assert (ST_in_E : S ∩₁ Tid_ thread ⊆₁ acts_set G).
{ subst. rewrite E_E0; eauto. unfold E0.
  unionR left -> right. basic_solver 10. }

assert
(F_SB_S :
   dom_rel (⦗(is_f G.(lab)) ∩₁ (is_ra G.(lab))⦘ ⨾ sb G ⨾ ⦗S⦘) ⊆₁ covered T).
{ rewrite sub_F; eauto.
  rewrite sub_AcqRel; eauto.
  rewrite sub_sb_in; eauto.
  apply ETCCOH. }
assert (RPPO_S : dom_rel ((detour G ∪ rfe G) ⨾ (data G ∪ rfi G ∪ rmw G)＊ ⨾ rppo G ⨾ ⦗S⦘) ⊆₁ issued T).
{ rewrite sub_detour_in; eauto.
  rewrite sub_rfe_in; eauto.
  rewrite sub_data_in; eauto.
  rewrite sub_rfi_in; eauto.
  subst.
  rewrite sub_rppo_in; eauto.
  2: by eapply Frmw_E_prefix_clos; eauto.
  rewrite sub_rmw_in; eauto.
  apply ETCCOH. }

assert (RMW_S : dom_rel ((detour G ∪ rfe G) ⨾ rmw G ⨾ ⦗S⦘) ⊆₁ issued T).
{ rewrite sub_detour_in; eauto.
  rewrite sub_rfe_in; eauto.
  rewrite sub_rmw_in; eauto.
  eapply etc_rmw_S with (T:=mkETC T S); eauto. }
assert (D_RMW_S : dom_rel (detour G ⨾ rmw G ⨾ ⦗S⦘) ⊆₁ issued T).
{ rewrite <- RMW_S. clear. basic_solver 10. }

assert (dom_rel
          ((detour G ∪ rfe G) ⨾ (rmw G ⨾ rfi G)＊ ⨾
           ⦗(is_r (lab G)) ∩₁ (is_acq (lab G))⦘ ⨾ sb G ⨾ ⦗S⦘) ⊆₁ issued T)
  as DRFE_RMW_RFI_R_ACQ.
{ rewrite sub_detour_in; eauto.
  rewrite sub_rfe_in; eauto.
  rewrite sub_rmw_in; eauto.
  rewrite sub_rfi_in; eauto.
  rewrite sub_R; eauto.
  rewrite sub_Acq; eauto.
  rewrite sub_sb_in; eauto.
  apply ETCCOH. }

set (delta_rf :=
       (new_rf G Gsc T S thread) ⨾ ⦗set_compl (dom_rel G.(rmw))⦘ ∪
       immediate (cert_co G T S thread) ⨾ G.(rmw)⁻¹ ⨾ ⦗set_compl (D G T S thread)⦘).
set (new_rfi := ⦗  Tid_ thread ⦘ ⨾ delta_rf ⨾ ⦗ Tid_ thread ⦘).
set (new_rfe := ⦗ NTid_ thread ⦘ ⨾ delta_rf ⨾ ⦗ Tid_ thread ⦘).

assert (delta_rf ⊆ cert_rf G Gsc T S thread) as DELTA_RF_CERT.
{ unfold delta_rf, cert_rf; clear. basic_solver 20. }

assert (delta_rf ≡
        ⦗acts_set G⦘ ⨾ delta_rf ⨾ ⦗acts_set G \₁ D G T S thread⦘)
  as delta_rfE.
{ apply dom_helper_3.
  arewrite (delta_rf ⊆ ⦗acts_set G⦘ ⨾ delta_rf ⨾ ⦗acts_set G⦘).
  { apply dom_helper_3.
    rewrite DELTA_RF_CERT. rewrite cert_rfE; eauto.
    clear. basic_solver. }
  subst delta_rf. rewrite wf_new_rfE; auto.
  clear. basic_solver 30. }

assert (delta_rf ≡ ⦗is_w G.(lab)⦘ ⨾ delta_rf ⨾ ⦗is_r G.(lab)⦘)
  as delta_rfD.
{ apply dom_helper_3.
  rewrite DELTA_RF_CERT. rewrite cert_rfD; auto. clear. basic_solver 10. }

assert (new_rfi ⊆ cert_rf G Gsc T S thread) as NEW_RFI_CERT.
{ unfold new_rfi. rewrite DELTA_RF_CERT. basic_solver 20. }
assert (new_rfif : functional new_rfi⁻¹).
{ rewrite NEW_RFI_CERT. apply cert_rff; auto. }

assert (new_rfe ⊆ cert_rf G Gsc T S thread) as NEW_RFE_CERT.
{ unfold new_rfe. rewrite DELTA_RF_CERT. basic_solver 20. }
assert (new_rfef : functional new_rfe⁻¹).
{ rewrite NEW_RFE_CERT. apply cert_rff; auto. }

set (new_rfe_ex := new_rfe ∪ ⦗ set_compl (codom_rel new_rfe) ⦘).

assert (new_rfe_unique: forall r, exists ! w, new_rfe_ex⁻¹  r w).
{ ins.
  destruct (classic ((codom_rel new_rfe) r)) as [X|X].
  { unfolder in X; desf.
    exists x; red; splits.
    unfold new_rfe_ex; basic_solver 12.
    unfold new_rfe_ex; unfolder; ins; desf.
    eapply new_rfef; basic_solver.
    exfalso; eauto. }
  exists r; red; splits.
  unfold new_rfe_ex; basic_solver 12.
  unfold new_rfe_ex; unfolder; ins; desf.
  unfolder in X; exfalso; eauto. }

assert (exists new_value, forall x, (new_rfe_ex)⁻¹ x (new_value x)); desc.
{ apply (unique_choice (new_rfe_ex)⁻¹ (new_rfe_unique)). }

set (get_val (v: option value) :=  match v with | Some v => v | _ => 0 end).

set (new_val := fun r => get_val (val G.(lab) (new_value r))).

assert (ST_in_W_ex : S ∩₁ Tid_ thread \₁ issued T ⊆₁ W_ex G).
{ arewrite (S ∩₁ Tid_ thread \₁ issued T ⊆₁
            W_ex Gf ∩₁ S ∩₁ Tid_ thread \₁ issued T).
  { unfolder. ins. desf. splits; auto.
    apply ETCCOH.(etc_S_I_in_W_ex). unfold eissued.
    basic_solver. }
  unfold W_ex.
  rewrite (sub_rmw SUB).
  subst.
  unfolder. ins. desf.
  eexists. splits; eauto.
  all: eapply E_E0; eauto.
  all: red.
  all: left; right.
  all: exists x; apply seq_eqv_r; split; [|split]; auto.
  eapply inclusion_step_cr; [reflexivity|]. by apply WF.(rmw_in_sb). }

assert (SB_S : dom_sb_S_rfrmw G (mkETC T S) (rf G ⨾ ⦗R_ex (lab G)⦘) (issued T) ⊆₁ S).
{ unfold dom_sb_S_rfrmw. 
  rewrite sub_sb_in; eauto.
  rewrite sub_rf_in; eauto.
  rewrite sub_R_ex; eauto.
  rewrite sub_rmw_in; eauto.
  apply ETCCOH. }
assert (RMWREX : dom_rel (rmw G) ⊆₁ (R_ex (lab G))).
{ rewrite sub_rmw_in; eauto.
  rewrite sub_R_ex; eauto.
  apply COMMON. }

assert (issued T ∪₁ S ∩₁ Tid_ thread ⊆₁ S) as IST_in_S.
{ generalize ETCCOH.(etc_I_in_S). unfold eissued. simpls.
  basic_solver. } 

assert (issued T ⊆₁ S) as I_in_S by apply ETCCOH.

exploit (@receptiveness_full thread state state'' new_val
                               new_rfi (E0 Gf T S thread \₁ D G T S thread)); auto.
{ clear -RMWRES. red in RMWRES. red. ins.
  red. apply RMWRES in IN. red in IN. desf. }
{ split; [|basic_solver].
  rewrite TEH''.(tr_acts_set).
  apply dom_helper_3.
  rewrite set_interC at 2. unfold new_rfi.
  rewrite delta_rfE. clear. basic_solver 10. }
{ apply dom_helper_3.
  unfold new_rfi. rewrite DELTA_RF_CERT.
  rewrite cert_rfE; auto. rewrite !seqA.
  rewrite cert_rfD; auto. rewrite !seqA.
  seq_rewrite <- !id_inter.
  rewrite set_interC with (s:=Tid_ thread) at 1.
  rewrite <- TEH''.(tr_acts_set).
  arewrite (acts_set (ProgToExecution.G state'') ∩₁  is_w (lab G) ≡₁
            is_w (lab (ProgToExecution.G state'')) ∩₁
            acts_set (ProgToExecution.G state'')).
  { split.
    all: intros x [AA BB]; split; auto.
    all: unfold is_w in *; rewrite TEH''.(tr_lab) in *; auto. }
  arewrite (is_r (lab G) ∩₁ acts_set (ProgToExecution.G state'') ≡₁
            is_r (lab (ProgToExecution.G state'')) ∩₁
            acts_set (ProgToExecution.G state'')).
  { split.
    all: intros x [AA BB]; split; auto.
    all: unfold is_r in *; rewrite TEH''.(tr_lab) in *; auto. }
  clear. basic_solver. }
{ unfold new_rfi. rewrite DELTA_RF_CERT.
  rewrite cert_rfE; auto. rewrite !seqA.
  rewrite cert_rfD; auto. rewrite !seqA.
  unfolder; ins; desc; subst thread.
  apply (@same_thread G) in H5; try done.
  2: { intro K; eapply init_w in K; try edone; type_solver. }
  destruct H5 as [X|Y].
  2: { unfold sb in Y; unfolder in Y; desf. }
  destruct X; [subst; type_solver|]. 
  exfalso.
  eapply Cert_coherence.hb_rf_irr with (G:=G); eauto.
  apply sb_in_hb in H1; unfolder; basic_solver 12. }
{ unfold new_rfi. rewrite delta_rfE.
  subst G; rewrite E_E0; try edone.
  clear. basic_solver 10. }
{ rewrite TEH''.(tr_acts_set).
unfold D; subst G; rewrite E_E0; try edone.
unfolder; ins; desf; splits; eauto.
destruct (classic (tid x = thread)); try done.
exfalso; apply H1; eauto 20. }
{ rewrite STATECOV. rewrite C_in_D. basic_solver. }
{ rewrite TEH''.(tr_rmw_dep).
  arewrite_id ⦗Tid_ thread⦘; rels.
  rewrite (@dom_frmw_in_D G _ _ S thread WF_G TCCOH_G); try done.
  basic_solver. }
{ rewrite TEH''.(tr_addr).
  arewrite_id ⦗Tid_ thread⦘; rels.
  rewrite (@dom_addr_in_D G _ _ S thread WF_G TCCOH_G); try done.
  basic_solver. }
{ rewrite TEH''.(tr_acts_set).
  unfolder; ins; desc.
  eapply H5; eauto.
  eapply Rex_in_D with (sc:=Gsc) (T:=T); try done.
  split; [|done].
  unfold R_ex, rmwmod in *.
  rewrite TEH''.(tr_lab) in H2; auto.
  eapply TEH''.(tr_acts_set). by split. }
{ rewrite TEH''.(tr_ctrl).
  arewrite_id ⦗Tid_ thread⦘; rels.
  rewrite (@dom_ctrl_in_D G _ _ S thread WF_G TCCOH_G); try done.
  basic_solver. }
{ rewrite TEH''.(tr_data).
  rewrite (dom_r (wf_dataE WF_G)).
  subst G.
  rewrite (E_E0 thread WF ETCCOH).
  unfolder; ins; desc.
  eapply H4; splits; eauto.
  intro.
  apply H6.
  apply (@dom_data_D (rstG Gf T S thread) Gsc T S thread WF_G); try done.
  basic_solver 12. }

ins; desc. 
set (lab' := fun x =>
               if excluded_middle_informative ((ProgToExecution.G s').(acts_set) x) 
               then s'.(ProgToExecution.G).(lab) x
               else G.(lab) x).
assert (same_lab_u2v_dom (ProgToExecution.G s').(acts_set)
                                 lab' (ProgToExecution.G s').(lab)) as SAME0.
{ red. ins. red. unfold lab'. desf. }

assert (same_lab_u2v_dom
          (ProgToExecution.G s').(acts_set)
          (ProgToExecution.G state'').(lab) G.(lab)) as SAME2.
{ unfold acts_set. rewrite <- RACTS.
  apply same_lab_u2v_dom_comm.
  eapply same_lab_u2v_dom_restricted; auto.
  apply TEH''. }
assert (same_lab_u2v_dom
          (ProgToExecution.G s').(acts_set) lab' G.(lab)) as SAME3.
{ eapply same_lab_u2v_dom_trans; eauto.
  eapply same_lab_u2v_dom_trans; eauto.
    by apply same_lab_u2v_follows_set. }

assert (same_lab_u2v lab' (lab G)) as SAME'.
{ red. red. ins.
  destruct (classic (acts_set (ProgToExecution.G s') e)) as [XX|XX].
  { by apply SAME3. }
  unfold lab'. desf. 
  red. desf. }

assert (thread_restricted_execution (certG G Gsc T S thread lab') thread
                                    (ProgToExecution.G s')) as YY.
{ constructor; auto.
  { rewrite cert_E.
    unfold acts_set. rewrite <- RACTS.
      by rewrite TEH''.(tr_acts_set). }
  { ins. unfold lab'. desf. }
  all: unfold certG; simpls.
  { rewrite <- RRMW. apply TEH''.(tr_rmw). }
  { rewrite <- RDATA. apply TEH''.(tr_data). }
  { rewrite <- RADDR. apply TEH''.(tr_addr). }
  { rewrite <- RCTRL. apply TEH''.(tr_ctrl). }
  rewrite <- RFAILRMW. apply TEH''.(tr_rmw_dep). }

assert (delta_rf ≡ new_rfi ∪ new_rfe) as NEWRF_SPLIT.
{ arewrite (delta_rf ≡ delta_rf ⨾ ⦗ Tid_ thread ⦘).
  2: { unfold new_rfi, new_rfe. 
       rewrite <- seq_union_l. rewrite <- id_union.
       arewrite (Tid_ thread ∪₁ NTid_ thread ≡₁ fun _ => True).
       2: { clear. basic_solver. }
       split; [basic_solver|].
       intros x _. red. by destruct (classic (tid x = thread)); [left|right]. }
  split; [|clear; basic_solver].
  cut (codom_rel delta_rf ⊆₁ Tid_ thread).
  { clear. basic_solver 21. }
  rewrite delta_rfE at 1; try done.
  unfold D.
  unfolder; ins; desf.
  destruct (classic (tid x = thread)); [done|].
  exfalso; eapply H4. do 5 left. by right. }

assert (forall r w : actid, delta_rf w r -> val lab' w = val lab' r)
  as SAME_VAL_RF.
{ intros r w NEWRF.
  apply NEWRF_SPLIT in NEWRF. destruct NEWRF as [NEWRF|NEWRF].
  { set (VV := NEWRF). apply NEW_VAL1 in VV.
    unfold new_rfi in NEWRF.
    apply seq_eqv_l in NEWRF. destruct NEWRF as [TIDW NEWRF].
    apply seq_eqv_r in NEWRF. destruct NEWRF as [NEWRF TIDR].
    apply delta_rfE in NEWRF; auto.
    apply seq_eqv_l in NEWRF. destruct NEWRF as [GEW NEWRF].
    apply seq_eqv_r in NEWRF. destruct NEWRF as [NEWRF [GER MOD]].
    assert (s'.(ProgToExecution.G).(acts_set) r) as ERR.
    { unfold acts_set. rewrite <- RACTS. apply TEH''.(tr_acts_set).
      split; auto. }
    assert (s'.(ProgToExecution.G).(acts_set) w) as EWW.
    { unfold acts_set. rewrite <- RACTS. apply TEH''.(tr_acts_set).
      split; auto. }
    unfold lab', val.
    destruct (excluded_middle_informative (acts_set (ProgToExecution.G s') w)) as [HH1|HH1].
    2: by desf.
    destruct (excluded_middle_informative (acts_set (ProgToExecution.G s') r)) as [HH2|HH2].
    2: by desf.
    symmetry. apply VV. }
  assert (NEWRF0 := NEWRF).
  unfold new_rfe in NEWRF.
  apply seq_eqv_l in NEWRF. destruct NEWRF as [TIDW NEWRF].
  apply seq_eqv_r in NEWRF. destruct NEWRF as [NEWRF TIDR].
  apply delta_rfE in NEWRF; auto.
  apply seq_eqv_l in NEWRF. destruct NEWRF as [GEW NEWRF].
  apply seq_eqv_r in NEWRF. destruct NEWRF as [NEWRF [GER MOD]].
  unfold val, lab'.
  destruct (excluded_middle_informative (acts_set (ProgToExecution.G s') w)) as [HH1|HH1].
  { exfalso. unfold acts_set in HH1. rewrite <- RACTS in HH1.
    apply TEH''.(tr_acts_set) in HH1. destruct HH1 as [_ HH1]. desf. }
  destruct (excluded_middle_informative (acts_set (ProgToExecution.G s') r)) as [HH2|HH2].
  2: { exfalso. apply HH2.
       unfold acts_set. rewrite <- RACTS. apply TEH''.(tr_acts_set).
       split; auto. }
  apply delta_rfD in NEWRF.
  apply seq_eqv_l in NEWRF. destruct NEWRF as [WW NEWRF].
  apply seq_eqv_r in NEWRF. destruct NEWRF as [NEWRF RR].

  assert (V: match lab (ProgToExecution.G s') r with
             | Aload _ _ _ v | Astore _ _ _ v => Some v
             | Afence _ => None
             end = val (lab (ProgToExecution.G s')) r).
  { by unfold val. }
  rewrite V; erewrite NEW_VAL2.
  { specialize (new_rfe_unique r).
    unfold unique in new_rfe_unique; desc.
    specialize (H0 r).
    assert (x = (new_value r)) by auto; subst x.
    assert (NWW: new_value r =w).
    { eapply new_rfe_unique0.
        by unfold new_rfe_ex; basic_solver. }
    subst w.
    clear -WW. 
    unfold new_val, get_val.
    unfold is_w, val in *. desf. }
  { eapply same_lab_u2v_dom_is_r.
    2: { split.
         { apply HH2. }
         eauto. }
    eapply same_lab_u2v_dom_trans.
    2: by apply SAME2.
    red. ins. by apply SAME. }
  { split; auto. rewrite H in GER.
    eapply E_E0 in GER; eauto. }
  unfold new_rfi. intros [z NEWRFI].
  apply seq_eqv_l in NEWRFI. destruct NEWRFI as [TIDZ NEWRFI].
  apply seq_eqv_r in NEWRFI. destruct NEWRFI as [NEWRFI _].
  assert (z = w) as XX.
  2: by desf.
  eapply cert_rff.
  4: { red; eauto. }
  all: eauto.
  all: eapply DELTA_RF_CERT; eauto. }

assert (forall a : actid, ~ (acts_set G \₁ D G T S thread) a -> val lab' a = val (lab G) a)
  as SAME_VAL.
{ intros a ZZ.
  unfold val, lab'.
  destruct (excluded_middle_informative (acts_set (ProgToExecution.G s') a)) as [MM|MM].
  2: done.
  assert (~ (E0 Gf T S thread \₁ D G T S thread) a) as XX.
  { intros [AA BB]. apply ZZ. split; auto.
    rewrite H. eapply E_E0; eauto. }
  specialize (OLD_VAL a XX). clear XX.
  unfold val in OLD_VAL. rewrite OLD_VAL.
  rewrite TEH''.(tr_lab); auto. 
  unfold acts_set. by rewrite RACTS. }

assert (forall r w : actid, (cert_rf G Gsc T S thread) w r ->
                            val lab' w = val lab' r)
  as SAME_VAL_RF_CERT.
{ intros r w HH. destruct HH as [[HH|HH]|HH].
  2,3: apply SAME_VAL_RF; unfold delta_rf; generalize HH.
  2,3: clear; basic_solver 10.
  erewrite !SAME_VAL.
  2,3: intros [_ AA]; apply AA.
  3: { eapply dom_rf_D; eauto. eexists; eauto. }
  2: { generalize HH. clear. basic_solver. }
  apply wf_rfv; auto. generalize HH. clear. basic_solver. }

assert (forall b (ISSB : issued T b), val lab' b = val Gf.(lab) b) as ISS_OLD.
{ ins. rewrite <- lab_G_eq_lab_Gf.
  rewrite SAME_VAL; auto.
  intros [_ HH]. apply HH. by apply I_in_D. }

assert (acts_certG_in_acts_Gf : acts_set (certG G Gsc T S thread lab') ⊆₁ acts_set Gf).
{ by unfold certG. }

assert (dom_rel (⦗W_ex G ∩₁ (is_xacq (lab G))⦘ ⨾ sb G ⨾ ⦗S⦘) ⊆₁ issued T) as XACQ_I.
{ rewrite sub_sb_in; eauto.
  rewrite sub_xacq; eauto.
  rewrite sub_W_ex_in; eauto.
  apply ETCCOH. }

assert (dom_rel (rmw G ⨾ ⦗S⦘) ⊆₁ codom_rel (rf G)) as COMP_RMW_S.
{ subst G. eapply COMP_RMW_S; eauto. }

assert ((cert_rf G Gsc T S thread ⨾ rmw G) ⨾ ⦗issued T ∪₁ S ∩₁ Tid_ thread⦘ ⊆
        rf Gf ⨾ rmw Gf) as RFRMW_IST_IN.
{ rewrite IST_in_S. rewrite seqA.
  rewrite cert_rmw_S_in_rf_rmw_S; auto.
  rewrite sub_rf_in; eauto.
  rewrite sub_rmw_in; eauto.
  clear. basic_solver. }

assert ((cert_rf G Gsc T S thread ⨾ rmw G) ⨾ ⦗issued T⦘ ⊆ rf Gf ⨾ rmw Gf) as RFRMW_IN.
{ arewrite (issued T ⊆₁ issued T ∪₁ S ∩₁ Tid_ thread). by rewrite <- seqA. }

assert (ISTex_rf_I :
          (issued T ∪₁ S ∩₁ Tid_ thread) ∩₁ W_ex G ⊆₁ codom_rel (⦗issued T⦘ ⨾ rf G ⨾ rmw G)).
{ assert ((issued T ∪₁ S ∩₁ Tid_ thread) ∩₁ W_ex G ⊆₁ S ∩₁ W_ex Gf) as AA.
  { rewrite I_in_S. subst. unfold rstG, restrict, W_ex. simpls.
    clear. basic_solver. }
  intros x HH.
  subst. unfold rstG, restrict, W_ex. simpls.
  set (BB:=HH). apply AA in BB.
  apply ETCCOH in BB. destruct BB as [y BB]. apply seq_eqv_l in BB.
  destruct BB as [IY [z [BB CC]]].
  exists y. apply seq_eqv_l. split; auto.
  exists z.
  assert (E0 Gf T S thread y) as E0Y.
  { red. do 2 left. by right. }
  assert (E0 Gf T S thread x) as E0X.
  { destruct HH as [_ HH]. unfold rstG, restrict, W_ex in HH. simpls.
    generalize HH. clear. basic_solver. }
  assert (E0 Gf T S thread z) as E0Z.
  2: by split; apply seq_eqv_lr; splits.
  destruct HH as [DD HH].
  assert (S x) as SX.
  { destruct DD as [|DD]; [|by apply DD].
      by apply ETCCOH.(etc_I_in_S). }
  destruct (classic (Tid_ thread x)) as [TID|NTID].
  { red. left. right. exists x. apply seq_eqv_r. split.
    2: by split.
    right. by apply rmw_in_sb. }
  destruct DD as [|DD]; eauto.
  { right. exists x. apply seq_eqv_r. split; [|split]; auto. }
  exfalso. apply NTID. apply DD. }
assert (DOM_SB_S_rf_I :
          dom_rel (sb G ⨾ ⦗issued T ∪₁ S ∩₁ Tid_ thread⦘)
                  ∩₁ codom_rel (⦗issued T⦘ ⨾ rf G ⨾ ⦗R_ex G.(lab)⦘ ⨾ rmw G) ⊆₁
                  issued T ∪₁ S ∩₁ Tid_ thread).
{ rewrite rmw_W_ex. rewrite (dom_r WF_G.(wf_rmwE)).
  rewrite <- !seqA. rewrite !codom_eqv1.
  rewrite !seqA.

  arewrite (R_ex G.(lab) ⊆₁ R_ex Gf.(lab)).
  { subst G. unfold rstG, restrict. simpls. }

  rewrite sub_rf_in; eauto.
  rewrite sub_rmw_in; eauto.
  rewrite sub_sb_in; eauto.
  arewrite (dom_rel (sb Gf ⨾ ⦗issued T ∪₁ S ∩₁ Tid_ thread⦘) ⊆₁
                    dom_rel (sb Gf ⨾ ⦗issued T ∪₁ S ∩₁ Tid_ thread⦘) ∩₁
                    dom_rel (sb Gf ⨾ ⦗S⦘)).
  { generalize IST_in_S. clear. basic_solver 10. }
  rewrite <- !set_interA. rewrite set_interC with (s':=W_ex G).
  rewrite <- !set_interA. rewrite set_interC with (s':=acts_set G).
  rewrite !set_interA.

  forward (eapply ETCCOH.(etc_sb_S)); intro AA1.
  unfold dom_sb_S_rfrmw in AA1.
  simpl in AA1.
  unfold eissued in AA1; simpl in AA1.
  rewrite !seqA in AA1.
  rewrite AA1.
  rewrite <- !set_interA. rewrite WF_G.(W_ex_in_W).

  simpls.
  intros x [[HH AA] SX].
  destruct (classic (issued T x)) as [|NISS]; [by left|].
  destruct (classic (Tid_ thread x)) as [|NTID]; [by right; split|].
  exfalso.
  apply IT_new_co in HH. destruct HH as [HH|[_ HH]]; desf. }

exists (certG G Gsc T S thread lab').
exists Gsc.
exists (mkTC (T.(covered) ∪₁ (G.(acts_set) ∩₁ NTid_ thread)) T.(issued)).
exists (T.(issued) ∪₁ S ∩₁ Tid_ thread).

assert (Wf (certG G Gsc T S thread lab')) as WF_CERT.
{ eapply WF_cert; eauto. }
assert (wf_sc (certG G Gsc T S thread lab') Gsc) as WF_SC_CERT.
{ eapply WF_SC_cert; eauto. }

assert (acts_set G ∩₁ (fun a : actid => is_f (lab G) a) ⊆₁
                 (fun a : actid => is_ra (lab G) a)) as FACQREL.
{ rewrite acts_G_in_acts_Gf.
  rewrite lab_G_eq_lab_Gf. apply SIMREL. }

splits; auto.
{ apply cert_imm_consistent; auto. }
{ unfold certG, acts_set; ins; basic_solver. }
cdes SIMREL. cdes COMMON.

red. splits.
{ red. splits; eauto; simpls; try by apply SIMREL.
  { erewrite same_lab_u2v_is_rlx; eauto.
    rewrite cert_E. rewrite acts_G_in_acts_Gf.
    rewrite lab_G_eq_lab_Gf. apply SIMREL. }
  { erewrite same_lab_u2v_is_ra; eauto.
    rewrite cert_E, cert_F; eauto. }
  { by apply ETCCOH_cert. }
  { erewrite same_lab_u2v_is_rel; eauto.
    erewrite same_lab_u2v_is_w; eauto.
    rewrite RELCOV_G. basic_solver. }
  { ins.
    assert (acts_set G r) as ER.
    { apply (dom_l WF_G.(wf_rmwE)) in RMW. apply seq_eqv_l in RMW. desf. }
    assert (acts_set G w) as EW.
    { apply (dom_r WF_G.(wf_rmwE)) in RMW. apply seq_eqv_r in RMW. desf. }
    set (RMW' := RMW).
    apply rmw_G_rmw_Gf in RMW'.
    apply seq_eqv_l in RMW'. destruct RMW' as [EER RMW'].
    apply seq_eqv_r in RMW'. destruct RMW' as [RMW' EEW].
    assert (tid r = tid w) as TIDRW.
    { by apply WF.(wf_rmwt). }
    split; (intros [COVV|[ACTS NTID]]; [by left; apply (RMWCOV r w)|]).
    all: right; split; [auto|by generalize NTID; rewrite TIDRW]. }
  { red. splits.
    1,2: by (intros x [AA BB]; apply FCOH; split; auto).
    { intros x HH AA. apply FCOH; auto. }
    { ins. apply FCOH.
      1,2: by apply IST_in_S.
      assert ((cert_co G T S thread ⨾ ⦗cert_co_base G T S thread⦘) x y) as HH.
      { apply seq_eqv_r. split; auto. apply IST_in_cert_co_base; auto. }
      eapply cert_co_I in HH; eauto.
      apply seq_eqv_r in HH. destruct HH as [HH _].
      eapply (sub_co SUB) in HH.
      apply seq_eqv_l in HH. destruct HH as [_ HH].
      apply seq_eqv_r in HH. desf. }
    ins. apply FCOH; auto.
    apply RFRMW_IST_IN. apply seq_eqv_r. split; auto. }
  { intros _.
    erewrite same_lab_u2v_is_sc; eauto.
    erewrite same_lab_u2v_is_f; eauto.
    unfold certG, acts_set. simpls.
    rewrite H.
    arewrite ((fun x => In x (acts (rstG Gf T S thread))) ⊆₁
              (acts_set (rstG Gf T S thread))).
    erewrite E_F_Sc_in_C; eauto.
    basic_solver. }
  { rewrite same_lab_u2v_R_ex; eauto. }
  splits.
  { subst G.
    erewrite <- cert_co_for_split with (G:=rstG Gf T S thread); eauto.
    unfold cert_co_base.
    hahn_frame. apply eqv_rel_mori.
    apply AuxRel.set_compl_mori. red.
      by erewrite Grfi_in_cert_rfi with (G:=rstG Gf T S thread); eauto. }
  subst G. unfold W_ex. rewrite cert_sb. unfold certG. simpls.
  rewrite <- seqA, codom_eqv1.
  arewrite (codom_rel (⦗E0 Gf T S thread⦘ ⨾ rmw Gf) ⊆₁ is_w Gf.(lab)).
  { rewrite WF.(wf_rmwD). basic_solver. }
  (* TODO: introduce a lemma *)
  arewrite (E0 Gf T S thread ⊆₁ E0 Gf T S thread ∩₁ E0 Gf T S thread).
  rewrite <- set_interA.
  unfold E0 at 1. rewrite !set_inter_union_r, !set_inter_union_l.
  unionL.
  4: { rewrite WF.(wf_rmwD). type_solver 10. }
  { rewrite w_covered_issued; eauto. basic_solver 10. }
  { basic_solver 10. }
  unfold sb. unfold rstG, restrict.
  arewrite (Tid_ thread ∩₁ S ⊆₁ Tid_ thread ∩₁ S ∩₁ E0 Gf T S thread).
  { assert (Tid_ thread ∩₁ S ⊆₁ E0 Gf T S thread) as AA.
    { unfold E0. basic_solver 10. }
    generalize AA. basic_solver. }
  clear.
  unfolder. ins. desf; eexists; eauto.
  unfold acts_set; simpls. splits; [|by eauto].
  right. splits; auto.
  all: apply in_filterP_iff; splits; auto. }
red. splits.
eexists. eexists. splits; auto.
{ apply GPC. }
all: eauto.
{ red. ins. eapply SIM_PROM in PROM. (* sim_prom *) 
  desc. exists b. splits; auto.
  { unfold certG. unfold acts_set. simpls.
    rewrite H. unfold rstG, restrict. simpls.
    apply in_filterP_iff. split; auto.
    red. left. left. by right. }
  { intros [HH|[_ HH]]; desf. }
  { erewrite same_lab_u2v_loc; eauto.
      by rewrite <- lab_G_eq_lab_Gf. }
  cdes HELPER.
  red. splits; auto.
  { unfold certG; simpls.
    rewrite ISS_OLD; auto. }
  intros ll. specialize (SIMMSG ll).
  eapply max_value_same_set; eauto.
  split; (intros x [AA|AA]; [left|right]).
  4: { erewrite <- same_lab_u2v_loc in AA; eauto.
       rewrite <- lab_G_eq_lab_Gf; eauto. }
  2: { erewrite same_lab_u2v_loc in AA; eauto.
       rewrite <- lab_G_eq_lab_Gf; eauto. }
  { assert ((msg_rel Gf sc ll ⨾ ⦗ issued T ⦘) x b) as XX.
    2: { apply seq_eqv_r in XX. desf. }
    eapply msg_rel_I; eauto.
    eapply cert_msg_rel with (lab':=lab'); eauto.
    { by rewrite <- H. }
    all: rewrite <- H; eauto.
    all: try by unfold rst_sc; rewrite <- HeqGsc.
    apply seq_eqv_r. split; auto.
    unfold rst_sc. by rewrite <- HeqGsc. }
  assert ((msg_rel (certG G Gsc T S thread lab') Gsc ll ⨾ ⦗ issued T ⦘) x b) as XX.
  2: { apply seq_eqv_r in XX. desf. }
  rewrite HeqGsc. rewrite H.
  eapply cert_msg_rel; eauto.
  all: rewrite <- H; auto.
  all: try by rewrite <- HeqGsc; auto.
  rewrite H.
  eapply msg_rel_I; eauto.
  apply seq_eqv_r. split; auto. }
{ red. ins. (* sim_res_prom *)
  eapply SIM_RPROM in RES.
  desc.
  assert (acts_set Gf b) as FEB.
  { by apply ETCCOH.(etc_S_in_E). }
  assert (acts_set G b) as EB.
  { subst. eapply ST_in_E; eauto. by split. }

  (* assert (~ issued T b /\ (S ∩₁ Tid_ thread) b) as [NIB SB]. *)
  (* { apply seq_eqv_lr in RFRMWS. unfolder in RFRMWS. desf. } *)
  (* set (AA:=RFRMWS). *)
  (* apply seq_eqv_lr in AA. destruct AA as [_ [RFIRMW SB']]. *)
  (* assert (~ is_init b) as NINITB. *)
  (* { intros AA. apply NIB. eapply init_issued with (G:=Gf); eauto. *)
  (*   split; auto. } *)
  (* assert (same_tid b b') as STT. *)
  (* { eapply WF.(ninit_rfi_rmw_rt_same_tid). *)
  (*   apply seq_eqv_l. by split. } *)

  (* assert (acts_set G b') as EB'. *)
  (* { subst. eapply ST_in_E; eauto. split; apply SB'. } *)

  (* destruct NOBEF as [w HH]. apply seq_eqv_l in HH. destruct HH as [IW RFRMW]. *)
  (* destruct RFRMW as [r [RF RMW]]. *)

  (* assert (acts_set G r) as ER. *)
  (* { subst. eapply dom_sb_TS_in_E; eauto. *)
  (*   exists b. apply seq_eqv_r. split. *)
  (*   2: by split; apply SB. *)
  (*   eapply inclusion_step_cr; [done|]. *)
  (*     by apply WF.(rmw_in_sb). } *)

  (* assert (rmw G r b) as GRMW. *)
  (* { subst. unfold rstG, restrict. simpls. *)
  (*   apply seq_eqv_lr. splits; auto. *)
  (*   all: eapply E_E0; eauto. } *)
  (* assert (D G T S thread r) as DR. *)
  (* { apply dom_rppo_S_in_D. exists b. *)
  (*   apply seq_eqv_r. split; [|by apply SB]. *)
  (*   apply rmw_in_rppo; auto. } *)

  exists b. splits; auto.
  { right. by split. }
  erewrite same_lab_u2v_loc in LOC; eauto.
  rewrite <- lab_G_eq_lab_Gf; eauto.
    by apply same_lab_u2v_comm. }
{ red. ins. (* sim_mem *)
  edestruct SIM_MEM with (b:=b) as [rel_opt]; eauto.
  { erewrite same_lab_u2v_loc in LOC; eauto.
    rewrite <- lab_G_eq_lab_Gf; eauto. }
  { rewrite <- ISS_OLD; auto. apply VAL. }
  simpls. desc.
  exists rel_opt.
  splits; eauto.
  { red. cdes HELPER. splits; eauto.
    intros ll. specialize (SIMMSG ll).
    eapply max_value_same_set; eauto.
    split; (intros x [AA|AA]; [left|right]).
    4: { erewrite <- same_lab_u2v_loc in AA; eauto.
         rewrite <- lab_G_eq_lab_Gf; eauto. }
    2: { erewrite same_lab_u2v_loc in AA; eauto.
         rewrite <- lab_G_eq_lab_Gf; eauto. }
    { assert ((msg_rel Gf sc ll ⨾ ⦗ issued T ⦘) x b) as XX.
      2: { apply seq_eqv_r in XX. desf. }
      eapply msg_rel_I; eauto.
      eapply cert_msg_rel with (lab':=lab'); eauto.
      { by rewrite <- H. }
      all: rewrite <- H; eauto.
      all: try by unfold rst_sc; rewrite <- HeqGsc.
      apply seq_eqv_r. split; auto.
        by unfold rst_sc; rewrite <- HeqGsc. }
    assert ((msg_rel (certG G Gsc T S thread lab') Gsc ll ⨾ ⦗ issued T ⦘) x b) as XX.
    2: { apply seq_eqv_r in XX. desf. }
    rewrite HeqGsc. rewrite H.
    eapply cert_msg_rel; eauto.
    all: rewrite <- H; auto.
    all: try by rewrite <- HeqGsc; auto.
    rewrite H.
    eapply msg_rel_I; eauto.
    apply seq_eqv_r. split; auto. }
  rename H1 into UU.
  intros UU1 UU2.
  destruct UU as [AA BB]; auto.
  { intros HH. apply UU2. by left. }
  splits; auto. red in BB. desc.
  exists p_rel. splits; auto.
  destruct BB0; desc; [left|right].
  { split; auto.
    intros HH. apply NINRMW.
    destruct HH as [z HH]. apply seq_eqv_l in HH. desc.
    exists z. apply seq_eqv_l. split; auto.
    apply RFRMW_IN. apply seq_eqv_r. by split. }
  exists p. splits; eauto.
  { destruct INRMW as [z [RF RMW]].
    assert ((E0 Gf T S thread) z).
    { unfold E0; left; right; exists b.
      generalize (rmw_in_sb WF); basic_solver 12. }
    assert ((E0 Gf T S thread) b).
    { unfold E0; left; left; right; basic_solver 12. }
    assert ((E0 Gf T S thread) p).
    { unfold E0; left; left; right; basic_solver 12. }
    assert (G.(rmw) z b).
    apply rmw_G_rmw_Gf; basic_solver 12.
    exists z; splits; [|done].
    cut ((cert_rf G Gsc T S thread ⨾ ⦗D G T S thread⦘) p z).
    { clear. basic_solver. }
    apply cert_rf_D; auto. apply seq_eqv_r. split; auto.
    { subst G. unfold rstG. unfold restrict. ins.
      apply seq_eqv_lr. splits; auto. }
    eapply dom_rmw_D; eauto. exists b.
    apply seq_eqv_r. split; auto. by apply I_in_D. }
  exists p_v. splits; eauto.
  rewrite ISS_OLD; auto. }
{ red. ins.
  assert (loc (lab Gf) b = Some l) as AA.
  { rewrite <- LOC. symmetry.
    erewrite same_lab_u2v_loc; eauto.
      by rewrite <- lab_G_eq_lab_Gf. }
  apply SIM_RES_MEM; auto. }
{ red. splits; red; ins. (* sim_tview *)
  { assert
      (t_cur (certG G Gsc T S thread lab') Gsc thread l
             (covered T ∪₁ acts_set G ∩₁ NTid_ thread) ≡₁
             t_cur Gf sc thread l (covered T)) as XX.
    2: { eapply max_value_same_set; eauto. apply SIM_TVIEW. }
    
    rewrite cert_t_cur_thread; try done.
    arewrite (Gsc ≡ (rst_sc Gf sc T S thread)).
    {  by unfold rst_sc; rewrite <- HeqGsc. }
    subst; eapply t_cur_thread; try done. }

  { assert
      (t_acq (certG G Gsc T S thread lab') Gsc thread l
             (covered T ∪₁ acts_set G ∩₁ NTid_ thread) ≡₁
             t_acq Gf sc thread l (covered T)) as XX.
    2: { eapply max_value_same_set; eauto. apply SIM_TVIEW. }

    rewrite cert_t_acq_thread; try done.
    arewrite (Gsc ≡ (rst_sc Gf sc T S thread)).
    { by unfold rst_sc; rewrite <- HeqGsc. }
    subst; eapply t_acq_thread; try done. }

  assert (t_rel (certG G Gsc T S thread lab') Gsc thread l l'
                (covered T ∪₁ acts_set G ∩₁ NTid_ thread) ≡₁
                t_rel Gf sc thread l l' (covered T)) as XX.
  { rewrite cert_t_rel_thread; try done.
    arewrite (Gsc ≡ (rst_sc Gf sc T S thread)).
    { by unfold rst_sc; rewrite <- HeqGsc. }
    subst; eapply t_rel_thread; try done. }

  cdes SIM_TVIEW.
  eapply max_value_same_set.
  { by apply REL. }
  apply set_equiv_union; auto.
  destruct (Loc.eq_dec l l'); [|done].
  erewrite same_lab_u2v_loc; eauto.
  erewrite same_lab_u2v_is_w; eauto.
  rewrite <- lab_G_eq_lab_Gf; eauto. 
  unfold tid. basic_solver 10. }
red. splits. (* sim_state *)
{ ins. split.
  2: { intros HH. left. by apply PCOV. }
  intros [HH|[_ HH]]; simpls.
    by apply PCOV. }
eexists. red. splits.
{ apply STEPS'. }
{ intros HH. inv HH. }
done.
Unshelve. clear; eapply (fun _ => Afence Orel).
Qed.

End Cert.
