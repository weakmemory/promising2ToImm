Require Import Arith.
Require Import Lia.
From hahn Require Import Hahn.
Require Import PromisingLib.
From imm Require Import AuxRel2.

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
From imm Require Import FairExecution.
From imm Require Import FinExecution.
From imm Require Import SubExecution. 
From imm Require Import ThreadBoundedExecution.

From imm Require Import RMWinstrProps.
Require Import promise_basics.PromiseLTS.
From Promising2 Require Import Memory.
Require Import lib.MemoryAux.

Require Import Cert_views.
Require Import Cert_rf.
Require Import Cert_tc.
Require Import Cert_ar.
Require Import Cert_co.
Require Import Cert_D.
Require Import CertT.
Require Import CertExecution2.
Require Import MaxValue.
Require Import ViewRel.
Require Import SimulationRel.
Require Import SimState.
Require Import ExtTraversalConfig.
Require Import CertExecution1.
Require Import ExtTraversalProperties.
Require Import FinTravConfigs. 

Require Import IndefiniteDescription.

From Promising2 Require Import Configuration Local.
From imm Require Import TLSCoherency.
From imm Require Import IordCoherency.
From imm Require Import TraversalOrder. 
Require Import TlsEventSets.
Require Import AuxRel. 
Require Import EventsTraversalOrder.

(* TODO: move*)
Global Add Parametric Morphism : iord_coherent with signature
       eq ==> Basics.flip inclusion ==> set_equiv ==> Basics.impl as iord_coherent_mori.
Proof using.
  intros G sc sc' EQ s s' EQS.
  unfold iord_coherent. red. 
  intros HH.
  by rewrite EQ, <- EQS. 
Qed.

Set Implicit Arguments.

Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'NTid_' t" := (fun x => tid x <> t) (at level 1).


Definition mkCT (G: execution) (T: trav_label -> Prop) (t1 t2: thread_id) :=
  E0 G T t1 ∩₁ Tid_ t2.


Lemma rstG_fair G T thread (FAIR: mem_fair G):
  mem_fair (rstG G T thread).
Proof using.
  unfold rstG. by apply restrict_fair.
Qed.


Lemma tid_is_init_fin_helper (S: actid -> Prop) thread
      (NT: thread <> tid_init)
      (FIN: set_finite (S \₁ is_init)):
  set_finite (S ∩₁ Tid_ thread).
Proof using. 
  rewrite AuxRel.set_split_comlete with (s := is_init).
  apply set_finite_union. split.
  { eapply set_finite_mori; [| by apply set_finite_empty].
    red. unfolder. ins. desc. vauto. by destruct x. }
  eapply set_finite_mori; [| by apply FIN].
  red. basic_solver.
Qed. 


Lemma codom_seq_eqv_r {A: Type} (r: relation A) (S: A -> Prop):
  codom_rel (r ⨾ ⦗S⦘) ⊆₁ S. 
Proof using. basic_solver. Qed.

Section CertGraphInit.
  Variable (Gf: execution) (sc: relation actid) (T: trav_label -> Prop).
  Variable (PC: Configuration.Configuration.t). 
  Variable (f_to f_from: actid -> Time.Time.t). 
  Variable (thread: thread_id).
  Variable (b: thread_id). 

  Hypothesis (WF: Wf Gf).
  Hypothesis (FAIRf: mem_fair Gf).
  Hypothesis (IMMCON : imm_consistent Gf sc).
  Hypothesis (SIMREL : simrel_thread Gf sc PC T f_to f_from thread sim_normal).

  Hypothesis (TLS_FIN: tls_fin T).

  Hypothesis (Gf_THREADS_BOUND: threads_bound Gf b).

  Definition G := rstG Gf T thread.
  Definition Gsc := ⦗E0 Gf T thread⦘ ⨾ sc ⨾ ⦗E0 Gf T thread⦘.

  Lemma thread_ninit: thread <> tid_init.
  Proof using SIMREL. cdes SIMREL. cdes LOCAL. auto. Qed.
  
  (* TODO: move to lib *)
  Lemma fin_dom_rel_cr_fsupp {A: Type} (r: relation A) (S: A -> Prop)
        (FIN: set_finite S) (FS: fsupp r):
    set_finite (dom_rel (r^? ⨾ ⦗S⦘)). 
  Proof using. rewrite crE. relsf. split; auto. by apply fin_dom_rel_fsupp. Qed. 

  Lemma CT_fin t1 t2:
    set_finite (mkCT Gf T t1 t2 \₁ is_init).
  Proof using WF TLS_FIN.
    unfold mkCT, E0.
    rewrite !set_inter_union_l, !set_minus_union_l.
    rewrite set_unionA. do 2 rewrite set_finite_union. splits.
    { eapply set_finite_mori; [| apply tls_fin_event_set with (a := ta_cover)].
      all: red; basic_solver 10. } 
    { eapply set_finite_mori; [| apply tls_fin_event_set with (a := ta_issue)].
      all: red; basic_solver 10. }
    eapply set_finite_mori with (x := dom_rel (⦗set_compl is_init⦘ ⨾ (sb Gf)^? ⨾ ⦗(event ↑₁ (T ∩₁ action ↓₁ (eq ta_reserve ∪₁ eq ta_issue))) \₁ is_init⦘)).
    { red.
      
do 2 (rewrite eqv_rel_mori with (x := _ ∩₁ _); [| intro; apply proj2]).
      do 2 (rewrite set_minus_mori with (x := _ ∩₁ _); [| intro; apply proj1| red; apply set_subset_refl2]).
      do 2 (rewrite set_minusE, set_interC, <- dom_eqv1).
      rewrite <- dom_union. apply dom_rel_mori.
      rewrite rmw_in_sb; auto. rewrite inclusion_step_cr with (r := sb Gf) at 2.
      2: { reflexivity. }
      rewrite <- !seq_union_r.
      assert (domb (⦗set_compl is_init⦘ ⨾ (sb Gf)^?) (set_compl is_init)) as D%domb_helper.
      { apply seq_r_domb; [basic_solver| ].
        rewrite no_sb_to_init; basic_solver. } 
      sin_rewrite D. hahn_frame.
      unfold reserved, issued. basic_solver 10. }
    rewrite crE. relsf. split.
    { eapply set_finite_mori; [red; intro; apply proj2| ].
      rewrite set_map_union. relsf. split; by apply tls_fin_event_set. }
    rewrite <- dom_eqv1. 
    rewrite <- seqA. apply fin_dom_rel_fsupp.
    { rewrite set_map_union. relsf. split; by apply tls_fin_event_set. }
    by apply fsupp_sb.
  Qed. 
     
  Lemma G_threads_bound: threads_bound G b.
  Proof using Gf_THREADS_BOUND. by apply restrict_threads_bound. Qed. 
  
  Lemma G_fin: fin_exec G.
  Proof using WF Gf_THREADS_BOUND TLS_FIN.
    unfold G, certG, rstG.
    eapply fin_exec_bounded_threads; eauto.
    { apply G_threads_bound. }
    ins. unfold restrict, fin_exec. simpl.
    eapply set_finite_mori.
    2: { by apply CT_fin with (t1 := thread) (t2 := t). }
    red. simpl. unfold mkCT. basic_solver 10.
  Qed.
  Hint Resolve G_fin: core.

  Lemma FAIR: mem_fair G.
  Proof using FAIRf. forward eapply (rstG_fair); eauto. Qed.

  Lemma WF_SC: wf_sc Gf sc. 
  Proof using IMMCON. by apply IMMCON. Qed.

  Lemma TCOH:
    tls_coherent Gf T. 
  Proof using SIMREL. by cdes SIMREL; cdes COMMON. Qed.
  
  Lemma ICOH:
    iord_coherent Gf sc T. 
  Proof using SIMREL. by cdes SIMREL; cdes COMMON. Qed.
  
  Lemma RCOH:
    reserve_coherent Gf T. 
  Proof using SIMREL. by cdes SIMREL; cdes COMMON. Qed.
  
  Lemma RELCOV:
    (fun a => is_w (lab Gf) a) ∩₁ (fun a : actid => is_rel (lab Gf) a) ∩₁ issued T
                            ⊆₁ covered T.
  Proof using SIMREL. by cdes SIMREL; cdes COMMON. Qed.

  Hint Resolve FAIR TCOH ICOH RCOH WF_SC RELCOV: core.

  Lemma SUB: sub_execution Gf G sc Gsc. 
  Proof using WF SIMREL.
    unfold rstG in *; subst.
    apply restrict_sub; eauto.  
    rewrite <- E_E0, E_E0, E0_in_Gf; auto. 
  Qed. 
  
  Lemma WF_G: Wf G.
  Proof using WF SIMREL. unfold G; eapply rstWF; eauto. Qed. 

  Lemma WF_SC_G: wf_sc G Gsc.
  Proof using IMMCON WF SIMREL. unfold G; eapply WF_SC_rst; eauto. Qed. 

  Lemma RELCOV_G: is_w (lab G) ∩₁ is_rel (lab G) ∩₁ (issued T) ⊆₁ (covered T).
  Proof using IMMCON WF SIMREL.
    rewrite (sub_W SUB), (sub_Rel SUB). eauto.  
  Qed. 

  Lemma RMWCOV: forall r w, rmw Gf r w -> covered T r <-> covered T w.
  Proof using SIMREL. by apply SIMREL. Qed.

  Hint Resolve SUB WF_G WF_SC_G RELCOV_G RMWCOV: core.

  (* Lemma TCCOH_G: tc_coherent G Gsc T.  *)
  (* Proof using WF IMMCON SIMREL. subst; eapply TCCOH_rst; eauto. Qed.  *)

  (* (* TODO: probably not true *) *)
  (* Lemma TCOH_G: tls_coherent G T. *)
  (* Proof using WF IMMCON SIMREL. *)
  (*   unfold G. unfold rstG. unfold E0. *)
  (*   certT *)
  (*   split. *)
  (* Qed. *)

  (* Lemma ICOH_G: iord_coherent G Gsc T.  *)
  (* Proof using WF IMMCON SIMREL. *)
  (*   unfold G. eapply ICOH_rst; eauto. *)
  (* Qed. *)

  (* Lemma TCCOH_rst_new_T: *)
  (*   tc_coherent G Gsc (mkTC ((covered T) ∪₁ ((acts_set G) ∩₁ NTid_ thread))  (issued T)). *)
  (* Proof using WF SIMREL IMMCON. subst; eapply TCOH_rst_new_T; eauto. Qed.  *)

  (* TODO: remove and use TCOH_rst directly? *)
  Lemma TCOH_rst_new_T:
    tls_coherent G (certT G T thread). 
  Proof using WF SIMREL. eapply TCOH_rst_certT; eauto. Qed.

  (* Lemma ICOH_cert' (FAIR: mem_fair Gf): *)
  (*   iord_coherent G Gsc (certT G T thread).  *)
  (* Proof using. *)
  (*   eapply iord_coherent_mori; [..| apply ICOH_cert]; eauto.  *)
  (*   unfold Gsc.  *)


  (* Lemma ICOH_rst_new_T: *)
  (*   iord_coherent G Gsc (certT G T thread). *)
  (* Proof using WF SIMREL. *)
  (*   apply ICOH_rst.  *)
  (* Qed. *)

  Lemma IT_new_co:
    (issued T) ∪₁ (acts_set G) ∩₁ is_w (lab G) ∩₁ Tid_ thread ≡₁ (acts_set G) ∩₁ is_w (lab G).
  Proof using WF SIMREL. subst; eapply IT_new_co; eauto. Qed. 

  Lemma ACYC_EXT_G: acyc_ext G Gsc.
  Proof using SIMREL WF IMMCON. subst; eapply acyc_ext_rst; eauto. Qed. 

  Lemma CSC_G: coh_sc G Gsc.
  Proof using WF SIMREL IMMCON. subst; eapply coh_sc_rst; eauto. Qed. 

  Lemma COH_G: coherence G. 
  Proof using WF SIMREL IMMCON. subst; eapply coherence_rst; eauto. Qed. 

  Lemma AT_G: rmw_atomicity G. 
  Proof using WF SIMREL IMMCON. subst; eapply rmw_atomicity_rst; eauto. Qed. 

  Lemma E_to_S: (acts_set G) ⊆₁ (covered T) ∪₁ dom_rel ((sb G)^? ⨾ ⦗reserved T⦘). 
  Proof using WF SIMREL. subst; eapply E_to_S; eauto. Qed. 
  
  Lemma Grfe_E : dom_rel (rfe G) ⊆₁ (issued T). 
  Proof using WF SIMREL IMMCON. subst; eapply Grfe_E; eauto. Qed. 

  Lemma E_F_AcqRel_in_C:
    (acts_set G) ∩₁ (is_f (lab G)) ∩₁ (is_ra (lab G)) ⊆₁ (covered T).
  Proof using WF SIMREL. subst; eapply E_F_AcqRel_in_C; eauto. Qed. 

  Lemma COMP_ACQ:
    forall r (IN: ((acts_set G) ∩₁ (is_r (lab G)) ∩₁ (is_acq (lab G))) r), exists w, (rf G) w r.
  Proof using WF SIMREL IMMCON.  subst; eapply COMP_ACQ; eauto. Qed.

  Lemma RMW_RFI_ACQ:
    dom_rel
      ((rmw G ⨾ rfi G)＊ ⨾ ⦗acts_set G ∩₁ (is_r (lab G)) ∩₁ (is_acq (lab G))⦘)
      ⊆₁ codom_rel (rf G). 
  Proof using WF SIMREL IMMCON. subst; eapply COMP_RMWRFI_ACQ; eauto. Qed. 

  Lemma urr_helper:
    dom_rel (((hb G) ⨾ ⦗(is_f (lab G)) ∩₁ (is_sc (lab G))⦘)^? ⨾ Gsc^? ⨾ (hb G)^? ⨾ (release G) ⨾ ⦗(issued T)⦘) ⊆₁ (covered T). 
  Proof using WF SIMREL IMMCON. subst; eapply urr_helper_rst; eauto. Qed. 

  Lemma urr_helper_C:
    dom_rel (((hb G) ⨾ ⦗(is_f (lab G)) ∩₁ (is_sc (lab G))⦘)^? ⨾ Gsc^? ⨾ (hb G)^? ⨾ ((release G) ⨾ (rf G))^? ⨾ ⦗(covered T)⦘) ⊆₁ (covered T). 
  Proof using WF SIMREL IMMCON. subst; eapply urr_helper_C_rst; eauto. Qed. 

  Lemma W_hb_sc_hb_to_I_NTid:
    dom_rel (⦗(is_w (lab G))⦘ ⨾ (hb G) ⨾ (Gsc ⨾ (hb G))^? ⨾ ⦗(issued T) ∩₁ NTid_ thread⦘) ⊆₁ (issued T).
  Proof using WF SIMREL IMMCON. subst; eapply W_hb_sc_hb_to_I_NTid; eauto. Qed.

  Lemma detour_E:
    dom_rel ((detour G) ⨾ ⦗(acts_set G) ∩₁ NTid_ thread⦘) ⊆₁ (issued T). 
  Proof using WF SIMREL. subst; eapply detour_E; eauto. Qed. 

  Lemma detour_Acq_E:
    dom_rel ((detour G) ⨾ ⦗(acts_set G) ∩₁ (is_r (lab G)) ∩₁ (is_acq (lab G))⦘) ⊆₁ (issued T).
  Proof using WF SIMREL. subst; eapply detour_Acq_E; eauto. Qed.

  Lemma hb_sc_hb_de:
    ⦗((acts_set G) \₁ (covered T)) ∩₁ ((acts_set G) \₁ (issued T))⦘ ⨾ (hb G) ⨾ (Gsc ⨾ (hb G))^? ⊆ (sb G).
  Proof using WF SIMREL IMMCON. subst; eapply hb_sc_hb_de; eauto. Qed. 

  Hint Resolve
       (* TCCOH_G TCCOH_rst_new_T *)
       IT_new_co ACYC_EXT_G CSC_G COH_G: core.
  Hint Resolve AT_G E_to_S Grfe_E E_F_AcqRel_in_C COMP_ACQ RMW_RFI_ACQ: core.
  Hint Resolve urr_helper urr_helper_C W_hb_sc_hb_to_I_NTid detour_E detour_Acq_E hb_sc_hb_de: core.

  Lemma COMP_C: (covered T) ∩₁ (is_r (lab G)) ⊆₁ codom_rel (rf G).
  Proof using WF SIMREL IMMCON. subst; eapply COMP_C; eauto. Qed. 

  Lemma COMP_NTID:
    (acts_set G) ∩₁ NTid_ thread ∩₁ (is_r (lab G)) ⊆₁ codom_rel (rf G).
  Proof using WF SIMREL IMMCON. subst; eapply COMP_NTID; eauto. Qed. 

  Lemma COMP_PPO:
    dom_rel ((ppo G) ⨾ ⦗(issued T)⦘) ∩₁ (is_r (lab G)) ⊆₁ codom_rel (rf G).
  Proof using WF SIMREL IMMCON. subst; eapply COMP_PPO; eauto. Qed.

  Lemma COM_PPO_ALT: dom_rel (ppo G ⨾ ⦗issued T⦘) ⊆₁ codom_rel (rf G). 
  Proof using WF SIMREL IMMCON.
    rewrite (dom_l (wf_ppoD G)), !seqA.
    rewrite dom_eqv1. rewrite set_interC. apply COMP_PPO. 
  Qed.

  Lemma acts_G_in_acts_Gf: acts_set G ⊆₁ acts_set Gf.
  Proof using WF SIMREL. by apply (sub_E_in SUB). Qed. 

  Lemma lab_G_eq_lab_Gf: lab G = lab Gf.
  Proof using. vauto. Qed. 

  Lemma rmw_G_rmw_Gf:
    rmw G ≡ ⦗ E0 Gf T thread ⦘ ⨾ rmw Gf ⨾ ⦗ E0 Gf T thread ⦘.
  Proof using. vauto. Qed.

  Hint Resolve COMP_C COMP_NTID COMP_PPO COM_PPO_ALT acts_G_in_acts_Gf lab_G_eq_lab_Gf rmw_G_rmw_Gf: core. 
  
  Definition CT := mkCT Gf T thread thread. 
  
  Lemma CTALT:
    CT ≡₁ (covered T ∪₁ issued T ∪₁ dom_rel ((sb Gf)^? ⨾ ⦗Tid_ thread ∩₁ reserved T⦘)) ∩₁ Tid_ thread.
  Proof using WF SIMREL. 
    unfold CT, mkCT, E0.
    arewrite (rmw Gf ⨾ ⦗NTid_ thread ∩₁ issued T⦘ ≡
                  ⦗NTid_ thread⦘ ⨾ rmw Gf ⨾ ⦗NTid_ thread ∩₁ issued T⦘).
    2: { basic_solver 10. }
    split; [|basic_solver].
    intros x y HH. apply seq_eqv_l. split; auto.
    apply seq_eqv_r in HH. destruct HH as [RMW [AA BB]].
    intros CC. apply AA. rewrite <- CC. symmetry.
      by apply (wf_rmwt WF). 
  Qed.

  Lemma CTEE: CT ⊆₁ acts_set Gf.
  Proof using WF SIMREL.
    rewrite CTALT.
    erewrite coveredE, issuedE, rcoh_S_in_E; eauto. 
    rewrite wf_sbE. basic_solver.
  Qed. 

  Lemma CREP_weak:
    forall e (CTE : CT e), exists index : nat,
        ⟪ EREP : e = ThreadEvent thread index ⟫.
  Proof using WF SIMREL.
    ins. apply CTALT in CTE. destruct CTE as [AA BB].
    cdes SIMREL. cdes LOCAL.
    destruct e; desf. simpls. eauto.
  Qed. 

  Hint Resolve thread_ninit: core.

  Lemma CTINDEX 
        (state': Language.state (PromiseLTS.thread_lts thread))
        (TEH: thread_restricted_execution Gf thread (ProgToExecution.G state'))
        (GPC': wf_thread_state thread state'):
    exists ctindex,
      ⟪ CCLOS :forall index (LT : index < ctindex),
          CT (ThreadEvent thread index) ⟫ /\
      ⟪ CREP : forall e (CTE : CT e),
          exists index : nat,
            ⟪ EREP : e = ThreadEvent thread index ⟫ /\
            ⟪ ILT : index < ctindex ⟫ ⟫.
  Proof using WF SIMREL TLS_FIN.
    destruct (classic (exists e, CT e)) as [|NCT].
    2: { exists 0. splits.
         { ins. inv LT. }
         ins. exfalso. apply NCT. eauto. }
    desc.
    assert (acyclic (sb Gf ⨾ ⦗ CT ⦘)) as AC.
    { arewrite (sb Gf ⨾ ⦗CT⦘ ⊆ sb Gf). apply sb_acyclic. }
    assert (exists doml, (forall c, (sb Gf ⨾ ⦗CT⦘)＊ e c -> In c doml)) as [doml UU].
    { fold (set_finite ((sb Gf ⨾ ⦗CT⦘)＊ e)).
      arewrite ((sb Gf ⨾ ⦗CT⦘)＊ e ⊆₁ codom_rel (⦗eq e⦘ ⨾ (sb Gf ⨾ ⦗CT⦘)＊)) by vauto.
      arewrite ((sb Gf ⨾ ⦗CT⦘)＊ ⊆ (sb Gf ⨾ ⦗CT⦘)^?).
      { rewrite crE, rtE. apply union_mori; [basic_solver| ].
        apply inclusion_t_ind; [basic_solver| ].
        generalize (@sb_trans Gf). basic_solver. }
      rewrite crE, seq_union_r, codom_union. apply set_finite_union. split.
      { exists [e]. basic_solver. }
      rewrite no_sb_to_init, seqA, <- id_inter.
      rewrite <- seqA, codom_seq_eqv_r.
      rewrite set_interC. apply CT_fin. }
    
    edestruct (last_exists doml AC UU) as [max [MM1 MM2]].
    
    assert (CT max) as CTMAX.
    { apply rtE in MM1. destruct MM1 as [MM1|MM1].
      { red in MM1. desf. }
      apply inclusion_ct_seq_eqv_r in MM1. apply seq_eqv_r in MM1. desf. }
    assert (Tid_ thread max) as CTTID by apply CTMAX.
    destruct max as [l|mthread mindex].
    { by destruct thread_ninit. }
    simpls. rewrite CTTID in *.
    assert (acts_set Gf (ThreadEvent thread mindex)) as EEM.
    { by apply CTEE. }
    exists (1 + mindex). splits.
    { ins. apply CTALT in CTMAX.
      apply CTALT. split; auto.
      apply le_lt_or_eq in LT. destruct LT as [LT|LT].
      2: { inv LT. apply CTMAX. }
      assert ((ProgToExecution.G state').(acts_set) (ThreadEvent thread mindex)) as PP.
      { apply (tr_acts_set TEH). by split. }
      assert ((acts_set Gf) (ThreadEvent thread index)) as EEE.
      { apply (tr_acts_set TEH). eapply acts_rep in PP; eauto.
        desc. eapply GPC'.(acts_clos). inv REP. lia. }
      assert (sb Gf (ThreadEvent thread index) (ThreadEvent thread mindex)) as QQ.
      { red.
        apply seq_eqv_l. split; auto.
        apply seq_eqv_r. split; auto.
        red. split; auto. lia. }
      destruct CTMAX as [[[AA|AA]|[z AA]] _].
      { do 2 left. eapply dom_sb_covered; basic_solver 10. }
      { right. exists (ThreadEvent thread mindex).
        apply seq_eqv_r. split; auto.
        split; auto. eapply rcoh_I_in_S; eauto. }
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
    apply seq_eqv_r. split; [vauto| by apply CTEE].
  Qed.

  (* TODO: move to imm *)
  Lemma step_threads_set s1 s2 t
        (STEP: step t s1 s2):
    ProgToExecution.G s2 = ProgToExecution.G s1 \/
    threads_set (ProgToExecution.G s2) ≡₁ threads_set (ProgToExecution.G s1) ∪₁ eq t. 
  Proof using. 
    inv STEP. inv H. red in H0, H1. desc. inv H2.
    all: rewrite UG; try by vauto. 
    all: simpl; right; basic_solver.
  Qed.

  (* TODO: move to imm *)
  Lemma steps_threads_set s1 s2 t
        (STEP: (step t)^* s1 s2):
    ProgToExecution.G s2 = ProgToExecution.G s1 \/
    threads_set (ProgToExecution.G s2) ≡₁ threads_set (ProgToExecution.G s1) ∪₁ eq t.
  Proof using.
    induction STEP.
    { by apply step_threads_set in H. }
    { tauto. }
    des.
    { left. congruence. }
    all: right; rewrite IHSTEP2, IHSTEP1; basic_solver. 
  Qed.

  Lemma STATE''
        (state: ProgToExecution.state)
        (state': Language.state (PromiseLTS.thread_lts thread))
        (ctindex: nat)
        (STEPS : (step thread)＊ state state')
        (TEH: thread_restricted_execution Gf thread (ProgToExecution.G state'))
        (GPC : wf_thread_state thread state)
        (GPC' : wf_thread_state thread state')
        (PCOV : forall index, covered T (ThreadEvent thread index) <-> index < eindex state)
        (CCLOS: forall index (LT : index < ctindex), CT (ThreadEvent thread index))
        (CREP: forall e, CT e -> exists index : nat,
              e = ThreadEvent thread index /\ index < ctindex)
    :
      exists state'',
        ⟪ STEPS'' : (step thread)＊ state state'' ⟫ /\
        ⟪ TEH'': thread_restricted_execution G thread state''.(ProgToExecution.G) ⟫.
  Proof using WF SIMREL.
    edestruct steps_middle_set with (C:=CT) (state:=state) (state':=state')
      as [state'']; eauto.
    { intros x HH. apply (acts_rep GPC) in HH.
      desc.
      apply CTALT. rewrite REP in *. split; auto.
      do 2 left. by apply PCOV. }
    { rewrite (tr_acts_set TEH).
      apply set_subset_inter_r. split. 
      { apply CTEE. }
      rewrite CTALT. basic_solver. }
    { cdes SIMREL. 
      ins.
      apply (tr_rmw TEH) in RMW.
      apply seq_eqv_l in RMW. destruct RMW as [TIDR RMW].
      apply seq_eqv_r in RMW. destruct RMW as [RMW TIDW].
      apply (dom_l (wf_rmwD WF)) in RMW.
      apply seq_eqv_l in RMW. destruct RMW as [RREX RMW].
      assert (is_r (lab Gf) r) as RR by type_solver.
      split; intros AA.
      all: apply CTALT; split; auto.
      all: apply CTALT in AA; destruct AA as [[[AA|AA]|AA] _].
      1,4: do 2 left; cdes COMMON; by apply (RMWCOV r w RMW).
      { eapply issuedW in AA; eauto. type_solver. }
      { right. unfolder in AA. desf.
        { eapply reservedW in AA2; eauto. type_solver. }
        exists y. apply seq_eqv_r. split; [|split]; auto.
        destruct (classic (w = y)) as [|NEQ]; subst.
        { basic_solver. }
        edestruct (@sb_semi_total_l Gf r y w WF); auto.
        { intros HH. apply (init_w WF) in HH.
          clear -RR HH. type_solver. }
        { by apply (rmw_in_sb WF). }
        exfalso. eapply (wf_rmwi WF); eauto. }
      { right. exists w. apply seq_eqv_r. split; [|split]; auto.
        { right. by apply rmw_in_sb. }
        eapply rcoh_I_in_S; eauto. }
      right. destruct AA as [y AA]. apply seq_eqv_r in AA. destruct AA as [AA BB].
      exists y. apply seq_eqv_r. split; auto.
      right. apply rewrite_trans_seq_cr_r.
      { apply sb_trans. }
      eexists; split; eauto. by apply rmw_in_sb. }
    desc.
    assert (wf_thread_state thread state'') as GPC''.
    { eapply wf_thread_state_steps; [|apply STEP1]; auto. }
    exists state''. splits; auto.
    edestruct steps_old_restrict with (state:=state'') (state':=state') as [ORMW]; eauto.
    desc. unnw.
    constructor.
    { rewrite CACTS. unfold CT, mkCT, G. 
      rewrite E_E0; eauto. }
    { 
      move STEP2 at bottom. move STEP1 at bottom. move STEPS at bottom. 
      apply steps_threads_set in STEP2; eauto. des.
      { rewrite <- STEP2. eapply tr_threads_set; eauto. }
      (* apply steps_threads_set in STEP1; eauto. des. *)
      (* { apply steps_threads_set in STEPS; eauto. des. *)
      (*   { rewrite STEP1, <- STEPS. eapply tr_threads_set; eauto. } *)

      erewrite tr_threads_set in STEP2; eauto. rewrite STEP2.
      symmetry. apply set_union_absorb_r. apply set_subset_eq. 
      admit. 
    }
    { ins. unfold G, rstG, restrict; simpls.
      rewrite <- (tr_lab TEH); auto.
      2: { eapply steps_preserve_E.
           3: by apply EE.
           all: eauto. }
      assert (tid x = thread) as HH.
      { apply GPC''.(acts_rep) in EE. desc. by subst. }
      rewrite <- HH in *.
      symmetry. eapply steps_preserve_lab; eauto. }
    all: unfold G, rstG, restrict; simpls.
    { rewrite ORMW. rewrite CACTS. unfold CT.
      rewrite !seqA.
      arewrite (⦗Tid_ thread⦘ ⨾ ⦗E0 Gf T thread⦘ ⨾ rmw Gf ⨾ ⦗E0 Gf T thread⦘ ⨾ ⦗Tid_ thread⦘ ≡
                              ⦗E0 Gf T thread⦘ ⨾ ⦗Tid_ thread⦘ ⨾ ⦗Tid_ thread⦘ ⨾ rmw Gf ⨾
                              ⦗Tid_ thread⦘ ⨾ ⦗Tid_ thread⦘ ⨾ ⦗E0 Gf T thread⦘).
      { basic_solver. }
      seq_rewrite <- (tr_rmw TEH). unfold mkCT. basic_solver. }
    { rewrite ODATA. rewrite CACTS. unfold CT.
      rewrite !seqA.
      arewrite (⦗Tid_ thread⦘ ⨾ ⦗E0 Gf T thread⦘ ⨾ data Gf ⨾ ⦗E0 Gf T thread⦘ ⨾ ⦗Tid_ thread⦘ ≡
                              ⦗E0 Gf T thread⦘ ⨾ ⦗Tid_ thread⦘ ⨾ ⦗Tid_ thread⦘ ⨾ data Gf ⨾
                              ⦗Tid_ thread⦘ ⨾ ⦗Tid_ thread⦘ ⨾ ⦗E0 Gf T thread⦘).
      { basic_solver. }
      seq_rewrite <- (tr_data TEH). unfold mkCT. basic_solver. }
    { rewrite OADDR. rewrite CACTS. unfold CT.
      rewrite !seqA.
      arewrite (⦗Tid_ thread⦘ ⨾ ⦗E0 Gf T thread⦘ ⨾ addr Gf ⨾ ⦗E0 Gf T thread⦘ ⨾ ⦗Tid_ thread⦘ ≡
                              ⦗E0 Gf T thread⦘ ⨾ ⦗Tid_ thread⦘ ⨾ ⦗Tid_ thread⦘ ⨾ addr Gf ⨾
                              ⦗Tid_ thread⦘ ⨾ ⦗Tid_ thread⦘ ⨾ ⦗E0 Gf T thread⦘).
      { basic_solver. }
      seq_rewrite <- (tr_addr TEH). unfold mkCT. basic_solver. }
    { rewrite OCTRL. rewrite CACTS. unfold CT.
      rewrite !seqA.
      arewrite (⦗Tid_ thread⦘ ⨾ ⦗E0 Gf T thread⦘ ⨾ ctrl Gf ⨾ ⦗E0 Gf T thread⦘ ⨾ ⦗Tid_ thread⦘ ≡
                              ⦗E0 Gf T thread⦘ ⨾ ⦗Tid_ thread⦘ ⨾ ⦗Tid_ thread⦘ ⨾ ctrl Gf ⨾
                              ⦗Tid_ thread⦘ ⨾ ⦗Tid_ thread⦘ ⨾ ⦗E0 Gf T thread⦘).
      { basic_solver. }
      seq_rewrite <- (tr_ctrl TEH). unfold mkCT. basic_solver. }
    rewrite OFAILDEP. rewrite CACTS. unfold CT.
    rewrite !seqA.
    arewrite (⦗Tid_ thread⦘ ⨾ ⦗E0 Gf T thread⦘ ⨾ rmw_dep Gf ⨾
                            ⦗E0 Gf T thread⦘ ⨾ ⦗Tid_ thread⦘ ≡
                            ⦗E0 Gf T thread⦘ ⨾ ⦗Tid_ thread⦘ ⨾ ⦗Tid_ thread⦘ ⨾ rmw_dep Gf ⨾
                            ⦗Tid_ thread⦘ ⨾ ⦗Tid_ thread⦘ ⨾ ⦗E0 Gf T thread⦘).
    { basic_solver. }
    seq_rewrite <- (tr_rmw_dep TEH). unfold mkCT. basic_solver.
  Admitted. 

  Lemma COMP_RPPO:
    dom_rel (⦗is_r (lab G)⦘ ⨾ (data G ∪ rfi G ∪ rmw G)＊ ⨾ rppo G ⨾ ⦗reserved T⦘)
            ⊆₁ codom_rel (rf G).
  Proof using WF SIMREL IMMCON.  subst. eapply COMP_RPPO; eauto. Qed. 

  Lemma S_in_W: reserved T ⊆₁ is_w (lab G).
  Proof using WF SIMREL.
    erewrite sub_W; eauto. 
    erewrite reservedW; eauto.
  Qed. 
  
  Lemma ST_in_E: reserved T ∩₁ Tid_ thread ⊆₁ acts_set G.
  Proof using WF SIMREL.
    unfold G. rewrite E_E0; eauto. unfold E0.
    unionR left -> right. basic_solver 10.
  Qed.
  
  Lemma F_SB_S:
    dom_rel (⦗(is_f (lab G)) ∩₁ (is_ra (lab G))⦘ ⨾ sb G ⨾ ⦗reserved T⦘)
    ⊆₁ covered T.
  Proof using WF SIMREL.
    rewrite sub_F; eauto.
    rewrite sub_AcqRel; eauto.
    rewrite sub_sb_in; eauto.
    apply RCOH. 
  Qed.
  
  Lemma RPPO_S:
    dom_rel ((detour G ∪ rfe G) ⨾ (data G ∪ rfi G ∪ rmw G)＊ ⨾ rppo G ⨾ ⦗reserved 
T⦘)
    ⊆₁ issued T.
  Proof using WF SIMREL IMMCON.
    rewrite sub_detour_in; eauto.
    rewrite sub_rfe_in; eauto.
    rewrite sub_data_in; eauto.
    rewrite sub_rfi_in; eauto.
    subst.
    rewrite sub_rppo_in; eauto.
    2: by eapply Frmw_E_prefix_clos; eauto.
    rewrite sub_rmw_in; eauto.
    apply RCOH. 
  Qed. 

  Lemma RMW_S: dom_rel ((detour G ∪ rfe G) ⨾ rmw G ⨾ ⦗reserved T⦘) ⊆₁ issued T.
  Proof using WF SIMREL. 
    rewrite sub_detour_in; eauto.
    rewrite sub_rfe_in; eauto.
    rewrite sub_rmw_in; eauto.
    eapply rcoh_rmw_S with (T:=T); eauto.
  Qed. 
  
  Lemma D_RMW_S:
    dom_rel (detour G ⨾ rmw G ⨾ ⦗reserved T⦘) ⊆₁ issued T.
  Proof using WF SIMREL. rewrite <- RMW_S. clear. basic_solver 10. Qed. 

  Lemma DRFE_RMW_RFI_R_ACQ:
    dom_rel
      ((detour G ∪ rfe G) ⨾ (rmw G ⨾ rfi G)＊ ⨾
       ⦗(is_r (lab G)) ∩₁ (is_acq (lab G))⦘ ⨾ sb G ⨾ ⦗reserved T⦘)
      ⊆₁ issued T. 
  Proof using WF SIMREL. 
    rewrite sub_detour_in; eauto.
    rewrite sub_rfe_in; eauto.
    rewrite sub_rmw_in; eauto.
    rewrite sub_rfi_in; eauto.
    rewrite sub_R; eauto.
    rewrite sub_Acq; eauto.
    rewrite sub_sb_in; eauto.
    apply RCOH. 
  Qed. 

  Hint Resolve COMP_RPPO S_in_W ST_in_E F_SB_S RPPO_S RMW_S D_RMW_S DRFE_RMW_RFI_R_ACQ: core.

  Definition delta_rf :=
    (new_rf G Gsc T thread) ⨾ ⦗set_compl (dom_rel (rmw G))⦘ ∪
                              immediate (cert_co G T thread) ⨾ (rmw G)⁻¹ ⨾ ⦗set_compl (D G T thread)⦘.
  Definition new_rfi := ⦗  Tid_ thread ⦘ ⨾ delta_rf ⨾ ⦗ Tid_ thread ⦘.
  Definition new_rfe := ⦗ NTid_ thread ⦘ ⨾ delta_rf ⨾ ⦗ Tid_ thread ⦘.

  Lemma DELTA_RF_CERT: delta_rf ⊆ cert_rf G Gsc T thread.
  Proof using. unfold delta_rf, cert_rf. basic_solver 20. Qed. 

  Lemma delta_rfE:
    delta_rf ≡ ⦗acts_set G⦘ ⨾ delta_rf ⨾ ⦗acts_set G \₁ D G T thread⦘. 
  Proof using WF SIMREL IMMCON. 
    apply dom_helper_3.
    arewrite (delta_rf ⊆ ⦗acts_set G⦘ ⨾ delta_rf ⨾ ⦗acts_set G⦘).
    { apply dom_helper_3.
      rewrite DELTA_RF_CERT. rewrite cert_rfE; eauto.
      clear. basic_solver. }
    unfold delta_rf. rewrite wf_new_rfE; auto.
    basic_solver.
  Qed.

  Lemma delta_rfD:
    delta_rf ≡ ⦗is_w (lab G)⦘ ⨾ delta_rf ⨾ ⦗is_r (lab G)⦘. 
  Proof using WF SIMREL. 
    apply dom_helper_3.
    rewrite DELTA_RF_CERT. rewrite cert_rfD; auto. clear. basic_solver 10.
  Qed. 

  Lemma NEW_RFI_CERT:
    new_rfi ⊆ cert_rf G Gsc T thread.
  Proof using. unfold new_rfi. rewrite DELTA_RF_CERT. basic_solver 20. Qed. 

  Lemma new_rfif: functional new_rfi⁻¹. 
  Proof using WF SIMREL IMMCON. rewrite NEW_RFI_CERT. apply cert_rff; auto. Qed.

  Lemma NEW_RFE_CERT: new_rfe ⊆ cert_rf G Gsc T thread.
  Proof using. unfold new_rfe. rewrite DELTA_RF_CERT. basic_solver 20. Qed.

  Lemma new_rfef: functional new_rfe⁻¹. 
  Proof using WF SIMREL IMMCON. rewrite NEW_RFE_CERT. apply cert_rff; auto. Qed.

  Hint Resolve delta_rfE delta_rfD NEW_RFE_CERT NEW_RFI_CERT new_rfif new_rfef: core. 

  Definition new_rfe_ex := new_rfe ∪ ⦗ set_compl (codom_rel new_rfe) ⦘.

  Lemma new_rfe_unique: forall r, exists ! w, new_rfe_ex⁻¹  r w. 
  Proof using WF SIMREL IMMCON.
    ins.
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
    unfolder in X; exfalso; eauto.
  Qed.

  Hint Resolve new_rfe_unique: core. 


  Definition get_val (v: option value) :=  match v with | Some v => v | _ => 0 end.

  Lemma ST_in_W_ex:
    reserved T ∩₁ Tid_ thread \₁ issued T ⊆₁ W_ex G.
  Proof using WF SIMREL. 
    arewrite (reserved T ∩₁ Tid_ thread \₁ issued T ⊆₁
                W_ex Gf ∩₁ reserved T ∩₁ Tid_ thread \₁ issued T).
    { unfolder. ins. desc. splits; auto.
      eapply rcoh_S_I_in_W_ex; eauto. basic_solver. }
    unfold W_ex.
    rewrite (sub_rmw SUB).
    subst.
    unfolder. ins. desc.
    eexists. splits; eauto.
    all: eapply E_E0; eauto.
    all: red.
    all: left; right.
    all: exists x; apply seq_eqv_r; split; [|split]; auto.
                eapply inclusion_step_cr; [reflexivity|]. by apply (rmw_in_sb WF).
  Qed.

  Lemma SB_S:
    dom_sb_S_rfrmw G T (rf G ⨾ ⦗R_ex (lab G)⦘) (issued T) ⊆₁ reserved T.
  Proof using WF SIMREL. 
    unfold dom_sb_S_rfrmw. 
    rewrite sub_sb_in; eauto.
    rewrite sub_rf_in; eauto.
    rewrite sub_R_ex; eauto.
    rewrite sub_rmw_in; eauto.
    apply RCOH.
  Qed.
  
  Lemma RMWREX : dom_rel (rmw G) ⊆₁ (R_ex (lab G)).
  Proof using SIMREL WF.
    rewrite sub_rmw_in; eauto. rewrite sub_R_ex; eauto.
    cdes SIMREL. apply COMMON.
  Qed.

  Lemma IST_in_S: issued T ∪₁ reserved T ∩₁ Tid_ thread ⊆₁ reserved T.
  Proof using WF SIMREL. 
    generalize (rcoh_I_in_S RCOH). simpls. basic_solver.
  Qed.

  Lemma I_in_S: issued T ⊆₁ reserved T.
  Proof using WF SIMREL. by apply RCOH. Qed.

  Hint Resolve ST_in_W_ex SB_S RMWREX IST_in_S I_in_S: core. 

  (* Lemma ICOH_rst_new_T: *)
  (*   iord_coherent G sc (certT G T thread).  *)
  (* Proof using. *)
    
  
  Definition receptiveness_def tid s_init s s'
             (MOD: actid -> Prop) (new_val : actid -> value) :=
    ⟪ STEPS' : (step tid)＊ s_init s' ⟫ /\
    ⟪ RACTS : (acts_set (ProgToExecution.G s)) = (acts_set (ProgToExecution.G s')) ⟫ /\
    ⟪ RRMW  : (rmw (ProgToExecution.G s))  ≡ (rmw (ProgToExecution.G s'))  ⟫ /\
    ⟪ RDATA : (data (ProgToExecution.G s)) ≡ (data (ProgToExecution.G s')) ⟫ /\
    ⟪ RADDR : (addr (ProgToExecution.G s)) ≡ (addr (ProgToExecution.G s')) ⟫ /\
    ⟪ RCTRL : (ctrl (ProgToExecution.G s)) ≡ (ctrl (ProgToExecution.G s')) ⟫  /\
    ⟪ RFAILRMW : (rmw_dep (ProgToExecution.G s)) ≡ (rmw_dep (ProgToExecution.G s')) ⟫  /\
    ⟪ SAME : same_lab_u2v ((lab (ProgToExecution.G s'))) ((lab (ProgToExecution.G s)))⟫ /\
    ⟪ NEW_VAL1 : forall r w (RF: new_rfi w r), val ((lab (ProgToExecution.G s'))) r = val ((lab (ProgToExecution.G s'))) w ⟫ /\
    ⟪ NEW_VAL2 : forall r (RR : is_r (lab (ProgToExecution.G s')) r) (IN: MOD r) (NIN: ~ (codom_rel new_rfi) r),
        val ((lab (ProgToExecution.G s'))) r = Some (new_val r) ⟫ /\
    ⟪ OLD_VAL : forall a (NIN: ~ MOD a), val ((lab (ProgToExecution.G s'))) a = val ((lab (ProgToExecution.G s))) a ⟫.

  Lemma receptiveness_impl state state'' (new_val: actid -> value)
        (GPC: wf_thread_state thread state)
        (RMWRES: RMWinstrProps.rmw_is_rex_instrs (instrs state))
        (STEPS'': (step thread)＊ state state'')
        (TEH'': thread_restricted_execution G thread (ProgToExecution.G state''))
        (STATECOV : acts_set (ProgToExecution.G state) ⊆₁ covered T):
    exists s', @receptiveness_def thread state state'' s' 
                             (E0 Gf T thread \₁ D G T thread) new_val.
  Proof using WF SIMREL IMMCON.
    forward eapply ICOH_rst_certT with (thread := thread) as ICOH'; eauto. 
    forward eapply TCOH_rst_certT with (thread := thread) as TCOH'; eauto.
    fold G in *. unfold rst_sc in ICOH'. fold Gsc in ICOH'.

    apply receptiveness_full; eauto.  
    { red. ins. red. apply RMWRES in IN. red in IN. desf. }
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
      basic_solver. }
    { unfold new_rfi. rewrite DELTA_RF_CERT.
      rewrite cert_rfE; auto. rewrite !seqA.
      rewrite cert_rfD; auto. rewrite !seqA.
      repeat seq_rewrite <- id_inter. 
      red. intros x y ?%seq_eqv_lr. unfold set_inter in *. desc. 
      rewrite <- H in *.
      apply (@same_thread G) in H3; try done.
      2: { intro K; eapply init_w in K; try edone; type_solver. }
      destruct H3 as [X|Y].
      2: { unfold sb in Y; unfolder in Y; desf. }
      destruct X; [subst; type_solver|].  
      exfalso.
      rewrite -> H in *. 



      eapply Cert_coherence.hb_rf_irr with (G:=G) (T:=T); eauto. 
      (* eapply Cert_coherence.hb_rf_irr with (G:=G) (T:=(certT G T thread)). *)
      (* all: eauto. *)
      (* all: rewrite ?covered_certT, ?issued_certT, ?reserved_certT.  *)
      (* all: eauto. *)
      (* { cdes SIMREL. cdes COMMON. *)
      (*   rewrite RELCOV0. basic_solver. } *)
      (* { rewrite set_split_complete with (s' := acts_set G) (s := is_init) at 1. *)
      (*   unionL. *)
      (*   { rewrite <- covered_certT. rewrite set_interC, init_covered; eauto.  *)
      (*     basic_solver. } *)
      (*   rewrite set_split_complete with (s' := acts_set G) (s := Tid_ thread)at 1. *)
      (*   relsf. split.  *)
      (*   2: { basic_solver 10. } *)
      (*   rewrite E_to_S at 1. relsf. split; [basic_solver| ]. *)
      (*   unionR right. do 2 rewrite set_interC, <- ?set_interA, <- dom_eqv1. *)
      (*   rewrite crE at 1. relsf. split; [basic_solver 10| ]. *)
      (*   unfolder. ins. desc. *)
      (*   exists y0. splits; vauto. right. split; auto. *)
      (*   apply sb_tid_init in H8. des; congruence. } *)
      (* { rewrite urr_helper. basic_solver. } *)
      (* { rewrite <- covered_certT. *)
      (*   eapply CertExecution1.urr_helper_C; eauto. *)
      (*   rewrite issued_certT, covered_certT. rewrite RELCOV. basic_solver. } *)
      (* { relsf. } *)
      (* { rewrite id_union. relsf. *)
      (*   rewrite <- COMP_RPPO at 2. split; [| basic_solver 10]. *)
      (*   rewrite rcoh_I_in_S; eauto. *)
      (*   rewrite <- dom_eqv1. apply COMP_RPPO. } *)
      (* { apply TCOH'.  *)
        
        apply sb_in_hb in H3; unfolder; basic_solver 12.
        (* TODO: get rid of that *)
        Unshelve. exact (fun _ => Afence Opln). }
    { unfold new_rfi. rewrite delta_rfE.
      unfold G; rewrite E_E0; basic_solver. }
    { rewrite TEH''.(tr_acts_set).
      unfold D, G; rewrite E_E0; try eauto.
      unfolder; ins; desf; splits; eauto.
      destruct (classic (tid x = thread)); try done.
      exfalso; apply H0; eauto 20. }
    { rewrite STATECOV. rewrite C_in_D. basic_solver. }
    { rewrite TEH''.(tr_rmw_dep).
      arewrite_id ⦗Tid_ thread⦘; rels.
      rewrite dom_frmw_in_D; eauto. basic_solver. }
    { rewrite TEH''.(tr_addr).
      arewrite_id ⦗Tid_ thread⦘; rels.
      rewrite dom_addr_in_D; eauto. basic_solver. }
    { rewrite TEH''.(tr_acts_set).
      unfolder; ins; desc.
      eapply H3; eauto.
      eapply Rex_in_D with (sc:=Gsc) (T:=T); try eauto.
      split; [|done].
      unfold R_ex, rmwmod in *.
      rewrite TEH''.(tr_lab) in H0; auto.
      eapply TEH''.(tr_acts_set). by split. }
    { rewrite TEH''.(tr_ctrl).
      arewrite_id ⦗Tid_ thread⦘; rels.
      rewrite dom_ctrl_in_D; eauto. basic_solver. }
    { rewrite TEH''.(tr_data).
      rewrite (dom_r (wf_dataE WF_G)).
      unfold G.
      rewrite E_E0; auto. 
      unfolder; ins; desc.
      eapply H3; splits; eauto.
      intro. apply H5.
      eapply dom_data_D; eauto. basic_solver 10. }
  Qed.

  Lemma XACQ_I: 
    dom_rel (⦗W_ex G ∩₁ (is_xacq (lab G))⦘ ⨾ sb G ⨾ ⦗reserved T⦘) ⊆₁ issued T.
  Proof using WF SIMREL. 
    rewrite sub_sb_in; eauto.
    rewrite sub_xacq; eauto.
    rewrite sub_W_ex_in; eauto.
    apply RCOH. 
  Qed. 

  Lemma COMP_RMW_S: dom_rel (rmw G ⨾ ⦗reserved T⦘) ⊆₁ codom_rel (rf G).
  Proof using WF SIMREL IMMCON. unfold G. eapply COMP_RMW_S; eauto. Qed.

  Lemma INIT_TLS_T: 
    init_tls G ⊆₁ T. 
  Proof using WF SIMREL.
    unfold G. rewrite <- init_tls_eq_rstG; auto.
    cdes SIMREL. cdes COMMON. apply TCOH. 
  Qed. 

  Lemma RFRMW_IST_IN:
    (cert_rf G Gsc T thread ⨾ rmw G) ⨾ ⦗issued T ∪₁ reserved T ∩₁ Tid_ thread⦘ ⊆ rf Gf ⨾ rmw Gf.
  Proof using WF SIMREL IMMCON Gf_THREADS_BOUND TLS_FIN.
    rewrite IST_in_S. rewrite seqA.    
    rewrite cert_rmw_S_in_rf_rmw_S; eauto using COMP_RMW_S; cycle 1.
    all: eauto using TCOH_rst_certT, ICOH_rst_certT, INIT_TLS_T. 
    rewrite sub_rf_in; eauto.
    rewrite sub_rmw_in; eauto.
    basic_solver.
  Qed. 

  Lemma RFRMW_IN: (cert_rf G Gsc T thread ⨾ rmw G) ⨾ ⦗issued T⦘ ⊆ rf Gf ⨾ rmw Gf.
  Proof using WF IMMCON SIMREL Gf_THREADS_BOUND TLS_FIN.
    arewrite (issued T ⊆₁ issued T ∪₁ reserved T ∩₁ Tid_ thread).
    rewrite <- seqA. apply RFRMW_IST_IN. 
  Qed. 

  Lemma ISTex_rf_I:
    (issued T ∪₁ reserved T ∩₁ Tid_ thread) ∩₁ W_ex G ⊆₁
    codom_rel (⦗issued T⦘ ⨾ rf G ⨾ rmw G).
  Proof using WF SIMREL. 
    assert ((issued T ∪₁ reserved T ∩₁ Tid_ thread) ∩₁ W_ex G ⊆₁
            reserved T ∩₁ W_ex Gf) as AA.
    { rewrite I_in_S. subst. unfold rstG, restrict, W_ex. simpls.
      clear. basic_solver. }
    intros x HH.
    subst. unfold rstG, restrict, W_ex. simpls.
    set (BB:=HH). apply AA in BB.
    (* apply ETCCOH in BB. *)
    apply rcoh_S_W_ex_rfrmw_I in BB; auto. 
    destruct BB as [y BB]. apply seq_eqv_l in BB.
    destruct BB as [IY [z [BB CC]]].
    exists y. apply seq_eqv_l. split; auto.
    exists z.
    assert (E0 Gf T thread y) as E0Y.
    { red. do 2 left. by right. }
    assert (E0 Gf T thread x) as E0X.
    { destruct HH as [_ HH]. unfold rstG, restrict, W_ex in HH. simpls.
      generalize HH. clear. basic_solver. }
    assert (E0 Gf T thread z) as E0Z.
    2: by split; apply seq_eqv_lr; splits.
    destruct HH as [DD HH].
    assert (reserved T x) as SX.
    { destruct DD as [|DD]; [|by apply DD].
      eapply rcoh_I_in_S; eauto. }
    destruct (classic (Tid_ thread x)) as [TID|NTID].
    { red. left. right. exists x. apply seq_eqv_r. split.
      2: by split.
      right. by apply rmw_in_sb. }
    destruct DD as [|DD]; eauto.
    { right. exists x. apply seq_eqv_r. split; [|split]; auto. }
    exfalso. apply NTID. apply DD.
  Qed. 

  Lemma DOM_SB_S_rf_I:
    dom_rel (sb G ⨾ ⦗issued T ∪₁ reserved T ∩₁ Tid_ thread⦘)
            ∩₁ codom_rel (⦗issued T⦘ ⨾ rf G ⨾ ⦗R_ex (lab G)⦘ ⨾ rmw G) ⊆₁
            issued T ∪₁ reserved T ∩₁ Tid_ thread.
  Proof using WF SIMREL. 
    rewrite rmw_W_ex. rewrite (dom_r (wf_rmwE WF_G)).
    rewrite <- !seqA. rewrite !codom_eqv1.
    rewrite !seqA.

    arewrite (R_ex (lab G) ⊆₁ R_ex (lab Gf)).
    
    rewrite sub_rf_in; eauto.
    rewrite sub_rmw_in; eauto.
    rewrite sub_sb_in; eauto.
    arewrite (dom_rel (sb Gf ⨾ ⦗issued T ∪₁ reserved T ∩₁ Tid_ thread⦘) ⊆₁
                      dom_rel (sb Gf ⨾ ⦗issued T ∪₁ reserved T ∩₁ Tid_ thread⦘) ∩₁
                      dom_rel (sb Gf ⨾ ⦗reserved T⦘)).
    { generalize IST_in_S. clear. basic_solver 10. }
    rewrite <- !set_interA. rewrite set_interC with (s':=W_ex G).
    rewrite <- !set_interA. rewrite set_interC with (s':=acts_set G).
    rewrite !set_interA.
    
    forward eapply rcoh_sb_S; eauto; intro AA1.
    unfold dom_sb_S_rfrmw in AA1.
    simpl in AA1.
    simpl in AA1.
    rewrite !seqA in AA1.
    rewrite AA1.
    rewrite <- !set_interA. rewrite (W_ex_in_W WF_G).
    
    simpls.
    intros x [[HH AA] SX].
    destruct (classic (issued T x)) as [|NISS]; [by left|].
    destruct (classic (Tid_ thread x)) as [|NTID]; [by right; split|].
    exfalso.
    apply IT_new_co in HH. destruct HH as [HH|[_ HH]]; desf.
  Qed. 

  Hint Resolve XACQ_I COMP_RMW_S RFRMW_IST_IN RFRMW_IN ISTex_rf_I DOM_SB_S_rf_I: core. 

  Section Lab'Properties.
    Variable (s' state'': state).

    Hypothesis TEH'':
      thread_restricted_execution G thread (ProgToExecution.G state'').
    Hypothesis (SAME: same_lab_u2v (lab (ProgToExecution.G s'))
                                   (lab (ProgToExecution.G state''))). 


    Variable (new_value: actid -> actid). 
    Variable (st: state).

    Definition new_val: actid -> value :=
      fun (r: actid) => get_val (val (lab G) (new_value r)). 

    Hypothesis     
      (RECP: receptiveness_def thread st state'' s'
                               (E0 Gf T thread \₁ D G T thread)
                               new_val).

    Hypothesis (H0: forall x, new_rfe_ex⁻¹ x (new_value x)). 
    
    Definition lab' :=
      fun x =>
        if excluded_middle_informative ((ProgToExecution.G s').(acts_set) x) 
        then s'.(ProgToExecution.G).(lab) x
        else (lab G) x.

    Lemma SAME0: same_lab_u2v_dom (ProgToExecution.G s').(acts_set)
                                                           lab' (ProgToExecution.G s').(lab).
    Proof using. red. ins. red. unfold lab'. desf. Qed. 

    Lemma SAME2:
      same_lab_u2v_dom (ProgToExecution.G s').(acts_set)
                                                (ProgToExecution.G state'').(lab) (lab G).
    Proof using TEH'' RECP.
      cdes RECP. rewrite <- RACTS.
      apply same_lab_u2v_dom_comm.
      eapply same_lab_u2v_dom_restricted; auto.
      apply TEH''.
    Qed. 

    Lemma SAME3:
      same_lab_u2v_dom (ProgToExecution.G s').(acts_set) lab' (lab G).
    Proof using TEH'' SAME RECP. 
      eapply same_lab_u2v_dom_trans; eauto using SAME0. 
      eapply same_lab_u2v_dom_trans; eauto using SAME2. 
        by apply same_lab_u2v_follows_set.
    Qed.

    Lemma SAME':
      same_lab_u2v lab' (lab G). 
    Proof using TEH'' SAME RECP.
      red. red. ins.
      destruct (classic (acts_set (ProgToExecution.G s') e)) as [XX|XX].
      { eapply SAME3; eauto. }
      unfold lab'. desf. red. basic_solver.
    Qed.

    Lemma YY:
      thread_restricted_execution (certG G Gsc T thread lab') thread
                                  (ProgToExecution.G s').
    Proof using TEH'' RECP.
      cdes RECP.
      constructor; auto.
      { rewrite cert_E. rewrite <- RACTS. by rewrite TEH''.(tr_acts_set). }
      { admit. }
      { ins. unfold lab'. desf. }
      all: unfold certG; simpls.
      { rewrite <- RRMW. apply TEH''.(tr_rmw). }
      { rewrite <- RDATA. apply TEH''.(tr_data). }
      { rewrite <- RADDR. apply TEH''.(tr_addr). }
      { rewrite <- RCTRL. apply TEH''.(tr_ctrl). }
      { rewrite <- RFAILRMW. apply TEH''.(tr_rmw_dep). }
    Admitted. 

    Lemma NEWRF_SPLIT: delta_rf ≡ new_rfi ∪ new_rfe.
    Proof using WF SIMREL IMMCON.
      arewrite (delta_rf ≡ delta_rf ⨾ ⦗ Tid_ thread ⦘).
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
      exfalso; eapply H3. do 5 left. by right.
    Qed.

    Lemma SAME_VAL_RF:
      forall r w, delta_rf w r -> val lab' w = val lab' r.
    Proof using WF SIMREL IMMCON TEH'' SAME RECP H0.
      intros r w NEWRF. cdes RECP.
      apply NEWRF_SPLIT in NEWRF. destruct NEWRF as [NEWRF|NEWRF].
      { set (VV := NEWRF). apply NEW_VAL1 in VV.
        unfold new_rfi in NEWRF.
        apply seq_eqv_l in NEWRF. destruct NEWRF as [TIDW NEWRF].
        apply seq_eqv_r in NEWRF. destruct NEWRF as [NEWRF TIDR].
        apply delta_rfE in NEWRF; auto.
        apply seq_eqv_l in NEWRF. destruct NEWRF as [GEW NEWRF].
        apply seq_eqv_r in NEWRF. destruct NEWRF as [NEWRF [GER MOD]].
        assert (s'.(ProgToExecution.G).(acts_set) r) as ERR.
        { rewrite <- RACTS. apply TEH''.(tr_acts_set). split; auto. }
        assert (s'.(ProgToExecution.G).(acts_set) w) as EWW.
        { rewrite <- RACTS. apply TEH''.(tr_acts_set). split; auto. }
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
      { exfalso. rewrite <- RACTS in HH1.
        apply TEH''.(tr_acts_set) in HH1. destruct HH1 as [_ HH1]. desf. }
      destruct (excluded_middle_informative (acts_set (ProgToExecution.G s') r)) as [HH2|HH2].
      2: { exfalso. apply HH2. rewrite <- RACTS. apply TEH''.(tr_acts_set).
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
      { pose proof (new_rfe_unique r) as new_rfe_unique.
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
        2: { eapply SAME2; eauto. }
        red. ins. by apply SAME. }
      { split; auto. unfold G in GER.
        eapply E_E0 in GER; eauto. }
      unfold new_rfi. intros [z NEWRFI].
      apply seq_eqv_l in NEWRFI. destruct NEWRFI as [TIDZ NEWRFI].
      apply seq_eqv_r in NEWRFI. destruct NEWRFI as [NEWRFI _].
      assert (z = w) as XX.
      2: by desf.
      eapply cert_rff.
      4: { red; eauto. }
      all: eauto.
      all: eapply DELTA_RF_CERT; eauto.
    Qed. 

    Lemma SAME_VAL:
      forall a, ~ (acts_set G \₁ D G T thread) a -> val lab' a = val (lab G) a.
    Proof using WF SIMREL TEH'' RECP.
      cdes RECP. 
      intros a ZZ.
      unfold val, lab'.
      destruct (excluded_middle_informative (acts_set (ProgToExecution.G s') a)) as [MM|MM].
      2: done.
      assert (~ (E0 Gf T thread \₁ D G T thread) a) as XX.
      { intros [AA BB]. apply ZZ. split; auto.
        unfold G. eapply E_E0; eauto. }
      specialize (OLD_VAL a XX). clear XX.
      unfold val in OLD_VAL. rewrite OLD_VAL.
      rewrite TEH''.(tr_lab); auto. by rewrite RACTS.
    Qed.

    Lemma SAME_VAL_RF_CERT:
      forall r w, (cert_rf G Gsc T thread) w r -> val lab' w = val lab' r.
    Proof using WF SIMREL IMMCON TEH'' SAME RECP H0.
      intros r w HH. destruct HH as [[HH|HH]|HH].
      2,3: eapply SAME_VAL_RF; eauto; unfold delta_rf; generalize HH.
      2,3: clear; basic_solver 10.
      erewrite !SAME_VAL; eauto. 
      2,3: intros [_ AA]; apply AA.
      3: { eapply dom_rf_D; eauto.
           3: by eexists; eauto.
           all: eauto using TCOH_rst_certT, ICOH_rst_certT. }
      2: { generalize HH. clear. basic_solver. }
      apply wf_rfv; auto. generalize HH. basic_solver.
    Qed. 

    Lemma ISS_OLD: forall b (ISSB : issued T b), val lab' b = val (lab Gf) b.
    Proof using TEH'' SIMREL RECP WF.
      ins. rewrite <- lab_G_eq_lab_Gf.
      rewrite SAME_VAL; auto.
      intros [_ HH]. apply HH. by apply I_in_D.
    Qed.
    
    Lemma acts_certG_in_acts_Gf:
      acts_set (certG G Gsc T thread lab') ⊆₁ acts_set Gf.
    Proof using. unfold certG, G. simpl. basic_solver. Qed.

    Lemma WF_CERT: Wf (certG G Gsc T thread lab'). 
    Proof using WF TEH'' SIMREL SAME RECP IMMCON H0.
      eapply WF_cert; eauto using SAME_VAL_RF_CERT, SAME_VAL, SAME',
        TCOH_rst_certT, ICOH_rst_certT, INIT_TLS_T. 
    Qed.

    Lemma WF_SC_CERT: wf_sc (certG G Gsc T thread lab') Gsc.
    Proof using WF TEH'' SIMREL SAME RECP IMMCON H0.
      eapply WF_SC_cert; eauto using SAME'.
    Qed.

    Hint Resolve SAME0 SAME2 SAME3 SAME' YY NEWRF_SPLIT SAME_VAL_RF SAME_VAL SAME_VAL_RF_CERT: core. 
    Hint Resolve ISS_OLD acts_certG_in_acts_Gf WF_CERT WF_SC_CERT: core. 

  End Lab'Properties.

  Lemma FACQREL:
    acts_set G ∩₁ (fun a : actid => is_f (lab G) a) ⊆₁ (fun a => is_ra (lab G) a).
  Proof using SIMREL WF.
    rewrite acts_G_in_acts_Gf.
    rewrite lab_G_eq_lab_Gf. apply SIMREL.
  Qed.

  Hint Resolve FACQREL: core. 

  (* TODO: remove SAME hypothesis from the previous section *)

  Definition simrel_thread_local_impl thread smode state local :=
    let memory := (Configuration.memory PC) in
    let threads := (Configuration.threads PC) in
    ⟪ TNNULL : thread <> tid_init ⟫ /\
    ⟪ GPC : wf_thread_state thread state ⟫ /\
    ⟪ RMWRES : rmw_is_rex_instrs (instrs state) ⟫ /\
    ⟪ LLH : IdentMap.find thread threads =
            Some (existT _ (thread_lts thread) state, local) ⟫ /\
    ⟪ PROM_DISJOINT :
        forall thread' langst' local'
          (TNEQ : thread <> thread')
          (TID' : IdentMap.find thread' threads = Some (langst', local')),
        forall loc to,
          Memory.get loc to local .(Local.promises) = None \/
          Memory.get loc to local'.(Local.promises) = None ⟫ /\

    ⟪ SIM_PROM  : sim_prom Gf sc T f_to f_from thread (Local.promises local) ⟫ /\
    ⟪ SIM_RPROM : sim_res_prom Gf T f_to f_from thread (Local.promises local) ⟫ /\

    ⟪ SIM_MEM : sim_mem Gf sc T f_to f_from thread local memory ⟫ /\
    ⟪ SIM_RES_MEM : sim_res_mem Gf T f_to f_from thread local memory ⟫ /\
    ⟪ SIM_TVIEW : sim_tview Gf sc (covered T) f_to (Local.tview local) thread ⟫ /\
    ⟪ PLN_RLX_EQ : pln_rlx_eq (Local.tview local) ⟫ /\
    ⟪ MEM_CLOSE : memory_close (Local.tview local) memory ⟫ /\
    ⟪ STATE : @sim_state Gf smode (covered T) thread state ⟫.

  Lemma simrel_thread_local_equiv smode:
    simrel_thread_local Gf sc PC T f_to f_from thread smode <->
    exists state local, simrel_thread_local_impl thread smode state local.
  Proof using. vauto. Qed.  


  (* TODO: merge with Lab'Properties ? *)
  Section SimRelCert.
    Variable (state'' state s': ProgToExecution.state).
    Variable (local: Local.t). 
    Variable (new_value: actid -> actid). 
    Hypothesis (STEPS'' : (step thread)＊ state state''). 
    Hypothesis (TEH'': thread_restricted_execution G thread (ProgToExecution.G state'')).
    Hypothesis (NV: forall x, (new_rfe_ex)⁻¹ x (new_value x)). 
    Hypothesis (RECP : receptiveness_def thread state state'' s'
                                         (E0 Gf T thread \₁ D G T thread)
                                         (new_val new_value)).
    Hypothesis STATE0: simrel_thread_local_impl thread sim_normal state local.
    Hypothesis (SAME: same_lab_u2v (lab (ProgToExecution.G s'))
                                   (lab (ProgToExecution.G state''))). 


    Lemma simrel_cert_common:
      simrel_common (certG G Gsc T S thread (lab' s')) Gsc PC
                    {| covered := covered T ∪₁ acts_set G ∩₁ NTid_ thread;
                       issued := issued T |}
                    (issued T ∪₁ S ∩₁ Tid_ thread) f_to f_from sim_certification.
    Proof using WF TEH'' SIMREL RECP NV IMMCON FAIRf Gf_THREADS_BOUND TLS_FIN.
      cdes SIMREL. cdes COMMON. cdes RECP.
      (* TODO: eauto doesn't use hints? *)
      red. splits; eauto; simpls; try by apply SIMREL.
      { erewrite same_lab_u2v_is_rlx; eauto using SAME'.
        rewrite <- cert_E. rewrite acts_G_in_acts_Gf; eauto. }
      { erewrite same_lab_u2v_is_ra; eauto  using SAME'. 
        rewrite <- cert_E, cert_F; eauto using SAME'. }
      { eapply ETCCOH_cert; eauto using SAME_VAL_RF_CERT, SAME_VAL, WF_CERT, WF_SC_CERT, SAME'.  
      }
      { erewrite same_lab_u2v_is_rel; eauto using SAME'.
        erewrite same_lab_u2v_is_w; eauto using SAME'.
        rewrite RELCOV_G. basic_solver. }
      { ins.
        assert (acts_set G r) as ER.
        { apply (dom_l (wf_rmwE WF_G)) in RMW. apply seq_eqv_l in RMW. desf. }
        assert (acts_set G w) as EW.
        { apply (dom_r (wf_rmwE WF_G)) in RMW. apply seq_eqv_r in RMW. desf. }
        set (RMW' := RMW).
        apply rmw_G_rmw_Gf in RMW'.
        apply seq_eqv_l in RMW'. destruct RMW' as [EER RMW'].
        apply seq_eqv_r in RMW'. destruct RMW' as [RMW' EEW].
        assert (tid r = tid w) as TIDRW.
        { by apply (wf_rmwt WF). }
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
        erewrite same_lab_u2v_is_sc; eauto using SAME'.
        erewrite same_lab_u2v_is_f; eauto using SAME'.
        unfold certG, acts_set. simpls.
        unfold G.
        arewrite (acts_set (rstG Gf T S thread) ⊆₁ acts_set (rstG Gf T S thread)).
        erewrite E_F_Sc_in_C; eauto.
        basic_solver. }
      { rewrite same_lab_u2v_R_ex; eauto  using SAME'. }
      splits.
      { unfold G.
        erewrite <- cert_co_for_split with (G:=rstG Gf T S thread); eauto.
        unfold cert_co_base.
        hahn_frame. apply eqv_rel_mori.
        apply AuxRel.set_compl_mori. red.
          by erewrite Grfi_in_cert_rfi with (G:=rstG Gf T S thread); eauto. }
      
      unfold G. unfold W_ex. rewrite cert_sb. unfold certG. simpls.
      rewrite <- seqA, codom_eqv1.
      arewrite (codom_rel (⦗E0 Gf T S thread⦘ ⨾ rmw Gf) ⊆₁ is_w (lab Gf)).
      { rewrite (wf_rmwD WF). basic_solver. }
      (* TODO: introduce a lemma *)
      arewrite (E0 Gf T S thread ⊆₁ E0 Gf T S thread ∩₁ E0 Gf T S thread).
      rewrite <- set_interA.
      unfold E0 at 1. rewrite !set_inter_union_r, !set_inter_union_l.
      unionL.
      4: { rewrite (wf_rmwD WF). type_solver 10. }
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
      all: apply in_filterP_iff; splits; auto. 
      Unshelve. all: done || exact (fun _ => Afence Opln).
    Qed.

    Lemma simrel_cert_local:
      simrel_thread_local (certG G Gsc T S thread (lab' s')) Gsc PC
                          {| covered := covered T ∪₁ acts_set G ∩₁ NTid_ thread; issued := issued T |}
                          (issued T ∪₁ S ∩₁ Tid_ thread) f_to f_from thread sim_certification. 
    Proof using WF TEH'' STATE0 SIMREL SAME RECP NV IMMCON FAIRf Gf_THREADS_BOUND TLS_FIN.
      cdes STATE0.
      red. splits.
      assert (same_lab_u2v (lab' s') (lab Gf)) as SAME_.      
      { erewrite <- lab_G_eq_lab_Gf; eauto using SAME'. }
      eexists. eexists. splits; eauto.
      all: eauto.
      { red. ins. eapply SIM_PROM in PROM. (* sim_prom *)
        desc. exists b0. splits; auto.
        { unfold certG. unfold acts_set. simpls.
          unfold G. unfold rstG, restrict. simpls. split; auto.
          red. left. left. by right. }
        { intros [HH|[_ HH]]; desf. }
        { erewrite same_lab_u2v_loc; eauto. }
        cdes HELPER.
        red. splits; auto.
        { unfold certG; simpls.
          erewrite ISS_OLD; eauto. }
        intros ll. specialize (SIMMSG ll).
        eapply max_value_same_set; eauto.
        split; (intros x [AA|AA]; [left|right]).
        4: { erewrite <- same_lab_u2v_loc in AA; eauto. }
        2: { erewrite same_lab_u2v_loc in AA; eauto. }
        { assert ((msg_rel Gf sc ll ⨾ ⦗ issued T ⦘) x b0) as XX.
          2: { apply seq_eqv_r in XX. desf. }
          eapply msg_rel_I; eauto.
          eapply cert_msg_rel with (lab':= (lab' s')); eauto.
          all: unfold G; eauto.
          all: try by unfold rst_sc; rewrite <- HeqGsc.
          apply seq_eqv_r. split; eauto. }
        assert ((msg_rel (certG G Gsc T S thread (lab' s')) Gsc ll ⨾ ⦗ issued T ⦘) x b0) as XX.
        2: { apply seq_eqv_r in XX. desf. }
        unfold G. simpl. 
        eapply cert_msg_rel; eauto.  
        unfold G. 
        eapply msg_rel_I; eauto.
        apply seq_eqv_r. split; auto. }
      { red. ins. (* sim_res_prom *)
        eapply SIM_RPROM in RES.
        desc.
        assert (acts_set Gf b0) as FEB.
        { by apply (etc_S_in_E ETCCOH). }
        assert (acts_set G b0) as EB.
        { subst. eapply ST_in_E; eauto. by split. }

        (* Some commented out code removed from there. 
           See ad483e9 commit *)
        
        exists b0. splits; auto.
        { right. by split. }
        erewrite same_lab_u2v_loc in LOC; eauto.
        rewrite <- lab_G_eq_lab_Gf; eauto.
          by apply same_lab_u2v_comm. }
      { red. ins. (* sim_mem *)
        edestruct SIM_MEM with (b:=b0) as [rel_opt]; eauto.
        { erewrite same_lab_u2v_loc in LOC; eauto. }
        { erewrite <- ISS_OLD; eauto. }
        simpls. desc.
        exists rel_opt.
        splits; eauto.
        { red. cdes HELPER. splits; eauto.
          intros ll. specialize (SIMMSG ll).
          eapply max_value_same_set; eauto.
          split; (intros x [AA|AA]; [left|right]).
          4: { erewrite <- same_lab_u2v_loc in AA; eauto. }
          2: { erewrite same_lab_u2v_loc in AA; eauto. }
          { assert ((msg_rel Gf sc ll ⨾ ⦗ issued T ⦘) x b0) as XX.
            2: { apply seq_eqv_r in XX. desf. }
            eapply msg_rel_I; eauto.
            eapply cert_msg_rel with (lab':=(lab' s')); eauto.
            apply seq_eqv_r. split; auto. }
          assert ((msg_rel (certG G Gsc T S thread (lab' s')) Gsc ll ⨾ ⦗ issued T ⦘) x b0) as XX.
          2: { apply seq_eqv_r in XX. desf. }
          unfold G.          
          eapply cert_msg_rel; eauto.
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
          { unfold E0; left; right; exists b0.
            generalize (rmw_in_sb WF); basic_solver 12. }
          assert ((E0 Gf T S thread) b0).
          { unfold E0; left; left; right; basic_solver 12. }
          assert ((E0 Gf T S thread) p).
          { unfold E0; left; left; right; basic_solver 12. }
          assert ((rmw G) z b0).
          apply rmw_G_rmw_Gf; basic_solver 12.
          exists z; splits; [|done].
          cut ((cert_rf G Gsc T S thread ⨾ ⦗D G T S thread⦘) p z).
          { clear. basic_solver. }
          apply cert_rf_D; auto. apply seq_eqv_r. split; auto.
          {  unfold G, rstG. unfold restrict. ins.
             apply seq_eqv_lr. splits; auto. }
          eapply dom_rmw_D; eauto. exists b0.
          apply seq_eqv_r. split; auto. by apply I_in_D. }
        exists p_v. splits; eauto.
        erewrite ISS_OLD; eauto. }
      { red. ins.
        assert (loc (lab Gf) b0 = Some l) as AA.
        { rewrite <- LOC. symmetry.
          erewrite same_lab_u2v_loc; eauto.
          (* by rewrite <- lab_G_eq_lab_Gf. *)
        }
        apply SIM_RES_MEM; auto. }
      { red. splits; red; ins. (* sim_tview *)
        { assert
            (t_cur (certG G Gsc T S thread (lab' s')) Gsc thread l
                   (covered T ∪₁ acts_set G ∩₁ NTid_ thread) ≡₁
                   t_cur Gf sc thread l (covered T)) as XX.
          2: { eapply max_value_same_set; eauto. apply SIM_TVIEW. }
          
          rewrite cert_t_cur_thread; try by eauto. 
          arewrite (Gsc ≡ (rst_sc Gf sc T S thread)).
          subst; eapply t_cur_thread; eauto. }
        { assert
            (t_acq (certG G Gsc T S thread (lab' s')) Gsc thread l
                   (covered T ∪₁ acts_set G ∩₁ NTid_ thread) ≡₁
                   t_acq Gf sc thread l (covered T)) as XX.
          2: { eapply max_value_same_set; eauto. apply SIM_TVIEW. }
          
          rewrite cert_t_acq_thread; eauto.
          arewrite (Gsc ≡ (rst_sc Gf sc T S thread)).
          subst; eapply t_acq_thread; eauto. }
        
        assert (t_rel (certG G Gsc T S thread (lab' s')) Gsc thread l l'
                      (covered T ∪₁ acts_set G ∩₁ NTid_ thread) ≡₁
                      t_rel Gf sc thread l l' (covered T)) as XX.
        { rewrite cert_t_rel_thread; eauto.
          arewrite (Gsc ≡ (rst_sc Gf sc T S thread)).
          subst; eapply t_rel_thread; eauto. }
        
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
      { cdes STATE. 
        ins. split.
        2: { intros HH. left. by apply PCOV. }
        intros [HH|[_ HH]]; simpls.
          by apply PCOV. }
      cdes RECP.
      eexists. red. splits.
      { apply STEPS'. }
      { intros HH. inv HH. }
      
      eapply YY; eauto.  
    Qed.                   
    
  End SimRelCert.

  Lemma cert_graph_init:
    exists G' sc' T' S',
      ⟪ WF : Wf G' ⟫ /\
      ⟪ IMMCON : imm_consistent G' sc' ⟫ /\
      ⟪ NTID  : NTid_ thread ∩₁ G'.(acts_set) ⊆₁ covered T' ⟫ /\
      ⟪ SIMREL : simrel_thread G' sc' PC T' S' f_to f_from thread sim_certification ⟫ /\
      ⟪ FIN': fin_exec G' ⟫ /\
      ⟪ FAIR': mem_fair G' ⟫. 
  Proof using WF T SIMREL S IMMCON FAIRf TLS_FIN Gf_THREADS_BOUND.
    cdes SIMREL.
    forward eapply (proj1 (simrel_thread_local_equiv sim_normal)); eauto.
    rename LOCAL into LOCAL_. ins. desc. rename H into LOCAL. cdes LOCAL.    
    red in STATE. desc. cdes STATE0.
    
    assert (wf_thread_state thread state') as GPC'. 
    { eapply wf_thread_state_steps; eauto. }

    forward eapply CTINDEX; eauto. ins. desc. 
    forward eapply STATE''; eauto. ins. desc. 
    
    assert (acts_set (ProgToExecution.G state) ⊆₁ covered T) as STATECOV.
    { intros x EE. apply (acts_rep GPC) in EE. desc. subst. by apply PCOV. }

    assert (exists new_value, forall x, (new_rfe_ex)⁻¹ x (new_value x)) as H0; desc.
    { apply (unique_choice (new_rfe_ex)⁻¹ (new_rfe_unique)). }

    set (new_val := new_val new_value). 
    
    forward eapply (@receptiveness_impl state state'' new_val); eauto.
    intros RECP. desc. cdes RECP. 
    
    assert (fin_exec (certG G Gsc T S thread (lab' s'))) as FIN'. 
    { apply fin_exec_same_events with (G := G); done. }

    exists (certG G Gsc T S thread (lab' s')).
    exists Gsc.
    exists (mkTC ((covered T) ∪₁ ((acts_set G) ∩₁ NTid_ thread)) (issued T)).
    exists ((issued T) ∪₁ S ∩₁ Tid_ thread).    
    
    splits; eauto using WF_CERT. 
    { eapply cert_imm_consistent;
        eauto using WF_CERT, WF_SC_CERT, FACQREL, SAME_VAL_RF_CERT, SAME_VAL, SAME'. }
    { unfold certG, acts_set; ins; basic_solver. }
    { red. splits; eauto using simrel_cert_common, simrel_cert_local. }
    apply fin_exec_fair; eauto using WF_CERT. 
  Qed.

End CertGraphInit.
