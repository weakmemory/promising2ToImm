From hahn Require Import Hahn.

From imm Require Import Events.
From imm Require Import Execution.
From imm Require Import Execution_eco.
From imm Require Import imm_bob imm_s_ppo.
From imm Require Import imm_s_hb.
From imm Require Import imm_s.
From imm Require Import imm_common_more.
From imm Require Import CertCOhelper.
From imm Require Import CombRelations.

From imm Require Import AuxRel2.
From imm Require Import TraversalConfig.
From imm Require Import TraversalConfigAlt.
From imm Require Import TraversalConfigAltOld.
From imm Require Import FinExecution. 
Require Import ExtTraversalConfig.

Require Import Cert_co.
Require Import Cert_D.
Require Import Cert_rf.
Require Import CertExecution2.
Require Import Cert_hb.

Set Implicit Arguments.

Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'NTid_' t" := (fun x => tid x <> t) (at level 1).

Section CertExec_views.

Variable G : execution.
Variable sc : relation actid.

Notation "'Init'" := (fun a => is_true (is_init a)).

Notation "'E'" := (acts_set G).
(* Notation "'Gacts'" := (acts G). *)
Notation "'Glab'" := (lab G).
Notation "'Gsb'" := (sb G).
Notation "'Grf'" := (rf G).
Notation "'Gco'" := (co G).
Notation "'Grmw'" := (rmw G).
Notation "'Gdata'" := (data G).
Notation "'Gaddr'" := (addr G).
Notation "'Gctrl'" := (ctrl G).
Notation "'Gdeps'" := (deps G).
Notation "'Grmw_dep'" := (rmw_dep G).

Notation "'Gfre'" := (fre G).
Notation "'Grfe'" := (rfe G).
Notation "'Gcoe'" := (coe G).
Notation "'Grfi'" := (rfi G).
Notation "'Gfri'" := (fri G).
Notation "'Gcoi'" := (coi G).
Notation "'Gfr'" := (fr G).
Notation "'Geco'" := (eco G).
Notation "'Gdetour'" := (detour G).
Notation "'Gsw'" := (sw G).
Notation "'Grelease'" := (release G).
Notation "'Grs'" := (rs G).
Notation "'Ghb'" := (hb G).
Notation "'Gppo'" := (ppo G).
Notation "'Grppo'" := (rppo G).
Notation "'Gbob'" := (bob G).
Notation "'Gfwbob'" := (fwbob G).
Notation "'Gar'" := ((ar G) sc).
Notation "'Gar_int'" := ((ar_int G)).
Notation "'Gurr'" := ((urr G) sc).
Notation "'Gfurr'" := ((furr G) sc).
Notation "'Gmsg_rel'" := ((msg_rel G) sc).

Notation "'Gloc'" := (loc Glab).
Notation "'Gval'" := (val Glab).
Notation "'Gsame_loc'" := (same_loc Glab).

Notation "'R'" := (fun a => is_true (is_r Glab a)).
Notation "'W'" := (fun a => is_true (is_w Glab a)).
Notation "'F'" := (fun a => is_true (is_f Glab a)).
Notation "'GR_ex'" := (fun a => is_true (R_ex Glab a)).
Notation "'GW_ex'" := (W_ex G).
Notation "'GW_ex_acq'" := (GW_ex ∩₁ (fun a => is_true (is_xacq Glab a))).

Notation "'Loc_' l" := (fun x => Gloc x = Some l) (at level 1).
Notation "'W_' l" := (W ∩₁ Loc_ l) (at level 1).
Notation "'R_' l" := (R ∩₁ Loc_ l) (at level 1).

Notation "'Pln'" := (fun a => is_true (is_only_pln Glab a)).
Notation "'Rlx'" := (fun a => is_true (is_rlx Glab a)).
Notation "'Rel'" := (fun a => is_true (is_rel Glab a)).
Notation "'Acq'" := (fun a => is_true (is_acq Glab a)).
Notation "'Acqrel'" := (fun a => is_true (is_acqrel Glab a)).
Notation "'Acq/Rel'" := (fun a => is_true (is_ra Glab a)).
Notation "'Sc'" := (fun a => is_true (is_sc Glab a)).
Notation "'xacq'" := (fun a => is_true (is_xacq Glab a)).


Variable T : trav_config.
Variable S : actid -> Prop.

Notation "'I'" := (issued T).
Notation "'C'" := (covered T).

Variable thread : BinNums.positive.

Notation "'cert_co'" := (cert_co G T thread).

Notation "'D'" := (D G T S thread).

Notation "'new_rf'" := (new_rf G sc T S thread).
Notation "'cert_rf'" := (cert_rf G sc T S thread).
Notation "'cert_rfi'" := (cert_rfi G sc T S thread).
Notation "'cert_rfe'" := (cert_rfe G sc T S thread).

Hypothesis WF : Wf G.
Hypothesis WF_SC : wf_sc G sc.
Hypothesis RELCOV : W ∩₁ Rel ∩₁ I ⊆₁ C.
Hypothesis TCCOH : tc_coherent G sc T.
Hypothesis ACYC_EXT : acyc_ext G sc.
Hypothesis CSC : coh_sc G sc.
Hypothesis COH : coherence G.
Hypothesis AT : rmw_atomicity G.
Hypothesis FIN : fin_exec G. 

Hypothesis IT_new_co: I ∪₁ E ∩₁ W ∩₁ Tid_ thread ≡₁ E ∩₁ W.
Hypothesis E_to_S: E ⊆₁ C ∪₁ dom_rel (Gsb^? ⨾ ⦗S⦘).
Hypothesis Grfe_E : dom_rel Grfe ⊆₁ I.
Hypothesis E_F_AcqRel_in_C: E ∩₁ F ∩₁ Acq/Rel ⊆₁ C.
Hypothesis COMP_ACQ: forall r (IN: (E ∩₁ R ∩₁ Acq) r), exists w, Grf w r.
Hypothesis urr_helper: dom_rel ((Ghb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ sc^? ⨾ Ghb^? ⨾ Grelease ⨾ ⦗I⦘) ⊆₁ C.
Hypothesis urr_helper_C: dom_rel ((Ghb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ sc^? ⨾ Ghb^? ⨾ (Grelease ⨾ Grf)^? ⨾ ⦗C⦘) ⊆₁ C.
Hypothesis W_hb_sc_hb_to_I_NTid: dom_rel (⦗W⦘ ⨾ Ghb ⨾ (sc ⨾ Ghb)^? ⨾ ⦗I ∩₁ NTid_ thread⦘) ⊆₁ I.
Hypothesis detour_E : dom_rel (Gdetour ⨾ ⦗E ∩₁ NTid_ thread⦘) ⊆₁ I.
Hypothesis detour_Acq_E : dom_rel (Gdetour ⨾ ⦗E ∩₁ R ∩₁ Acq⦘) ⊆₁ I.
Hypothesis hb_sc_hb_de : ⦗(E \₁ C) ∩₁ (E \₁ I)⦘ ⨾ Ghb ⨾ (sc ⨾ Ghb)^? ⊆ Gsb.
Hypothesis COMP_C : C ∩₁ R ⊆₁ codom_rel Grf.
Hypothesis COMP_NTID : E ∩₁ NTid_ thread ∩₁ R ⊆₁ codom_rel Grf.
Hypothesis COMP_PPO : dom_rel (Gppo ⨾ ⦗I⦘) ⊆₁ codom_rel Grf.
Hypothesis COMP_RPPO : dom_rel (⦗R⦘ ⨾ (Gdata ∪ Grfi ∪ Grmw)＊ ⨾ Grppo ⨾ ⦗S⦘) ⊆₁ codom_rel Grf.
Hypothesis TCCOH_rst_new_T : tc_coherent G sc (mkTC (C ∪₁ (E ∩₁ NTid_ thread)) I).

Hypothesis S_in_W : S ⊆₁ W.
Hypothesis RPPO_S : dom_rel ((Gdetour ∪ Grfe) ⨾ (Gdata ∪ Grfi ∪ Grmw)＊ ⨾ Grppo ⨾ ⦗S⦘) ⊆₁ I.
Hypothesis RMW_S : dom_rel ((Gdetour ∪ Grfe) ⨾ Grmw ⨾ ⦗S⦘) ⊆₁ I.
Hypothesis ST_in_E : S ∩₁ Tid_ thread ⊆₁ E.
Hypothesis I_in_S : I ⊆₁ S.

Hypothesis F_in_C : E ∩₁ F ∩₁ Acq/Rel ⊆₁ C.

Hypothesis S_I_in_W_ex : (S ∩₁ Tid_ thread) \₁ I ⊆₁ W_ex G.

Hypothesis ETC_DR_R_ACQ_I : dom_rel ((Gdetour ∪ Grfe) ⨾ (Grmw ⨾ Grfi)＊ ⨾ ⦗R∩₁Acq⦘ ⨾ Gsb ⨾ ⦗S⦘) ⊆₁ I.

Hypothesis COMP_R_ACQ_SB : dom_rel ((Grmw ⨾ Grfi)＊ ⨾ ⦗E ∩₁ R ∩₁ Acq⦘) ⊆₁ codom_rel Grf.
Hypothesis RMWREX : dom_rel Grmw ⊆₁ GR_ex.

Variable lab' : actid -> label.
Hypothesis SAME : same_lab_u2v lab' Glab.

Notation "'certG'" := (certG G sc T S thread lab').


(* Notation "'CE'" := (acts_set certG). *)
(* Notation "'Cacts'" := (acts certG). *)
(* Notation "'Clab'" := (lab certG). *)
(* Notation "'Csb'" := (sb certG). *)
Notation "'Crf'" := (rf certG).
Notation "'Cco'" := (co certG).
Notation "'Crmw'" := (rmw certG).
(* Notation "'Cdata'" := (data certG). *)
(* Notation "'Caddr'" := (addr certG). *)
(* Notation "'Cctrl'" := (ctrl certG). *)
Notation "'Cdeps'" := (deps certG).
(* Notation "'Crmw_dep'" := (rmw_dep certG). *)

Notation "'Cfre'" := (fre certG).
(* Notation "'Crfe'" := (rfe certG). *)
Notation "'Ccoe'" := (coe certG).
Notation "'Crfi'" := (rfi certG).
Notation "'Cfri'" := (fri certG).
Notation "'Ccoi'" := (coi certG).
Notation "'Cfr'" := (fr certG).
Notation "'Ceco'" := (eco certG).
Notation "'Cdetour'" := (detour certG).
Notation "'Csw'" := (sw certG).
Notation "'Crelease'" := (release certG).
Notation "'Crs'" := (rs certG).
Notation "'Chb'" := (hb certG).
Notation "'Cppo'" := (ppo certG).
(* Notation "'Cbob'" := (bob certG). *)
(* Notation "'Cfwbob'" := (fwbob certG). *)
Notation "'Car'" := ((ar certG) sc).
Notation "'Car_int'" := ((ar_int certG)).
Notation "'Curr'" := ((urr certG) sc).
Notation "'Cmsg_rel'" := ((msg_rel certG) sc).

(* Notation "'E'" := (acts_set G). *)
(* Notation "'Gacts'" := (acts G). *)
Notation "'Clab'" := (lab certG).
Notation "'Csb'" := (sb certG).
(* Notation "'Grf'" := (rf G). *)
(* Notation "'Gco'" := (co G). *)
(* Notation "'Gdata'" := (data G). *)
(* Notation "'Gaddr'" := (addr G). *)
(* Notation "'Gctrl'" := (ctrl G). *)
(* Notation "'Gdeps'" := (deps G). *)
(* Notation "'Grmw_dep'" := (rmw_dep G). *)

(* Notation "'Gfre'" := (fre G). *)
Notation "'Crfe'" := (rfe certG).
(* Notation "'Gcoe'" := (coe G). *)
Notation "'Crfi'" := (rfi certG).
(* Notation "'Gfri'" := (fri G). *)
(* Notation "'Gcoi'" := (coi G). *)
(* Notation "'Gfr'" := (fr G). *)
(* Notation "'Geco'" := (eco G). *)
(* Notation "'Gdetour'" := (detour G). *)
(* Notation "'Gsw'" := (sw G). *)
Notation "'Crelease'" := (release certG).
(* Notation "'Grs'" := (rs G). *)
(* Notation "'Ghb'" := (hb G). *)
(* Notation "'Gppo'" := (ppo G). *)
(* Notation "'Grppo'" := (rppo G). *)
(* Notation "'Gbob'" := (bob G). *)
(* Notation "'Gfwbob'" := (fwbob G). *)
(* Notation "'Gar'" := ((ar G) sc). *)
(* Notation "'Gar_int'" := ((ar_int G)). *)
(* Notation "'Gurr'" := ((urr G) sc). *)
(* Notation "'Gfurr'" := ((furr G) sc). *)
(* Notation "'Gmsg_rel'" := ((msg_rel G) sc). *)

(* Notation "'Gloc'" := (loc Glab). *)
(* Notation "'Gval'" := (val Glab). *)
Notation "'Csame_loc'" := (same_loc Clab).

Notation "'CR'" := (fun a => is_true (is_r Clab a)).
Notation "'CW'" := (fun a => is_true (is_w Clab a)).
Notation "'CF'" := (fun a => is_true (is_f Clab a)).
(* Notation "'GR_ex'" := (fun a => is_true (R_ex Glab a)). *)
(* Notation "'GW_ex'" := (W_ex G). *)
(* Notation "'GW_ex_acq'" := (GW_ex ∩₁ (fun a => is_true (is_xacq Glab a))). *)

Notation "'CPln'" := (fun a => is_true (is_only_pln Clab a)).
Notation "'CRlx'" := (fun a => is_true (is_rlx Clab a)).
Notation "'CRel'" := (fun a => is_true (is_rel Clab a)).
Notation "'CAcq'" := (fun a => is_true (is_acq Clab a)).
Notation "'CAcqrel'" := (fun a => is_true (is_acqrel Clab a)).
Notation "'CAcq/Rel'" := (fun a => is_true (is_ra Clab a)).
Notation "'CSc'" := (fun a => is_true (is_sc Clab a)).


Lemma cert_msg_rel l : Cmsg_rel l ⨾ ⦗I⦘ ≡ Gmsg_rel l ⨾ ⦗I⦘.
Proof using All.
  unfold CombRelations.msg_rel, urr.
  rewrite (cert_W_ _ SAME).
  rewrite (cert_F _ SAME).
  rewrite (cert_Sc _ SAME).
  rewrite (cert_hb); eauto.
  rewrite !seqA.
  arewrite (Crelease ⨾ ⦗I⦘ ≡ Grelease ⨾ ⦗I⦘).
  { arewrite (⦗I⦘ ≡ ⦗D⦘ ⨾ ⦗I⦘).
    { generalize I_in_D. clear. basic_solver. }
    arewrite (Crelease ⨾ ⦗D⦘ ≡ Grelease ⨾ ⦗D⦘).
    { apply Crelease_D_eq_Grelease_D; eauto. }
    done. }
  arewrite ((Ghb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ sc^? ⨾ Ghb^? ⨾ Grelease ⨾ ⦗I⦘ ≡
            ⦗C⦘ ⨾ (Ghb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ sc^? ⨾ Ghb^? ⨾ Grelease ⨾ ⦗I⦘).
  { split; [|basic_solver 21].
      by rewrite (dom_rel_helper (urr_helper)) at 1. }

  arewrite (Crf^? ⨾ ⦗C⦘ ≡ Grf^? ⨾ ⦗C⦘).
  rewrite !crE; relsf.
  arewrite (⦗C⦘ ≡ ⦗C⦘ ⨾ ⦗C⦘) at 2 by basic_solver.
  arewrite (⦗C⦘ ≡ ⦗C⦘ ⨾ ⦗C⦘) at 5 by basic_solver.
  split; unionL; try basic_solver.
  { rewrite C_in_D with (G:=G) (T:=T) (S:=S) (thread:= thread) at 1.
    arewrite (Crf ⨾ ⦗D⦘ ⊆ Grf ⨾ ⦗ D ⦘).
    { apply cert_rf_D; auto. } 
    clear. basic_solver. }
  2: done.
  rewrite C_in_D with (G:=G) (T:=T) (S:=S) (thread:= thread) at 1.
  arewrite (Grf ⨾ ⦗D⦘ ⊆ Crf ⨾ ⦗ D ⦘).
  { by apply cert_rf_D. }
  clear. basic_solver.
Qed.

Lemma cert_t_cur_thread l : t_cur certG sc thread l
  (covered T ∪₁ E ∩₁ NTid_ thread) ≡₁ t_cur G sc thread l (covered T).
Proof using All.
  unfold t_cur, c_cur, urr.
  rewrite (cert_W_ _ SAME).
  rewrite (cert_F _ SAME).
  rewrite (cert_Sc _ SAME).
  rewrite (cert_hb); eauto.
  rewrite !seqA.

  arewrite  (⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C ∪₁ E ∩₁ NTid_ thread⦘ ≡  ⦗C⦘ ⨾ ⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C⦘).
  { unfolder; splits; ins; desf; splits; eauto.
    all: by apply (init_covered TCCOH); split; eauto; apply (sub_E_in SUB). }
  arewrite (⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C⦘ ≡ ⦗C⦘ ⨾ ⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C⦘) at 2 by basic_solver 12.

  arewrite ((Ghb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ sc^? ⨾ Ghb^? ⨾ ⦗C⦘ ≡ ⦗C⦘ ⨾ (Ghb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ sc^? ⨾ Ghb^? ⨾ ⦗C⦘).
  { split; generalize (urr_helper_C); clear; basic_solver 21. }

  remember (dom_rel
              (⦗W_ l⦘ ⨾ Crf^? ⨾ ⦗C⦘ ⨾ (Ghb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ sc^? ⨾ Ghb^? ⨾ ⦗C⦘ ⨾
                      ⦗C⦘ ⨾ ⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C⦘)) as X.

  arewrite ((Ghb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ sc^? ⨾ Ghb^? ⨾ ⦗C⦘ ≡
            ⦗C⦘ ⨾ (Ghb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ sc^? ⨾ Ghb^? ⨾ ⦗C⦘).
  { split; generalize (urr_helper_C); clear; basic_solver 21. }
  subst.

  arewrite (Crf^? ⨾ ⦗C⦘ ≡ Grf^? ⨾ ⦗C⦘).
  2: done.
  arewrite (⦗C⦘ ≡ ⦗D⦘ ⨾ ⦗C⦘).
  split.
  generalize C_in_D; basic_solver.
  basic_solver. 
  rewrite !crE; relsf. 
  arewrite (Crf ⨾ ⦗D⦘ ≡ Grf ⨾ ⦗ D ⦘).
  { apply cert_rf_D; basic_solver. }
  clear. basic_solver.
Qed.

Lemma cert_t_rel_thread l l' : t_rel certG sc thread l l'
  (covered T ∪₁ E ∩₁ NTid_ thread) ≡₁ t_rel G sc thread l l' (covered T).
Proof using All.
  unfold t_rel, c_rel, urr.
  rewrite !(cert_W_ _ SAME).
  rewrite (cert_F _ SAME).
  rewrite (cert_Sc _ SAME).
  rewrite (cert_Rel _ SAME).
  rewrite (cert_hb); eauto.
  rewrite !seqA.

  arewrite  (⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C ∪₁ E ∩₁ NTid_ thread⦘ ≡  ⦗C⦘ ⨾ ⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C⦘).
  { unfolder; splits; ins; desf; splits; eauto.
    all: by apply (init_covered TCCOH); split; eauto; apply (sub_E_in SUB). }

  arewrite (⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C⦘ ≡ ⦗C⦘ ⨾ ⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C⦘) at 2 by basic_solver 12.
  arewrite (⦗Rel⦘ ⨾ ⦗W_ l' ∪₁ F⦘ ⨾ ⦗C⦘ ≡ ⦗C⦘ ⨾ ⦗Rel⦘ ⨾ ⦗W_ l' ∪₁ F⦘) by basic_solver 12.
  arewrite ((Ghb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ sc^? ⨾ Ghb^? ⨾ ⦗C⦘ ≡ ⦗C⦘ ⨾ (Ghb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ sc^? ⨾ Ghb^? ⨾ ⦗C⦘).
  { split; generalize (urr_helper_C); clear; basic_solver 21. }

  remember (dom_rel (⦗W_ l⦘ ⨾ Crf^? ⨾ ⦗C⦘ ⨾ (Ghb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ sc^? ⨾ Ghb^? ⨾ ⦗C⦘ ⨾
                            ⦗C⦘ ⨾ ⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C⦘)) as X.

  arewrite ((Ghb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ sc^? ⨾ Ghb^? ⨾ ⦗C⦘ ≡
            ⦗C⦘ ⨾ (Ghb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ sc^? ⨾ Ghb^? ⨾ ⦗C⦘).
  { split; generalize (urr_helper_C); clear; basic_solver 21. }
  subst.
  arewrite (Crf^? ⨾ ⦗C⦘ ≡ Grf^? ⨾ ⦗C⦘).
  2: done.
  arewrite (⦗C⦘ ≡ ⦗D⦘ ⨾ ⦗C⦘).
  split.
  generalize C_in_D; basic_solver.
  basic_solver. 
  rewrite !crE; relsf. 
  arewrite (Crf ⨾ ⦗D⦘ ≡ Grf ⨾ ⦗ D ⦘).
  { apply cert_rf_D; basic_solver. }
  basic_solver.
Qed.

Lemma cert_t_acq_thread l : t_acq certG sc thread l
  (covered T ∪₁ E ∩₁ NTid_ thread) ≡₁ t_acq G sc thread l (covered T).
Proof using All.
  unfold t_acq, c_acq, urr.
  rewrite !(cert_W_ _ SAME).
  rewrite (cert_F _ SAME).
  rewrite (cert_Sc _ SAME).
  rewrite (cert_hb); eauto.
  rewrite !seqA.
  arewrite  (⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C ∪₁ E ∩₁ NTid_ thread⦘ ≡  ⦗C⦘ ⨾ ⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C⦘).
  { unfolder; splits; ins; desf; splits; eauto.
    all: by apply (init_covered TCCOH); split; eauto; apply (sub_E_in SUB). }

  arewrite (⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C⦘ ≡ ⦗C⦘ ⨾ ⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C⦘) at 2 by basic_solver 12.
  arewrite ((Crelease ⨾ Crf)^? ⨾ ⦗C⦘ ≡ (Grelease ⨾ Grf)^? ⨾ ⦗C⦘).
  { arewrite (⦗C⦘ ≡ ⦗D⦘ ⨾ ⦗C⦘).
    { split.
      { generalize C_in_D; basic_solver. }
      basic_solver. }
    rewrite !crE; relsf.
    rewrite !seqA.
    arewrite (Crf ⨾ ⦗D⦘ ≡ Grf ⨾ ⦗ D ⦘) by (by apply cert_rf_D).
    apply union_more; [done|].
    rewrite seq_eqvC at 1 2.
    seq_rewrite rf_covered; eauto. rewrite !seqA.
    arewrite (⦗I⦘ ≡ ⦗D⦘ ⨾ ⦗I⦘).
    { generalize I_in_D. clear. basic_solver. }
    arewrite (Crelease ⨾ ⦗D⦘ ≡ Grelease ⨾ ⦗D⦘).
    { apply Crelease_D_eq_Grelease_D; eauto. }
    done. }

  arewrite ((Ghb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ sc^? ⨾ Ghb^? ⨾ (Grelease ⨾ Grf)^? ⨾  ⦗C⦘ ≡
            ⦗C⦘ ⨾ (Ghb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ sc^? ⨾ Ghb^? ⨾ (Grelease ⨾ Grf)^? ⨾ ⦗C⦘).
  { split; generalize (urr_helper_C); clear; basic_solver 21. }

  remember (dom_rel (⦗W_ l⦘ ⨾ Crf^? ⨾ ⦗C⦘ ⨾ (Ghb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ sc^? ⨾ Ghb^? ⨾
                     (Grelease ⨾ Grf)^? ⨾ ⦗C⦘ ⨾ ⦗C⦘ ⨾ ⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C⦘)) as X.

  arewrite ((Ghb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ sc^? ⨾ Ghb^? ⨾ (Grelease ⨾ Grf)^? ⨾ ⦗C⦘ ≡
            ⦗C⦘ ⨾ (Ghb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ sc^? ⨾ Ghb^? ⨾ (Grelease ⨾ Grf)^? ⨾ ⦗C⦘).
  { split; generalize (urr_helper_C); clear; basic_solver 21. }
  subst.
  arewrite (Crf^? ⨾ ⦗C⦘ ≡ Grf^? ⨾ ⦗C⦘).
  2: done.
  arewrite (⦗C⦘ ≡ ⦗D⦘ ⨾ ⦗C⦘).
  split.
  generalize C_in_D; basic_solver.
  basic_solver. 
  rewrite !crE; relsf. 
  arewrite (Crf ⨾ ⦗D⦘ ≡ Grf ⨾ ⦗ D ⦘).
  { apply cert_rf_D; basic_solver. }
  basic_solver.
Qed.

End CertExec_views.
