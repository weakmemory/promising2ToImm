Require Import Setoid.
From hahn Require Import Hahn.
From imm Require Import AuxDef Events Execution Execution_eco
     imm_bob imm_s_ppo imm_s imm_s_hb CombRelations AuxRel2.
(* From imm Require Import TraversalConfig Traversal. *)
Require Import AuxRel.
Require Export ExtTravRelations.
(* From imm Require Import TraversalProperties. *)
Require Import TlsAux.
From imm Require Import TraversalOrder. 
From imm Require Import TLSCoherency. 

Set Implicit Arguments.

Section ExtTraversalConfig.
Variable G : execution.
Variable sc : relation actid.

(* Notation "'acts'" := (acts G). *)
Notation "'sb'" := (sb G).
Notation "'rmw'" := (rmw G).
Notation "'data'" := (data G).
Notation "'addr'" := (addr G).
Notation "'ctrl'" := (ctrl G).
Notation "'rmw_dep'" := (rmw_dep G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'coe'" := (coe G).
Notation "'fr'" := (fr G).

Notation "'eco'" := (eco G).

Notation "'bob'" := (bob G).
Notation "'fwbob'" := (fwbob G).
Notation "'ppo'" := (ppo G).
Notation "'rppo'" := (rppo G).
Notation "'fre'" := (fre G).
Notation "'rfi'" := (rfi G).
Notation "'rfe'" := (rfe G).
Notation "'deps'" := (deps G).
Notation "'detour'" := (detour G).
Notation "'release'" := (release G).
Notation "'sw'" := (sw G).
Notation "'hb'" := (hb G).

Notation "'urr'" := (urr G sc).
Notation "'c_acq'" := (c_acq G sc).
Notation "'c_cur'" := (c_cur G sc).
Notation "'c_rel'" := (c_rel G sc).
Notation "'t_acq'" := (t_acq G sc).
Notation "'t_cur'" := (t_cur G sc).
Notation "'t_rel'" := (t_rel G sc).
Notation "'S_tm'" := (S_tm G).
Notation "'S_tmr'" := (S_tmr G).
Notation "'msg_rel'" := (msg_rel G sc).

Notation "'lab'" := (lab G).
Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'mod'" := (Events.mod lab).
Notation "'same_loc'" := (same_loc lab).

Notation "'E'" := (acts_set G).
Notation "'R'" := (fun x => is_true (is_r lab x)).
Notation "'W'" := (fun x => is_true (is_w lab x)).
Notation "'F'" := (fun x => is_true (is_f lab x)).
Notation "'RW'" := (R ∪₁ W).
Notation "'FR'" := (F ∪₁ R).
Notation "'FW'" := (F ∪₁ W).
Notation "'R_ex'" := (fun a => is_true (R_ex lab a)).
Notation "'W_ex'" := (W_ex G).
Notation "'W_ex_acq'" := (W_ex ∩₁ (fun a => is_true (is_xacq lab a))).

Notation "'Init'" := (fun a => is_true (is_init a)).
Notation "'Loc_' l" := (fun x => loc x = Some l) (at level 1).
Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'W_' l" := (W ∩₁ Loc_ l) (at level 1).

Notation "'Pln'" := (fun x => is_true (is_only_pln lab x)).
Notation "'Rlx'" := (fun x => is_true (is_rlx lab x)).
Notation "'Rel'" := (fun x => is_true (is_rel lab x)).
Notation "'Acq'" := (fun x => is_true (is_acq lab x)).
Notation "'Acqrel'" := (fun x => is_true (is_acqrel lab x)).
Notation "'Sc'" := (fun x => is_true (is_sc lab x)).
Notation "'Acq/Rel'" := (fun a => is_true (is_ra lab a)).

(******************************************************************************)
(** **   *)
(******************************************************************************)

(* Record ext_trav_config := *)
(*   mkETC { etc_TC : trav_config; reserved : actid -> Prop; }. *)

(* Definition eissued  T := issued  (etc_TC T). *)
(* Definition ecovered T := covered (etc_TC T). *)

Definition dom_sb_S_rfrmw (T: trav_label -> Prop) rrf P :=
  dom_rel (sb ⨾ ⦗reserved T⦘) ∩₁ codom_rel (⦗P⦘ ⨾ rrf ⨾ rmw).

(* Record etc_coherent (T : ext_trav_config) := *)
(*   mkETCC { *)
(*   etc_tccoh          : tc_coherent G sc (etc_TC T); *)
(*   etc_S_in_E         : reserved T ⊆₁ E; *)
(*   etc_I_in_S         : eissued T ⊆₁ reserved T; *)
(*   etc_S_I_in_W_ex    : reserved T \₁ eissued T ⊆₁ W_ex; *)
(*   etc_F_sb_S         : dom_rel (⦗F∩₁Acq/Rel⦘ ⨾ sb ⨾ ⦗reserved T⦘) ⊆₁ ecovered T ; *)
(*   etc_dr_R_acq_I     : dom_rel ((detour ∪ rfe) ⨾ (rmw ⨾ rfi)＊ ⨾ ⦗R∩₁Acq⦘ ⨾ sb ⨾ ⦗reserved T⦘) ⊆₁ eissued T ; *)
(*   etc_W_ex_sb_I      : dom_rel (⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗reserved T⦘) ⊆₁ eissued T ; *)
(*   etc_sb_S           : dom_sb_S_rfrmw T (rf ⨾ ⦗R_ex⦘) (eissued T) ⊆₁ reserved T; *)
(*   (* TODO: uncomment the next property for handling FADDs. *) *)
(*   (* etc_sb_Acq_S       : dom_rel ((rmw ⨾ rfi)＊ ⨾ ⦗R∩₁Acq⦘ ⨾ sb ⨾ ⦗reserved T⦘) ∩₁ codom_rel (⦗eissued T⦘ ⨾ rf ⨾ rmw); *) *)
(*   etc_rppo_S         : dom_rel ((detour ∪ rfe) ⨾ (data ∪ rfi ∪ rmw)＊ ⨾ rppo ⨾ ⦗ reserved T ⦘) ⊆₁ eissued T; *)
(*   etc_d_rmw_S        : dom_rel (detour ⨾ rmw ⨾ ⦗ reserved T ⦘) ⊆₁ eissued T; *)
(*   etc_S_W_ex_rfrmw_I : reserved T ∩₁ W_ex ⊆₁ codom_rel (⦗eissued T⦘ ⨾ rf ⨾ rmw); *)
(*  }. *)
Record reserve_coherent (T: trav_label -> Prop) :=
  mkETCC {
  rcoh_S_in_E         : reserved T ⊆₁ E;
  rcoh_I_in_S         : issued T ⊆₁ reserved T;
  rcoh_S_I_in_W_ex    : reserved T \₁ issued T ⊆₁ W_ex;
  rcoh_F_sb_S         : dom_rel (⦗F∩₁Acq/Rel⦘ ⨾ sb ⨾ ⦗reserved T⦘) ⊆₁ covered T ;
  rcoh_dr_R_acq_I     : dom_rel ((detour ∪ rfe) ⨾ (rmw ⨾ rfi)＊ ⨾ ⦗R∩₁Acq⦘ ⨾ sb ⨾ ⦗reserved T⦘) ⊆₁ issued T ;
  rcoh_W_ex_sb_I      : dom_rel (⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗reserved T⦘) ⊆₁ issued T ;
  rcoh_sb_S           : dom_sb_S_rfrmw T (rf ⨾ ⦗R_ex⦘) (issued T) ⊆₁ reserved T;
  (* TODO: uncomment the next property for handling FADDs. *)
  (* rcoh_sb_Acq_S       : dom_rel ((rmw ⨾ rfi)＊ ⨾ ⦗R∩₁Acq⦘ ⨾ sb ⨾ ⦗reserved T⦘) ∩₁ codom_rel (⦗eissued T⦘ ⨾ rf ⨾ rmw); *)
  rcoh_rppo_S         : dom_rel ((detour ∪ rfe) ⨾ (data ∪ rfi ∪ rmw)＊ ⨾ rppo ⨾ ⦗ reserved T ⦘) ⊆₁ issued T;
  rcoh_d_rmw_S        : dom_rel (detour ⨾ rmw ⨾ ⦗ reserved T ⦘) ⊆₁ issued T;
  rcoh_S_W_ex_rfrmw_I : reserved T ∩₁ W_ex ⊆₁ codom_rel (⦗issued T⦘ ⨾ rf ⨾ rmw);
 }.
  

Section Props.

Variable WF : Wf G.
Variable T : trav_label -> Prop. 
Variable TCOH : tls_coherent G T.
Variable RCOH : reserve_coherent T.

Lemma rcoh_rmw_S : dom_rel ((detour ∪ rfe) ⨾ rmw ⨾ ⦗ reserved T ⦘) ⊆₁ issued T.
Proof using WF RCOH.
  rewrite !seq_union_l, dom_union. unionL; [by apply RCOH|].
  rewrite rmw_W_ex, !seqA. rewrite <- id_inter. rewrite set_interC.
  rewrite rcoh_S_W_ex_rfrmw_I; auto. rewrite rfe_in_rf.
  remember (rf ⨾ rmw) as X.
  arewrite (rf ⨾ rmw ⊆ X) by subst.
  unfolder. ins. desf.
  assert (x = z); subst; auto.
  eapply wf_rfrmwf; eauto.
Qed.

(* Lemma eissuedW : eissued T ⊆₁ W. *)
(* Proof using ETCCOH. unfold eissued. eapply issuedW. apply ETCCOH. Qed. *)

Lemma reservedW : reserved T ⊆₁ W.
Proof using WF TCOH RCOH.
  arewrite (reserved T ⊆₁ reserved T \₁ issued T ∪₁ reserved T ∩₁ issued T).
  2: { rewrite issuedW at 2; eauto. rewrite rcoh_S_I_in_W_ex; auto.
       rewrite W_ex_in_W; auto. basic_solver. }
  unfolder. ins.
  destruct (classic (issued T x)); eauto.
Qed.

End Props.
End ExtTraversalConfig.
