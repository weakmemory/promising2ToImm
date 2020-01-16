Require Import Setoid.
From hahn Require Import Hahn.
From imm Require Import AuxDef Events Execution Execution_eco
     imm_bob imm_s_ppo imm_s imm_s_hb CombRelations.
Require Import TraversalConfig Traversal.
Require Import AuxRel AuxRel2.
Require Export ExtTravRelations.
Require Import TraversalProperties.
Require Import ImmProperties.

Set Implicit Arguments.

Section ExtTraversalConfig.
Variable G : execution.
Variable sc : relation actid.

Notation "'acts'" := G.(acts).
Notation "'sb'" := G.(sb).
Notation "'rmw'" := G.(rmw).
Notation "'data'" := G.(data).
Notation "'addr'" := G.(addr).
Notation "'ctrl'" := G.(ctrl).
Notation "'rmw_dep'" := G.(rmw_dep).
Notation "'rf'" := G.(rf).
Notation "'co'" := G.(co).
Notation "'coe'" := G.(coe).
Notation "'fr'" := G.(fr).

Notation "'eco'" := G.(eco).

Notation "'bob'" := G.(bob).
Notation "'fwbob'" := G.(fwbob).
Notation "'ppo'" := G.(ppo).
Notation "'rppo'" := G.(rppo).
Notation "'fre'" := G.(fre).
Notation "'rfi'" := G.(rfi).
Notation "'rfe'" := G.(rfe).
Notation "'deps'" := G.(deps).
Notation "'detour'" := G.(detour).
Notation "'release'" := G.(release).
Notation "'sw'" := G.(sw).
Notation "'hb'" := G.(hb).

Notation "'urr'" := (urr G sc).
Notation "'c_acq'" := (c_acq G sc).
Notation "'c_cur'" := (c_cur G sc).
Notation "'c_rel'" := (c_rel G sc).
Notation "'t_acq'" := (t_acq G sc).
Notation "'t_cur'" := (t_cur G sc).
Notation "'t_rel'" := (t_rel G sc).
Notation "'S_tm'" := G.(S_tm).
Notation "'S_tmr'" := G.(S_tmr).
Notation "'msg_rel'" := (msg_rel G sc).

Notation "'lab'" := G.(lab).
Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'mod'" := (Events.mod lab).
Notation "'same_loc'" := (same_loc lab).

Notation "'E'" := G.(acts_set).
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

Record ext_trav_config :=
  mkETC { etc_TC : trav_config; reserved : actid -> Prop; }.

Definition eissued  T := issued  (etc_TC T).
Definition ecovered T := covered (etc_TC T).

Definition dom_sb_S_rfrmw T rrf P :=
  dom_rel (⦗W_ex⦘ ⨾ sb ⨾ ⦗reserved T⦘) ∩₁ codom_rel (⦗P⦘ ⨾ rrf ⨾ (rmw ∩ ctrl)).

Record etc_coherent (T : ext_trav_config) :=
  mkETCC {
  etc_tccoh          : tc_coherent G sc (etc_TC T);
  etc_S_in_E         : reserved T ⊆₁ E;
  etc_I_in_S         : eissued T ⊆₁ reserved T;
  etc_S_I_in_W_ex    : reserved T \₁ eissued T ⊆₁ W_ex;
  etc_F_sb_S         : dom_rel (⦗F∩₁Acq/Rel⦘ ⨾ sb ⨾ ⦗reserved T⦘) ⊆₁ ecovered T ;
  etc_dr_R_acq_I     : dom_rel ((detour ∪ rfe) ⨾ (rmw ⨾ rfi)^* ⨾ ⦗R∩₁Acq⦘ ⨾ sb ⨾ ⦗reserved T⦘) ⊆₁ eissued T ;
  etc_W_ex_sb_I      : dom_rel (⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗reserved T⦘) ⊆₁ eissued T ;
  etc_sb_S           : dom_sb_S_rfrmw T rf (eissued T) ⊆₁ reserved T;
  etc_rppo_S         : dom_rel ((detour ∪ rfe) ⨾ (data ∪ rfi ∪ rmw)＊ ⨾ (rppo ∪ rmw) ⨾ ⦗ reserved T ⦘) ⊆₁ eissued T;
  etc_S_W_ex_rfrmw_I : reserved T ∩₁ W_ex ⊆₁ codom_rel (⦗eissued T⦘ ⨾ rf ⨾ rmw);
 }.

Section Props.

Variable WF : Wf G.
Variable T : ext_trav_config.
Variable ETCCOH : etc_coherent T.

Lemma eissuedW : eissued T ⊆₁ W.
Proof using ETCCOH. unfold eissued. eapply issuedW. apply ETCCOH. Qed.

Lemma reservedW : reserved T ⊆₁ W.
Proof using WF ETCCOH.
  arewrite (reserved T ⊆₁ reserved T \₁ eissued T ∪₁ reserved T ∩₁ eissued T).
  2: { rewrite eissuedW at 2; auto. rewrite etc_S_I_in_W_ex; auto.
       rewrite W_ex_in_W; auto. basic_solver. }
  unfolder. ins.
  destruct (classic (eissued T x)); eauto.
Qed.

End Props.
End ExtTraversalConfig.
