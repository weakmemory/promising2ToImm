Require Import ClassicalDescription Omega.

From hahn Require Import Hahn.
From imm Require Import Events Execution Prog ProgToExecution
     ProgToExecutionProperties.

Set Implicit Arguments.

(******************************************************************************)
(** **  *)
(******************************************************************************)

Lemma ectrl_increasing (tid : thread_id) s s' (STEP : step tid s s'):
  s.(ectrl) ⊆₁ s'.(ectrl).
Proof.
destruct STEP; desc.
red in H; desc.
destruct ISTEP0; rewrite UECTRL; try done. 
basic_solver.
Qed.

Lemma ectrl_increasing_steps (tid : thread_id) s s' (STEP : (step tid)＊ s s'):
  s.(ectrl) ⊆₁ s'.(ectrl).
Proof.
induction STEP.
eby eapply ectrl_increasing.
done.
unfolder in *; basic_solver.
Qed.

Lemma ctrl_increasing (tid : thread_id) s s' (STEP : step tid s s'):
  s.(G).(ctrl) ⊆ s'.(G).(ctrl).
Proof.
destruct STEP; desc.
red in H; desc.
destruct ISTEP0.
all: rewrite UG; try done.
all: unfold add, add_rmw; ins; basic_solver.
Qed.

Lemma rmw_increasing (tid : thread_id) s s' (STEP : step tid s s'):
  s.(G).(rmw) ⊆ s'.(G).(rmw).
Proof.
destruct STEP; desc.
red in H; desc.
destruct ISTEP0.
all: rewrite UG; try done.
all: unfold add, add_rmw; ins; basic_solver.
Qed.

Lemma rmw_dep_increasing (tid : thread_id) s s' (STEP : step tid s s'):
  s.(G).(rmw_dep) ⊆ s'.(G).(rmw_dep).
Proof.
destruct STEP; desc.
red in H; desc.
destruct ISTEP0.
all: rewrite UG; try done.
all: unfold add, add_rmw; ins; basic_solver.
Qed.

Lemma addr_increasing (tid : thread_id) s s' (STEP : step tid s s'):
  s.(G).(addr) ⊆ s'.(G).(addr).
Proof.
destruct STEP; desc.
red in H; desc.
destruct ISTEP0.
all: rewrite UG; try done.
all: unfold add, add_rmw; ins; basic_solver.
Qed.

Lemma data_increasing (tid : thread_id) s s' (STEP : step tid s s'):
  s.(G).(data) ⊆ s'.(G).(data).
Proof.
destruct STEP; desc.
red in H; desc.
destruct ISTEP0.
all: rewrite UG; try done.
all: unfold add, add_rmw; ins; basic_solver.
Qed.

Lemma ectrl_ctrl_step (tid : thread_id) 
         s s' (STEP : step tid s s')
         MOD (ECTRL: exists a, (MOD ∩₁ ectrl s') a)
        (NCTRL: MOD ∩₁ dom_rel (s'.(G).(ctrl)) ⊆₁ ∅) :
         s.(G) = s'.(G).
Proof.
destruct STEP; desc.
red in H; desc.
destruct ISTEP0; try done.
all: exfalso; eapply NCTRL.
all: revert ECTRL;  unfolder; splits; try edone.
all: desc; eauto; exists (ThreadEvent tid (eindex s)).
all: rewrite UG; unfold add; ins; rewrite <- UECTRL; basic_solver.
Qed.


Lemma TWF_helper tid s1 (TWF : thread_wf tid s1): 
~ acts_set s1.(G) (ThreadEvent tid (s1.(eindex))).
Proof.
red in TWF.
intro.
specialize (TWF (ThreadEvent tid (eindex s1)) H); desf.
omega.
Qed.

Lemma TWF_helper_rmw tid s1 (TWF : thread_wf tid s1): 
~ acts_set s1.(G) (ThreadEvent tid (s1.(eindex) + 1)).
Proof.
red in TWF.
intro.
specialize (TWF (ThreadEvent tid (eindex s1 +1)) H); desf.
omega.
Qed.


Lemma acts_increasing (tid : thread_id) s s' (STEP : step tid s s') :
  s.(G).(acts_set) ⊆₁ s'.(G).(acts_set).
Proof.
destruct STEP; desc.
red in H; desc.
destruct ISTEP0.
all: rewrite UG; try done.
all: unfold add, add_rmw, acts_set; ins.
all: unfolder; ins; desc; eauto.
Qed.

Lemma is_r_ex_increasing (tid : thread_id) s s' (STEP : step tid s s') (TWF : thread_wf tid s):
  s.(G).(acts_set) ∩₁ R_ex s.(G).(lab) ⊆₁ R_ex s'.(G).(lab).
Proof.
destruct STEP; desc.
red in H; desc.
destruct ISTEP0.
all: rewrite UG; try done.
all: unfold add, add_rmw, R_ex; ins.
all: unfolder; ins; desc; eauto.
all: rewrite !updo; try done.
all: try by (intro; subst; eapply TWF_helper; edone).
all: try by (intro; subst; eapply TWF_helper_rmw; edone).
Qed.

Lemma is_r_increasing (tid : thread_id) s s' (STEP : step tid s s') (TWF : thread_wf tid s):
  s.(G).(acts_set) ∩₁ is_r s.(G).(lab) ⊆₁ is_r s'.(G).(lab).
Proof.
destruct STEP; desc.
red in H; desc.
destruct ISTEP0.
all: rewrite UG; try done.
all: unfold add, add_rmw, is_r; ins.
all: unfolder; ins; desc; eauto.
all: rewrite !updo; try done.
all: try by (intro; subst; eapply TWF_helper; edone).
all: try by (intro; subst; eapply TWF_helper_rmw; edone).
Qed.


Lemma is_w_increasing (tid : thread_id) s s' (STEP : step tid s s') (TWF : thread_wf tid s):
  s.(G).(acts_set) ∩₁ is_w s.(G).(lab) ⊆₁ is_w s'.(G).(lab).
Proof.
destruct STEP; desc.
red in H; desc.
destruct ISTEP0.
all: rewrite UG; try done.
all: unfold add, add_rmw, is_w; ins.
all: unfolder; ins; desc; eauto.
all: rewrite !updo; try done.
all: try by (intro; subst; eapply TWF_helper; edone).
all: try by (intro; subst; eapply TWF_helper_rmw; edone).
Qed.

(******************************************************************************)
(** **  *)
(******************************************************************************)

Lemma regf_expr_helper regf regf' depf MOD expr
  (REGF : forall reg, RegFun.find reg regf = RegFun.find reg regf' \/ 
           (exists a, RegFun.find reg depf a /\ MOD a))
  (NDEP: forall a (IN: MOD a), ~ DepsFile.expr_deps depf expr a):
  RegFile.eval_expr regf expr = RegFile.eval_expr regf' expr.
Proof.
unfold DepsFile.expr_deps, DepsFile.val_deps in NDEP.
unfold RegFile.eval_expr, RegFile.eval_value.
destruct expr.
- destruct val; [by vauto| specialize (REGF reg); desf].
  exfalso; eapply NDEP; edone.
- destruct op0; [by vauto| specialize (REGF reg); desf].
  rewrite REGF; auto.
  exfalso; eapply NDEP; edone.
- destruct op1, op2.
* by vauto.
* specialize (REGF reg); desf; [rewrite REGF|]; eauto.
  exfalso; eapply NDEP; [edone| basic_solver].
* specialize (REGF reg); desf; [rewrite REGF|]; eauto. 
  exfalso; eapply NDEP; [edone| basic_solver].
* generalize (REGF reg0); intro REGF0. 
  specialize (REGF reg).
  desf.
  by rewrite REGF, REGF0; auto.
  all: exfalso; eapply NDEP; [edone| basic_solver].
Qed.

Lemma regf_lexpr_helper regf regf' depf MOD expr
  (REGF : forall reg, RegFun.find reg regf = RegFun.find reg regf' \/ 
            (exists a, RegFun.find reg depf a /\ MOD a))
  (NDEP: forall a (IN: MOD a), ~ DepsFile.lexpr_deps depf expr a):
  RegFile.eval_lexpr regf expr = RegFile.eval_lexpr regf' expr.
Proof.
unfold DepsFile.lexpr_deps in NDEP.
unfold RegFile.eval_lexpr.
desf; exfalso; apply n; erewrite regf_expr_helper; eauto.
ins; specialize (REGF reg); desf; eauto.
Qed.

(******************************************************************************)
(** **  *)
(******************************************************************************)

Definition sim_execution G G' MOD :=
      ⟪ ACTS : G.(acts) = G'.(acts) ⟫ /\
      ⟪ SAME : same_lab_u2v G'.(lab) G.(lab) ⟫ /\
      ⟪ OLD_VAL : forall a (NIN: ~ MOD a), val (G'.(lab)) a = val (G.(lab)) a ⟫ /\
      ⟪ RMW  : G.(rmw)  ≡ G'.(rmw)  ⟫ /\
      ⟪ DATA : G.(data) ≡ G'.(data) ⟫ /\
      ⟪ ADDR : G.(addr) ≡ G'.(addr) ⟫ /\
      ⟪ CTRL : G.(ctrl) ≡ G'.(ctrl) ⟫ /\
      ⟪ FRMW : G.(rmw_dep) ≡ G'.(rmw_dep) ⟫ /\
      ⟪ RRF : G.(rf) ≡ G'.(rf) ⟫ /\
      ⟪ RCO : G.(co) ≡ G'.(co) ⟫.

Definition sim_state s s' MOD (new_rfi : relation actid) new_val := 
      ⟪ INSTRS  : s.(instrs) = s'.(instrs) ⟫ /\
      ⟪ PC  : s.(pc) = s'.(pc) ⟫ /\
      ⟪ EXEC : sim_execution s.(G) s'.(G) MOD ⟫ /\
      ⟪ EINDEX  : s.(eindex) = s'.(eindex) ⟫ /\
      ⟪ REGF  : forall reg, RegFun.find reg s.(regf) = RegFun.find reg s'.(regf) \/ 
exists a, (RegFun.find reg s.(depf)) a /\ MOD a ⟫ /\
      ⟪ DEPF  : s.(depf) = s'.(depf) ⟫ /\
      ⟪ ECTRL  : s.(ectrl) = s'.(ectrl) ⟫ /\
      ⟪ NEW_VAL1 : forall r w (RF: new_rfi w r) (INr: s'.(G).(acts_set) r) 
(INw: s'.(G).(acts_set) w) (READ: is_r s'.(G).(lab) r) (WRITE: is_w s'.(G).(lab) w) (IN_MOD: MOD r), 
                     val (s'.(G).(lab)) r = val (s'.(G).(lab)) w ⟫ /\
      ⟪ NEW_VAL2 : forall r (READ: is_r s'.(G).(lab) r) (IN_MOD: MOD r) 
                     (IN: s'.(G).(acts_set) r) (NIN_NEW_RF: ~ (codom_rel new_rfi) r), 
                     val (s'.(G).(lab)) r = Some (new_val r) ⟫.

Lemma sim_execution_same_r G G' MOD (EXEC: sim_execution G G' MOD) :
is_r G'.(lab) ≡₁ is_r G.(lab).
Proof.
red in EXEC; desf.
eby erewrite same_lab_u2v_is_r.
Qed.

Lemma sim_execution_same_w G G' MOD (EXEC: sim_execution G G' MOD) :
is_w G'.(lab) ≡₁ is_w G.(lab).
Proof.
red in EXEC; desf.
eby erewrite same_lab_u2v_is_w.
Qed.

Lemma sim_execution_same_acts G G' MOD (EXEC: sim_execution G G' MOD) :
acts_set G ≡₁ acts_set G'.
Proof.
red in EXEC; desf.
unfold acts_set; rewrite ACTS; basic_solver.
Qed.

(******************************************************************************)
(** **  *)
(******************************************************************************)

Lemma receptiveness_sim_assign (tid : thread_id)
  s1 s2 (INSTRS0 : instrs s1 = instrs s2)
  (reg : Reg.t) (expr : Instr.expr)
  (ISTEP : Some (Instr.assign reg expr) = nth_error (instrs s1) (pc s1))
  (UPC : pc s2 = pc s1 + 1) (UG : G s2 = G s1)
  (UINDEX : eindex s2 = eindex s1)
  (UREGS : regf s2 = RegFun.add reg (RegFile.eval_expr (regf s1) expr) (regf s1))
  (UDEPS : depf s2 = RegFun.add reg (DepsFile.expr_deps (depf s1) expr) (depf s1))
  (UECTRL : ectrl s2 = ectrl s1)
  MOD (new_rfi : relation actid) new_val
  s1' (SIM: sim_state s1 s1' MOD new_rfi new_val) :
 exists s2', (step tid) s1' s2' /\ sim_state s2 s2' MOD new_rfi new_val.
Proof.
red in SIM; desc.
cut (exists instrs pc G_ eindex regf depf ectrl, 
  step tid s1' {| instrs := instrs; pc := pc; G := G_; eindex := eindex; regf := regf; depf := depf; ectrl := ectrl |} /\ 
  (sim_state s2 {| instrs := instrs; pc := pc; G := G_; eindex := eindex; regf := regf; depf := depf; ectrl := ectrl |}
  MOD new_rfi new_val)).
by ins; desc; eauto.
do 7 eexists; splits; red; splits.
  * eexists; red; splits; [by ins; eauto|].
    eby eexists; splits; [ rewrite <- INSTRS, <- PC| eapply assign; reflexivity].
  * ins; congruence.
  * ins; congruence.
  * ins; congruence.
  * ins; congruence.
  * ins; rewrite UREGS, UDEPS.
    unfold RegFun.add, RegFun.find in *; desf.
    destruct (classic ((exists a : actid, DepsFile.expr_deps (depf s1) expr a /\ MOD a))) as [A|A].
    by auto.
    by left; apply (regf_expr_helper (regf s1) (regf s1') (depf s1) MOD expr REGF); eauto.
  * ins; congruence.
  * ins; congruence.
  * by ins; apply NEW_VAL1; try done; rewrite <- UG.
  * by ins; apply NEW_VAL2; try done; rewrite <- UG.
Qed.

Lemma receptiveness_sim_if_else (tid : thread_id)
  s1 s2 (INSTRS0 : instrs s1 = instrs s2)
  (expr : Instr.expr) (shift : nat)
  (e : RegFile.eval_expr (regf s1) expr = 0)
  (ISTEP : Some (Instr.ifgoto expr shift) = nth_error (instrs s1) (pc s1))
  (UPC : pc s2 = pc s1 + 1) (UG : G s2 = G s1)
  (UINDEX : eindex s2 = eindex s1)
  (UREGS : regf s2 = regf s1)
  (UDEPS : depf s2 = depf s1)
  (UECTRL : ectrl s2 = DepsFile.expr_deps (depf s1) expr ∪₁ ectrl s1)
  MOD (new_rfi : relation actid) new_val
  (NCTRL : MOD ∩₁ ectrl s2 ⊆₁ ∅)
  s1' (SIM: sim_state s1 s1' MOD new_rfi new_val) :
 exists s2', (step tid) s1' s2' /\ sim_state s2 s2' MOD new_rfi new_val.
Proof.
red in SIM; desc.
cut (exists instrs pc G_ eindex regf depf ectrl, 
  step tid s1' {| instrs := instrs; pc := pc; G := G_; eindex := eindex; regf := regf; depf := depf; ectrl := ectrl |} /\ 
  (sim_state s2 {| instrs := instrs; pc := pc; G := G_; eindex := eindex; regf := regf; depf := depf; ectrl := ectrl |}
  MOD new_rfi new_val)).
by ins; desc; eauto.
eexists.
  exists (if Const.eq_dec (RegFile.eval_expr (regf s1') expr) 0
        then pc s1' + 1 else shift).
  do 5 eexists; splits; red; splits.
  * eexists; red; splits; [by ins; eauto|].
    eexists; splits; [eby rewrite <- INSTRS, <- PC|].
    eapply if_; try reflexivity; ins; desf.
  * ins; congruence.
  * ins.
    erewrite <- regf_expr_helper with (regf:= regf s1).
    desf; congruence.
    eauto.
    ins; intro; eapply NCTRL; rewrite UECTRL; basic_solver.
  * ins; congruence.
  * ins; congruence.
  * ins; rewrite UREGS, UDEPS; eauto.
  * ins; congruence.
  * ins; congruence.
  * by ins; apply NEW_VAL1; try done; rewrite <- UG.
  * by ins; apply NEW_VAL2; try done; rewrite <- UG.
Qed.

Lemma receptiveness_sim_if_then (tid : thread_id)
  s1 s2 (INSTRS0 : instrs s1 = instrs s2)
  (expr : Instr.expr) (shift : nat)
  (n : RegFile.eval_expr (regf s1) expr <> 0)
  (ISTEP : Some (Instr.ifgoto expr shift) = nth_error (instrs s1) (pc s1))
  (UPC : pc s2 = shift) (UG : G s2 = G s1)
  (UINDEX : eindex s2 = eindex s1)
  (UREGS : regf s2 = regf s1)
  (UDEPS : depf s2 = depf s1)
  (UECTRL : ectrl s2 = DepsFile.expr_deps (depf s1) expr ∪₁ ectrl s1)
  MOD (new_rfi : relation actid) new_val
  (NCTRL : MOD ∩₁ ectrl s2 ⊆₁ ∅)
  s1' (SIM: sim_state s1 s1' MOD new_rfi new_val) :
 exists s2', (step tid) s1' s2' /\ sim_state s2 s2' MOD new_rfi new_val.
Proof.
red in SIM; desc.
cut (exists instrs pc G_ eindex regf depf ectrl, 
  step tid s1' {| instrs := instrs; pc := pc; G := G_; eindex := eindex; regf := regf; depf := depf; ectrl := ectrl |} /\ 
  (sim_state s2 {| instrs := instrs; pc := pc; G := G_; eindex := eindex; regf := regf; depf := depf; ectrl := ectrl |}
  MOD new_rfi new_val)).
by ins; desc; eauto.
 eexists.
  exists (if Const.eq_dec (RegFile.eval_expr (regf s1') expr) 0
        then pc s1' + 1 else shift).
  do 5 eexists; splits; red; splits.
  * eexists; red; splits; [by ins; eauto|].
    eexists; splits; [eby rewrite <- INSTRS, <- PC|].
    eapply if_; try reflexivity; ins; desf.
  * ins; congruence.
  * ins.
    erewrite <- regf_expr_helper with (regf:= regf s1).
    desf; congruence.
    eauto.
    ins; intro; eapply NCTRL; rewrite UECTRL; basic_solver.
  * ins; congruence.
  * ins; congruence.
  * ins; rewrite UREGS, UDEPS; eauto.
  * ins; congruence.
  * ins; congruence.
  * by ins; apply NEW_VAL1; try done; rewrite <- UG.
  * by ins; apply NEW_VAL2; try done; rewrite <- UG.
Qed.

Definition new_rfi_ex (new_rfi :relation actid) :=
new_rfi ∪ ⦗ set_compl (codom_rel new_rfi) ⦘.

Lemma new_rfi_unique (new_rfi : relation actid)
      (new_rfif : functional new_rfi⁻¹):
forall r, exists ! w, (new_rfi_ex new_rfi)⁻¹  r w.
Proof.
ins.
destruct (classic ((codom_rel new_rfi) r)) as [X|X].
- unfolder in X; desf.
exists x; red; splits.
unfold new_rfi_ex; basic_solver 12.
unfold new_rfi_ex; unfolder; ins; desf.
eapply new_rfif; basic_solver.
exfalso; eauto.
- exists r; red; splits.
unfold new_rfi_ex; basic_solver 12.
unfold new_rfi_ex; unfolder; ins; desf.
unfolder in X; exfalso; eauto.
Qed.

Definition new_write new_rfi new_rfif := 
  unique_choice (new_rfi_ex new_rfi)⁻¹ (@new_rfi_unique new_rfi new_rfif).

Definition get_val (v: option value) := 
  match v with | Some v => v | _ => 0 end.

Lemma RFI_index_helper tid s new_rfi (TWF : thread_wf tid s)
   (RFI_INDEX : new_rfi ⊆ ext_sb)
   w r (RFI: new_rfi w r) 
  (IN: ThreadEvent tid s.(eindex) = r \/ In r s.(G).(acts)) :
   w <> ThreadEvent tid (s.(eindex)).
Proof.
intro; subst; desf.
apply RFI_INDEX in RFI.
eby eapply ext_sb_irr.
specialize (TWF r IN); desf.
apply RFI_INDEX in RFI.
unfold sb, ext_sb in RFI; unfolder in RFI; desf; omega.
Qed.

Lemma receptiveness_sim_load (tid : thread_id)
  s1 s2 (INSTRS0 : instrs s1 = instrs s2)
  (ord : mode) (reg : Reg.t)
  (lexpr : Instr.lexpr) (ISTEP : Some (Instr.load ord reg lexpr) = nth_error (instrs s1) (pc s1))
  (val_ : value) (UPC : pc s2 = pc s1 + 1)
  (UG : G s2 =
     add (G s1) tid (eindex s1)
       (Aload false ord (RegFile.eval_lexpr (regf s1) lexpr) val_) 
       ∅ (DepsFile.lexpr_deps (depf s1) lexpr) (ectrl s1) 
       ∅)
  (UINDEX : eindex s2 = eindex s1 + 1)
  (UREGS : regf s2 = RegFun.add reg val_ (regf s1))
  (UDEPS : depf s2 = RegFun.add reg (eq (ThreadEvent tid (eindex s1))) (depf s1))
  (UECTRL : ectrl s2 = ectrl s1)
  MOD (new_rfi : relation actid) new_val
  (NADDR : MOD ∩₁ dom_rel (s2.(G).(addr)) ⊆₁ ∅)
  (RFI_INDEX : new_rfi ⊆ ext_sb)
  (TWF : thread_wf tid s1)
  (new_rfif : functional new_rfi⁻¹)
  s1' (SIM: sim_state s1 s1' MOD new_rfi new_val) :
 exists s2', (step tid) s1' s2' /\ sim_state s2 s2' MOD new_rfi new_val.
Proof.
generalize (@new_write new_rfi new_rfif); intro F; destruct F as [new_w F].
red in SIM; desc.

assert (SAME_LOC: RegFile.eval_lexpr (regf s1) lexpr = RegFile.eval_lexpr (regf s1') lexpr).
{ ins; eapply regf_lexpr_helper; eauto.
ins; intro; eapply NADDR; unfolder; splits; eauto.
exists (ThreadEvent tid (eindex s1)).
rewrite UG; unfold add; basic_solver. } 

cut (exists instrs pc G_ eindex regf depf ectrl, 
  step tid s1' {| instrs := instrs; pc := pc; G := G_; eindex := eindex; regf := regf; depf := depf; ectrl := ectrl |} /\ 
  (sim_state s2 {| instrs := instrs; pc := pc; G := G_; eindex := eindex; regf := regf; depf := depf; ectrl := ectrl |}
  MOD new_rfi new_val)).
by ins; desc; eauto.

do 7 eexists; splits; red; splits.
  * eexists; red; splits; [by ins; eauto|].
    eexists; splits; [eby rewrite <- INSTRS, <- PC |].
    eapply load with (val := 
      if excluded_middle_informative (MOD (ThreadEvent tid (eindex s1'))) 
      then if excluded_middle_informative ((codom_rel new_rfi) (ThreadEvent tid (eindex s1'))) 
           then (get_val (val s1'.(G).(lab) (new_w (ThreadEvent tid (eindex s1')))))
           else (new_val (ThreadEvent tid (eindex s1')))
      else val_);
    reflexivity.
  * ins; congruence.
  * ins; congruence.
  * ins.
    destruct (G s2) as [acts2 lab2 rmw2 data2 addr2 ctrl2 rf2 co2].
    inversion UG; subst; clear UG.
    red in EXEC; desc.
    red; splits; ins.
    + by rewrite EINDEX, ACTS.
    + rewrite EINDEX.
      unfold same_lab_u2v in *; intro e.
      destruct (eq_dec_actid e (ThreadEvent tid (eindex s1'))).
      { by subst; rewrite !upds. }
      ins. rewrite !updo; auto.
    + rewrite EINDEX.
      destruct (eq_dec_actid a (ThreadEvent tid (eindex s1'))).
      by desf; unfold val; rewrite !upds.
      unfold val; rewrite !updo; [|intro; desf|intro; desf].
      by apply OLD_VAL in NIN; unfold val in NIN; rewrite NIN.
    + by rewrite DATA, EINDEX.
    + by rewrite ADDR, EINDEX, DEPF.
    + by rewrite CTRL, EINDEX, ECTRL.
    + by rewrite FRMW, EINDEX.
  * ins; congruence.
  * ins; rewrite UREGS, UDEPS.
    unfold RegFun.add, RegFun.find in *; desf; eauto.
  * eby ins; rewrite <- DEPF, <- EINDEX.
  * ins; congruence.
  * simpl; ins.
     unfold add, acts_set in INw; ins.
    destruct (eq_dec_actid w (ThreadEvent tid (eindex s1'))); subst.
    + exfalso; eapply RFI_index_helper.
      edone.
      eapply RFI_INDEX.
      edone.
      unfold add, acts_set in INr; ins.
      rewrite EINDEX; destruct INr; [eauto|].
      right; eapply sim_execution_same_acts; eauto.
      by rewrite EINDEX.
    + destruct INw as [X|INw]; [desf|].
      destruct (eq_dec_actid r (ThreadEvent tid (eindex s1'))); subst.
      -- unfold val in *; rewrite !upds.
         rewrite !updo; try done.
         destruct (excluded_middle_informative (MOD (ThreadEvent tid (eindex s1')))); [|desf].
         destruct (excluded_middle_informative (codom_rel new_rfi (ThreadEvent tid (eindex s1')))).
         2: by exfalso; apply n0; basic_solver 12.
         assert (w = new_w (ThreadEvent tid (eindex s1'))).
         { assert (U: exists ! w1 : actid, (new_rfi_ex new_rfi)⁻¹ (ThreadEvent tid (eindex s1')) w1).
           apply new_rfi_unique, new_rfif.
           eapply unique_existence with 
           (P:= fun x => (@new_rfi_ex new_rfi)⁻¹ (ThreadEvent tid (eindex s1')) x) in U; desc.
           eapply U0.
           unfold new_rfi_ex.
           basic_solver.
           apply F. }
         unfold is_w in WRITE; rewrite updo in WRITE; desf.
      -- unfold val in *; rewrite !updo; try done.
         eapply NEW_VAL1; try edone.
         unfold add, acts_set in INr; ins; desf.
         by unfold is_r in *; rewrite updo in READ.
         by unfold is_w in *; rewrite updo in WRITE.
  * simpl; ins.
    destruct (eq_dec_actid r (ThreadEvent tid (eindex s1'))); subst.
    + destruct (excluded_middle_informative (MOD (ThreadEvent tid (eindex s1')))); [subst|desf].
      destruct (excluded_middle_informative (codom_rel new_rfi (ThreadEvent tid (eindex s1')))); [desf|].
      by unfold val in *; rewrite !upds.
    + unfold val in *; rewrite !updo; try done.
      apply NEW_VAL2; try done.
      by unfold is_r in *; rewrite updo in READ.
      by unfold add, acts_set in IN; ins; desf.
Qed.

Lemma receptiveness_sim_store (tid : thread_id)
  s1 s2 (INSTRS0 : instrs s1 = instrs s2)
  (ord : mode) (reg : Reg.t)
  (lexpr : Instr.lexpr) (expr : Instr.expr)
  (ISTEP : Some (Instr.store ord lexpr expr) = nth_error (instrs s1) (pc s1))
  (UPC : pc s2 = pc s1 + 1)
  (UG : G s2 = add (G s1) tid (eindex s1)
         (Astore Xpln ord (RegFile.eval_lexpr (regf s1) lexpr) (RegFile.eval_expr (regf s1) expr)) 
         (DepsFile.expr_deps (depf s1) expr) (DepsFile.lexpr_deps (depf s1) lexpr) (ectrl s1) ∅) 
  (UINDEX : eindex s2 = eindex s1 + 1)
  (UREGS : regf s2 = regf s1)
  (UDEPS : depf s2 = depf s1)
  (UECTRL : ectrl s2 = ectrl s1)
  MOD (new_rfi : relation actid) new_val
  (NADDR : MOD ∩₁ dom_rel (s2.(G).(addr)) ⊆₁ ∅)
  (NDATA: ⦗MOD⦘ ⨾ s2.(G).(data) ⨾ ⦗set_compl MOD⦘ ⊆ ∅₂)
   (RFI_INDEX : new_rfi ⊆ ext_sb)
  (TWF : thread_wf tid s1)
  s1' (SIM: sim_state s1 s1' MOD new_rfi new_val) :
 exists s2', (step tid) s1' s2' /\ sim_state s2 s2' MOD new_rfi new_val.
Proof.
red in SIM; desc.

assert (SAME_LOC: RegFile.eval_lexpr (regf s1) lexpr = RegFile.eval_lexpr (regf s1') lexpr).
{ ins; eapply regf_lexpr_helper; eauto.
ins; intro; eapply NADDR; unfolder; splits; eauto.
exists (ThreadEvent tid (eindex s1)).
rewrite UG; unfold add; basic_solver. } 

cut (exists instrs pc G_ eindex regf depf ectrl, 
  step tid s1' {| instrs := instrs; pc := pc; G := G_; eindex := eindex; regf := regf; depf := depf; ectrl := ectrl |} /\ 
  (sim_state s2 {| instrs := instrs; pc := pc; G := G_; eindex := eindex; regf := regf; depf := depf; ectrl := ectrl |}
  MOD new_rfi new_val)).
by ins; desc; eauto.

 do 7 eexists; splits; red; splits.
  * eexists; red; splits; [by ins; eauto|].
    eexists; splits; [eby rewrite <- INSTRS, <- PC |].
    eapply store; reflexivity.
  * ins; congruence.
  * ins; congruence.
  * ins.
    destruct (G s2) as [acts2 lab2 rmw2 data2 addr2 ctrl2 rf2 co2].
    inversion UG; subst; clear UG.
    red in EXEC; desc.
    red; splits; ins.
    + by rewrite EINDEX, ACTS.
    + rewrite EINDEX.
      unfold same_lab_u2v in *; intro e.
      destruct (eq_dec_actid e (ThreadEvent tid (eindex s1'))).
      { by subst; rewrite !upds. }
      rewrite !updo; auto.
    + rewrite EINDEX.
      destruct (eq_dec_actid a (ThreadEvent tid (eindex s1'))); subst.
      -- desf; unfold val; rewrite !upds.
         erewrite regf_expr_helper; try edone.
         intro reg0; specialize (REGF reg0); desf; eauto.
         ins; intro DEPS; eapply NDATA; unfolder; splits; eauto.
         by rewrite EINDEX.
      -- unfold val;  rewrite !updo; try done.
         by apply OLD_VAL in NIN; unfold val in NIN; rewrite NIN.
    + by rewrite DATA, EINDEX, DEPF.
    + by rewrite ADDR, EINDEX, DEPF.
    + by rewrite CTRL, EINDEX, ECTRL.
    + by rewrite FRMW, EINDEX.
  * ins; congruence.
  * ins; rewrite UREGS, UDEPS.
    unfold RegFun.add, RegFun.find in *; desf; eauto.
  * by ins; rewrite <- DEPF, <- UDEPS.
  * ins; congruence.
  * simpl; ins.
    unfold add, acts_set in INw; ins.
    destruct (eq_dec_actid w (ThreadEvent tid (eindex s1'))); subst.
    + exfalso; eapply RFI_index_helper.
      edone.
      eapply RFI_INDEX.
      edone.
      unfold add, acts_set in INr; ins.
      rewrite EINDEX; destruct INr; [eauto|].
      right; eapply sim_execution_same_acts; eauto.
      by rewrite EINDEX.
    + destruct INw as [X|INw]; [desf|].
      destruct (eq_dec_actid r (ThreadEvent tid (eindex s1'))); subst.
      by unfold is_r in *; rewrite !upds in READ; desf.
      unfold val in *; rewrite !updo; try done.
      eapply NEW_VAL1; try edone.
      by  unfold add, acts_set in INr; ins; desf.
      by unfold is_r in *; rewrite updo in READ.
      by unfold is_w in *; rewrite updo in WRITE.
  * simpl; ins.
    destruct (eq_dec_actid r (ThreadEvent tid (eindex s1'))); subst.
    by unfold is_r in *; rewrite upds in READ; desf.
    unfold val; rewrite updo; try done.
    apply NEW_VAL2; try done.
    unfold is_r in *; rewrite updo in READ; try done.
    by unfold add, acts_set in IN; ins; desf.
Qed.

Lemma receptiveness_sim_fence (tid : thread_id)
  s1 s2 (INSTRS0 : instrs s1 = instrs s2)
  (ord : mode) 
  (ISTEP : Some (Instr.fence ord) = nth_error (instrs s1) (pc s1))
  (UPC : pc s2 = pc s1 + 1)
  (UG : G s2 = add (G s1) tid (eindex s1) (Afence ord) ∅ ∅ (ectrl s1) ∅)
  (UINDEX : eindex s2 = eindex s1 + 1)
  (UREGS : regf s2 = regf s1)
  (UDEPS : depf s2 = depf s1)
  (UECTRL : ectrl s2 = ectrl s1)
  MOD (new_rfi : relation actid) new_val
  s1' (SIM: sim_state s1 s1' MOD new_rfi new_val) :
 exists s2', (step tid) s1' s2' /\ sim_state s2 s2' MOD new_rfi new_val.
Proof.
red in SIM; desc.

cut (exists instrs pc G_ eindex regf depf ectrl, 
  step tid s1' {| instrs := instrs; pc := pc; G := G_; eindex := eindex; regf := regf; depf := depf; ectrl := ectrl |} /\ 
  (sim_state s2 {| instrs := instrs; pc := pc; G := G_; eindex := eindex; regf := regf; depf := depf; ectrl := ectrl |}
  MOD new_rfi new_val)).
by ins; desc; eauto.

do 7 eexists; splits; red; splits.
  * eexists; red; splits; [by ins; eauto|].
    eexists; splits; [eby rewrite <- INSTRS, <- PC |].
    eapply fence; reflexivity.
  * ins; congruence.
  * ins; congruence.
  * ins.
    destruct (G s2) as [acts2 lab2 rmw2 data2 addr2 ctrl2 rf2 co2].
    inversion UG; subst; clear UG.
    red in EXEC; desc.
    red; splits; ins.
    + by rewrite EINDEX, ACTS.
    + rewrite EINDEX.
      unfold same_lab_u2v in *; intro e.
      destruct (eq_dec_actid e (ThreadEvent tid (eindex s1'))).
      { by subst; rewrite !upds. }
      rewrite !updo; auto.
    + rewrite EINDEX.
      destruct (eq_dec_actid a (ThreadEvent tid (eindex s1'))).
      by desf; unfold val; rewrite !upds.
      unfold val; rewrite !updo; [|intro; desf|intro; desf].
      by apply OLD_VAL in NIN; unfold val in NIN; rewrite NIN.
    + by rewrite DATA, EINDEX.
    + by rewrite ADDR, EINDEX.
    + by rewrite CTRL, EINDEX, ECTRL.
    + by rewrite FRMW, EINDEX.
  * ins; congruence.
  * ins; rewrite UREGS, UDEPS.
    unfold RegFun.add, RegFun.find in *; desf; eauto.
  * by ins; rewrite <- DEPF, <- UDEPS.
  * ins; congruence.
  * ins.
    destruct (eq_dec_actid w (ThreadEvent tid (eindex s1'))); subst.
    by unfold is_w in WRITE; rewrite upds in WRITE; desf.
    destruct (eq_dec_actid r (ThreadEvent tid (eindex s1'))); subst.
    by unfold is_r in READ; rewrite upds in READ; desf.
    unfold val; rewrite !updo; try done.
    eapply NEW_VAL1; try edone.
    unfold add, acts_set in INr; ins; desf.
    rewrite <- EINDEX in n0; desf.
    unfold add, acts_set in INw; ins; desf.
    rewrite <- EINDEX in n; desf.
    red in EXEC; desf.
    unfold is_r in *; rewrite updo in READ; try edone.
    unfold is_w in *; rewrite updo in WRITE; try edone.
  * simpl; ins.
    destruct (eq_dec_actid r (ThreadEvent tid (eindex s1'))); subst.
    by unfold is_r in *; rewrite upds in READ; desf.
    unfold val; rewrite updo; try done.
    apply NEW_VAL2; try done.
    unfold is_r in *; rewrite updo in READ; try done.
    by unfold add, acts_set in IN; ins; desf.
Qed.



Lemma receptiveness_sim_cas_fail (tid : thread_id)
  s1 s2 (INSTRS0 : instrs s1 = instrs s2)
  (expr_old expr_new : Instr.expr)
  xmod
(ordr ordw : mode)
(reg : Reg.t)
(lexpr : Instr.lexpr)
(ISTEP : Some (Instr.update (Instr.cas expr_old expr_new) xmod ordr ordw reg lexpr) =
        nth_error (instrs s1) (pc s1))
(val_ : value)
(NEXPECTED : val_ <> RegFile.eval_expr (regf s1) expr_old)
(UPC : pc s2 = pc s1 + 1)
(UG : G s2 =
     add (G s1) tid (eindex s1) (Aload true ordr (RegFile.eval_lexpr (regf s1) lexpr) val_) 
       ∅ (DepsFile.lexpr_deps (depf s1) lexpr) (ectrl s1)
       (DepsFile.expr_deps (depf s1) expr_old))
(UINDEX : eindex s2 = eindex s1 + 1)
(UREGS : regf s2 = RegFun.add reg val_ (regf s1))
(UDEPS : depf s2 = RegFun.add reg (eq (ThreadEvent tid (eindex s1))) (depf s1))
(UECTRL : ectrl s2 = ectrl s1)
  MOD (new_rfi : relation actid) new_val
  (NFRMW: MOD ∩₁ dom_rel (s2.(G).(rmw_dep)) ⊆₁ ∅)
  (NADDR : MOD ∩₁ dom_rel (s2.(G).(addr)) ⊆₁ ∅)
  (NREX:  MOD ∩₁ s2.(G).(acts_set) ∩₁ (R_ex s2.(G).(lab)) ⊆₁ ∅) 
  s1' (SIM: sim_state s1 s1' MOD new_rfi new_val) :
 exists s2', (step tid) s1' s2' /\ sim_state s2 s2' MOD new_rfi new_val.
Proof.
red in SIM; desc.

assert (SAME_LOC: RegFile.eval_lexpr (regf s1) lexpr = RegFile.eval_lexpr (regf s1') lexpr).
{ ins; eapply regf_lexpr_helper; eauto.
ins; intro; eapply NADDR; unfolder; splits; eauto.
exists (ThreadEvent tid (eindex s1)).
rewrite UG; unfold add; basic_solver. } 

cut (exists instrs pc G_ eindex regf depf ectrl, 
  step tid s1' {| instrs := instrs; pc := pc; G := G_; eindex := eindex; regf := regf; depf := depf; ectrl := ectrl |} /\ 
  (sim_state s2 {| instrs := instrs; pc := pc; G := G_; eindex := eindex; regf := regf; depf := depf; ectrl := ectrl |}
  MOD new_rfi new_val)).
by ins; desc; eauto.

do 7 eexists; splits; red; splits.
  * eexists; red; splits; [by ins; eauto|].
    eexists; splits; [eby rewrite <- INSTRS, <- PC |].
    eapply cas_un with (val := val_); try reflexivity.
    erewrite <- regf_expr_helper with (regf := (regf s1)); try edone.
    ins; intro;  eapply NFRMW; rewrite UG; unfold add; ins; basic_solver.
  * ins; congruence.
  * ins; congruence.
  * ins.
    destruct (G s2) as [acts2 lab2 rmw2 data2 addr2 ctrl2 rf2 co2].
    inversion UG; subst; clear UG.
    red in EXEC; desc.
    red; splits; ins.
    + by rewrite EINDEX, ACTS.
    + rewrite EINDEX.
      unfold same_lab_u2v in *; intro e.
      destruct (eq_dec_actid e (ThreadEvent tid (eindex s1'))).
      { by subst; rewrite !upds; rewrite SAME_LOC. }
      rewrite !updo; auto.
    + rewrite EINDEX.
      destruct (eq_dec_actid a (ThreadEvent tid (eindex s1'))).
      rewrite SAME_LOC.
      by desf; unfold val; rewrite !upds.
      unfold val; rewrite !updo; [|intro; desf|intro; desf].
      by apply OLD_VAL in NIN; unfold val in NIN; rewrite NIN.
    + by rewrite DATA, EINDEX.
    + by rewrite ADDR, EINDEX, DEPF.
    + by rewrite CTRL, EINDEX, ECTRL.
    + by rewrite FRMW, EINDEX, DEPF.
  * ins; congruence.
  * ins; rewrite UREGS, UDEPS.
    unfold RegFun.add, RegFun.find in *; desf; eauto.
  * eby ins; rewrite <- DEPF, <- EINDEX.
  * ins; congruence.
  * ins.
    destruct (eq_dec_actid w (ThreadEvent tid (eindex s1'))); subst.
    by unfold is_w in WRITE; rewrite upds in WRITE; desf.
    destruct (eq_dec_actid r (ThreadEvent tid (eindex s1'))); subst.
    + exfalso.
      eapply NREX; split; [eauto|].
      rewrite UG; unfold add; unfold acts_set; ins.
      split; [eauto| rewrite EINDEX; eauto].
      rewrite UG; unfold add; unfold R_ex; ins.
      by rewrite EINDEX, upds.
    + unfold val; rewrite !updo; try done.
      eapply NEW_VAL1; try edone.
      unfold add, acts_set in INr; ins; desf.
      rewrite <- EINDEX in n0; desf.
      unfold add, acts_set in INw; ins; desf.
      rewrite <- EINDEX in n; desf.
      red in EXEC; desf.
      unfold is_r in *; rewrite updo in READ; try edone.
      unfold is_w in *; rewrite updo in WRITE; try edone.
  * simpl; ins.
    destruct (eq_dec_actid r (ThreadEvent tid (eindex s1'))); subst.
    + exfalso.
      eapply NREX; split; [eauto|].
      rewrite UG; unfold add; unfold acts_set; ins.
      split; [eauto| rewrite EINDEX; eauto].
      rewrite UG; unfold add; unfold R_ex; ins.
      by rewrite EINDEX, upds.
    + unfold val; rewrite updo; try done.
      apply NEW_VAL2; try done.
      unfold is_r in *; rewrite updo in READ; try done.
      by unfold add, acts_set in IN; ins; desf.
Qed.


Lemma receptiveness_sim_cas_suc (tid : thread_id)
  s1 s2 (INSTRS0 : instrs s1 = instrs s2)
  (expr_old expr_new : Instr.expr)
  xmod
(ordr ordw : mode)
(reg : Reg.t)
(lexpr : Instr.lexpr)
(ISTEP : Some (Instr.update (Instr.cas expr_old expr_new) xmod ordr ordw reg lexpr) =
        nth_error (instrs s1) (pc s1))
(UPC : pc s2 = pc s1 + 1)
(UG : G s2 =
     add_rmw (G s1) tid (eindex s1)
       (Aload true ordr (RegFile.eval_lexpr (regf s1) lexpr)
          (RegFile.eval_expr (regf s1) expr_old))
       (Astore xmod ordw (RegFile.eval_lexpr (regf s1) lexpr)
          (RegFile.eval_expr (regf s1) expr_new))
       (DepsFile.expr_deps (depf s1) expr_new)
       (DepsFile.lexpr_deps (depf s1) lexpr) (ectrl s1)
       (DepsFile.expr_deps (depf s1) expr_old))
(UINDEX : eindex s2 = eindex s1 + 2)
(UREGS : regf s2 = RegFun.add reg (RegFile.eval_expr (regf s1) expr_old) (regf s1))
(UDEPS : depf s2 = RegFun.add reg (eq (ThreadEvent tid (eindex s1))) (depf s1))
(UECTRL : ectrl s2 = ectrl s1)
  MOD (new_rfi : relation actid) new_val
  (NFRMW: MOD ∩₁ dom_rel (s2.(G).(rmw_dep)) ⊆₁ ∅)
  (NADDR : MOD ∩₁ dom_rel (s2.(G).(addr)) ⊆₁ ∅)
  (NREX:  MOD ∩₁ s2.(G).(acts_set) ∩₁ (R_ex s2.(G).(lab)) ⊆₁ ∅) 
  (NDATA: ⦗MOD⦘ ⨾ s2.(G).(data) ⨾ ⦗set_compl MOD⦘ ⊆ ∅₂)
  (RFI_INDEX : new_rfi ⊆ ext_sb)
  (TWF : thread_wf tid s1)
  s1' (SIM: sim_state s1 s1' MOD new_rfi new_val) :
 exists s2', (step tid) s1' s2' /\ sim_state s2 s2' MOD new_rfi new_val.
Proof.
red in SIM; desc.

assert (SAME_LOC: RegFile.eval_lexpr (regf s1) lexpr = RegFile.eval_lexpr (regf s1') lexpr).
{ ins; eapply regf_lexpr_helper; eauto.
ins; intro; eapply NADDR; unfolder; splits; eauto.
exists (ThreadEvent tid (eindex s1)).
rewrite UG; unfold add_rmw; basic_solver. } 

cut (exists instrs pc G_ eindex regf depf ectrl, 
  step tid s1' {| instrs := instrs; pc := pc; G := G_; eindex := eindex; regf := regf; depf := depf; ectrl := ectrl |} /\ 
  (sim_state s2 {| instrs := instrs; pc := pc; G := G_; eindex := eindex; regf := regf; depf := depf; ectrl := ectrl |}
  MOD new_rfi new_val)).
by ins; desc; eauto.

do 7 eexists; splits; red; splits.
  * eexists; red; splits; [by ins; eauto|].
    eexists; splits; [eby rewrite <- INSTRS, <- PC |].
    eapply cas_suc; try reflexivity.
  * ins; congruence.
  * ins; congruence.
  * ins.
    destruct (G s2) as [acts2 lab2 rmw2 data2 addr2 ctrl2 rf2 co2].
    inversion UG; subst; clear UG; ins.
    unfold acts_set, R_ex in NREX; ins.
    red in EXEC; desc.
    red; splits; ins.
    + by rewrite EINDEX, ACTS.
    + rewrite EINDEX.
      unfold same_lab_u2v in *; intro e.
      destruct (eq_dec_actid e (ThreadEvent tid (eindex s1' + 1))).
      by subst; rewrite !upds; rewrite SAME_LOC.
      rewrite updo; try done.
      destruct (eq_dec_actid e (ThreadEvent tid (eindex s1'))).
      by subst; rewrite !upds; rewrite updo; [| by desf]; rewrite upds; rewrite SAME_LOC.
      rewrite !updo; auto.
    + rewrite EINDEX.
      destruct (eq_dec_actid a (ThreadEvent tid (eindex s1' + 1))).
      -- subst; rewrite SAME_LOC.
         unfold val; rewrite !upds.
         erewrite regf_expr_helper; try edone.
         intro reg0; specialize (REGF reg0); desf; eauto.
         ins; intro DEPS; eapply NDATA; unfolder; splits; eauto.
         by rewrite EINDEX.
      -- unfold val; rewrite updo; [|done].
         destruct (eq_dec_actid a (ThreadEvent tid (eindex s1'))).
         ** subst; rewrite SAME_LOC.
            rewrite !upds.
            rewrite updo; [|intro; desf; omega].
            rewrite !upds.
            erewrite regf_expr_helper; try edone.
            intro reg0; specialize (REGF reg0); desf; eauto.
            ins; intro DEPS; eapply NFRMW; unfolder; splits; eauto.
         ** rewrite !updo; try done.
            by apply OLD_VAL in NIN; unfold val in NIN; rewrite NIN.
    + by rewrite RMW, EINDEX.
    + by rewrite DATA, EINDEX, DEPF.
    + by rewrite ADDR, EINDEX, DEPF.
    + by rewrite CTRL, EINDEX, ECTRL.
    + by rewrite FRMW, EINDEX, DEPF.
  * ins; congruence.
  * ins; rewrite UREGS, UDEPS.
    unfold RegFun.add, RegFun.find in *; desf; eauto.
    erewrite regf_expr_helper; eauto.
    ins; intro; eapply NFRMW.
    rewrite UG; ins; basic_solver.
  * eby ins; rewrite <- DEPF, <- EINDEX.
  * ins; congruence.
  * ins; unfold acts_set, is_r, is_w in INr, INw, READ, WRITE; ins.
    destruct (eq_dec_actid r (ThreadEvent tid (eindex s1'+1))); subst.
    by rewrite upds in READ; desf.
    destruct (eq_dec_actid w (ThreadEvent tid (eindex s1'))); subst.
    rewrite updo in WRITE; [| intro; desf; omega].
    by rewrite upds in WRITE; desf.
    destruct (eq_dec_actid r (ThreadEvent tid (eindex s1'))); subst.
    + exfalso.
      eapply NREX; split; [eauto|].
      rewrite UG; unfold add; unfold acts_set; ins.
      split; [eauto| rewrite EINDEX; eauto].
      rewrite UG; unfold add; unfold R_ex; ins.
       by rewrite updo; [| intro; desf; omega]; rewrite EINDEX, upds.
    + unfold val; rewrite updo; [|done].
      rewrite updo; [|done].
      destruct (eq_dec_actid w (ThreadEvent tid (eindex s1'+1))); subst.
      -- exfalso.
         apply RFI_INDEX in RF; unfold ext_sb in RF.
         destruct r; [eauto|]; desc.
         destruct INr as [X|[X|INr]]; try by desf.
         apply sim_execution_same_acts in EXEC.
         apply EXEC in INr.
         apply TWF in INr; desc.
         rewrite <- EINDEX in RF0.
         desf; omega.
      -- rewrite !updo; try done.
         eapply NEW_VAL1; try edone.
         by rewrite <- EINDEX in n0; desf.
         by rewrite <- EINDEX in n; desf.
         by rewrite !updo in READ; try edone.
         by rewrite !updo in WRITE; try edone.
  * simpl; ins.
    destruct (eq_dec_actid r (ThreadEvent tid (eindex s1'+1))); subst.
    by unfold is_r in READ; rewrite upds in READ; desf.
    unfold val; rewrite updo; [|done].
    destruct (eq_dec_actid r (ThreadEvent tid (eindex s1'))); subst.
    + exfalso.
      eapply NREX; split; [eauto|].
      rewrite UG; unfold add; unfold acts_set; ins.
      split; [eauto| rewrite EINDEX; eauto].
      rewrite UG; unfold add; unfold R_ex; ins.
      by rewrite updo; [| intro; desf; omega]; rewrite EINDEX, upds.
    + unfold val; rewrite updo; try done.
      apply NEW_VAL2; try done.
      unfold is_r in *; rewrite !updo in READ; try done.
      by unfold add, acts_set in IN; ins; desf.
Qed.

Lemma receptiveness_sim_inc (tid : thread_id)
      s1 s2 (INSTRS0 : instrs s1 = instrs s2)
      (expr_add : Instr.expr)
      xmod
      (ordr ordw : mode)
      (reg : Reg.t)
      (lexpr : Instr.lexpr)
      (ISTEP : Some (Instr.update
                       (Instr.fetch_add expr_add) xmod ordr ordw reg lexpr) =
               nth_error (instrs s1) (pc s1))
      (val_ : nat)
      (UPC : pc s2 = pc s1 + 1)
      (UG : G s2 =
            add_rmw (G s1) tid (eindex s1)
                    (Aload false ordr
                           (RegFile.eval_lexpr (regf s1) lexpr) val_)
                    (Astore xmod ordw (RegFile.eval_lexpr (regf s1) lexpr)
                            (val_ + RegFile.eval_expr (regf s1) expr_add))
                    ((eq (ThreadEvent tid s1.(eindex))) ∪₁
                     (DepsFile.expr_deps s1.(depf) expr_add))
                    (DepsFile.lexpr_deps (depf s1) lexpr)
                    (ectrl s1) ∅)
      (UINDEX : eindex s2 = eindex s1 + 2)
      (UREGS : regf s2 = RegFun.add reg val_ (regf s1))
      (UDEPS : depf s2 = RegFun.add reg (eq (ThreadEvent tid (eindex s1))) (depf s1))
      (UECTRL : ectrl s2 = ectrl s1)
      MOD (new_rfi : relation actid) new_val
      (NFRMW: MOD ∩₁ dom_rel (s2.(G).(rmw_dep)) ⊆₁ ∅)
      (NADDR : MOD ∩₁ dom_rel (s2.(G).(addr)) ⊆₁ ∅)
      (NREX:  MOD ∩₁ s2.(G).(acts_set) ∩₁ (R_ex s2.(G).(lab)) ⊆₁ ∅) 
      (NDATA: ⦗MOD⦘ ⨾ s2.(G).(data) ⨾ ⦗set_compl MOD⦘ ⊆ ∅₂)
      (TWF : thread_wf tid s1)
      (RFI_INDEX : new_rfi ⊆ ext_sb)
      (new_rfif : functional new_rfi⁻¹)
      s1' (SIM: sim_state s1 s1' MOD new_rfi new_val) :
 exists s2', (step tid) s1' s2' /\ sim_state s2 s2' MOD new_rfi new_val.
Proof.
  generalize (@new_write new_rfi new_rfif); intro F; destruct F as [new_w F].
  red in SIM; desc.
  assert (SAME_LOC : RegFile.eval_lexpr (regf s1) lexpr =
                     RegFile.eval_lexpr (regf s1') lexpr).
  { ins; eapply regf_lexpr_helper; eauto.
    ins; intro; eapply NADDR; unfolder; splits; eauto.
    exists (ThreadEvent tid (eindex s1)).
    rewrite UG; unfold add_rmw; basic_solver. } 

  cut (exists instrs pc G_ eindex regf depf ectrl, 
          step tid s1' (Build_state instrs pc G_ eindex regf depf ectrl) /\ 
          (sim_state s2 (Build_state instrs pc G_ eindex regf depf ectrl)
                     MOD new_rfi new_val)).
  { ins; desc; eauto. }
  do 7 eexists; splits; red; splits.
  { eexists; red; splits; [by ins; eauto|].
    eexists; splits; [eby rewrite <- INSTRS, <- PC |].
    eapply inc with (val := 
      if excluded_middle_informative (MOD (ThreadEvent tid (eindex s1'))) 
      then if excluded_middle_informative ((codom_rel new_rfi) (ThreadEvent tid (eindex s1'))) 
           then (get_val (val s1'.(G).(lab) (new_w (ThreadEvent tid (eindex s1')))))
           else (new_val (ThreadEvent tid (eindex s1')))
      else val_);
    reflexivity. }
  1,2,4,7: ins; congruence.
  { ins.
    destruct (G s2) as [acts2 lab2 rmw2 data2 addr2 ctrl2 rf2 co2].
    inversion UG; subst; clear UG.
    red in EXEC; desc.
    red; splits; ins.
    { by rewrite EINDEX, ACTS. }
    { rewrite EINDEX.
      unfold same_lab_u2v in *; intro e.
      destruct (eq_dec_actid e (ThreadEvent tid (eindex s1'))).
      { subst.
        rewrite updo; [|intros HH; clear -HH; inv HH; omega]. 
        rewrite !upds. unfold same_label_u2v.
        rewrite updo; [|intros HH; clear -HH; inv HH; omega]. 
        rewrite upds; auto.  }
      destruct (eq_dec_actid e (ThreadEvent tid (eindex s1' + 1))).
      { subst.
        rewrite !upds. unfold same_label_u2v; auto. }
      ins. rewrite !updo; auto. }
    { rewrite EINDEX.
      unfold val.
      destruct (eq_dec_actid a (ThreadEvent tid (eindex s1' + 1))).
      { subst.
        destruct (excluded_middle_informative (MOD (ThreadEvent tid (eindex s1')))) as [MN|NMN].
        { exfalso.
          eapply NDATA. 
          apply seq_eqv_lr. splits; eauto.
          basic_solver 10. }
        assert (SAME_VAL : RegFile.eval_expr (regf s1 ) expr_add =
                           RegFile.eval_expr (regf s1') expr_add).
        { ins; eapply regf_expr_helper; eauto.
          ins; intro; eapply NDATA; unfolder; splits; eauto.
            by rewrite EINDEX. }
        rewrite !upds. by rewrite SAME_VAL. }
      rewrite updo; auto.
      destruct (eq_dec_actid a (ThreadEvent tid (eindex s1'))).
      { subst.
        rewrite !upds.
        destruct (excluded_middle_informative (MOD (ThreadEvent tid (eindex s1')))) as [MN|NMN].
        { exfalso. eauto. }
        rewrite updo; [|intros HH; clear -HH; inv HH; omega]. 
          by rewrite upds. }
      rewrite !updo; auto.
      by apply OLD_VAL in NIN; unfold val in NIN; rewrite NIN. }
    { by rewrite RMW, EINDEX. }
    { by rewrite DATA, EINDEX, DEPF. }
    { by rewrite ADDR, EINDEX, DEPF. }
    { by rewrite CTRL, EINDEX, ECTRL. }
      by rewrite FRMW, EINDEX. }
  { ins; rewrite UREGS, UDEPS.
    unfold RegFun.add, RegFun.find in *; desf; eauto. }
  { eby ins; rewrite <- DEPF, <- EINDEX. }
  { ins; unfold acts_set, is_r, is_w in INr, INw, READ, WRITE; ins.
    destruct (eq_dec_actid r (ThreadEvent tid (eindex s1'+1))); subst.
    { by rewrite upds in READ; desf. }
    destruct (eq_dec_actid w (ThreadEvent tid (eindex s1'))); subst.
    rewrite updo in WRITE; [| intro; desf; omega].
    { by rewrite upds in WRITE; desf. }

    destruct (eq_dec_actid w (ThreadEvent tid (eindex s1' + 1))); subst.
    { exfalso.
      apply RFI_INDEX in RF; unfold ext_sb in RF.
      destruct INr as [INr|[INr|INr]]; subst.
      1,2: clear -RF; omega.
      destruct r; [eauto|]; desc.
      apply sim_execution_same_acts in EXEC.
      apply EXEC in INr.
      apply TWF in INr; desc.
      rewrite <- EINDEX in RF0.
      inv EE. clear -RF0 LT. omega. }

    assert (is_w (lab (G s1')) w) as WW'.
    { rewrite !updo in WRITE; edone. }

    unfold val.
    rewrite updo; auto.
    destruct (eq_dec_actid r (ThreadEvent tid (eindex s1'))); subst.
    { rewrite !upds.
      destruct (excluded_middle_informative (MOD (ThreadEvent tid (eindex s1')))) as [MN|NMN].
      2: eby exfalso.
      rewrite !updo; auto.
      destruct (excluded_middle_informative
                  (codom_rel new_rfi (ThreadEvent tid (eindex s1')))) as [|XX].
      2: { exfalso. apply XX. generalize RF. clear. basic_solver. }
      assert (w = new_w (ThreadEvent tid (eindex s1'))); subst.
      { edestruct new_rfi_unique with
            (r:=ThreadEvent tid (eindex s1')) as [wu [_ HH]]; eauto.
        transitivity wu.
        2: by apply HH.
        symmetry. apply HH. do 2 red. generalize RF. clear. basic_solver. }
      unfold get_val.
      clear -WW'. unfold is_w in WW'. desf. }
    rewrite !updo; auto.
    eapply NEW_VAL1; try edone.
    { by rewrite <- EINDEX in n0; desf. }
    { by rewrite <- EINDEX in n; desf. }
      by rewrite !updo in READ; try edone. }
  simpl; ins.
  destruct (eq_dec_actid r (ThreadEvent tid (eindex s1'+1))); subst.
  { by unfold is_r in READ; rewrite upds in READ; desf. }
  unfold val; rewrite updo; [|done].
  destruct (eq_dec_actid r (ThreadEvent tid (eindex s1'))); subst.
  { rewrite upds.
    destruct (excluded_middle_informative (MOD (ThreadEvent tid (eindex s1')))) as [MN|NMN].
    2: eby exfalso.
    destruct (excluded_middle_informative
                (codom_rel new_rfi (ThreadEvent tid (eindex s1')))) as [XX|];
      auto.
    exfalso; eauto. }
  unfold val; rewrite updo; try done.
  apply NEW_VAL2; try done.
  unfold is_r in *; rewrite !updo in READ; try done.
    by unfold add, acts_set in IN; ins; desf.
Qed.

Lemma receptiveness_sim_step (tid : thread_id)
  s1 s2
  (STEP : (step tid) s1 s2) 
  MOD (new_rfi : relation actid) new_val
  (NCTRL : MOD ∩₁ ectrl s2 ⊆₁ ∅)
  (NFRMW: MOD ∩₁ dom_rel (s2.(G).(rmw_dep)) ⊆₁ ∅)
  (NADDR : MOD ∩₁ dom_rel (s2.(G).(addr)) ⊆₁ ∅)
  (NREX:  MOD ∩₁ s2.(G).(acts_set) ∩₁ (R_ex s2.(G).(lab)) ⊆₁ ∅) 
  (NDATA: ⦗MOD⦘ ⨾ s2.(G).(data) ⨾ ⦗set_compl MOD⦘ ⊆ ∅₂)
  (new_rfif : functional new_rfi⁻¹)
   (RFI_INDEX : new_rfi ⊆ ext_sb)
  (TWF : thread_wf tid s1)
  s1' (SIM: sim_state s1 s1' MOD new_rfi new_val) :
 exists s2', (step tid) s1' s2' /\ sim_state s2 s2' MOD new_rfi new_val.
Proof.
destruct STEP; red in H; desf.
destruct ISTEP0; desf.
- eby eapply receptiveness_sim_assign.
- eby eapply receptiveness_sim_if_else.
- eby eapply receptiveness_sim_if_then.
- eby eapply receptiveness_sim_load.
- eby eapply receptiveness_sim_store.
- eby eapply receptiveness_sim_fence.
- eby eapply receptiveness_sim_cas_fail.
- eby eapply receptiveness_sim_cas_suc.
- eby eapply receptiveness_sim_inc.
Qed.


Lemma receptiveness_sim (tid : thread_id)
  s1 s2
  (STEPS : (step tid)＊ s1 s2)
  MOD (new_rfi : relation actid) new_val
  (NCTRL : MOD ∩₁ ectrl s2 ⊆₁ ∅)
  (NFRMW: MOD ∩₁ dom_rel (s2.(G).(rmw_dep)) ⊆₁ ∅)
  (NADDR : MOD ∩₁ dom_rel (s2.(G).(addr)) ⊆₁ ∅)
  (NREX:  MOD ∩₁ s2.(G).(acts_set) ∩₁ (R_ex s2.(G).(lab)) ⊆₁ ∅) 
  (NDATA: ⦗MOD⦘ ⨾ s2.(G).(data) ⨾ ⦗set_compl MOD⦘ ⊆ ∅₂)
  (new_rfif : functional new_rfi⁻¹)
   (RFI_INDEX : new_rfi ⊆ ext_sb)
  (TWF : thread_wf tid s1)
  s1' (SIM: sim_state s1 s1' MOD new_rfi new_val) :
 exists s2', (step tid)＊ s1' s2' /\ sim_state s2 s2' MOD new_rfi new_val.
Proof.
apply clos_rt_rtn1 in STEPS.
induction STEPS.
by eexists; vauto.
exploit IHSTEPS.
* unfolder; splits; ins; eauto; desf.
  eapply ectrl_increasing in H1; eauto.
  eapply NCTRL; basic_solver.
* unfolder; splits; ins; eauto; desf.
  eapply rmw_dep_increasing in H1; eauto.
  eapply NFRMW; basic_solver.
*  unfolder; splits; ins; eauto; desf.
  eapply addr_increasing in H1; eauto.
  eapply NADDR; basic_solver.
* unfolder; splits; ins; eauto; desf.
  eapply NREX; split; [split; [eauto |] |].
  eapply acts_increasing; edone.
  eapply is_r_ex_increasing; eauto.
  eapply thread_wf_steps; try edone.
  by apply clos_rtn1_rt.
  basic_solver.
* unfolder; splits; ins; eauto; desf.
  eapply data_increasing in H1; eauto.
  eapply NDATA; basic_solver.
* intro; desc.
  eapply receptiveness_sim_step in x0; eauto; desf.
  + exists s2'0; splits; eauto. 
    by eapply rt_trans; [eauto | econs].
  + eapply thread_wf_steps; try edone.
    by apply clos_rtn1_rt.
Qed.

Lemma receptiveness_helper (tid : thread_id)
      s_init s
      (GPC : wf_thread_state tid s_init)
      (new_val : actid -> value)
      (new_rfi : relation actid)
      (MOD: actid -> Prop)
      (STEPS : (step tid)＊ s_init s)
      (new_rfiE : new_rfi ≡ ⦗s.(G).(acts_set)⦘ ⨾ new_rfi ⨾ ⦗s.(G).(acts_set)⦘)
      (new_rfiD : new_rfi ≡ ⦗is_w s.(G).(lab)⦘ ⨾ new_rfi ⨾ ⦗is_r s.(G).(lab)⦘)
      (new_rfif : functional new_rfi⁻¹)
      (RFI_INDEX : new_rfi ⊆ ext_sb)
      (NCTRL : MOD ∩₁ ectrl s ⊆₁ ∅) 
      (NFRMW: MOD ∩₁ dom_rel (s.(G).(rmw_dep)) ⊆₁ ∅)
      (NADDR : MOD ∩₁ dom_rel (s.(G).(addr)) ⊆₁ ∅)
      (NREX:  MOD ∩₁ s.(G).(acts_set) ∩₁ (R_ex s.(G).(lab)) ⊆₁ ∅) 
      (NDATA: ⦗MOD⦘ ⨾ s.(G).(data) ⨾ ⦗set_compl MOD⦘ ⊆ ∅₂) 
      (new_rfiMOD : codom_rel new_rfi ⊆₁ MOD)
      (NMODINIT: MOD ∩₁ s_init.(ProgToExecution.G).(acts_set) ⊆₁ ∅)
      (EMOD : MOD ⊆₁ (ProgToExecution.G s).(acts_set)) :
    exists s',
      ⟪ STEPS' : (step tid)＊ s_init s' ⟫ /\
      ⟪ EXEC : sim_execution s.(G) s'.(G) MOD ⟫ /\
      ⟪ NEW_VAL1 : forall r w (RF: new_rfi w r), val (s'.(G).(lab)) r = val (s'.(G).(lab)) w ⟫ /\
      ⟪ NEW_VAL2 : forall r (RR : is_r s'.(G).(lab) r) (IN: MOD r) (NIN: ~ (codom_rel new_rfi) r),
          val (s'.(G).(lab)) r = Some (new_val r) ⟫ /\
      ⟪ OLD_VAL : forall a (NIN: ~ MOD a), val (s'.(G).(lab)) a = val (s.(G).(lab)) a ⟫.
Proof.
apply receptiveness_sim with (s1':= s_init) (MOD:=MOD) (new_rfi:=new_rfi) (new_val:=new_val) in STEPS.
all: try done.
- desc.
  red in STEPS0; desc.
  exists s2'; splits; eauto.
  * ins; eapply NEW_VAL1; try done.
    + hahn_rewrite new_rfiE in RF; unfolder in RF; desf.
      apply sim_execution_same_acts in EXEC.
      revert EXEC; basic_solver.
    + hahn_rewrite new_rfiE in RF; unfolder in RF; desf.
      apply sim_execution_same_acts in EXEC.
      revert EXEC; basic_solver.
    + hahn_rewrite new_rfiD in RF; unfolder in RF; desf.
      apply sim_execution_same_r in EXEC.
      revert EXEC; basic_solver.
    + hahn_rewrite new_rfiD in RF; unfolder in RF; desf.
      apply sim_execution_same_w in EXEC.
      revert EXEC; basic_solver.
    + revert new_rfiMOD; basic_solver.
  * ins; eapply NEW_VAL2; try done.
    apply sim_execution_same_acts in EXEC.
    revert EXEC; basic_solver.
  * ins; red in EXEC; desc.
    by eapply OLD_VAL.
- red; apply (acts_rep GPC).
- red; splits; eauto.
  { red; splits; eauto; red; red; ins; red; eauto; desf. }
  ins; exfalso; revert NMODINIT; basic_solver.
  ins; exfalso; unfolder in *; basic_solver.
Qed.

Lemma receptiveness_ectrl_helper (tid : thread_id) 
      s_init s 
      (GPC : wf_thread_state tid s_init)
      (STEPS : (step tid)＊ s_init s)
      MOD (NCTRL: MOD ∩₁ dom_rel (s.(G).(ctrl)) ⊆₁ ∅) 
      (NMODINIT: MOD ∩₁ s_init.(G).(acts_set) ⊆₁ ∅):
      exists s', (step tid)＊ s_init s' /\
                 (MOD ∩₁ ectrl s' ⊆₁ ∅) /\ s'.(G) = s.(G).
Proof.
apply clos_rt_rtn1 in STEPS.
induction STEPS.
- exists s_init; splits; vauto.
  by rewrite (wft_ectrlE GPC).
- assert (A: MOD ∩₁ dom_rel (ctrl (G y)) ⊆₁ ∅).
  generalize (ctrl_increasing H).
  revert NCTRL; basic_solver 12.
  apply IHSTEPS in A.
  desc.
  destruct  (classic (MOD ∩₁ ectrl z ⊆₁ ∅)).
  * exists z; splits; eauto.
    eapply rt_trans.
    eby apply clos_rtn1_rt.
    by apply rt_step.
  * exists s'; splits; eauto.
    transitivity (G y); [done|].
    eapply ectrl_ctrl_step; try edone.
    destruct (classic (exists a : actid, (MOD ∩₁ ectrl z) a)); auto.
    exfalso; apply H0; unfolder; ins; eapply H1; basic_solver.
Qed.

Lemma receptiveness_full (tid : thread_id)
      s_init s
      (new_val : actid -> value)
      (new_rfi : relation actid)
      (MOD: actid -> Prop)
      (GPC : wf_thread_state tid s_init)
      (STEPS : (step tid)＊ s_init s)
      (new_rfiE : new_rfi ≡ ⦗s.(G).(acts_set)⦘ ⨾ new_rfi ⨾ ⦗s.(G).(acts_set)⦘)
      (new_rfiD : new_rfi ≡ ⦗is_w s.(G).(lab)⦘ ⨾ new_rfi ⨾ ⦗is_r s.(G).(lab)⦘)
      (new_rfif : functional new_rfi⁻¹)
      (RFI_INDEX : new_rfi ⊆ ext_sb)
      (new_rfiMOD : codom_rel new_rfi ⊆₁ MOD)
      (EMOD : MOD ⊆₁ (ProgToExecution.G s).(acts_set))
      (NMODINIT: MOD ∩₁ s_init.(ProgToExecution.G).(acts_set) ⊆₁ ∅)
      (NFRMW: MOD ∩₁ dom_rel (s.(G).(rmw_dep)) ⊆₁ ∅)
      (NADDR : MOD ∩₁ dom_rel (s.(G).(addr)) ⊆₁ ∅)
      (NREX:  MOD ∩₁ s.(G).(acts_set) ∩₁(R_ex s.(G).(lab)) ⊆₁ ∅) 
      (NCTRL: MOD ∩₁ dom_rel (s.(G).(ctrl)) ⊆₁ ∅)
      (NDATA: ⦗MOD⦘ ⨾ s.(G).(data) ⨾ ⦗set_compl MOD⦘ ⊆ ∅₂) :
    exists s',
      ⟪ STEPS' : (step tid)＊ s_init s' ⟫ /\
      ⟪ RACTS : s.(G).(acts) = s'.(G).(acts) ⟫ /\
      ⟪ RRMW  : s.(G).(rmw)  ≡ s'.(G).(rmw)  ⟫ /\
      ⟪ RDATA : s.(G).(data) ≡ s'.(G).(data) ⟫ /\
      ⟪ RADDR : s.(G).(addr) ≡ s'.(G).(addr) ⟫ /\
      ⟪ RCTRL : s.(G).(ctrl) ≡ s'.(G).(ctrl) ⟫  /\
      ⟪ RFAILRMW : s.(G).(rmw_dep) ≡ s'.(G).(rmw_dep) ⟫  /\
      ⟪ SAME : same_lab_u2v (s'.(G).(lab)) (s.(G).(lab))⟫ /\
      ⟪ NEW_VAL1 : forall r w (RF: new_rfi w r), val (s'.(G).(lab)) r = val (s'.(G).(lab)) w ⟫ /\
      ⟪ NEW_VAL2 : forall r (RR : is_r s'.(G).(lab) r) (IN: MOD r) (NIN: ~ (codom_rel new_rfi) r),
          val (s'.(G).(lab)) r = Some (new_val r) ⟫ /\
      ⟪ OLD_VAL : forall a (NIN: ~ MOD a), val (s'.(G).(lab)) a = val (s.(G).(lab)) a ⟫.
Proof.
forward (apply receptiveness_ectrl_helper); try edone.

ins; desc.
rewrite <- H1 in *.
clear STEPS H1 s.
forward (eapply receptiveness_helper with (new_rfi:=new_rfi)); ins; eauto.
desc.
red in EXEC; desc.
eexists; splits; eauto.
Qed.
