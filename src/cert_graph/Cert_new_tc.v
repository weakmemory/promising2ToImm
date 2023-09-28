From hahn Require Import Hahn.

From imm Require Import Events.
From imm Require Import Execution.
From hahnExt Require Import HahnExt.
From hahnExt Require Import HahnExt.

(* From imm Require Import TraversalConfig. *)
(* From imm Require Import TraversalConfigAlt. *)
From imm Require Import TraversalOrder.
From imm Require Import TLSCoherency.
From imm Require Import IordCoherency.
From imm Require Import SimClosure.
From imm Require Import TlsEventSets.
From hahnExt Require Import HahnExt.

Set Implicit Arguments.

Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'NTid_' t" := (fun x => tid x <> t) (at level 1).

Section CertT.

Variable G : execution.
Variable T : trav_label -> Prop. 
Variable thread : thread_id.
Variable E0 : actid -> Prop.

Hypothesis TCOH : tls_coherent G T.
Hypothesis E0_in_E : E0 ⊆₁ acts_set G.

Notation "'C'" := (covered T).
Notation "'I'" := (issued T).
Notation "'S'" := (reserved T).

Definition certT :=
  T ∩₁ action ↓₁ (eq ta_cover ∪₁ eq ta_issue ∪₁
                     (fun x => is_true (is_ta_propagate x))) ∪₁
    (eq ta_reserve <*> (I ∪₁ S ∩₁ Tid_ thread)) ∪₁
    ((eq ta_cover) <*> (E0 ∩₁ NTid_ thread)).

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

Lemma init_tls_in_certT : init_tls G ⊆₁ certT.
Proof using TCOH.
  unfold init_tls.
  arewrite (eq ta_cover ∪₁ eq ta_issue ∪₁
            eq ta_reserve ∪₁ is_ta_propagate_to_G G ⊆₁
            (eq ta_cover ∪₁ eq ta_issue ∪₁ is_ta_propagate_to_G G) ∪₁
            eq ta_reserve).
  { basic_solver 10. }
  rewrite set_pair_union_l. unionL.
  { unfold certT; repeat unionR left.
    rewrite <- (tls_coh_init TCOH).
    unfold init_tls, set_pair.
    unfolder; ins; do 2 desf; eauto 30.
    ins. splits; auto.
    match goal with
    | H : is_ta_propagate_to_G _ _ |- _ => rename H into HH
    end.
    inv HH. desf; auto. }
  unfold certT.
  transitivity (eq ta_reserve <*> (I ∪₁ S ∩₁ Tid_ thread)).
  2: now eauto with hahn.
  apply set_pair_mori; eauto with hahn.
  transitivity I; eauto with hahn.
  rewrite <- init_issued; eauto.
  now rewrite set_interC.
Qed.

End CertT.
