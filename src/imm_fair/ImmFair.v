From imm Require Import Events.
From imm Require Import Execution.
From imm Require Import Execution_eco.
From imm Require Import imm_s_hb imm_hb.
From imm Require Import imm_s.
From imm Require Import imm_bob imm_s_ppo.
(* From imm Require Import CombRelations. *)
(* From imm Require Import AuxDef. *)
(* From imm Require Import AuxRel2. *)
(* From imm Require Import TraversalConfig. *)
From imm Require Import imm_s_rfppo.
(* From imm Require Import Traversal.  *)
From imm Require Import FairExecution.
(* From imm Require Import FinExecution. *)

From hahn Require Import Hahn.


(* TODO: move to IMM *)
Definition imm_fair G sc := fsupp (ar G sc)⁺.

Section ImmFairProperties.

  Variables (G: execution) (sc: relation actid).
  Hypotheses (WF: Wf G) (WFSC: wf_sc G sc).
  Hypotheses (COM: complete G) (IMMCON: imm_consistent G sc). 
  Hypotheses (FAIR: mem_fair G) (IMM_FAIR: imm_fair G sc).

  Notation "'E'" := (acts_set G).
  Notation "'R'" := (fun x => is_true (is_r (lab G) x)).
  Notation "'W'" := (fun x => is_true (is_w (lab G) x)).
  Notation "'F'" := (fun x => is_true (is_f (lab G) x)).
  
  Lemma fsupp_rf_ppo_loc: fsupp (rf G ⨾ ppo G ∩ same_loc (lab G)).
  Proof using WF FAIR. 
    apply fsupp_seq; [by apply fsupp_rf| ]. 
    rewrite ppo_in_sb; auto. by apply fsupp_sb_loc. 
  Qed.

  Lemma fsupp_rf_ppo_loc_ct:
    fsupp (rf G ⨾ ppo G ∩ same_loc (lab G))⁺.
  Proof using FAIR WF IMMCON.
    eapply fsupp_mori with (x := (co G)^* ⨾ rf G ⨾ ppo G ∩ same_loc (lab G)).
    2: { apply fsupp_seq; [| by apply fsupp_rf_ppo_loc].
         apply fsupp_ct_rt. rewrite ct_of_trans; [| by apply WF].
         apply FAIR. }
    red.
    rewrite ctEE. apply inclusion_bunion_l. intros i _. induction i.
    { simpl. apply seq_mori; basic_solver. }
    rewrite pow_S_end. rewrite IHi.
    arewrite (rf G ≡ ⦗W⦘ ⨾ rf G) at 2.
    { rewrite wf_rfD; basic_solver. }
    hahn_frame.
    etransitivity; [| apply inclusion_t_rt]. rewrite ct_end. hahn_frame_l.
    rewrite ppo_in_sb; auto. apply rf_sbl_w_in_co; auto.
    cdes IMMCON. by apply imm_s_hb.coherence_sc_per_loc. 
  Qed.  

  Lemma wf_ar_rf_ppo_loc_ct_inf:
    well_founded (ar G sc ∪ rf G ;; ppo G ∩ same_loc (lab G))⁺.
  Proof using WF IMMCON IMM_FAIR FAIR COM. 
    apply fsupp_well_founded.
    3: by apply transitive_ct.
    2: by apply ar_rf_ppo_loc_acyclic.

    rewrite ct_unionE. apply fsupp_union.
    { by apply fsupp_rf_ppo_loc_ct. }
    apply fsupp_seq.
    { apply fsupp_ct_rt, fsupp_rf_ppo_loc_ct; auto. }  

    eapply fsupp_mori; [| by apply IMM_FAIR].
    red. rewrite rtE, seq_union_r, seq_id_r.
    rewrite ar_rf_ppo_loc_ct_in_ar_ct; auto.
    etransitivity.
    2: { rewrite <- ct_of_ct. reflexivity. }
    apply clos_trans_mori. basic_solver. 
  Qed.

End ImmFairProperties.
