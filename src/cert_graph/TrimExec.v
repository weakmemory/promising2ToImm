From imm Require Import Execution.
From imm Require Import Events.
From imm Require Import FinExecution.
From hahn Require Import Hahn.
From imm Require Import imm_s.
From imm Require Import imm_hb.

Require Import AuxRel.
Import ListNotations. 

Definition trim_events (G: execution) :=
  acts_set G ∩₁ (fun e => exists e', acts_set G e' /\ ~ is_init e' /\ same_loc (lab G) e e').

Definition trim_exec (G: execution) :=
  let E' := trim_events G in 
  {| acts_set := E';
     lab := lab G;
     rmw := rmw G;
     data := data G;
     addr := addr G;
     ctrl := ctrl G;
     rmw_dep := rmw_dep G;
     rf := rf G;
     co := co G;
  |}.

Section TrimEvents.
  Variables (G: execution) (sc_: relation actid).
  Hypothesis (WF: Wf G).
  Hypothesis (Wf_sc: wf_sc G sc_). 

  Lemma trim_same_ninit:
    acts_set G \₁ is_init ≡₁ acts_set (trim_exec G) \₁ is_init. 
  Proof using.
    unfold trim_exec, trim_events. simpl. 
    split; [| basic_solver].
    unfolder. ins. desc. splits; auto.
    exists x. splits; auto. basic_solver.
  Qed.
    
  Lemma trim_fin_exec_locs (FIN: fin_exec G):
    exists (locs: list location),
      forall e l (E'e: acts_set (trim_exec G) e) (LOC: loc (lab G) e = Some l),
        In l locs.
  Proof using.
    do 2 red in FIN. desc.
    destruct (classic (inhabited location)) as [[l0]| ].
    2: { exists []. ins. eauto. }
    set (defloc := fun e => match (loc (lab G) e) with | Some l => l | _ => l0 end).
    exists (map defloc findom). ins. apply in_map_iff.
    do 2 red in E'e. desc.  
    exists e'. split.
    2: { by apply FIN. }
    unfold defloc. by rewrite <- E'e2, LOC.
  Qed. 

  Lemma trim_fin_exec_  (FIN': fin_exec G):
    fin_exec_full (trim_exec G).
  Proof using WF.
    red. unfold trim_exec, trim_events. simpl.
    rewrite AuxRel.set_split_comlete with (s := is_init) at 1.

    edestruct trim_fin_exec_locs as [locs FIN_LOCS]; eauto. 
    red in FIN'.
    apply set_finite_union. split.
    2: { eapply set_finite_mori; eauto. red. basic_solver. }
    
    exists (map InitEvent locs). ins.
    unfolder in IN. desc. destruct x; [| done]. 
    apply in_map_iff. eexists. split; eauto.
    eapply FIN_LOCS; eauto.
    { red. unfolder. splits; eauto. exists e'. splits; eauto. basic_solver. }
    rewrite <- IN3. unfold loc. rewrite wf_init_lab; auto. 
  Qed.

  Lemma trim_events_inclusion:
    trim_events G ⊆₁ acts_set G.
  Proof using. unfold trim_events. basic_solver. Qed. 

  Lemma trim_preserves_wf_sc:
    wf_sc (trim_exec G) (restr_rel (trim_events G) sc_).
  Proof using Wf_sc.
    destruct Wf_sc. split; simpl. 
    { basic_solver. }
    { rewrite wf_scD, restr_relE. basic_solver. }
    { basic_solver. }
    { red. ins. red in wf_sc_total.
      unfolder in *. desc. 
      forward eapply (@trim_events_inclusion a) as Ea; [basic_solver| ].
      forward eapply (@trim_events_inclusion b) as Eb; [basic_solver| ].
      specialize wf_sc_total with (a := a) (b := b).
      specialize_full wf_sc_total; auto. 
      desf; auto. }
    basic_solver.
  Qed.

  Lemma trim_sb_inclusion:
    sb (trim_exec G) ⊆ sb G.
  Proof using.
    unfold sb. rewrite <- !restr_relE.
    apply restr_rel_mori; [apply trim_events_inclusion | done].
  Qed.

  (* Lemma trim_sw_inclusion: *)
  (*   sw (trim_exec G) ⊆ sw G. *)
  (* Proof using. *)
  (*   unfold sw. simpl. rewrite trim_sb_inclusion. hahn_frame. *)
  (*   rewrite trim_sb_inclusion. simpl. hahn_frame.  *)
  (*   apply seq_mori; [| basic_solver]. *)
  (*   simpl. rewrite trim_sb_inclusion. basic_solver.  *)
  (* Qed. *)
  
  (* Lemma trim_hb_inclusion (G: execution): *)
  (*   hb (trim_exec G) ⊆ hb G. *)
  (* Proof using. *)
  (*   unfold hb. apply clos_trans_mori. *)
  (*   by rewrite trim_sb_inclusion, trim_sw_inclusion. *)
  (* Qed.  *)
  
  (* (* Lemma trim_rf_same_events (G: execution)  (WF_: Wf G) (SCpL: sc_per_loc G): *) *)
  (* (*   rf (trim_exec G) ≡ ⦗acts_set G⦘ ⨾ rf G ⨾ ⦗acts_set G⦘.  *) *)
  (* (* Proof using. *) *)
  (* (*   simpl. split. *) *)
  (* (*   { rewrite <- !restr_relE. *) *)
  (* (*     apply restr_rel_mori; [apply trim_events_inclusion | basic_solver]. } *) *)
  (* (*   red. intros x y REL%seq_eqv_lr. apply seq_eqv_lr. desc. *) *)
  (* (*   apply no_rf_to_init, seq_eqv_r in REL0; auto. desc. *) *)
  (* (*   splits; auto. *) *)
  (* (*   2: { apply trim_same_ninit. split; auto. } *) *)
  (* (*   red. split; auto. exists y. splits; auto. apply wf_rfl; auto. *) *)
  (* (* Qed.  *) *)

  (* (* Lemma trim_co_same_events (G: execution)  (WF_: Wf G) (SCpL: sc_per_loc G): *) *)
  (* (*   co (trim_exec G) ≡ ⦗acts_set G⦘ ⨾ co G ⨾ ⦗acts_set G⦘.  *) *)
  (* (* Proof using. *) *)
  (* (*   simpl. split. *) *)
  (* (*   { rewrite <- !restr_relE. *) *)
  (* (*     apply restr_rel_mori; [apply trim_events_inclusion | basic_solver]. } *) *)
  (* (*   red. intros x y REL%seq_eqv_lr. apply seq_eqv_lr. desc. *) *)
  (* (*   apply no_co_to_init, seq_eqv_r in REL0; auto. desc. *) *)
  (* (*   splits; auto. *) *)
  (* (*   2: { apply trim_same_ninit. split; auto. } *) *)
  (* (*   red. split; auto. exists y. splits; auto. apply wf_col; auto. *) *)
  (* (* Qed.  *) *)

  (* Lemma trim_fr_same (G: execution) (WF_: Wf G) (SCpL: sc_per_loc G): *)
  (*   fr (trim_exec G) ≡ fr G. *)
  (* Proof using. by unfold fr. Qed.  *)
  
  (* Lemma trim_eco_same (G: execution) (WF_: Wf G) (SCpL: sc_per_loc G): *)
  (*   eco (trim_exec G) ≡ eco G. *)
  (* Proof using. *)
  (*   unfold eco. simpl. rewrite trim_fr_same; auto.  *)
  (* Qed. *)
  
  (* (* Lemma sl_rel_same (G: execution) (r: execution -> relation actid) *) *)
  (* (*       (SL: forall G (WF: Wf G), r G ⊆ same_loc (lab G)) *) *)
  (* (*       (NI: forall G (WF: Wf G), r G ≡ r G ⨾ ⦗set_compl is_init⦘) *) *)
  (* (*   : *) *)
  (* (*   r (trim_exec G) ≡ r G. *) *)
  (* (* Proof using. *) *)
  (* (*   unfold trim_exec. simpl.  *) *)

  (* Lemma trim_ar_inclusion G sc_ (WF_: Wf G) (SCpL: sc_per_loc G): *)
  (*   ar (trim_exec G) (restr_rel (trim_events G) sc_) ⊆ ar G sc_. *)
  (* Proof using. *)
  (*   unfold ar. apply union_mori. *)
  (*   2: { unfold ar_int. simpl. apply union_mori. *)
  (*        2: { simpl. unfold W_ex. simpl. *)
    
  (* Lemma trim_preserves_imm_consistency (G: execution) (sc_: relation actid) *)
  (*       (WF_: Wf G) (CONS: imm_consistent G sc_): *)
  (*   imm_consistent (trim_exec G) (restr_rel (trim_events G) sc_). *)
  (* Proof using. *)
  (*   cdes CONS. *)
  (*   assert (sc_per_loc G) as SCpL; [by apply coherence_sc_per_loc| ].  *)

  (*   red. splits.     *)
  (*   { apply trim_preserves_wf_sc; auto. } *)
  (*   { red in Csc. eapply irreflexive_mori; [| by apply Csc]. red. *)
  (*     rewrite trim_hb_inclusion, trim_eco_inclusion; auto. *)
  (*     repeat (apply seq_mori; basic_solver). } *)
  (*   { red. rewrite trim_rf_same_events; auto. rewrite <- wf_rfE; auto.  *)
  (*     simpl. by rewrite trim_events_inclusion. } *)
  (*   { red. eapply irreflexive_mori; [| by apply Cint]. red. *)
  (*     rewrite trim_hb_inclusion, trim_eco_inclusion; auto. basic_solver. } *)
  (*   { red.  *)
  (*     red in Comp.  *)

End TrimEvents.   
