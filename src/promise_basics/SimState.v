From hahn Require Import Hahn.
Require Import PromisingLib.
From imm Require Import Events Execution.
From imm Require Import ProgToExecution.
From imm Require Import ProgToExecutionProperties.
Require Import PromiseLTS.

Set Implicit Arguments.

Inductive sim_mode := sim_normal | sim_certification.
  
Definition sim_state_helper G smode thread
           (state state' : Language.state (thread_lts thread)) : Prop :=
  ⟪ STEPS : (step thread)＊ state state' ⟫ /\
  ⟪ TERMINAL : smode = sim_normal -> is_terminal state' ⟫ /\
  ⟪ TEH  : thread_restricted_execution G thread state'.(ProgToExecution.G) ⟫.

Definition sim_state G smode (C : actid -> Prop) thread
           (state : Language.state (thread_lts thread)) : Prop :=
  ⟪ PCOV : forall index , C (ThreadEvent thread index) <-> index < (eindex state)⟫ /\
  exists state', sim_state_helper G smode state state'.

Lemma sim_state_other_thread_step G
      (C C' : actid -> Prop) smode thread (state : Language.state (thread_lts thread))
      (CINCL : C ⊆₁ C')
      (COVSTEP : forall a, tid a = thread -> C' a -> C a)
      (SIMSTATE: sim_state G smode C state) :
  sim_state G smode C' state.
Proof using.
  cdes SIMSTATE.
  red. splits; eauto.
  ins. split; ins.
  { apply PCOV. apply COVSTEP; eauto. }
  apply CINCL. by apply PCOV.
Qed.
