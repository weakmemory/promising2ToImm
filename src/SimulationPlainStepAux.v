From hahn Require Import Hahn.
Require Import PromisingLib.
From Promising Require Import TView View Time Event Cell Thread Memory Configuration.

Require Import Events Execution.
Require Import PArith.
Require Import Setoid.
Require Import MaxValue.
Require Import ViewRel.
Require Import SimulationRel.
Require Import PromiseLTS.
Require Import ProgToExecution.

Lemma rtc_lang_tau_step_rtc_thread_tau_step
      thread st1 st2 lc sc mem
      (STEP: rtc (Language.step (thread_lts thread) ProgramEvent.silent) st1 st2):
  rtc (@Thread.tau_step (thread_lts thread))
      (Thread.mk (thread_lts thread) st1 lc sc mem)
      (Thread.mk (thread_lts thread) st2 lc sc mem).
Proof.
  induction STEP.
  { econs 1. }
  econs 2; eauto. econs.
  { econs. econs 2. econs; [|econs 1]; eauto. }
  simpls.
Qed.

Lemma tau_steps_same_instrs thread 
      (s1 s2 : Thread.t (thread_lts thread))
      (ESTEPS : rtc (Thread.tau_step (lang:=thread_lts thread)) s1 s2) :
  instrs (Thread.state s2) = instrs (Thread.state s1).
Proof.
  induction ESTEPS; ins; desf.
  destruct y; simpls.
  rewrite IHESTEPS.
  clear dependent z.
  inv H. inv TSTEP. inv STEP; inv STEP0.
  simpls. inv STATE. desc.
    by cdes ISTEP.
Qed.

Lemma tau_steps_rmw_is_xacq (PC : Configuration.t) thread
      (state : ProgToExecution.state)
      (local : Local.t)
      (XACQIN : ProgToExecutionProperties.rmw_is_xacq_instrs (instrs state))
      (ev : ProgramEvent.t)
      (state'' state''' : ProgToExecution.state)
      (ESTEPS : rtc (Thread.tau_step (lang:=thread_lts thread))
                    (Thread.mk (thread_lts thread)
                               state local
                               PC.(Configuration.sc)
                               PC.(Configuration.memory))
                    (Thread.mk (thread_lts thread)
                               state'' local
                               PC.(Configuration.sc)
                               PC.(Configuration.memory)))
      (STEP : lts_step thread ev state'' state''') :
  ProgToExecutionProperties.rmw_is_xacq_instrs (instrs state''').
Proof.
  cdes STEP. cdes ISTEP. rewrite <- INSTRS.
  arewrite (instrs state'' = instrs state); auto.
  clear -ESTEPS.
  remember (Thread.mk (thread_lts thread)
                      state local
                      PC.(Configuration.sc)
                           PC.(Configuration.memory)) as s1.
  remember (Thread.mk (thread_lts thread)
                      state'' local
                      PC.(Configuration.sc)
                           PC.(Configuration.memory)) as s2.
  arewrite (state   = Thread.state s1) by desf.
  arewrite (state'' = Thread.state s2) by desf.
  eapply tau_steps_same_instrs; eauto.
Qed.
