Require Import PArith Setoid.
From hahn Require Import Hahn.
Require Import PromisingLib.
From Promising2 Require Import TView View Time Event Cell Thread Memory Configuration Local.

From imm Require Import Events Execution.
From imm Require Import ProgToExecution.
From imm Require Import RMWinstrProps.
Require Import MaxValue.
Require Import ViewRel.
Require Import SimulationRel.
Require Import PromiseLTS.

Lemma rtc_lang_tau_step_rtc_thread_tau_step
      thread st1 st2 lc sc mem
      (STEP: rtc (Language.step (thread_lts thread) ProgramEvent.silent) st1 st2):
  rtc (@Thread.tau_step (thread_lts thread))
      (Thread.mk (thread_lts thread) st1 lc sc mem)
      (Thread.mk (thread_lts thread) st2 lc sc mem).
Proof using.
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
Proof using.
  induction ESTEPS; ins; desf.
  destruct y; simpls.
  rewrite IHESTEPS.
  clear dependent z.
  inv H. inv TSTEP. inv STEP; inv STEP0.
  simpls. inv STATE. desc.
    by cdes ISTEP.
Qed.

Lemma tau_steps_step_same_instrs (PC : Configuration.t) thread
      (state : ProgToExecution.state)
      (local : Local.t)
      (ev : ProgramEvent.t)
      (state'' state''' : ProgToExecution.state)
      (ESTEPS : rtc (Thread.tau_step (lang:=thread_lts thread))
                    (Thread.mk (thread_lts thread)
                               state local
                               (Configuration.sc PC)
                               (Configuration.memory PC))
                    (Thread.mk (thread_lts thread)
                               state'' local
                               (Configuration.sc PC)
                               (Configuration.memory PC)))
      (STEP : lts_step thread ev state'' state''') :
  instrs state''' = instrs state.
Proof using.
  cdes STEP. cdes ISTEP. rewrite <- INSTRS.
  clear -ESTEPS.
  remember (Thread.mk (thread_lts thread)
                      state local
                      (Configuration.sc PC)
                           (Configuration.memory PC)) as s1.
  remember (Thread.mk (thread_lts thread)
                      state'' local
                      (Configuration.sc PC)
                           (Configuration.memory PC)) as s2.
  arewrite (state   = Thread.state s1) by desf.
  arewrite (state'' = Thread.state s2) by desf.
  eapply tau_steps_same_instrs; eauto.
Qed.
