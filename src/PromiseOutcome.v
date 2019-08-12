From hahn Require Import Hahn.
Require Import PromisingLib.
From Promising Require Import Event Cell Memory Configuration Thread.
From imm Require Import Prog.
From imm Require Import ProgToExecution.
From imm Require Import Events.
From imm Require Import Event_imm_promise.
From imm Require Import PromiseLTS.

Set Implicit Arguments.
Remove Hints plus_n_O.

Definition init_threads (prog : Prog.t) : Threads.syntax :=
  IdentMap.mapi (fun tid (linstr : list Instr.t) => existT _ (thread_lts tid) linstr) prog.

Definition conf_step (PC PC' : Configuration.t) :=
  exists pe tid, Configuration.step pe tid PC PC'.

Definition final_memory_state (memory : Memory.t) (loc : location) : option value :=
  match Memory.get loc (Memory.max_ts loc memory) memory with
  | Some (_, msg) => Some msg.(Message.val)
  | None => None
  end.

Definition conf_init (prog : Prog.t) := Configuration.init (init_threads prog).

Definition promise_allows (prog : Prog.t) (final_memory : location -> value) :=
  exists PC,
    ⟪STEPS   : conf_step＊ (conf_init prog) PC⟫ /\
    ⟪FINAL   : Configuration.is_terminal PC⟫ /\
    ⟪OUTCOME : forall loc, final_memory_state PC.(Configuration.memory) loc =
                           Some (final_memory loc)⟫.
