Require Import PArith Setoid.
From hahn Require Import Hahn.
Require Import PromisingLib.
From Promising2 Require Import TView View Time Event Cell Thread Memory Configuration Local.

From imm Require Import Events Execution.
From imm Require Import imm_s_hb.
From imm Require Import imm_s.
From imm Require Import CombRelations.
From imm Require Import ProgToExecution.
From imm Require Import ProgToExecutionProperties.

Require Import TraversalConfig.
Require Import MaxValue.
Require Import ViewRel.
Require Import Event_imm_promise.
Require Import PromiseLTS.
Require Import SimState.
Require Import MemoryAux.
Require Import FtoCoherent.
Require Import ExtTraversal.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section SimRel.
Variable G : execution.
Variable WF : Wf G.
Variable sc : relation actid.
Variable PC : Configuration.t.
Variable T : trav_config.
Variable S : actid -> Prop. (* A set of reserved events *)
Variables f_to f_from : actid -> Time.t.

Notation "'acts'" := G.(acts).
Notation "'co'" := G.(co).
Notation "'coi'" := G.(coi).
Notation "'sw'" := G.(sw).
Notation "'sb'" := G.(sb).
Notation "'rf'" := G.(rf).
Notation "'rfe'" := G.(rfe).
Notation "'rfi'" := G.(rfi).
Notation "'rmw'" := G.(rmw).
Notation "'lab'" := G.(lab).
Notation "'msg_rel'" := (msg_rel G sc).
Notation "'urr'" := (urr G sc).

Notation "'E'" := G.(acts_set).
Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'Loc_' l" := (fun x => loc lab x = Some l) (at level 1). (* , format "'Loc_'  l"). *)
Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'W_'" := (fun l => W ∩₁ Loc_ l).
(* Notation "'RW'" := (fun x => R x \/ W x). *)
Notation "'FR'" := (fun x => F x \/ R x).
Notation "'FW'" := (fun x => F x \/ W x).

Notation "'Pln'" := (fun a => is_true (is_only_pln lab a)).
Notation "'Rlx'" := (is_rlx lab).
Notation "'Rel'" := (is_rel lab).
Notation "'Acq'" := (is_acq lab).
Notation "'Acqrel'" := (is_acqrel lab).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

Notation "'W_ex'" := G.(W_ex).
Notation "'W_ex_acq'" := (W_ex ∩₁ (fun a => is_true (is_xacq lab a))).

Notation "'C'" := (covered T).
Notation "'I'" := (issued T).
  
Definition sim_prom (thread : thread_id) promises :=
  forall l to from v rel
         (PROM  : Memory.get l to promises =
                  Some (from, Message.full v rel)),
  exists b,
    ⟪ ACTS : E b ⟫ /\
    ⟪ TID  : tid b = thread ⟫ /\
    ⟪ ISS  : I b ⟫ /\
    ⟪ NCOV : ~ covered T b ⟫ /\
    ⟪ LOC  : Loc_ l b ⟫ /\
    ⟪ FROM : f_from b = from ⟫ /\
    ⟪ TO   : f_to b = to ⟫ /\
    ⟪ HELPER : sim_mem_helper G sc f_to b from v rel.(View.unwrap) ⟫.

Definition sim_res_prom (thread : thread_id) promises :=
  forall l to from (RES : Memory.get l to promises = Some (from, Message.reserve)),
  exists b,
    ⟪ ACTS  :   E b ⟫ /\
    ⟪ TID   : tid b = thread ⟫ /\
    ⟪ RES   :   S b ⟫ /\
    ⟪ NOISS : ~ I b ⟫ /\
    ⟪ LOC   : Loc_ l b ⟫ /\
    ⟪ FROM  : f_from b = from ⟫ /\
    ⟪ TO    : f_to b = to ⟫.

Definition sim_res_mem (thread : thread_id) (local : Local.t) mem :=
    forall l b (RESB: S b) (NISSB: ~ I b) (LOC: Loc_ l b),
      ⟪ INMEM : Memory.get l (f_to b) mem =
                 Some (f_from b, Message.reserve) ⟫ /\
      (⟪ TID  : tid b = thread ⟫ ->
       ⟪ PROM : Memory.get l (f_to b) local.(Local.promises) =
                Some (f_from b, Message.reserve) ⟫).

Definition sim_mem (thread : thread_id) (local : Local.t) mem :=
    forall l b (ISSB: I b) (LOC: Loc_ l b) v (VAL: val lab b = Some v),
    exists rel_opt,
      let rel := rel_opt.(View.unwrap) in
      ⟪ INMEM : Memory.get l (f_to b) mem =
                 Some (f_from b, Message.full v rel_opt) ⟫ /\

      ⟪ HELPER : sim_mem_helper G sc f_to b (f_from b) v rel ⟫ /\
      ⟪ REL_PLN_RLX : TimeMap.eq (View.pln rel) (View.rlx rel) ⟫ /\
      ⟪ MEM_CLOS : Memory.closed_timemap (View.rlx rel) mem ⟫ /\

      (⟪ TID  : tid b = thread ⟫ ->
       ⟪ NCOV : ~ covered T b ⟫ ->
       ⟪ PROM: Memory.get l (f_to b) local.(Local.promises) =
          Some (f_from b, Message.full v rel_opt) ⟫ /\
       ⟪ REL_REPR :
         exists p_rel,
           ⟪ REL : rel_opt =
                   Some (View.join (View.join (TView.rel (Local.tview local) l)
                                              p_rel.(View.unwrap))
                                   (View.singleton_ur l (f_to b))) ⟫ /\
           ((⟪ NINRMW : ~ codom_rel (⦗ I ⦘ ⨾ rf ⨾ rmw) b ⟫ /\
             ⟪ PREL : p_rel = None ⟫) \/
            (exists p,
                ⟪ ISSP  : I p ⟫ /\
                ⟪ INRMW : (rf ⨾ rmw) p b ⟫ /\
             exists p_v,
                ⟪ P_VAL : val lab p = Some p_v ⟫ /\
                ⟪ P_INMEM : Memory.get l (f_to p) mem =
                            Some (f_from p, Message.full p_v p_rel) ⟫))
       ⟫).

Definition message_to_event (memory : Memory.t) :=
  forall l to from v rel
         (MSG : Memory.get l to memory = Some (from, Message.full v rel)),
    (to = Time.bot /\ from = Time.bot) \/
    exists b,
    ⟪ ACTS : E b ⟫ /\
    ⟪ ISS  : I b ⟫ /\
    ⟪ LOC  : Loc_ l b ⟫ /\
    ⟪ FROM : f_from b = from ⟫ /\
    ⟪ TO   : f_to b = to ⟫.

Definition half_message_to_event (memory : Memory.t) :=
  forall l to from
         (MSG : Memory.get l to memory = Some (from, Message.reserve)),
  exists b,
    ⟪ ACTS  :   E b ⟫ /\
    ⟪ RES   :   S b ⟫ /\
    ⟪ NOISS : ~ I b ⟫ /\
    ⟪ LOC   : Loc_ l b ⟫ /\
    ⟪ FROM  : f_from b = from ⟫ /\
    ⟪ TO    : f_to   b = to ⟫.

Definition reserved_time smode memory :=
  match smode with
  | sim_normal =>
    (* During normal simulation *)
    (⟪ MEM   : message_to_event memory ⟫ /\
     ⟪ HMEM  : half_message_to_event memory ⟫ /\
     ⟪ TFRMW : forall x y, S x -> S y -> co x y ->
                           f_to x = f_from y -> (rf ⨾ rmw) x y ⟫)
  | sim_certification => 
    (* During certification *)
    (⟪ FOR_SPLIT : ⦗ set_compl (W_ex ∪₁ S) ⦘ ⨾ (immediate co) ⊆ sb ⟫ /\
     ⟪ RMW_BEF_S : W_ex ⊆₁ dom_rel (sb^? ;; <| S |>) ⟫)
  end.

Definition simrel_common
           (smode : sim_mode) :=
  let memory := PC.(Configuration.memory) in
  let threads := PC.(Configuration.threads) in
  let sc_view := PC.(Configuration.sc) in
  ⟪ ALLRLX: E \₁ is_init ⊆₁ Rlx ⟫ /\
  ⟪ TCCOH : etc_coherent G sc (mkETC T S) ⟫ /\
  ⟪ RELCOV : W ∩₁ Rel ∩₁ I ⊆₁ C ⟫ /\
  ⟪ RMWCOV : forall r w (RMW : rmw r w), covered T r <-> covered T w ⟫ /\

  ⟪ THREAD : forall e (ACT : E e) (NINIT : ~ is_init e),
    exists langst, IdentMap.find (tid e) threads = Some langst ⟫ /\

  ⟪ PROM_IN_MEM :
     forall thread' langst local
            (TID : IdentMap.find thread' threads = Some (langst, local)),
           Memory.le local.(Local.promises) memory ⟫ /\

  ⟪ FCOH: f_to_coherent G S f_to f_from ⟫ /\

  ⟪ SC_COV : smode = sim_certification -> E∩₁F∩₁Sc ⊆₁ covered T ⟫ /\ 
  ⟪ SC_REQ : smode = sim_normal -> 
         forall l,
         max_value f_to (S_tm G l (covered T)) (LocFun.find l sc_view) ⟫ /\

  ⟪ RESERVED_TIME: reserved_time smode memory ⟫ /\
                    
  ⟪ CLOSED_SC  : Memory.closed_timemap sc_view memory ⟫ /\
  ⟪ INHAB      : Memory.inhabited memory ⟫ /\
  ⟪ CLOSED_MEM : Memory.closed memory ⟫.

Definition pln_rlx_eq tview :=
  ⟪ EQ_CUR : TimeMap.eq (View.pln (TView.cur tview)) (View.rlx (TView.cur tview)) ⟫ /\
  ⟪ EQ_ACQ : TimeMap.eq (View.pln (TView.acq tview)) (View.rlx (TView.acq tview)) ⟫ /\
  ⟪ EQ_REL :
    forall l, TimeMap.eq (View.pln (TView.rel tview l)) (View.rlx (TView.rel tview l)) ⟫.

Definition simrel_thread_local (thread : thread_id) (smode : sim_mode) :=
  let memory := PC.(Configuration.memory) in
  let threads := PC.(Configuration.threads) in
  exists state local,
    ⟪ TNNULL : thread <> tid_init ⟫ /\
    ⟪ GPC : wf_thread_state thread state ⟫ /\
    ⟪ LLH : IdentMap.find thread threads =
             Some (existT _ (thread_lts thread) state, local) ⟫ /\
    ⟪ PROM_DISJOINT :
        forall thread' langst' local'
               (TNEQ : thread <> thread')
               (TID' : IdentMap.find thread' threads = Some (langst', local')),
        forall loc to,
          Memory.get loc to local .(Local.promises) = None \/
          Memory.get loc to local'.(Local.promises) = None ⟫ /\

    ⟪ SIM_PROM  : sim_prom     thread local.(Local.promises) ⟫ /\
    ⟪ SIM_RPROM : sim_res_prom thread local.(Local.promises) ⟫ /\

    ⟪ SIM_MEM : sim_mem thread local memory ⟫ /\
    ⟪ SIM_RES_MEM : sim_res_mem thread local memory ⟫ /\
    ⟪ SIM_TVIEW : sim_tview G sc (covered T) f_to local.(Local.tview) thread ⟫ /\
    ⟪ PLN_RLX_EQ : pln_rlx_eq local.(Local.tview) ⟫ /\
    ⟪ MEM_CLOSE : memory_close local.(Local.tview) memory ⟫ /\
    ⟪ STATE : @sim_state G smode (covered T) thread state ⟫.

Definition simrel_thread (thread : thread_id) (smode : sim_mode) :=
  ⟪ COMMON : simrel_common smode ⟫ /\
  ⟪ LOCAL  : simrel_thread_local thread smode ⟫.

Definition simrel :=
  ⟪ COMMON : simrel_common sim_normal ⟫ /\
  ⟪ THREADS : forall thread (TP : IdentMap.In thread PC.(Configuration.threads)),
      simrel_thread_local thread sim_normal ⟫.

End SimRel.
