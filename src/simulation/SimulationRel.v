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
From imm Require Import RMWinstrProps.

Require Import MaxValue.
Require Import ViewRel.
Require Import Event_imm_promise.
Require Import PromiseLTS.
Require Import SimState.
Require Import MemoryAux.
Require Import FtoCoherent.
Require Import ExtTraversalConfig.

From imm Require Import TraversalOrder.
From imm Require Import TLSCoherency.
From imm Require Import IordCoherency.
Require Import TlsEventSets.

Set Implicit Arguments.

Section SimRel.
Variable G : execution.
Variable WF : Wf G.
Variable sc : relation actid.
Variable PC : Configuration.t.
Variable TLS : trav_label -> Prop.
Variables f_to f_from : actid -> Time.t.

(* Notation "'acts'" := (acts G). *)
Notation "'co'" := (co G).
Notation "'coi'" := (coi G).
Notation "'sw'" := (sw G).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'rfe'" := (rfe G).
Notation "'rfi'" := (rfi G).
Notation "'rmw'" := (rmw G).
Notation "'lab'" := (lab G).
Notation "'msg_rel'" := (msg_rel G sc).
Notation "'urr'" := (urr G sc).

Notation "'E'" := (acts_set G).
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
Notation "'Acq/Rel'" := (is_ra lab).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

Notation "'W_ex'" := (W_ex G).
Notation "'W_ex_acq'" := (W_ex ∩₁ (fun a => is_true (is_xacq lab a))).

Notation "'C'" := (covered  TLS).
Notation "'I'" := (issued   TLS).
Notation "'S'" := (reserved TLS).
  
Definition sim_prom (thread : thread_id) promises :=
  forall l to from v rel
         (PROM  : Memory.get l to promises =
                  Some (from, Message.full v rel)),
  exists b,
    ⟪ ACTS : E b ⟫ /\
    ⟪ TID  : tid b = thread ⟫ /\
    ⟪ ISS  : I b ⟫ /\
    ⟪ NCOV : ~ C b ⟫ /\
    ⟪ LOC  : Loc_ l b ⟫ /\
    ⟪ FROM : f_from b = from ⟫ /\
    ⟪ TO   : f_to b = to ⟫ /\
    ⟪ HELPER : sim_mem_helper G sc f_to b from v (View.unwrap rel) ⟫.

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
       ⟪ PROM : Memory.get l (f_to b) (Local.promises local) =
                Some (f_from b, Message.reserve) ⟫).

Definition sim_mem (thread : thread_id) (local : Local.t) mem :=
    forall l b (ISSB: I b) (LOC: Loc_ l b) v (VAL: val lab b = Some v),
    exists rel_opt,
      let rel := (View.unwrap rel_opt) in
      ⟪ INMEM : Memory.get l (f_to b) mem =
                 Some (f_from b, Message.full v rel_opt) ⟫ /\

      ⟪ HELPER : sim_mem_helper G sc f_to b (f_from b) v rel ⟫ /\
      ⟪ REL_PLN_RLX : TimeMap.eq (View.pln rel) (View.rlx rel) ⟫ /\
      ⟪ MEM_CLOS : Memory.closed_timemap (View.rlx rel) mem ⟫ /\

      (⟪ TID  : tid b = thread ⟫ ->
       ⟪ NCOV : ~ C b ⟫ ->
       ⟪ PROM: Memory.get l (f_to b) (Local.promises local) =
          Some (f_from b, Message.full v rel_opt) ⟫ /\
       ⟪ REL_REPR :
         exists p_rel,
           ⟪ REL : rel_opt =
                   Some (View.join (View.join (TView.rel (Local.tview local) l)
                                              (View.unwrap p_rel))
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
    (⟪ FOR_SPLIT :
         ⦗ set_compl (codom_rel (<|S|> ;; (rfi ;; rmw)^* )) ⦘ ⨾ (immediate co) ⊆ sb ⟫ /\
     ⟪ RMW_BEF_S : W_ex ⊆₁ dom_rel (sb^? ⨾ ⦗ S ⦘) ⟫)
  end.

Definition simrel_common
           (smode : sim_mode) :=
  let memory := (Configuration.memory PC) in
  let threads := (Configuration.threads PC) in
  let sc_view := (Configuration.sc PC) in
  ⟪ ALLRLX  : E \₁ is_init ⊆₁ Rlx ⟫ /\
  ⟪ FRELACQ : E ∩₁ F ⊆₁ Acq/Rel ⟫ /\
  ⟪ TLSCOH  : tls_coherent G TLS ⟫ /\
  ⟪ IORDCOH : iord_coherent G sc TLS ⟫ /\
  ⟪ RCOH   : reserve_coherent G TLS ⟫ /\
  ⟪ RELCOV  : W ∩₁ Rel ∩₁ I ⊆₁ C ⟫ /\
  ⟪ RMWCOV  : forall r w (RMW : rmw r w), C r <-> C w ⟫ /\

  ⟪ THREAD : forall e (ACT : E e) (NINIT : ~ is_init e),
    exists langst, IdentMap.find (tid e) threads = Some langst ⟫ /\

  ⟪ PROM_IN_MEM :
     forall thread' langst local
            (TID : IdentMap.find thread' threads = Some (langst, local)),
           Memory.le (Local.promises local) memory ⟫ /\

  ⟪ FCOH: f_to_coherent G S f_to f_from ⟫ /\

  ⟪ SC_COV : smode = sim_certification -> E∩₁F∩₁Sc ⊆₁ C ⟫ /\ 
  ⟪ SC_REQ : smode = sim_normal -> 
         forall l,
         max_value f_to (S_tm G l C) (LocFun.find l sc_view) ⟫ /\
  
  (* TODO: To support RMWs (even FADDs) w/o ctrl dependency, we need to
           get rid of RMWREX.
   *)
  ⟪ RMWREX : dom_rel rmw ⊆₁ R_ex lab ⟫ /\ 

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
  let memory := (Configuration.memory PC) in
  let threads := (Configuration.threads PC) in
  exists state local,
    ⟪ TNNULL : thread <> tid_init ⟫ /\
    ⟪ GPC : wf_thread_state thread state ⟫ /\
    ⟪ RMWRES : rmw_is_rex_instrs (instrs state) ⟫ /\
    ⟪ LLH : IdentMap.find thread threads =
             Some (existT _ (thread_lts thread) state, local) ⟫ /\
    ⟪ PROM_DISJOINT :
        forall thread' langst' local'
               (TNEQ : thread <> thread')
               (TID' : IdentMap.find thread' threads = Some (langst', local')),
        forall loc to,
          Memory.get loc to local .(Local.promises) = None \/
          Memory.get loc to local'.(Local.promises) = None ⟫ /\

    ⟪ SIM_PROM  : sim_prom     thread (Local.promises local) ⟫ /\
    ⟪ SIM_RPROM : sim_res_prom thread (Local.promises local) ⟫ /\

    ⟪ SIM_MEM : sim_mem thread local memory ⟫ /\
    ⟪ SIM_RES_MEM : sim_res_mem thread local memory ⟫ /\
    ⟪ SIM_TVIEW : sim_tview G sc C f_to (Local.tview local) thread ⟫ /\
    ⟪ PLN_RLX_EQ : pln_rlx_eq (Local.tview local) ⟫ /\
    ⟪ MEM_CLOSE : memory_close (Local.tview local) memory ⟫ /\
    ⟪ STATE : @sim_state G smode C thread state ⟫.

Definition simrel_thread (thread : thread_id) (smode : sim_mode) :=
  ⟪ COMMON : simrel_common smode ⟫ /\
  ⟪ LOCAL  : simrel_thread_local thread smode ⟫.

Definition simrel :=
  ⟪ COMMON : simrel_common sim_normal ⟫ /\
  ⟪ THREADS : forall thread (TP : IdentMap.In thread (Configuration.threads PC)),
      simrel_thread_local thread sim_normal ⟫.

End SimRel.

Add Parametric Morphism : message_to_event with signature
    eq ==> (@set_subset trav_label) ==> eq ==> eq ==> eq ==> Basics.impl
       as message_to_event_mori.
Proof using.
  ins. red. intros HH; red.
  ins; apply HH in MSG; desf; auto.
  right; eexists; splits; eauto.
  eapply issued_mori; eauto. 
Qed.

(* TODO: move to IMM *)
Global Add Parametric Morphism : msg_rel with signature
       eq ==> (@same_relation actid) ==> eq ==>
          (@same_relation actid) as msg_rel_more. 
Proof using. ins. unfold msg_rel. rewrite H. basic_solver. Qed. 

Global Add Parametric Morphism : sim_prom with signature
       eq ==> (@same_relation actid) ==> (@set_equiv trav_label) ==> eq ==> eq ==> eq
          ==> (@set_subset Memory.t) as sim_prom_more_impl. 
Proof using.
  ins. unfold sim_prom. red. ins.
  specialize (H1 l to from v rel PROM). desc.
  eexists. splits; eauto.
  { eapply issued_more; [symmetry| ]; eauto. }
  { intros ?. apply NCOV. eapply covered_more; eauto. }
  red in HELPER. desc. 
  red. splits; eauto.
  red in SIMMSG. red. ins. specialize (SIMMSG l0).
  eapply max_value_more; eauto.
  eapply set_equiv_union; [| basic_solver].
  enough (msg_rel y y0 l0 ≡ msg_rel y x l0) by (generalize H1; basic_solver). 
  apply msg_rel_more; auto. by symmetry. 
Qed. 
  
Global Add Parametric Morphism : sim_prom with signature
       eq ==> (@same_relation actid) ==> (@set_equiv trav_label) ==> eq ==> eq ==> eq
          ==> (@set_equiv Memory.t) as sim_prom_more. 
Proof using. 
  ins. split; apply sim_prom_more_impl; auto; by symmetry. 
Qed. 

Lemma sim_res_prom_issued_reserved_subset G T1 T2 f_to f_from thread
      (ISS: issued T2 ⊆₁ issued T1)
      (RES: reserved T1 ⊆₁ reserved T2):
  sim_res_prom G T1 f_to f_from thread ⊆₁ sim_res_prom G T2 f_to f_from thread.
Proof using.  
  ins. unfold sim_res_prom. red. ins.
  specialize (H l to from RES0). desc. eexists. splits; eauto.
Qed. 

Global Add Parametric Morphism : sim_res_prom with signature
       eq ==> (@set_equiv trav_label) ==> eq ==> eq ==> eq
          ==> (@set_equiv Memory.t) as sim_res_prom_more. 
Proof using.
  ins. split; apply sim_res_prom_issued_reserved_subset; by rewrite H. 
Qed. 

Global Add Parametric Morphism : sim_mem with signature
       eq ==> (@same_relation actid) ==> (@set_equiv trav_label) ==>
       eq ==> eq ==> eq ==> eq ==>
       (@set_subset Memory.t) as sim_mem_more_impl.
Proof using. 
  ins. unfold sim_mem. red. ins.
  specialize (H1 l b). specialize_full H1; eauto.
  { eapply issued_more; eauto. }
  desc. eexists. splits; eauto.
  { red in HELPER. red. desc. splits; eauto.
    red in SIMMSG. red. desc. splits; eauto. 
    eapply max_value_more; eauto.
    eapply set_equiv_union; [| basic_solver].
    enough (msg_rel y y0 l0 ≡ msg_rel y x l0) as MM by (generalize MM; basic_solver). 
    apply msg_rel_more; auto. by symmetry. }
  ins. specialize_full H1; eauto.
  { intro. apply H3. symmetry in H0. eapply covered_more; eauto. }
  desc. splits; eauto. 
  exists p_rel. rewrite REL. splits; vauto. des.
  { left. split; auto. intro. apply NINRMW.
    eapply set_equiv_exp; [rewrite H0| ]; eauto. }
  right. exists p. splits; eauto.
  symmetry  in H0. eapply issued_more; eauto.    
Qed. 
 
Global Add Parametric Morphism : sim_mem with signature
       eq ==> (@same_relation actid) ==> (@set_equiv trav_label) ==>
       eq ==> eq ==> eq ==> eq ==>
       (@set_equiv Memory.t) as sim_mem_more.
Proof using. 
  ins. split; apply sim_mem_more_impl; auto; by symmetry. 
Qed. 

Global Add Parametric Morphism : sim_res_mem with signature
       eq ==> (@set_equiv trav_label) ==>
       eq ==> eq ==> eq ==> eq ==>
       (@set_subset Memory.t) as sim_res_mem_more_impl.
Proof using. 
  ins. unfold sim_res_mem. red. ins.
  specialize (H0 l b). specialize_full H0; eauto.
  { eapply reserved_more; eauto. }
  intro. apply NISSB. symmetry in H. eapply issued_more; eauto.
Qed.  

Global Add Parametric Morphism : sim_res_mem with signature
       eq ==> (@set_equiv trav_label) ==>
       eq ==> eq ==> eq ==> eq ==>
       (@set_equiv Memory.t) as sim_res_mem_more.
Proof using. 
  ins. split; apply sim_res_mem_more_impl; auto; by symmetry. 
Qed. 


