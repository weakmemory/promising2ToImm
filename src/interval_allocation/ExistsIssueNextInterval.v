Require Import Setoid PArith.
From hahn Require Import Hahn.
Require Import PromisingLib.
From Promising2 Require Import TView View Time Event Cell Thread Memory Configuration Local.

From imm Require Import Events.
From imm Require Import Execution.
From imm Require Import Execution_eco.
From imm Require Import imm_s_hb.
From imm Require Import imm_s.
From imm Require Import imm_bob imm_s_ppo.
From imm Require Import CombRelations.
From imm Require Import AuxDef.

Require Import AuxRel2.
Require Import TraversalConfig.
Require Import SimulationRel.
Require Import SimState.
Require Import MemoryAux.
Require Import MaxValue.
Require Import ViewRel.
Require Import Event_imm_promise.
Require Import ExtTraversalConfig.
Require Import ExtTraversal.
Require Import ExtTraversalProperties.
Require Import FtoCoherent.
Require Import SimulationRelProperties.
Require Import ImmProperties.
Require Import IntervalHelper.

Set Implicit Arguments.

Section Aux.

Variable G : execution.
Variable WF : Wf G.
Variable sc : relation actid.

Notation "'acts'" := G.(acts).
Notation "'co'" := G.(co).
Notation "'sw'" := G.(sw).
Notation "'hb'" := G.(hb).
Notation "'sb'" := G.(sb).
Notation "'rf'" := G.(rf).
Notation "'rfi'" := G.(rfi).
Notation "'rfe'" := G.(rfe).
Notation "'rmw'" := G.(rmw).
Notation "'lab'" := G.(lab).
Notation "'msg_rel'" := (msg_rel G sc).
Notation "'urr'" := (urr G sc).
Notation "'release'" := G.(release).

Notation "'E'" := G.(acts_set).
Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'Loc_' l" := (fun x => loc lab x = Some l) (at level 1).
Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'W_'" := (fun l => W ∩₁ Loc_ l).
Notation "'FR'" := (fun x => F x \/ R x).
Notation "'FW'" := (fun x => F x \/ W x).

Notation "'W_ex'" := (W_ex G).
Notation "'W_ex_acq'" := (W_ex ∩₁ (fun a => is_true (is_xacq lab a))).

Notation "'Pln'" := (fun a => is_true (is_only_pln lab a)).
Notation "'Rlx'" := (is_rlx lab).
Notation "'Rel'" := (is_rel lab).
Notation "'Acq'" := (is_acq lab).
Notation "'Acqrel'" := (is_acqrel lab).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

Hypothesis IMMCON : imm_consistent G sc.

Variable T : trav_config.
Variable S : actid -> Prop.
Hypothesis ETCCOH : etc_coherent G sc (mkETC T S).

Hypothesis RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T.

Variable f_to f_from : actid -> Time.t.
Hypothesis FCOH : f_to_coherent G S f_to f_from.

Variable thread : thread_id.
Variable PC : Configuration.t.
Variable local : Local.t.

Hypothesis SIM_TVIEW : sim_tview G sc (covered T) f_to local.(Local.tview) thread.
Hypothesis INHAB : Memory.inhabited PC.(Configuration.memory).
Hypothesis PLN_RLX_EQ : pln_rlx_eq local.(Local.tview).
Hypothesis MEM_CLOSE : memory_close local.(Local.tview) PC.(Configuration.memory).

Lemma exists_time_interval_for_issue_next w wnext locw valw langst smode
      (ISSUABLE : issuable G sc T w)
      (WNISS : ~ issued T w)
      (NWEX : ~ W_ex w)
      (WNEXT : dom_sb_S_rfrmw G (mkETC T S) rfi (eq w) wnext)
      (LOC : loc lab w = Some locw)
      (VAL : val lab w = Some valw)
      (WTID : thread = tid w)
      (PROM_IN_MEM :
         forall thread' langst local
                (TID : IdentMap.find thread' PC.(Configuration.threads) =
                       Some (langst, local)),
           Memory.le local.(Local.promises) PC.(Configuration.memory))
      (RESERVED_TIME:
         reserved_time G T S f_to f_from smode PC.(Configuration.memory))
      (SIM_RES_MEM :
         sim_res_mem G T S f_to f_from (tid w) local (Configuration.memory PC))
      (SIM_MEM : sim_mem G sc T f_to f_from
                         (tid w) local PC.(Configuration.memory))
      (TID : IdentMap.find (tid w) PC.(Configuration.threads) = Some (langst, local))
      (WEXRES : smode = sim_certification ->
                dom_rel (<|W_ex|> ;; sb ∩ same_loc lab ;; <|issued T|>) ⊆₁ S) :
  let promises := local.(Local.promises) in
  let memory   := PC.(Configuration.memory) in
  let T'       := mkTC (covered T) (issued T ∪₁ eq w) in
  let S'       := S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G (mkETC T S) rfi (eq w) in
  exists p_rel,
    rfrmw_prev_rel G sc T f_to f_from PC.(Configuration.memory) w locw p_rel /\
    ⟪ FOR_ISSUE :
         exists f_to' f_from',
           let rel'' :=
               if is_rel lab w
               then (TView.cur (Local.tview local))
               else (TView.rel (Local.tview local) locw)
           in
           let rel' := (View.join (View.join rel'' p_rel.(View.unwrap))
                                  (View.singleton_ur locw (f_to' w))) in
           ⟪ RELWFEQ : View.pln rel' = View.rlx rel' ⟫ /\
           ⟪ REL_VIEW_LT : Time.lt (View.rlx rel'' locw) (f_to' w) ⟫ /\
           ⟪ REL_VIEW_LE : Time.le (View.rlx rel'  locw) (f_to' w) ⟫ /\

           ⟪ REQ_TO : forall e (SE : S e), f_to' e = f_to e ⟫ /\
           ⟪ REQ_FROM : forall e (SE : S e), f_from' e = f_from e ⟫ /\
           ⟪ ISSEQ_TO   : forall e (ISS: issued T e), f_to' e = f_to e ⟫ /\
           ⟪ ISSEQ_FROM : forall e (ISS: issued T e), f_from' e = f_from e ⟫ /\
           ⟪ FTOWNBOT     : f_to' w     <> Time.bot ⟫ /\
           ⟪ FTOWNEXTNBOT : f_to' wnext <> Time.bot ⟫ /\
           ⟪ FWWNEXTEQ    : f_from' wnext = f_to' w ⟫ /\
           << FTONEXTNEQ : f_to' w <> f_to' wnext >> /\

           ⟪ DISJOINT : forall to from msg
               (INMEM : Memory.get locw to (Configuration.memory PC) = Some (from, msg)),
               Interval.disjoint (f_from' w, f_to' w) (from, to) ⟫ /\

           ⟪ DISJOINT' : forall to from msg
               (INMEM : Memory.get locw to (Configuration.memory PC) = Some (from, msg)),
               Interval.disjoint (f_from' wnext, f_to' wnext) (from, to) ⟫ /\

           exists promises_add memory_add promises_rel promises' memory',
             ⟪ PADD :
                 Memory.add local.(Local.promises) locw (f_from' w) (f_to' w)
                            (Message.full valw (Some rel')) promises_add ⟫ /\
             ⟪ MADD :
                 Memory.add memory locw (f_from' w) (f_to' w)
                            (Message.full valw (Some rel')) memory_add ⟫ /\
             ⟪ PEQ :
                 if Rel w
                 then Memory.remove promises_add locw (f_from' w) (f_to' w)
                                    (Message.full valw (Some rel')) promises_rel
                 else promises_rel = promises_add ⟫ /\

             ⟪ PADD2 :
                 Memory.add promises_rel locw (f_from' wnext) (f_to' wnext)
                            Message.reserve promises' ⟫ /\
             ⟪ MADD2 :
                 Memory.add memory_add locw (f_from' wnext) (f_to' wnext)
                            Message.reserve memory' ⟫ /\

             ⟪ INHAB : Memory.inhabited memory' ⟫ /\
             ⟪ RELMCLOS : Memory.closed_timemap (View.rlx rel') memory_add ⟫ /\
             ⟪ RELVCLOS : Memory.closed_view rel' memory_add ⟫ /\

             ⟪ FCOH : f_to_coherent G S' f_to' f_from' ⟫ /\

             ⟪ HELPER :
                 sim_mem_helper
                   G sc f_to' w (f_from' w) valw
                   (View.join (View.join (if is_rel lab w
                                          then (TView.cur (Local.tview local))
                                          else (TView.rel (Local.tview local) locw))
                                         p_rel.(View.unwrap))
                              (View.singleton_ur locw (f_to' w))) ⟫ /\

             ⟪ RESERVED_TIME :
                 reserved_time G T' S' f_to' f_from' smode memory' ⟫ ⟫.

         (* TODO: To support FADDs w/ ctrl dependency, we need to
                  use splitting here. For that, we might want to parametrize
                  traversal by simmode.
          *)
(* \/ *)
(*      ⟪ FOR_SPLIT : *)
(*          ⟪ SMODE : smode = sim_certification ⟫ /\ *)
(*          exists ws wsmsg f_to' f_from', *)
(*            let rel'' := *)
(*                if is_rel lab w *)
(*                then (TView.cur (Local.tview local)) *)
(*                else (TView.rel (Local.tview local) locw) *)
(*            in *)
(*            let rel' := (View.join (View.join rel'' p_rel.(View.unwrap)) *)
(*                                   (View.singleton_ur locw (f_to' w))) in *)
(*            ⟪ WSISS  : S ws ⟫ /\ *)
(*            ⟪ WSNCOV : ~ covered T ws ⟫ /\ *)

(*            ⟪ SBWW : sb w ws ⟫ /\ *)
(*            ⟪ SAME_LOC : Loc_ locw ws ⟫ /\ *)
(*            ⟪ COWW : co w ws ⟫ /\ *)

(*            ⟪ FEQ1 : f_to' wnext = f_from' ws ⟫ /\ *)
(*            ⟪ FEQ2 : f_from' w = f_from ws ⟫ /\ *)

(*            ⟪ WSPROM : Memory.get locw (f_to ws) (Local.promises local) = *)
(*                       Some (f_from ws, wsmsg)⟫ /\ *)
(*            ⟪ WSMEM : Memory.get locw (f_to ws) memory = *)
(*                      Some (f_from ws, wsmsg)⟫ /\ *)

(*            ⟪ RELWFEQ : View.pln rel' = View.rlx rel' ⟫ /\ *)
(*            ⟪ REL_VIEW_LT : Time.lt (View.rlx rel'' locw) (f_to' w) ⟫ /\ *)
(*            ⟪ REL_VIEW_LE : Time.le (View.rlx rel'  locw) (f_to' w) ⟫ /\ *)
(*            ⟪ FCOH : f_to_coherent G S' f_to' f_from' ⟫ /\ *)

(*            exists promises_split memory_split promises' memory', *)
(*              ⟪ PSPLIT : *)
(*                  Memory.split (Local.promises local) *)
(*                               locw (f_from' w) (f_to' wnext) (f_to' ws) *)
(*                               (Message.full valw (Some rel')) wsmsg *)
(*                               promises_split ⟫ /\ *)
(*              ⟪ MSPLIT : *)
(*                  Memory.split memory locw (f_from' w) (f_to' wnext) (f_to' ws) *)
(*                               (Message.full valw (Some rel')) wsmsg *)
(*                               memory_split ⟫ /\ *)

(*              ⟪ PADD : *)
(*                  Memory.split promises'  *)
(*                               locw (f_from' w) (f_to' w) (f_to' wnext) *)
(*                               (Message.full valw (Some rel')) *)
(*                               Message.reserve  *)
(*                               promises' ⟫ /\ *)
(*              ⟪ MADD : *)
(*                  Memory.split memory_split *)
(*                               locw (f_from' w) (f_to' w) (f_to' wnext) *)
(*                               (Message.full valw (Some rel')) *)
(*                               Message.reserve  *)
(*                               memory' ⟫ /\ *)

(*              ⟪ INHAB : Memory.inhabited memory' ⟫ /\ *)
(*              ⟪ RELMCLOS : Memory.closed_timemap (View.rlx rel') memory' ⟫ /\ *)
(*              ⟪ RELVCLOS : Memory.closed_view rel' memory' ⟫ /\ *)


(*              ⟪ HELPER : *)
(*                  sim_mem_helper *)
(*                    G sc f_to' w (f_from' w) valw *)
(*                    (View.join (View.join (if is_rel lab w *)
(*                                           then (TView.cur (Local.tview local)) *)
(*                                           else (TView.rel (Local.tview local) locw)) *)
(*                                          p_rel.(View.unwrap)) *)
(*                               (View.singleton_ur locw (f_to' w))) ⟫ /\ *)

(*              ⟪ RESERVED_TIME : *)
(*                  reserved_time G T' S' f_to' f_from' smode memory' ⟫ ⟫). *)
Proof using WF IMMCON ETCCOH RELCOV FCOH SIM_TVIEW PLN_RLX_EQ INHAB MEM_CLOSE.
  assert (sc_per_loc G) as SPL. 
  { apply coherence_sc_per_loc. apply IMMCON. }
  assert (rmw_atomicity G) as ATOM by apply IMMCON.
  assert (tc_coherent G sc T) as TCCOH by apply ETCCOH.
  assert (S ⊆₁ E ∩₁ W) as SEW.
  { apply set_subset_inter_r. split; [by apply ETCCOH|].
    apply (reservedW WF ETCCOH). }
  assert (S ⊆₁ E /\ S ⊆₁ W) as [SE SW] by (split; rewrite SEW; clear; basic_solver).

  assert (issued T ⊆₁ S) as IE by apply ETCCOH.
  assert (W w) as WW.
  { eapply issuableW; eauto. }
  assert (E w) as EW.
  { eapply issuableE; eauto. }
  assert (~ covered T w) as WNCOV.
  { intros HH. apply WNISS. eapply w_covered_issued; eauto. by split. }
  assert (~ S w) as NSW.
  { intros HH. apply NWEX. eapply etc_S_I_in_W_ex; eauto. by split. }
  assert (~ is_init w) as WNINIT.
  { intros HH. apply WNCOV. eapply init_covered; eauto. by split. }

  forward (eapply dom_sb_S_rfrmw_single_props with (w:=w) (wnext:=wnext)); eauto.
  intros HH. desc.
  assert (w <> wnext) as WNEXTNEQ.
  { intros HH. subst. eapply WF.(co_irr); eauto. }

  assert ((E ∩₁ W ∩₁ Loc_ locw) w) as WEW.
  { split; [split|]; auto. }
  assert ((E ∩₁ W ∩₁ Loc_ locw) wnext) as WEWNEXT.
  { split; [split|]; auto. }

  destruct langst as [lang state].

  edestruct exists_wprev_rel with (w:=w) as [p_rel PRELSPEC]; eauto.
  set (rel'' :=
         if Rel w
         then TView.cur (Local.tview local)
         else TView.rel (Local.tview local) locw).
  exists p_rel. split; auto.

  assert (p_rel = None) as PRELNN.
  { desc.
    red in PRELSPEC. desc.
    destruct PRELSPEC0; desc; auto.
    exfalso.
    generalize INRMW NWEX. clear. unfold Execution.W_ex. basic_solver. }
  assert (Message.wf (Message.full valw p_rel)) as WFMSG.
  { subst. constructor. apply View.opt_wf_none. }

  assert (View.pln rel'' = View.rlx rel'') as RELPLN''.
  { subst rel''. destruct (Rel w); apply PLN_RLX_EQ. }

  edestruct co_prev_to_imm_co_prev with (w:=w) as [wprev]; eauto. desc.

  assert (wprev <> wnext) as NEQCONEXTP by (by intros HH; subst).
  assert (co wprev wnext) as WNEXTCOPREV.
  { eapply WF.(co_trans) with (y:=w); eauto. }
  assert (immediate (⦗S⦘ ⨾ co) wprev wnext) as PREVNEXTCOIMM.
  (* TODO: make a lemma. *)
  { split.
    { apply seq_eqv_l. split; auto. }
    ins.
    destruct_seq_l R1 as AA. destruct_seq_l R2 as BB.
    eapply PCOIMM with (c:=c); apply seq_eqv_l; split; auto.
    edestruct WF.(wf_co_total) with (a:=c) (b:=w) as [|HH]; eauto.
    { apply (dom_l WF.(wf_coE)) in R2. destruct_seq_l R2 as CE.
      apply (dom_l WF.(wf_coD)) in R2. destruct_seq_l R2 as CD.
      split; [split|]; auto. rewrite <- WNEXTLOC. by apply WF.(wf_col). }
    { by intros HH; subst. }
    exfalso. eapply rf_rmw_in_coimm; eauto. }

  set (S':=S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G (mkETC T S) rfi (eq w)).
  assert (S ⊆₁ S') as SINS by (unfold S'; eauto with hahn).
  assert (S' ⊆₁ E ∩₁ W) as SEW'.
  { subst S'. rewrite SEW at 1. unionL; eauto with hahn.
    { unfolder. ins. desf. }
    intros x HH.
    assert (x = wnext); subst.
    2: by split.
    eapply dom_sb_S_rfrmwf; eauto. }

  destruct (classic (exists wconext, (co ⨾ ⦗ S ⦘) w wconext)) as [WCONEXT|WNONEXT].
  { edestruct co_next_to_imm_co_next with (w:=w) as [wconext]; eauto. clear WCONEXT. desc.
    assert ((co ⨾ ⦗set_compl S⦘ ⨾ co) wprev wconext) as CONS.
    { exists w. split; auto. apply seq_eqv_l. by split. }
    assert (co wprev wconext) as COPN.
    { eapply WF.(co_trans) with (y:=w); eauto. }

    assert (immediate (⦗S⦘ ⨾ co ⨾ ⦗S⦘) wprev wconext) as COSIMM.
    { apply P_co_nP_co_P_imm; auto.
      exists w. split; auto. apply seq_eqv_l. by split. }

    assert (~ (rf ⨾ rmw) w wconext) as NRFRMWCONEXT.
    { intros AA. apply NSW. eapply (dom_rf_rmw_S WF ETCCOH).
      exists wconext. apply seqA. apply seq_eqv_r. by split. }

    assert (Time.le (f_to wprev) (f_from wconext)) as FFLE by (by apply FCOH).
    
    assert (wconext <> wnext) as NEQCONEXT by (by intros HH; subst).
    assert (co wnext wconext) as WNEXTCONEXT.
    { edestruct WF.(wf_co_total) with (a:=wnext) (b:=wconext) as [|HH]; eauto.
      { split; [split|]; eauto. }
      exfalso. eapply rf_rmw_in_coimm; eauto. }

    assert (NEXTCOIMM : immediate (co ⨾ ⦗S⦘) wnext wconext).
    (* TODO: make a lemma. *)
    { split.
      { apply seq_eqv_r. by split. }
      ins.
      destruct_seq_r R1 as AA. destruct_seq_r R2 as BB.
      eapply NCOIMM with (c:=c); apply seq_eqv_r; split; auto.
      eapply WF.(co_trans) with (y:=wnext); auto. }

    assert (issued T wconext /\ ~ W_ex wconext) as [WSISS NWEXCONEXT].
    { eapply codom_nS_imm_co_S_in_I with (T:=mkETC T S); eauto.
      simpls. exists w. apply seq_eqv_l. by split. }

    destruct smode eqn:SMODE. (* [left|right]. *)
    2: { (* TODO: Currently, it's impossible to split wconextmsg in the needed way. *)
         (* TODO: To support FADDs w/ ctrl dependency, we need to
                  use splitting here. For that, we might want to parametrize
                  traversal by simmode.
          *)
         cdes RESERVED_TIME.

         assert (sb wnext wconext) as SBNEXTNEXT.
         { eapply nS_imm_co_in_sb with (S:=S); eauto. }

         exfalso. apply NSWNEXT. apply WEXRES; auto.
         exists wconext. apply seq_eqv_lr. splits; auto.
         { red. generalize RFRMWNEXT. clear. basic_solver. }
         split; auto. red. by rewrite WNEXTLOC. }

         (* splits; eauto. *)
         (* assert (set_compl (W_ex ∪₁ S) w) as WNRMWS. *)
         (* { intros [|]; eauto. } *)

          (* assert (sb w wconext) as SBNEXT. *)
          (* { eapply nS_imm_co_in_sb with (S:=S); eauto. } *)

         (* assert (w <> wconext /\ wnext <> wconext) as [WCONEXTNEQ WNEXTCONEQ]. *)
         (* { by split; intros HH; subst. } *)

         (* assert (tid wconext = tid w) as TIDNEXT. *)
         (* { apply sb_tid_init in SBNEXT. destruct SBNEXT as [H|H]; desf. } *)
         (* assert (~ covered T wconext) as NCOVNEXT. *)
         (* { intros H; apply TCCOH in H. *)
         (*   apply WNCOV. apply H. *)
         (*   eexists. apply seq_eqv_r; split; eauto. } *)

         (* edestruct reserved_to_message with (l:=locw) (b:=wconext) *)
         (*   as [wconextmsg [WCONEXTMEM WCONEXTPROM']]; eauto. *)
         (* assert (Memory.get locw (f_to wconext) (Local.promises local) = *)
         (*         Some (f_from wconext, wconextmsg)) as WCONEXTPROM. *)
         (* { apply WCONEXTPROM'; auto. } *)

         (* assert (~ is_init wconext) as NINITWCONEXT. *)
         (* { apply no_co_to_init in CONEXT; auto. *)
         (*   apply seq_eqv_r in CONEXT. desf. } *)

         (* set (nn_to := Time.middle (f_from wconext) (f_to wconext)). *)
         (* set ( n_to := Time.middle (f_from wconext) nn_to). *)
         (* assert (Time.lt n_to nn_to) as LTNNTO. *)
         (* { unfold n_to, nn_to. do 2 apply Time.middle_spec. by apply FCOH. } *)

         (* assert (Time.lt (f_from wconext) (f_to wconext)) as LLWCONEXT. *)
         (* { by apply FCOH. } *)
         (* assert (Time.lt (f_from wconext) n_to) as LLFROMN. *)
         (* { unfold n_to, nn_to. by do 2 apply DenseOrder.middle_spec. } *)
         (* assert (Time.lt nn_to (f_to wconext)) as LLTONN. *)
         (* { unfold nn_to. by apply DenseOrder.middle_spec. } *)
         (* assert (Time.lt n_to (f_to wconext)) as LLTON. *)
         (* { etransitivity; [|by apply LLTONN]. *)
         (*   unfold n_to, nn_to. by do 2 apply DenseOrder.middle_spec. } *)

         (* assert (Time.lt (f_to wprev) n_to) as LTPREVN. *)
         (* { unfold n_to. *)
         (*   apply TimeFacts.le_lt_lt with (b:=f_from wconext). *)
         (*   { by apply FCOH. } *)
         (*   apply Time.middle_spec. etransitivity; eauto. } *)
         (* assert (Time.le (f_to wprev) n_to) as LEPREVN. *)
         (* { apply Time.le_lteq; eauto. } *)

         (* set (f_to'   := upd (upd f_to w n_to) wnext nn_to). *)
         (* set (f_from' := upd (upd (upd f_from w (f_from wconext)) wnext n_to) wconext nn_to). *)

         (* set (rel' := View.join *)
         (*                (View.join rel'' p_rel.(View.unwrap)) *)
         (*                (View.singleton_ur locw (f_to' w))). *)
         (* assert (View.opt_wf (Some rel')) as RELWF. *)
         (* { apply View.opt_wf_some. *)
         (*   apply View.join_wf. *)
         (*   2: by apply View.singleton_ur_wf. *)
         (*   constructor. *)
         (*   unfold View.join; simpls. *)
         (*   rewrite PRELNN. simpls. *)
         (*   rewrite RELPLN''. reflexivity. } *)

         (* assert (Message.wf (Message.full valw (Some rel'))) as MSGWF. *)
         (* { by constructor. } *)

         (* set (S':=S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G (mkETC T S) rfi (eq w)). *)
         (* assert (f_to_coherent G S' f_to' f_from') as FCOH_NEW. *)
         (* (* TODO: make a lemma. *) *)
         (* { unfold S', f_to', f_from'. *)
         (*   red; splits; ins. *)
         (*   { rewrite !updo. *)
         (*     { by apply FCOH. } *)
         (*     all: intros HH; subst; by destruct H. } *)
         (*   { do 3 (rewrite updo; [|by intros HH; subst; destruct H]). *)
         (*       by apply FCOH. } *)
         (*   { destruct H as [[H|]|H]; subst. *)
         (*     3: { assert (x = wnext); subst. *)
         (*          { eapply dom_sb_S_rfrmwf; eauto. } *)
         (*          rewrite upds. *)
         (*          rewrite updo; auto; rewrite upds; auto. } *)
         (*     2: by do 3 (rewrite updo; auto; try rewrite upds). *)
         (*     rewrite updo with (a:=wnext); [|by intros HH; subst]. *)
         (*     rewrite updo with (a:=w); [|by intros HH; subst]. *)
         (*     destruct (classic (wconext = x)) as [|NEQ]; subst; *)
         (*       [by rewrite upds | rewrite updo; auto]. *)
         (*     do 2 (rewrite updo; auto; try by intros HH; subst). *)
         (*       by apply FCOH. } *)
         (*   { assert (x <> y) as HXY. *)
         (*     { by intros HH; subst; apply WF.(co_irr) in H1. } *)
         (*     destruct H as [[H|]|H]; destruct H0 as [[H0|]|H0]; subst. *)
         (*     all: try (rewrite !upds). *)
         (*     all: try repeat (rewrite updo; [|by intros HH; subst]). *)
         (*     all: try (rewrite !upds). *)
         (*     all: try by *)
         (*         match goal with  *)
         (*         | H : ?X <> ?X |- _ => exfalso; apply H *)
         (*         end. *)
         (*     all: try (assert (x = wnext) by (eapply dom_sb_S_rfrmwf; eauto); subst). *)
         (*     all: try (assert (y = wnext) by (eapply dom_sb_S_rfrmwf; eauto); subst). *)
         (*     all: try rewrite !upds. *)
         (*     all: try (rewrite updo; [|done]). *)
         (*     all: try rewrite !upds. *)
         (*     all: try (rewrite updo; [|done]). *)
         (*     all: try rewrite !upds. *)
         (*     all: try reflexivity. *)
         (*     all: try by (Time.le_lteq; eauto). *)
         (*     all: try by *)
         (*         match goal with  *)
         (*         | H : co ?X ?X |- _ => exfalso; eapply WF.(co_irr); eauto *)
         (*         end. *)
         (*     { destruct (classic (y = wconext)) as [|NEQ]; subst; *)
         (*         [rewrite upds | rewrite updo; auto]. *)
         (*       2: { do 2 (rewrite updo; [|by intros HH; subst]). *)
         (*              by apply FCOH. } *)
         (*       apply Time.le_lteq; left. *)
         (*       transitivity n_to; auto. *)
         (*       unfold n_to. *)
         (*       eapply TimeFacts.le_lt_lt with (b:=f_from wconext); auto. *)
         (*         by apply FCOH. } *)
         (*     { apply FCOH; auto. eapply WF.(co_trans); eauto. } *)
         (*     { assert (co^? x wprev) as [|COX]; subst; auto. *)
         (*       { eapply P_co_immediate_P_co_transp_in_co_cr with (P:=S); auto. *)
         (*         exists wnext. split; auto.  *)
         (*         apply seq_eqv_l. by split. } *)
         (*       transitivity (f_to wprev); auto. *)
         (*       apply Time.le_lteq; left. eapply f_to_co_mon; eauto. } *)
         (*     { assert (co^? wconext y) as [|COX]; subst; eauto. *)
         (*       { eapply immediate_co_P_transp_co_P_in_co_cr with (P:=S); auto. *)
         (*         exists x. split; auto.  *)
         (*         apply seq_eqv_r. by split. } *)
         (*       { rewrite upds. apply Time.le_lteq; eauto. } *)
         (*       assert (y <> wconext). *)
         (*       { intros HH. subst. eapply WF.(co_irr). eauto. } *)
         (*       repeat (rewrite updo; [|by intros HH; subst]). *)
         (*       transitivity (f_to wconext); auto. *)
         (*       2: by apply FCOH. *)
         (*       apply Time.le_lteq; eauto. } *)
         (*     { assert (co^? wconext y) as [|COX]; subst; eauto. *)
         (*       { eapply immediate_co_P_transp_co_P_in_co_cr with (P:=S); auto. *)
         (*         exists wnext. split; auto.  *)
         (*         apply seq_eqv_r. by split. } *)
         (*       { rewrite upds. apply Time.le_lteq; eauto. } *)
         (*       assert (y <> wconext). *)
         (*       { intros HH. subst. eapply WF.(co_irr). eauto. } *)
         (*       repeat (rewrite updo; [|by intros HH; subst]). *)
         (*       transitivity (f_to wconext); auto. *)
         (*       2: by apply FCOH. *)
         (*       apply Time.le_lteq; eauto. } *)
         (*     exfalso. eapply WF.(co_irr). eapply WF.(co_trans); eauto. } *)
         (*   destruct H0 as [[H0|]|H0]; subst. *)
         (*   3: { assert (y = wnext) by (eapply dom_sb_S_rfrmwf; eauto); subst. *)
         (*        assert (x = w) by (eapply wf_rfrmwf; eauto); subst. *)
         (*          by do 2 (rewrite updo; auto; rewrite upds). } *)
         (*   2: { exfalso. apply NWEX. red. generalize H1. clear. basic_solver. } *)
         (*   destruct H as [[H|]|H]; subst. *)
         (*   3: { assert (x = wnext) by (eapply dom_sb_S_rfrmwf; eauto); subst. *)
         (*        exfalso. apply NSWNEXT. eapply dom_rf_rmw_S with (T:=mkETC T S); eauto. *)
         (*        generalize H0 H1. clear. basic_solver 10. } *)
         (*   2: { exfalso. apply NSW. eapply dom_rf_rmw_S with (T:=mkETC T S); eauto. *)
         (*        generalize H0 H1. clear. basic_solver 10. } *)
         (*   do 2 (rewrite updo; [|by intros HH; subst]). *)
         (*   destruct (classic (y = wconext)) as [|NEQ]; subst. *)
         (*   2: { rewrite updo; auto. *)
         (*        repeat (rewrite updo; [|by intros HH; subst]). by apply FCOH. } *)
         (*   exfalso.  *)
         (*   assert (co x wconext) as AA by (by apply rf_rmw_in_co). *)
         (*   apply NCOIMM with (c:=x); apply seq_eqv_r; split; auto. *)
         (*   edestruct WF.(wf_co_total) with (a:=w) (b:=x) as [|HH]; eauto. *)
         (*   { apply (dom_l WF.(wf_coE)) in AA. destruct_seq_l AA as CE. *)
         (*     apply (dom_l WF.(wf_coD)) in AA. destruct_seq_l AA as CD. *)
         (*     split; [split|]; auto. rewrite <- LOCNEXT. by apply WF.(wf_col). } *)
         (*   { by intros HH; subst. } *)
         (*   exfalso. eapply rf_rmw_in_coimm; eauto. } *)

         (* assert (Time.lt (f_from' w) (f_to' wnext)) as LTFWTWNEXT. *)
         (* { unfold f_from', f_to'. *)
         (*   rewrite upds. do 2 (rewrite updo; auto). rewrite upds. *)
         (*   etransitivity; eauto. } *)
         (* assert (Time.lt (f_to' wnext) (f_to' wconext)) as LTFWNEXTFWCONEXT. *)
         (* { unfold f_from', f_to'. *)
         (*   rewrite !upds. do 2 (rewrite updo; auto). } *)

         (* edestruct (@Memory.split_exists (Local.promises local) locw *)
         (*                                 (f_from' w) (f_to' wnext) (f_to' wconext) *)
         (*                                 (Message.full valw (Some rel')) wconextmsg) *)
         (*   as [promises_split PSPLIT]; eauto. *)
         (* { unfold f_to', f_from'. repeat (rewrite updo; [|done]). by rewrite upds. } *)

         (* edestruct (@Memory.split_exists (Configuration.memory PC) locw  *)
         (*                                 (f_from' w) (f_to' wnext) (f_to' wconext) *)
         (*                                 (Message.full valw (Some rel')) wconextmsg) *)
         (*   as [memory_split MSPLIT]; eauto. *)
         (* { unfold f_to', f_from'. repeat (rewrite updo; [|done]). by rewrite upds. } *)

         (* assert (Time.lt (f_from' w) (f_to' w)) as LTFTW'. *)
         (* { apply FCOH_NEW; auto. red. clear. basic_solver. } *)
         (* assert (Time.lt (f_to' w) (f_to' wnext)) as LTTNEXT'. *)
         (* { eapply f_to_co_mon; eauto. *)
         (*   all: red; basic_solver. } *)

         (* edestruct (@Memory.split_exists promises_split locw *)
         (*                                 (f_from' w) (f_to' w) (f_to' wnext) *)
         (*                                 (Message.full valw (Some rel')) Message.reserve) *)
         (*   as [promises' PADD]; eauto. *)
         (* { erewrite Memory.split_o; eauto. by rewrite loc_ts_eq_dec_eq. } *)
         (* admit. } *)

    assert (f_to wprev <> f_from wconext) as FFNEQ.
    { intros HH.
      cdes RESERVED_TIME.
      apply TFRMW in HH; auto.
      eapply rfrmw_in_im_co in HH; eauto.
        by eapply HH; [apply COPREV|]. }

    assert (Time.lt (f_to wprev) (f_from wconext)) as FFLT.
    { clear -FFLE FFNEQ. apply Time.le_lteq in FFLE. desf. }

    cdes RESERVED_TIME. desc.
    set (nn_to := Time.middle (f_to wprev) (f_from wconext)).
    set ( n_to := Time.middle (f_to wprev) nn_to).
    set (f_to' := upd (upd f_to w n_to) wnext nn_to).
    exists f_to'.
    
    set (B := (rf ⨾ rmw) wprev w).
    assert (exists n_from,
               ⟪ NFROM : (n_from = f_to wprev /\ B) \/
                         (n_from = Time.middle (f_to wprev) n_to /\ ~B) ⟫)
      as [n_from NFROM].
    { by destruct (classic B); eexists; [left|right]. }
    set (f_from' := upd (upd f_from w n_from) wnext n_to).
    exists f_from'.

    assert (Time.lt n_to nn_to) as LTNTONNTO.
    { unfold n_to, nn_to. repeat (apply Time.middle_spec). auto. }
    assert (Time.le n_to nn_to) as LENTONNTO.
    { apply Time.le_lteq. eauto. }

    assert (Time.lt (f_to wprev) nn_to) as LTNNTO.
    { subst nn_to. by apply DenseOrder.middle_spec. }

    assert (Time.lt (f_to wprev) n_to) as LTNTO.
    { subst n_to. by apply DenseOrder.middle_spec. }

    assert (Time.le (f_to wprev) n_from) as LEPREVFROM.
    { destruct NFROM; desc; subst.
      { reflexivity. }
      apply Time.le_lteq. left. by apply Time.middle_spec. }

    assert (Time.lt n_from n_to) as LTFROMTO.
    { destruct NFROM; desc; subst; auto.
        by apply Time.middle_spec. }

    assert (Time.lt (f_to' wprev) (f_to' w)) as PREVNLT.
    { unfold f_to'. repeat (rewrite updo; [|done]). by rewrite upds. }

    assert (Time.le (View.rlx rel'' locw)
                    (View.rlx (TView.cur (Local.tview local)) locw)) as GG.
    { unfold rel''. destruct (Rel w).
      { reflexivity. }
      subst. eapply rel_le_cur; eauto. }

    assert (Time.lt (View.rlx rel'' locw) (f_to' w)) as REL_VIEW_LT.
    { unfold f_to'. rewrite updo; [|done]. rewrite upds.
      eapply TimeFacts.le_lt_lt; [|by apply LTNTO].
      eapply le_msg_rel_f_to_wprev; eauto. by subst thread. }

    assert (Time.le (View.rlx rel'' locw) (f_to' w)) as REL_VIEW_LE.
    { apply Time.le_lteq. eauto. }
    
    set (rel' := View.join (View.join rel'' (View.unwrap p_rel))
                           (View.singleton_ur locw (f_to' w))).
    assert (Time.le (View.rlx (View.unwrap p_rel) locw) (f_to' w)) as PREL_LE.
    { subst. apply Time.bot_spec. }

    assert (Time.lt (f_from' w) (f_to' w)) as LTTFW.
    { unfold f_to', f_from'.
        by repeat (repeat (rewrite updo; [|done]); rewrite upds). }

    assert (Time.lt (f_from' wnext) (f_to' wnext)) as LTTFWNEXT.
    { unfold f_to', f_from'.
        by repeat (repeat (rewrite updo; [|done]); rewrite upds). }

    assert (Time.le nn_to (f_from wconext)) as LENNTOWCONEXT.
    { unfold nn_to.
      apply Time.le_lteq; left; apply Time.middle_spec; auto. }

    assert (Time.le n_to (f_from wconext)) as LENTOWCONEXT.
    { transitivity nn_to; auto. }

    assert (REQ_TO : forall e (SE : S e), f_to' e = f_to e).
    { ins. subst f_to'. by repeat (rewrite updo; [|by intros HH; subst]). }
    assert (REQ_FROM : forall e (SE : S e), f_from' e = f_from e).
    { ins. subst f_from'. by repeat (rewrite updo; [|by intros HH; subst]). }
    assert (ISSEQ_TO   : forall e (ISS: issued T e), f_to' e = f_to e).
    { ins. subst f_to'. by repeat (rewrite updo; [|by intros HH; subst]). }
    assert (ISSEQ_FROM : forall e (ISS: issued T e), f_from' e = f_from e).
    { ins. subst f_from'. by repeat (rewrite updo; [|by intros HH; subst]). }
    assert (FTOWNBOT : f_to' w <> Time.bot).
    { intros HH. eapply Time.lt_strorder with (x:=f_to' w). rewrite HH at 1.
      eapply TimeFacts.le_lt_lt; eauto. apply Time.bot_spec. }

    assert (FTOWNEXTNBOT : f_to' wnext <> Time.bot).
    { intros HH. eapply Time.lt_strorder with (x:=f_to' wnext). rewrite HH at 1.
      eapply TimeFacts.le_lt_lt; eauto. apply Time.bot_spec. }

    assert (~ is_init wconext) as NINITWCONEXT.
    { apply no_co_to_init in CONEXT; auto.
      apply seq_eqv_r in CONEXT. desf. }

    assert (forall to from msg,
               Memory.get locw to (Configuration.memory PC) = Some (from, msg) ->
               Interval.disjoint (f_from' w, f_to' wnext) (from, to)) as DISJOINT.
    { ins. unfold f_to', f_from'; rewrite !upds.
      rewrite updo; auto. rewrite upds.
      apply Interval.le_disjoint with (b:= (f_to wprev,f_from wconext)); auto.
      { eapply co_S_memory_disjoint; eauto. }
      constructor; simpls. }

    assert (forall to from msg,
               Memory.get locw to (Configuration.memory PC) = Some (from, msg) ->
               Interval.disjoint (f_from' w, f_to' w) (from, to)) as DISJOINT'.
    { ins.
      eapply Interval.le_disjoint; [eapply DISJOINT|]; eauto.
      constructor; simpls; [reflexivity|].
      unfold f_to', f_from'.
        by repeat (rewrite !upds; repeat (rewrite updo; [|done])). }

    assert (forall to from msg,
               Memory.get locw to (Configuration.memory PC) = Some (from, msg) ->
               Interval.disjoint (f_from' wnext, f_to' wnext) (from, to)) as DISJOINT''.
    { ins.
      eapply Interval.le_disjoint; [eapply DISJOINT|]; eauto.
      constructor; simpls; [|reflexivity].
      unfold f_to', f_from'.
      repeat (rewrite !upds; repeat (rewrite updo; [|done])).
      apply Time.le_lteq. eauto. }

    assert (Message.wf (Message.full valw (Some rel'))) as WFREL'.
    { do 3 constructor.
      subst rel'. subst. simpls. rewrite RELPLN''. reflexivity. }

    edestruct (@Memory.add_exists (Local.promises local) locw (f_from' w) (f_to' w)
                                  (Message.full valw (Some rel')))
      as [promises_add PADD]; eauto.
    { ins. eapply DISJOINT'. eapply PROM_IN_MEM; eauto. }

    edestruct (@Memory.add_exists (Configuration.memory PC)
                                  locw (f_from' w) (f_to' w)
                                  (Message.full valw (Some rel')))
      as [memory_add MADD]; eauto.

    assert (exists promises_rel,
               ⟪ PEQ :
                   if Rel w
                   then Memory.remove promises_add locw (f_from' w) (f_to' w)
                                      (Message.full valw (Some rel')) promises_rel
                   else promises_rel = promises_add ⟫).
    { destruct (is_rel lab w) eqn:REL; eauto.
      edestruct Memory.remove_exists as [promises''].
      2: { exists promises''. eauto. }
      erewrite Memory.add_o; eauto. by rewrite loc_ts_eq_dec_eq. }
    desc.

    assert (forall to2 from2 msg2
                   (GET2 : Memory.get locw to2 promises_add = Some (from2, msg2)),
               Interval.disjoint (f_from' wnext, f_to' wnext) (from2, to2)) as DISJMM.
    { ins; erewrite Memory.add_o in GET2; eauto.
      destruct (loc_ts_eq_dec (locw, to2) (locw, f_to' w)) as [|NEQ];
        simpls; desc; subst.
      { rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in GET2. inv GET2.
        unfold f_to', f_from'.
        repeat (rewrite !upds; repeat (rewrite updo; [|done])).
        symmetry. apply Interval.disjoint_imm. }
      rewrite (loc_ts_eq_dec_neq NEQ) in GET2.
      eapply DISJOINT''. eapply PROM_IN_MEM; eauto. }

    edestruct (@Memory.add_exists promises_rel locw (f_from' wnext) (f_to' wnext)
                                  Message.reserve)
      as [promises' PADD2]; eauto; try by constructor.
    { destruct (Rel w); subst; ins; auto.
      erewrite Memory.remove_o in GET2; eauto.
      destruct (loc_ts_eq_dec (locw, to2) (locw, f_to' w)).
      { simpls; desc; subst. rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in GET2.
        inv GET2. }
      rewrite loc_ts_eq_dec_neq in GET2; auto. eapply DISJMM; eauto. }

    edestruct (@Memory.add_exists memory_add locw (f_from' wnext) (f_to' wnext)
                                  Message.reserve)
      as [memory' MADD2]; eauto; try by constructor.
    { ins. erewrite Memory.add_o in GET2; eauto.
      destruct (loc_ts_eq_dec (locw, to2) (locw, f_to' w)) as [|NEQ]; simpls; desc; subst.
      { rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in GET2. inv GET2.
        unfold f_to', f_from'.
        repeat (rewrite !upds; repeat (rewrite updo; [|done])).
        symmetry. apply Interval.disjoint_imm. }
      rewrite (loc_ts_eq_dec_neq NEQ) in GET2.
      eapply DISJOINT''. eauto. }

    assert (n_from = Time.middle (f_to wprev) n_to) as FROM.
    { destruct NFROM as [[_ BB]|]; desc; auto.
      exfalso. apply NWEX. red. generalize BB. unfold B. clear. basic_solver. }

    assert (forall x (SX : S x) (CO : co x w), 
               Time.lt (f_to x) (Time.middle (f_to wprev) n_to)) as LTNSFROM.
    { subst. ins.
      assert (co^? x wprev) as COX; subst; auto.
      { eapply P_co_immediate_P_co_transp_in_co_cr with (P:=S); auto.
        exists wnext. split; auto. 
        apply seq_eqv_l. split; auto. eapply WF.(co_trans); eauto. }
      assert (Time.le (f_to x) (f_to wprev)) as LEA.
      { destruct COX; subst; [reflexivity|].
        apply Time.le_lteq; left. eapply f_to_co_mon; eauto. }
      apply TimeFacts.le_lt_lt with (b:=f_to wprev); auto.
        by apply Time.middle_spec. }

    assert (forall x (SX : S x) (CO : co wnext x),
               Time.le (f_from wconext) (f_from x)) as LENSFROMCONEXT.
    { ins.
      assert (co^? wconext x) as [|COX]; subst; eauto.
      { eapply immediate_co_P_transp_co_P_in_co_cr with (P:=S); auto.
        exists wnext. split; auto. 
        apply seq_eqv_r. by split. }
      { reflexivity. }
      apply Time.le_lteq; left. eapply f_from_co_mon; eauto. }

    assert (forall x (SX : S x) (CO : co x w), 
               Time.lt (f_to x) n_to) as LTNSFROMN.
    { ins. etransitivity.
      { by apply LTNSFROM. }
        by apply Time.middle_spec. }

    assert (forall x (SX : S x) (CO : co x w), 
               Time.le (f_to x) (Time.middle (f_to wprev) n_to)) as LENSFROM.
    { ins. apply Time.le_lteq; left. by apply LTNSFROM. }

    assert (forall x (SX : S x) (CO : co x w), f_to x <> n_from) as NSNFROM.
    { subst. ins. intros HH.
      apply Time.lt_strorder with (x:=f_to x).
      rewrite HH at 2. by apply LTNSFROM. }
    
    assert (forall x (SX : S x), co x w <-> co x wnext) as COPREVEQ.
    { ins. split; intros HH.
      { eapply WF.(co_trans); eauto. }
      assert (co^? x wprev) as [|COX]; subst; auto.
      { eapply P_co_immediate_P_co_transp_in_co_cr with (P:=S); auto.
        exists wnext. split; auto. 
        apply seq_eqv_l. split; auto. }
      eapply WF.(co_trans); eauto. }

    assert (forall x (SX : S x), co w x <-> co wnext x) as CONEXTEQ.
    { ins. split; intros HH.
      2: { by eapply WF.(co_trans); [|by apply HH]. }
      assert (co^? wconext x) as [|COX]; subst; eauto.
      { eapply immediate_co_P_transp_co_P_in_co_cr with (P:=S); auto.
        exists w. split; auto. 
        apply seq_eqv_r. by split. }
        by eapply WF.(co_trans); [|by apply COX]. }

    assert (f_to_coherent G S' f_to' f_from') as FCOH_NEW.
    (* TODO: make a lemma. *)
    { unfold S', f_to', f_from'.
      red; splits; ins.
      { rewrite !updo.
        { by apply FCOH. }
        all: intros HH; subst; by destruct H. }
      { do 2 (rewrite updo; [|by intros HH; subst; destruct H]).
          by apply FCOH. }
      { destruct H as [[H|]|H]; subst.
        3: { assert (x = wnext); subst.
             { eapply dom_sb_S_rfrmwf; eauto. }
               by rewrite !upds. }
        2: by do 2 (rewrite updo; auto; try rewrite upds).
        repeat (rewrite updo with (a:=wnext); [|by intros HH; subst];
                rewrite updo with (a:=w); [|by intros HH; subst]).
          by apply FCOH. }
      { assert (x <> y) as HXY.
        { by intros HH; subst; apply WF.(co_irr) in H1. }
        destruct H as [[H|]|H]; destruct H0 as [[H0|]|H0]; subst.
        all: try (rewrite !upds).
        all: try repeat (rewrite updo; [|by intros HH; subst]).
        all: try by
            match goal with 
            | H : ?X <> ?X |- _ => exfalso; apply H
            end.
        all: try (assert (x = wnext) by (eapply dom_sb_S_rfrmwf; eauto); subst).
        all: try (assert (y = wnext) by (eapply dom_sb_S_rfrmwf; eauto); subst).
        all: try rewrite !upds.
        all: try (rewrite updo; [|done]).
        all: try (rewrite updo; [|by intros HH; subst]).
        all: try rewrite !upds.
        all: try (rewrite updo; [|by auto]).
        all: try reflexivity.
        all: try by
            match goal with 
            | H : co ?X ?X |- _ => exfalso; eapply WF.(co_irr); eauto
            end.
        { by apply FCOH. }
        { by apply LENSFROM. }
        { apply Time.le_lteq; left. apply LTNSFROMN; auto. by apply COPREVEQ. }
        { etransitivity; [|apply LENSFROMCONEXT]; eauto. by apply CONEXTEQ. }
        { rewrite updo; [|by intros HH; subst].
          etransitivity; [|apply LENSFROMCONEXT]; eauto. }
        exfalso. eapply WF.(co_irr). eapply WF.(co_trans); eauto. }
      destruct H0 as [[H0|]|H0]; subst.
      3: { assert (y = wnext) by (eapply dom_sb_S_rfrmwf; eauto); subst.
           assert (x = w) by (eapply wf_rfrmwf; eauto); subst.
             by rewrite updo; auto; rewrite !upds. }
      2: { exfalso. apply NWEX. red. generalize H1. clear. basic_solver. }
      destruct H as [[H|]|H]; subst.
      3: { assert (x = wnext) by (eapply dom_sb_S_rfrmwf; eauto); subst.
           exfalso. apply NSWNEXT. eapply dom_rf_rmw_S with (T:=mkETC T S); eauto.
           generalize H0 H1. clear. basic_solver 10. }
      2: { exfalso. apply NSW. eapply dom_rf_rmw_S with (T:=mkETC T S); eauto.
           generalize H0 H1. clear. basic_solver 10. }
      do 2 (rewrite updo; [|by intros HH; subst]).
      destruct (classic (y = wconext)) as [|NEQ]; subst.
      2: { repeat (rewrite updo; [|by intros HH; subst]). by apply FCOH. }
      exfalso. 
      assert (co x wconext) as AA by (by apply rf_rmw_in_co).
      apply NCOIMM with (c:=x); apply seq_eqv_r; split; auto.
      edestruct WF.(wf_co_total) with (a:=w) (b:=x) as [|HH]; eauto.
      { apply (dom_l WF.(wf_coE)) in AA. destruct_seq_l AA as CE.
        apply (dom_l WF.(wf_coD)) in AA. destruct_seq_l AA as CD.
        split; [split|]; auto. rewrite <- LOCNEXT. by apply WF.(wf_col). }
      { by intros HH; subst. }
      exfalso. eapply rf_rmw_in_coimm; eauto. }
    assert (n_to <> nn_to) as NNTONEQ.
    { intros HH. rewrite HH in *. exfalso. eapply Time.lt_strorder; eauto. }

    assert (reserved_time
              G (mkTC (covered T) (issued T ∪₁ eq w))
              S' f_to' f_from' 
              sim_normal memory') as RST.
    (* TODO: make a lemma. *)
    { unfold S'. red. splits.
      { red. ins. erewrite Memory.add_o in MSG; eauto.
        destruct (loc_ts_eq_dec (l, to) (locw, f_to' wnext)) as [|NEQ]; simpls; desc; subst.
        { rewrite (loc_ts_eq_dec_eq locw (f_to' wnext)) in MSG. inv MSG. }
        rewrite (loc_ts_eq_dec_neq NEQ) in MSG.
        erewrite Memory.add_o in MSG; eauto.
        destruct (loc_ts_eq_dec (l, to) (locw, f_to' w)) as [|NEQ']; simpls; desc; subst.
        { rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in MSG. inv MSG.
          right. exists w. splits; eauto. red. eauto. }
        rewrite (loc_ts_eq_dec_neq NEQ') in MSG.
        eapply MEM0 in MSG. destruct MSG as [|MSG]; [by left|right].
        desc. exists b. splits; eauto.
        { red. eauto. }
        all: unfold f_to', f_from'; rewrite updo; [rewrite updo|]; auto.
        all: intros HH; subst; eauto. }
      { red. ins. erewrite Memory.add_o in MSG; eauto.
        destruct (loc_ts_eq_dec (l, to) (locw, f_to' wnext)) as [|NEQ]; simpls; desc; subst.
        { rewrite (loc_ts_eq_dec_eq locw (f_to' wnext)) in MSG. inv MSG.
          exists wnext. splits; eauto.
          2: by intros [HH|HH]; subst; eauto.
          unfolder. eauto. }
        rewrite (loc_ts_eq_dec_neq NEQ) in MSG.
        erewrite Memory.add_o in MSG; eauto.
        destruct (loc_ts_eq_dec (l, to) (locw, f_to' w)) as [|NEQ']; simpls; desc; subst.
        { rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in MSG. inv MSG. }
        rewrite (loc_ts_eq_dec_neq NEQ') in MSG.
        eapply HMEM0 in MSG.
        desc. exists b. splits; eauto.
        { unfolder. eauto. }
        { intros [HH|HH]; subst; eauto. }
        all: unfold f_to', f_from'; rewrite updo; [rewrite updo|]; auto.
        all: intros HH; subst; eauto. }
      unfold f_to', f_from'.
      intros x y [[AA|]|AA] [[BB|]|BB] CO; subst.
      all: try (assert (x = wnext) by (eapply dom_sb_S_rfrmwf; eauto); subst).
      all: try (assert (y = wnext) by (eapply dom_sb_S_rfrmwf; eauto); subst).
      all: try rewrite !upds.
      all: try repeat (rewrite updo; [|done]).
      all: try repeat (rewrite updo; [|by intros HH; subst]).
      all: try rewrite !upds.
      all: try repeat (rewrite updo; [|by intros HH; subst]).
      all: try rewrite !upds.
      all: intros HH; eauto.
      all: try by (exfalso; eauto).
      { exfalso. eapply NSNFROM; eauto. }
      { exfalso. eapply Time.lt_strorder with (x:=f_to x).
        rewrite HH at 2. apply LTNSFROMN; auto. by apply COPREVEQ. }
      { exfalso.
        eapply Time.lt_strorder with (x:=f_from y).
        eapply TimeFacts.lt_le_lt; [|apply LENSFROMCONEXT]; eauto.
        2: by apply CONEXTEQ.
        rewrite <- HH. by eapply TimeFacts.lt_le_lt; [|by apply LENNTOWCONEXT]. }
      { exfalso. subst. by apply WF.(co_irr) with (x:=y). }
      { exfalso.
        eapply Time.lt_strorder with (x:=f_from y).
        eapply TimeFacts.lt_le_lt; [|apply LENSFROMCONEXT]; eauto.
        rewrite <- HH. unfold nn_to. by apply Time.middle_spec. }
      exfalso.
      eapply Time.lt_strorder with (x:=nn_to).
      rewrite HH at 1. transitivity n_to; auto. }

    assert (Memory.inhabited memory_add) as INHABADD. 
    { eapply Memory.add_inhabited; eauto. }

    assert (Memory.inhabited memory') as INHAB'. 
    { do 2 (eapply Memory.add_inhabited; eauto). }

    assert (View.pln
              (View.join
                 (View.join rel'' (View.unwrap p_rel))
                 (View.singleton_ur locw (f_to' w))) =
            View.rlx
              (View.join (View.join rel'' (View.unwrap p_rel))
                         (View.singleton_ur locw (f_to' w)))) as RELPLN.
    { subst. simpls. by rewrite RELPLN''. }

    assert (Memory.closed_timemap
              (View.rlx
                 (View.join (View.join rel'' (View.unwrap p_rel))
                            (View.singleton_ur locw (f_to' w))))
              memory_add) as CLOSTM.
    { unfold View.join; ins.
      apply Memory.join_closed_timemap.
      2: { eapply Memory.singleton_closed_timemap; eauto.
           erewrite Memory.add_o; eauto.
           rewrite loc_ts_eq_dec_eq; eauto. }
      apply Memory.join_closed_timemap.
      2: { subst. simpls. by apply Memory.closed_timemap_bot. }
      eapply Memory.add_closed_timemap; eauto.
      subst rel''. destruct (Rel w); apply MEM_CLOSE. }

    assert (f_to' w <> f_to' wnext) as FTONEXTNEQ.
    { intros HH. eapply f_to_eq with (I:=S') in HH; eauto.
      { red. by rewrite LOC. }
      all: red; basic_solver. }

    splits; eauto; subst rel'0; subst rel''0. 
    { unfold View.join, TimeMap.join; ins. 
      repeat apply DenseOrder.join_spec; auto.
      unfold TimeMap.singleton, LocFun.add. rewrite Loc.eq_dec_eq. reflexivity. }
    { unfold f_from', f_to'. rewrite upds. rewrite updo; auto. by rewrite upds. }
    exists promises_add, memory_add, promises_rel, promises', memory'. splits; eauto.
    { constructor; auto. by rewrite RELPLN. }
    subst. eapply sim_helper_issue with (S':=S'); eauto.
    { transitivity (fun _ : actid => False); [|clear; basic_solver].
      generalize NWEX. unfold Execution.W_ex. clear; basic_solver. }
    { red. unfolder. eauto. }
    rewrite IE. unfold S'. eauto with hahn. }

  assert (WNEXTNONEXT : ~ (exists wconext : actid, (co ⨾ ⦗S⦘) wnext wconext)).
  { intros [x HH]. destruct_seq_r HH as AA. eapply WNONEXT. exists x.
    apply seq_eqv_r. split; auto. eapply WF.(co_trans); eauto. }

  set (ts := Memory.max_ts locw (Configuration.memory PC)).
  set ( n_to := (Time.incr (Time.incr ts))).
  set (nn_to := Time.incr n_to).
  set (f_to' := upd (upd f_to w n_to) wnext nn_to).
  exists f_to'.
 
  set (A :=
         exists wprev, ⟪ WPISS : issued T wprev ⟫ /\
                       ⟪ RFRMW : (rf ⨾ rmw) wprev w ⟫).
  assert (exists n_from,
             ⟪ NFROM_SPEC : ((n_from = ts) /\ A) \/ ((n_from = Time.incr ts) /\ ~ A) ⟫ )
    as [n_from NFROM].
  { destruct (classic A) as [H|H].
    { by exists ts; left. }
    by exists (Time.incr ts); right. }
  assert (Time.le ts n_from) as LENFROM_R.
  { destruct NFROM as [[N _]|[N _]]; subst; [reflexivity|].
    apply Time.le_lteq; left. apply DenseOrder.incr_spec. }

  assert (Time.le n_from (Time.incr ts)) as LENFROM_L.
  { destruct NFROM as [[N _]|[N _]]; subst; [|reflexivity].
    apply Time.le_lteq; left. apply DenseOrder.incr_spec. }

  set (f_from' := upd (upd f_from w n_from) wnext n_to).
  exists f_from'.

  assert (Time.lt n_from n_to) as NNLT.
  { eapply TimeFacts.le_lt_lt.
    2: by apply Time.incr_spec.
    done. }
  assert (Time.lt n_to nn_to) as LTNNTO.
  { unfold nn_to. apply Time.incr_spec. }

  assert (Time.lt (f_from' w) (f_to' w)) as NLT.
  { unfold f_to', f_from', ts. by repeat (rewrite updo; auto; rewrite upds). }

  assert (Time.lt (f_from' wnext) (f_to' wnext)) as NLTNEXT.
  { unfold f_to', f_from'. by rewrite !upds. }

  assert (Time.lt (View.rlx (TView.cur (Local.tview local)) locw) (f_to' w))
    as REL_VIEW_HELPER.
  { unfold f_to', ts. rewrite updo; auto. rewrite upds.
    etransitivity.
    2: by apply DenseOrder.incr_spec.
    eapply TimeFacts.le_lt_lt.
    2: by apply DenseOrder.incr_spec.
    apply Memory.max_ts_spec2.
    apply MEM_CLOSE. }

  assert (Time.lt (View.rlx rel'' locw) (f_to' w)) as REL_VIEW_LT.
  { subst rel''. destruct (Rel w); auto.
    eapply TimeFacts.le_lt_lt; [|by apply REL_VIEW_HELPER].
    subst. eapply rel_le_cur; eauto.  }
  assert (Time.le (View.rlx rel'' locw) (f_to' w)) as REL_VIEW_LE.
  { by apply Time.le_lteq; left. }

  assert (forall to from msg,
             Memory.get locw to (Configuration.memory PC) =
             Some (from, msg) ->
             Interval.disjoint (f_from' w, f_to' w) (from, to)) as DISJOINT.
  { unfold f_to', f_from', ts; repeat (rewrite updo; auto; rewrite upds).
    ins; red; ins. destruct LHS. destruct RHS.
    simpls.
    eapply Time.lt_strorder.
    eapply TimeFacts.le_lt_lt.
    2: by apply FROM.
    etransitivity.
    2: by apply LENFROM_R.
    etransitivity.
    { apply TO0. }
    unfold ts.
    apply Memory.max_ts_spec in H. desf. }

  assert (forall to from msg,
             Memory.get locw to (Configuration.memory PC) =
             Some (from, msg) ->
             Interval.disjoint (f_from' wnext, f_to' wnext) (from, to)) as DISJOINT'.
  { unfold f_to', f_from', ts. rewrite !upds.
    ins; red; ins. destruct LHS. destruct RHS.
    simpls.
    eapply Time.lt_strorder.
    etransitivity; [|by apply NNLT].
    eapply TimeFacts.lt_le_lt with (b:=x); auto.
    transitivity ts; auto.
    unfold ts.
    transitivity to; auto.
    apply Memory.max_ts_spec in H. desf. }

  set (rel' := View.join (View.join rel'' (View.unwrap p_rel))
                         (View.singleton_ur locw (f_to' w))).
  assert (Time.le (View.rlx (View.unwrap p_rel) locw) (f_to' w)) as PREL_LE.
  { subst. apply Time.bot_spec. }

  assert (Message.wf (Message.full valw (Some rel'))) as WFREL'.
  { do 3 constructor.
    subst rel'. subst. simpls. rewrite RELPLN''. reflexivity. }

  edestruct (@Memory.add_exists
               (Local.promises local) locw (f_from' w) (f_to' w)
               (Message.full valw (Some rel')))
    as [promises_add PADD]; auto.
  { ins. eapply DISJOINT.
    eapply PROM_IN_MEM; eauto. }

  edestruct (@Memory.add_exists
               PC.(Configuration.memory) locw (f_from' w) (f_to' w)
               (Message.full valw (Some rel')))
    as [memory_add MADD]; auto.

  assert (exists promises_rel,
             ⟪ PEQ :
                 if Rel w
                 then Memory.remove promises_add locw (f_from' w) (f_to' w)
                                    (Message.full valw (Some rel')) promises_rel
                 else promises_rel = promises_add ⟫).
  { destruct (is_rel lab w) eqn:REL; eauto.
    edestruct Memory.remove_exists as [promises''].
    2: { exists promises''. eauto. }
    erewrite Memory.add_o; eauto. by rewrite loc_ts_eq_dec_eq. }
  desc.

  assert (forall to2 from2 msg2
                 (GET2 : Memory.get locw to2 promises_add = Some (from2, msg2)),
             Interval.disjoint (f_from' wnext, f_to' wnext) (from2, to2)) as DISJMM.
  { ins. erewrite Memory.add_o in GET2; eauto.
    destruct (classic (to2 = f_to' w)); subst.
    { rewrite loc_ts_eq_dec_eq in GET2. inv GET2.
      unfold f_to', f_from'. rewrite !upds. repeat (rewrite updo; auto; rewrite upds).
      symmetry. apply Interval.disjoint_imm. }
    rewrite loc_ts_eq_dec_neq in GET2; eauto.
    eapply DISJOINT'.
    eapply PROM_IN_MEM; eauto. }

  edestruct (@Memory.add_exists promises_rel locw (f_from' wnext) (f_to' wnext)
                                Message.reserve)
    as [promises' PADD2]; eauto; try by constructor.
  { destruct (Rel w); subst; ins; auto.
    erewrite Memory.remove_o in GET2; eauto.
    destruct (loc_ts_eq_dec (locw, to2) (locw, f_to' w)).
    { simpls; desc; subst. rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in GET2.
      inv GET2. }
    rewrite loc_ts_eq_dec_neq in GET2; auto. eapply DISJMM; eauto. }

  edestruct (@Memory.add_exists
               memory_add locw (f_from' wnext) (f_to' wnext)
               Message.reserve)
    as [memory' MADD2]; auto; try by constructor.
  { ins. erewrite Memory.add_o in GET2; eauto.
    destruct (classic (to2 = f_to' w)); subst.
    { rewrite loc_ts_eq_dec_eq in GET2. inv GET2.
      unfold f_to', f_from'. rewrite !upds. repeat (rewrite updo; auto; rewrite upds).
      symmetry. apply Interval.disjoint_imm. }
    rewrite loc_ts_eq_dec_neq in GET2; eauto. }

  assert (Memory.inhabited memory_add) as INHABADD. 
  { eapply Memory.add_inhabited; eauto. }
  assert (Memory.inhabited memory') as INHAB'. 
  { eapply Memory.add_inhabited; eauto. }

  assert (n_from = Memory.max_ts locw (Configuration.memory PC) /\ (rf ⨾ rmw) wprev w \/
          n_from = Time.incr (Memory.max_ts locw (Configuration.memory PC)) /\
          ~ (rf ⨾ rmw) wprev w) as FCOH_HELPER.
  { right. splits; auto.
    2: { intros HH. generalize NWEX, HH. unfold Execution.W_ex. clear. basic_solver. }
    subst ts A.
    clear PEQ.
    destruct NFROM as [AA|]; desf.
    exfalso. generalize NWEX, RFRMW. unfold Execution.W_ex. clear. basic_solver. }

  assert (f_to_coherent G S' f_to' f_from') as FCOH_NEW.
  (* TODO: make a lemma. *)
  { unfold f_to', f_from', S'.
    red. splits; ins.
    1,2: repeat (rewrite updo; [|by destruct H; intros HH; subst]); by apply FCOH.
    { destruct H as [[H|]|H]; subst.
      { repeat (rewrite updo; [|by intros HH; subst]). by apply FCOH. }
      { by repeat (rewrite updo; [|done]; rewrite upds). }
      assert (x = wnext) by (eapply dom_sb_S_rfrmwf; eauto); subst.
        by rewrite !upds. }
    { assert (x <> y) as HXY.
      { by intros HH; subst; apply WF.(co_irr) in H1. }
      destruct H as [[H|]|H]; destruct H0 as [[H0|]|H0]; subst.
      all: try repeat (rewrite updo; [|by intros HH; subst]).
      all: try (rewrite !upds).
      all: try by
          match goal with 
          | H : ?X <> ?X |- _ => exfalso; apply H
          end.
      all: try (assert (x = wnext) by (eapply dom_sb_S_rfrmwf; eauto); subst).
      all: try (assert (y = wnext) by (eapply dom_sb_S_rfrmwf; eauto); subst).
      all: try rewrite !upds.
      all: try (rewrite updo; [|done]).
      all: try rewrite !upds.
      all: try (rewrite updo; [|done]).
      all: try rewrite !upds.
      all: try repeat (rewrite updo; [|by intros HH; subst]).
      all: try reflexivity.
      { by apply FCOH. }
      { etransitivity; [|by apply LENFROM_R].
        edestruct reserved_to_message with (l:=locw) (b:=x)
          as [wconextmsg [WCONEXTMEM WCONEXTPROM']]; eauto.
        { rewrite <- LOC. by apply WF.(wf_col). }
        subst ts. eapply Memory.max_ts_spec; eauto. }
      { apply Time.le_lteq; left.
        eapply TimeFacts.le_lt_lt; [|by apply NNLT].
        etransitivity; [|by apply LENFROM_R].
        edestruct reserved_to_message with (l:=locw) (b:=x)
          as [wconextmsg [WCONEXTMEM WCONEXTPROM']]; eauto.
        { rewrite <- WNEXTLOC. by apply WF.(wf_col). }
        subst ts. eapply Memory.max_ts_spec; eauto. }
      { exfalso. eapply WNONEXT. eexists. apply seq_eqv_r. eauto. }
      { exfalso. eapply WNEXTNONEXT. eexists. apply seq_eqv_r. eauto. }
      { exfalso. eapply WF.(co_irr). eapply WF.(co_trans); eauto. }
      exfalso. eapply WF.(co_irr); eauto. }
    destruct H0 as [[H0|]|H0]; subst.
    3: { assert (y = wnext) by (eapply dom_sb_S_rfrmwf; eauto); subst.
         assert (x = w) by (eapply wf_rfrmwf; eauto); subst.
           by rewrite updo; auto; rewrite !upds. }
    2: { exfalso. apply NWEX. red. generalize H1. clear. basic_solver. }
    destruct H as [[H|]|H]; subst.
    3: { assert (x = wnext) by (eapply dom_sb_S_rfrmwf; eauto); subst.
         exfalso. apply NSWNEXT. eapply dom_rf_rmw_S with (T:=mkETC T S); eauto.
         generalize H0 H1. clear. basic_solver 10. }
    2: { exfalso. apply NSW. eapply dom_rf_rmw_S with (T:=mkETC T S); eauto.
         generalize H0 H1. clear. basic_solver 10. }
    repeat (rewrite updo; [|by intros HH; subst]). by apply FCOH. }

  assert (NNEQ : nn_to <> n_to).
  { intros HH. rewrite HH in LTNNTO. eapply Time.lt_strorder. apply LTNNTO. }

  assert (n_from = Time.incr ts) as FROM.
  { destruct NFROM as [[_ AA]|]; desc; auto. exfalso.
    apply NWEX. red. generalize AA. unfold A. clear. basic_solver. }

  assert (forall x (SX : S x) (XLOC : loc lab x = Some locw),
             Time.le (f_to x) ts) as LESTS.
  { ins. unfold ts.
    edestruct reserved_to_message with (l:=locw) (b:=x)
      as [wconextmsg [WCONEXTMEM WCONEXTPROM']]; eauto.
    eapply Memory.max_ts_spec; eauto. }

  assert (reserved_time
            G (mkTC (covered T) (issued T ∪₁ eq w))
            S' f_to' f_from' smode memory') as RST.
  (* TODO: make a lemma. *)
  { unfold f_to', f_from'.
    red in RESERVED_TIME.
    red. destruct smode; desc.
    2: by splits; rewrite <- SINS.
    unfold S'. splits.
    { red. ins. erewrite Memory.add_o in MSG; eauto.
      destruct (loc_ts_eq_dec (l, to) (locw, f_to' wnext)) as [|NEQ]; simpls; desc; subst.
      { rewrite (loc_ts_eq_dec_eq locw (f_to' wnext)) in MSG. inv MSG. }
      rewrite (loc_ts_eq_dec_neq NEQ) in MSG.
      erewrite Memory.add_o in MSG; eauto.
      destruct (loc_ts_eq_dec (l, to) (locw, f_to' w)) as [|NEQ']; simpls; desc; subst.
      { rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in MSG. inv MSG. right.
        exists w. splits; eauto. red. eauto. }
      rewrite (loc_ts_eq_dec_neq NEQ') in MSG.
      apply MEM in MSG. destruct MSG as [|]; [by left|right]. desc.
      exists b. splits; eauto.
      { red. eauto. }
      all: repeat (rewrite updo; [|by intros HH; subst; eauto]); auto. }
    { red. ins. erewrite Memory.add_o in MSG; eauto.
      destruct (loc_ts_eq_dec (l, to) (locw, f_to' wnext)) as [|NEQ]; simpls; desc; subst.
      { rewrite (loc_ts_eq_dec_eq locw (f_to' wnext)) in MSG. inv MSG.
        exists wnext. splits; eauto.
        { unfolder. eauto. }
        intros [|]; eauto. }
      rewrite (loc_ts_eq_dec_neq NEQ) in MSG.
      erewrite Memory.add_o in MSG; eauto.
      destruct (loc_ts_eq_dec (l, to) (locw, f_to' w)) as [|NEQ']; simpls; desc; subst.
      { rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in MSG. inv MSG. }
      rewrite (loc_ts_eq_dec_neq NEQ') in MSG.
      apply HMEM in MSG. desc. exists b. splits; eauto.
      { unfolder. eauto. }
      { intros [|]; subst; eauto. }
      all: repeat (rewrite updo; [|by intros HH; subst; eauto]); auto. }
    intros x y [[AA|]|AA] [[BB|]|BB] CO; subst.
    all: try (assert (x = wnext) by (eapply dom_sb_S_rfrmwf; eauto); subst).
    all: try (assert (y = wnext) by (eapply dom_sb_S_rfrmwf; eauto); subst).
    all: try rewrite !upds.
    all: try repeat (rewrite updo; [|done]).
    all: try repeat (rewrite updo; [|by intros HH; subst]).
    all: try rewrite !upds.
    all: try repeat (rewrite updo; [|by intros HH; subst]).
    all: try rewrite !upds.
    all: intros HH; eauto.
    7: { exfalso; eauto. }
    4: { exfalso; eapply WF.(co_irr); eauto. }
    1,2: exfalso; eapply Time.lt_strorder with (x:=f_to x); rewrite HH at 2.
    { eapply TimeFacts.le_lt_lt; [|by apply Time.incr_spec].
      apply LESTS; auto. rewrite <- LOC. by apply WF.(wf_col). }
    { eapply TimeFacts.le_lt_lt.
      { apply LESTS; auto. rewrite <- WNEXTLOC. by apply WF.(wf_col). }
      unfold n_to. etransitivity; apply Time.incr_spec. }
    { exfalso. apply WNONEXT. eexists. apply seq_eqv_r. split; eauto. }
    { exfalso. apply WNEXTNONEXT. eexists. apply seq_eqv_r. split; eauto. }
    exfalso. eapply WF.(co_irr) with (x:=wnext). eapply WF.(co_trans); eauto. }

  assert (View.pln
            (View.join
               (View.join rel'' (View.unwrap p_rel))
               (View.singleton_ur locw (f_to' w))) =
          View.rlx
            (View.join (View.join rel'' (View.unwrap p_rel))
                       (View.singleton_ur locw (f_to' w)))) as RELPLN.
  { subst. simpls. by rewrite RELPLN''. }

  assert (Memory.closed_timemap
            (View.rlx
               (View.join (View.join rel'' (View.unwrap p_rel))
                          (View.singleton_ur locw (f_to' w))))
            memory_add) as CLOSTM.
  { unfold View.join; ins.
    apply Memory.join_closed_timemap.
    2: { eapply Memory.singleton_closed_timemap; eauto.
         erewrite Memory.add_o; eauto.
         rewrite loc_ts_eq_dec_eq; eauto. }
    apply Memory.join_closed_timemap.
    2: { subst. simpls. by apply Memory.closed_timemap_bot. }
    eapply Memory.add_closed_timemap; eauto.
    subst rel''. destruct (Rel w); apply MEM_CLOSE. }

  assert (REQ_TO : forall e (SE : S e), f_to' e = f_to e).
  { ins. subst f_to'. by repeat (rewrite updo; [|by intros HH; subst]). }
  assert (REQ_FROM : forall e (SE : S e), f_from' e = f_from e).
  { ins. subst f_from'. by repeat (rewrite updo; [|by intros HH; subst]). }
  assert (ISSEQ_TO   : forall e (ISS: issued T e), f_to' e = f_to e).
  { ins. subst f_to'. by repeat (rewrite updo; [|by intros HH; subst]). }
  assert (ISSEQ_FROM : forall e (ISS: issued T e), f_from' e = f_from e).
  { ins. subst f_from'. by repeat (rewrite updo; [|by intros HH; subst]). }
  assert (FTOWNBOT : f_to' w <> Time.bot).
  { intros HH. eapply Time.lt_strorder with (x:=f_to' w). rewrite HH at 1.
    eapply TimeFacts.le_lt_lt; eauto. apply Time.bot_spec. }
  assert (FTOWNEXTNBOT : f_to' wnext <> Time.bot).
  { intros HH. eapply Time.lt_strorder with (x:=f_to' wnext). rewrite HH at 1.
    eapply TimeFacts.le_lt_lt; eauto. apply Time.bot_spec. }

  assert (f_to' w <> f_to' wnext) as FTONEXTNEQ.
  { intros HH. eapply f_to_eq with (I:=S') in HH; eauto.
    { red. by rewrite LOC. }
    all: red; basic_solver. }

  splits; eauto; subst rel'0; subst rel''0.
  { unfold View.join, TimeMap.join; ins. 
    repeat apply DenseOrder.join_spec; auto.
    unfold TimeMap.singleton, LocFun.add. rewrite Loc.eq_dec_eq. reflexivity. }
  { unfold f_from', f_to'. rewrite upds. rewrite updo; auto. by rewrite upds. }
  exists promises_add, memory_add, promises_rel, promises', memory'.
  splits; eauto.
  { constructor; auto. by rewrite RELPLN. }
  subst. eapply sim_helper_issue with (S':=S'); eauto.
  { transitivity (fun _ : actid => False); [|clear; basic_solver].
    generalize NWEX. unfold Execution.W_ex. clear; basic_solver. }
  { red. unfolder. eauto. }
  rewrite IE. eauto with hahn.
Qed.

End Aux.
