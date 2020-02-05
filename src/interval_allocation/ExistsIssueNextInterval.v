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
      (TID : IdentMap.find (tid w) PC.(Configuration.threads) = Some (langst, local)) :
  let promises := local.(Local.promises) in
  let memory   := PC.(Configuration.memory) in
  let T'       := mkTC (covered T) (issued T ∪₁ eq w) in
  let S'       := S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G (mkETC T S) rfi (eq w) in
  exists p_rel,
    rfrmw_prev_rel G sc T f_to f_from PC.(Configuration.memory) w locw p_rel /\
    (⟪ FOR_ISSUE :
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

           exists promises_add memory_add promises' memory',
             ⟪ PADD :
                 Memory.add local.(Local.promises) locw (f_from' w) (f_to' w)
                            Message.reserve promises_add ⟫ /\
             ⟪ MADD :
                 Memory.add memory locw (f_from' w) (f_to' w)
                            Message.reserve memory_add ⟫ /\

             ⟪ PADD2 :
                 Memory.add promises_add locw (f_from' wnext) (f_to' wnext)
                            Message.reserve promises' ⟫ /\
             ⟪ MADD2 :
                 Memory.add memory_add locw (f_from' wnext) (f_to' wnext)
                            Message.reserve memory' ⟫ /\

             ⟪ INHAB : Memory.inhabited memory' ⟫ /\
             ⟪ RELMCLOS : Memory.closed_timemap (View.rlx rel') memory' ⟫ /\
             ⟪ RELVCLOS : Memory.closed_view rel' memory' ⟫ /\

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
                 reserved_time G T' S' f_to' f_from' smode memory' ⟫ ⟫ \/
     ⟪ FOR_SPLIT :
         ⟪ SMODE : smode = sim_certification ⟫ /\
         exists ws wsmsg f_to' f_from',
           let rel'' :=
               if is_rel lab w
               then (TView.cur (Local.tview local))
               else (TView.rel (Local.tview local) locw)
           in
           let rel' := (View.join (View.join rel'' p_rel.(View.unwrap))
                                  (View.singleton_ur locw (f_to' w))) in
           ⟪ WSISS  : S ws ⟫ /\
           ⟪ WSNCOV : ~ covered T ws ⟫ /\

           ⟪ SBWW : sb w ws ⟫ /\
           ⟪ SAME_LOC : Loc_ locw ws ⟫ /\
           ⟪ COWW : co w ws ⟫ /\

           ⟪ FEQ1 : f_to' wnext = f_from' ws ⟫ /\
           ⟪ FEQ2 : f_from' w = f_from ws ⟫ /\

           ⟪ WSPROM : Memory.get locw (f_to ws) (Local.promises local) =
                      Some (f_from ws, wsmsg)⟫ /\
           ⟪ WSMEM : Memory.get locw (f_to ws) memory =
                     Some (f_from ws, wsmsg)⟫ /\

           ⟪ RELWFEQ : View.pln rel' = View.rlx rel' ⟫ /\
           ⟪ REL_VIEW_LT : Time.lt (View.rlx rel'' locw) (f_to' w) ⟫ /\
           ⟪ REL_VIEW_LE : Time.le (View.rlx rel'  locw) (f_to' w) ⟫ /\
           ⟪ FCOH : f_to_coherent G S' f_to' f_from' ⟫ /\

           exists promises_split memory_split promises' memory',
             ⟪ PSPLIT :
                 Memory.split (Local.promises local)
                              locw (f_from' w) (f_to' wnext) (f_to' ws)
                              (Message.full valw (Some rel')) wsmsg
                              promises_split ⟫ /\
             ⟪ MSPLIT :
                 Memory.split memory locw (f_from' w) (f_to' wnext) (f_to' ws)
                              (Message.full valw (Some rel')) wsmsg
                              memory_split ⟫ /\

             ⟪ PADD :
                 Memory.split promises' 
                              locw (f_from' w) (f_to' w) (f_to' wnext)
                              (Message.full valw (Some rel'))
                              Message.reserve 
                              promises' ⟫ /\
             ⟪ MADD :
                 Memory.split memory_split
                              locw (f_from' w) (f_to' w) (f_to' wnext)
                              (Message.full valw (Some rel'))
                              Message.reserve 
                              memory' ⟫ /\

             ⟪ INHAB : Memory.inhabited memory' ⟫ /\
             ⟪ RELMCLOS : Memory.closed_timemap (View.rlx rel') memory' ⟫ /\
             ⟪ RELVCLOS : Memory.closed_view rel' memory' ⟫ /\


             ⟪ HELPER :
                 sim_mem_helper
                   G sc f_to' w (f_from' w) valw
                   (View.join (View.join (if is_rel lab w
                                          then (TView.cur (Local.tview local))
                                          else (TView.rel (Local.tview local) locw))
                                         p_rel.(View.unwrap))
                              (View.singleton_ur locw (f_to' w))) ⟫ /\

             ⟪ RESERVED_TIME :
                 reserved_time G T' S' f_to' f_from' smode memory' ⟫ ⟫).
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

  destruct (classic (exists wconext, (co ⨾ ⦗ S ⦘) w wconext)) as [WCONEXT|WNONEXT]; [|left].
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
    
    destruct smode eqn:SMODE; [left|right].
    2: { splits; eauto.
         cdes RESERVED_TIME.
         assert (set_compl (W_ex ∪₁ S) w) as WNRMWS.
         { intros [|]; eauto. }

         assert (sb w wconext) as SBNEXT.
         { eapply nS_imm_co_in_sb with (S:=S); eauto. }

         assert (w <> wconext /\ wnext <> wconext) as [WCONEXTNEQ WNEXTCONEQ].
         { by split; intros HH; subst. }

         assert (tid wconext = tid w) as TIDNEXT.
         { apply sb_tid_init in SBNEXT. destruct SBNEXT as [H|H]; desf. }
         assert (~ covered T wconext) as NCOVNEXT.
         { intros H; apply TCCOH in H.
           apply WNCOV. apply H.
           eexists. apply seq_eqv_r; split; eauto. }

         edestruct reserved_to_message with (l:=locw) (b:=wconext)
           as [wconextmsg [WCONEXTMEM WCONEXTPROM']]; eauto.
         assert (Memory.get locw (f_to wconext) (Local.promises local) =
                 Some (f_from wconext, wconextmsg)) as WCONEXTPROM.
         { apply WCONEXTPROM'; auto. }

         assert (~ is_init wconext) as NINITWCONEXT.
         { apply no_co_to_init in CONEXT; auto.
           apply seq_eqv_r in CONEXT. desf. }

         set (nn_to := Time.middle (f_from wconext) (f_to wconext)).
         set ( n_to := Time.middle (f_from wconext) nn_to).
         assert (Time.lt n_to nn_to) as LTNNTO.
         { unfold n_to, nn_to. do 2 apply Time.middle_spec. by apply FCOH. }

         assert (Time.lt (f_from wconext) (f_to wconext)) as LLWCONEXT.
         { by apply FCOH. }
         assert (Time.lt (f_from wconext) n_to) as LLFROMN.
         { unfold n_to, nn_to. by do 2 apply DenseOrder.middle_spec. }
         assert (Time.lt nn_to (f_to wconext)) as LLTONN.
         { unfold nn_to. by apply DenseOrder.middle_spec. }
         assert (Time.lt n_to (f_to wconext)) as LLTON.
         { etransitivity; [|by apply LLTONN].
           unfold n_to, nn_to. by do 2 apply DenseOrder.middle_spec. }

         assert (Time.lt (f_to wprev) n_to) as LTPREVN.
         { unfold n_to.
           apply TimeFacts.le_lt_lt with (b:=f_from wconext).
           { by apply FCOH. }
           apply Time.middle_spec. etransitivity; eauto. }
         assert (Time.le (f_to wprev) n_to) as LEPREVN.
         { apply Time.le_lteq; eauto. }

         set (f_to'   := upd (upd f_to w n_to) wnext nn_to).
         set (f_from' := upd (upd (upd f_from w (f_from wconext)) wnext n_to) wconext nn_to).

         set (rel' := View.join
                        (View.join rel'' p_rel.(View.unwrap))
                        (View.singleton_ur locw (f_to' w))).
         assert (View.opt_wf (Some rel')) as RELWF.
         { apply View.opt_wf_some.
           apply View.join_wf.
           2: by apply View.singleton_ur_wf.
           constructor.
           unfold View.join; simpls.
           rewrite PRELNN. simpls.
           rewrite RELPLN''. reflexivity. }

         assert (Message.wf (Message.full valw (Some rel'))) as MSGWF.
         { by constructor. }

         set (S':=S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G (mkETC T S) rfi (eq w)).
         assert (f_to_coherent G S' f_to' f_from') as FCOH_NEW.
         (* TODO: make a lemma. *)
         { unfold S', f_to', f_from'.
           red; splits; ins.
           { rewrite !updo.
             { by apply FCOH. }
             all: intros HH; subst; by destruct H. }
           { do 3 (rewrite updo; [|by intros HH; subst; destruct H]).
               by apply FCOH. }
           { destruct H as [[H|]|H]; subst.
             3: { assert (x = wnext); subst.
                  { eapply dom_sb_S_rfrmwf; eauto. }
                  rewrite upds.
                  rewrite updo; auto; rewrite upds; auto. }
             2: by do 3 (rewrite updo; auto; try rewrite upds).
             rewrite updo with (a:=wnext); [|by intros HH; subst].
             rewrite updo with (a:=w); [|by intros HH; subst].
             destruct (classic (wconext = x)) as [|NEQ]; subst;
               [by rewrite upds | rewrite updo; auto].
             do 2 (rewrite updo; auto; try by intros HH; subst).
               by apply FCOH. }
           { assert (x <> y) as HXY.
             { by intros HH; subst; apply WF.(co_irr) in H1. }
             destruct H as [[H|]|H]; destruct H0 as [[H0|]|H0]; subst.
             all: try (rewrite !upds).
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
             all: try reflexivity.
             all: try by (Time.le_lteq; eauto).
             all: try by
                 match goal with 
                 | H : co ?X ?X |- _ => exfalso; eapply WF.(co_irr); eauto
                 end.
             { destruct (classic (y = wconext)) as [|NEQ]; subst;
                 [rewrite upds | rewrite updo; auto].
               2: { do 2 (rewrite updo; [|by intros HH; subst]).
                      by apply FCOH. }
               apply Time.le_lteq; left.
               transitivity n_to; auto.
               unfold n_to.
               eapply TimeFacts.le_lt_lt with (b:=f_from wconext); auto.
                 by apply FCOH. }
             { apply FCOH; auto. eapply WF.(co_trans); eauto. }
             { assert (co^? x wprev) as [|COX]; subst; auto.
               { eapply P_co_immediate_P_co_transp_in_co_cr with (P:=S); auto.
                 exists wnext. split; auto. 
                 apply seq_eqv_l. by split. }
               transitivity (f_to wprev); auto.
               apply Time.le_lteq; left. eapply f_to_co_mon; eauto. }
             { assert (co^? wconext y) as [|COX]; subst; eauto.
               { eapply immediate_co_P_transp_co_P_in_co_cr with (P:=S); auto.
                 exists x. split; auto. 
                 apply seq_eqv_r. by split. }
               { rewrite upds. apply Time.le_lteq; eauto. }
               assert (y <> wconext).
               { intros HH. subst. eapply WF.(co_irr). eauto. }
               repeat (rewrite updo; [|by intros HH; subst]).
               transitivity (f_to wconext); auto.
               2: by apply FCOH.
               apply Time.le_lteq; eauto. }
             { assert (co^? wconext y) as [|COX]; subst; eauto.
               { eapply immediate_co_P_transp_co_P_in_co_cr with (P:=S); auto.
                 exists wnext. split; auto. 
                 apply seq_eqv_r. by split. }
               { rewrite upds. apply Time.le_lteq; eauto. }
               assert (y <> wconext).
               { intros HH. subst. eapply WF.(co_irr). eauto. }
               repeat (rewrite updo; [|by intros HH; subst]).
               transitivity (f_to wconext); auto.
               2: by apply FCOH.
               apply Time.le_lteq; eauto. }
             exfalso. eapply WF.(co_irr). eapply WF.(co_trans); eauto. }
           destruct H0 as [[H0|]|H0]; subst.
           3: { assert (y = wnext) by (eapply dom_sb_S_rfrmwf; eauto); subst.
                assert (x = w) by (eapply wf_rfrmwf; eauto); subst.
                  by do 2 (rewrite updo; auto; rewrite upds). }
           2: { exfalso. apply NWEX. red. generalize H1. clear. basic_solver. }
           destruct H as [[H|]|H]; subst.
           3: { assert (x = wnext) by (eapply dom_sb_S_rfrmwf; eauto); subst.
                exfalso. apply NSWNEXT. eapply dom_rf_rmw_S with (T:=mkETC T S); eauto.
                generalize H0 H1. clear. basic_solver 10. }
           2: { exfalso. apply NSW. eapply dom_rf_rmw_S with (T:=mkETC T S); eauto.
                generalize H0 H1. clear. basic_solver 10. }
           do 2 (rewrite updo; [|by intros HH; subst]).
           destruct (classic (y = wconext)) as [|NEQ]; subst.
           2: { rewrite updo; auto.
                repeat (rewrite updo; [|by intros HH; subst]). by apply FCOH. }
           exfalso. 
           assert (co x wconext) as AA by (by apply rf_rmw_in_co).
           apply NCOIMM with (c:=x); apply seq_eqv_r; split; auto.
           edestruct WF.(wf_co_total) with (a:=w) (b:=x) as [|HH]; eauto.
           { apply (dom_l WF.(wf_coE)) in AA. destruct_seq_l AA as CE.
             apply (dom_l WF.(wf_coD)) in AA. destruct_seq_l AA as CD.
             split; [split|]; auto. rewrite <- LOCNEXT. by apply WF.(wf_col). }
           { by intros HH; subst. }
           exfalso. eapply rf_rmw_in_coimm; eauto. }

         assert (Time.lt (f_from' w) (f_to' wnext)) as LTFWTWNEXT.
         { unfold f_from', f_to'.
           rewrite upds. do 2 (rewrite updo; auto). rewrite upds.
           etransitivity; eauto. }
         assert (Time.lt (f_to' wnext) (f_to' wconext)) as LTFWNEXTFWCONEXT.
         { unfold f_from', f_to'.
           rewrite !upds. do 2 (rewrite updo; auto). }

         edestruct (@Memory.split_exists (Local.promises local) locw
                                         (f_from' w) (f_to' wnext) (f_to' wconext)
                                         (Message.full valw (Some rel')) wconextmsg)
           as [promises_split PSPLIT]; eauto.
         { unfold f_to', f_from'. repeat (rewrite updo; [|done]). by rewrite upds. }

         edestruct (@Memory.split_exists (Configuration.memory PC) locw 
                                         (f_from' w) (f_to' wnext) (f_to' wconext)
                                         (Message.full valw (Some rel')) wconextmsg)
           as [memory_split MSPLIT]; eauto.
         { unfold f_to', f_from'. repeat (rewrite updo; [|done]). by rewrite upds. }

         assert (Time.lt (f_from' w) (f_to' w)) as LTFTW'.
         { apply FCOH_NEW; auto. red. clear. basic_solver. }
         assert (Time.lt (f_to' w) (f_to' wnext)) as LTTNEXT'.
         { eapply f_to_co_mon; eauto.
           all: red; basic_solver. }

         (* TODO: Currently, it's impossible to split wconextmsg in the needed way. *)
         (* edestruct (@Memory.split_exists promises_split locw *)
         (*                                 (f_from' w) (f_to' w) (f_to' wnext) *)
         (*                                 (Message.full valw (Some rel')) Message.reserve) *)
         (*   as [promises' PADD]; eauto. *)
         (* { erewrite Memory.split_o; eauto. by rewrite loc_ts_eq_dec_eq. } *)
         admit. }

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

    edestruct (@Memory.add_exists promises_add locw (f_from' wnext) (f_to' wnext)
                                  Message.reserve)
      as [promises' PADD2]; eauto.
    { ins. erewrite Memory.add_o in GET2; eauto.
      destruct (loc_ts_eq_dec (locw, to2) (locw, f_to' w)) as [|NEQ]; simpls; desc; subst.
      { rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in GET2. inv GET2.
        unfold f_to', f_from'.
        repeat (rewrite !upds; repeat (rewrite updo; [|done])).
        symmetry. apply Interval.disjoint_imm. }
      rewrite (loc_ts_eq_dec_neq NEQ) in GET2.
      eapply DISJOINT''. eapply PROM_IN_MEM; eauto. }

    edestruct (@Memory.add_exists (Configuration.memory PC)
                                  locw (f_from' wnext) (f_to' wnext)
                                  Message.reserve)
      as [memory' MADD2]; eauto; try constructor.

    set (S':=S ∪₁ eq w ∪₁ dom_sb_S_rfrmw G (mkETC T S) rfi (eq w)).
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
        { assert (co^? x wprev) as [|COX]; subst; auto.
          { eapply P_co_immediate_P_co_transp_in_co_cr with (P:=S); auto.
            exists wnext. split; auto. 
            apply seq_eqv_l. split; auto. eapply WF.(co_trans); eauto. }
          transitivity (f_to wprev); auto.
          apply Time.le_lteq; left. eapply f_to_co_mon; eauto. }
        { assert (co^? x wprev) as [|COX]; subst; auto.
          { eapply P_co_immediate_P_co_transp_in_co_cr with (P:=S); auto.
            exists wnext. split; auto. 
            apply seq_eqv_l. split; auto. }
          { apply Time.le_lteq. eauto. }
          transitivity (f_to wprev).
          { apply Time.le_lteq; left. eapply f_to_co_mon; eauto. }
          apply Time.le_lteq. eauto. }
        { assert (co^? wconext y) as [|COX]; subst; eauto.
          { eapply immediate_co_P_transp_co_P_in_co_cr with (P:=S); auto.
            exists x. split; auto. 
            apply seq_eqv_r. by split. }
          transitivity (f_from wconext); auto.
          apply Time.le_lteq; left. eapply f_from_co_mon; eauto. }
        { rewrite updo; [|by intros HH; subst].
          assert (co^? wconext y) as [|COX]; subst; eauto.
          { eapply immediate_co_P_transp_co_P_in_co_cr with (P:=S); auto.
            exists wnext. split; auto. 
            apply seq_eqv_r. by split. }
          transitivity (f_from wconext); auto.
          apply Time.le_lteq; left. eapply f_from_co_mon; eauto. }
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

    (* TODO: continue from here. *)
    
    assert (reserved_time
              G (mkTC (covered T) (issued T ∪₁ eq w))
              (S ∪₁ eq w) (upd f_to w n_to) (upd f_from w n_from)
              sim_normal memory') as RST.
    { eapply reserved_time_add_S_middle; eauto. }
    
    assert (Memory.inhabited memory') as INHAB'. 
    { eapply Memory.add_inhabited; eauto. }

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
              memory') as CLOSTM.
    { unfold View.join; ins.
      apply Memory.join_closed_timemap.
      2: { eapply Memory.singleton_closed_timemap; eauto.
           erewrite Memory.add_o; eauto. rewrite loc_ts_eq_dec_eq; eauto. }
      apply Memory.join_closed_timemap.
      2: { subst. simpls. by apply Memory.closed_timemap_bot. }
      eapply Memory.add_closed_timemap; eauto.
      subst rel''. destruct (Rel w); apply MEM_CLOSE. }

    splits; eauto; subst rel'0; subst rel''0. 
    { unfold View.join, TimeMap.join; ins. 
      repeat apply DenseOrder.join_spec; auto.
      unfold TimeMap.singleton, LocFun.add. rewrite Loc.eq_dec_eq. reflexivity. }
    do 2 eexists. splits; eauto.
    { constructor; auto. by rewrite RELPLN. }
    { eapply f_to_coherent_mori; [|by apply FCOH_NEW].
      rewrite NONEXT. clear. basic_solver. }
    { subst. eapply sim_helper_issue with (S':=S ∪₁ eq w); eauto.
      { transitivity (fun _ : actid => False); [|clear; basic_solver].
        generalize NWEX. unfold Execution.W_ex. clear; basic_solver. }
      { ins. unfold f_to'. rewrite updo; auto. intros HH; subst. eauto. }
      { by right. }
      rewrite IE. eauto with hahn. }
    eapply reserved_time_more; (try by apply RST); auto.
    { apply same_tc. }
    split; [rewrite NONEXT|]; eauto with hahn.
    clear. basic_solver 10. }

  set (ts := Memory.max_ts locw (Configuration.memory PC)).
  set (f_to' := upd f_to w (Time.incr (Time.incr ts))).
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

  set (f_from' := upd f_from w n_from).
  exists f_from'.

  assert (Time.lt (f_from' w) (f_to' w)) as NLT.
  { unfold f_to', f_from', ts; rewrite !upds.
    eapply TimeFacts.le_lt_lt.
    { apply LENFROM_L. }
    apply DenseOrder.incr_spec. }

  assert (Time.lt n_from (Time.incr (Time.incr ts))) as NNLT.
  { eapply TimeFacts.le_lt_lt.
    2: by apply Time.incr_spec.
    done. }

  assert (Time.lt (View.rlx (TView.cur (Local.tview local)) locw) (f_to' w))
    as REL_VIEW_HELPER.
  { unfold f_to', ts; rewrite upds.
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
  { unfold f_to', f_from', ts; rewrite !upds.
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
    as [promises' PADD]; auto.
  { ins. eapply DISJOINT.
    eapply PROM_IN_MEM; eauto. }

  edestruct (@Memory.add_exists
               PC.(Configuration.memory) locw (f_from' w) (f_to' w)
               (Message.full valw (Some rel')))
    as [memory' MADD]; auto.

  assert (Memory.inhabited memory') as INHAB'. 
  { eapply Memory.add_inhabited; eauto. }

  assert (n_from = Memory.max_ts locw (Configuration.memory PC) /\ (rf ⨾ rmw) wprev w \/
          n_from = Time.incr (Memory.max_ts locw (Configuration.memory PC)) /\
          ~ (rf ⨾ rmw) wprev w) as FCOH_HELPER.
  { right. splits; auto.
    2: { intros HH. generalize NWEX, HH. unfold Execution.W_ex. clear. basic_solver. }
    subst ts A.
    destruct NFROM as [AA|]; desf.
    exfalso. generalize NWEX, RFRMW. unfold Execution.W_ex. clear. basic_solver. }

  assert (f_to_coherent G (S ∪₁ eq w) f_to' f_from') as FCOH_NEW.
  { unfold f_to', f_from'.
    eapply f_to_coherent_add_S_after; eauto.
    transitivity (fun _ : actid => False); [|clear; basic_solver].
    generalize NWEX. unfold Execution.W_ex. clear. basic_solver. }

  assert (reserved_time
            G (mkTC (covered T) (issued T ∪₁ eq w))
            (S ∪₁ eq w) f_to' f_from'
            smode memory') as RST.
  { unfold f_to', f_from'.
    eapply reserved_time_add_S_after; eauto. }

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
            memory') as CLOSTM.
  { unfold View.join; ins.
    apply Memory.join_closed_timemap.
    2: { eapply Memory.singleton_closed_timemap; eauto.
         erewrite Memory.add_o; eauto. rewrite loc_ts_eq_dec_eq; eauto. }
    apply Memory.join_closed_timemap.
    2: { subst. simpls. by apply Memory.closed_timemap_bot. }
    eapply Memory.add_closed_timemap; eauto.
    subst rel''. destruct (Rel w); apply MEM_CLOSE. }

  splits; eauto; subst rel'0; subst rel''0.
  { unfold View.join, TimeMap.join; ins. 
    repeat apply DenseOrder.join_spec; auto.
    unfold TimeMap.singleton, LocFun.add. rewrite Loc.eq_dec_eq. reflexivity. }
  do 2 eexists. splits; eauto.
  { constructor; auto. by rewrite RELPLN. }
  { eapply f_to_coherent_mori; [|by apply FCOH_NEW].
    rewrite NONEXT. clear. basic_solver. }
  { subst. eapply sim_helper_issue with (S':=S ∪₁ eq w); eauto.
    { transitivity (fun _ : actid => False); [|clear; basic_solver].
      generalize NWEX. unfold Execution.W_ex. clear; basic_solver. }
    { ins. unfold f_to'. rewrite updo; auto. intros HH; subst. eauto. }
    { by right. }
    rewrite IE. eauto with hahn. }
  eapply reserved_time_more; (try by apply RST); auto.
  { apply same_tc. }
  split; [rewrite NONEXT|]; eauto with hahn.
  clear. basic_solver 10.
Qed.

End Aux.
