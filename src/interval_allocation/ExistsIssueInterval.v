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

Lemma exists_time_interval_for_issue_no_next w locw valw langst smode
      (ISSUABLE : issuable G sc T w)
      (WNISS : ~ issued T w)
      (NWEX : ~ W_ex w)
      (NONEXT : dom_sb_S_rfrmw G (mkETC T S) rfi (eq w) ⊆₁ ∅)
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

           exists promises' memory',
             ⟪ PADD :
                 Memory.add local.(Local.promises) locw (f_from' w) (f_to' w)
                                                   (Message.full valw (Some rel')) promises' ⟫ /\
             ⟪ MADD :
                 Memory.add memory locw (f_from' w) (f_to' w)
                            (Message.full valw (Some rel')) memory' ⟫ /\

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

           ⟪ FEQ1 : f_to' w = f_from' ws ⟫ /\
           ⟪ FEQ2 : f_from' w = f_from ws ⟫ /\

           ⟪ WSPROM : Memory.get locw (f_to ws) (Local.promises local) =
                      Some (f_from ws, wsmsg)⟫ /\
           ⟪ WSMEM : Memory.get locw (f_to ws) memory =
                     Some (f_from ws, wsmsg)⟫ /\

           ⟪ RELWFEQ : View.pln rel' = View.rlx rel' ⟫ /\
           ⟪ REL_VIEW_LT : Time.lt (View.rlx rel'' locw) (f_to' w) ⟫ /\
           ⟪ REL_VIEW_LE : Time.le (View.rlx rel'  locw) (f_to' w) ⟫ /\
           ⟪ FCOH : f_to_coherent G S' f_to' f_from' ⟫ /\

           exists promises' memory',
             ⟪ PADD :
                 Memory.split (Local.promises local)
                              locw (f_from' w) (f_to' w) (f_to' ws)
                              (Message.full valw (Some rel'))
                              wsmsg
                              promises' ⟫ /\
             ⟪ MADD :
                 Memory.split memory locw (f_from' w) (f_to' w) (f_to' ws)
                              (Message.full valw (Some rel'))
                              wsmsg
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
Proof using WF IMMCON ETCCOH RELCOV FCOH SIM_TVIEW.
  assert (tc_coherent G sc T) as TCCOH by apply ETCCOH.
  assert (S ⊆₁ E ∩₁ W) as SEW.
  { apply set_subset_inter_r. split; [by apply ETCCOH|].
    apply (reservedW WF ETCCOH). }
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

  assert ((E ∩₁ W ∩₁ Loc_ locw) w) as WEW.
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

  edestruct co_prev_to_imm_co_prev with (w:=w) as [wprev]; eauto. desc.

  destruct (classic (exists wnext, (co ⨾ ⦗ S ⦘) w wnext)) as [WNEXT|WNONEXT]; [|left].
  { edestruct co_next_to_imm_co_next with (w:=w) as [wnext]; eauto. clear WNEXT. desc.
    assert ((co ⨾ ⦗set_compl S⦘ ⨾ co) wprev wnext) as CONS.
    { exists w. split; auto. apply seq_eqv_l. by split. }
    assert (co wprev wnext) as COPN.
    { eapply WF.(co_trans); eauto. }

    assert (immediate (⦗S⦘ ⨾ co ⨾ ⦗S⦘) wprev wnext) as COSIMM.
    { apply P_co_nP_co_P_imm; auto.
      { apply ETCCOH. }
      { apply (reservedW WF ETCCOH). }
      exists w. split; auto. apply seq_eqv_l. by split. }

    assert (~ (rf ⨾ rmw) w wnext) as NRFRMWNEXT.
    { intros AA. apply NSW. eapply (dom_rf_rmw_S WF ETCCOH).
      exists wnext. apply seqA. apply seq_eqv_r. by split. }

    assert (Time.le (f_to wprev) (f_from wnext)) as FFLE by (by apply FCOH).
    
    destruct smode eqn:SMODE; [left|right].
    2: { splits; eauto.
         cdes RESERVED_TIME.
         assert (set_compl (W_ex ∪₁ S) w) as WNRMWS.
         { intros [|]; eauto. }

         (* TODO: introduce a lemma *)
         assert (sb w wnext) as SBNEXT.
         { admit. }
         (* { clear -WF WW NSW FOR_SPLIT NCOIMM ISSNEXT CONEXT WNRMWS. simpls. desc. *)
         (*   clear NSW. *)
         (*   (* RMW_ISSUED  *) *)
         (*   apply clos_trans_of_transitiveD; [apply sb_trans|]. *)
         (*   apply (inclusion_t_t FOR_SPLIT). *)
         (*   eapply ct_imm1 in CONEXT. *)
         (*   2: by apply WF.(co_irr). *)
         (*   2: by apply WF.(co_trans). *)
         (*   2: by intros x [y H']; apply WF.(wf_coE) in H'; apply seq_eqv_l in H'; desf; eauto. *)
         (*   apply t_rt_step in CONEXT. destruct CONEXT as [z [IMMS IMM]]. *)
         (*   apply t_rt_step. exists z; split; [|apply seq_eqv_l; split; [|done]]. *)
         (*   { apply rtE in IMMS. destruct IMMS as [IMMS|IMMS]. *)
         (*     { red in IMMS; desf. apply rt_refl. } *)
         (*     assert (immediate (co ⨾ ⦗S⦘) z wnext) as IMM'. *)
         (*     { red; split; [apply seq_eqv_r; split; auto|]. *)
         (*       { apply clos_trans_immediate1; auto. *)
         (*         eapply WF.(co_trans). } *)
         (*       ins. eapply NCOIMM; [|by apply R2]. *)
         (*       apply seq_eqv_r in R1; destruct R1 as [R1 R3]. *)
         (*       apply seq_eqv_r; split; auto. *)
         (*       eapply WF.(co_trans); [|by apply R1]. *)
         (*       apply clos_trans_immediate1; auto. *)
         (*       eapply WF.(co_trans). } *)
         (*     clear IMM. *)
         (*     induction IMMS. *)
         (*     { apply rt_step. apply seq_eqv_l; split; auto. } *)
         (*     assert (co y wnext) as YNEXT. *)
         (*     { apply clos_trans_immediate1; auto. *)
         (*       eapply WF.(co_trans). *)
         (*       eapply transitive_ct; [by apply IMMS2|]. *)
         (*       eapply clos_trans_immediate2. *)
         (*       { apply WF.(co_trans). } *)
         (*       { apply WF.(co_irr). } *)
         (*       { red; ins. apply WF.(wf_coE) in REL. *)
         (*         apply seq_eqv_l in REL; destruct REL as [_ REL]. *)
         (*         apply seq_eqv_r in REL. apply REL. } *)
         (*       destruct IMM' as [II _]. *)
         (*       apply seq_eqv_r in II; apply II. } *)
         (*     assert (immediate (co ⨾ ⦗S⦘) y wnext) as YNEXTIMM. *)
         (*     { red; split; [by apply seq_eqv_r; split|]. *)
         (*       ins. eapply NCOIMM; [|by apply R2]. *)
         (*       apply seq_eqv_r in R1; destruct R1 as [R1 R3]. *)
         (*       apply seq_eqv_r; split; auto. *)
         (*       eapply WF.(co_trans); [|by apply R1]. *)
         (*       apply clos_trans_immediate1; auto. *)
         (*       eapply WF.(co_trans). } *)
         (*     eapply rt_trans. *)
         (*     { by apply IHIMMS1. } *)
         (*     apply IHIMMS2; auto. *)
         (*     { apply WF.(wf_coD) in YNEXT. *)
         (*       apply seq_eqv_l in YNEXT; desf. } *)
         (*     { intros NISS. eapply NCOIMM; apply seq_eqv_r; split; auto. *)
         (*       2: by apply NISS. *)
         (*       2: done. *)
         (*       apply clos_trans_immediate1; auto. *)
         (*         by apply WF.(co_trans). } *)
         (*     admit. } *)
         (*   intros HH. apply rtE in IMMS; destruct IMMS as [IMSS|IMMS]. *)
         (*   { red in IMSS; desf. } *)
         (*   eapply NCOIMM; apply seq_eqv_r; split; auto. *)
         (*   2: by apply HH. *)
         (*   all: apply clos_trans_immediate1; auto. *)
         (*   all: apply WF.(co_trans). } *)

         assert (tid wnext = tid w) as TIDNEXT.
         { apply sb_tid_init in SBNEXT. destruct SBNEXT as [H|H]; desf. }
         assert (~ covered T wnext) as NCOVNEXT.
         { intros H; apply TCCOH in H.
           apply WNCOV. apply H.
           eexists. apply seq_eqv_r; split; eauto. }

         edestruct reserved_to_message with (l:=locw) (b:=wnext)
           as [wnextmsg WNEXTMEM]; eauto.
         assert (Memory.get locw (f_to wnext) (Local.promises local) =
                 Some (f_from wnext, wnextmsg)) as WNEXTPROM.
         { admit. }

         set (n_to := Time.middle (f_from wnext) (f_to wnext)).

         assert (~ is_init wnext) as NINITWNEXT.
         { apply no_co_to_init in CONEXT; auto.
           2: { apply coherence_sc_per_loc. apply IMMCON. }
           apply seq_eqv_r in CONEXT. desf. }

         assert (Time.lt (f_from wnext) (f_to wnext)) as LLWNEXT.
         { by apply FCOH. }
         assert (Time.lt (f_from wnext) n_to) as LLFROMN.
         { unfold n_to. by apply DenseOrder.middle_spec. }
         assert (Time.lt n_to (f_to wnext)) as LLTON.
         { unfold n_to. by apply DenseOrder.middle_spec. }

         set (rel' := View.join
                        (View.join rel'' p_rel.(View.unwrap))
                        (View.singleton_ur locw n_to)).
         assert (View.opt_wf (Some rel')) as RELWF.
         { apply View.opt_wf_some.
           apply View.join_wf.
           2: by apply View.singleton_ur_wf.
           constructor.
           unfold View.join; simpls.
           rewrite PRELNN. simpls.
           admit. }
           (* rewrite REL_PLN_RLX. *)
           (* cdes PLN_RLX_EQ. rewrite EQ_REL. *)
           (* reflexivity. } *)

         assert (Message.wf (Message.full valw (Some rel'))) as MSGWF.
         { by constructor. }

         assert (f_to_coherent G (S ∪₁ eq w) (upd f_to w n_to)
                               (upd (upd f_from wnext n_to) w (f_from wnext))) as FCOH_NEW.
         (* TODO: introduce a lemma *)
         { red; splits; ins.
           { rewrite updo.
             { by apply FCOH. }
             intros HH; subst. by destruct H. }
           { rewrite updo.
             rewrite updo.
             { by apply FCOH. }
             all: intros HH; subst.
             { apply NCOVNEXT. by apply TCCOH. }
             destruct H; desf. } 
           { destruct H as [H|]; subst.
             2: by rewrite !upds.
             rewrite updo.
             2: by intros HH; subst.
             destruct (classic (wnext = x)) as [|NEQ]; subst;
               [rewrite upds | rewrite updo; auto];
               rewrite updo; auto.
               by apply FCOH.
                 by intros HH; subst. }
           { assert (x <> y) as HXY.
             { by intros HH; subst; apply WF.(co_irr) in H1. }
             destruct H as [H|]; destruct H0 as [H0|]; subst.
             all: try (rewrite !upds).
             { rewrite updo; [|by intros HH; subst].
               rewrite updo; [|by intros HH; subst].
               destruct (classic (wnext = y)) as [|NEQ]; subst;
                 [rewrite upds | rewrite updo; auto].
               { etransitivity; eauto.
                 2: by apply Time.le_lteq; left; eauto.
                   by apply FCOH. }
                 by apply FCOH. }
             { rewrite updo; auto.
               apply FCOH; auto.
               eapply WF.(co_trans); eauto. }
             { rewrite updo; auto.
               destruct (classic (wnext = y)) as [|NEQ]; subst;
                 [by rewrite upds; apply DenseOrder_le_PreOrder | rewrite updo; auto].
               etransitivity.
               { apply Time.le_lteq; left. apply LLTON. }
               apply FCOH; auto.
               eapply tot_ex.
               { by eapply WF. }
               { unfolder; splits; eauto.
                 hahn_rewrite (dom_r (wf_coE WF)) in H1; unfolder in H1; basic_solver 12.
                 hahn_rewrite (dom_r (wf_coD WF)) in H1; unfolder in H1; basic_solver 12. }
               { unfolder; splits; eauto.
                 hahn_rewrite (wf_col WF) in H1; unfold same_loc in *; congruence. }
               { unfold immediate in NCOIMM; desc; intro; eapply NCOIMM0; basic_solver 21. }
                 by intro; subst. }
               by apply WF.(co_irr) in H1. }
           destruct H as [H|]; subst.
           { assert (x <> w) as NXW.
             { intros YY. desf. }
             rewrite updo; auto.
             destruct H0 as [H0|]; subst.
             2: { exfalso. generalize H1, NWEX. unfold Execution.W_ex. clear. basic_solver. }
             assert (y <> w) as NXY.
             { intros YY. desf. }
             rewrite updo; auto.
             assert (y <> wnext) as NYN.
             2: { rewrite updo; auto. by apply FCOH. }
             intros UU; subst.
             assert (loc lab x = Some locw) as XLOC.
             { rewrite <- LOCNEXT. by apply WF.(wf_rfrmwl). }
             edestruct WF.(wf_co_total) with (a:=w) (b:=x) as [CO|CO]; auto.
             1,2: split; [split|]; auto.
             { by apply ETCCOH.(etc_S_in_E). }
             { by apply (reservedW WF ETCCOH). }
             { by rewrite XLOC. }
             { eapply NCOIMM.
               all: apply seq_eqv_r; split; eauto.
               eapply rfrmw_in_im_co; eauto. }
             eapply rfrmw_in_im_co in H1; eauto. eapply H1; eauto. }
           rewrite upds. rewrite updo.
           2: { intros HH; subst. eapply wf_rfrmw_irr; eauto. }
           destruct H0 as [H0|]; subst.
           2: { exfalso. eapply wf_rfrmw_irr; eauto. }
           assert (y = wnext); subst.
           2: by rewrite upds.
           admit. }
           (* { apply NRFRMW. apply seqA. apply seq_eqv_r. by split. } *)
    
    edestruct (@Memory.split_exists (Local.promises local) locw
                                    (f_from wnext) n_to (f_to wnext)
                                    (Message.full valw (Some rel')) wnextmsg)
           as [promises' PSPLIT]; eauto.

    edestruct (@Memory.split_exists PC.(Configuration.memory) locw
                                    (f_from wnext) n_to (f_to wnext)
                                    (Message.full valw (Some rel')) wnextmsg)
           as [memory' MSPLIT]; eauto.

    (* assert (issued T wnext) as NEXTISS. *)
    (* { destruct NIMMCO as [HH _]. apply seq_eqv_r in HH; desf. } *)
    (* assert (~ Rel w) as NREL. *)
    (* { intros WREL. apply WNISS. *)
    (*   eapply w_covered_issued; eauto. split; auto. *)
    (*   apply TCCOH in NEXTISS. destruct NEXTISS as [[[_ NN] _] _]. *)
    (*   apply NN. exists wnext. apply seq_eqv_r; split; auto. *)
    (*   red. left; left; right. apply seq_eqv_l; split; [by split|]. *)
    (*   apply seq_eqv_r; split; auto. split; auto. *)
    (*   red. by rewrite LOC. } *)

    (* assert (vnext = valwnext); subst. *)
    (* { rewrite VALWNEXT in VNEXT. inv VNEXT. } *)

    exists wnext, wnextmsg.
    exists (upd f_to w n_to).
    exists (upd (upd f_from wnext n_to) w (f_from wnext)).

    assert (Time.le (f_to wprev) (f_from wnext)) as LEWPWTO.
    { destruct (classic (is_init wprev)) as [WPINIT|WPNINIT].
      2: by apply FCOH; eauto.
      assert (f_to wprev = tid_init) as HH.
      { apply FCOH. by split. }
      rewrite HH. apply Time.bot_spec. }

    assert (Time.lt (f_to wprev) n_to) as LEWPNTO.
    { eapply TimeFacts.le_lt_lt; [by apply LEWPWTO|].
      unfold n_to.
      apply Time.middle_spec. by apply FCOH. }

    assert (DenseOrder.lt tid_init n_to) as NTOBOT.
    { unfold n_to.
      eapply TimeFacts.le_lt_lt; eauto.
      apply Time.bot_spec. }
    
    assert (Memory.inhabited memory') as INHAB'.
    { eapply Memory.split_inhabited; eauto. }

    assert (Memory.closed_timemap
              (View.rlx
                 (View.join (View.join rel'' (View.unwrap p_rel))
                            (View.singleton_ur locw n_to)))
              memory') as CLOSTM.
    { unfold View.join; ins.
      apply Memory.join_closed_timemap.
      2: { eapply Memory.singleton_closed_timemap; eauto.
           erewrite Memory.split_o; eauto. rewrite loc_ts_eq_dec_eq; eauto. }
      apply Memory.join_closed_timemap.
      2: { subst. simpls. by apply Memory.closed_timemap_bot. }
      eapply Memory.split_closed_timemap; eauto.
      subst rel''. destruct (Rel w); apply MEM_CLOSE. }

    assert (Time.lt (View.rlx (TView.rel (Local.tview local) locw) locw) n_to)
      as LTNTO.
    { eapply TimeFacts.le_lt_lt.
      2: by apply LEWPNTO.
      assert (Time.le (View.rlx (TView.rel (Local.tview local) locw) locw)
                      (View.rlx (TView.cur (Local.tview local)) locw)) as VV.
      { subst. eapply rel_le_cur; eauto. }
      etransitivity; [by apply VV|].
      cdes SIM_TVIEW. cdes CUR.
      admit. }
      (* eapply max_value_leS with (w:=w) (S:=S); eauto. *)
      (* { unfold t_cur, c_cur, CombRelations.urr. *)
      (*   rewrite !seqA. rewrite dom_eqv1. *)
      (*     by intros x [[_ YY]]. } *)
      (* { apply t_cur_covered; eauto. } *)
      (* split; [|basic_solver]. *)
      (* intros x y QQ. apply seq_eqv_l in QQ. destruct QQ as [QQ' QQ]; subst. *)
      (* apply seq_eqv_r in QQ. destruct QQ as [COXY TCUR]. *)
      (* red in TCUR. destruct TCUR as [z CCUR]. red in CCUR. *)
      (* hahn_rewrite <- seqA in CCUR. *)
      (* apply seq_eqv_r in CCUR. destruct CCUR as [URR COVZ]. *)
      (* apply seq_eqv_r in URR. destruct URR as [URR II]. *)
      (* eapply eco_urr_irr with (sc:=sc); eauto. *)
      (* 1-3: by apply IMMCON. *)
      (* exists y. split. *)
      (* { apply co_in_eco. apply COXY. } *)
      (* apply urr_hb. exists z. split; eauto. *)
      (* right. apply sb_in_hb. *)
      (* assert (E z) as EZ. *)
      (* { apply TCCOH in COVZ. apply COVZ. } *)
      (* destruct II as [TIDZ|INITZ]. *)
      (* 2: by apply init_ninit_sb; auto. *)
      (* destruct (@same_thread G x z) as [[|SB]|SB]; auto. *)
      (* { desf. } *)
      (* exfalso. apply WNCOV. apply TCCOH in COVZ. *)
      (* apply COVZ. eexists. apply seq_eqv_r; eauto. } *)
    splits; eauto.
    { by rewrite upds, updo, upds. }
    { by rewrite upds. }
    { admit. }
    { rewrite upds. admit. }
    { rewrite upds. admit. }
    { eapply f_to_coherent_mori; [|by apply FCOH_NEW].
      rewrite NONEXT. clear. basic_solver. }

    exists promises'; exists memory'. unfold rel', rel'' in *.
    splits; auto.
    all: try (rewrite upds; (try rewrite (fun x y => updo x y NEQNEXT));
      (try rewrite upds); auto).
    { constructor; auto. admit. }
    { red. rewrite upds. splits; eauto.
      red. ins. admit. }
    (* { rewrite upds. cdes SIM_TVIEW. clear ACQ REL. *)
    (*   apply Time.join_spec. *)
    (*   2: { unfold TimeMap.singleton, LocFun.add. *)
    (*        rewrite Loc.eq_dec_eq. apply DenseOrder_le_PreOrder. } *)
    (*   apply Time.le_lteq. left. *)
    (*   apply TimeFacts.join_spec_lt; auto. *)
    (*   eapply TimeFacts.le_lt_lt. *)
    (*   2: by apply LEWPNTO. *)
    (*   destruct PREL0; desc. *)
    (*   { subst. simpls. apply Time.bot_spec. } *)
    (*   eapply max_value_leS with (w:=w); eauto. *)
    (*   { intros x [HH|HH]. *)
    (*     2: by desf. *)
    (*     unfold CombRelations.msg_rel, CombRelations.urr in HH. *)
    (*     hahn_rewrite seqA in HH. apply seq_eqv_l in HH. apply HH. } *)
    (*   { intros x [HH|HH]. *)
    (*     2: by desf. *)
    (*     eapply msg_rel_issued; eauto. *)
    (*     exists p. apply seq_eqv_r. split; eauto. } *)
    (*   split; [|basic_solver]. *)
    (*   intros x y QQ. apply seq_eqv_l in QQ. destruct QQ as [QQ' QQ]; subst. *)
    (*   apply seq_eqv_r in QQ. destruct QQ as [COXY [MSG|[MSG EQ]]]. *)
    (*   2: { subst. eapply WF.(co_irr). eapply WF.(co_trans). *)
    (*        { apply COXY. } *)
    (*        eapply rfrmw_in_im_co in INRMW; eauto. apply INRMW. } *)
    (*   assert (msg_rel locw ⨾ (rf ⨾ rmw) ⊆ msg_rel locw) as YY. *)
    (*   { unfold CombRelations.msg_rel, imm_s_hb.release, rs.  *)
    (*     rewrite !seqA. by rewrite rt_unit. } *)
    (*   assert (msg_rel locw y x) as MSGYX. *)
    (*   { apply YY. eexists. eauto. } *)
    (*   unfold CombRelations.msg_rel in MSGYX. *)
    (*   destruct MSGYX as [z [URR RELES]]. *)
    (*   eapply release_co_urr_irr; eauto. *)
    (*   1-4: by apply IMMCON. *)
    (*   eexists; split; [|eexists; split]; eauto. } *)
    (* { ins. rewrite updo; auto. by intros HH; subst. } *)
    (* { ins. destruct ISS as [ISS NEQ]. *)
    (*   rewrite updo. *)
    (*   2: by intros HH; subst. *)
    (*   rewrite updo; auto. } *)
    (* { etransitivity; eauto. *)
    (*   arewrite (set_compl (issued T ∪₁ eq w) ⊆₁ set_compl (issued T)); [|done]. *)
    (*   basic_solver. } *)
    (* { etransitivity; eauto. *)
    (*   basic_solver. } *)
    (* destruct (Rel w); simpls. *)
    (* apply SIM_HELPER; auto. by ins; rewrite updo; auto; intros H; subst. } *)
    admit. }

    assert (f_to wprev <> f_from wnext) as FFNEQ.
    { intros HH.
      cdes RESERVED_TIME.
      apply TFRMW in HH; auto.
      eapply rfrmw_in_im_co in HH; eauto.
        by eapply HH; [apply COPREV|]. }

    assert (Time.lt (f_to wprev) (f_from wnext)) as FFLT.
    { clear -FFLE FFNEQ. apply Time.le_lteq in FFLE. desf. }

    cdes RESERVED_TIME. desc.
    set (n_to := Time.middle (f_to wprev) (f_from wnext)).
    set (f_to' := upd f_to w n_to).
    exists f_to'.

    set (B := (rf ⨾ rmw) wprev w).
    assert (exists n_from,
               ⟪ NFROM : (n_from = f_to wprev /\ B) \/
                         (n_from = Time.middle (f_to wprev) n_to /\ ~B) ⟫)
      as [n_from NFROM].
    { by destruct (classic B); eexists; [left|right]. }
    set (f_from' := upd f_from w n_from).
    exists f_from'.

    assert (~ is_init wnext) as NINITWNEXT.
    { apply no_co_to_init in CONEXT; auto.
      2: { apply coherence_sc_per_loc. apply IMMCON. }
      apply seq_eqv_r in CONEXT. desf. }

    assert (forall to from msg,
               Memory.get locw to (Configuration.memory PC) = Some (from, msg) ->
               Interval.disjoint (f_from' w, f_to' w) (from, to)) as DISJOINT.
    { ins. unfold f_to', f_from'; rewrite !upds.
      apply Interval.le_disjoint with (b:= (f_to wprev,f_from wnext)); auto.
      2: { eapply f_to_coherent_add_S_middle with (S:=S); eauto. }
      eapply co_S_memory_disjoint; eauto. }

    assert (Time.lt (f_to wprev) n_to) as LTNTO.
    { subst n_to. by apply DenseOrder.middle_spec. }

    assert (Time.lt (f_to' wprev) (f_to' w)) as PREVNLT.
    { unfold f_to'. rewrite upds, updo; auto. }

    assert (Time.le (View.rlx rel'' locw)
                    (View.rlx (TView.cur (Local.tview local)) locw)) as GG.
    { unfold rel''. destruct (Rel w).
      { reflexivity. }
      subst. eapply rel_le_cur; eauto. }

    assert (Time.lt (View.rlx rel'' locw) (f_to' w)) as REL_VIEW_LT.
    { eapply TimeFacts.le_lt_lt; eauto.
      eapply TimeFacts.le_lt_lt.
      2: by apply PREVNLT.
      unfold f_to'. rewrite updo; auto.
      cdes SIM_TVIEW. cdes CUR.
      eapply max_value_leS with (w:=w).
      9: by apply CUR0.
      all: eauto.
      { intros HH. apply WNISS. eapply t_cur_covered; eauto. }
      { unfold t_cur, c_cur, CombRelations.urr.
        rewrite !seqA. rewrite dom_eqv1.
          by intros x [[_ YY]]. }
      { rewrite <- ETCCOH.(etc_I_in_S). apply t_cur_covered; eauto. }
      split; [|basic_solver].
      intros x y QQ. apply seq_eqv_l in QQ. destruct QQ as [QQ' QQ]; subst.
      apply seq_eqv_r in QQ. destruct QQ as [COXY TCUR].
      red in TCUR. destruct TCUR as [z CCUR]. red in CCUR.
      hahn_rewrite <- seqA in CCUR.
      apply seq_eqv_r in CCUR. destruct CCUR as [URR COVZ].
      apply seq_eqv_r in URR. destruct URR as [URR II].
      eapply eco_urr_irr with (sc:=sc); eauto.
      1-3: by apply IMMCON.
      exists y. split.
      { apply co_in_eco. apply COXY. }
      apply urr_hb. exists z. split; eauto.
      right. apply sb_in_hb.
      assert (E z) as EZ.
      { apply TCCOH in COVZ. apply COVZ. }
      destruct II as [TIDZ|INITZ].
      2: by apply init_ninit_sb; auto.
      destruct (@same_thread G x z) as [[|SB]|SB]; auto.
      { desf. }
      exfalso. apply WNCOV. apply TCCOH in COVZ.
      apply COVZ. eexists. apply seq_eqv_r; eauto. }

    assert (Time.le (View.rlx rel'' locw) (f_to' w)) as REL_VIEW_LE.
    { apply Time.le_lteq. eauto. }
    
    set (rel' := View.join (View.join rel'' (View.unwrap p_rel))
                           (View.singleton_ur locw (f_to' w))).
    assert (Time.le (View.rlx (View.unwrap p_rel) locw) (f_to' w)) as PREL_LE.
    { subst. apply Time.bot_spec. }

    assert (View.pln rel'' = View.rlx rel'') as RELPLN''.
    { subst rel''. destruct (Rel w); apply PLN_RLX_EQ. }

    assert (Message.wf (Message.full valw (Some rel'))) as WFREL'.
    { do 3 constructor.
      subst rel'. subst. simpls. rewrite RELPLN''. reflexivity. }

    edestruct (@Memory.add_exists (Local.promises local) locw (f_from' w) (f_to' w)
                                  (Message.full valw (Some rel')))
      as [promises' PADD]; eauto.
    { ins. eapply DISJOINT.
      eapply PROM_IN_MEM; eauto. }
    { unfold f_from', f_to'. rewrite !upds.
      eapply f_to_coherent_add_S_middle with (S:=S); eauto. }

    edestruct (@Memory.add_exists PC.(Configuration.memory)
                                  locw (f_from' w) (f_to' w)
                                  (Message.full valw (Some rel')))
      as [memory' MADD]; eauto.
    { unfold f_from', f_to'. rewrite !upds.
      eapply f_to_coherent_add_S_middle with (S:=S); eauto. }
    
    assert (f_to_coherent G (S ∪₁ eq w) f_to' f_from') as FCOH_NEW.
    { unfold f_to', f_from'.
      eapply f_to_coherent_add_S_middle; eauto. }

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

  assert (View.pln rel'' = View.rlx rel'') as RELPLN''.
  { subst rel''. destruct (Rel w); apply PLN_RLX_EQ. }

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
Admitted.

End Aux.
