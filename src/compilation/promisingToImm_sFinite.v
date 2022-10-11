
(* TODO: remove? *)
Lemma unused_thread:
  exists thread', acts_set G ∩₁ Tid_ thread' ≡₁ ∅. 
Proof using WF FIN_THREADS. 
  destruct FIN_THREADS as [threads THREADS].
  exists (BinPos.Pos.of_nat (list_max (map BinPos.Pos.to_nat threads) + 1)).
  split; [| basic_solver].
  unfolder. ins. desc. apply wf_threads, THREADS in H; auto.
  apply (@f_equal _ _ BinPos.Pos.to_nat) in H0.
  rewrite Pnat.Nat2Pos.id in H0; [| lia].
  forward eapply In_gt_list_max with (l := map BinPos.Pos.to_nat threads)
                                     (n := BinPos.Pos.to_nat (tid x)) as NIN.
  { lia. }
  destruct NIN. eapply in_map_iff; eauto.
Qed. 

Lemma simulation_finite
      (FAIR: mem_fair G)
      (FIN: fin_exec G) :
  exists T PC f_to f_from,
    ⟪ FINALT : acts_set G ⊆₁ covered T ⟫ /\
    ⟪ PSTEP  : conf_step＊ (conf_init prog) PC ⟫ /\
    ⟪ SIMREL : simrel G sc PC T f_to f_from ⟫.
Proof using All.
      (*  *)
      (* (IMM_FAIR: imm_fair G sc): *)
  assert (complete G) as CG by apply IMMCON.
  assert (wf_sc G sc) as WFSC by apply IMMCON.
  (* generalize (sim_traversal WF WFSC CG FIN IMMCON); ins; desc. *)
    
  forward eapply simrel_init as SI.
  (* TODO: write a version sim_step_cov_full_traversal for general traversal
     (without thread argument) *)
  forward eapply sim_step_cov_full_traversal with (T := init_tls G) as T; eauto.
  all: try by apply SI. 
  { apply fin_exec_imm_s_fair; auto. }
  { admit. }

  destruct T as [T S].
  exists T, S.
  apply rtE in H.
  destruct H as [H|H].
  { red in H. desf.
    eexists. eexists. eexists.
    splits; auto.
    { apply rtE. left. red. eauto. }
    unfold ext_init_trav in *. inv H.
    apply simrel_init. }
  apply inclusion_t_rt in H.
  eapply sim_steps in H; eauto.
  3: { by apply simrel_init. }
  2: { by apply init_etc_fin. }
  desf.
  eexists. eexists. eexists.
  splits; eauto.
Qed.