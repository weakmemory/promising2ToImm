Require Import PArith Arith.
From hahn Require Import Hahn.
Require Import PromisingLib.
From Promising2 Require Import Configuration TView View Time Event Cell Thread Memory Local.

From imm Require Import AuxRel.
From imm Require Import AuxRel2.
From imm Require Import AuxDef. 
From imm Require Import TLSCoherency.
From imm Require Import IordCoherency.
From imm Require Import TlsEventSets.

Require Import ExtTraversalConfig.
Require Import SimulationRel.
Require Import SimState.

Lemma half_message_to_event_ta_propagate_irrelevance
  G memory T f_to f_from T'
  (ISS : issued   T' ≡₁ issued   T)
  (RES : reserved T' ≡₁ reserved T)
  (HMTE : half_message_to_event G T f_to f_from memory) : 
  half_message_to_event G T' f_to f_from memory.
Proof using.
  red; ins. red in HMTE.
  apply HMTE in MSG.
  desf; auto.
  exists b. splits; auto.
  { now apply RES. }
  intros AA. apply NOISS.
  now apply ISS.
Qed.

Lemma message_to_event_ta_propagate_irrelevance
  G memory T f_to f_from T'
  (ISS : issued   T' ≡₁ issued   T)
  (MTE : message_to_event G T f_to f_from memory) : 
  message_to_event G T' f_to f_from memory.
Proof using.
  red; ins. red in MTE.
  apply MTE in MSG.
  desf; auto.
  right. exists b. splits; auto.
  now apply ISS.
Qed.

Lemma reserved_time_ta_propagate_irrelevance
  G memory T f_to f_from smode T'
  (RTIME : reserved_time G T f_to f_from smode memory)
  (ISS : issued   T' ≡₁ issued   T)
  (RES : reserved T' ≡₁ reserved T) :
  reserved_time G T' f_to f_from smode memory.
Proof using.
  red. red in RTIME. do 2 desf.
  2: { splits; rewrite RES; auto. }
  splits.
  all: eauto using message_to_event_ta_propagate_irrelevance,
                   half_message_to_event_ta_propagate_irrelevance.
  intros x y XX YY.
  apply RES in XX.
  apply RES in YY.
  intuition.
Qed.

Lemma simrel_common_ta_propagate_irrelevance
  G sc PC T f_to f_from smode T'
  (COMMON : simrel_common G sc PC T f_to f_from smode)
  (TCOH : tls_coherent G T')
  (ICOH : iord_coherent G sc T')
  (RCOH : reserve_coherent G T')
  (COV : covered  T' ≡₁ covered  T)
  (ISS : issued   T' ≡₁ issued   T)
  (RES : reserved T' ≡₁ reserved T) :
  simrel_common G sc PC T' f_to f_from smode.
Proof using.
  red. splits; auto.
  all: rewrite ?COV, ?ISS, ?RES; try apply COMMON.
  3: { eapply reserved_time_ta_propagate_irrelevance; eauto.
       apply COMMON. }
  2: { ins. rewrite COV. now apply COMMON. }
  ins.
  assert (covered T r <-> covered T w) as AA by now apply COMMON.
  split; intros HH.
  all: apply set_subset_single_l.
  all: apply set_subset_single_l in HH.
  all: revert HH.
  all: rewrite ?COV, ?ISS, ?RES.
  all: generalize AA; clear; basic_solver.
Qed.

Lemma simrel_thread_local_ta_propagate_irrelevance
  G sc thread PC T f_to f_from smode T'
  (LOCAL : simrel_thread_local G sc PC T f_to f_from thread smode)
  (COV : covered T' ≡₁ covered T)
  (ISS : issued T' ≡₁ issued T)
  (RES : reserved T' ≡₁ reserved T) :
  simrel_thread_local G sc PC T' f_to f_from thread smode.
Proof using.
  red in LOCAL. desf.
  red. do 2 eexists; splits; eauto.
  all: try rewrite COV; auto.
  5: { eapply sim_state_more; eauto. }
  { red. ins. apply SIM_PROM in PROM. desf.
    eexists. splits; eauto.
    { now apply ISS. }
    intros HH. apply NCOV. now apply COV. }
  { red. ins. eapply SIM_RPROM in RES0. desf.
    eexists. splits; eauto.
    { now apply RES. }
    intros HH. apply NOISS. now apply ISS. }
  { red. ins. eapply SIM_MEM in VAL; eauto.
    2: now apply ISS.
    desf. destruct VAL as [AA BB]. desf. unnw.
    eexists. splits; eauto.
    intros CC DD. eapply BB0 in CC.
    2: { intros HH. apply DD. now apply COV. }
    desc. splits; auto.
    eexists. splits; eauto.
    destruct CC1 as [CC1|CC1]; [left|right].
    { desc. splits; eauto.
      intros HH. apply CC1.
      apply set_subset_single_l. rewrite <- ISS.
      generalize HH. clear. basic_solver. }
    desf. exists p. splits; eauto.
    now apply ISS. }
  red. ins. apply SIM_RES_MEM; auto.
  { now apply RES. }
  intros HH. apply NISSB. now apply ISS.
Qed.
