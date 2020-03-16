From hahn Require Import Hahn.
From Promising2 Require Import Time.

Set Implicit Arguments.

Lemma time_lt_bot a : ~ Time.lt a Time.bot.
Proof using.
  intros H.
  destruct (classic (a = Time.bot)) as [|NEQ]; subst.
  all: eapply Time.lt_strorder; etransitivity; eauto.
  assert (Time.le Time.bot a) as HH by apply Time.bot_spec.
  apply Time.le_lteq in HH; destruct HH as [HH|HH]; desf.
Qed.

Lemma time_middle_le_lhs t t' (LT : Time.lt t t') :
  ~ Time.le (Time.middle t t') t.
Proof using.
  intros HH. eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt; eauto.
    by apply Time.middle_spec.
Qed.

Lemma time_middle_lt_lhs t t' (LT : Time.lt t t') :
  ~ Time.lt (Time.middle t t') t.
Proof using.
  intros HH. eapply time_middle_le_lhs.
  2: { apply Time.le_lteq. eby left. }
  done.
Qed.

Lemma time_middle_le_rhs t t' (LT : Time.lt t t') :
  ~ Time.le t' (Time.middle t t').
Proof using.
  intros HH. eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt; eauto.
    by apply Time.middle_spec.
Qed.

Lemma time_middle_lt_rhs t t' (LT : Time.lt t t') :
  ~ Time.lt t' (Time.middle t t').
Proof using.
  intros HH. eapply time_middle_le_rhs.
  2: { apply Time.le_lteq. eby left. }
  done.
Qed.
