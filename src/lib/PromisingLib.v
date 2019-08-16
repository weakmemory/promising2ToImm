From hahn Require Import Hahn.
From PromisingLib Require Export Basic DenseOrder Loc Language.

(* WARNING, TODO:
  This lemma has to be deleted since it doesn't hold!
 *)
Lemma loc_to_floc (l : Loc.t) : exists (fl : FLoc.t), << FEQ : FLoc.loc fl = l >>.
Proof. Admitted.
