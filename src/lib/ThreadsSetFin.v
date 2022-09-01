(* TODO: replace Threadboundedexecution in imm with this *)
From hahn Require Import Hahn. 
From imm Require Import Execution.

Definition fin_threads G := set_finite (threads_set G).

