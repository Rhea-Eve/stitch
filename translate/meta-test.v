From MetaCoq.Template Require Import All.

Definition inc (n : nat) := S n.

MetaCoq Run (tmQuoteRec (fun p => tmPrint p) inc).

(* Alternatively, explicitly quote the lambda term *)
MetaCoq Quote Recursively Definition q_inc := inc.
Print q_inc.
