From MetaCoq.Template Require Import All.

Definition inc (n : nat) := S n.

MetaCoq Quote Definition q_inc_shallow := inc.
Print q_inc_shallow.

(* Correct syntax for TemplateMonad sequencing in Coq 8.17 *)
MetaCoq Run (
  t <- tmQuoteRec inc ;;
  tmMsg "=== Full quoted AST ===" ;;
  tmPrint t
).
