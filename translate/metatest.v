From MetaCoq.Template Require Import All.
Require Import String List Ascii DecimalString.
Import ListNotations.
Open Scope string_scope.

(* === Step 0: define a simple function to quote === *)
Definition inc (n : nat) := S n.

(* === Step 1: quote its definition === *)
MetaCoq Quote Definition q_inc := inc.

(* === Step 2: helper for printing nats as strings === *)
Fixpoint nat_to_string (n : nat) : string :=
  match n with
  | 0 => "0"
  | S n' => "S" ++ nat_to_string n'
  end.

(* === Step 3: pretty-printer for MetaCoq AST to Lisp syntax === *)
Fixpoint show_term (t : term) : string :=
  match t with
  | tRel n => nat_to_string n
  | tVar id => string_of_ident id
  | tConst kn _ => string_of_kername kn
  | tLambda na _ body =>
      let x :=
        match na with
        | nNamed nm => string_of_name nm
        | nAnon => "anon"
        end in
      "(lam (" ++ x ++ " " ++ show_term body ++ "))"
  | tApp f a =>
      "(" ++ show_term f ++ " " ++ show_term a ++ ")"
  | tConstruct ind _ _ =>
      string_of_kername (inductive_mind ind)
  | tInd ind _ =>
      string_of_kername (inductive_mind ind)
  | _ => "/*unhandled*/"
  end.

(* === Step 4: show AST and Lisp-like form === *)
MetaCoq Run (tmPrint q_inc).
MetaCoq Run (tmMsg (show_term q_inc)).
