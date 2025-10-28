(* You need MetaCoq installed. This file assumes Coq + MetaCoq is available. *)

From MetaCoq.Template Require Import All.
Require Import String List.
Import ListNotations.
Open Scope string_scope.

Require Import pipeline.verified.  (* adjust if Coq can't find it; sometimes it's just Require Import verified. *)

(* Step 1: Quote the definition *)
MetaCoq Quote Definition q_inc_verified := inc_verified.

(* q_inc_verified : term
   This is the AST (lambda calculus style) that represents inc_verified.
*)

(* Step 2: For development/debugging:
   We define a function to pretty-print a tiny subset of terms into a super simple S-expression-ish string.
   We'll ONLY handle what we know we used: tLambda, tApp, tConst, tRel, tConstruct.
*)

Fixpoint show_term (t : term) : string :=
  match t with
  | tRel n =>
      (* de Bruijn index. we'll just print "#<n>" *)
      ("#" ++ string_of_nat n)
  | tVar id =>
      id
  | tConst kn _ =>
      (* kernel name, we just show the last part *)
      let '(mkKerName mp id) := kn in
      id
  | tLambda na ty body =>
      (* (lam (x BODY)) – we throw away type for now *)
      let x :=
        match na with
        | nNamed nm => nm
        | nAnon => "anon"
        end in
      "(lam (" ++ x ++ " " ++ show_term body ++ "))"
  | tApp f a =>
      "(" ++ show_term f ++ " " ++ show_term a ++ ")"
  | tConstruct (mkInd kername idx) c u =>
      (* constructors like "exist" live here *)
      let '(mkKerName _ cname) := kername in
      "(" ++ cname ++ ")" (* super naive; we'll refine in python *)
  | tInd (mkInd kn idx) u =>
      let '(mkKerName _ cname) := kn in
      cname
  | tProd na ty body =>
      (* we ignore for now *)
      "/*prod*/"
  | tLetIn na val ty body =>
      "/*let*/"
  | tCase _p _ret _scrut _branches =>
      "/*match*/"
  | tFix _ _ =>
      "/*fix*/"
  | _ =>
      "/*unhandled*/"
  end.

(* Step 3: spit the string out so you can copy it *)
MetaCoq Run (tmPrint q_inc_verified).
MetaCoq Run (tmMsg (show_term q_inc_verified)).
