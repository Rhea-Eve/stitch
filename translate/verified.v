Require Import Arith.
Require Import Coq.Init.Nat.

(* inc_verified returns n+1 together with a proof that the result = n+1 *)
Definition inc_verified (n : nat)
  : { m : nat | m = n + 1 } :=
  exist _ (S n)
        eq_refl.
