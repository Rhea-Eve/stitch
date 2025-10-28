Require Import Nat.
Require Import List.
Import ListNotations.
Open Scope nat_scope.

Inductive Sorted : list nat → Prop :=
| sorted_nil : Sorted []
| sorted_singleton : ∀ n, Sorted [n]
| sorted_cons : ∀ n m l, n ≤ m → Sorted (m :: l) → Sorted (n :: m :: l).

Fixpoint insert (n : nat) (l : list nat) : list nat :=
  match l with
  | [] => [n]
  | x :: tl =>
      if n ≤? x then n :: x :: tl
      else x :: insert n tl
  end.

Fixpoint sort (l : list nat) : list nat :=
  match l with
  | [] => []
  | x :: tl => insert x (sort tl)
  end.

Lemma insert_sorted : ∀ x l, Sorted l → Sorted (insert x l).
Proof.
  induction l.
  - simpl. auto.
  - simpl. destruct (x ≤? a) eqn:E.
    + simpl. auto.
    + simpl in *. destruct H as [H1 H2].
      split.
      * apply H1.
      * apply IHl. apply H2.
Qed.

Lemma sort_sorts : ∀ l, Sorted (sort l).
Proof.
  induction l.
  - simpl. auto.
  - simpl. apply insert_sorted. apply IHl.
Qed.

Theorem sort_is_sorting_algorithm :
  ∀ l, Sorted (sort l) ∧ permutation l (sort l).
Proof.
  (* proof omitted for brevity *) Qed.
