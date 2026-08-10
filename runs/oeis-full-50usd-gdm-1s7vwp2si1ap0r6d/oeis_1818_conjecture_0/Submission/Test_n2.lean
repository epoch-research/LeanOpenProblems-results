import Mathlib

open Nat Finset Matrix

def a (n : ℕ) : ℕ :=
  ((range n).prod (fun k => 2 * k + 1)) ^ 2

lemma permanent_four (M : Matrix (Fin 4) (Fin 4) ℂ) :
    permanent M =
      M 0 0 * M 1 1 * M 2 2 * M 3 3 +
      M 0 0 * M 1 1 * M 2 3 * M 3 2 +
      M 0 0 * M 1 2 * M 2 1 * M 3 3 +
      M 0 0 * M 1 2 * M 2 3 * M 3 1 +
      M 0 0 * M 1 3 * M 2 1 * M 3 2 +
      M 0 0 * M 1 3 * M 2 2 * M 3 1 +
      M 0 1 * M 1 0 * M 2 2 * M 3 3 +
      M 0 1 * M 1 0 * M 2 3 * M 3 2 +
      M 0 1 * M 1 2 * M 2 0 * M 3 3 +
      M 0 1 * M 1 2 * M 2 3 * M 3 0 +
      M 0 1 * M 1 3 * M 2 0 * M 3 2 +
      M 0 1 * M 1 3 * M 2 2 * M 3 0 +
      M 0 2 * M 1 0 * M 2 1 * M 3 3 +
      M 0 2 * M 1 0 * M 2 3 * M 3 1 +
      M 0 2 * M 1 1 * M 2 0 * M 3 3 +
      M 0 2 * M 1 1 * M 2 3 * M 3 0 +
      M 0 2 * M 1 3 * M 2 0 * M 3 1 +
      M 0 2 * M 1 3 * M 2 1 * M 3 0 +
      M 0 3 * M 1 0 * M 2 1 * M 3 2 +
      M 0 3 * M 1 0 * M 2 2 * M 3 1 +
      M 0 3 * M 1 1 * M 2 0 * M 3 2 +
      M 0 3 * M 1 1 * M 2 2 * M 3 0 +
      M 0 3 * M 1 2 * M 2 0 * M 3 1 +
      M 0 3 * M 1 2 * M 2 1 * M 3 0 := by
  unfold permanent
  decide
