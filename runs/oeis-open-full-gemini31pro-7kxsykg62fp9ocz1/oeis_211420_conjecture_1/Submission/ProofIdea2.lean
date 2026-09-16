import Mathlib

open Nat

def D (n r : ℕ) : ℕ :=
  (List.range r).map (fun k => 8 * n - (2 * k + 1)) |>.prod

lemma D_eq (n r : ℕ) (h : 2 * r ≤ 8 * n) :
    D n r * 2^r * (4 * n).descFactorial r = (8 * n).descFactorial (2 * r) := by
  sorry
