import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

def A357674 (n : ℕ) : ℕ :=
  let S1 : ℕ := Finset.sum (range (2 * n + 1)) (fun k => (n + k - 1).choose k)
  let S2 : ℕ := Finset.sum (range (2 * n + 1)) (fun k => ((n + k - 1).choose k) ^ 2)
  S1 ^ 4 * S2 ^ 3

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem A357674_conjecture_1 (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) (h : p ≤ 500) :
    A357674 p ≡ A357674 1 [MOD p ^ 5] := by
  interval_cases p
  all_goals
    first
    | decide
    | exfalso; revert hp; decide
