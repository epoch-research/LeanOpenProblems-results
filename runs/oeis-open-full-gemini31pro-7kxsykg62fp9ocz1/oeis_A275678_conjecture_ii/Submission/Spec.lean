import FormalConjectures.Util.ProblemImports
open Nat

def A275678 (n : ℕ) : ℕ :=
  let B := n + 1
  Finset.sum (Finset.range B) fun k =>
  Finset.sum (Finset.range B) fun x =>
  Finset.sum (Finset.range B) fun y =>
    if x ≤ y then
      let P_term := 4^k * (1 + 4 * x^2 + y^2)
      if P_term ≤ n then
        let r := n - P_term
        let z_candidate := r.sqrt
        if z_candidate ^ 2 = r then 1 else 0
      else 0
    else 0

theorem oeis_A275678_conjecture_ii (n : ℕ) (hn : n > 0) :
  ∃ k x y z : ℕ, n = 4^k * (1 + 4 * x^2 + y^2) + z^2 ∧ x ≤ z := by
  sorry

theorem oeis_A275678_conjecture_ii.disproof : ¬ (type_of% @oeis_A275678_conjecture_ii) := by
  sorry
