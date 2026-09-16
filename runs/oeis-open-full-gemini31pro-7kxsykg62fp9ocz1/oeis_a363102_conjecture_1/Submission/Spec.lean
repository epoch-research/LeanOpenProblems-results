import FormalConjectures.Util.ProblemImports

open Nat Finset

def a051403 (n : ℕ) : ℕ :=
  let fact_sum := Finset.sum (range (n + 1)) (fun k => k.factorial)
  ((n + 2) * fact_sum) / 2

def a (n : ℕ) : ℕ :=
  let num : ℕ := n ^ 2 - 2
  let a051403_nm3 := a051403 (n - 3)
  let a051403_nm4 := a051403 (n - 4)
  let denom_arg := 2 * a051403_nm3 + n * a051403_nm4
  num / Nat.gcd num denom_arg

theorem oeis_a363102_conjecture_1 :
  ∀ n : ℕ, 3 ≤ n → a n = 1 ∨ Nat.Prime (a n) := sorry

theorem oeis_a363102_conjecture_1.disproof : ¬ (type_of% @oeis_a363102_conjecture_1) := by
  sorry
