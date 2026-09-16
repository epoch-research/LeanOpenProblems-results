import FormalConjectures.Util.ProblemImports

def A120424 : ℕ → ℕ
| 0     => 1
| 1     => 3
| n + 2 =>
  let f (x : ℕ) : ℕ := if x % 2 = 0 then x / 2 else x
  f (A120424 (n + 1)) + f (A120424 n)

theorem oeis_a120424_conjecture_0 :
  ({n : ℕ | A120424 n % 2 = 0}).HasDensity (1/2 : ℝ) ∧
  Set.Infinite { n : ℕ | A120424 (n + 1) = A120424 n + 1 ∨ A120424 n = A120424 (n + 1) + 1 } := by
  sorry

theorem oeis_a120424_conjecture_0.disproof : ¬ (type_of% @oeis_a120424_conjecture_0) := by
  sorry
