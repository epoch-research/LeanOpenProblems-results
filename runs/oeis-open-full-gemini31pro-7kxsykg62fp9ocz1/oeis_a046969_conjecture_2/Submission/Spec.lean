import FormalConjectures.Util.ProblemImports
open Rat Nat

noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let m := 2 * n
    let k := m * (m - 1)
    (bernoulli m / (k : ℚ)).den

theorem oeis_a046969_conjecture_2 (n : ℕ) :
    2 ≤ n →
    (a n) % 12 = 0 →
    Nat.Prime ((a n) / 12) →
    (a (n - 1)) % 12 = 0 →
    (a (n + 2)) % 12 = 0 →
    6 ∣ (((a (n - 1)) / 12 : ℤ) - ((n - 1) : ℤ)) ∧
    6 ∣ (((a n) / 12 : ℤ) - (n : ℤ)) ∧
    6 ∣ (((a (n + 2)) / 12 : ℤ) - ((n + 2) : ℤ)) := by
  sorry

theorem oeis_a046969_conjecture_2.disproof : ¬ (type_of% @oeis_a046969_conjecture_2) := by
  sorry
