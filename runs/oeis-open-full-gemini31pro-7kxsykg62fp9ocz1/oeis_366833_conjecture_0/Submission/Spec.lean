import FormalConjectures.Util.ProblemImports

open Nat Classical

noncomputable def A366833 (n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else
    let p_n   : ℕ := Nat.nth Nat.Prime (n - 1)
    let p_np1 : ℕ := Nat.nth Nat.Prime n
    let count_prime_powers : ℕ :=
      Finset.card ((Finset.Icc p_n p_np1).filter IsPrimePow)
    count_prime_powers - 1

theorem oeis_366833_conjecture_0 : ∀ (n : ℕ), 1 ≤ n → A366833 n ∈ ({1, 2, 3} : Finset ℕ) := sorry
theorem oeis_366833_conjecture_0.disproof : ¬ (type_of% @oeis_366833_conjecture_0) := sorry
