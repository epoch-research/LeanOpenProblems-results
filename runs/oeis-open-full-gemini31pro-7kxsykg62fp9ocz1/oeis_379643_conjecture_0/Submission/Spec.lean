import FormalConjectures.Util.ProblemImports

open Nat Finset

noncomputable def a (n : ℕ) : ℤ :=
  if hn : n = 0 then 0 else
  let p_n : ℕ := Nat.nth Nat.Prime (n - 1)
  let count_primes_mod_b (b : ℕ) : ℕ :=
    ((Finset.range (p_n + 1)).filter (fun p => Nat.Prime p ∧ p % 8 = b)).card
  (count_primes_mod_b 3 : ℤ) - (count_primes_mod_b 7 : ℤ)

noncomputable def b (n : ℕ) : ℤ :=
  if hn : n = 0 then 0 else
  let p_n : ℕ := Nat.nth Nat.Prime (n - 1)
  let count_primes_mod_b (b : ℕ) : ℕ :=
    ((Finset.range (p_n + 1)).filter (fun p => Nat.Prime p ∧ p % 8 = b)).card
  (count_primes_mod_b 5 : ℤ) - (count_primes_mod_b 1 : ℤ)

theorem oeis_379643_conjecture_0 : ∀ (n : ℕ), 0 < n → ¬ (a n = 0 ∧ b n < 0) := by
  sorry

theorem oeis_379643_conjecture_0.disproof : ¬ (type_of% @oeis_379643_conjecture_0) := by
  sorry
