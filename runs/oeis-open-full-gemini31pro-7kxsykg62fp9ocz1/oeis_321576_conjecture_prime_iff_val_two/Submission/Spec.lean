import FormalConjectures.Util.ProblemImports

open Nat Set

noncomputable def a (n : ℕ) : ℕ :=
  if h_n : n > 0 then
    let S_n : Set ℕ :=
      { b | b > 1 ∧
          let k := b ^ n - (b - 1) ^ n
          ∀ (d : ℕ), d ∣ k → d ≡ 1 [MOD n] }
    sInf S_n
  else
    0

theorem oeis_321576_conjecture_prime_iff_val_two (n : ℕ) (h_n : n > 1) :
  a n = 2 ↔ Nat.Prime n :=
by sorry

theorem oeis_321576_conjecture_prime_iff_val_two.disproof : ¬ (type_of% @oeis_321576_conjecture_prime_iff_val_two) := by
  sorry
