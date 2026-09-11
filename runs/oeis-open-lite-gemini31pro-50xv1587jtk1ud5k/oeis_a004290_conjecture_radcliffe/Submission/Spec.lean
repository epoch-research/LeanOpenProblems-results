import FormalConjectures.Util.ProblemImports
import Mathlib

open Nat List Set

noncomputable def A004290 (n : ℕ) : ℕ :=
  let S := { m : ℕ | 0 < m ∧ n ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 }
  sInf S

theorem oeis_a004290_conjecture_radcliffe (k : ℕ) (hk : k > 0) :
  (A004290 (10 ^ k) = 10 ^ k) ∧
  (A004290 (10 ^ k - 1) = (10 ^ (9 * k) - 1) / 9) ∧
  (∀ n : ℕ, n < 10 ^ k - 1 → A004290 n < A004290 (10 ^ k - 1)) :=
by
  sorry

theorem oeis_a004290_conjecture_radcliffe.disproof : ¬ (type_of% @oeis_a004290_conjecture_radcliffe) :=
by
  sorry
