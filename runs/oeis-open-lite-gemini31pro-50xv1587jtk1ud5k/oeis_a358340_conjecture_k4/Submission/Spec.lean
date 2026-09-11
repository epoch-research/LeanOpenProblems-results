import FormalConjectures.Util.ProblemImports

open Nat List Set

def is_zeroless (k : ℕ) : Prop := 0 ∉ Nat.digits 10 k

def is_n_digit (m n : ℕ) : Prop := 10^(n-1) ≤ m ∧ m < 10^n

noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else
  let S : Set ℕ := { m : ℕ | is_n_digit m n ∧ is_zeroless (m ^ 4) }
  sInf S

theorem oeis_a358340_conjecture_k4 : Set.Infinite { m : ℕ | is_zeroless (m ^ 4) } := by
  sorry

theorem oeis_a358340_conjecture_k4.disproof : ¬ (type_of% @oeis_a358340_conjecture_k4) := by
  sorry
