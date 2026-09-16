import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ :=
  let valid_x_range := Finset.Icc 1 (n / 2)
  valid_x_range.filter (fun x : ℕ => Nat.Prime ((x * (n - x)) ^ 2 + 1)) |>.card

theorem oeis_219791_conjecture_2 :
  ∀ (k : ℕ), 0 < k →
    ∃ (N : ℕ), ∀ (n : ℕ), N ≤ n →
      ∃ (x y : ℕ), 0 < x ∧ 0 < y ∧ x + y = n ∧ Nat.Prime ((x * y) ^ (2^k) + 1) := sorry

theorem oeis_219791_conjecture_2.disproof : ¬ (type_of% @oeis_219791_conjecture_2) :=
  fun h => h _
