import FormalConjectures.Util.ProblemImports

open Classical
open Nat

noncomputable def next_prime (r : ℕ) : ℕ :=
  sInf {k : ℕ | Nat.Prime k ∧ r < k}

noncomputable def S_sum (r : ℕ) : ℕ := r + next_prime r

noncomputable def a (n : ℕ) : ℕ :=
  let target := 2 * n
  let R := Finset.range target
  Finset.card $ Finset.filter (fun pr : ℕ × ℕ =>
    let (p, q) := pr
    Nat.Prime p ∧ Nat.Prime q ∧ p ≤ q ∧ S_sum p + S_sum q = target
  ) (R ×ˢ R)

def is_conjectured_largest_value (n_max k : ℕ) : Prop :=
  a n_max = k ∧ ∀ n > n_max, a n ≠ k

theorem oeis_A389790_conjecture_max_n :
  is_conjectured_largest_value 833 2 ∧
  is_conjectured_largest_value 1487 3 ∧
  is_conjectured_largest_value 1411 4 ∧
  is_conjectured_largest_value 1523 5 ∧
  is_conjectured_largest_value 1747 6 ∧
  is_conjectured_largest_value 2621 7 ∧
  is_conjectured_largest_value 2153 8 ∧
  is_conjectured_largest_value 3091 9 ∧
  is_conjectured_largest_value 3238 10
:= by sorry

theorem oeis_A389790_conjecture_max_n.disproof : ¬ (type_of% @oeis_A389790_conjecture_max_n) := by
  sorry
