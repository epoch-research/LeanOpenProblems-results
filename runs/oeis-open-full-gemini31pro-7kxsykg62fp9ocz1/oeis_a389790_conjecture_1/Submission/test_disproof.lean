import FormalConjectures.Util.ProblemImports
open Classical
open Nat

noncomputable def next_prime (r : ℕ) : ℕ :=
  sInf {k : ℕ | Nat.Prime k ∧ r < k}

noncomputable def S_sum (r : ℕ) : ℕ := r + next_prime r

noncomputable def a (n : ℕ) : ℕ :=
  let target := 2 * n
  let R := Finset.range n
  Finset.card $ Finset.filter (fun ⟨p, q⟩ =>
    Nat.Prime p ∧ Nat.Prime q ∧ p ≤ q ∧ S_sum p + S_sum q = target
  ) (R ×ˢ R)

theorem oeis_a389790_conjecture_1 : ∀ n : ℕ, 474 ≤ n → 0 < a n := sorry

lemma empty_filter_prop (n : ℕ) (h : ∀ p q, p < n → q < n → Nat.Prime p → Nat.Prime q → p ≤ q → S_sum p + S_sum q ≠ 2 * n) : Finset.filter (fun x : ℕ × ℕ => Nat.Prime x.1 ∧ Nat.Prime x.2 ∧ x.1 ≤ x.2 ∧ S_sum x.1 + S_sum x.2 = 2 * n) (Finset.range n ×ˢ Finset.range n) = ∅ := by
  sorry

theorem a_473 : a 473 = 0 := by
  sorry

