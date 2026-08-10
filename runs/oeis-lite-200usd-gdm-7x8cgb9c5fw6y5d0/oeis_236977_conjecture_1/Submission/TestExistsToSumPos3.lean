import FormalConjectures.Util.ProblemImports

open Nat

def a (n : ℕ) : ℕ :=
  (Finset.Ico 1 ((n - 1) / 2 + 1)).sum fun k =>
    let m := totient k * totient (n - k)
    if sqrt m ^ 2 = m then 1 else 0

theorem a_pos_of_exists (n : ℕ) (k : ℕ) (hk : k ∈ Finset.Ico 1 ((n - 1) / 2 + 1))
    (h_sq : sqrt (totient k * totient (n - k)) ^ 2 = totient k * totient (n - k)) :
    a n > 0 := by
  dsimp [a]
  rw [← Finset.add_sum_erase (Finset.Ico 1 ((n - 1) / 2 + 1)) _ hk]
  rw [if_pos h_sq]
  have h_nonneg : ∑ x ∈ (Finset.Ico 1 ((n - 1) / 2 + 1)).erase k, (if sqrt (totient x * totient (n - x)) ^ 2 = totient x * totient (n - x) then 1 else 0) ≥ 0 := by
    apply Finset.sum_nonneg
    intro x _
    split_ifs <;> omega
  omega
