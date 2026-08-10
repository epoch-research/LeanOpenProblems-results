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
  have h_term : (fun k => if sqrt (totient k * totient (n - k)) ^ 2 = totient k * totient (n - k) then 1 else 0) k = 1 := by
    dsimp
    rw [if_pos h_sq]
  -- We want to show that a sum of non-negative terms with one term equal to 1 is positive.
  sorry
