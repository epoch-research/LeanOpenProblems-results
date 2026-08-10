import FormalConjectures.Util.ProblemImports

open scoped Nat.Prime

def a_test (n : ℕ) : ℕ :=
  Finset.card $ (Finset.Icc 1 n).filter fun k : ℕ =>
    let m := π (π (k * n))
    m.sqrt ^ 2 = m

theorem a_test_pos_of_exists (n : ℕ) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ n)
    (h_sq : let m := π (π (k * n)); m.sqrt ^ 2 = m) : a_test n > 0 := by
  unfold a_test
  apply Finset.card_pos.mpr
  use k
  rw [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨hk1, hk2⟩, h_sq⟩
