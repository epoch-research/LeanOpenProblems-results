import FormalConjectures.Util.ProblemImports
open scoped Nat.Prime

def a (n : ℕ) : ℕ :=
  Finset.card $ (Finset.Icc 1 n).filter fun k : ℕ =>
    let m := π (π (k * n))
    m.sqrt ^ 2 = m

example (n : ℕ) (hn : n > 0)
    (H : ∃ k, 1 ≤ k ∧ k ≤ n ∧ (π (π (k * n))).sqrt ^ 2 = π (π (k * n))) : a n > 0 := by
  rcases H with ⟨k,hk1,hkn,hsq⟩
  unfold a
  exact Finset.card_pos.mpr ⟨k, by simp [hk1, hkn, hsq]⟩
