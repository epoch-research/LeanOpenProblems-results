import Mathlib

lemma W_eq_one (p q : ℕ) (h_gap : q - p = 2) :
  Finset.prod (Finset.Icc (p + 1) (q - 2)) id = 1 := by
  have : q - 2 = p := by omega
  rw [this]
  have empty_Icc : Finset.Icc (p + 1) p = ∅ := Finset.Icc_eq_empty (by omega)
  rw [empty_Icc]
  rfl
