import Submission.Spec
open Finset

lemma a_140 : a 140 = 471 := sorry
lemma a_144 : a 144 = 484 := sorry
lemma a_157 : a 157 = 528 := sorry
lemma a_161 : a 161 = 542 := sorry

theorem expand_sum (f : Fin 21 → ℤ) : ∑ i : Fin 21, A190363_coeffs i * f i =
      - f 0 + f 4 + f 17 := by
  have : (univ : Finset (Fin 21)) = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20} := rfl
  rw [this]
  simp [A190363_coeffs]
  ring

theorem disproof_check : ¬ A190363_LR.IsSolution (fun n : ℕ => (a (n + 1) : ℤ)) := by
  intro h
  have h1 := h 139
  change (a 161 : ℤ) = ∑ i : Fin 21, A190363_coeffs i * (a (139 + 1 + ↑i) : ℤ) at h1
  have h2 : (fun i : Fin 21 => (a (139 + 1 + ↑i) : ℤ)) = (fun i : Fin 21 => (a (140 + ↑i) : ℤ)) := by
    ext i
    congr 1
    omega
  -- Actually, `139 + 1 + ↑i` is just `140 + ↑i`.
  -- We can just do `have h1 := h 139` and `dsimp at h1`.
  sorry
