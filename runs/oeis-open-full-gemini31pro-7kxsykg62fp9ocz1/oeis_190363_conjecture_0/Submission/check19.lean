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
  change (a 161 : ℤ) = ∑ i : Fin 21, A190363_coeffs i * (a (140 + ↑i) : ℤ) at h1
  rw [expand_sum (fun i => (a (140 + ↑i) : ℤ))] at h1
  have h_0 : (a (140 + ↑(0 : Fin 21)) : ℤ) = a 140 := by rfl
  have h_4 : (a (140 + ↑(4 : Fin 21)) : ℤ) = a 144 := by rfl
  have h_17 : (a (140 + ↑(17 : Fin 21)) : ℤ) = a 157 := by rfl
  rw [h_0, h_4, h_17] at h1
  rw [a_161, a_140, a_144, a_157] at h1
  norm_num at h1
