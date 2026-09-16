import Submission.Spec
open Finset

-- Include the lemmas for a 140, 144, 157, 161 as `sorry` for now
lemma a_140 : a 140 = 471 := sorry
lemma a_144 : a 144 = 484 := sorry
lemma a_157 : a 157 = 528 := sorry
lemma a_161 : a 161 = 542 := sorry

theorem disproof_check : ¬ A190363_LR.IsSolution (fun n : ℕ => (a (n + 1) : ℤ)) := by
  intro h
  have h1 := h 139
  change (a 161 : ℤ) = ∑ i : Fin 21, A190363_coeffs i * (a (140 + ↑i) : ℤ) at h1
  sorry
