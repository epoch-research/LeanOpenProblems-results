import Submission.CumulativeVariation

/-! Finite cumulative-mass transfer with an explicit endpoint jump. The
strict cutoff is intentional, and its atom is not silently discarded. -/
namespace Erdos970.FiniteSelberg
open Finset Real MeasureTheory
variable {ι : Type*} [Fintype ι]

noncomputable def jumpProfile (L c : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x < L then c + ∫ t in x..L, g t else 0

lemma jumpProfile_split (L c : ℝ) (g : ℝ → ℝ) (x : ℝ) :
    jumpProfile L c g x = (if x < L then c else 0) +
      if x ≤ L then (∫ t in x..L, g t) else 0 := by
  unfold jumpProfile
  by_cases hx : x < L
  · simp only [if_pos hx, if_pos hx.le]
  · simp only [if_neg hx]
    by_cases hxL : x = L
    · simp [hxL]
    · rw [if_neg (not_le.mpr (lt_of_le_of_ne (le_of_not_gt hx) (Ne.symm hxL)))]
      ring

theorem weighted_jump_integral (w a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (L c : ℝ) (hL : 0 ≤ L) (g : ℝ → ℝ)
    (hg : IntervalIntegrable g volume 0 L) :
    (∑ i, w i * jumpProfile L c g (a i)) =
      c * cumulativeMass w a L + (∫ t in 0..L, g t * cumulativeMass w a t) := by
  simp_rw [jumpProfile_split, mul_add]
  rw [sum_add_distrib]
  congr 1
  · unfold cumulativeMass
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    split_ifs <;> ring
  · exact weighted_profile_integral w a ha L hL g
      (fun x => if x ≤ L then (∫ t in x..L, g t) else 0) hg (fun _ _ => rfl)

/-- Total variation plus the endpoint jump controls the error. No continuity
  at the cutoff is assumed, and c may have either sign. -/
theorem weighted_jump_error (w a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (L c E : ℝ) (hL : 0 ≤ L) (g : ℝ → ℝ)
    (hg : IntervalIntegrable g volume 0 L)
    (hF : ∀ t ∈ Set.Icc 0 L, |cumulativeMass w a t - t| ≤ E) :
    |(∑ i, w i * jumpProfile L c g (a i)) -
      (c * L + ∫ t in 0..L, g t * t)| ≤
      E * (|c| + ∫ t in 0..L, |g t|) := by
  rw [weighted_jump_integral w a ha L c hL g hg]
  have hi := cumulative_integral_error w a L E hL g hg hF
  have he := mul_le_mul_of_nonneg_left (hF L ⟨hL, le_rfl⟩) (abs_nonneg c)
  have hid : c * cumulativeMass w a L + (∫ t in 0..L, g t * cumulativeMass w a t) -
      (c * L + ∫ t in 0..L, g t * t) =
      c * (cumulativeMass w a L - L) +
        ((∫ t in 0..L, g t * cumulativeMass w a t) - (∫ t in 0..L, g t * t)) := by ring
  rw [hid]
  apply (abs_add_le _ _).trans
  rw [abs_mul]
  nlinarith only [hi, he]

#print axioms weighted_jump_integral
#print axioms weighted_jump_error
end Erdos970.FiniteSelberg
