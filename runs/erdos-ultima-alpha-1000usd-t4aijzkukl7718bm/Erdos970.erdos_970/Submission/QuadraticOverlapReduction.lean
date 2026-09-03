import Submission.TripleCoverQuadratic
import Submission.HighMultiplicityPacking

/-! A trimmed quadratic probe. The high-overlap contribution is bounded by
incidence packing. The moderate-overlap mass is retained as an explicit term;
no estimate disposing of that term for arbitrary covers is asserted. -/
namespace Erdos970.QuadraticOverlap
open Finset HighMultiplicityPacking

noncomputable def moderatePositions (P : Finset ℕ) (r : ℕ → ℕ) (m B : ℕ) : Finset ℕ :=
  (range m).filter (fun x => 4 ≤ (hitPrimes P r x).card ∧ (hitPrimes P r x).card < B)

noncomputable def moderateMass (P : Finset ℕ) (r : ℕ → ℕ) (m B : ℕ) : ℝ :=
  ∑ x ∈ moderatePositions P r m B, ((hitPrimes P r x).card : ℝ) ^ 2

lemma moderateMass_nonneg (P : Finset ℕ) (r : ℕ → ℕ) (m B : ℕ) :
    0 ≤ moderateMass P r m B := sum_nonneg (fun x _ => sq_nonneg _)

lemma quadratic_probe_pointwise (H B : ℕ) (hH : 1 ≤ H) :
    ((H : ℝ) - 1) * ((H : ℝ) - 3) ≤
      (if 4 ≤ H ∧ H < B then (H : ℝ) ^ 2 else 0) +
      (if B ≤ H then (H : ℝ) ^ 2 else 0) := by
  have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
  by_cases h4 : 4 ≤ H
  · have hh : ((H : ℝ) - 1) * ((H : ℝ) - 3) ≤ (H : ℝ) ^ 2 := by nlinarith
    by_cases hB : H < B
    · simpa only [h4, hB, and_self, if_true, if_neg (by omega : ¬B ≤ H), add_zero] using hh
    · simpa only [h4, hB, and_false, if_false, if_pos (by omega : B ≤ H), zero_add] using hh
  · have h3 : (H : ℝ) ≤ 3 := by exact_mod_cast (show H ≤ 3 by omega)
    have hh : ((H : ℝ) - 1) * ((H : ℝ) - 3) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    simp only [h4, false_and, if_false, zero_add]
    exact hh.trans (by split_ifs <;> positivity)

/-- The pointwise comparison needed for applying high-multiplicity packing to
this particular probe. It is not a statement about arbitrary sieve polynomials. -/
lemma total_probe_le_split_mass (P : Finset ℕ) (r : ℕ → ℕ) (m B : ℕ)
    (hcover : ∀ x < m, ∃ p ∈ P, x ≡ r p [MOD p]) :
    (∑ x ∈ range m,
      (((hitPrimes P r x).card : ℝ) - 1) * (((hitPrimes P r x).card : ℝ) - 3)) ≤
      moderateMass P r m B +
        ∑ x ∈ highPositions P r m B, ((hitPrimes P r x).card : ℝ) ^ 2 := by
  classical
  unfold moderateMass moderatePositions highPositions
  rw [sum_filter, sum_filter, ← sum_add_distrib]
  apply sum_le_sum
  intro x hx
  have hh : 1 ≤ (hitPrimes P r x).card := by
    obtain ⟨p, hp, hpx⟩ := hcover x (mem_range.mp hx)
    exact card_pos.mpr ⟨p, mem_filter.mpr ⟨hp, hpx⟩⟩
  exact quadratic_probe_pointwise _ _ hh

/-- Once B² >= 2kt, the whole contribution from H >= B costs only 2k².
The contribution from 4 <= H < B remains in the conclusion. -/
theorem covered_length_le_moderate_mass
    (P : Finset ℕ) (r : ℕ → ℕ) (m B t : ℕ)
    (hP : ∀ p ∈ P, p.Prime)
    (hcover : ∀ x < m, ∃ p ∈ P, x ≡ r p [MOD p])
    (hB : 0 < B) (htB : t ≤ B) (hBt : 2 * P.card * t ≤ B ^ 2)
    (hcommon : ∀ x < m, ∀ y < m, x ≠ y →
      (hitPrimes P r x ∩ hitPrimes P r y).card ≤ t) :
    (m : ℝ) ≤ 72 * (P.card : ℝ) ^ 2 + 8 * moderateMass P r m B := by
  classical
  by_cases hm : m = 0
  · simp only [hm, Nat.cast_zero]
    exact add_nonneg (by positivity)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) (moderateMass_nonneg P r 0 B))
  have hk : 1 ≤ P.card := by
    obtain ⟨p, hp, _⟩ := hcover 0 (by omega)
    exact card_pos.mpr ⟨p, hp⟩
  have hlo := TripleCover.total_probe_lower (fun p : P => p.val)
    (fun p => hP p.val p.property) Subtype.val_injective r m
  simp only [Fintype.card_coe, TripleCover.subtype_hits] at hlo
  change (m : ℝ) * (5 / 36 : ℝ) - (3 + 4 * P.card + (P.card : ℝ) ^ 2) ≤
    ∑ x ∈ range m,
      (((hitPrimes P r x).card : ℝ) - 1) * (((hitPrimes P r x).card : ℝ) - 3) at hlo
  have hup := total_probe_le_split_mass P r m B hcover
  have hhi := high_positions_square_hits_le P r m B t hB htB hBt hcommon
  have hM := moderateMass_nonneg P r m B
  have hkR : (1 : ℝ) ≤ P.card := by exact_mod_cast hk
  nlinarith only [hlo, hup, hhi, hM, hkR, sq_nonneg ((P.card : ℝ) - 1)]

/-- A deterministic sufficient condition at quadratic scale. The moderate-mass
premise is an additional hypothesis and is not known uniformly for covers. -/
theorem quadratic_of_small_moderate_mass
    (P : Finset ℕ) (r : ℕ → ℕ) (m B t : ℕ)
    (hP : ∀ p ∈ P, p.Prime)
    (hcover : ∀ x < m, ∃ p ∈ P, x ≡ r p [MOD p])
    (hB : 0 < B) (htB : t ≤ B) (hBt : 2 * P.card * t ≤ B ^ 2)
    (hcommon : ∀ x < m, ∀ y < m, x ≠ y →
      (hitPrimes P r x ∩ hitPrimes P r y).card ≤ t)
    (hmoderate : moderateMass P r m B ≤ (m : ℝ) / 16) :
    m ≤ 144 * P.card ^ 2 := by
  have hh := covered_length_le_moderate_mass P r m B t hP hcover hB htB hBt hcommon
  have hhR : (m : ℝ) ≤ 144 * (P.card : ℝ) ^ 2 := by linarith
  exact_mod_cast hhR

/-- Factorial control of differences supplies the shared-hit premise for
arbitrary prime phases, without any phase average or independence assumption. -/
theorem covered_length_le_moderate_mass_factorial
    (P : Finset ℕ) (r : ℕ → ℕ) (m B t : ℕ)
    (hP : ∀ p ∈ P, p.Prime)
    (hcover : ∀ x < m, ∃ p ∈ P, x ≡ r p [MOD p])
    (ht : 0 < t) (hm : m ≤ t.factorial)
    (hB : 0 < B) (htB : t ≤ B) (hBt : 2 * P.card * t ≤ B ^ 2) :
    (m : ℝ) ≤ 72 * (P.card : ℝ) ^ 2 + 8 * moderateMass P r m B :=
  covered_length_le_moderate_mass P r m B t hP hcover hB htB hBt
    (fun x hx y hy hne => common_hits_factorial_bound P r m t x y hP ht hm hx hy hne)

#print axioms total_probe_le_split_mass
#print axioms covered_length_le_moderate_mass
#print axioms quadratic_of_small_moderate_mass
#print axioms covered_length_le_moderate_mass_factorial
end Erdos970.QuadraticOverlap
