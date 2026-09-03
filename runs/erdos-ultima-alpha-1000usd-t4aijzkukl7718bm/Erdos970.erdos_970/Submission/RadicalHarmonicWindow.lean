import Submission.RadicalTailNormalizer

/-! Uniform reciprocal sums on multiplicative windows of multiples. -/
namespace Erdos970.FiniteSelberg
open Finset Real

lemma harmonic_Ioc (A B : ℕ) (hAB : A ≤ B) :
    (∑ j ∈ Ioc A B, 1 / (j : ℝ)) = (harmonic B : ℝ) - (harmonic A : ℝ) := by
  have hsub : Icc 1 A ⊆ Icc 1 B := Icc_subset_Icc_right hAB
  have he : Icc 1 B \ Icc 1 A = Ioc A B := by
    ext j
    simp only [mem_sdiff, mem_Icc, mem_Ioc]
    omega
  have hs := sum_sdiff (f := fun j : ℕ => 1 / (j : ℝ)) hsub
  rw [he] at hs
  have hh (N : ℕ) : (harmonic N : ℝ) = ∑ j ∈ Icc 1 N, 1 / (j : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    simp only [one_div]
  rw [hh, hh]
  linarith

lemma harmonic_multiplicative_window (R q b : ℕ) (hq : 0 < q) (hb : 0 < b) :
    (∑ j ∈ Ioc (R / (q * b)) (R / q), 1 / (j : ℝ)) ≤ 1 + log b := by
  have hb1 : 1 ≤ b := hb
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  have hAB : R / (q * b) ≤ R / q :=
    Nat.div_le_div_left (by nlinarith) hq
  rw [harmonic_Ioc _ _ hAB]
  by_cases hR : q ≤ R
  · have hx1 : (1 : ℝ) ≤ (R : ℝ) / q := (le_div_iff₀ hq0).mpr (by simpa using (show (q : ℝ) ≤ R by exact_mod_cast hR))
    have hR0 : (0 : ℝ) < R := by exact_mod_cast (hq.trans_le hR)
    have hu := harmonic_floor_le_one_add_log ((R : ℝ) / q) hx1
    have hl := log_le_harmonic_floor ((R : ℝ) / (q * b)) (by positivity)
    rw [Nat.floor_div_natCast, Nat.floor_natCast] at hu
    rw [← Nat.cast_mul q b, Nat.floor_div_natCast, Nat.floor_natCast] at hl
    rw [Nat.cast_mul, log_div hR0.ne' (mul_pos hq0 hb0).ne', log_mul hq0.ne' hb0.ne'] at hl
    rw [log_div hR0.ne' hq0.ne'] at hu
    linarith
  · have hz : R / q = 0 := Nat.div_eq_of_lt (by omega)
    have hz' : R / (q * b) = 0 := by
      apply Nat.eq_zero_of_le_zero
      simpa only [hz] using hAB
    rw [hz, hz']
    simp only [harmonic_zero, Rat.cast_zero, sub_self]
    have hlog : 0 ≤ log (b : ℝ) := log_nonneg (by exact_mod_cast hb1)
    linarith

/-- The residue-modulus factor is retained, including when the lower endpoint
  is below one. -/
theorem reciprocal_multiples_window (s : Finset ℕ) (R q b : ℕ)
    (hq : 0 < q) (hb : 0 < b)
    (hs : ∀ d ∈ s, 0 < d ∧ d ≤ R ∧ R < d * b ∧ q ∣ d) :
    (∑ d ∈ s, 1 / (d : ℝ)) ≤ (1 + log b) / q := by
  let T := Ioc (R / (q * b)) (R / q)
  have hinj : Set.InjOn (fun d => d / q) (↑s : Set ℕ) := by
    intro d hd e he hde
    have hdq := Nat.div_mul_cancel (hs d hd).2.2.2
    have heq := Nat.div_mul_cancel (hs e he).2.2.2
    dsimp only at hde
    rw [hde, heq] at hdq
    exact hdq.symm
  have hmap : s.image (fun d => d / q) ⊆ T := by
    intro j hj
    obtain ⟨d, hd, rfl⟩ := mem_image.mp hj
    obtain ⟨hd0, hdR, hRd, hdq⟩ := hs d hd
    apply mem_Ioc.mpr
    constructor
    · apply (Nat.div_lt_iff_lt_mul (Nat.mul_pos hq hb)).mpr
      simpa only [← Nat.mul_assoc, Nat.div_mul_cancel hdq] using hRd
    · exact Nat.div_le_div_right hdR
  have he (d : ℕ) (hd : d ∈ s) :
      1 / (d : ℝ) = (1 / (q : ℝ)) * (1 / ((d / q : ℕ) : ℝ)) := by
    have hprod : (d : ℝ) = (q : ℝ) * ((d / q : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mul_div_cancel' (hs d hd).2.2.2).symm
    rw [hprod]
    ring
  calc
    _ = (1 / (q : ℝ)) * ∑ d ∈ s, 1 / ((d / q : ℕ) : ℝ) := by
      rw [mul_sum]
      exact sum_congr rfl he
    _ = (1 / (q : ℝ)) * ∑ j ∈ s.image (fun d => d / q), 1 / (j : ℝ) := by
      rw [sum_image hinj]
    _ ≤ (1 / (q : ℝ)) * ∑ j ∈ T, 1 / (j : ℝ) :=
      mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg hmap
        (fun _ _ _ => by positivity)) (by positivity)
    _ ≤ (1 / (q : ℝ)) * (1 + log b) :=
      mul_le_mul_of_nonneg_left (harmonic_multiplicative_window R q b hq hb) (by positivity)
    _ = _ := by ring

lemma log_add_one_le_twice_sqrt (b : ℕ) (hb : 0 < b) :
    1 + log (b : ℝ) ≤ 2 * sqrt b := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  have h := log_le_sub_one_of_pos (sqrt_pos.mpr hb0)
  rw [log_sqrt hb0.le] at h
  linarith

#print axioms reciprocal_multiples_window
end Erdos970.FiniteSelberg
