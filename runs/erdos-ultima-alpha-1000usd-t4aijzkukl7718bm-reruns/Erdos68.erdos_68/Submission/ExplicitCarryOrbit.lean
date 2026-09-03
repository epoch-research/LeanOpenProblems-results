import Submission.CarriedPrimeFloor

/-! An explicit rational recurrence for the carried residual. This is an
auxiliary reformulation; no infinite nonconstancy or irrationality result is
asserted without an additional hypothesis. -/

namespace ExplicitCarryOrbit

open CongruencePreservingCarry Erdos68Development

/-- The quotient at a composite step depends only on the preceding residual
and the original factorial-minus-one summand. -/
lemma composite_quotient (r : ℕ) (hp : ¬ (r+4).Prime) :
    coeffRow r = 1 + (r+3 : ℤ) *
      ⌊((r+4 : ℚ) * z r + delta r) / (r+3)⌋ := by
  obtain ⟨k, hk⟩ := coeffRow_congruence r
  have hkQ : (coeffRow r : ℚ) = 1 + (r+3 : ℚ) * k := by
    exact_mod_cast (show coeffRow r = 1 + (r+3 : ℤ) * k by omega)
  have he := coeffRow_identity r
  have hz := z_nonprime_bounds r hp
  rw [hkQ] at he
  have hf : ⌊((r+4 : ℚ) * z r + delta r) / (r+3)⌋ = k := by
    apply Int.floor_eq_iff.mpr
    constructor
    · apply (le_div_iff₀ (by positivity : (0 : ℚ) < r+3)).mpr
      nlinarith [hz.1]
    · apply (div_lt_iff₀ (by positivity : (0 : ℚ) < r+3)).mpr
      nlinarith [hz.2]
  rw [hf]
  omega

lemma residual_composite (r : ℕ) (hp : ¬ (r+4).Prime) :
    z (r+1) = (r+4 : ℚ) * z r + delta r - (r+3) *
      (⌊((r+4 : ℚ) * z r + delta r) / (r+3)⌋ : ℤ) := by
  have he := coeffRow_identity r
  rw [composite_quotient r hp] at he
  push_cast at he
  linarith

/-- No Lambert coefficients occur in this definition. Index r corresponds
to the original row n=r+3. -/
def orbit : ℕ → ℚ
  | 0 => 16/5
  | r+1 =>
      let v := (r+4 : ℚ) * orbit r + 1 / ((r+4).factorial-1 : ℚ)
      if (r+4).Prime then v else v - (r+3) * (⌊v / (r+3)⌋ : ℤ)

theorem orbit_eq_residual (r : ℕ) : orbit r = z r := by
  induction r with
  | zero => exact z_zero.symm
  | succ r ih =>
    rw [orbit, ih]
    by_cases hp : (r+4).Prime
    · simpa only [if_pos hp, delta] using (z_prime r hp).symm
    · simpa only [if_neg hp, delta] using (residual_composite r hp).symm

lemma orbit_nonneg (r : ℕ) : 0 ≤ orbit r := by
  rw [orbit_eq_residual]
  exact z_nonneg r

lemma orbit_composite_bounds (r : ℕ) (hp : ¬ (r+4).Prime) :
    0 ≤ orbit (r+1) ∧ orbit (r+1) < r+3 := by
  rw [orbit_eq_residual]
  exact z_nonprime_bounds r hp

lemma orbit_fractional_part (r : ℕ) :
    Int.fract (orbit r) = Int.fract (scaledSumQ (r+2)) := by
  rw [orbit_eq_residual, CarriedPrimeFloor.residual_eq, Int.fract_sub_intCast]

lemma orbit_fractional_step (r : ℕ) :
    Int.fract (orbit (r+1)) =
      Int.fract ((r+4 : ℚ) * orbit r + 1 / ((r+4).factorial-1 : ℚ)) := by
  rw [orbit_eq_residual, orbit_eq_residual]
  apply Int.fract_eq_fract.mpr
  refine ⟨1-coeffRow r, ?_⟩
  have he := coeffRow_identity r
  simp only [delta] at he
  push_cast
  linarith

/-- Rationality forces the fractional part of this explicit orbit into
an interval approaching one. No eventual membership is asserted
unconditionally. -/
theorem rational_fractional_interval (q : ℚ)
    (hq : (∑' k : ℕ, term k) = (q : ℝ)) (r : ℕ)
    (hden : q.den ≤ r+3) :
    1 - 3 / (r+4 : ℝ) ≤ ((Int.fract (orbit r) : ℚ) : ℝ) ∧
      ((Int.fract (orbit r) : ℚ) : ℝ) < 1 := by
  obtain ⟨k, hklo, hkhi⟩ := rational_forces_partial_sums q hq (r+2) (by omega)
  norm_num only [Nat.cast_add, Nat.cast_ofNat] at hklo hkhi
  have hsmall : (3 : ℝ) / (r+2+2) < 1 := by
    apply (div_lt_one (by positivity)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) r]
  have hf : ⌊(scaledSumQ (r+2) : ℝ)⌋ = k-1 := by
    apply Int.floor_eq_iff.mpr
    rw [cast_scaledSumQ]
    push_cast
    constructor <;> linarith
  rw [orbit_fractional_part, Rat.cast_fract, Int.fract, hf, cast_scaledSumQ]
  push_cast
  rw [show (r : ℝ)+2+2 = r+4 by ring] at hklo
  constructor <;> linarith

/-- A sufficient recurrence-only condition. Proving arbitrarily late
small fractional parts for the actual orbit remains an open step here. -/
theorem irrational_of_frequent_small_fraction
    (h : ∀ N : ℕ, ∃ r ≥ N, Int.fract (orbit r) ≤ (1/2 : ℚ)) :
    Irrational (∑' k : ℕ, term k) := by
  rintro ⟨q, hq⟩
  obtain ⟨r, hr, hfrac⟩ := h (max q.den 3)
  have hlarge : 3 ≤ r := (le_max_right _ _).trans hr
  have hden : q.den ≤ r+3 := by omega
  have hb := (rational_fractional_interval q hq.symm r hden).1
  have hs : (3 : ℝ) / (r+4) < 1/2 := by
    apply (div_lt_iff₀ (by positivity)).mpr
    have hlarge' : (3 : ℝ) ≤ r := by exact_mod_cast hlarge
    linarith
  have hfrac' : ((Int.fract (orbit r) : ℚ) : ℝ) ≤ 1/2 := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr hfrac
  linarith

end ExplicitCarryOrbit

#print axioms ExplicitCarryOrbit.composite_quotient
#print axioms ExplicitCarryOrbit.orbit_eq_residual
#print axioms ExplicitCarryOrbit.orbit_fractional_part
#print axioms ExplicitCarryOrbit.orbit_fractional_step
#print axioms ExplicitCarryOrbit.rational_fractional_interval
#print axioms ExplicitCarryOrbit.irrational_of_frequent_small_fraction
