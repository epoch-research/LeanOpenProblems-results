import Submission.QuarticFiveInputAllDegrees

/-! Rational five-input transfers whose denominators are powers of the
source quartic norm. These constructions are radial at every degree. -/
namespace Erdos322Research.QuarticFormalSpecialization
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 0

lemma rationalFiveNorm_ne_zero : rationalFiveNorm ≠ 0 := by
  intro h
  have hh := congrArg (MvPolynomial.eval (![1, 0, 0, 0, 0] : Fin 5 → ℚ)) h
  norm_num [rationalFiveNorm, Fin.sum_univ_succ, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hh

abbrev FiveAway := Localization.Away rationalFiveNorm
abbrev fivePolyMap : MvPolynomial (Fin 5) ℚ →+* FiveAway :=
  algebraMap _ _
abbrev fiveRatMap : ℚ →+* FiveAway := fivePolyMap.comp MvPolynomial.C

lemma fivePolyMap_injective : Function.Injective fivePolyMap := by
  intro P Q h
  obtain ⟨m, hm⟩ := IsLocalization.Away.exists_of_eq rationalFiveNorm h
  exact mul_left_cancel₀ (pow_ne_zero m rationalFiveNorm_ne_zero) hm

/-- A constant four-coordinate fourth-power norm in this localization has
only constant coordinates. Arbitrary powers of the denominator are allowed. -/
theorem fiveAway_constant_norm (f : Fin 4 → FiveAway) (c : ℚ)
    (h : ∑ i, f i ^ 4 = fiveRatMap c) :
    ∃ b : Fin 4 → ℚ, ∀ i, f i = fiveRatMap (b i) := by
  obtain ⟨D, hD⟩ := IsLocalization.exist_integer_multiples_of_finite
    (Submonoid.powers rationalFiveNorm) f
  choose P hP using hD
  obtain ⟨m, hm⟩ := D.property
  have hD' : (D : MvPolynomial (Fin 5) ℚ) = rationalFiveNorm ^ m := hm.symm
  have hPm (i : Fin 4) : fivePolyMap (P i) =
      fivePolyMap (rationalFiveNorm ^ m) * f i := by
    simpa only [Algebra.smul_def, hD'] using hP i
  have hp : ∑ i, P i ^ 4 = MvPolynomial.C c * rationalFiveNorm ^ (4 * m) := by
    apply fivePolyMap_injective
    simp only [map_sum, map_pow, map_mul, hPm, mul_pow]
    rw [← Finset.mul_sum, h]
    change (fivePolyMap rationalFiveNorm ^ m) ^ 4 * fiveRatMap c =
      fiveRatMap c * fivePolyMap rationalFiveNorm ^ (4 * m)
    rw [← pow_mul, Nat.mul_comm m 4, mul_comm]
  obtain ⟨b, hb, _⟩ := rational_transfer_radial P c m hp
  refine ⟨b, fun i ↦ ?_⟩
  have hi := hPm i
  rw [hb i, map_mul] at hi
  have hu : IsUnit (fivePolyMap (rationalFiveNorm ^ m)) := by
    simpa only [map_pow] using
      IsLocalization.Away.algebraMap_pow_isUnit rationalFiveNorm (S := FiveAway) m
  apply hu.mul_left_cancel
  simpa only [fiveRatMap, RingHom.comp_apply, mul_comm] using hi.symm

/-- Every nonzero norm-power transfer in the localization is radial, and its
power exponent is divisible by four. -/
theorem fiveAway_transfer_radial (f : Fin 4 → FiveAway) (c : ℚ) (e : ℕ)
    (hc : c ≠ 0)
    (h : ∑ i, f i ^ 4 = fiveRatMap c * fivePolyMap rationalFiveNorm ^ e) :
    ∃ (m : ℕ) (b : Fin 4 → ℚ), e = 4 * m ∧
      ∀ i, f i = fiveRatMap (b i) * fivePolyMap rationalFiveNorm ^ m := by
  obtain ⟨D, hD⟩ := IsLocalization.exist_integer_multiples_of_finite
    (Submonoid.powers rationalFiveNorm) f
  choose P hP using hD
  obtain ⟨s, hs⟩ := D.property
  have hD' : (D : MvPolynomial (Fin 5) ℚ) = rationalFiveNorm ^ s := hs.symm
  have hPs (i : Fin 4) : fivePolyMap (P i) =
      fivePolyMap (rationalFiveNorm ^ s) * f i := by
    simpa only [Algebra.smul_def, hD'] using hP i
  have hp : ∑ i, P i ^ 4 = MvPolynomial.C c * rationalFiveNorm ^ (e + 4 * s) := by
    apply fivePolyMap_injective
    simp only [map_sum, map_pow, map_mul, hPs, mul_pow]
    rw [← Finset.mul_sum, h, ← pow_mul, Nat.mul_comm s 4, pow_add]
    dsimp only [fiveRatMap, RingHom.comp_apply]
    ring
  obtain ⟨q, b, hq, hb, _⟩ := (rational_transfer_iff P c (e + 4 * s) hc).mp hp
  have hd : 4 ∣ e := by omega
  obtain ⟨m, hm⟩ := hd
  have hqs : q = m + s := by omega
  refine ⟨m, b, hm, fun i ↦ ?_⟩
  have hu : IsUnit (fivePolyMap (rationalFiveNorm ^ s)) := by
    simpa only [map_pow] using
      IsLocalization.Away.algebraMap_pow_isUnit rationalFiveNorm (S := FiveAway) s
  apply hu.mul_left_cancel
  rw [← hPs i, hb i, hqs, map_mul, map_pow, pow_add, map_pow]
  dsimp only [fiveRatMap, RingHom.comp_apply]
  ring

end
end Erdos322Research.QuarticFormalSpecialization
