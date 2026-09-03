import Submission.ConstructiveCover

/-!
A stronger lower bound for the uniform Jacobsthal function. This is not a
negation of the quadratic conjecture.
-/
namespace Erdos970.ConstructiveCover

set_option maxHeartbeats 2000000

/-- Multiples of `k log k` do not uniformly bound the Jacobsthal function.
The statement uses `log (k+1)` to avoid the immaterial zero at `k = 1`. -/
theorem not_mul_log_bound :
    ¬(∃ C > (0 : ℝ), ∀ k : ℕ, 0 < k →
      (jacobsthalFunction k : ℝ) ≤ C * k * Real.log (k + 1)) := by
  rintro ⟨C, hC, hupper⟩
  let B : ℝ := Real.log 4 + 1
  let E : ℝ := B + 1
  have hB : 0 < B := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    dsimp [B]
    linarith
  have hE : 0 < E := by dsimp [E]; linarith
  obtain ⟨A, hA⟩ := exists_nat_gt (3 * C * E + 1)
  have hAR : 1 < (A : ℝ) := by nlinarith
  have hA1 : 1 < A := by exact_mod_cast hAR
  have hApos : 0 < A := by omega
  have hARpos : 0 < (A : ℝ) := by positivity
  obtain ⟨S, hS, hden⟩ := exists_prime_tail_density A A
  let H := 2 ^ (S.sup id + 1).primesBelow.card
  let D := A * S.card + H * A + 1
  have ht : Filter.Tendsto (fun t : ℕ => (t : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have ht2 : Filter.Tendsto (fun t : ℕ => ((t ^ 2 : ℕ) : ℝ)) Filter.atTop Filter.atTop := by
    simpa only [Nat.cast_pow, pow_two, Nat.cast_mul] using ht.atTop_mul_atTop₀ ht
  have htA : Filter.Tendsto (fun t : ℕ => ((A * t ^ 2 : ℕ) : ℝ)) Filter.atTop Filter.atTop := by
    simpa only [Nat.cast_mul] using ht2.const_mul_atTop hARpos
  have hcheb1 : ∀ᶠ t : ℕ in Filter.atTop,
      ((t ^ 2).primeCounting : ℝ) ≤ B * (t ^ 2 : ℕ) / Real.log (t ^ 2 : ℕ) := by
    simpa only [Nat.floor_natCast] using ht2.eventually
      (Chebyshev.eventually_primeCounting_le (ε := 1) (by norm_num))
  have hchebA : ∀ᶠ t : ℕ in Filter.atTop,
      ((A * t ^ 2).primeCounting : ℝ) ≤ B * (A * t ^ 2 : ℕ) / Real.log (A * t ^ 2 : ℕ) := by
    simpa only [Nat.floor_natCast] using htA.eventually
      (Chebyshev.eventually_primeCounting_le (ε := 1) (by norm_num))
  have hsmall : ∀ᶠ t : ℕ in Filter.atTop, (D : ℝ) * Real.log t ≤ t := by
    have hh := ((Real.isLittleO_log_id_atTop.const_mul_left (D : ℝ)).comp_tendsto ht).bound
      (by norm_num : (0 : ℝ) < 1)
    filter_upwards [hh] with t hh
    have hh' : |(D : ℝ) * Real.log t| ≤ t := by simpa using hh
    exact (le_abs_self _).trans hh'
  have hlarge : ∀ᶠ t : ℕ in Filter.atTop, E ≤ Real.log (t : ℝ) :=
    (Real.tendsto_log_atTop.comp ht).eventually (Filter.eventually_ge_atTop E)
  obtain ⟨t, ht1, htA', htsmall, htlarge, htge⟩ :=
    (hcheb1.and (hchebA.and (hsmall.and (hlarge.and (Filter.eventually_ge_atTop A))))).exists
  have htpos : 0 < t := by omega
  have htR : 1 < (t : ℝ) := by exact_mod_cast (show 1 < t by omega)
  have htRpos : 0 < (t : ℝ) := by positivity
  have hLpos : 0 < Real.log (t : ℝ) := Real.log_pos htR
  have hAX : A ≤ t ^ 2 := by nlinarith
  obtain ⟨k, hbad, hbudget⟩ := exists_cover_budget A (t ^ 2) S hApos hAX hS hden
  have hMpos : 0 < A * t ^ 2 := by positivity
  have hkpos : 0 < k := by
    by_contra hh
    have hk0 : k = 0 := by omega
    subst k
    apply hbad
    have hb := isJacobsthalBound_factorial 0
    apply isJacobsthalBound_mono hb
    change 1 ≤ A * t ^ 2
    omega
  have hj : A * t ^ 2 < jacobsthalFunction k := by
    apply lt_of_not_ge
    intro hh
    exact hbad ((jacobsthalFunction_le_iff _ _).mp hh)
  have hsqrt : (A * t ^ 2).sqrt ≤ A * t := by
    have hh : A * t ^ 2 ≤ (A * t) ^ 2 := by nlinarith [sq_nonneg (t : ℤ)]
    simpa only [Nat.sqrt_eq'] using Nat.sqrt_le_sqrt hh
  have hbudget' : A * k ≤ A * ((t ^ 2).primeCounting + S.card) + (A * t ^ 2).primeCounting +
      H * (A * t) + 1 := by
    exact hbudget.trans (by dsimp only [H]; gcongr)
  have hbudgetR : (A : ℝ) * k ≤ A * (((t ^ 2).primeCounting : ℝ) + S.card) +
      ((A * t ^ 2).primeCounting : ℝ) + H * (A * (t : ℝ)) + 1 := by
    exact_mod_cast hbudget'
  have hlog2 : Real.log ((t ^ 2 : ℕ) : ℝ) = 2 * Real.log (t : ℝ) := by
    simp only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
  have hlogA : 2 * Real.log (t : ℝ) ≤ Real.log ((A * t ^ 2 : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_pow, Real.log_mul (by positivity) (by positivity), Real.log_pow]
    have hh := Real.log_nonneg hAR.le
    norm_num
    linarith
  have hlogApos : 0 < Real.log ((A * t ^ 2 : ℕ) : ℝ) := by linarith
  have hp1 : 2 * ((t ^ 2).primeCounting : ℝ) * Real.log (t : ℝ) ≤ B * (t : ℝ) ^ 2 := by
    rw [hlog2] at ht1
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * Real.log (t : ℝ))).mp ht1
    push_cast at hh
    nlinarith
  have hpA : 2 * ((A * t ^ 2).primeCounting : ℝ) * Real.log (t : ℝ) ≤
      B * A * (t : ℝ) ^ 2 := by
    have hh := (le_div_iff₀ hlogApos).mp htA'
    have hh' := mul_le_mul_of_nonneg_left hlogA (Nat.cast_nonneg (A * t ^ 2).primeCounting)
    push_cast at hh hh'
    nlinarith only [hh, hh']
  have hD : ((D : ℕ) : ℝ) = A * (S.card : ℝ) + (H : ℝ) * A + 1 := by
    dsimp [D]
    push_cast
    rfl
  have herr : ((A : ℝ) * S.card + H * (A * (t : ℝ)) + 1) * Real.log (t : ℝ) ≤
      (t : ℝ) ^ 2 := by
    have hcoeff : (A : ℝ) * S.card + H * (A * (t : ℝ)) + 1 ≤ D * (t : ℝ) := by
      rw [hD]
      have hh := mul_nonneg (by positivity : 0 ≤ (A : ℝ) * S.card + 1) (sub_nonneg.mpr htR.le)
      nlinarith
    have hh := mul_le_mul_of_nonneg_right hcoeff hLpos.le
    have hh' := mul_le_mul_of_nonneg_right htsmall htRpos.le
    nlinarith
  have hkl : (k : ℝ) * Real.log (t : ℝ) ≤ E * (t : ℝ) ^ 2 := by
    have hb := mul_le_mul_of_nonneg_right hbudgetR hLpos.le
    have hp1' := mul_le_mul_of_nonneg_left hp1 hARpos.le
    have hma : (A : ℝ) * ((k : ℝ) * Real.log (t : ℝ)) ≤ A * (E * (t : ℝ) ^ 2) := by
      dsimp only [E]
      nlinarith [mul_nonneg (sub_nonneg.mpr hAR.le) (sq_nonneg (t : ℝ))]
    exact (mul_le_mul_iff_right₀ hARpos).mp hma
  have hkle : (k : ℝ) ≤ (t : ℝ) ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left htlarge (Nat.cast_nonneg k)
    nlinarith
  have hk1le : (k : ℝ) + 1 ≤ (t : ℝ) ^ 3 := by
    have ht2 : (2 : ℝ) ≤ t := by exact_mod_cast (show 2 ≤ t by omega)
    nlinarith [sq_nonneg (t : ℝ), mul_nonneg (sub_nonneg.mpr ht2) (sq_nonneg (t : ℝ))]
  have hlogk : Real.log ((k : ℝ) + 1) ≤ 3 * Real.log (t : ℝ) := by
    have hh := Real.log_le_log (by positivity : 0 < (k : ℝ) + 1) hk1le
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have hu := hupper k hkpos
  have hu' : (jacobsthalFunction k : ℝ) ≤ 3 * C * E * (t : ℝ) ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hlogk (by positivity : 0 ≤ C * (k : ℝ))
    have hh' := mul_le_mul_of_nonneg_left hkl (by positivity : 0 ≤ 3 * C)
    nlinarith
  have hjR : (A : ℝ) * (t : ℝ) ^ 2 < jacobsthalFunction k := by exact_mod_cast hj
  have hlast := mul_lt_mul_of_pos_right hA (by positivity : 0 < (t : ℝ) ^ 2)
  nlinarith

#print axioms not_mul_log_bound
end Erdos970.ConstructiveCover
