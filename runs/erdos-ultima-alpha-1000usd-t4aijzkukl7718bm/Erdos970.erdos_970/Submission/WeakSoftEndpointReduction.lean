import Submission.SoftEndpointReduction
import Submission.WeakerVoidReduction

/-! Weakened endpoint criteria. All positive-parameter endpoint estimates
remain explicit hypotheses. No unconditional quadratic estimate is asserted. -/
namespace Erdos970.GapAverages
open Finset Real Filter

/-- Iteration only needs a fixed rate for the particular prime set, not a
universal multiple of its density. -/
theorem countLaplace_le_of_endpoint_rate (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (t a : ℝ) (ht : 0 ≤ t)
    (h : ∀ m : ℕ, a * countLaplace P t m ≤ endpointLaplace P t m) (m : ℕ) :
    countLaplace P t m ≤ exp (-(a * (1-exp (-t)) * (m : ℝ))) := by
  have he : 0 ≤ 1-exp (-t) := by
    have hh : exp (-t) ≤ exp 0 := exp_le_exp.mpr (by linarith only [ht])
    simpa only [exp_zero] using sub_nonneg.mpr hh
  induction m with
  | zero => simp [countLaplace_zero P hP]
  | succ m ih =>
    have hh := mul_le_mul_of_nonneg_left (h m) he
    have hs : countLaplace P t (m+1) ≤
        (1-a*(1-exp (-t))) * countLaplace P t m := by
      rw [countLaplace_succ]
      nlinarith only [hh]
    have hex : 1-a*(1-exp (-t)) ≤ exp (-(a*(1-exp (-t)))) := by
      have := add_one_le_exp (-(a*(1-exp (-t))))
      linarith
    calc
      countLaplace P t (m+1) ≤ (1-a*(1-exp (-t))) * countLaplace P t m := hs
      _ ≤ exp (-(a*(1-exp (-t)))) * countLaplace P t m :=
        mul_le_mul_of_nonneg_right hex (countLaplace_nonneg P t m)
      _ ≤ exp (-(a*(1-exp (-t)))) * exp (-(a*(1-exp (-t))*(m : ℝ))) :=
        mul_le_mul_of_nonneg_left ih (exp_pos _).le
      _ = exp (-(a*(1-exp (-t))*((m+1 : ℕ) : ℝ))) := by
        rw [← exp_add]
        congr 1
        push_cast
        ring

/-- A much smaller endpoint rate suffices for the original quadratic target.
This definition is an UNPROVED candidate at every positive parameter. -/
def CriticalSoftEndpointBound (c t : ℝ) : Prop :=
  ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → ∀ k : ℕ, P.card ≤ k → ∀ m : ℕ,
    (c * log ((k : ℝ)+2) / ((k : ℝ)+1)) * countLaplace P t m ≤
      endpointLaplace P t m

/-- Transfer the critical endpoint hypothesis to the already verified void
criterion, retaining the precise loss from the fixed Laplace parameter. -/
theorem critical_void_of_critical_softEndpoint {c t : ℝ} (ht : 0 ≤ t)
    (h : CriticalSoftEndpointBound c t) :
    CriticalVoidBound (c*(1-exp (-t))) := by
  intro P hP k hk m
  have hh := (coveredFraction_le_countLaplace P t m).trans
    (countLaplace_le_of_endpoint_rate P hP t
      (c*log ((k : ℝ)+2)/((k : ℝ)+1)) ht (h P hP k hk) m)
  convert hh using 1
  congr 1
  ring

/-- CONDITIONAL: this weaker endpoint estimate, if proved for some positive
constants, is sufficient for exactly the unchanged conjecture. -/
theorem quadratic_bound_of_critical_softEndpoint {c t : ℝ}
    (hc : 0 < c) (ht : 0 < t) (h : CriticalSoftEndpointBound c t) :
    ∃ C > (0 : ℝ), ∀ k : ℕ, 0 < k →
      (jacobsthalFunction k : ℝ) ≤ C*k^2 := by
  apply quadratic_bound_of_critical_void (c := c*(1-exp (-t)))
  · apply mul_pos hc
    have he := exp_lt_exp.mpr (show -t < (0 : ℝ) by linarith)
    simpa only [exp_zero] using sub_pos.mpr he
  · exact critical_void_of_critical_softEndpoint ht.le h

/-- A fixed power of the sieve density is another sufficient endpoint rate.
The integer B is fixed independently of the prime set and interval length. -/
def DensityPowerSoftEndpointBound (c t : ℝ) (B : ℕ) : Prop :=
  ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → ∀ m : ℕ,
    (c*density P^B) * countLaplace P t m ≤ endpointLaplace P t m

/-- Mertens' lower bound converts the density power into a fixed logarithmic
loss. The endpoint premise itself is not supplied by Mertens' theorem. -/
theorem polylog_void_of_density_power_softEndpoint {c t : ℝ} (hc : 0 ≤ c)
    (ht : 0 ≤ t) (B : ℕ) (h : DensityPowerSoftEndpointBound c t B) :
    PolylogVoidBound
      (c*(1-exp (-t))*exp (-WeightedMertens.reciprocalConstant-1)^B) B := by
  intro P hP k hk m
  let d := exp (-WeightedMertens.reciprocalConstant-1)
  have hd : 0 < d := exp_pos _
  have hlog : 0 < log ((k : ℝ)+2) := log_pos (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
  have hdens : d / log ((k : ℝ)+2) ≤ density P := by
    simpa only [density, one_div, d] using
      WeightedMertens.prime_set_density_lower P hP k hk
  have hpow := pow_le_pow_left₀ (div_pos hd hlog).le hdens B
  have he : 0 ≤ 1-exp (-t) := by
    have hh := exp_le_exp.mpr (show -t ≤ (0 : ℝ) by linarith)
    simpa only [exp_zero] using sub_nonneg.mpr hh
  have hm := mul_le_mul_of_nonneg_left hpow
    (show 0 ≤ c*(1-exp (-t))*(m : ℝ) by positivity)
  have hrate : c*(1-exp (-t))*d^B*(m : ℝ)/log ((k : ℝ)+2)^B ≤
      (c*density P^B)*(1-exp (-t))*(m : ℝ) := by
    rw [div_pow] at hm
    convert hm using 1 <;> ring
  have hh := (coveredFraction_le_countLaplace P t m).trans
    (countLaplace_le_of_endpoint_rate P hP t (c*density P^B) ht (h P hP) m)
  exact hh.trans (exp_le_exp.mpr (neg_le_neg hrate))

/-- CONDITIONAL: any fixed density-power loss still permits the exact
quadratic conclusion. -/
theorem quadratic_bound_of_density_power_softEndpoint {c t : ℝ}
    (hc : 0 < c) (ht : 0 < t) (B : ℕ)
    (h : DensityPowerSoftEndpointBound c t B) :
    ∃ C > (0 : ℝ), ∀ k : ℕ, 0 < k →
      (jacobsthalFunction k : ℝ) ≤ C*k^2 := by
  apply quadratic_bound_of_polylog_void (B := B)
    (c := c*(1-exp (-t))*exp (-WeightedMertens.reciprocalConstant-1)^B)
  · have he : 0 < 1-exp (-t) := by
      have hh := exp_lt_exp.mpr (show -t < (0 : ℝ) by linarith)
      simpa only [exp_zero] using sub_pos.mpr hh
    positivity
  · exact polylog_void_of_density_power_softEndpoint hc.le ht.le B h

/-- At parameter zero every positive integral power of density is available.
This does not supply a uniform positive parameter: the reduction above
requires t>0, and its decay factor vanishes exactly at t=0. -/
theorem density_power_softEndpoint_zero (B : ℕ) :
    DensityPowerSoftEndpointBound 1 0 (B+1) := by
  intro P hP m
  have hF : countLaplace P 0 m = 1 := by
    unfold countLaplace
    simp only [neg_zero, zero_mul, exp_zero]
    exact phaseMean_const P hP 1
  have hG : endpointLaplace P 0 m = density P := by
    unfold endpointLaplace
    simp only [neg_zero, zero_mul, exp_zero, mul_one]
    exact phaseMean_point P hP m
  rw [hF, hG, one_mul, mul_one, pow_succ]
  have hp := pow_le_one₀ (density_pos P hP).le (density_le_one P hP) (n := B)
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hp (density_pos P hP).le

#print axioms density_power_softEndpoint_zero
#print axioms countLaplace_le_of_endpoint_rate
#print axioms quadratic_bound_of_critical_softEndpoint
#print axioms quadratic_bound_of_density_power_softEndpoint
end Erdos970.GapAverages
