import Submission.ExponentialVoidReduction

/-! A precise conditional endpoint-to-void reduction. The endpoint inequality
is an explicit hypothesis, not a proved fact. In particular this file does
not prove the quadratic Jacobsthal conjecture. -/
namespace Erdos970.GapAverages
open Finset Real

/-- Laplace transform of the actual interval survivor count. -/
noncomputable def countLaplace (P : Finset ℕ) (t : ℝ) (m : ℕ) : ℝ :=
  phaseMean P (fun r => exp (-t * intervalCount P m r))

/-- The corresponding transform weighted by survival of the next endpoint. -/
noncomputable def endpointLaplace (P : Finset ℕ) (t : ℝ) (m : ℕ) : ℝ :=
  phaseMean P (fun r => point P m r * exp (-t * intervalCount P m r))

/-- This is the missing uniform hypothesis, at one fixed Laplace parameter.
It is not asserted by any unconditional theorem below. -/
def SoftEndpointBound (c t : ℝ) : Prop :=
  ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → ∀ m : ℕ,
    c * density P * countLaplace P t m ≤ endpointLaplace P t m

lemma point_eq_zero_or_one (P : Finset ℕ) (x : ℕ) (r : Phase P) :
    point P x r = 0 ∨ point P x r = 1 := by
  have hh : point P x r * (point P x r - 1) = 0 := by
    nlinarith only [point_sq P x r]
  rcases mul_eq_zero.mp hh with hh | hh
  · exact Or.inl hh
  · exact Or.inr (by linarith only [hh])

lemma countLaplace_nonneg (P : Finset ℕ) (t : ℝ) (m : ℕ) :
    0 ≤ countLaplace P t m := by
  unfold countLaplace phaseMean
  exact div_nonneg (sum_nonneg (fun _ _ => (exp_pos _).le)) (by positivity)

lemma countLaplace_zero (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (t : ℝ) :
    countLaplace P t 0 = 1 := by
  unfold countLaplace
  simp only [intervalCount, range_zero, sum_empty, mul_zero, exp_zero]
  exact phaseMean_const P hP 1

/-- An exact update, using that endpoint survival is zero or one. -/
lemma countLaplace_succ (P : Finset ℕ) (t : ℝ) (m : ℕ) :
    countLaplace P t (m + 1) =
      countLaplace P t m - (1 - exp (-t)) * endpointLaplace P t m := by
  have he (r : Phase P) : exp (-t * intervalCount P (m + 1) r) =
      exp (-t * intervalCount P m r) - (1 - exp (-t)) *
        (point P m r * exp (-t * intervalCount P m r)) := by
    rw [intervalCount_succ]
    rcases point_eq_zero_or_one P m r with hr | hr
    · simp [hr]
    · rw [hr]
      rw [mul_add, mul_one, exp_add]
      ring
  unfold countLaplace endpointLaplace
  simp_rw [he]
  rw [phaseMean_sub, phaseMean_mul]

/-- Exponential decay follows by iteration, provided the stated endpoint
inequality holds. No independence between adjacent windows is used. -/
theorem countLaplace_le_of_softEndpoint {c t : ℝ} (ht : 0 ≤ t)
    (h : SoftEndpointBound c t) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (m : ℕ) :
    countLaplace P t m ≤ exp (-(c * (1 - exp (-t)) * (m : ℝ) * density P)) := by
  have he : 0 ≤ 1 - exp (-t) := by
    have hh : exp (-t) ≤ exp 0 := exp_le_exp.mpr (by linarith only [ht])
    simpa only [exp_zero] using sub_nonneg.mpr hh
  induction m with
  | zero => simp [countLaplace_zero P hP]
  | succ m ih =>
    have hh := mul_le_mul_of_nonneg_left (h P hP m) he
    have hstep : countLaplace P t (m + 1) ≤
        (1 - c * (1 - exp (-t)) * density P) * countLaplace P t m := by
      rw [countLaplace_succ]
      nlinarith only [hh]
    have hexp : 1 - c * (1 - exp (-t)) * density P ≤
        exp (-(c * (1 - exp (-t)) * density P)) := by
      have hh := add_one_le_exp (-(c * (1 - exp (-t)) * density P))
      linarith only [hh]
    calc
      countLaplace P t (m + 1) ≤
          (1 - c * (1 - exp (-t)) * density P) * countLaplace P t m := hstep
      _ ≤ exp (-(c * (1 - exp (-t)) * density P)) * countLaplace P t m :=
        mul_le_mul_of_nonneg_right hexp (countLaplace_nonneg P t m)
      _ ≤ exp (-(c * (1 - exp (-t)) * density P)) *
          exp (-(c * (1 - exp (-t)) * (m : ℝ) * density P)) :=
        mul_le_mul_of_nonneg_left ih (exp_pos _).le
      _ = exp (-(c * (1 - exp (-t)) * ((m + 1 : ℕ) : ℝ) * density P)) := by
        rw [← exp_add]
        congr 1
        push_cast
        ring

lemma coveredFraction_le_countLaplace (P : Finset ℕ) (t : ℝ) (m : ℕ) :
    coveredFraction P m ≤ countLaplace P t m := by
  apply phaseMean_mono
  intro r
  split_ifs with hr
  · simp only [hr, mul_zero, exp_zero, le_refl]
  · exact (exp_pos _).le

/-- The constant in the resulting void estimate is exactly c*(1-exp(-t)). -/
theorem exponential_void_of_softEndpoint {c t : ℝ} (ht : 0 ≤ t)
    (h : SoftEndpointBound c t) : ExponentialVoidBound (c * (1 - exp (-t))) := by
  intro P hP m
  exact (coveredFraction_le_countLaplace P t m).trans
    (countLaplace_le_of_softEndpoint ht h P hP m)

/-- Any positive uniform endpoint constant at a fixed positive parameter
would settle the target. The unproved hypothesis is retained explicitly. -/
theorem quadratic_bound_of_softEndpoint {c t : ℝ} (hc : 0 < c) (ht : 0 < t)
    (h : SoftEndpointBound c t) :
    ∃ C > (0 : ℝ), ∀ k : ℕ, 0 < k →
      (jacobsthalFunction k : ℝ) ≤ C * k ^ 2 := by
  apply quadratic_bound_of_exponential_void
    (c := c * (1 - exp (-t)))
  · apply mul_pos hc
    have hh : exp (-t) < exp 0 := exp_lt_exp.mpr (by linarith only [ht])
    simpa only [exp_zero] using sub_pos.mpr hh
  · exact exponential_void_of_softEndpoint ht.le h

/-- Even the empty prime set forces the endpoint constant to be at most one. -/
theorem softEndpoint_constant_le_one {c t : ℝ} (h : SoftEndpointBound c t) : c ≤ 1 := by
  have hh := h ∅ (by simp) 0
  simpa [density, countLaplace, endpointLaplace, phaseMean, point, intervalCount] using hh

/-- A single phase contributes its exact reciprocal phase-space mass. -/
lemma phase_term_le_countLaplace (P : Finset ℕ) (t : ℝ) (m : ℕ) (r : Phase P) :
    exp (-t * intervalCount P m r) / (∏ p : P, (p.val : ℝ)) ≤
      countLaplace P t m := by
  unfold countLaplace phaseMean
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact single_le_sum (f := fun s : Phase P => exp (-t * intervalCount P m s))
    (fun s _ => (exp_pos _).le) (mem_univ r)

/-- The endpoint hypothesis would force a deterministic positive-density
lower bound, up to the logarithm of the phase-space size. This is another
conditional consequence, not an unconditional count estimate. -/
theorem count_lower_of_softEndpoint {c t : ℝ} (ht : 0 ≤ t)
    (h : SoftEndpointBound c t) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (m : ℕ) (r : Phase P) :
    c * (1 - exp (-t)) * (m : ℝ) * density P ≤
      t * intervalCount P m r + ∑ p ∈ P, log (p : ℝ) := by
  have hN : 0 < ∏ p : P, (p.val : ℝ) := by
    apply prod_pos
    intro p _
    exact_mod_cast (hP p.val p.property).pos
  have hh := (phase_term_le_countLaplace P t m r).trans
    (countLaplace_le_of_softEndpoint ht h P hP m)
  have hl := log_le_log (div_pos (exp_pos _) hN) hh
  rw [log_div (exp_pos _).ne' hN.ne', log_exp, log_exp,
    log_phase_product P hP] at hl
  linarith only [hl]

/-- At the zero parameter the hypothesis is trivial, and gives no decay.
The strict positivity of t in the quadratic reduction is indispensable. -/
theorem softEndpoint_zero_parameter_iff (c : ℝ) :
    SoftEndpointBound c 0 ↔ c ≤ 1 := by
  constructor
  · exact softEndpoint_constant_le_one
  · intro hc P hP m
    have hF : countLaplace P 0 m = 1 := by
      unfold countLaplace
      simp only [neg_zero, zero_mul, exp_zero]
      exact phaseMean_const P hP 1
    have hG : endpointLaplace P 0 m = density P := by
      unfold endpointLaplace
      simp only [neg_zero, zero_mul, exp_zero, mul_one]
      exact phaseMean_point P hP m
    rw [hF, hG, mul_one]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (density_pos P hP).le

#print axioms count_lower_of_softEndpoint
#print axioms softEndpoint_zero_parameter_iff

#print axioms countLaplace_succ
#print axioms exponential_void_of_softEndpoint
#print axioms quadratic_bound_of_softEndpoint
#print axioms softEndpoint_constant_le_one
end Erdos970.GapAverages
