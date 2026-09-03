import Submission.SharpCyclicStability

/-! A check on applicability: centered [0,1]-valued functions have every stored
uniformity power at most1/4. The near-maximal inverse theorem cannot be applied
directly to the balanced indicator in the AP counting argument. -/
namespace Erdos3CenteredUniformityBarrier
open Finset Erdos3FiniteUniformity Erdos3HigherUniformityDefect
  Erdos3CyclicStabilityParameters Erdos3QuantitativeCyclicInverse
  Erdos3NearConstantUniformity Erdos3SharpCyclicStability
open scoped BigOperators Classical
set_option maxHeartbeats 2000000
variable {G : Type*} [AddCommGroup G] [Fintype G]

lemma uniformity_le_mean_norm_sq (n : ℕ) (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    uniformityPower n f ≤ (𝔼 x : G, ‖f x‖)^2 := by
  cases n with
  | zero => exact pow_le_pow_left₀ (norm_nonneg _) (RCLike.norm_expect_le (K := ℂ)) 2
  | succ n =>
    calc
      _ ≤ 𝔼 h : G, 𝔼 x : G, ‖derivative f h x‖ :=
        expect_le_expect (fun h _ ↦ uniformity_le_mean_norm n _ (derivative_norm_le_one f hf h))
      _ = _ := mean_derivative_norm f

lemma centered_norm_mean (f : G → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    (𝔼 x : G, ‖((f x-(𝔼 y : G, f y) : ℝ) : ℂ)‖) ≤ 1/2 := by
  let μ : ℝ := 𝔼 y : G, f y
  have hμ0 : 0 ≤ μ := expect_nonneg (fun x _ ↦ (hf x).1)
  have hμ1 : μ ≤ 1 := expect_le univ_nonempty (fun x _ ↦ (hf x).2)
  have hpt (x : G) : ‖((f x-μ : ℝ) : ℂ)‖ ≤ μ+(1-2*μ)*f x := by
    rw [Complex.norm_real,Real.norm_eq_abs]
    have hmf := mul_le_mul_of_nonneg_left (hf x).2 hμ0
    have hfm := mul_le_mul_of_nonneg_right hμ1 (hf x).1
    apply abs_le.mpr
    constructor <;> nlinarith only [hmf,hfm]
  have hh := expect_le_expect (s := univ) (fun x _ ↦ hpt x)
  rw [expect_add_distrib,Fintype.expect_const,← mul_expect] at hh
  change (𝔼 x : G, ‖((f x-μ : ℝ) : ℂ)‖) ≤ μ+(1-2*μ)*μ at hh
  have hs := sq_nonneg (μ-1/2)
  change (𝔼 x : G, ‖((f x-μ : ℝ) : ℂ)‖) ≤ _
  nlinarith only [hh,hs]

/-- This includes the balanced indicator used by the counting lemma. -/
theorem centered_uniformity_le_quarter (n : ℕ) (f : G → ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    uniformityPower n (fun x ↦ ((f x-(𝔼 y : G, f y) : ℝ) : ℂ)) ≤ 1/4 := by
  let μ : ℝ := 𝔼 y : G, f y
  have hμ0 : 0 ≤ μ := expect_nonneg (fun x _ ↦ (hf x).1)
  have hμ1 : μ ≤ 1 := expect_le univ_nonempty (fun x _ ↦ (hf x).2)
  have hbound (x : G) : ‖((f x-μ : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real,Real.norm_eq_abs]
    apply abs_le.mpr
    constructor <;> linarith only [hμ0,hμ1,(hf x).1,(hf x).2]
  have hU := uniformity_le_mean_norm_sq n (fun x ↦ ((f x-μ : ℝ) : ℂ)) hbound
  have hm := centered_norm_mean f hf
  have hm0 : 0 ≤ 𝔼 x : G, ‖((f x-μ : ℝ) : ℂ)‖ := expect_nonneg (fun x _ ↦ norm_nonneg _)
  change (𝔼 x : G, ‖((f x-μ : ℝ) : ℂ)‖) ≤ 1/2 at hm
  change uniformityPower n (fun x ↦ ((f x-μ : ℝ) : ℂ)) ≤ _
  nlinarith only [hU,hm,hm0]

lemma sharpTolerance_le_sixteenth (n : ℕ) : sharpTolerance n ≤ 1/16 := by
  have hr := localRadius_le_eighth n
  have hr0 := localRadius_pos n
  have hτ := phaseTolerance_pos n (by linarith only [hr0] : 0 < localRadius n/2)
  calc
    _ ≤ phaseTolerance n (localRadius n/2) := div_le_self hτ.le (one_le_pow₀ (by norm_num))
    _ ≤ localRadius n/2 := phaseTolerance_le n (by linarith only [hr0]) (by linarith only [hr])
    _ ≤ _ := by linarith only [hr]

/-- A formal obstruction to directly invoking sharp_cyclic_inverse on a
centered indicator. This is NOT a disproof of the Erdős conjecture. -/
theorem centered_not_near_maximal (n : ℕ) (f : G → ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    ¬ (1-sharpTolerance n ≤ uniformityPower n (fun x ↦ ((f x-(𝔼 y : G, f y) : ℝ) : ℂ))) := by
  intro h
  linarith only [h,centered_uniformity_le_quarter n f hf,sharpTolerance_le_sixteenth n]

#print axioms centered_uniformity_le_quarter
#print axioms centered_not_near_maximal
end Erdos3CenteredUniformityBarrier
