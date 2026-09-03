import Submission.BuchstabLowTail
import Submission.SoftCylinderLaplace

/-! An unconditional Laplace upper bound at an explicit varying positive
parameter, obtained from the verified19/20 low-count bound. This does not
establish the soft-cylinder comparison needed for a quadratic survivor bound. -/
namespace Erdos970.SoftExposure
open Finset Real Filter GapAverages
set_option maxHeartbeats 1000000

noncomputable def refinedLaplaceThreshold (k : ℕ) : ℝ :=
  (refinedQuadraticScale*k^2 : ℕ)/(refinedLowCountLogConstant*log ((k : ℝ)+2))

noncomputable def refinedLaplaceRate (k : ℕ) : ℝ :=
  (k : ℝ)^(19/20 : ℝ)/64

noncomputable def refinedLaplaceParameter (k : ℕ) : ℝ :=
  refinedLaplaceRate k / refinedLaplaceThreshold k

lemma refinedLaplaceThreshold_pos (k : ℕ) (hk : 0 < k) :
    0 < refinedLaplaceThreshold k := by
  unfold refinedLaplaceThreshold
  apply div_pos
  · have hm : 0 < refinedQuadraticScale*k^2 := by
      unfold refinedQuadraticScale
      positivity
    exact_mod_cast hm
  · apply mul_pos refinedLowCountLogConstant_pos
    apply log_pos
    have hh := Nat.cast_nonneg (α := ℝ) k
    linarith only [hh]

lemma refinedLaplaceParameter_pos (k : ℕ) (hk : 0 < k) :
    0 < refinedLaplaceParameter k := by
  unfold refinedLaplaceParameter refinedLaplaceRate
  exact div_pos (div_pos (rpow_pos_of_pos (by exact_mod_cast hk) _) (by norm_num))
    (refinedLaplaceThreshold_pos k hk)

lemma refinedLaplaceParameter_eq (k : ℕ) (hk : 0 < k) :
    refinedLaplaceParameter k =
      (refinedLowCountLogConstant/(64*(refinedQuadraticScale : ℝ))) *
        log ((k : ℝ)+2)/(k : ℝ)^(21/20 : ℝ) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hL : 0 < log ((k : ℝ)+2) := log_pos (by linarith only [hk0])
  have hM : 0 < (refinedQuadraticScale : ℝ) := by norm_num [refinedQuadraticScale]
  have hpow : (k : ℝ)^2 = (k : ℝ)^(19/20 : ℝ)*(k : ℝ)^(21/20 : ℝ) := by
    rw [← rpow_add hk0]
    norm_num
  have ha : 0 < (k : ℝ)^(19/20 : ℝ) := rpow_pos_of_pos hk0 _
  have hb : 0 < (k : ℝ)^(21/20 : ℝ) := rpow_pos_of_pos hk0 _
  unfold refinedLaplaceParameter refinedLaplaceRate refinedLaplaceThreshold
  push_cast
  rw [hpow]
  field_simp

/-- This is genuinely a varying-parameter estimate: the positive parameter
converges to zero, so it must not be presented as a fixed-parameter bound. -/
theorem refinedLaplaceParameter_tendsto_zero :
    Tendsto refinedLaplaceParameter atTop (nhds 0) := by
  let A : ℝ := refinedLowCountLogConstant/(64*(refinedQuadraticScale : ℝ))
  have hA : 0 < A := by
    dsimp only [A]
    apply div_pos refinedLowCountLogConstant_pos
    norm_num [refinedQuadraticScale]
  have hpow := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/20)).comp
    tendsto_natCast_atTop_atTop
  have hpow' : Tendsto (fun k : ℕ => (k : ℝ)^(1/20 : ℝ)) atTop atTop := by
    simpa only [Function.comp_def] using hpow
  apply squeeze_zero' _ _ (hpow'.const_div_atTop (2*A))
  · filter_upwards [eventually_ge_atTop 1] with k hk
    exact (refinedLaplaceParameter_pos k (by omega)).le
  · filter_upwards [eventually_ge_atTop 1] with k hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hk0 : (0 : ℝ) < k := by linarith only [hk1]
    have hlog := log_le_sub_one_of_pos (show 0 < (k : ℝ)+2 by linarith only [hk0])
    have hlog' : log ((k : ℝ)+2) ≤ 2*k := by linarith only [hlog,hk1]
    have he : (k : ℝ)^(21/20 : ℝ) = (k : ℝ)*(k : ℝ)^(1/20 : ℝ) := by
      calc
        _ = (k : ℝ)^(1+(1/20 : ℝ)) := by norm_num
        _ = (k : ℝ)^1*(k : ℝ)^(1/20 : ℝ) := rpow_add hk0 _ _
        _ = _ := by rw [rpow_one]
    rw [refinedLaplaceParameter_eq k (by omega)]
    change A*log ((k : ℝ)+2)/(k : ℝ)^(21/20 : ℝ) ≤ _
    have hh := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlog' hA.le) (rpow_nonneg hk0.le (21/20 : ℝ))
    apply hh.trans_eq
    rw [he]
    field_simp [(rpow_pos_of_pos hk0 (1/20 : ℝ)).ne']

/-- The parameter is chosen so that the exponential remainder equals the
known low-count probability envelope. Both contributions are retained. -/
theorem eventually_refined_quadratic_laplace :
    ∀ᶠ k : ℕ in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → P.card ≤ k →
      countLaplace P (refinedLaplaceParameter k) (refinedQuadraticScale*k^2) ≤
        2*exp (-refinedLaplaceRate k) := by
  filter_upwards [eventually_refined_quadratic_low_tail,eventually_ge_atTop 1]
    with k htail hk
  intro P hP hPk
  have hk0 : 0 < k := by omega
  have hb := refinedLaplaceThreshold_pos k hk0
  have ht := refinedLaplaceParameter_pos k hk0
  have hh := countLaplace_le_lowCountFraction_add_exp P hP
    (refinedQuadraticScale*k^2) (refinedLaplaceThreshold k) (refinedLaplaceParameter k) ht.le
  have he : -refinedLaplaceParameter k*refinedLaplaceThreshold k = -refinedLaplaceRate k := by
    unfold refinedLaplaceParameter
    field_simp
  rw [he] at hh
  have hlow : lowCountFraction P (refinedQuadraticScale*k^2) (refinedLaplaceThreshold k) ≤
      exp (-refinedLaplaceRate k) := htail P hP hPk
  linarith only [hh,hlow]

/-- A precise remaining sufficient condition at this parameter. The product
comparison is not a consequence of the Laplace upper bound and is not proved. -/
theorem eventually_survivor_of_refined_soft_weight :
    ∀ᶠ k : ℕ in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → P.card ≤ k →
      2*exp (-refinedLaplaceRate k) <
        softCylinderWeight P (fun p => ((refinedQuadraticScale*k^2 : ℕ) : ℝ)/p.val+1)
          (refinedLaplaceParameter k) →
      ∀ r : ℕ → ℕ, ∃ x < refinedQuadraticScale*k^2, ∀ p ∈ P, ¬x ≡ r p [MOD p] := by
  filter_upwards [eventually_refined_quadratic_laplace,eventually_ge_atTop 1]
    with k hupper hk
  intro P hP hPk hweight r
  exact survivor_of_softCylinderLaplace P hP (refinedQuadraticScale*k^2)
    (refinedLaplaceParameter k) (refinedLaplaceParameter_pos k (by omega)).le
    ((hupper P hP hPk).trans_lt hweight) r

#print axioms refinedLaplaceParameter_tendsto_zero
#print axioms eventually_refined_quadratic_laplace
#print axioms eventually_survivor_of_refined_soft_weight
end Erdos970.SoftExposure
