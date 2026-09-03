import Submission.QuadraticRankPowerBound

/-! The local quadratic inverse has a power rank bound and a single-exponential
correlation bound in the reciprocal U³ parameter. -/
namespace Erdos3SingleExponentialQuadraticInverse
open Erdos3QuadraticRankPowerBound Erdos3PolynomialRankSkewSymmetry
  Erdos3PolynomialRankQuadraticInverse Erdos3ReducedLossQuadraticInverse
  Erdos3UnlocalizedBilinearExtraction Erdos3FiniteUniformity Erdos3FiniteFourier
  Erdos3FiniteBohr Erdos3LocalQuadraticInverse
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 6000000
set_option maxRecDepth 3000

noncomputable def extractionConstant : ℝ := 256*(4*((2 : ℝ)^65)^25)^388
noncomputable def parameterConstant : ℝ := 1024*(extractionConstant+1)^4
noncomputable def rankConstant : ℝ := 30000000000000*parameterConstant^21
noncomputable def correlationConstant : ℝ := 9+extractionConstant+16770*rankConstant

theorem extractionConstant_ge_one : 1 ≤ extractionConstant := by
  unfold extractionConstant
  apply one_le_mul_of_one_le_of_one_le (by norm_num)
  apply one_le_pow₀
  exact one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ (one_le_pow₀ (by norm_num)))

lemma retainedDensity_inv_bound {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    1/retainedDensity δ ≤ extractionConstant*(1/δ)^397705 := by
  let t := 1/δ
  have ht : 1 ≤ t := (le_div_iff₀ hδ).mpr (by simpa using hδ1)
  have hδpow : (2 : ℝ)^65/δ^41 = (2 : ℝ)^65*t^41 := by
    simp only [t,div_eq_mul_inv,inv_pow,one_mul]
  have hx : 1 ≤ ((2 : ℝ)^65*t^41)^25 := one_le_pow₀
    (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ ht))
  have hL : unlocalizedLoss δ ≤ (4*((2 : ℝ)^65)^25)^388*t^397700 := by
    calc
      _ = (2*(((2 : ℝ)^65*t^41)^25+1))^388 := by rw [unlocalizedLoss,hδpow]
      _ ≤ (4*((2 : ℝ)^65*t^41)^25)^388 := by
        apply pow_le_pow_left₀ (by positivity)
        linarith only [hx]
      _ = ((4*((2 : ℝ)^65)^25)*t^(41*25))^388 := by
        congr 1
        simp only [mul_pow,← pow_mul,mul_assoc]
      _ = _ := by simp only [mul_pow,← pow_mul]
  calc
    _ = 256*unlocalizedLoss δ*t^5 := by
      simp only [retainedDensity,t,div_eq_mul_inv,mul_inv_rev,inv_inv,inv_pow,one_mul]
    _ ≤ 256*((4*((2 : ℝ)^65)^25)^388*t^397700)*t^5 := by gcongr
    _ = _ := by
      change 256*((4*((2 : ℝ)^65)^25)^388*t^397700)*t^5 =
        (256*(4*((2 : ℝ)^65)^25)^388)*t^397705
      rw [mul_assoc 256, mul_assoc, ← pow_add, ← mul_assoc]

lemma retainedDensity_le_one {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) : retainedDensity δ ≤ 1 := by
  have hL : 1 ≤ unlocalizedLoss δ := by
    unfold unlocalizedLoss
    apply one_le_pow₀
    have hh : 0 ≤ ((2 : ℝ)^65/δ^41)^25 := by positivity
    linarith
  have hd : 0 < 256*unlocalizedLoss δ := by linarith
  apply (div_le_one hd).mpr
  have hh := pow_le_one₀ hδ.le hδ1 (n := 5)
  linarith

lemma parameterConstant_bounds :
    1 ≤ parameterConstant ∧ 1024*extractionConstant ≤ parameterConstant ∧
    256*extractionConstant^4 ≤ parameterConstant := by
  have hC := extractionConstant_ge_one
  have h1 : 1 ≤ extractionConstant+1 := by linarith
  have hpow : extractionConstant ≤ (extractionConstant+1)^4 :=
    (by linarith : extractionConstant ≤ extractionConstant+1).trans
      (by simpa only [pow_one] using pow_le_pow_right₀ h1 (by decide : 1 ≤ 4))
  have hpow4 : extractionConstant^4 ≤ (extractionConstant+1)^4 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 4
  unfold parameterConstant
  constructor
  · have hh := one_le_pow₀ h1 (n := 4); linarith
  constructor <;> nlinarith only [hpow,hpow4,one_le_pow₀ h1 (n := 4)]

lemma inverse_parameter_bounds {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    let t := parameterConstant*(1/δ)^1590828
    1 ≤ t ∧ 1/retainedDensity δ ≤ t ∧
    1/((δ/2)^8*(retainedDensity δ)^4) ≤ t ∧
    1/tolerance (retainedDensity δ) (δ/16) ≤ t := by
  let x := 1/δ
  have hx : 1 ≤ x := (le_div_iff₀ hδ).mpr (by simpa using hδ1)
  have hx0 : 0 ≤ x := by linarith
  have hα := retainedDensity_pos hδ
  have hi := retainedDensity_inv_bound hδ hδ1
  change 1/retainedDensity δ ≤ extractionConstant*x^397705 at hi
  have hC := extractionConstant_ge_one
  obtain ⟨hD1,hDC,hD4⟩ := parameterConstant_bounds
  have hDC' : extractionConstant ≤ parameterConstant := by linarith
  have hsmall : x^397705 ≤ x^1590828 := pow_le_pow_right₀ hx (by decide)
  have hsmall' : x^397706 ≤ x^1590828 := pow_le_pow_right₀ hx (by decide)
  change 1 ≤ parameterConstant*x^1590828 ∧ _ ∧ _ ∧ _
  refine ⟨one_le_mul_of_one_le_of_one_le hD1 (one_le_pow₀ hx),?_,?_,?_⟩
  · exact hi.trans (mul_le_mul hDC' hsmall (pow_nonneg hx0 _) (by linarith))
  · calc
      _ = 256*x^8*(1/retainedDensity δ)^4 := by
        simp only [x,div_eq_mul_inv,mul_inv_rev,inv_inv,inv_pow,one_mul]
        ring
      _ ≤ 256*x^8*(extractionConstant*x^397705)^4 := by gcongr
      _ = (256*extractionConstant^4)*x^1590828 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hD4 (pow_nonneg hx0 _)
  · calc
      _ = 1024*x*(1/retainedDensity δ) := by
        simp only [tolerance,x,div_eq_mul_inv,mul_inv_rev,inv_inv,one_mul]
        ring
      _ ≤ 1024*x*(extractionConstant*x^397705) := by gcongr
      _ = (1024*extractionConstant)*x^397706 := by ring
      _ ≤ _ := mul_le_mul hDC hsmall' (pow_nonneg hx0 _) (by linarith)

/-- An explicit power bound on the rank, uniform in the ambient group. -/
theorem sharpRank_power_bound {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (sharpRank δ : ℝ) ≤ rankConstant*(1/δ)^33407388 := by
  obtain ⟨ht,hαt,hΛt,hτt⟩ := inverse_parameter_bounds hδ hδ1
  have hα := retainedDensity_pos hδ
  have hh := fixedRadiusRank_power_bound hα (retainedDensity_le_one hδ hδ1)
    (by positivity : 0 < (δ/2)^8*(retainedDensity δ)^4)
    (by positivity : 0 < δ/16) ht hαt hΛt hτt
  apply hh.trans_eq
  simp only [rankConstant,mul_pow,pow_mul]
  ring

lemma rankConstant_pos : 0 < rankConstant := by
  have hD := parameterConstant_bounds.1
  unfold rankConstant
  positivity

lemma correlationConstant_pos : 0 < correlationConstant := by
  have hC := extractionConstant_ge_one
  have hR := rankConstant_pos
  unfold correlationConstant
  positivity

/-- The correlation cost is at worst one exponential of a fixed power of 1/δ. -/
theorem sharpCorrelation_exp_lower {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Real.exp (-correlationConstant*(1/δ)^33407388) ≤ sharpCorrelation δ := by
  let x := 1/δ
  have hx : 1 ≤ x := (le_div_iff₀ hδ).mpr (by simpa using hδ1)
  have hx0 : 0 < x := by linarith
  have hα := retainedDensity_pos hδ
  have hi := retainedDensity_inv_bound hδ hδ1
  have hr := sharpRank_power_bound hδ hδ1
  have hc := sharpCorrelation_pos hδ
  have hC := extractionConstant_ge_one
  have hid : 1/sharpCorrelation δ = 8*x*(1/retainedDensity δ)*(8385 : ℝ)^(2*sharpRank δ) := by
    simp only [sharpCorrelation,x,div_eq_mul_inv,mul_inv_rev,inv_inv,one_mul]
    ring
  have hlogid : Real.log (1/sharpCorrelation δ) = Real.log 8+Real.log x+
      Real.log (1/retainedDensity δ)+(2*sharpRank δ : ℕ)*Real.log 8385 := by
    rw [hid,Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),Real.log_mul (by norm_num) hx0.ne',Real.log_pow]
  have hlog8 : Real.log 8 ≤ 8 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8)
    linarith
  have hlogx : Real.log x ≤ x := by linarith [Real.log_le_sub_one_of_pos hx0]
  have hlogα : Real.log (1/retainedDensity δ) ≤ extractionConstant*x^397705 := by
    have hh := Real.log_le_sub_one_of_pos (one_div_pos.mpr hα)
    change 1/retainedDensity δ ≤ extractionConstant*x^397705 at hi
    linarith
  have hlog8385 : Real.log 8385 ≤ 8385 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8385)
    linarith
  have hterm : (2*sharpRank δ : ℕ)*Real.log 8385 ≤ 16770*rankConstant*x^33407388 := by
    calc
      _ ≤ ((2*sharpRank δ : ℕ) : ℝ)*8385 :=
        mul_le_mul_of_nonneg_left hlog8385 (Nat.cast_nonneg _)
      _ = 16770*(sharpRank δ : ℝ) := by push_cast; ring
      _ ≤ 16770*(rankConstant*x^33407388) := mul_le_mul_of_nonneg_left hr (by norm_num)
      _ = _ := by ring
  have hxsmall : x ≤ x^33407388 := by
    simpa only [pow_one] using pow_le_pow_right₀ hx (by decide : 1 ≤ 33407388)
  have hCsmall := mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hx (by decide : 397705 ≤ 33407388)) (by linarith : 0 ≤ extractionConstant)
  have h1 : 1 ≤ x^33407388 := one_le_pow₀ hx
  have hlog : Real.log (1/sharpCorrelation δ) ≤ correlationConstant*x^33407388 := by
    rw [hlogid]
    unfold correlationConstant
    nlinarith only [hlog8,hlogx,hlogα,hterm,hxsmall,hCsmall,h1]
  simp only [one_div,Real.log_inv] at hlog
  rw [← Real.exp_log hc]
  apply Real.exp_le_exp.mpr
  change -correlationConstant*x^33407388 ≤ Real.log (sharpCorrelation δ)
  linarith

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Conventional quantitative formulation of the completed U³ inverse theorem.
This statement does not assert a higher-order inverse or AP-density bound. -/
theorem single_exponential_local_quadratic_inverse
    (h2 : Function.Bijective (fun x : G ↦ x+x)) (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (hU : δ ≤ uniformityPower 2 f) :
    ∃ C : Finset (AddChar G ℂ), ∃ q : G → ℂ, ∃ a : G,
      (C.card : ℝ) ≤ rankConstant*(1/δ)^33407388 ∧ (∀ x, ‖q x‖ = 1) ∧
      IsLocallyQuadratic (bohr C (1/8) : Set G) q ∧
      Real.exp (-correlationConstant*(1/δ)^33407388) ≤
        ‖𝔼 y, if y ∈ bohr C (1/8) then f (a+y)*conj (q y) else 0‖^2 := by
  have hδ1 := hU.trans (uniformityPower_le_one 2 f hf)
  obtain ⟨C,q,a,hC,hq,hquad,hcorr⟩ := polynomial_rank_quadratic_inverse h2 f hf hδ hU
  exact ⟨C,q,a,(by exact_mod_cast hC : (C.card : ℝ) ≤ sharpRank δ).trans
    (sharpRank_power_bound hδ hδ1),hq,hquad,(sharpCorrelation_exp_lower hδ hδ1).trans hcorr⟩

#print axioms sharpRank_power_bound
#print axioms single_exponential_local_quadratic_inverse
end Erdos3SingleExponentialQuadraticInverse
