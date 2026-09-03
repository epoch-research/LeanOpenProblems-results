import FormalConjecturesUtil

/-!
# A positive averaged-arity model with geometrically decaying coefficients

This is an abstract probability model, NOT a model of actual shifted primes.
All orders have exactly their expected logarithmic power, and the first two
normalized coefficients are one. Nevertheless the higher coefficients can
have arbitrarily small geometric rate. Thus positivity and the first two
asymptotics alone do not justify a higher-order bootstrap.
-/
open Nat Filter
open scoped Classical BigOperators Topology NNReal
namespace Erdos821.ArityModel
set_option maxHeartbeats 2000000

noncomputable def arityMoment (r k : ℕ) (μ : ℝ≥0) : ℝ :=
  ∑' n : ℕ, ProbabilityTheory.poissonPMFReal μ n * (k : ℝ)^(n+r)

noncomputable def logarithmicScale (r : ℕ) (μ : ℝ≥0) : ℝ :=
  (2 : ℝ)^r * Real.exp (μ : ℝ)

noncomputable def leadingCoefficient (r k : ℕ) : ℝ :=
  ((k : ℝ)/(2 : ℝ)^(k-1))^r

lemma poisson_weights_nonneg (μ : ℝ≥0) (n : ℕ) :
    0 ≤ ProbabilityTheory.poissonPMFReal μ n := ProbabilityTheory.poissonPMFReal_nonneg

lemma poisson_weights_sum_one (μ : ℝ≥0) :
    HasSum (ProbabilityTheory.poissonPMFReal μ) 1 := ProbabilityTheory.poissonPMFRealSum μ

lemma arityMoment_hasSum (r k : ℕ) (μ : ℝ≥0) :
    HasSum (fun n : ℕ => ProbabilityTheory.poissonPMFReal μ n * (k : ℝ)^(n+r))
      ((k : ℝ)^r*Real.exp ((μ : ℝ)*((k : ℝ)-1))) := by
  have hs : HasSum (fun n : ℕ => ((μ : ℝ)*(k : ℝ))^n/(n.factorial : ℝ))
      (Real.exp ((μ : ℝ)*(k : ℝ))) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp _
  convert hs.mul_left (Real.exp (-(μ : ℝ))*(k : ℝ)^r) using 1
  · ext n
    simp only [ProbabilityTheory.poissonPMFReal,pow_add,mul_pow]
    ring
  · rw [show Real.exp (-(μ : ℝ))*(k : ℝ)^r*Real.exp ((μ : ℝ)*(k : ℝ)) =
        (k : ℝ)^r*(Real.exp (-(μ : ℝ))*Real.exp ((μ : ℝ)*(k : ℝ))) by ring,
      ← Real.exp_add]
    congr 2
    ring

lemma arityMoment_eq (r k : ℕ) (μ : ℝ≥0) :
    arityMoment r k μ = (k : ℝ)^r*Real.exp ((μ : ℝ)*((k : ℝ)-1)) :=
  (arityMoment_hasSum r k μ).tsum_eq

lemma logarithmicScale_pos (r : ℕ) (μ : ℝ≥0) : 0 < logarithmicScale r μ := by
  unfold logarithmicScale
  positivity

lemma leadingCoefficient_pos (r k : ℕ) (hk : 1 ≤ k) : 0 < leadingCoefficient r k := by
  unfold leadingCoefficient
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  positivity

/-- Exact, not merely asymptotic, normalization at every positive order. -/
theorem normalized_arityMoment_eq (r k : ℕ) (hk : 1 ≤ k) (μ : ℝ≥0) :
    arityMoment r k μ/(logarithmicScale r μ)^(k-1) = leadingCoefficient r k := by
  have hcast : ((k-1 : ℕ) : ℝ) = (k : ℝ)-1 := by
    rw [Nat.cast_sub hk,Nat.cast_one]
  rw [arityMoment_eq]
  unfold logarithmicScale leadingCoefficient
  rw [mul_pow,← Real.exp_nat_mul,hcast]
  rw [show ((k : ℝ)-1)*(μ : ℝ) = (μ : ℝ)*((k : ℝ)-1) by ring]
  rw [div_pow,← pow_mul,← pow_mul,Nat.mul_comm r (k-1)]
  field_simp

lemma leadingCoefficient_one (r : ℕ) : leadingCoefficient r 1 = 1 := by
  simp [leadingCoefficient]

lemma leadingCoefficient_two (r : ℕ) : leadingCoefficient r 2 = 1 := by
  norm_num [leadingCoefficient]

lemma leadingCoefficient_three (r : ℕ) : leadingCoefficient r 3 = (3/4 : ℝ)^r := by
  norm_num [leadingCoefficient]

/-- The normalized coefficients are not log-convex, despite arising from
positive probability-weighted arity moments. -/
theorem leadingCoefficient_not_logconvex (r : ℕ) (hr : 1 ≤ r) :
    leadingCoefficient r 1 * leadingCoefficient r 3 < (leadingCoefficient r 2)^2 := by
  rw [leadingCoefficient_one,leadingCoefficient_two,leadingCoefficient_three,one_mul,one_pow]
  exact pow_lt_one₀ (by norm_num) (by norm_num) (by omega)

lemma leadingCoefficient_geometric_form (r k : ℕ) (hk : 1 ≤ k) :
    leadingCoefficient r k = (2 : ℝ)^r*(k : ℝ)^r*((1/2 : ℝ)^r)^k := by
  have he : (2 : ℝ)^k = (2 : ℝ)^(k-1)*2 := by
    rw [← _root_.pow_succ,Nat.sub_add_cancel hk]
  have hbase : (k : ℝ)/(2 : ℝ)^(k-1) = 2*(k : ℝ)*(1/2 : ℝ)^k := by
    rw [div_pow,one_pow,he]
    field_simp
  unfold leadingCoefficient
  rw [hbase,mul_pow,mul_pow]
  rw [← pow_mul,← pow_mul,Nat.mul_comm k r]

/-- For each fixed r, every geometric rate strictly above 2^(-r)
beats the normalized coefficients at sufficiently large fixed orders. -/
theorem tendsto_leadingCoefficient_div_geometric (r : ℕ) (θ : ℝ)
    (hθ : (1/2 : ℝ)^r < θ) :
    Tendsto (fun k : ℕ => leadingCoefficient r k/θ^k) atTop (𝓝 0) := by
  have hθ0 : 0 < θ := (pow_pos (by norm_num : (0 : ℝ)<1/2) r).trans hθ
  have hq0 : 0 ≤ (1/2 : ℝ)^r/θ := by positivity
  have hq1 : (1/2 : ℝ)^r/θ < 1 := (div_lt_one hθ0).mpr hθ
  have hh := (tendsto_pow_const_mul_const_pow_of_lt_one r hq0 hq1).const_mul ((2 : ℝ)^r)
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with k hk
  rw [leadingCoefficient_geometric_form r k hk,div_pow]
  ring

/-- The first two coefficients can be one while all sufficiently high
coefficients are smaller than ANY prescribed positive geometric rate.
This does not assert this behavior for shifted-prime moments. -/
theorem exists_positive_model_with_small_geometric_coefficients (θ : ℝ) (hθ : 0<θ) :
    ∃ r : ℕ, 1 ≤ r ∧ leadingCoefficient r 1 = 1 ∧ leadingCoefficient r 2 = 1 ∧
      ∀ᶠ k : ℕ in atTop, ∀ μ : ℝ≥0,
        arityMoment r k μ/(logarithmicScale r μ)^(k-1) < θ^k := by
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1)
  obtain ⟨R,hR⟩ := eventually_atTop.mp (hpow.eventually (eventually_lt_nhds hθ))
  let r := max 1 R
  have hr : 1 ≤ r := le_max_left _ _
  have hrt : (1/2 : ℝ)^r < θ := hR r (le_max_right _ _)
  refine ⟨r,hr,leadingCoefficient_one r,leadingCoefficient_two r,?_⟩
  filter_upwards [(tendsto_leadingCoefficient_div_geometric r θ hrt).eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ)<1)),eventually_ge_atTop 1] with k hk hk1
  intro μ
  rw [normalized_arityMoment_eq r k hk1 μ]
  exact (div_lt_one (pow_pos hθ k)).mp hk

end Erdos821.ArityModel
