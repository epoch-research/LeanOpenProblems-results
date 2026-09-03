import Submission.UniformSmoothCorrelationTail
import Submission.CovarianceScaleBudgets

/-! Fixed positive-parameter correlation means on the common irrational
scales. The scale sequence may be chosen independently of the damping
parameter. This is not a simultaneous limit with damping tending to zero. -/
namespace Erdos972FixedDampedCorrelation

open Finset Filter ArithmeticFunction
open scoped Topology ArithmeticFunction.Moebius
open Erdos972DampedDivisorKernel Erdos972UniformDampedTail
open Erdos972UniformSmoothCorrelationTail Erdos972SmoothDivisorTail
open Erdos972DivisorCovariance Erdos972DivisorPairCount Erdos972PrimePowerError
open Erdos972PolynomialRowScales Erdos972CenteredRowScales Erdos972GrowingTypeI
open Erdos972CovarianceScaleBudgets Erdos972ExponentialSum

lemma eventually_uniform_tail_cutoff {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε) :
    ∀ᶠ D : ℕ in atTop, ∀ N : ℕ,
      (∑ n ∈ Ioc 0 N, (expTail t D n)^2) ≤ ε*N := by
  have hh := (damping_tendsto_zero ht).mul_const (kernelMass (t/2))
  simp only [zero_mul] at hh
  filter_upwards [(tendsto_order.mp hh).2 ε hε] with D hD N
  apply (expTail_uniform_energy ht D N).trans
  have h := mul_le_mul_of_nonneg_left hD.le (Nat.cast_nonneg N)
  nlinarith only [h]

lemma eventually_uniform_correlation_cutoff {α t ε : ℝ}
    (hα : 1 ≤ α) (ht : 0 < t) (hε : 0 < ε) :
    ∀ᶠ D : ℕ in atTop, ∀ N : ℕ,
      |fullExpCorrelation t α N-truncatedExpCorrelation t α D N| ≤ ε*N := by
  let η := ε/4
  let δ := ε/(2*(1/η+1)*(1+α))
  have hη : 0 < η := by dsimp [η]; positivity
  have hc : 0 < 1/η+1 := by positivity
  have hαc : 0 < 1+α := by linarith
  have hδ : 0 < δ := div_pos hε (by positivity)
  filter_upwards [eventually_uniform_tail_cutoff ht hδ] with D hD N
  have hh := correlation_error_of_uniform_energy hα ht.le hδ.le hη D N hD
  have he : 2*η+(1/η+1)*δ*(1+α) = ε := by
    dsimp only [δ]
    field_simp
    dsimp only [η]
    ring
  rwa [he] at hh

noncomputable def dampedMean (t : ℝ) : ℝ :=
  ∑' d : ℕ, dampedCoefficient t d / d

lemma summable_dampedMean {t : ℝ} (ht : 0 < t) :
    Summable (fun d : ℕ => dampedCoefficient t d/d) := by
  apply (summable_reciprocalWeight ht).of_norm_bounded
  intro d
  have hμ : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one (n := d)
  simp only [Real.norm_eq_abs, dampedCoefficient, abs_div, abs_mul,
    abs_of_pos (Real.exp_pos _), abs_of_nonneg (Nat.cast_nonneg (α := ℝ) d)]
  unfold reciprocalWeight
  exact div_le_div_of_nonneg_right
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hμ (Real.exp_pos (-t * Real.log d)).le)
    (Nat.cast_nonneg d)

lemma divisorMean_tendsto {t : ℝ} (ht : 0 < t) :
    Tendsto (fun D : ℕ => divisorMean D (dampedCoefficient t)) atTop (𝓝 (dampedMean t)) := by
  have hh := (summable_dampedMean ht).hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def, sum_range_succ', Nat.cast_zero, div_zero, add_zero,
    divisorMean, sum_Ioc_zero_eq_sum_range_succ, dampedMean] using hh

/-- The actual small-divisor row property provided on arbitrarily large
common irrational scales. -/
def DivisorScale (α : ℝ) (u : ℕ) : Prop :=
  ∀ d e : ℕ, 0 < d → 0 < e → e ≤ root64 u → ∀ X ≤ scaleCutoff α u,
    |((divisorPairs α X d e).card : ℝ)-(X : ℝ)/(d*e)| ≤
      118*(root64 u : ℝ)*(u : ℝ)^4

lemma truncated_correlation_error {α t B : ℝ} (hα : 1 ≤ α)
    (ht : 0 ≤ t) (hB : 0 ≤ B) (D N : ℕ)
    (hlocal : ∀ d ∈ Ioc 0 D, ∀ e ∈ Ioc 0 D,
      |((divisorPairs α N d e).card : ℝ)-(N : ℝ)/(d*e)| ≤ B) :
    |truncatedExpCorrelation t α D N-(N : ℝ)*(divisorMean D (dampedCoefficient t))^2| ≤
      B*(D : ℝ)^2 := by
  have heq : truncatedExpCorrelation t α D N =
      ∑ n ∈ Ioc 0 N, divisorPolynomial D (dampedCoefficient t) n *
        divisorPolynomial D (dampedCoefficient t) (floorMul α n) := by
    apply sum_congr rfl
    intro n hn
    rw [truncatedExpSum_eq_polynomial t D (mem_Ioc.mp hn).1.ne',
      truncatedExpSum_eq_polynomial t D (floorMul_pos hα (mem_Ioc.mp hn).1).ne']
  have hp := polynomial_pair_error α N D D (dampedCoefficient t) (dampedCoefficient t) B hlocal
  rw [← heq] at hp
  have hmass0 : 0 ≤ coefficientMass D (dampedCoefficient t) := sum_nonneg fun _ _ => abs_nonneg _
  have hmass := coefficientMass_damped_le ht D
  have he : (N : ℝ)*divisorMean D (dampedCoefficient t)*divisorMean D (dampedCoefficient t) =
      (N : ℝ)*(divisorMean D (dampedCoefficient t))^2 := by ring
  rw [he] at hp
  apply hp.trans
  nlinarith only [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hmass0 hmass 2) hB]

lemma fixed_divisor_error_tendsto {α : ℝ} (hα : 1 ≤ α) (D : ℕ) :
    Tendsto (fun u : ℕ => 118*(root64 u : ℝ)*(u : ℝ)^4*(D : ℝ)^2 /
      (scaleCutoff α u : ℝ)) atTop (𝓝 0) := by
  have hh : Tendsto (fun u : ℕ => (236*α*(D : ℝ)^2)/(u : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  apply squeeze_zero_norm' _ hh
  filter_upwards [eventually_ge_atTop (1 : ℕ), eventually_ge_atTop ⌈α⌉₊] with u hu huα
  have hαu : α ≤ u := (Nat.le_ceil α).trans (Nat.cast_le.mpr huα)
  obtain ⟨huN, _, hscale⟩ := scaleCutoff_bounds hα hu hαu
  have huR : (0 : ℝ) < u := Nat.cast_pos.mpr hu
  have hNR : (0 : ℝ) < scaleCutoff α u := Nat.cast_pos.mpr (hu.trans huN)
  have hv : (root64 u : ℝ) ≤ u := Nat.cast_le.mpr (root64_le u)
  have hinv : 1/(scaleCutoff α u : ℝ) ≤ 2*α/(u : ℝ)^6 := by
    apply (div_le_div_iff₀ hNR (pow_pos huR 6)).mpr
    simpa only [one_mul] using hscale
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ = (118*(root64 u : ℝ)*(u : ℝ)^4*(D : ℝ)^2)*(1/(scaleCutoff α u : ℝ)) := by ring
    _ ≤ (118*(u : ℝ)*(u : ℝ)^4*(D : ℝ)^2)*(2*α/(u : ℝ)^6) := by
      apply mul_le_mul
      · gcongr
      · exact hinv
      · positivity
      · positivity
    _ = _ := by field_simp; ring

lemma eventually_fixed_truncated_error {α t ε : ℝ} (hα : 1 ≤ α)
    (ht : 0 ≤ t) (D : ℕ) (hε : 0 < ε) :
    ∀ᶠ u : ℕ in atTop, DivisorScale α u →
      |truncatedExpCorrelation t α D (scaleCutoff α u)-
        (scaleCutoff α u : ℝ)*(divisorMean D (dampedCoefficient t))^2| ≤
          ε*(scaleCutoff α u : ℝ) := by
  have hb := eventually_bound_of_scaled_limit hα _ (fixed_divisor_error_tendsto hα D) hε
  filter_upwards [hb, root64_tendsto.eventually_ge_atTop D] with u hb hD hs
  apply (truncated_correlation_error hα ht (by positivity) D (scaleCutoff α u) ?_).trans hb
  intro d hd e he
  exact hs d e (mem_Ioc.mp hd).1 (mem_Ioc.mp he).1 ((mem_Ioc.mp he).2.trans hD) _ le_rfl

/-- For each fixed positive t, the full correlation has the product mean on
all sufficiently large good scales. The threshold is allowed to depend on t. -/
theorem eventually_fixed_full_error {α t ε : ℝ} (hα : 1 ≤ α)
    (ht : 0 < t) (hε : 0 < ε) :
    ∀ᶠ u : ℕ in atTop, DivisorScale α u →
      |fullExpCorrelation t α (scaleCutoff α u)-
        (scaleCutoff α u : ℝ)*(dampedMean t)^2| ≤ ε*(scaleCutoff α u : ℝ) := by
  have hthird : 0 < ε/3 := by positivity
  have hm := ((divisorMean_tendsto ht).pow 2).sub_const ((dampedMean t)^2)
  have hma := hm.abs
  simp only [sub_self, abs_zero] at hma
  obtain ⟨D, hD, hmean⟩ := ((eventually_uniform_correlation_cutoff hα ht hthird).and
    ((tendsto_order.mp hma).2 (ε/3) hthird)).exists
  filter_upwards [eventually_fixed_truncated_error hα ht.le D hthird] with u hu hs
  have h₁ := hD (scaleCutoff α u)
  have h₂ := hu hs
  have h₃ : |(scaleCutoff α u : ℝ)*(divisorMean D (dampedCoefficient t))^2-
      (scaleCutoff α u : ℝ)*(dampedMean t)^2| ≤ (ε/3)*(scaleCutoff α u : ℝ) := by
    rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hmean.le (Nat.cast_nonneg (scaleCutoff α u))
  have hh := (abs_sub_le (fullExpCorrelation t α (scaleCutoff α u))
    (truncatedExpCorrelation t α D (scaleCutoff α u))
    ((scaleCutoff α u : ℝ)*(dampedMean t)^2)).trans
    (add_le_add h₁ ((abs_sub_le _ ((scaleCutoff α u : ℝ)*(divisorMean D (dampedCoefficient t))^2) _).trans
      (add_le_add h₂ h₃)))
  linarith only [hh]

#print axioms eventually_fixed_full_error

lemma fixed_full_mean_on_scales {α t : ℝ} (hα : 1 ≤ α) (ht : 0 < t)
    (u : ℕ → ℕ) (hu : Tendsto u atTop atTop) (hs : ∀ k, DivisorScale α (u k)) :
    Tendsto (fun k => fullExpCorrelation t α (scaleCutoff α (u k)) /
      (scaleCutoff α (u k) : ℝ)) atTop (𝓝 ((dampedMean t)^2)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hu.eventually (eventually_fixed_full_error hα ht (show 0 < ε/2 by positivity)),
    ((scaleCutoff_tendsto hα).comp hu).eventually_ge_atTop 1] with k hk hN
  have hNR : (0 : ℝ) < scaleCutoff α (u k) := Nat.cast_pos.mpr hN
  have hh := (div_le_iff₀ hNR).mpr (hk (hs k))
  rw [Real.dist_eq]
  have he : fullExpCorrelation t α (scaleCutoff α (u k))/(scaleCutoff α (u k) : ℝ) -
      (dampedMean t)^2 =
      (fullExpCorrelation t α (scaleCutoff α (u k))-
        (scaleCutoff α (u k) : ℝ)*(dampedMean t)^2)/(scaleCutoff α (u k) : ℝ) := by
    field_simp
  rw [he, abs_div, abs_of_pos hNR]
  exact hh.trans_lt (by linarith)

/-- A single unbounded sequence works for all fixed t>0. This does not
assert uniform convergence over parameters approaching zero. -/
theorem exists_fixed_damped_scale_sequence {α : ℝ} (hα : 1 < α) (hI : Irrational α) :
    ∃ u : ℕ → ℕ, Tendsto u atTop atTop ∧ (∀ k, DivisorScale α (u k)) ∧
      ∀ t : ℝ, 0 < t →
        Tendsto (fun k => fullExpCorrelation t α (scaleCutoff α (u k)) /
          (scaleCutoff α (u k) : ℝ)) atTop (𝓝 ((dampedMean t)^2)) := by
  have hex : ∀ k : ℕ, ∃ u : ℕ, k < u ∧ DivisorScale α u := by
    intro k
    obtain ⟨u, hku, _, _, _, hrow⟩ := exists_joint_prime_divisor_scale hα hI k
    exact ⟨u, hku, hrow⟩
  choose u hku hs using hex
  have hu : Tendsto u atTop atTop := tendsto_atTop_mono (fun k => (hku k).le) tendsto_id
  exact ⟨u, hu, hs, fun t ht => fixed_full_mean_on_scales hα.le ht u hu hs⟩

#print axioms exists_fixed_damped_scale_sequence

open Erdos972SmoothMangoldt Erdos972SmoothCorrelationApprox

lemma fixed_smooth_mean_on_scales {α t : ℝ} (hα : 1 ≤ α) (ht : 0 < t)
    (u : ℕ → ℕ) (hu : Tendsto u atTop atTop) (hs : ∀ k, DivisorScale α (u k)) :
    Tendsto (fun k => smoothCorrelation t α (scaleCutoff α (u k)) /
      (scaleCutoff α (u k) : ℝ)) atTop (𝓝 ((dampedMean t/t)^2)) := by
  have hN := (scaleCutoff_tendsto hα).comp hu
  have hNR : Tendsto (fun k => (scaleCutoff α (u k) : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hN
  have hbound : Tendsto (fun k => 1/(scaleCutoff α (u k) : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hNR
  have he : Tendsto (fun k =>
      (fullExpCorrelation t α (scaleCutoff α (u k))-
        t^2*smoothCorrelation t α (scaleCutoff α (u k)))/(scaleCutoff α (u k) : ℝ))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hbound
    filter_upwards with k
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (scaleCutoff α (u k)))]
    exact div_le_div_of_nonneg_right (full_minus_scaled_smooth hα ht _) (Nat.cast_nonneg _)
  have hh := ((fixed_full_mean_on_scales hα ht u hu hs).sub he).div_const (t^2)
  simp only [sub_zero] at hh
  convert hh using 1
  · funext k
    field_simp
    ring
  · rw [div_pow]

#print axioms fixed_smooth_mean_on_scales

end Erdos972FixedDampedCorrelation
