import Submission.ResidueEquidistributionExplore

/-! Continuous test-function consequences of the generating-function moment
ratios. These are a step towards a Tauberian counting-profile theorem, not a
proof of the logarithmic representation conjecture. -/
namespace Erdos66TauberianTests
open Filter MeasureTheory AdditiveCombinatorics Erdos66Generating
open scoped Topology Classical Polynomial

abbrev I := Set.Icc (0 : ℝ) 1

noncomputable def clip (x : ℝ) : I :=
  ⟨max 0 (min 1 x), le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

lemma clip_coe {x : ℝ} (hx : x ∈ I) : (clip x : ℝ) = x := by
  simp only [clip, min_eq_right hx.2, max_eq_right hx.1]

noncomputable def gaussPoint (x : ℝ) : I :=
  ⟨Real.exp (-x ^ 2), (Real.exp_pos _).le,
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg x))⟩

@[fun_prop] lemma continuous_gaussPoint : Continuous gaussPoint := by
  apply Continuous.subtype_mk
  fun_prop

lemma integrable_gauss_test (g : C(I, ℝ)) :
    Integrable (fun x : ℝ ↦ Real.exp (-x ^ 2) * g (gaussPoint x)) := by
  have hg : Integrable (fun x : ℝ ↦ Real.exp (-x ^ 2) * ‖g‖) := by
    simpa only [neg_mul, one_mul] using (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).mul_const ‖g‖
  apply hg.mono' ((by fun_prop : Continuous (fun x : ℝ ↦
    Real.exp (-x ^ 2) * g (gaussPoint x))).aestronglyMeasurable)
  filter_upwards [] with x
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (g.norm_coe_le_norm _) (Real.exp_pos _).le

noncomputable def gaussTest (g : C(I, ℝ)) : ℝ :=
  (∫ x : ℝ, Real.exp (-x ^ 2) * g (gaussPoint x)) / Real.sqrt Real.pi

lemma gaussTest_add (g h : C(I, ℝ)) : gaussTest (g + h) = gaussTest g + gaussTest h := by
  simp only [gaussTest, ContinuousMap.add_apply, mul_add,
    integral_add (integrable_gauss_test g) (integrable_gauss_test h), add_div]

lemma gaussTest_sub (g h : C(I, ℝ)) : gaussTest (g - h) = gaussTest g - gaussTest h := by
  simp only [gaussTest, ContinuousMap.sub_apply, mul_sub,
    integral_sub (integrable_gauss_test g) (integrable_gauss_test h), sub_div]

lemma gaussTest_norm (g : C(I, ℝ)) : |gaussTest g| ≤ ‖g‖ := by
  have hg : Integrable (fun x : ℝ ↦ Real.exp (-x ^ 2) * ‖g‖) := by
    simpa only [neg_mul, one_mul] using (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).mul_const ‖g‖
  have hb := norm_integral_le_of_norm_le hg (f := fun x : ℝ ↦ Real.exp (-x ^ 2) * g (gaussPoint x))
    (Filter.Eventually.of_forall (fun x ↦ by
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (g.norm_coe_le_norm _) (Real.exp_pos _).le))
  have he : (∫ x : ℝ, Real.exp (-x ^ 2) * ‖g‖) = Real.sqrt Real.pi * ‖g‖ := by
    rw [integral_mul_const]
    have hh := integral_gaussian (1 : ℝ)
    simpa only [neg_mul, one_mul, div_one] using congrArg (fun x : ℝ ↦ x * ‖g‖) hh
  rw [he, Real.norm_eq_abs] at hb
  dsimp [gaussTest]
  rw [abs_div, abs_of_pos (Real.sqrt_pos.mpr Real.pi_pos)]
  exact (div_le_iff₀ (Real.sqrt_pos.mpr Real.pi_pos)).mpr (by nlinarith)

lemma gaussTest_dist (g h : C(I, ℝ)) : |gaussTest g - gaussTest h| ≤ ‖g - h‖ := by
  rw [← gaussTest_sub]
  exact gaussTest_norm _

noncomputable def test (A : Set ℕ) (r : ℝ) (g : C(I, ℝ)) : ℝ :=
  (∑' n, indicator A n * r ^ n * g (clip (r ^ n))) / series (indicator A) r

lemma summable_test (A : Set ℕ) {r : ℝ} (hr : |r| < 1) (g : C(I, ℝ)) :
    Summable (fun n ↦ indicator A n * r ^ n * g (clip (r ^ n))) := by
  apply Summable.of_norm_bounded ((summable_indicator A hr).norm.mul_right ‖g‖)
  intro n
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (g.norm_coe_le_norm _) (norm_nonneg _)

lemma test_add (A : Set ℕ) {r : ℝ} (hr : |r| < 1) (g h : C(I, ℝ)) :
    test A r (g + h) = test A r g + test A r h := by
  simp only [test, ContinuousMap.add_apply, mul_add,
    (summable_test A hr g).tsum_add (summable_test A hr h), add_div]

lemma test_sub (A : Set ℕ) {r : ℝ} (hr : |r| < 1) (g h : C(I, ℝ)) :
    test A r (g - h) = test A r g - test A r h := by
  simp only [test, ContinuousMap.sub_apply, mul_sub,
    (summable_test A hr g).tsum_sub (summable_test A hr h), sub_div]

lemma series_indicator_nonneg (A : Set ℕ) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ series (indicator A) r :=
  tsum_nonneg (fun n ↦ mul_nonneg (indicator_nonneg A n) (pow_nonneg hr n))

lemma test_norm (A : Set ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (g : C(I, ℝ)) :
    |test A r g| ≤ ‖g‖ := by
  have hr : |r| < 1 := by rwa [abs_of_nonneg hr0]
  have hF := series_indicator_nonneg A hr0
  by_cases hF0 : series (indicator A) r = 0
  · simp only [test, hF0, div_zero, abs_zero]
    exact norm_nonneg _
  have hFp : 0 < series (indicator A) r := lt_of_le_of_ne hF (Ne.symm hF0)
  have hbound : |∑' n, indicator A n * r ^ n * g (clip (r ^ n))| ≤
      series (indicator A) r * ‖g‖ := by
    calc
      _ ≤ ∑' n, ‖indicator A n * r ^ n * g (clip (r ^ n))‖ := by
        simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (summable_test A hr g).norm
      _ ≤ ∑' n, indicator A n * r ^ n * ‖g‖ := by
        apply Summable.tsum_le_tsum _ (summable_test A hr g).norm ((summable_indicator A hr).mul_right ‖g‖)
        intro n
        rw [norm_mul, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (indicator_nonneg A n) (pow_nonneg hr0 n))]
        exact mul_le_mul_of_nonneg_left (g.norm_coe_le_norm _)
          (mul_nonneg (indicator_nonneg A n) (pow_nonneg hr0 n))
      _ = _ := by rw [tsum_mul_right]; rfl
  dsimp [test]
  rw [abs_div, abs_of_pos hFp]
  exact (div_le_iff₀ hFp).mpr (by nlinarith)

lemma test_dist (A : Set ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (g h : C(I, ℝ)) :
    |test A r g - test A r h| ≤ ‖g - h‖ := by
  rw [← test_sub A (by rwa [abs_of_nonneg hr0])]
  exact test_norm A hr0 hr1 _

lemma gaussTest_monomial (k : ℕ) (a : ℝ) :
    gaussTest ((Polynomial.monomial k a).toContinuousMapOn I) = a / Real.sqrt ((k : ℝ) + 1) := by
  have he (x : ℝ) : Real.exp (-x ^ 2) *
      ((Polynomial.monomial k a).toContinuousMapOn I) (gaussPoint x) =
      a * Real.exp (-((k : ℝ) + 1) * x ^ 2) := by
    simp only [Polynomial.toContinuousMapOn_apply, Polynomial.toContinuousMap_apply,
      Polynomial.eval_monomial, gaussPoint]
    rw [← Real.exp_nat_mul, mul_left_comm, ← Real.exp_add]
    congr 2
    ring
  simp only [gaussTest, he]
  rw [integral_const_mul, integral_gaussian, Real.sqrt_div Real.pi_pos.le]
  have hpi := Real.sqrt_ne_zero'.mpr Real.pi_pos
  have hk := Real.sqrt_ne_zero'.mpr (by positivity : (0 : ℝ) < (k : ℝ) + 1)
  field_simp

lemma test_monomial (A : Set ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (k : ℕ) (a : ℝ) :
    test A r ((Polynomial.monomial k a).toContinuousMapOn I) =
      a * (series (indicator A) (r ^ (k + 1)) / series (indicator A) r) := by
  have he (n : ℕ) : indicator A n * r ^ n *
      ((Polynomial.monomial k a).toContinuousMapOn I) (clip (r ^ n)) =
      a * (indicator A n * (r ^ (k + 1)) ^ n) := by
    simp only [Polynomial.toContinuousMapOn_apply, Polynomial.toContinuousMap_apply,
      Polynomial.eval_monomial, clip_coe ⟨pow_nonneg hr0 n, pow_le_one₀ hr0 hr1⟩]
    rw [← pow_mul, ← pow_mul, Nat.add_mul, pow_add, Nat.one_mul, Nat.mul_comm k n]
    ring
  simp only [test, he, tsum_mul_left, series]
  ring

lemma polynomial_test_limit_of_moments {A : Set ℕ}
    (hMom : ∀ k : ℕ, k ≠ 0 → Tendsto
      (fun r : ℝ ↦ series (indicator A) (r ^ k) / series (indicator A) r)
      (𝓝[<] 1) (𝓝 (1 / Real.sqrt (k : ℝ)))) (p : ℝ[X]) :
    Tendsto (fun r ↦ test A r (p.toContinuousMapOn I)) (𝓝[<] 1)
      (𝓝 (gaussTest (p.toContinuousMapOn I))) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have he : (p + q).toContinuousMapOn I = p.toContinuousMapOn I + q.toContinuousMapOn I := by
      ext x
      simp
    rw [he, gaussTest_add]
    apply (hp.add hq).congr'
    filter_upwards [unit_interval_eventually] with r hr
    symm
    exact test_add A (by simpa only [abs_of_pos hr.1] using hr.2) _ _
  | monomial k a =>
    rw [gaussTest_monomial]
    have hh := (hMom (k + 1) (by omega)).const_mul a
    simp only [Nat.cast_add, Nat.cast_one, mul_one_div] at hh
    apply hh.congr'
    filter_upwards [unit_interval_eventually] with r hr
    exact (test_monomial A hr.1.le hr.2.le k a).symm

/-- The normalized Laplace-weighted distribution has the Gaussian-square
moment law, first for polynomials and then for all continuous test functions. -/
theorem continuous_test_limit_of_moments {A : Set ℕ}
    (hMom : ∀ k : ℕ, k ≠ 0 → Tendsto
      (fun r : ℝ ↦ series (indicator A) (r ^ k) / series (indicator A) r)
      (𝓝[<] 1) (𝓝 (1 / Real.sqrt (k : ℝ)))) (g : C(I, ℝ)) :
    Tendsto (fun r ↦ test A r g) (𝓝[<] 1) (𝓝 (gaussTest g)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨p, hp⟩ := exists_polynomial_near_continuousMap 0 1 g (ε / 3) (by positivity)
  have hlim := polynomial_test_limit_of_moments hMom p
  have hev := (Metric.tendsto_nhds.mp hlim) (ε / 3) (by positivity)
  filter_upwards [unit_interval_eventually, hev] with r hr hclose
  rw [Real.dist_eq] at hclose ⊢
  have h₁ := test_dist A hr.1.le hr.2 g (p.toContinuousMapOn I)
  have h₂ := gaussTest_dist (p.toContinuousMapOn I) g
  rw [norm_sub_rev] at h₁
  calc
    |test A r g - gaussTest g| =
        |(test A r g - test A r (p.toContinuousMapOn I)) +
          (test A r (p.toContinuousMapOn I) - gaussTest (p.toContinuousMapOn I)) +
          (gaussTest (p.toContinuousMapOn I) - gaussTest g)| := by congr 1; ring
    _ ≤ |test A r g - test A r (p.toContinuousMapOn I)| +
        |test A r (p.toContinuousMapOn I) - gaussTest (p.toContinuousMapOn I)| +
        |gaussTest (p.toContinuousMapOn I) - gaussTest g| := abs_add_three _ _ _
    _ < ε := by linarith

lemma polynomial_test_limit {A : Set ℕ} {c : ℝ} (hc : c ≠ 0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)) (p : ℝ[X]) :
    Tendsto (fun r ↦ test A r (p.toContinuousMapOn I)) (𝓝[<] 1)
      (𝓝 (gaussTest (p.toContinuousMapOn I))) :=
  polynomial_test_limit_of_moments (witness_generating_power_ratio hc h) p

/-- Specialization of the continuous-test transfer to a hypothetical witness. -/
theorem continuous_test_limit {A : Set ℕ} {c : ℝ} (hc : c ≠ 0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)) (g : C(I, ℝ)) :
    Tendsto (fun r ↦ test A r g) (𝓝[<] 1) (𝓝 (gaussTest g)) :=
  continuous_test_limit_of_moments (witness_generating_power_ratio hc h) g

end Erdos66TauberianTests
