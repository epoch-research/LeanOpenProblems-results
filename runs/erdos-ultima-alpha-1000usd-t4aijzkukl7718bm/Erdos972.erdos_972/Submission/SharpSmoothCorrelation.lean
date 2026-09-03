import Submission.SharpSmoothMangoldt

/-! A sharper full-correlation comparison. The logarithmic cost is reduced
by combining the pointwise Euler-product bound with Chebyshev first moments,
rather than bounding both Mangoldt factors by their maximum. This supplies
no lower bound for the smoothed or prime-pair correlation. -/
namespace Erdos972SharpSmoothCorrelation

open Finset ArithmeticFunction Filter
open scoped Topology
open Erdos972PrimePowerError Erdos972SharpSmoothMangoldt
open Erdos972SmoothMangoldt Erdos972SmoothCorrelationApprox

lemma pair_error_via_mangoldt {t E : ℝ} (hE : 0 ≤ E) (m n : ℕ)
    (hm : |smoothMangoldt t m-Λ m| ≤ E) (hn : |smoothMangoldt t n-Λ n| ≤ E) :
    |smoothMangoldt t m*smoothMangoldt t n-Λ m*Λ n| ≤ E*(Λ m+Λ n)+E^2 := by
  have he : smoothMangoldt t m*smoothMangoldt t n-Λ m*Λ n =
      Λ m*(smoothMangoldt t n-Λ n)+Λ n*(smoothMangoldt t m-Λ m)+
        (smoothMangoldt t m-Λ m)*(smoothMangoldt t n-Λ n) := by ring
  rw [he]
  calc
    _ ≤ |Λ m*(smoothMangoldt t n-Λ n)| + |Λ n*(smoothMangoldt t m-Λ m)| +
        |(smoothMangoldt t m-Λ m)*(smoothMangoldt t n-Λ n)| :=
      (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
    _ = Λ m*|smoothMangoldt t n-Λ n|+Λ n*|smoothMangoldt t m-Λ m|+
        |smoothMangoldt t m-Λ m| * |smoothMangoldt t n-Λ n| := by
      simp only [abs_mul, abs_of_nonneg (vonMangoldt_nonneg (n := m)),
        abs_of_nonneg (vonMangoldt_nonneg (n := n))]
    _ ≤ Λ m*E+Λ n*E+E*E := by
      apply add_le_add
      · exact add_le_add (mul_le_mul_of_nonneg_left hn vonMangoldt_nonneg)
          (mul_le_mul_of_nonneg_left hm vonMangoldt_nonneg)
      · exact mul_le_mul hm hn (abs_nonneg _) hE
    _ = _ := by ring

lemma sum_output_mangoldt_le {α : ℝ} (hα : 1 ≤ α) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, Λ (floorMul α n)) ≤ (Real.log 4+4)*α*N := by
  classical
  calc
    _ = ∑ m ∈ (Ioc 0 N).image (floorMul α), Λ m := by
      rw [sum_image]
      exact (floorMul_strictMono hα).injective.injOn
    _ ≤ ∑ m ∈ Ioc 0 (floorMul α N), Λ m := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro m hm
        obtain ⟨n, hn, rfl⟩ := mem_image.mp hm
        exact mem_Ioc.mpr ⟨floorMul_pos hα (mem_Ioc.mp hn).1,
          (floorMul_strictMono hα).monotone (mem_Ioc.mp hn).2⟩
      · intro _ _ _
        exact vonMangoldt_nonneg
    _ = Chebyshev.psi (floorMul α N) := by simp only [Chebyshev.psi, Nat.floor_natCast]
    _ ≤ (Real.log 4+4)*(floorMul α N) := Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg _)
    _ ≤ _ := by
      have hC : (0 : ℝ) ≤ Real.log 4+4 := by positivity
      have hh := mul_le_mul_of_nonneg_left (floorMul_le_real hα (le_refl N)) hC
      simpa only [mul_assoc] using hh

noncomputable def scaledParameter (α t : ℝ) (N : ℕ) : ℝ :=
  t*(1+Real.log (floorMul α N))^2

/-- The exact finite comparison uses only two first moments and a quadratic
pointwise-error term. It holds for all positive t, not merely small t. -/
theorem smoothCorrelation_error_sharp {α t : ℝ} (hα : 1 ≤ α) (ht : 0 < t) (N : ℕ) :
    |smoothCorrelation t α N-mangoldtCorrelation α N| ≤
      ((Real.log 4+4)*(1+α)*scaledParameter α t N+(scaledParameter α t N)^2)*N := by
  let E := scaledParameter α t N
  have hE : 0 ≤ E := by dsimp [E, scaledParameter]; positivity
  have hC : (0 : ℝ) ≤ Real.log 4+4 := by positivity
  have hm (n : ℕ) (hn : n ∈ Ioc 0 N) :
      |smoothMangoldt t n-Λ n| ≤ E := by
    apply (smoothMangoldt_error_sharp ht n).trans
    apply mul_le_mul_of_nonneg_left _ ht.le
    have hnM : n ≤ floorMul α N := (mem_Ioc.mp hn).2.trans (self_le_floorMul hα N)
    have hl := Real.log_le_log (Nat.cast_pos.mpr (mem_Ioc.mp hn).1) (Nat.cast_le.mpr hnM)
    exact pow_le_pow_left₀ (Real.log_natCast_nonneg n) (by linarith only [hl]) 2
  have ho (n : ℕ) (hn : n ∈ Ioc 0 N) :
      |smoothMangoldt t (floorMul α n)-Λ (floorMul α n)| ≤ E := by
    apply (smoothMangoldt_error_sharp ht _).trans
    apply mul_le_mul_of_nonneg_left _ ht.le
    have hl := Real.log_le_log (Nat.cast_pos.mpr (floorMul_pos hα (mem_Ioc.mp hn).1))
      (Nat.cast_le.mpr ((floorMul_strictMono hα).monotone (mem_Ioc.mp hn).2))
    exact pow_le_pow_left₀ (Real.log_natCast_nonneg _) (by linarith only [hl]) 2
  have hi : (∑ n ∈ Ioc 0 N, Λ n) ≤ (Real.log 4+4)*N := by
    simpa only [Chebyshev.psi, Nat.floor_natCast] using
      Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg (α := ℝ) N)
  have hout := sum_output_mangoldt_le hα N
  unfold smoothCorrelation mangoldtCorrelation
  rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ Ioc 0 N, |smoothMangoldt t n*smoothMangoldt t (floorMul α n)-Λ n*Λ (floorMul α n)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Ioc 0 N, (E*(Λ n+Λ (floorMul α n))+E^2) :=
      sum_le_sum (fun n hn => pair_error_via_mangoldt hE n (floorMul α n) (hm n hn) (ho n hn))
    _ = E*((∑ n ∈ Ioc 0 N, Λ n)+(∑ n ∈ Ioc 0 N, Λ (floorMul α n)))+(N : ℝ)*E^2 := by
      simp only [sum_add_distrib, ← mul_sum, sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]
    _ ≤ E*((Real.log 4+4)*N+(Real.log 4+4)*α*N)+(N : ℝ)*E^2 := by
      exact add_le_add_left (mul_le_mul_of_nonneg_left (add_le_add hi hout) hE) _
    _ = _ := by dsimp only [E]; ring

/-- A general joint-parameter comparison theorem: t_N log(N)^2 -> 0 is
sufficient. This does not assert a mean formula for the smoothed correlation
at those parameters. -/
theorem variable_sharp_error_tendsto {α : ℝ} (hα : 1 ≤ α) (t : ℕ → ℝ)
    (ht : ∀ᶠ N : ℕ in atTop, 0 < t N)
    (hsmall : Tendsto (fun N => scaledParameter α (t N) N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (smoothCorrelation (t N) α N-mangoldtCorrelation α N)/(N : ℝ))
      atTop (𝓝 0) := by
  have hh := (hsmall.const_mul ((Real.log 4+4)*(1+α))).add (hsmall.pow 2)
  simp only [mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero] at hh
  apply squeeze_zero_norm' _ hh
  filter_upwards [ht, eventually_ge_atTop (1 : ℕ)] with N ht hN
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) N)]
  exact (div_le_iff₀ (Nat.cast_pos.mpr hN)).mpr (smoothCorrelation_error_sharp hα ht N)

noncomputable def cubeParameter (α : ℝ) (N : ℕ) : ℝ :=
  1/(1+Real.log (floorMul α N))^3

lemma cubeParameter_pos (α : ℝ) (N : ℕ) : 0 < cubeParameter α N := by
  unfold cubeParameter
  positivity [Real.log_natCast_nonneg (floorMul α N)]

lemma scaled_cubeParameter (α : ℝ) (N : ℕ) :
    scaledParameter α (cubeParameter α N) N = 1/(1+Real.log (floorMul α N)) := by
  have hL : 1+Real.log (floorMul α N) ≠ 0 := by
    have := Real.log_natCast_nonneg (floorMul α N)
    linarith
  unfold scaledParameter cubeParameter
  field_simp

/-- A larger concrete parameter than the preceding inverse-fifth-log
choice still gives an o(N) comparison with the actual Mangoldt correlation. -/
theorem cubeParameter_correlation_error_tendsto {α : ℝ} (hα : 1 ≤ α) :
    Tendsto (fun N : ℕ =>
      (smoothCorrelation (cubeParameter α N) α N-mangoldtCorrelation α N)/(N : ℝ))
      atTop (𝓝 0) := by
  apply variable_sharp_error_tendsto hα _ (Eventually.of_forall (cubeParameter_pos α))
  simp_rw [scaled_cubeParameter]
  have hM : Tendsto (floorMul α) atTop atTop :=
    tendsto_atTop_mono (self_le_floorMul hα) tendsto_id
  have hMR : Tendsto (fun N : ℕ => (floorMul α N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hM
  have hL : Tendsto (fun N : ℕ => 1+Real.log (floorMul α N)) atTop atTop := by
    apply tendsto_atTop_mono (fun N => show Real.log (floorMul α N) ≤ 1+Real.log (floorMul α N) by linarith)
    exact Real.tendsto_log_atTop.comp hMR
  exact tendsto_const_nhds.div_atTop hL

#print axioms smoothCorrelation_error_sharp
#print axioms variable_sharp_error_tendsto
#print axioms cubeParameter_correlation_error_tendsto

/-- Even throughout the improved comparison regime, the exponential
factor at any divisor cutoff D_N<=N tends to one. The new comparison
therefore cannot simply be substituted into a tail estimate requiring
that factor to tend to zero. This is not a bound on the actual signed tail. -/
theorem sharp_regime_damping_tendsto_one {α : ℝ} (hα : 1 ≤ α) (t : ℕ → ℝ)
    (ht : ∀ᶠ N : ℕ in atTop, 0 < t N)
    (hsmall : Tendsto (fun N => scaledParameter α (t N) N) atTop (𝓝 0))
    (D : ℕ → ℕ) (hD : ∀ᶠ N : ℕ in atTop, D N ≤ N) :
    Tendsto (fun N : ℕ => Real.exp (-(t N)*Real.log (D N))) atTop (𝓝 1) := by
  have hh : Tendsto (fun N : ℕ => t N*Real.log (D N)) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ hsmall
    · filter_upwards [ht] with N ht
      exact mul_nonneg ht.le (Real.log_natCast_nonneg _)
    · filter_upwards [ht, hD] with N ht hD
      have hlog : Real.log (D N) ≤ Real.log (floorMul α N) := by
        by_cases hD0 : D N = 0
        · simpa only [hD0, Nat.cast_zero, Real.log_zero] using Real.log_natCast_nonneg (floorMul α N)
        · exact Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hD0))
            (Nat.cast_le.mpr (hD.trans (self_le_floorMul hα N)))
      have hlarge : Real.log (floorMul α N) ≤ (1+Real.log (floorMul α N))^2 := by
        nlinarith only [sq_nonneg (Real.log (floorMul α N)), Real.log_natCast_nonneg (floorMul α N)]
      exact mul_le_mul_of_nonneg_left (hlog.trans hlarge) ht.le
  have hneg := hh.neg
  simp only [neg_zero] at hneg
  have he := (Real.continuous_exp.tendsto (0 : ℝ)).comp hneg
  simpa only [Real.exp_zero, Function.comp_def, ← neg_mul] using he

#print axioms sharp_regime_damping_tendsto_one

end Erdos972SharpSmoothCorrelation
