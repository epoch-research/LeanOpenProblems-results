import FormalConjectures.Util.ProblemImports

open Set Filter MeasureTheory intervalIntegral
open scoped BigOperators Interval

namespace Elliptic

noncomputable def K (m : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..Real.pi / 2, (Real.sqrt (1 - m * Real.sin x ^ 2))⁻¹

noncomputable def E (m : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..Real.pi / 2, Real.sqrt (1 - m * Real.sin x ^ 2)

lemma sin_sq_le_one (x : ℝ) : Real.sin x ^ 2 ≤ 1 := by
  nlinarith [sq_nonneg (Real.cos x), Real.sin_sq_add_cos_sq x]

lemma sin_sq_nonneg (x : ℝ) : 0 ≤ Real.sin x ^ 2 := sq_nonneg _

lemma radicand_pos {m : ℝ} (hm : m < 1) (x : ℝ) :
    0 < 1 - m * Real.sin x ^ 2 := by
  by_cases h : 0 ≤ m
  · have hs := sin_sq_le_one x
    nlinarith [mul_le_mul_of_nonneg_left hs h]
  · have hs := sin_sq_nonneg x
    have : m * Real.sin x ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge h) hs
    linarith

lemma continuous_K_integrand {m : ℝ} (hm : m < 1) :
    Continuous (fun x : ℝ => (Real.sqrt (1 - m * Real.sin x ^ 2))⁻¹) := by
  apply Continuous.inv₀
  · fun_prop
  · intro x
    exact (Real.sqrt_pos.2 (radicand_pos hm x)).ne'

lemma continuous_E_integrand (m : ℝ) :
    Continuous (fun x : ℝ => Real.sqrt (1 - m * Real.sin x ^ 2)) := by
  fun_prop

lemma intervalIntegrable_K {m : ℝ} (hm : m < 1) :
    IntervalIntegrable (fun x : ℝ => (Real.sqrt (1 - m * Real.sin x ^ 2))⁻¹)
      volume 0 (Real.pi / 2) :=
  (continuous_K_integrand hm).intervalIntegrable _ _

lemma intervalIntegrable_E (m : ℝ) :
    IntervalIntegrable (fun x : ℝ => Real.sqrt (1 - m * Real.sin x ^ 2))
      volume 0 (Real.pi / 2) :=
  (continuous_E_integrand m).intervalIntegrable _ _

lemma hasDerivAt_E_integrand {m x : ℝ} (hm : m < 1) :
    HasDerivAt (fun q : ℝ => Real.sqrt (1 - q * Real.sin x ^ 2))
      (- Real.sin x ^ 2 / (2 * Real.sqrt (1 - m * Real.sin x ^ 2))) m := by
  convert ((hasDerivAt_const m (1 : ℝ)).sub
    ((hasDerivAt_id m).mul_const (Real.sin x ^ 2))).sqrt
      (radicand_pos hm x).ne' using 1 <;>
    simp only [Pi.sub_apply, Pi.one_apply, id_eq] <;> ring

lemma hasDerivAt_K_integrand {m x : ℝ} (hm : m < 1) :
    HasDerivAt (fun q : ℝ => (Real.sqrt (1 - q * Real.sin x ^ 2))⁻¹)
      (Real.sin x ^ 2 / (2 * (Real.sqrt (1 - m * Real.sin x ^ 2)) ^ 3)) m := by
  have h := (hasDerivAt_E_integrand (x := x) hm).inv
    (Real.sqrt_pos.2 (radicand_pos hm x)).ne'
  convert h using 1
  field_simp [Real.sqrt_ne_zero'.2 (radicand_pos hm x)]


lemma radicand_ge_half {m q : ℝ} (hq0 : 0 ≤ q)
    (hq : q < (m + 1) / 2) (x : ℝ) :
    (1 - m) / 2 ≤ 1 - q * Real.sin x ^ 2 := by
  have hs := sin_sq_le_one x
  have hmul := mul_le_mul_of_nonneg_left hs hq0
  nlinarith

lemma derivE_bound {m q x : ℝ} (hm : m < 1) (hq0 : 0 ≤ q)
    (hq : q < (m + 1) / 2) :
    ‖- Real.sin x ^ 2 / (2 * Real.sqrt (1 - q * Real.sin x ^ 2))‖ ≤
      1 / (2 * Real.sqrt ((1 - m) / 2)) := by
  have hd : 0 < (1 - m) / 2 := by linarith
  have hr := radicand_ge_half hq0 hq x
  have hsqrt : Real.sqrt ((1-m)/2) ≤ Real.sqrt (1-q*Real.sin x^2) :=
    Real.sqrt_le_sqrt hr
  have hs0 : 0 ≤ Real.sin x ^ 2 := sin_sq_nonneg x
  have hs1 : Real.sin x ^ 2 ≤ 1 := sin_sq_le_one x
  have hroot : 0 < Real.sqrt (1-q*Real.sin x^2) := by
    exact lt_of_lt_of_le (Real.sqrt_pos.2 hd) hsqrt
  rw [Real.norm_eq_abs, abs_div, abs_neg, abs_of_nonneg hs0,
    abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
    abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    Real.sin x ^ 2 / (2 * Real.sqrt (1-q*Real.sin x^2)) ≤
        1 / (2 * Real.sqrt (1-q*Real.sin x^2)) := by
      exact (div_le_div_iff_of_pos_right (mul_pos (by norm_num) hroot)).2 hs1
    _ ≤ 1 / (2 * Real.sqrt ((1-m)/2)) := by
      gcongr

lemma hasDerivAt_E {m : ℝ} (hm0 : 0 < m) (hm : m < 1) :
    HasDerivAt E
      (∫ x in (0 : ℝ)..Real.pi / 2,
        - Real.sin x ^ 2 / (2 * Real.sqrt (1 - m * Real.sin x ^ 2))) m := by
  let s : Set ℝ := Ioo (m / 2) ((m + 1) / 2)
  let bound : ℝ → ℝ := fun _ => 1 / (2 * Real.sqrt ((1-m)/2))
  have hs : s ∈ nhds m := Ioo_mem_nhds (by linarith) (by linarith)
  have hmeas : ∀ᶠ q in nhds m,
      AEStronglyMeasurable (fun x : ℝ => Real.sqrt (1-q*Real.sin x^2))
        (volume.restrict (Ι (0:ℝ) (Real.pi/2))) := by
    filter_upwards [Iio_mem_nhds hm] with q hq
    exact (continuous_E_integrand q).aestronglyMeasurable
  have hdmeas : AEStronglyMeasurable
      (fun x : ℝ => - Real.sin x ^ 2 /
        (2 * Real.sqrt (1-m*Real.sin x^2)))
      (volume.restrict (Ι (0:ℝ) (Real.pi/2))) := by
    apply Continuous.aestronglyMeasurable
    apply Continuous.div₀
    · fun_prop
    · fun_prop
    · intro x
      exact mul_ne_zero (by norm_num) (Real.sqrt_pos.2 (radicand_pos hm x)).ne'
  have hbint : IntervalIntegrable bound volume 0 (Real.pi/2) := by
    exact _root_.intervalIntegrable_const
  have hbound : ∀ᵐ x ∂volume, x ∈ Ι (0:ℝ) (Real.pi/2) →
      ∀ q ∈ s, ‖-Real.sin x^2/(2*Real.sqrt (1-q*Real.sin x^2))‖ ≤ bound x := by
    filter_upwards [] with x hx q hq
    dsimp [s] at hq
    exact derivE_bound hm (by linarith [hq.1]) hq.2
  have hdiff : ∀ᵐ x ∂volume, x ∈ Ι (0:ℝ) (Real.pi/2) →
      ∀ q ∈ s, HasDerivAt (fun q : ℝ => Real.sqrt (1-q*Real.sin x^2))
        (-Real.sin x^2/(2*Real.sqrt (1-q*Real.sin x^2))) q := by
    filter_upwards [] with x hx q hq
    dsimp [s] at hq
    exact hasDerivAt_E_integrand (by linarith [hq.2])
  change HasDerivAt (fun m => ∫ x in (0:ℝ)..Real.pi/2,
    Real.sqrt (1-m*Real.sin x^2)) _ m
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hs hmeas (intervalIntegrable_E m) hdmeas hbound hbint hdiff).2


lemma derivK_bound {m q x : ℝ} (hm : m < 1) (hq0 : 0 ≤ q)
    (hq : q < (m + 1) / 2) :
    ‖Real.sin x ^ 2 / (2 * Real.sqrt (1 - q * Real.sin x ^ 2) ^ 3)‖ ≤
      1 / (2 * Real.sqrt ((1 - m) / 2) ^ 3) := by
  have hd : 0 < (1 - m) / 2 := by linarith
  have hr := radicand_ge_half hq0 hq x
  have hsqrt : Real.sqrt ((1-m)/2) ≤ Real.sqrt (1-q*Real.sin x^2) :=
    Real.sqrt_le_sqrt hr
  have hs0 : 0 ≤ Real.sin x ^ 2 := sin_sq_nonneg x
  have hs1 : Real.sin x ^ 2 ≤ 1 := sin_sq_le_one x
  have hroot : 0 < Real.sqrt (1-q*Real.sin x^2) :=
    lt_of_lt_of_le (Real.sqrt_pos.2 hd) hsqrt
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg hs0, abs_mul,
    abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_pow,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    Real.sin x ^ 2 / (2 * Real.sqrt (1-q*Real.sin x^2)^3) ≤
        1 / (2 * Real.sqrt (1-q*Real.sin x^2)^3) := by
      apply (div_le_div_iff_of_pos_right ?_).2 hs1
      positivity
    _ ≤ 1 / (2 * Real.sqrt ((1-m)/2)^3) := by
      gcongr

lemma hasDerivAt_K {m : ℝ} (hm0 : 0 < m) (hm : m < 1) :
    HasDerivAt K
      (∫ x in (0 : ℝ)..Real.pi / 2,
        Real.sin x ^ 2 / (2 * Real.sqrt (1 - m * Real.sin x ^ 2) ^ 3)) m := by
  let s : Set ℝ := Ioo (m / 2) ((m + 1) / 2)
  let bound : ℝ → ℝ := fun _ => 1 / (2 * Real.sqrt ((1-m)/2)^3)
  have hs : s ∈ nhds m := Ioo_mem_nhds (by linarith) (by linarith)
  have hmeas : ∀ᶠ q in nhds m,
      AEStronglyMeasurable
        (fun x : ℝ => (Real.sqrt (1-q*Real.sin x^2))⁻¹)
        (volume.restrict (Ι (0:ℝ) (Real.pi/2))) := by
    filter_upwards [Iio_mem_nhds hm] with q hq
    exact (continuous_K_integrand hq).aestronglyMeasurable
  have hdmeas : AEStronglyMeasurable
      (fun x : ℝ => Real.sin x ^ 2 /
        (2 * Real.sqrt (1-m*Real.sin x^2)^3))
      (volume.restrict (Ι (0:ℝ) (Real.pi/2))) := by
    apply Continuous.aestronglyMeasurable
    apply Continuous.div₀
    · fun_prop
    · fun_prop
    · intro x
      exact mul_ne_zero (by norm_num)
        (pow_ne_zero _ (Real.sqrt_pos.2 (radicand_pos hm x)).ne')
  have hbint : IntervalIntegrable bound volume 0 (Real.pi/2) :=
    _root_.intervalIntegrable_const
  have hbound : ∀ᵐ x ∂volume, x ∈ Ι (0:ℝ) (Real.pi/2) →
      ∀ q ∈ s, ‖Real.sin x^2/(2*Real.sqrt (1-q*Real.sin x^2)^3)‖ ≤ bound x := by
    filter_upwards [] with x hx q hq
    dsimp [s] at hq
    exact derivK_bound hm (by linarith [hq.1]) hq.2
  have hdiff : ∀ᵐ x ∂volume, x ∈ Ι (0:ℝ) (Real.pi/2) →
      ∀ q ∈ s, HasDerivAt
        (fun q : ℝ => (Real.sqrt (1-q*Real.sin x^2))⁻¹)
        (Real.sin x^2/(2*Real.sqrt (1-q*Real.sin x^2)^3)) q := by
    filter_upwards [] with x hx q hq
    dsimp [s] at hq
    exact hasDerivAt_K_integrand (by linarith [hq.2])
  change HasDerivAt (fun m => ∫ x in (0:ℝ)..Real.pi/2,
    (Real.sqrt (1-m*Real.sin x^2))⁻¹) _ m
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hs hmeas (intervalIntegrable_K hm) hdmeas hbound hbint hdiff).2


lemma E_sub_K_integral {m : ℝ} (hm : m < 1) :
    E m - K m = ∫ x in (0:ℝ)..Real.pi/2,
      -m * Real.sin x^2 / Real.sqrt (1-m*Real.sin x^2) := by
  rw [E, K, ← intervalIntegral.integral_sub
    (intervalIntegrable_E m) (intervalIntegrable_K hm)]
  apply intervalIntegral.integral_congr
  intro x hx
  have hp := radicand_pos hm x
  have hn := (Real.sqrt_pos.2 hp).ne'
  field_simp
  rw [Real.sq_sqrt hp.le]
  ring

lemma E_deriv_integral {m : ℝ} (hm0 : 0 < m) (hm : m < 1) :
    (∫ x in (0:ℝ)..Real.pi/2,
      - Real.sin x^2 / (2*Real.sqrt (1-m*Real.sin x^2))) =
      (E m - K m) / (2*m) := by
  rw [E_sub_K_integral hm]
  have h : (∫ x in (0:ℝ)..Real.pi/2,
      -m * Real.sin x^2 / Real.sqrt (1-m*Real.sin x^2)) =
      (2*m) * (∫ x in (0:ℝ)..Real.pi/2,
        - Real.sin x^2 / (2*Real.sqrt (1-m*Real.sin x^2))) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    ring
  rw [h]
  field_simp
  apply intervalIntegral.integral_congr
  intro x hx
  ring

lemma hasDerivAt_E_formula {m : ℝ} (hm0 : 0 < m) (hm : m < 1) :
    HasDerivAt E ((E m - K m) / (2*m)) m := by
  simpa [E_deriv_integral hm0 hm] using hasDerivAt_E hm0 hm


lemma hasDerivAt_aux {m x : ℝ} (hm : m < 1) :
    HasDerivAt
      (fun x : ℝ => Real.sin x * Real.cos x /
        Real.sqrt (1-m*Real.sin x^2))
      ((Real.cos x^2-Real.sin x^2) / Real.sqrt (1-m*Real.sin x^2) +
        m*Real.sin x^2*Real.cos x^2 / Real.sqrt (1-m*Real.sin x^2)^3) x := by
  have hp := radicand_pos hm x
  have hs : HasDerivAt (fun x : ℝ => Real.sin x ^ 2)
      (2 * Real.sin x * Real.cos x) x := by
    convert (Real.hasDerivAt_sin x).pow 2 using 1 <;> ring
  have hrad : HasDerivAt (fun x : ℝ => 1-m*Real.sin x^2)
      (-m*(2*Real.sin x*Real.cos x)) x := by
    convert (hasDerivAt_const x (1:ℝ)).sub (hs.const_mul m) using 1 <;> ring
  have hsqrt := hrad.sqrt hp.ne'
  have hnum := (Real.hasDerivAt_sin x).mul (Real.hasDerivAt_cos x)
  have h := hnum.div hsqrt (Real.sqrt_pos.2 hp).ne'
  convert h using 1
  simp only [Pi.mul_apply]
  field_simp [Real.sqrt_ne_zero'.2 hp]
  ring


lemma continuous_aux_deriv {m : ℝ} (hm : m < 1) : Continuous
    (fun x : ℝ =>
      ((Real.cos x^2-Real.sin x^2) / Real.sqrt (1-m*Real.sin x^2) +
        m*Real.sin x^2*Real.cos x^2 / Real.sqrt (1-m*Real.sin x^2)^3)) := by
  have hi := continuous_K_integrand hm
  simpa only [div_eq_mul_inv, inv_pow] using
    (((Real.continuous_cos.pow 2).sub (Real.continuous_sin.pow 2)).mul hi).add
      (((continuous_const.mul (Real.continuous_sin.pow 2)).mul
        (Real.continuous_cos.pow 2)).mul (hi.pow 3))


lemma integral_aux_deriv_zero {m : ℝ} (hm : m < 1) :
    (∫ x in (0:ℝ)..Real.pi/2,
      ((Real.cos x^2-Real.sin x^2) / Real.sqrt (1-m*Real.sin x^2) +
        m*Real.sin x^2*Real.cos x^2 / Real.sqrt (1-m*Real.sin x^2)^3)) = 0 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hasDerivAt_aux hm)
    ((continuous_aux_deriv hm).intervalIntegrable _ _)]
  simp

lemma K_deriv_integral {m : ℝ} (hm0 : 0 < m) (hm : m < 1) :
    (∫ x in (0:ℝ)..Real.pi/2,
      Real.sin x^2 / (2*Real.sqrt (1-m*Real.sin x^2)^3)) =
      (E m - (1-m)*K m) / (2*m*(1-m)) := by
  have hp : 0 < 1-m := by linarith
  let j : ℝ → ℝ := fun x => Real.sin x^2 / Real.sqrt (1-m*Real.sin x^2)^3
  let au : ℝ → ℝ := fun x =>
    (Real.cos x^2-Real.sin x^2) / Real.sqrt (1-m*Real.sin x^2) +
      m*Real.sin x^2*Real.cos x^2 / Real.sqrt (1-m*Real.sin x^2)^3
  have hj : IntervalIntegrable j volume 0 (Real.pi/2) := by
    apply Continuous.intervalIntegrable
    dsimp [j]
    have hi := continuous_K_integrand hm
    simpa only [div_eq_mul_inv, inv_pow] using
      (Real.continuous_sin.pow 2).mul (hi.pow 3)
  have hau : IntervalIntegrable au volume 0 (Real.pi/2) := by
    exact (continuous_aux_deriv hm).intervalIntegrable _ _
  have hpoint : ∀ x : ℝ,
      Real.sqrt (1-m*Real.sin x^2) -
          (1-m) / Real.sqrt (1-m*Real.sin x^2) =
        m*(1-m)*j x + m*au x := by
    intro x
    dsimp [j, au]
    have hr := radicand_pos hm x
    have ht := Real.sin_sq_add_cos_sq x
    field_simp [Real.sqrt_ne_zero'.2 hr]
    rw [Real.sq_sqrt hr.le]
    nlinarith
  have hEK : E m - (1-m)*K m =
      ∫ x in (0:ℝ)..Real.pi/2,
        (Real.sqrt (1-m*Real.sin x^2) -
          (1-m) / Real.sqrt (1-m*Real.sin x^2)) := by
    rw [E, K, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (intervalIntegrable_E m)
        ((intervalIntegrable_K hm).const_mul (1-m))]
    apply intervalIntegral.integral_congr
    intro x hx
    ring
  have hmain : E m - (1-m)*K m =
      m*(1-m) * (∫ x in (0:ℝ)..Real.pi/2, j x) := by
    calc
      E m - (1-m)*K m = ∫ x in (0:ℝ)..Real.pi/2,
          (Real.sqrt (1-m*Real.sin x^2) -
            (1-m) / Real.sqrt (1-m*Real.sin x^2)) := hEK
      _ = ∫ x in (0:ℝ)..Real.pi/2, (m*(1-m)*j x + m*au x) :=
        intervalIntegral.integral_congr (fun x hx => hpoint x)
      _ = (∫ x in (0:ℝ)..Real.pi/2, m*(1-m)*j x) +
          (∫ x in (0:ℝ)..Real.pi/2, m*au x) :=
        intervalIntegral.integral_add (hj.const_mul _) (hau.const_mul _)
      _ = m*(1-m) * (∫ x in (0:ℝ)..Real.pi/2, j x) +
          m * (∫ x in (0:ℝ)..Real.pi/2, au x) := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
      _ = m*(1-m) * (∫ x in (0:ℝ)..Real.pi/2, j x) := by
        rw [show (∫ x in (0:ℝ)..Real.pi/2, au x) = 0 by
          simpa [au] using integral_aux_deriv_zero hm]
        ring
  rw [hmain]
  have hhalf : (∫ x in (0:ℝ)..Real.pi/2,
      Real.sin x^2 / (2*Real.sqrt (1-m*Real.sin x^2)^3)) =
      (1/2:ℝ) * (∫ x in (0:ℝ)..Real.pi/2, j x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp [j]
    ring
  rw [hhalf]
  field_simp

lemma hasDerivAt_K_formula {m : ℝ} (hm0 : 0 < m) (hm : m < 1) :
    HasDerivAt K ((E m - (1-m)*K m) / (2*m*(1-m))) m := by
  rw [← K_deriv_integral hm0 hm]
  exact hasDerivAt_K hm0 hm


noncomputable def L (m : ℝ) : ℝ :=
  E m * K (1-m) + E (1-m) * K m - K m * K (1-m)

lemma hasDerivAt_L {m : ℝ} (hm0 : 0 < m) (hm : m < 1) :
    HasDerivAt L 0 m := by
  have hc0 : 0 < 1-m := by linarith
  have hc1 : 1-m < 1 := by linarith
  have hEm := hasDerivAt_E_formula hm0 hm
  have hKm := hasDerivAt_K_formula hm0 hm
  have hEc : HasDerivAt (fun m => E (1-m))
      (-((E (1-m)-K (1-m))/(2*(1-m)))) m := by
    convert (hasDerivAt_E_formula hc0 hc1).comp m
      ((hasDerivAt_const m (1:ℝ)).sub (hasDerivAt_id m)) using 1 <;> ring
  have hKc : HasDerivAt (fun m => K (1-m))
      (-((E (1-m)-m*K (1-m))/(2*(1-m)*m))) m := by
    convert (hasDerivAt_K_formula hc0 hc1).comp m
      ((hasDerivAt_const m (1:ℝ)).sub (hasDerivAt_id m)) using 1 <;> ring
  change HasDerivAt
    (fun m => E m*K (1-m) + E (1-m)*K m - K m*K (1-m)) 0 m
  convert (hEm.mul hKc).add (hEc.mul hKm) |>.sub (hKm.mul hKc) using 1
  field_simp
  ring

lemma L_eq_of_mem {a b : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hb0 : 0 < b) (hb1 : b < 1) : L a = L b := by
  wlog hab : a ≤ b generalizing a b
  · symm
    exact this hb0 hb1 ha0 ha1 (le_of_not_ge hab)
  have hcont : ContinuousOn L (Icc a b) := by
    intro x hx
    exact (hasDerivAt_L (lt_of_lt_of_le ha0 hx.1)
      (lt_of_le_of_lt hx.2 hb1)).continuousAt.continuousWithinAt
  have hc := constant_of_has_deriv_right_zero hcont
    (fun x hx => (hasDerivAt_L (lt_of_lt_of_le ha0 hx.1)
      (lt_trans hx.2 hb1)).hasDerivWithinAt)
  have hba : b ∈ Icc a b := ⟨hab, le_rfl⟩
  exact (hc b hba).symm



lemma inv_nat_succ_tendsto_zero :
    Tendsto (fun n : ℕ => (1 / (n:ℝ))) atTop (nhds 0) :=
  tendsto_one_div_atTop_nhds_zero_nat

lemma eventually_two_le : ∀ᶠ n : ℕ in atTop, 2 ≤ n := eventually_ge_atTop 2

lemma tendsto_K_zero_seq :
    Tendsto (fun n : ℕ => K (1/(n:ℝ))) atTop (nhds (Real.pi/2)) := by
  let μ := volume.restrict (Ioc (0:ℝ) (Real.pi/2))
  have hlim : ∀ᵐ x ∂μ, Tendsto
      (fun n : ℕ => (Real.sqrt (1-(1/(n:ℝ))*Real.sin x^2))⁻¹)
      atTop (nhds (1:ℝ)) := by
    filter_upwards [] with x
    have hq : Tendsto (fun n : ℕ => 1-(1/(n:ℝ))*Real.sin x^2)
        atTop (nhds (1:ℝ)) := by
      convert tendsto_const_nhds.sub
        (inv_nat_succ_tendsto_zero.mul_const (Real.sin x^2)) using 1 <;> ring
    convert hq.sqrt.inv₀ (by norm_num) using 1 <;> norm_num
  have hmeas : ∀ᶠ n : ℕ in atTop, AEStronglyMeasurable
      (fun x : ℝ => (Real.sqrt (1-(1/(n:ℝ))*Real.sin x^2))⁻¹) μ := by
    filter_upwards [eventually_two_le] with n hn
    have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hn1 : (1/(n:ℝ)) < 1 := by
      rw [div_lt_one hn0]
      exact_mod_cast (by omega : 1 < n)
    exact (continuous_K_integrand hn1).aestronglyMeasurable
  have hbound : ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, ∀ᵐ x ∂μ,
      ‖(Real.sqrt (1-(1/(n:ℝ))*Real.sin x^2))⁻¹‖ ≤ C := by
    refine ⟨2, ?_⟩
    filter_upwards [eventually_two_le] with n hn
    filter_upwards [] with x
    have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hu0 : 0 ≤ (1/(n:ℝ)) := by positivity
    have hu : (1/(n:ℝ)) ≤ 1/2 := by
      apply (div_le_iff₀ hn0).2
      have hnr : (2:ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    have hs := sin_sq_le_one x
    have hus : (1/(n:ℝ))*Real.sin x^2 ≤ 1/2 := by
      calc
        (1/(n:ℝ))*Real.sin x^2 ≤ (1/(n:ℝ))*1 :=
          mul_le_mul_of_nonneg_left hs hu0
        _ ≤ 1/2 := by simpa using hu
    have hr : (1/2:ℝ) ≤ 1-(1/(n:ℝ))*Real.sin x^2 := by linarith
    have hsqr := Real.sqrt_le_sqrt hr
    have hs2 : (1/2:ℝ) ≤ Real.sqrt (1/2) := by
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 1/2), Real.sqrt_nonneg (1/2)]
    have hroot : (1/2:ℝ) ≤ Real.sqrt (1-(1/(n:ℝ))*Real.sin x^2) := le_trans hs2 hsqr
    rw [Real.norm_eq_abs, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc
      (Real.sqrt (1-(1/(n:ℝ))*Real.sin x^2))⁻¹ ≤ ((1/2:ℝ))⁻¹ :=
        inv_anti₀ (by norm_num) hroot
      _ = 2 := by norm_num
  have ht := tendsto_integral_filter_of_norm_le_const hmeas hbound hlim
  rw [show (fun n : ℕ => K (1/(n:ℝ))) =
      fun (n : ℕ) => ∫ x, (Real.sqrt (1-(1/(n:ℝ))*Real.sin x^2))⁻¹ ∂μ by
    funext n
    rw [K, intervalIntegral.integral_of_le (by positivity)]
  ]
  convert ht using 1
  congr 1
  simp [μ, Real.volume_Ioc]
  positivity


lemma tendsto_E_zero_seq :
    Tendsto (fun n : ℕ => E (1/(n:ℝ))) atTop (nhds (Real.pi/2)) := by
  let μ := volume.restrict (Ioc (0:ℝ) (Real.pi/2))
  have hlim : ∀ᵐ x ∂μ, Tendsto
      (fun n : ℕ => Real.sqrt (1-(1/(n:ℝ))*Real.sin x^2))
      atTop (nhds (1:ℝ)) := by
    filter_upwards [] with x
    have hq : Tendsto (fun n : ℕ => 1-(1/(n:ℝ))*Real.sin x^2)
        atTop (nhds (1:ℝ)) := by
      convert tendsto_const_nhds.sub
        (inv_nat_succ_tendsto_zero.mul_const (Real.sin x^2)) using 1 <;> ring
    convert hq.sqrt using 1 <;> norm_num
  have hmeas : ∀ᶠ n : ℕ in atTop, AEStronglyMeasurable
      (fun x : ℝ => Real.sqrt (1-(1/(n:ℝ))*Real.sin x^2)) μ := by
    filter_upwards [] with n
    exact (continuous_E_integrand (1/(n:ℝ))).aestronglyMeasurable
  have hbound : ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, ∀ᵐ x ∂μ,
      ‖Real.sqrt (1-(1/(n:ℝ))*Real.sin x^2)‖ ≤ C := by
    refine ⟨2, ?_⟩
    filter_upwards [eventually_two_le] with n hn
    filter_upwards [] with x
    have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hu0 : 0 ≤ (1/(n:ℝ)) := by positivity
    have hrad0 : 0 ≤ 1-(1/(n:ℝ))*Real.sin x^2 := by
      have hu : (1/(n:ℝ)) ≤ 1 := by
        apply (div_le_iff₀ hn0).2
        have hnr : (1:ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
        simpa using hnr
      have := mul_le_mul_of_nonneg_left (sin_sq_le_one x) hu0
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    have hsquare := Real.sq_sqrt hrad0
    have hrle : 1-(1/(n:ℝ))*Real.sin x^2 ≤ 1 :=
      sub_le_self _ (mul_nonneg hu0 (sin_sq_nonneg x))
    nlinarith [Real.sqrt_nonneg (1-(1/(n:ℝ))*Real.sin x^2)]
  have ht := tendsto_integral_filter_of_norm_le_const hmeas hbound hlim
  rw [show (fun n : ℕ => E (1/(n:ℝ))) =
      fun (n : ℕ) => ∫ x, Real.sqrt (1-(1/(n:ℝ))*Real.sin x^2) ∂μ by
    funext n
    rw [E, intervalIntegral.integral_of_le (by positivity)]
  ]
  convert ht using 1
  congr 1
  simp [μ]
  positivity


lemma tendsto_E_compl_zero_seq :
    Tendsto (fun n : ℕ => E (1-1/(n:ℝ))) atTop (nhds 1) := by
  let μ := volume.restrict (Ioc (0:ℝ) (Real.pi/2))
  have hlim : ∀ᵐ x ∂μ, Tendsto
      (fun n : ℕ => Real.sqrt (1-(1-1/(n:ℝ))*Real.sin x^2))
      atTop (nhds (Real.sqrt (1-Real.sin x^2))) := by
    filter_upwards [] with x
    apply Filter.Tendsto.sqrt
    convert tendsto_const_nhds.sub
      ((tendsto_const_nhds.sub inv_nat_succ_tendsto_zero).mul_const
        (Real.sin x^2)) using 1 <;> ring
  have hmeas : ∀ᶠ n : ℕ in atTop, AEStronglyMeasurable
      (fun x : ℝ => Real.sqrt (1-(1-1/(n:ℝ))*Real.sin x^2)) μ := by
    filter_upwards [] with n
    exact (continuous_E_integrand (1-1/(n:ℝ))).aestronglyMeasurable
  have hbound : ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, ∀ᵐ x ∂μ,
      ‖Real.sqrt (1-(1-1/(n:ℝ))*Real.sin x^2)‖ ≤ C := by
    refine ⟨2, ?_⟩
    filter_upwards [eventually_two_le] with n hn
    filter_upwards [] with x
    have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hu0 : 0 ≤ (1/(n:ℝ)) := by positivity
    have hu : (1/(n:ℝ)) ≤ 1 := by
      apply (div_le_iff₀ hn0).2
      have hnr : (1:ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
      simpa using hnr
    have hc0 : 0 ≤ 1-1/(n:ℝ) := by linarith
    have hrad0 : 0 ≤ 1-(1-1/(n:ℝ))*Real.sin x^2 := by
      have := mul_le_mul_of_nonneg_left (sin_sq_le_one x) hc0
      nlinarith
    have hrle : 1-(1-1/(n:ℝ))*Real.sin x^2 ≤ 1 :=
      sub_le_self _ (mul_nonneg hc0 (sin_sq_nonneg x))
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    nlinarith [Real.sq_sqrt hrad0,
      Real.sqrt_nonneg (1-(1-1/(n:ℝ))*Real.sin x^2)]
  have ht := tendsto_integral_filter_of_norm_le_const hmeas hbound hlim
  have heval : (∫ x, Real.sqrt (1-Real.sin x^2) ∂μ) = 1 := by
    rw [← intervalIntegral.integral_of_le (μ := volume) (by positivity)]
    calc
      (∫ x in (0:ℝ)..Real.pi/2, Real.sqrt (1-Real.sin x^2)) =
          ∫ x in (0:ℝ)..Real.pi/2, Real.cos x := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hx' : x ∈ Icc (0:ℝ) (Real.pi/2) := by
          simpa [uIcc_of_le (by positivity : (0:ℝ) ≤ Real.pi/2)] using hx
        change Real.sqrt (1-Real.sin x^2) = Real.cos x
        rw [← Real.abs_cos_eq_sqrt_one_sub_sin_sq]
        exact abs_of_nonneg (Real.cos_nonneg_of_mem_Icc
          ⟨by linarith [Real.pi_pos.le, hx'.1], hx'.2⟩)
      _ = 1 := by rw [integral_cos]; simp
  rw [show (fun n : ℕ => E (1-1/(n:ℝ))) =
      fun (n : ℕ) => ∫ x, Real.sqrt (1-(1-1/(n:ℝ))*Real.sin x^2) ∂μ by
    funext n
    rw [E, intervalIntegral.integral_of_le (by positivity)]
  ]
  convert ht using 1
  rw [heval]



lemma norm_E_sub_K_le {m : ℝ} (hm0 : 0 ≤ m) (hm : m ≤ 1/2) :
    ‖E m - K m‖ ≤ m * Real.pi := by
  rw [E_sub_K_integral (by linarith)]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := Real.pi/2) (C := 2*m)
    (f := fun x : ℝ => -m * Real.sin x^2 / Real.sqrt (1-m*Real.sin x^2))
    (fun x hx => ?_)
  · convert hb using 1
    rw [sub_zero, abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.pi/2)]
    ring
  have hr : (1/2:ℝ) ≤ 1-m*Real.sin x^2 := by
    have hmul := mul_le_mul_of_nonneg_left (sin_sq_le_one x) hm0
    nlinarith
  have hsqrt := Real.sqrt_le_sqrt hr
  have hs2 : (1/2:ℝ) ≤ Real.sqrt (1/2) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 1/2), Real.sqrt_nonneg (1/2)]
  have hroot : (1/2:ℝ) ≤ Real.sqrt (1-m*Real.sin x^2) := le_trans hs2 hsqrt
  have hroot0 : 0 < Real.sqrt (1-m*Real.sin x^2) := lt_of_lt_of_le (by norm_num) hroot
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_neg, abs_of_nonneg hm0,
    abs_of_nonneg (sin_sq_nonneg x), abs_of_nonneg (Real.sqrt_nonneg _)]
  apply (div_le_iff₀ hroot0).2
  have hs := sin_sq_le_one x
  nlinarith [mul_nonneg hm0 (sin_sq_nonneg x)]

lemma norm_K_compl_le {m : ℝ} (hm0 : 0 < m) (hm1 : m ≤ 1) :
    ‖K (1-m)‖ ≤ (1 / Real.sqrt m) * (Real.pi/2) := by
  rw [K]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := Real.pi/2) (C := 1/Real.sqrt m)
    (f := fun x : ℝ => (Real.sqrt (1-(1-m)*Real.sin x^2))⁻¹)
    (fun x hx => ?_)
  · convert hb using 1
    rw [sub_zero, abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.pi/2)]
  have hc : 0 ≤ Real.cos x^2 := sq_nonneg _
  have hs : 0 ≤ Real.sin x^2 := sin_sq_nonneg x
  have ht := Real.sin_sq_add_cos_sq x
  have hr : m ≤ 1-(1-m)*Real.sin x^2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hm1) hc]
  have hsqrt := Real.sqrt_le_sqrt hr
  have hmroot : 0 < Real.sqrt m := Real.sqrt_pos.2 hm0
  have hroot : 0 < Real.sqrt (1-(1-m)*Real.sin x^2) := lt_of_lt_of_le hmroot hsqrt
  rw [Real.norm_eq_abs, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _)]
  simpa [one_div] using inv_anti₀ hmroot hsqrt

lemma tendsto_residual_zero : Tendsto
    (fun n : ℕ => (E (1/(n:ℝ))-K (1/(n:ℝ))) * K (1-1/(n:ℝ)))
    atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hg : Tendsto (fun n : ℕ => Real.pi^2 * Real.sqrt (1/(n:ℝ)))
      atTop (nhds 0) := by
    convert (inv_nat_succ_tendsto_zero.sqrt).const_mul (Real.pi^2) using 1 <;> norm_num
  apply squeeze_zero' (by filter_upwards [] with n; positivity) ?_ hg
  filter_upwards [eventually_two_le] with n hn
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hu0 : 0 < (1/(n:ℝ)) := by positivity
  have hu : (1/(n:ℝ)) ≤ 1/2 := by
    apply (div_le_iff₀ hn0).2
    have hnr : (2:ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  rw [norm_mul]
  calc
    ‖E (1/(n:ℝ))-K (1/(n:ℝ))‖ * ‖K (1-1/(n:ℝ))‖ ≤
        ((1/(n:ℝ))*Real.pi) *
          ((1/Real.sqrt (1/(n:ℝ)))*(Real.pi/2)) :=
      mul_le_mul (norm_E_sub_K_le hu0.le hu)
        (norm_K_compl_le hu0 (by linarith [hu])) (norm_nonneg _) (by positivity)
    _ ≤ Real.pi^2 * Real.sqrt (1/(n:ℝ)) := by
      have hs : Real.sqrt (1/(n:ℝ)) ^ 2 = 1/(n:ℝ) :=
        Real.sq_sqrt hu0.le
      have hs0 := Real.sqrt_pos.2 hu0
      have hdiv : (1/(n:ℝ)) / Real.sqrt (1/(n:ℝ)) =
          Real.sqrt (1/(n:ℝ)) := by
        apply (div_eq_iff hs0.ne').2
        nlinarith [hs]
      have heq : ((1/(n:ℝ))*Real.pi) *
          ((1/Real.sqrt (1/(n:ℝ)))*(Real.pi/2)) =
          (Real.pi^2/2) * Real.sqrt (1/(n:ℝ)) := by
        rw [show (1 / Real.sqrt (1/(n:ℝ))) =
          (Real.sqrt (1/(n:ℝ)))⁻¹ by rw [one_div]
        ]
        calc
          ((1/(n:ℝ))*Real.pi) *
              ((Real.sqrt (1/(n:ℝ)))⁻¹*(Real.pi/2)) =
              ((1/(n:ℝ))/Real.sqrt (1/(n:ℝ))) * (Real.pi^2/2) := by ring
          _ = _ := by rw [hdiv]; ring
      rw [heq]
      nlinarith [mul_nonneg (sq_nonneg Real.pi) hs0.le]


lemma tendsto_L_zero_seq :
    Tendsto (fun n : ℕ => L (1/(n:ℝ))) atTop (nhds (Real.pi/2)) := by
  have h := (tendsto_E_compl_zero_seq.mul tendsto_K_zero_seq).add
    tendsto_residual_zero
  convert h using 1
  · funext n
    simp [L]
    ring
  · ring

/-- Legendre's relation for complete elliptic integrals, in parameter notation. -/
theorem legendre_relation {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1) :
    E m * K (1-m) + E (1-m) * K m - K m * K (1-m) = Real.pi/2 := by
  have hevent : ∀ᶠ n : ℕ in atTop, L m = L (1/(n:ℝ)) := by
    filter_upwards [eventually_two_le] with n hn
    have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hu0 : 0 < (1/(n:ℝ)) := by positivity
    have hu1 : (1/(n:ℝ)) < 1 := by
      rw [div_lt_one hn0]
      exact_mod_cast (by omega : 1 < n)
    exact L_eq_of_mem hm0 hm1 hu0 hu1
  have hc : Tendsto (fun _ : ℕ => L m) atTop (nhds (L m)) := tendsto_const_nhds
  have hm_lim : Tendsto (fun n : ℕ => L (1/(n:ℝ))) atTop (nhds (L m)) :=
    hc.congr' hevent
  have := tendsto_nhds_unique hm_lim tendsto_L_zero_seq
  simpa [L] using this

noncomputable def H (m : ℝ) : ℝ := (2/Real.pi) * K m
noncomputable def En (m : ℝ) : ℝ := (2/Real.pi) * E m

theorem normalized_legendre_relation {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1) :
    En m * H (1-m) + En (1-m) * H m - H m * H (1-m) = 2/Real.pi := by
  have hl := legendre_relation hm0 hm1
  simp only [En, H]
  field_simp [Real.pi_ne_zero]
  linarith [hl]









end Elliptic
