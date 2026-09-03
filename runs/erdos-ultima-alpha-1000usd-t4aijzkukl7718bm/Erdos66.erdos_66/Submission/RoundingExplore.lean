import Submission.FractionalProfileExplore
import Submission.GeneratingExplore

/-!
# The quadratic error left by rounding the harmonic fractional profile

Bounded prefix discrepancy controls the mixed convolution term. It does not
control the self-convolution of the rounding error; that remains an unproved
condition in the sufficient construction criterion below.
-/

namespace Erdos66Rounding
open AdditiveCombinatorics Erdos66Fractional Erdos66Generating Filter
open scoped Topology

noncomputable def prefixSum (e : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), e i

lemma prefix_first_difference (e : ℕ → ℝ) :
    (1 - PowerSeries.X) * PowerSeries.mk (prefixSum e) = PowerSeries.mk e := by
  rw [sub_mul, one_mul]
  ext n
  cases n with
  | zero => simp [prefixSum]
  | succ n =>
    simp only [map_sub, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk, prefixSum]
    rw [Finset.sum_range_succ]
    ring

lemma mixed_convolution_identity (e : ℕ → ℝ) (n : ℕ) :
    sumConv e profile n = prefixSum e n - sumConv (prefixSum e) stepMass n := by
  have he : PowerSeries.mk e * PowerSeries.mk profile =
      PowerSeries.mk (prefixSum e) - PowerSeries.mk (prefixSum e) * PowerSeries.mk stepMass := by
    rw [← prefix_first_difference e]
    calc
      _ = PowerSeries.mk (prefixSum e) * ((1 - PowerSeries.X) * PowerSeries.mk profile) := by ring
      _ = _ := by rw [profile_first_difference]; ring
  have hh := congrArg (PowerSeries.coeff n) he
  simpa only [map_sub, PowerSeries.coeff_mul, PowerSeries.coeff_mk, sumConv] using hh

lemma mixed_convolution_bound (e : ℕ → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (h : ∀ n, |prefixSum e n| ≤ D) (n : ℕ) : |sumConv e profile n| ≤ 2 * D := by
  have htail : |sumConv (prefixSum e) stepMass n| ≤ D := by
    calc
      _ ≤ ∑ p ∈ Finset.antidiagonal n, |prefixSum e p.1 * stepMass p.2| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ Finset.antidiagonal n, D * stepMass p.2 := by
        apply Finset.sum_le_sum
        intro p hp
        rw [abs_mul, abs_of_nonneg (stepMass_nonneg _)]
        exact mul_le_mul_of_nonneg_right (h p.1) (stepMass_nonneg _)
      _ = D * ∑ i ∈ Finset.range (n + 1), stepMass i := by
        rw [← Finset.mul_sum, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        congr 1
        simpa only [Nat.add_sub_cancel] using Finset.sum_range_reflect stepMass (n + 1)
      _ ≤ D := (mul_le_mul_of_nonneg_left (stepMass_partial_le_one _) hD).trans_eq (mul_one D)
  rw [mixed_convolution_identity]
  exact (abs_sub _ _).trans (by linarith [h n])

lemma mixed_convolution_log_limit (e : ℕ → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (h : ∀ n, |prefixSum e n| ≤ D) :
    Tendsto (fun n ↦ sumConv e profile n / Real.log n) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n ↦ abs_nonneg _)) ?_
    (hlog.const_div_atTop (2 * D))
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hl : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  rw [abs_div, abs_of_pos hl]
  exact div_le_div_of_nonneg_right (mixed_convolution_bound e D hD h n) hl.le

lemma sumConv_comm_real (f g : ℕ → ℝ) (n : ℕ) : sumConv f g n = sumConv g f n := by
  have hh := congrArg (PowerSeries.coeff n)
    (mul_comm (PowerSeries.mk f) (PowerSeries.mk g))
  simpa only [PowerSeries.coeff_mul, PowerSeries.coeff_mk, sumConv] using hh

lemma sumConv_add_self (f g : ℕ → ℝ) (n : ℕ) :
    sumConv (fun i ↦ f i + g i) (fun i ↦ f i + g i) n =
      sumConv f f n + 2 * sumConv f g n + sumConv g g n := by
  have he (p : ℕ × ℕ) : (f p.1 + g p.1) * (f p.2 + g p.2) =
      f p.1 * f p.2 + f p.1 * g p.2 + g p.1 * f p.2 + g p.1 * g p.2 := by ring
  unfold sumConv
  simp_rw [he, Finset.sum_add_distrib]
  change sumConv f f n + sumConv f g n + sumConv g f n + sumConv g g n =
    sumConv f f n + 2 * sumConv f g n + sumConv g g n
  rw [sumConv_comm_real g f]
  ring

noncomputable def roundingError (A : Set ℕ) (n : ℕ) : ℝ := indicator A n - profile n

lemma rounding_decomposition (A : Set ℕ) (n : ℕ) :
    (sumRep A n : ℝ) = (harmonic (n + 1) : ℝ) +
      2 * sumConv (roundingError A) profile n + sumConv (roundingError A) (roundingError A) n := by
  have he : indicator A = fun n ↦ profile n + roundingError A n := by
    funext n
    simp only [roundingError]
    ring
  rw [← sum_indicator_antidiagonal A n]
  change sumConv (indicator A) (indicator A) n = _
  rw [he, sumConv_add_self, profile_convolution, sumConv_comm_real profile]

/-- Within the bounded-discrepancy class, the missing rounding estimate is exactly
the vanishing of the quadratic error divided by `log n`. -/
theorem logarithmic_limit_iff_quadratic_error (A : Set ℕ) (D : ℝ) (hD : 0 ≤ D)
    (h : ∀ n, |prefixSum (roundingError A) n| ≤ D) :
    Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 1) ↔
      Tendsto (fun n ↦ sumConv (roundingError A) (roundingError A) n / Real.log n)
        atTop (𝓝 0) := by
  have hm := (mixed_convolution_log_limit (roundingError A) D hD h).const_mul 2
  simp only [mul_zero] at hm
  constructor
  · intro hA
    have hh := (hA.sub harmonic_shift_log_ratio).sub hm
    simp only [sub_self] at hh
    apply hh.congr'
    filter_upwards [] with n
    rw [rounding_decomposition]
    ring
  · intro he
    have hh := (harmonic_shift_log_ratio.add hm).add he
    simp only [add_zero] at hh
    apply hh.congr'
    filter_upwards [] with n
    rw [rounding_decomposition]
    ring

noncomputable def cumulative (p : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, p i

noncomputable def roundedSet (p : ℕ → ℝ) : Set ℕ :=
  {n | Int.floor (cumulative p (n + 1)) - Int.floor (cumulative p n) = 1}

lemma cumulative_succ (p : ℕ → ℝ) (n : ℕ) : cumulative p (n + 1) = cumulative p n + p n := by
  exact Finset.sum_range_succ _ _

lemma floor_increment_binary (p : ℕ → ℝ) (hp : ∀ n, 0 ≤ p n ∧ p n ≤ 1) (n : ℕ) :
    Int.floor (cumulative p (n + 1)) - Int.floor (cumulative p n) = 0 ∨
      Int.floor (cumulative p (n + 1)) - Int.floor (cumulative p n) = 1 := by
  have hlo := Int.floor_mono (show cumulative p n ≤ cumulative p (n + 1) by
    rw [cumulative_succ]; linarith [hp n])
  have hhi := Int.floor_mono (show cumulative p (n + 1) ≤ cumulative p n + 1 by
    rw [cumulative_succ]; linarith [hp n])
  rw [Int.floor_add_one] at hhi
  omega

lemma rounded_indicator_eq (p : ℕ → ℝ) (hp : ∀ n, 0 ≤ p n ∧ p n ≤ 1) (n : ℕ) :
    indicator (roundedSet p) n =
      (Int.floor (cumulative p (n + 1)) : ℝ) - (Int.floor (cumulative p n) : ℝ) := by
  classical
  have he := floor_increment_binary p hp n
  unfold indicator roundedSet
  simp only [Set.mem_setOf_eq]
  rcases he with he | he
  · rw [if_neg (by omega)]
    exact_mod_cast he.symm
  · rw [if_pos he]
    exact_mod_cast he.symm

lemma rounded_prefix_sum (p : ℕ → ℝ) (hp : ∀ n, 0 ≤ p n ∧ p n ≤ 1) (N : ℕ) :
    (∑ i ∈ Finset.range N, indicator (roundedSet p) i) = (Int.floor (cumulative p N) : ℝ) := by
  simp_rw [rounded_indicator_eq p hp]
  rw [Finset.sum_range_sub (fun i : ℕ ↦ (Int.floor (cumulative p i) : ℝ)) N]
  simp [cumulative]

lemma rounded_prefix_discrepancy (p : ℕ → ℝ) (hp : ∀ n, 0 ≤ p n ∧ p n ≤ 1) (N : ℕ) :
    |∑ i ∈ Finset.range N, (indicator (roundedSet p) i - p i)| ≤ 1 := by
  rw [Finset.sum_sub_distrib, rounded_prefix_sum p hp]
  change |(Int.floor (cumulative p N) : ℝ) - cumulative p N| ≤ 1
  rw [abs_le]
  constructor
  · linarith [Int.lt_floor_add_one (cumulative p N)]
  · linarith [Int.floor_le (cumulative p N)]

lemma harmonic_rounding_discrepancy :
    ∀ n, |prefixSum (roundingError (roundedSet profile)) n| ≤ 1 := by
  intro n
  exact rounded_prefix_discrepancy profile (fun n ↦ ⟨profile_nonneg n, profile_le_one n⟩) (n + 1)

/-- This conditional theorem isolates, but does not prove, a sufficient rounding estimate. -/
theorem rounded_profile_suffices
    (h : Tendsto (fun n ↦ sumConv (roundingError (roundedSet profile))
      (roundingError (roundedSet profile)) n / Real.log n) atTop (𝓝 0)) :
    ∃ (A : Set ℕ) (c : ℝ), c ≠ 0 ∧
      Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c) := by
  refine ⟨roundedSet profile, 1, one_ne_zero, ?_⟩
  exact (logarithmic_limit_iff_quadratic_error _ 1 (by norm_num) harmonic_rounding_discrepancy).mpr h

noncomputable def alternatingError (n : ℕ) : ℝ := (-1 : ℝ) ^ n / 2

lemma alternating_prefix_bound (n : ℕ) : |prefixSum alternatingError n| ≤ 1 / 2 := by
  have he := geom_sum_mul_neg (-1 : ℝ) (n + 1)
  have hp : |(-1 : ℝ) ^ (n + 1)| = 1 := by simp
  have hs : prefixSum alternatingError n = (1 - (-1 : ℝ) ^ (n + 1)) / 4 := by
    unfold prefixSum alternatingError
    rw [← Finset.sum_div]
    linarith
  rw [hs, abs_div]
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  have hb := abs_sub (1 : ℝ) ((-1 : ℝ) ^ (n + 1))
  norm_num only [abs_one, hp] at hb
  linarith

lemma alternating_quadratic_error (n : ℕ) :
    sumConv alternatingError alternatingError n = ((n : ℝ) + 1) * (-1 : ℝ) ^ n / 4 := by
  unfold sumConv alternatingError
  calc
    _ = ∑ p ∈ Finset.antidiagonal n, (-1 : ℝ) ^ n / 4 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [← Finset.mem_antidiagonal.mp hp, pow_add]
      ring
    _ = _ := by simp [Finset.Nat.card_antidiagonal, nsmul_eq_mul, mul_div_assoc]

/-- Bounded prefix discrepancy alone cannot imply a small quadratic convolution error. -/
lemma alternating_not_quadratic_log_limit :
    ¬Tendsto (fun n ↦ sumConv alternatingError alternatingError n / Real.log n)
      atTop (𝓝 0) := by
  intro h
  have ha := h.abs
  simp only [abs_zero] at ha
  have he := ha.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))
  obtain ⟨n, hn, he⟩ := ((eventually_ge_atTop 2).and he).exists
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hl : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  rw [alternating_quadratic_error, abs_div, abs_div, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1), abs_of_pos hl] at he
  norm_num only [abs_pow, abs_neg, abs_one, one_pow, mul_one, abs_of_pos (by norm_num : (0 : ℝ) < 4)] at he
  have hb := Real.log_le_sub_one_of_pos hn0
  have he' := (div_lt_iff₀ hl).mp he
  nlinarith

end Erdos66Rounding
