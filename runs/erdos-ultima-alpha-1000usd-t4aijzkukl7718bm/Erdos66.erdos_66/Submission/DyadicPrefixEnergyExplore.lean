import FormalConjecturesUtil

/-! A scalar multiscale energy test.  This file does not assert that a
hypothetical witness to Erdős 66 supplies the hypotheses of the test. -/
namespace Erdos66DyadicPrefixEnergy
open Filter
open scoped Topology

noncomputable def running (x : ℕ → ℝ) : ℕ → ℝ
  | 0 => x 0
  | n + 1 => x (n + 1) + running x n / 2

lemma running_step_sq (x : ℕ → ℝ) (n : ℕ) :
    2 * running x (n + 1) ^ 2 ≤ 4 * x (n + 1) ^ 2 + running x n ^ 2 := by
  rw [running]
  nlinarith [sq_nonneg (2 * x (n + 1) - running x n)]

lemma finite_energy_with_tail (x : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), running x j ^ 2) + running x n ^ 2 ≤
      4 * ∑ j ∈ Finset.range (n + 1), x j ^ 2 := by
  induction n with
  | zero => simp only [Nat.zero_add, Finset.sum_range_one, running]; nlinarith [sq_nonneg (x 0)]
  | succ n ih =>
      rw [Finset.sum_range_succ (f := fun j ↦ running x j ^ 2) (n + 1),
        Finset.sum_range_succ (f := fun j ↦ x j ^ 2) (n + 1)]
      have hs := running_step_sq x n
      nlinarith

lemma finite_energy (x : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n, running x j ^ 2) ≤
      4 * ∑ j ∈ Finset.range n, x j ^ 2 := by
  cases n with
  | zero => simp
  | succ n =>
      have hh := finite_energy_with_tail x n
      nlinarith [sq_nonneg (running x n)]

/-- Geometrically weighted cumulative sums preserve square summability. -/
theorem summable_running_sq (x : ℕ → ℝ)
    (hx : Summable (fun n ↦ x n ^ 2)) :
    Summable (fun n ↦ running x n ^ 2) := by
  apply summable_of_sum_range_le (fun n ↦ sq_nonneg _) (c := 4 * ∑' n, x n ^ 2)
  intro n
  exact (finite_energy x n).trans (mul_le_mul_of_nonneg_left
    (hx.sum_le_tsum (Finset.range n) (fun j hj ↦ sq_nonneg _)) (by norm_num))

lemma running_eq_scaled_prefix (y : ℕ → ℝ) (n : ℕ) :
    running (fun j ↦ y j / (2 : ℝ) ^ j) n =
      (∑ j ∈ Finset.range (n + 1), y j) / (2 : ℝ) ^ n := by
  induction n with
  | zero => simp [running]
  | succ n ih =>
      rw [running, ih, Finset.sum_range_succ (f := y) (n + 1), pow_succ]
      ring

/-- The squared cumulative mass normalized by 4^n is summable whenever
the squared masses of the separate geometric blocks have summable energy. -/
theorem summable_scaled_prefix_sq (y E : ℕ → ℝ)
    (hE : Summable E)
    (hblock : ∀ n, y n ^ 2 ≤ (4 : ℝ) ^ n * E n) :
    Summable (fun n ↦ (∑ j ∈ Finset.range (n + 1), y j) ^ 2 / (4 : ℝ) ^ n) := by
  have hp (n : ℕ) : ((2 : ℝ) ^ n) ^ 2 = (4 : ℝ) ^ n := by
    rw [pow_two, ← mul_pow]
    norm_num
  have hx : Summable (fun n ↦ (y n / (2 : ℝ) ^ n) ^ 2) := by
    apply hE.of_nonneg_of_le (fun n ↦ sq_nonneg _) (fun n ↦ ?_)
    rw [div_pow, hp]
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < (4 : ℝ) ^ n)).mpr
      (by simpa only [mul_comm] using hblock n)
  have hh := summable_running_sq (fun n ↦ y n / (2 : ℝ) ^ n) hx
  simpa only [running_eq_scaled_prefix, div_pow, hp] using hh

/-- A positive harmonic lower floor at every sufficiently late scale is
incompatible with the preceding finite total energy. -/
theorem no_eventual_harmonic_floor (y E : ℕ → ℝ)
    (hE : Summable E)
    (hblock : ∀ n, y n ^ 2 ≤ (4 : ℝ) ^ n * E n)
    (c : ℝ) (hc : 0 < c) :
    ¬ (∀ᶠ n : ℕ in atTop,
      c / ((n : ℝ) + 1) ≤
        (∑ j ∈ Finset.range (n + 1), y j) ^ 2 / (4 : ℝ) ^ n) := by
  intro hf
  have hs := summable_scaled_prefix_sq y E hE hblock
  have hh : Summable (fun n : ℕ ↦ c / ((n : ℝ) + 1)) := by
    apply hs.of_norm_bounded_eventually_nat
    filter_upwards [hf] with n hn
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ c / ((n : ℝ) + 1))]
    exact hn
  have hunit : Summable (fun n : ℕ ↦ (1 : ℝ) / ((n : ℝ) + 1)) := by
    convert hh.mul_left c⁻¹ using 1
    ext n
    field_simp
  exact Real.not_summable_one_div_natCast
    ((summable_nat_add_iff 1).mp (by simpa only [Nat.cast_add, Nat.cast_one] using hunit))

end Erdos66DyadicPrefixEnergy
