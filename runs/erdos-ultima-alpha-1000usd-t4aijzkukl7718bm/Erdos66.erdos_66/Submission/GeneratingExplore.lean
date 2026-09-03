import Submission.CountingExplore
import Submission.Explore

/-!
# Generating functions for the logarithmic representation conjecture

These are auxiliary necessary conditions, not a solution of Erdős Problem 66.
-/

namespace Erdos66Generating
open Filter AdditiveCombinatorics
open scoped Topology

noncomputable def series (f : ℕ → ℝ) (r : ℝ) : ℝ := ∑' n, f n * r ^ n

noncomputable def indicator (A : Set ℕ) (n : ℕ) : ℝ := by
  classical
  exact if n ∈ A then 1 else 0

lemma indicator_nonneg (A : Set ℕ) (n : ℕ) : 0 ≤ indicator A n := by
  classical
  simp only [indicator]
  split <;> norm_num

lemma indicator_le_one (A : Set ℕ) (n : ℕ) : indicator A n ≤ 1 := by
  classical
  simp only [indicator]
  split <;> norm_num

lemma summable_indicator (A : Set ℕ) {r : ℝ} (hr : |r| < 1) :
    Summable (fun n ↦ indicator A n * r ^ n) := by
  apply Summable.of_norm_bounded (summable_geometric_of_lt_one (abs_nonneg r) hr)
  intro n
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (indicator_nonneg A n), norm_pow,
    Real.norm_eq_abs]
  exact mul_le_of_le_one_left (pow_nonneg (abs_nonneg r) n) (indicator_le_one A n)

lemma sum_indicator_antidiagonal (A : Set ℕ) (n : ℕ) :
    (∑ p ∈ Finset.antidiagonal n, indicator A p.1 * indicator A p.2) = sumRep A n := by
  classical
  rw [sumRep_def, Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro p hp
  simp only [indicator]
  split_ifs <;> simp_all

lemma generating_identity (A : Set ℕ) {r : ℝ} (hr : |r| < 1) :
    series (indicator A) r ^ 2 = series (fun n ↦ (sumRep A n : ℝ)) r := by
  unfold series
  rw [pow_two, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
    (summable_indicator A hr).norm (summable_indicator A hr).norm]
  apply tsum_congr
  intro n
  calc
    _ = ∑ p ∈ Finset.antidiagonal n, (indicator A p.1 * indicator A p.2) * r ^ n := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [← Finset.mem_antidiagonal.mp hp, pow_add]
      ring
    _ = _ := by rw [← Finset.sum_mul, sum_indicator_antidiagonal]

lemma summable_sumRep (A : Set ℕ) {r : ℝ} (hr : |r| < 1) :
    Summable (fun n ↦ (sumRep A n : ℝ) * r ^ n) := by
  have hpoly := (summable_pow_mul_geometric_of_norm_lt_one 1
    (show ‖|r|‖ < 1 by simpa using hr)).add
      (summable_geometric_of_lt_one (abs_nonneg r) hr)
  apply Summable.of_norm_bounded hpoly
  intro n
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _), norm_pow,
    Real.norm_eq_abs]
  calc
    _ ≤ ((n : ℝ) + 1) * |r| ^ n := by
      gcongr
      exact_mod_cast Erdos66Counting.sumRep_le_succ A n
    _ = _ := by ring

lemma harmonic_nonneg (n : ℕ) : 0 ≤ (harmonic n : ℝ) := by
  unfold harmonic
  push_cast
  positivity

lemma harmonic_le_nat (n : ℕ) : (harmonic n : ℝ) ≤ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [harmonic_succ]
    push_cast
    have : ((n : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
    linarith

lemma summable_harmonic {r : ℝ} (hr : |r| < 1) :
    Summable (fun n ↦ (harmonic n : ℝ) * r ^ n) := by
  apply Summable.of_norm_bounded (summable_pow_mul_geometric_of_norm_lt_one 1
    (show ‖|r|‖ < 1 by simpa using hr))
  intro n
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (harmonic_nonneg n), norm_pow,
    Real.norm_eq_abs, pow_one]
  exact mul_le_mul_of_nonneg_right (harmonic_le_nat n) (pow_nonneg (abs_nonneg r) n)

lemma harmonic_series {r : ℝ} (hr : |r| < 1) :
    (1 - r) * series (fun n ↦ (harmonic n : ℝ)) r = -Real.log (1 - r) := by
  have hh := (summable_harmonic hr).tsum_eq_zero_add
  have hs : Summable (fun n : ℕ ↦ (harmonic n : ℝ) * r ^ (n + 1)) := by
    simpa only [pow_succ, mul_assoc] using (summable_harmonic hr).mul_right r
  have hl := Real.hasSum_pow_div_log_of_abs_lt_one hr
  have he : ∀ n : ℕ, (harmonic (n + 1) : ℝ) * r ^ (n + 1) =
      (harmonic n : ℝ) * r ^ (n + 1) + r ^ (n + 1) / (n + 1) := by
    intro n
    rw [harmonic_succ]
    push_cast
    ring
  simp only [he] at hh
  rw [hs.tsum_add hl.summable, hl.tsum_eq] at hh
  simp only [harmonic_zero, Rat.cast_zero, zero_mul, zero_add] at hh
  rw [show (∑' n, (harmonic n : ℝ) * r ^ (n + 1)) =
    series (fun n ↦ (harmonic n : ℝ)) r * r by
      simp only [series, pow_succ, ← mul_assoc, tsum_mul_right]] at hh
  dsimp only [series] at *
  linarith

lemma harmonic_log_ratio :
    Tendsto (fun n : ℕ ↦ (harmonic n : ℝ) / Real.log n) atTop (𝓝 1) := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hh := (Real.tendsto_harmonic_sub_log.div_atTop hlog).add_const 1
  simp only [zero_add] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hl : Real.log (n : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hn))
  field_simp
  ring

lemma harmonic_ratio {f : ℕ → ℝ} {c : ℝ}
    (h : Tendsto (fun n ↦ f n / Real.log n) atTop (𝓝 c)) :
    Tendsto (fun n ↦ f n / (harmonic n : ℝ)) atTop (𝓝 c) := by
  have hh := h.div harmonic_log_ratio (by norm_num : (1 : ℝ) ≠ 0)
  simp only [div_one] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  exact div_div_div_cancel_right₀
    (ne_of_gt (Real.log_pos (by exact_mod_cast hn))) _ _

lemma global_harmonic_error {f : ℕ → ℝ} {c ε : ℝ}
    (h : Tendsto (fun n ↦ f n / Real.log n) atTop (𝓝 c)) (hε : 0 < ε) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n, |f n - c * (harmonic n : ℝ)| ≤
      ε * (harmonic n : ℝ) + D := by
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (harmonic_ratio h) ε hε
  let D := ∑ n ∈ Finset.range (max N 1), |f n - c * (harmonic n : ℝ)|
  have hD : 0 ≤ D := Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)
  refine ⟨D, hD, fun n ↦ ?_⟩
  by_cases hn : n < max N 1
  · have hle : |f n - c * (harmonic n : ℝ)| ≤ D :=
      Finset.single_le_sum (f := fun k ↦ |f k - c * (harmonic k : ℝ)|)
        (fun _ _ ↦ abs_nonneg _) (Finset.mem_range.mpr hn)
    exact hle.trans (le_add_of_nonneg_left (mul_nonneg hε.le (harmonic_nonneg n)))
  · have hnN : N ≤ n := by omega
    have hn0 : n ≠ 0 := by omega
    have hH : 0 < (harmonic n : ℝ) := by exact_mod_cast harmonic_pos hn0
    have he := hN n hnN
    rw [Real.dist_eq] at he
    have heq : |f n - c * (harmonic n : ℝ)| =
        |f n / (harmonic n : ℝ) - c| * (harmonic n : ℝ) := by
      rw [← abs_of_pos hH, ← abs_mul]
      congr 1
      rw [abs_of_pos hH]
      field_simp
    rw [heq]
    exact (mul_le_mul_of_nonneg_right he.le hH.le).trans (le_add_of_nonneg_right hD)

lemma series_error_bound {f : ℕ → ℝ} {c ε D r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hf : Summable (fun n ↦ f n * r ^ n))
    (hbound : ∀ n, |f n - c * (harmonic n : ℝ)| ≤ ε * (harmonic n : ℝ) + D) :
    |series f r - c * series (fun n ↦ (harmonic n : ℝ)) r| ≤
      ε * series (fun n ↦ (harmonic n : ℝ)) r + D / (1 - r) := by
  have hr : |r| < 1 := by rwa [abs_of_nonneg hr0]
  have hH := summable_harmonic hr
  have hG := summable_geometric_of_lt_one hr0 hr1
  have he := hf.sub (hH.mul_left c)
  have hb := (hH.mul_left ε).add (hG.mul_left D)
  have heq : series f r - c * series (fun n ↦ (harmonic n : ℝ)) r =
      ∑' n, (f n * r ^ n - c * ((harmonic n : ℝ) * r ^ n)) := by
    rw [hf.tsum_sub (hH.mul_left c), tsum_mul_left]
    rfl
  rw [heq]
  calc
    _ ≤ ∑' n, |f n * r ^ n - c * ((harmonic n : ℝ) * r ^ n)| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm he.norm
    _ ≤ ∑' n, (ε * ((harmonic n : ℝ) * r ^ n) + D * r ^ n) := by
      apply Summable.tsum_le_tsum _ he.abs hb
      intro n
      calc
        _ = |f n - c * (harmonic n : ℝ)| * r ^ n := by
          rw [← mul_assoc, ← sub_mul, abs_mul, abs_of_nonneg (pow_nonneg hr0 n)]
        _ ≤ (ε * (harmonic n : ℝ) + D) * r ^ n :=
          mul_le_mul_of_nonneg_right (hbound n) (pow_nonneg hr0 n)
        _ = _ := by ring
    _ = _ := by
      rw [(hH.mul_left ε).tsum_add (hG.mul_left D), tsum_mul_left, tsum_mul_left,
        (hasSum_geometric_of_lt_one hr0 hr1).tsum_eq]
      simp only [series, div_eq_mul_inv]

lemma negative_log_one_sub :
    Tendsto (fun r : ℝ ↦ -Real.log (1 - r)) (𝓝[<] 1) atTop := by
  have ht : Tendsto (fun r : ℝ ↦ 1 - r) (𝓝[<] 1) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · simpa using ((tendsto_id : Tendsto (fun r : ℝ ↦ r) (𝓝 1) (𝓝 1)).mono_left
        (show 𝓝[<] (1 : ℝ) ≤ 𝓝 1 from nhdsWithin_le_nhds)).const_sub (1 : ℝ)
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact sub_pos.mpr (show r < (1 : ℝ) from hr)
  exact tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp ht)

lemma normalized_series_error_bound {f : ℕ → ℝ} {c ε D r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1)
    (hf : Summable (fun n ↦ f n * r ^ n))
    (hbound : ∀ n, |f n - c * (harmonic n : ℝ)| ≤ ε * (harmonic n : ℝ) + D) :
    |series f r * (1 - r) / (-Real.log (1 - r)) - c| ≤
      ε + D / (-Real.log (1 - r)) := by
  have hL : 0 < -Real.log (1 - r) := neg_pos.mpr (Real.log_neg (by linarith) (by linarith))
  have hH := harmonic_series (show |r| < 1 by rwa [abs_of_pos hr0])
  have h1 : 1 - r ≠ 0 := ne_of_gt (sub_pos.mpr hr1)
  have hlog : Real.log (1 - r) ≠ 0 := neg_ne_zero.mp (ne_of_gt hL)
  have hH' : series (fun n ↦ (harmonic n : ℝ)) r = -Real.log (1 - r) / (1 - r) := by
    apply (eq_div_iff h1).mpr
    simpa only [mul_comm] using hH
  have hden : 0 ≤ (1 - r) / (-Real.log (1 - r)) := div_nonneg (by linarith) hL.le
  have hh := mul_le_mul_of_nonneg_right (series_error_bound hr0.le hr1 hf hbound) hden
  calc
    _ = |series f r - c * series (fun n ↦ (harmonic n : ℝ)) r| *
        ((1 - r) / (-Real.log (1 - r))) := by
      rw [← abs_of_nonneg hden, ← abs_mul]
      congr 1
      rw [hH']
      field_simp
      ring
    _ ≤ _ := hh
    _ = _ := by
      rw [hH']
      field_simp
      ring

/-- Abelian transfer for coefficients asymptotic to a multiple of `log n`. -/
lemma logarithmic_abelian_limit {f : ℕ → ℝ} {c : ℝ}
    (h : Tendsto (fun n ↦ f n / Real.log n) atTop (𝓝 c))
    (hs : ∀ r : ℝ, 0 < r → r < 1 → Summable (fun n ↦ f n * r ^ n)) :
    Tendsto (fun r : ℝ ↦ series f r * (1 - r) / (-Real.log (1 - r)))
      (𝓝[<] 1) (𝓝 c) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨D, hD, hbound⟩ := global_harmonic_error h (half_pos hε)
  have hd := negative_log_one_sub.const_div_atTop D
  have hev := Metric.tendsto_nhds.mp hd (ε / 2) (half_pos hε)
  have hrpos : ∀ᶠ r : ℝ in 𝓝[<] 1, 0 < r :=
    (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hev, hrpos, self_mem_nhdsWithin] with r hr hr0 hr1
  have hb := normalized_series_error_bound hr0 hr1 (hs r hr0 hr1) hbound
  rw [Real.dist_eq, sub_zero] at hr
  rw [Real.dist_eq]
  have he := le_abs_self (D / (-Real.log (1 - r)))
  linarith

lemma witness_generating_square_limit {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)) :
    Tendsto (fun r : ℝ ↦ series (indicator A) r ^ 2 * (1 - r) /
      (-Real.log (1 - r))) (𝓝[<] 1) (𝓝 c) := by
  have hh := logarithmic_abelian_limit h
    (fun r hr0 hr1 ↦ summable_sumRep A (by rwa [abs_of_pos hr0]))
  apply hh.congr'
  have hrpos : ∀ᶠ r : ℝ in 𝓝[<] 1, 0 < r :=
    (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hrpos, self_mem_nhdsWithin] with r hr0 hr1
  rw [generating_identity A (show |r| < 1 by rwa [abs_of_pos hr0])]

lemma series_indicator_nonneg (A : Set ℕ) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ series (indicator A) r :=
  tsum_nonneg (fun n ↦ mul_nonneg (indicator_nonneg A n) (pow_nonneg hr n))

lemma witness_generating_limit {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)) :
    Tendsto (fun r : ℝ ↦ series (indicator A) r *
      Real.sqrt ((1 - r) / (-Real.log (1 - r)))) (𝓝[<] 1) (𝓝 (Real.sqrt c)) := by
  apply (witness_generating_square_limit h).sqrt.congr'
  have hrpos : ∀ᶠ r : ℝ in 𝓝[<] 1, 0 < r :=
    (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hrpos] with r hr
  rw [mul_div_assoc, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (series_indicator_nonneg A hr.le)]

/-- The same Abelian profile, with the distance to the convergence boundary as parameter. -/
lemma witness_generating_limit_zero {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)) :
    Tendsto (fun t : ℝ ↦ series (indicator A) (1 - t) * Real.sqrt (t / (-Real.log t)))
      (𝓝[>] 0) (𝓝 (Real.sqrt c)) := by
  have ht : Tendsto (fun t : ℝ ↦ 1 - t) (𝓝[>] 0) (𝓝[<] 1) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · simpa using ((tendsto_id : Tendsto (fun t : ℝ ↦ t) (𝓝 0) (𝓝 0)).mono_left
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)).const_sub (1 : ℝ)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact sub_lt_self _ (show (0 : ℝ) < t from ht)
  simpa only [Function.comp_def, sub_sub_cancel] using (witness_generating_limit h).comp ht

lemma unit_interval_eventually : ∀ᶠ r : ℝ in 𝓝[<] 1, 0 < r ∧ r < 1 := by
  have hrpos : ∀ᶠ r : ℝ in 𝓝[<] 1, 0 < r :=
    (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hrpos, self_mem_nhdsWithin] with r hr0 hr1
  exact ⟨hr0, hr1⟩

lemma power_tendsto_one_left (k : ℕ) (hk : k ≠ 0) :
    Tendsto (fun r : ℝ ↦ r ^ k) (𝓝[<] 1) (𝓝[<] 1) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · simpa using ((tendsto_id : Tendsto (fun r : ℝ ↦ r) (𝓝 1) (𝓝 1)).pow k).mono_left
      (show 𝓝[<] (1 : ℝ) ≤ 𝓝 1 from nhdsWithin_le_nhds)
  · filter_upwards [unit_interval_eventually] with r hr
    exact pow_lt_one₀ hr.1.le hr.2 hk

lemma geometric_sum_limit (k : ℕ) :
    Tendsto (fun r : ℝ ↦ ∑ i ∈ Finset.range k, r ^ i) (𝓝[<] 1) (𝓝 (k : ℝ)) := by
  have hc : Continuous (fun r : ℝ ↦ ∑ i ∈ Finset.range k, r ^ i) := by fun_prop
  simpa using (hc.tendsto 1).mono_left (show 𝓝[<] (1 : ℝ) ≤ 𝓝 1 from nhdsWithin_le_nhds)

lemma power_log_ratio (k : ℕ) (hk : k ≠ 0) :
    Tendsto (fun r : ℝ ↦ (-Real.log (1 - r ^ k)) / (-Real.log (1 - r)))
      (𝓝[<] 1) (𝓝 1) := by
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hq := geometric_sum_limit k
  have hlogq := (Real.continuousAt_log (ne_of_gt hkpos)).tendsto.comp hq
  have hh := (hlogq.div_atTop negative_log_one_sub).const_sub 1
  simp only [sub_zero] at hh
  apply hh.congr'
  filter_upwards [unit_interval_eventually, hq.eventually (eventually_gt_nhds hkpos)] with r hr hqr
  have hL : Real.log (1 - r) ≠ 0 := ne_of_lt (Real.log_neg (by linarith [hr.2]) (by linarith [hr.1]))
  simp only [Function.comp_apply]
  rw [← geom_sum_mul_neg r k, Real.log_mul (ne_of_gt hqr) (ne_of_gt (sub_pos.mpr hr.2))]
  field_simp
  ring

noncomputable def kernel (r : ℝ) : ℝ := (1 - r) / (-Real.log (1 - r))

lemma kernel_pos {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) : 0 < kernel r := by
  apply div_pos (sub_pos.mpr hr1)
  exact neg_pos.mpr (Real.log_neg (by linarith) (by linarith))

lemma power_kernel_ratio (k : ℕ) (hk : k ≠ 0) :
    Tendsto (fun r : ℝ ↦ kernel (r ^ k) / kernel r) (𝓝[<] 1) (𝓝 (k : ℝ)) := by
  have hh := (geometric_sum_limit k).div (power_log_ratio k hk) (by norm_num : (1 : ℝ) ≠ 0)
  simp only [div_one] at hh
  apply hh.congr'
  filter_upwards [unit_interval_eventually] with r hr
  have hrk0 := pow_pos hr.1 k
  have hrk1 := pow_lt_one₀ hr.1.le hr.2 hk
  have h1 : 1 - r ≠ 0 := ne_of_gt (sub_pos.mpr hr.2)
  have hL : Real.log (1 - r) ≠ 0 := ne_of_lt (Real.log_neg (by linarith [hr.2]) (by linarith [hr.1]))
  have hLk : Real.log (1 - r ^ k) ≠ 0 := ne_of_lt (Real.log_neg (by linarith) (by linarith))
  dsimp only [Pi.div_apply, kernel]
  field_simp
  nlinarith [geom_sum_mul_neg r k]

/-- The geometric/Laplace moment ratios forced by a nonzero logarithmic coefficient. -/
lemma witness_generating_power_ratio {A : Set ℕ} {c : ℝ} (hc : c ≠ 0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c))
    (k : ℕ) (hk : k ≠ 0) :
    Tendsto (fun r : ℝ ↦ series (indicator A) (r ^ k) / series (indicator A) r)
      (𝓝[<] 1) (𝓝 (1 / Real.sqrt (k : ℝ))) := by
  have hcpos := Erdos66Explore.limit_pos hc h
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hN : Tendsto (fun r : ℝ ↦ series (indicator A) r * Real.sqrt (kernel r))
      (𝓝[<] 1) (𝓝 (Real.sqrt c)) := witness_generating_limit h
  have hNk := hN.comp (power_tendsto_one_left k hk)
  have hquot := hNk.div hN (Real.sqrt_ne_zero'.mpr hcpos)
  simp only [Function.comp_def, div_self (Real.sqrt_ne_zero'.mpr hcpos)] at hquot
  have hh := hquot.div (power_kernel_ratio k hk).sqrt (Real.sqrt_ne_zero'.mpr hkpos)
  apply hh.congr'
  filter_upwards [unit_interval_eventually] with r hr
  have hw : 0 < kernel r := kernel_pos hr.1 hr.2
  have hwk : 0 < kernel (r ^ k) := kernel_pos (pow_pos hr.1 k) (pow_lt_one₀ hr.1.le hr.2 hk)
  dsimp only [Pi.div_apply]
  rw [Real.sqrt_div hwk.le]
  by_cases hF : series (indicator A) r = 0
  · simp only [hF, zero_mul, div_zero, zero_div]
  · have hs := Real.sqrt_ne_zero'.mpr hw
    have hsk := Real.sqrt_ne_zero'.mpr hwk
    field_simp

end Erdos66Generating
