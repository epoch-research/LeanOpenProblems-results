import Submission.ExponentialWindow

/-! A bounded-sequence exponential Tauberian argument using finite binomial
windows. Exponential cancellation is a hypothesis, not an arithmetic result. -/
namespace Erdos371.ExponentialWindow
open Finset Filter
open scoped Topology

lemma exp_inverse_gap_bound {t : ℝ} (ht : 0 < t) :
    (1-Real.exp (-t))⁻¹ ≤ 1+t⁻¹ := by
  have he := Real.add_one_le_exp t
  have he1 : 1 < Real.exp t := Real.one_lt_exp_iff.mpr ht
  have hid : 1-(Real.exp t)⁻¹ = (Real.exp t-1)/Real.exp t := by
    field_simp
  rw [Real.exp_neg, hid, inv_div]
  apply (div_le_iff₀ (sub_pos.mpr he1)).mpr
  have ht0 : t ≠ 0 := ht.ne'
  have hh := mul_le_mul_of_nonneg_right he (inv_nonneg.mpr ht.le)
  rw [add_mul, mul_inv_cancel₀ ht0, one_mul] at hh
  nlinarith

noncomputable def endpointRatio (k N : ℕ) : ℝ := Real.exp (-Real.log k / N)

lemma endpointRatio_properties (k N : ℕ) (hk : 1 < k) (hN : 0 < N) :
    0 < endpointRatio k N ∧ endpointRatio k N < 1 ∧
      (k : ℝ)*(endpointRatio k N)^N = 1 := by
  have hkR : (1 : ℝ) < k := by exact_mod_cast hk
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hlog : 0 < Real.log k := Real.log_pos hkR
  refine ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (neg_neg_of_pos hlog)
    (by exact_mod_cast hN)), ?_⟩
  rw [endpointRatio, ← Real.exp_nat_mul]
  have he : (N : ℝ)*(-Real.log k/N) = -Real.log k := by field_simp
  rw [he, Real.exp_neg, Real.exp_log (by linarith : (0 : ℝ) < k)]
  exact mul_inv_cancel₀ (by positivity)

/-- With t=log(k)/N the normalized approximation error is at most
2/N+2/log(k), uniformly in the bounded sequence. -/
theorem prefix_exponential_window_error (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (k N : ℕ) (hk : 1 < k) (hN : 0 < N) :
    |((∑ n ∈ range N, f n) - ∑' n : ℕ, f n*window k (endpointRatio k N) n)/N| ≤
      2/N + 2/Real.log k := by
  obtain ⟨hr0,hr1,hkr⟩ := endpointRatio_properties k N hk hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog : 0 < Real.log k := Real.log_pos (by exact_mod_cast hk)
  have hgap : 0 < 1-endpointRatio k N := sub_pos.mpr hr1
  have hi := exp_inverse_gap_bound (div_pos hlog hNr)
  have hie : (1-endpointRatio k N)⁻¹ ≤ 1+(Real.log k/N)⁻¹ := by
    simpa only [endpointRatio, neg_div] using hi
  rw [abs_div, abs_of_pos hNr]
  apply (div_le_div_of_nonneg_right (prefix_window_error f hf k N hr0.le hr1 hkr) hNr.le).trans
  calc
    ((1+endpointRatio k N)/(1-endpointRatio k N))/(N : ℝ) ≤
        (2*(1-endpointRatio k N)⁻¹)/(N : ℝ) := by
      rw [div_eq_mul_inv (1+endpointRatio k N)]
      gcongr
      linarith
    _ ≤ (2*(1+(Real.log k/N)⁻¹))/(N : ℝ) := by gcongr
    _ = _ := by field_simp

lemma binomial_window (k : ℕ) (r : ℝ) (n : ℕ) :
    window k r n = -∑ j ∈ range k,
      ((-1 : ℝ)^(j+1)*(k.choose (j+1) : ℝ))*(r^(j+1))^n := by
  have he := add_pow (-(r^n)) (1 : ℝ) k
  rw [sum_range_succ'] at he
  simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one] at he
  have hterm (j : ℕ) : (-(r^n))^(j+1)*(k.choose (j+1) : ℝ) =
      ((-1 : ℝ)^(j+1)*(k.choose (j+1) : ℝ))*(r^(j+1))^n := by
    rw [neg_pow, ← pow_mul, ← pow_mul, Nat.mul_comm n (j+1)]
    ring
  simp only [hterm, neg_add_eq_sub] at he
  unfold window
  linarith

lemma summable_weighted_geometric (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) : Summable (fun n => f n*r^n) := by
  apply Summable.of_norm_bounded (summable_geometric_of_lt_one hr hr1)
  intro n
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hr n)]
  exact mul_le_of_le_one_left (pow_nonneg hr n) (hf n)

lemma window_tsum_expansion (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (k : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    (∑' n : ℕ, f n*window k r n) = -∑ j ∈ range k,
      ((-1 : ℝ)^(j+1)*(k.choose (j+1) : ℝ)) * ∑' n : ℕ, f n*(r^(j+1))^n := by
  have he (n : ℕ) : f n*window k r n =
      -∑ j ∈ range k, ((-1 : ℝ)^(j+1)*(k.choose (j+1) : ℝ)) * (f n*(r^(j+1))^n) := by
    rw [binomial_window, mul_neg, mul_sum]
    congr 1
    apply sum_congr rfl
    intro j _
    ring
  simp_rw [he]
  rw [tsum_neg, Summable.tsum_finsetSum]
  · simp_rw [tsum_mul_left]
  · intro j hj
    exact (summable_weighted_geometric f hf (pow_nonneg hr _)
      (pow_lt_one₀ hr hr1 (by omega : j+1 ≠ 0))).mul_left _

noncomputable def exponentialMean (f : ℕ → ℝ) (t : ℝ) : ℝ :=
  t * ∑' n : ℕ, f n * Real.exp (-t*n)

lemma scaled_exponential_mean_zero (f : ℕ → ℝ)
    (hA : Tendsto (exponentialMean f) (𝓝[>] 0) (𝓝 0)) (c : ℝ) (hc : 0 < c) :
    Tendsto (fun N : ℕ => (∑' n : ℕ, f n*Real.exp (-(c/N)*n))/N) atTop (𝓝 0) := by
  have ht : Tendsto (fun N : ℕ => c/(N : ℝ)) atTop (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨tendsto_const_div_atTop_nhds_zero_nat c, ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    exact div_pos hc (by exact_mod_cast hN)
  have hh := (hA.comp ht).div_const c
  simp only [zero_div] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  unfold exponentialMean
  dsimp only [Function.comp_apply]
  field_simp

lemma endpointRatio_powers (k N j n : ℕ) :
    ((endpointRatio k N)^(j+1))^n =
      Real.exp (-((Real.log k*(j+1))/N)*n) := by
  simp only [endpointRatio, ← Real.exp_nat_mul, Nat.cast_add, Nat.cast_one]
  congr 1
  ring

lemma window_mean_zero (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (hA : Tendsto (exponentialMean f) (𝓝[>] 0) (𝓝 0))
    (k : ℕ) (hk : 1 < k) :
    Tendsto (fun N : ℕ => (∑' n : ℕ, f n*window k (endpointRatio k N) n)/N)
      atTop (𝓝 0) := by
  have hlog : 0 < Real.log k := Real.log_pos (by exact_mod_cast hk)
  have hj (j : ℕ) : Tendsto (fun N : ℕ =>
      ((-1 : ℝ)^(j+1)*(k.choose (j+1) : ℝ)) *
        ((∑' n : ℕ, f n*Real.exp (-((Real.log k*(j+1))/N)*n))/N)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (scaled_exponential_mean_zero f hA (Real.log k*(j+1)) (by positivity)).const_mul
        ((-1 : ℝ)^(j+1)*(k.choose (j+1) : ℝ))
  have ht := (tendsto_finset_sum (range k) (fun j _ => hj j)).neg
  simp only [sum_const_zero, neg_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  obtain ⟨hr0,hr1,_⟩ := endpointRatio_properties k N hk hN
  rw [window_tsum_expansion f hf k hr0.le hr1, neg_div, sum_div]
  simp only [endpointRatio_powers, mul_div_assoc]

/-- Ordinary exponential Abel cancellation implies natural Cesàro
cancellation for every real sequence bounded in absolute value by one.
This theorem does NOT assert the exponential hypothesis for factorSign. -/
theorem cesaro_zero_of_exponential_zero (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (hA : Tendsto (exponentialMean f) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, f n)/N) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hlog : Tendsto (fun k : ℕ => Real.log (k : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun k : ℕ => 2/Real.log (k : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero.comp hlog).const_mul 2
  have he := hi.eventually_lt_const (by positivity : (0 : ℝ) < ε/3)
  obtain ⟨k,hk,hsmall⟩ := ((eventually_gt_atTop (1 : ℕ)).and he).exists
  have hw := window_mean_zero f hf hA k hk
  have hwε := (Metric.tendsto_nhds.mp hw) (ε/3) (by positivity)
  have hNε := (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).eventually_lt_const
    (by positivity : (0 : ℝ) < ε/3)
  filter_upwards [eventually_gt_atTop (0 : ℕ), hwε, hNε] with N hN hwN hNsmall
  rw [Real.dist_eq, sub_zero] at hwN ⊢
  have hb := prefix_exponential_window_error f hf k N hk hN
  have htri := abs_sub_le ((∑ n ∈ range N, f n)/N)
    ((∑' n : ℕ, f n*window k (endpointRatio k N) n)/N) 0
  simp only [sub_zero] at htri
  rw [← sub_div] at htri
  linarith

#print axioms cesaro_zero_of_exponential_zero
#print axioms prefix_exponential_window_error
end Erdos371.ExponentialWindow
