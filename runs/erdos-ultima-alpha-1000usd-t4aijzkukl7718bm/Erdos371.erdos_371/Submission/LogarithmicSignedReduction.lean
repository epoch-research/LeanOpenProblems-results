import Submission.LogNearTieRarity
import Submission.SmoothedComparison

/-! A continuous signed reduction using normalized logarithms. Dilation gives
uniform control on divisible progressions, not unrestricted gap invariance.
The continuous signed cancellation hypothesis at the end is not proved here. -/

namespace Erdos371
open Finset Filter
open FiniteSieve

noncomputable def primeLog (n : ℕ) : ℝ := Real.log (Nat.maxPrimeFac n)
noncomputable def normalizedPrimeLog (N n : ℕ) : ℝ := primeLog n / Real.log N
noncomputable def logDifference (N n : ℕ) : ℝ :=
  (primeLog (n+1)-primeLog n)/Real.log N

lemma maxPrimeFac_pos_of_pos (n : ℕ) (hn : 0 < n) : 0 < Nat.maxPrimeFac n := by
  by_cases h : n = 1
  · subst n; simp
  · exact (Nat.prime_maxPrimeFac_of_one_lt n (by omega)).pos

lemma primeLog_nonneg (n : ℕ) : 0 ≤ primeLog n := Real.log_natCast_nonneg _

@[simp] lemma primeLog_zero : primeLog 0 = 0 := by simp [primeLog]

lemma primeLog_le_log (n : ℕ) : primeLog n ≤ Real.log n := by
  by_cases hn : n = 0
  · subst n; simp
  · exact Real.log_le_log (by exact_mod_cast maxPrimeFac_pos_of_pos n (by omega))
      (by exact_mod_cast (Nat.maxPrimeFac_le (n := n)))

lemma primeLog_mul (k n : ℕ) (hk : 0 < k) (hn : 0 < n) :
    primeLog (k*n) = max (primeLog k) (primeLog n) := by
  have hp : (0 : ℝ) < Nat.maxPrimeFac k := by exact_mod_cast maxPrimeFac_pos_of_pos k hk
  have hq : (0 : ℝ) < Nat.maxPrimeFac n := by exact_mod_cast maxPrimeFac_pos_of_pos n hn
  unfold primeLog
  rw [Nat.maxPrimeFac_mul hk.ne' hn.ne']
  rcases le_total (Nat.maxPrimeFac k) (Nat.maxPrimeFac n) with h | h
  · rw [max_eq_right h,max_eq_right (Real.log_le_log hp (by exact_mod_cast h))]
  · rw [max_eq_left h,max_eq_left (Real.log_le_log hq (by exact_mod_cast h))]

lemma primeLog_mul_change (k n : ℕ) (hk : 0 < k) :
    0 ≤ primeLog (k*n)-primeLog n ∧ primeLog (k*n)-primeLog n ≤ Real.log k := by
  by_cases hn : n = 0
  · subst n; simp [Real.log_natCast_nonneg]
  · rw [primeLog_mul k n hk (by omega)]
    have hkn := primeLog_le_log k
    have hn0 := primeLog_nonneg n
    have hk0 := Real.log_natCast_nonneg k
    constructor
    · exact sub_nonneg.mpr (le_max_right _ _)
    · rcases le_total (primeLog k) (primeLog n) with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith

/-- Uniform dilation control. The left side samples a gap of size `k` only
at starting points divisible by `k`. It is not a full gap-`k` average. -/
lemma normalized_log_gap_dilation_bound (N k n : ℕ) (hN : 1 < N) (hk : 0 < k) :
    |(normalizedPrimeLog N (k*(n+1))-normalizedPrimeLog N (k*n))-logDifference N n| ≤
      Real.log k / Real.log N := by
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  obtain ⟨h0,h1⟩ := primeLog_mul_change k n hk
  obtain ⟨h2,h3⟩ := primeLog_mul_change k (n+1) hk
  unfold normalizedPrimeLog logDifference
  rw [← sub_div,← sub_div,abs_div,abs_of_pos hlog]
  apply div_le_div_of_nonneg_right _ hlog.le
  rw [abs_le]
  constructor <;> linarith

lemma logDifference_eq_sub (N n : ℕ) :
    logDifference N n = normalizedPrimeLog N (n+1)-normalizedPrimeLog N n := by
  simp only [logDifference,normalizedPrimeLog,sub_div]

lemma normalizedPrimeLog_mem_unit (N n : ℕ) (hN : 1 < N) (hn : n ≤ N) :
    0 ≤ normalizedPrimeLog N n ∧ normalizedPrimeLog N n ≤ 1 := by
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  constructor
  · exact div_nonneg (primeLog_nonneg n) hlog.le
  · apply (div_le_one hlog).mpr
    by_cases hn0 : n = 0
    · subst n; simpa using hlog.le
    · exact (primeLog_le_log n).trans (Real.log_le_log (by exact_mod_cast (show 0 < n by omega))
        (by exact_mod_cast hn))

lemma logDifference_sum (N : ℕ) :
    ∑ n ∈ range N, logDifference N n = normalizedPrimeLog N N := by
  simp_rw [logDifference_eq_sub]
  rw [sum_range_sub]
  simp [normalizedPrimeLog]

/-- The first signed logarithmic moment vanishes by telescoping. This does
not imply cancellation for nonlinear odd functions of the difference. -/
theorem logDifference_first_moment_tendsto_zero :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, logDifference N n)/N) atTop (nhds 0) := by
  simp_rw [logDifference_sum]
  apply squeeze_zero' _ _ (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  · filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
    exact div_nonneg (normalizedPrimeLog_mem_unit N N hN le_rfl).1 (Nat.cast_nonneg N)
  · filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
    exact div_le_div_of_nonneg_right (normalizedPrimeLog_mem_unit N N hN le_rfl).2 (Nat.cast_nonneg N)

lemma logRatioEvent_iff_logDifference (N n : ℕ) (δ : ℝ) (hN : 1 < N) (hn : 0 < n) :
    logRatioEvent N δ n ↔ |logDifference N n| ≤ δ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hp : (0 : ℝ) < Nat.maxPrimeFac n := by exact_mod_cast maxPrimeFac_pos_of_pos n hn
  have hq : (0 : ℝ) < Nat.maxPrimeFac (n+1) := by exact_mod_cast maxPrimeFac_pos_of_pos (n+1) (by omega)
  have hr := Real.rpow_pos_of_pos hN0 δ
  have he1 := Real.log_mul hr.ne' hq.ne'
  have he2 := Real.log_mul hr.ne' hp.ne'
  rw [Real.log_rpow hN0] at he1 he2
  unfold logRatioEvent logDifference primeLog
  rw [abs_le,le_div_iff₀ hlog,div_le_iff₀ hlog]
  constructor
  · rintro ⟨h1,h2⟩
    have hl1 := Real.log_le_log hp h1
    have hl2 := Real.log_le_log hq h2
    rw [he1] at hl1
    rw [he2] at hl2
    constructor <;> linarith
  · rintro ⟨h1,h2⟩
    constructor
    · apply (Real.log_le_log_iff hp (mul_pos hr hq)).mp
      rw [he1]
      linarith
    · apply (Real.log_le_log_iff hq (mul_pos hr hp)).mp
      rw [he2]
      linarith

lemma logDifference_pos_iff (N n : ℕ) (hN : 1 < N) (hn : 0 < n) :
    0 < logDifference N n ↔ Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1) := by
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hp : (0 : ℝ) < Nat.maxPrimeFac n := by exact_mod_cast maxPrimeFac_pos_of_pos n hn
  have hq : (0 : ℝ) < Nat.maxPrimeFac (n+1) := by exact_mod_cast maxPrimeFac_pos_of_pos (n+1) (by omega)
  unfold logDifference primeLog
  rw [lt_div_iff₀ hlog,zero_mul,sub_pos,Real.log_lt_log_iff hp hq]
  exact_mod_cast Iff.rfl

noncomputable def clippedOdd (δ x : ℝ) : ℝ := x / max δ |x|
noncomputable def clippedLogSign (δ : ℝ) (N n : ℕ) : ℝ := clippedOdd δ (logDifference N n)

lemma continuous_clippedOdd (δ : ℝ) (hδ : 0 < δ) : Continuous (clippedOdd δ) := by
  apply continuous_id.div (continuous_const.max continuous_abs)
  intro x
  exact (hδ.trans_le (le_max_left _ _)).ne'

lemma clippedOdd_neg (δ x : ℝ) : clippedOdd δ (-x) = -clippedOdd δ x := by
  simp only [clippedOdd,abs_neg,neg_div]

lemma abs_clippedOdd_le_one (δ x : ℝ) (hδ : 0 < δ) : |clippedOdd δ x| ≤ 1 := by
  unfold clippedOdd
  rw [abs_div,abs_of_pos (hδ.trans_le (le_max_left _ _))]
  exact (div_le_one (hδ.trans_le (le_max_left _ _))).mpr (le_max_right _ _)

lemma clippedOdd_eq_one (δ x : ℝ) (hδ : 0 < δ) (hx : δ ≤ x) : clippedOdd δ x = 1 := by
  have hx0 := hδ.trans_le hx
  simp [clippedOdd,abs_of_pos hx0,max_eq_right hx,hx0.ne']

lemma clippedOdd_eq_neg_one (δ x : ℝ) (hδ : 0 < δ) (hx : x ≤ -δ) : clippedOdd δ x = -1 := by
  have h := clippedOdd_eq_one δ (-x) hδ (by linarith)
  rw [clippedOdd_neg] at h
  linarith

lemma clippedLogSign_error_le_two (δ : ℝ) (hδ : 0 < δ) (N n : ℕ) :
    |factorSign n-clippedLogSign δ N n| ≤ 2 := by
  have h := abs_clippedOdd_le_one δ (logDifference N n) hδ
  have hs : |factorSign n| = 1 := by unfold factorSign predicateSign; split_ifs <;> norm_num
  have hb := abs_sub (factorSign n) (clippedLogSign δ N n)
  change |clippedLogSign δ N n| ≤ 1 at h
  linarith

lemma clippedLogSign_eq_of_not_near (δ : ℝ) (hδ : 0 < δ) (N n : ℕ)
    (hN : 1 < N) (hn : 0 < n) (hnear : ¬ logRatioEvent N δ n) :
    clippedLogSign δ N n = factorSign n := by
  have hd : δ < |logDifference N n| := lt_of_not_ge (fun h => hnear ((logRatioEvent_iff_logDifference N n δ hN hn).mpr h))
  unfold factorSign predicateSign clippedLogSign
  by_cases hp : Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1)
  · rw [if_pos hp]
    have hdpos := (logDifference_pos_iff N n hN hn).mpr hp
    rw [abs_of_pos hdpos] at hd
    exact clippedOdd_eq_one δ _ hδ hd.le
  · rw [if_neg hp]
    have hdneg : logDifference N n ≤ 0 := not_lt.mp (fun h => hp ((logDifference_pos_iff N n hN hn).mp h))
    rw [abs_of_nonpos hdneg] at hd
    exact clippedOdd_eq_neg_one δ _ hδ (by linarith)

lemma clippedLogSign_error_sum_bound (δ : ℝ) (hδ : 0 < δ) (N : ℕ) (hN : 1 < N) :
    (∑ n ∈ range N, |factorSign n-clippedLogSign δ N n|) ≤
      2+2*((logRatioSet N δ).card : ℝ) := by
  classical
  have hterm (n : ℕ) : |factorSign n-clippedLogSign δ N n| ≤
      (if n = 0 then (2 : ℝ) else 0)+(if logRatioEvent N δ n then (2 : ℝ) else 0) := by
    by_cases hn : n = 0
    · rw [if_pos hn]
      exact (clippedLogSign_error_le_two δ hδ N n).trans (le_add_of_nonneg_right (by split_ifs <;> norm_num))
    · rw [if_neg hn,zero_add]
      by_cases hnear : logRatioEvent N δ n
      · rw [if_pos hnear]; exact clippedLogSign_error_le_two δ hδ N n
      · rw [if_neg hnear,clippedLogSign_eq_of_not_near δ hδ N n hN (by omega) hnear,sub_self,abs_zero]
  have hs := sum_le_sum (s := range N) (fun n _ => hterm n)
  simpa only [sum_add_distrib,sum_ite_eq',mem_range,show 0 < N by omega,if_true,
    sum_ite,sum_const_zero,add_zero,sum_const,nsmul_eq_mul,logRatioSet,mul_comm] using hs

/-- The comparison sign is approximable in mean by continuous odd functions
of the normalized logarithmic difference. -/
theorem clippedLogSign_uniform_approximation (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ range N, |factorSign n-clippedLogSign δ N n|)/N ≤ ε := by
  obtain ⟨δ,hδ,hr⟩ := logRatioSet_uniform_rarity (ε/4) (by positivity)
  refine ⟨δ,hδ,?_⟩
  have ht := tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)
  filter_upwards [hr,ht.eventually_lt_const (by positivity : (0 : ℝ) < ε/2),
    eventually_gt_atTop (1 : ℕ)] with N hr ht hN
  have hb := div_le_div_of_nonneg_right (clippedLogSign_error_sum_bound δ hδ N hN) (Nat.cast_nonneg (α := ℝ) N)
  rw [add_div,mul_div_assoc] at hb
  linarith

/-- A sufficient continuous signed cancellation criterion. The hypothesis
for the largest-prime-factor process remains an arithmetic problem. -/
theorem continuous_odd_logDifference_cancellation_implies_density
    (hcancel : ∀ f : ℝ → ℝ, Continuous f → (∀ x, f (-x) = -f x) →
      Tendsto (fun N : ℕ => (∑ n ∈ range N, f (logDifference N n))/N) atTop (nhds 0)) :
    {n | Nat.maxPrimeFac (n+1) > Nat.maxPrimeFac n}.HasDensity (1/2) := by
  rw [density_iff_signed_count]
  simp_rw [← factorSign_sum_eq_count_difference]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ,hδ,ha⟩ := clippedLogSign_uniform_approximation (ε/2) (by positivity)
  have hc := hcancel (clippedOdd δ) (continuous_clippedOdd δ hδ) (clippedOdd_neg δ)
  have he := (Metric.tendsto_nhds.mp hc) (ε/2) (by positivity)
  filter_upwards [ha,he] with N ha he
  rw [Real.dist_eq,sub_zero] at he ⊢
  have hdiff : |(∑ n ∈ range N, factorSign n)/N-(∑ n ∈ range N, clippedLogSign δ N n)/N| ≤
      (∑ n ∈ range N, |factorSign n-clippedLogSign δ N n|)/N := by
    rw [← sub_div,← sum_sub_distrib,abs_div,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) N)]
    exact div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) (Nat.cast_nonneg N)
  have ht := abs_sub ( (∑ n ∈ range N, factorSign n)/N-(∑ n ∈ range N, clippedLogSign δ N n)/N)
    (-((∑ n ∈ range N, clippedLogSign δ N n)/N))
  simp only [sub_neg_eq_add,sub_add_cancel,abs_neg] at ht
  change |(∑ n ∈ range N, clippedLogSign δ N n)/N| < ε/2 at he
  linarith

#print axioms normalized_log_gap_dilation_bound
#print axioms logDifference_first_moment_tendsto_zero
#print axioms continuous_odd_logDifference_cancellation_implies_density
end Erdos371
