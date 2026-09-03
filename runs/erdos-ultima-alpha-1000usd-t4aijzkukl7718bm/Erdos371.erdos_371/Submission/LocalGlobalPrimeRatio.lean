import Submission.LocalPrimeQuantization
import Submission.FiniteEndpointTransfer

/-! Local versus global logarithmic normalization in natural mean. -/
namespace Erdos371
open Finset Filter FiniteInformation
open scoped Topology
set_option autoImplicit false

lemma normalizedPrimeLog_unit_on_prefix (N n : ℕ) (hn : n<N) :
    0 ≤ normalizedPrimeLog N n ∧ normalizedPrimeLog N n ≤ 1 := by
  by_cases hN : 1 < N
  · exact normalizedPrimeLog_mem_unit N n hN hn.le
  · have hn0 : n=0 := by omega
    subst n
    simp [normalizedPrimeLog]

lemma local_global_prime_ratio_error_le_one (N n : ℕ) (hn : n<N) :
    |normalizedPrimeLog N n-localPrimeRatio n| ≤ 1 := by
  have hx := normalizedPrimeLog_unit_on_prefix N n hn
  have hy := localPrimeRatio_mem_unit n
  rw [abs_le]
  constructor <;> linarith

lemma local_global_prime_ratio_error (K N n : ℕ) (hK : 0<K) (hN : 1<N)
    (hn : n<N) (hscale : N ≤ K*n) :
    |normalizedPrimeLog N n-localPrimeRatio n| ≤ Real.log K/Real.log N := by
  have hKN : 0 ≤ Real.log (K : ℝ)/Real.log N :=
    div_nonneg (Real.log_natCast_nonneg K) (Real.log_natCast_nonneg N)
  by_cases hn1 : 1 < n
  · have hln : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn1)
    have hlN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
    have hnR : (0 : ℝ)<n := by exact_mod_cast (Nat.zero_lt_of_lt hn1)
    have hlog : Real.log (n : ℝ) ≤ Real.log N :=
      Real.log_le_log hnR (by exact_mod_cast hn.le)
    have hx := localPrimeRatio_mem_unit n
    have hnum := primeLog_nonneg n
    have hcomp : normalizedPrimeLog N n ≤ localPrimeRatio n :=
      div_le_div_of_nonneg_left hnum hln hlog
    have hgap : Real.log N-Real.log n ≤ Real.log K := by
      have hh := Real.log_le_log (by exact_mod_cast (Nat.zero_lt_of_lt hN))
        (show (N : ℝ) ≤ (K : ℝ)*n by exact_mod_cast hscale)
      rw [Real.log_mul (by exact_mod_cast hK.ne') hnR.ne'] at hh
      linarith
    rw [abs_of_nonpos (sub_nonpos.mpr hcomp)]
    have he : -(normalizedPrimeLog N n-localPrimeRatio n) =
        localPrimeRatio n*((Real.log N-Real.log n)/Real.log N) := by
      dsimp [normalizedPrimeLog,localPrimeRatio]
      field_simp
      <;> ring
    rw [he]
    calc
      _ ≤ 1*((Real.log N-Real.log n)/Real.log N) :=
        mul_le_mul_of_nonneg_right hx.2 (div_nonneg (sub_nonneg.mpr hlog) hlN.le)
      _ ≤ _ := by simpa only [one_mul] using div_le_div_of_nonneg_right hgap hlN.le
  · have hnle : n ≤ 1 := by omega
    interval_cases n <;> simpa [normalizedPrimeLog,localPrimeRatio,primeLog] using hKN

/-- An explicit averaging bound. The initial segment N/k costs at most 1/k;
the remaining inputs cost at most log(2k)/log N. -/
lemma local_global_prime_ratio_mean_bound (k N : ℕ) (hk : 0 < k) (hN : 2*k ≤ N) :
    prefixMean N (fun n => |normalizedPrimeLog N n-localPrimeRatio n|) ≤
      1/(k : ℝ)+Real.log (2*k : ℕ)/Real.log N := by
  have hN1 : 1 < N := by omega
  have hNr : (0 : ℝ)<N := by exact_mod_cast (by omega : 0<N)
  let T := N/k
  have hT : 1 ≤ T := Nat.le_div_iff_mul_le hk |>.mpr (by omega)
  have hdec := Nat.div_add_mod N k
  have hrem := Nat.mod_lt N hk
  have hscale : N ≤ 2*k*T := by dsimp [T] at *; nlinarith
  let B : ℝ := Real.log (2*k : ℕ)/Real.log N
  have hB : 0 ≤ B := div_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
  have he (n : ℕ) (hn : n<N) : |normalizedPrimeLog N n-localPrimeRatio n| ≤
      (if n<T then (1 : ℝ) else 0)+B := by
    by_cases hnT : n<T
    · rw [if_pos hnT]
      exact (local_global_prime_ratio_error_le_one N n hn).trans (le_add_of_nonneg_right hB)
    · rw [if_neg hnT,zero_add]
      exact local_global_prime_ratio_error (2*k) N n (by omega) hN1 hn
        (hscale.trans (Nat.mul_le_mul_left _ (not_lt.mp hnT)))
  have hs := sum_le_sum (s := range N) (fun n hn => he n (mem_range.mp hn))
  rw [sum_add_distrib,sum_const,card_range,nsmul_eq_mul] at hs
  have ht : (∑ n ∈ range N, if n<T then (1 : ℝ) else 0) ≤ T := by
    simp only [sum_boole]
    have hh := card_le_card (show (range N).filter (fun n => n<T) ⊆ range T from
      fun n hn => mem_range.mpr (mem_filter.mp hn).2)
    rw [card_range] at hh
    exact_mod_cast hh
  have hTdiv : (T : ℝ)/(N : ℝ) ≤ 1/(k : ℝ) := by
    apply (div_le_div_iff₀ hNr (by exact_mod_cast hk)).mpr
    have hh := Nat.mul_div_le N k
    change k*T ≤ N at hh
    exact_mod_cast (by simpa only [one_mul,mul_one,mul_comm] using hh)
  have hd := div_le_div_of_nonneg_right hs hNr.le
  rw [add_div,mul_div_cancel_left₀ _ hNr.ne'] at hd
  have ht' := div_le_div_of_nonneg_right ht hNr.le
  exact hd.trans (by linarith)

/-- The moving global normalization and the fixed local normalization agree
in natural L1 mean. No joint prime-factor independence is used. -/
theorem local_global_prime_ratio_mean_zero :
    Tendsto (fun N : ℕ => prefixMean N (fun n => |normalizedPrimeLog N n-localPrimeRatio n|))
      atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨k,hk⟩ := exists_nat_gt (max 1 (4/ε))
  have hk0 : 0 < k := by
    have := (le_max_left _ _).trans_lt hk
    exact_mod_cast (show (0 : ℝ)<k by linarith)
  have hsmall : 1/(k : ℝ)<ε/4 := by
    have hh := (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hk)
    apply (div_lt_iff₀ (by exact_mod_cast hk0)).mpr
    nlinarith
  have ht : Tendsto (fun N : ℕ => Real.log (2*k : ℕ)/Real.log N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [eventually_ge_atTop (2*k),ht.eventually_lt_const (by positivity : (0 : ℝ)<ε/2)]
    with N hN ht
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (by unfold prefixMean; positivity)]
  exact (local_global_prime_ratio_mean_bound k N hk0 hN).trans_lt (by linarith)

#print axioms local_global_prime_ratio_mean_zero
end Erdos371
