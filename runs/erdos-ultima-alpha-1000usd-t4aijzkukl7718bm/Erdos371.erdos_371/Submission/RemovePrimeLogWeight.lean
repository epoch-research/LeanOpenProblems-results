import Submission.NaturalResiduePrimeDensity

/-! An elementary logarithmic-weight removal lemma for bounded nonnegative
coefficients. A fixed power cutoff is used before taking the limit; no
moving-parameter interchange is made. -/
namespace Erdos371.AbelPrimes
open Finset Filter
open scoped Topology
set_option autoImplicit false

noncomputable def logWeightedSum (b : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, b n*Real.log n

noncomputable def plainSum (b : ℕ → ℝ) (N : ℕ) : ℝ := ∑ n ∈ Icc 1 N, b n

lemma logWeightedSum_nonneg (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n) (N : ℕ) :
    0 ≤ logWeightedSum b N := by
  apply sum_nonneg
  intro n hn
  exact mul_nonneg (hb n) (Real.log_nonneg (by exact_mod_cast (mem_Icc.mp hn).1))

lemma logWeightedSum_le_plain (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n) (N : ℕ) :
    logWeightedSum b N ≤ plainSum b N*Real.log N := by
  rw [plainSum,sum_mul]
  apply sum_le_sum
  intro n hn
  obtain ⟨hn,hN⟩ := mem_Icc.mp hn
  exact mul_le_mul_of_nonneg_left
    (Real.log_le_log (by exact_mod_cast hn : (0 : ℝ) < n) (by exact_mod_cast hN)) (hb n)

lemma plain_log_sum_power_bound (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n ∧ b n ≤ 1)
    (N : ℕ) (hN : 2 ≤ N) (t : ℝ) (ht : 0 < t) :
    plainSum b N*Real.log N ≤ logWeightedSum b N/t+(N : ℝ)^t*Real.log N := by
  let V := Icc 1 ⌊(N : ℝ)^t⌋₊
  have hNp : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hN)
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hpow : 0 < (N : ℝ)^t := Real.rpow_pos_of_pos hNp t
  have hpoint (n : ℕ) (hn : n ∈ Icc 1 N) :
      b n*Real.log N ≤ b n*Real.log n/t+(if n ∈ V then Real.log N else 0) := by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hln : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (mem_Icc.mp hn).1)
    by_cases hv : n ∈ V
    · rw [if_pos hv]
      have hb1 := mul_le_mul_of_nonneg_right (hb n).2 hlog
      have hb0 : 0 ≤ b n*Real.log n/t := by positivity [ (hb n).1 ]
      linarith
    · rw [if_neg hv,add_zero]
      have hnlt : (N : ℝ)^t < n := by
        have hnf : ¬n ≤ ⌊(N : ℝ)^t⌋₊ := by
          intro h
          exact hv (mem_Icc.mpr ⟨(mem_Icc.mp hn).1,h⟩)
        exact lt_of_not_ge (fun h => hnf ((Nat.le_floor_iff hpow.le).mpr h))
      have hl := Real.log_le_log hpow hnlt.le
      rw [Real.log_rpow hNp t] at hl
      apply (le_div_iff₀ ht).mpr
      nlinarith [mul_le_mul_of_nonneg_left hl (hb n).1]
  have hsmall : (∑ n ∈ Icc 1 N, if n ∈ V then Real.log N else 0) ≤ (N : ℝ)^t*Real.log N := by
    rw [sum_ite_mem]
    calc
      _ ≤ ∑ _n ∈ V, Real.log N := sum_le_sum_of_subset_of_nonneg inter_subset_right (fun _ _ _ => hlog)
      _ = (⌊(N : ℝ)^t⌋₊ : ℝ)*Real.log N := by simp [V]
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.floor_le hpow.le) hlog
  have hs := sum_le_sum hpoint
  simp only [← sum_mul,sum_add_distrib,← sum_div] at hs
  exact hs.trans (add_le_add le_rfl hsmall)

lemma power_log_error_zero (t : ℝ) (ht : t < 1) :
    Tendsto (fun N : ℕ => (N : ℝ)^t*Real.log N/(N : ℝ)) atTop (𝓝 0) := by
  have hl := (isLittleO_log_rpow_atTop (by linarith : 0 < 1-t)).tendsto_div_nhds_zero
  have hn := hl.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  apply hn.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hp : (N : ℝ)^t*(N : ℝ)^(1-t) = N := by
    rw [← Real.rpow_add hNp]
    simp
  have hp0 := (Real.rpow_pos_of_pos hNp (1-t)).ne'
  change Real.log (N : ℝ)/(N : ℝ)^(1-t) = (N : ℝ)^t*Real.log N/(N : ℝ)
  field_simp
  nlinarith [congrArg (fun x : ℝ => x*Real.log (N : ℝ)) hp]

/-- If the log-weighted summatory function has a linear asymptotic, then the
unweighted sum has the corresponding `N/log N` asymptotic. -/
theorem remove_log_weight (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n ∧ b n ≤ 1) (A : ℝ)
    (hlim : Tendsto (fun N : ℕ => logWeightedSum b N/(N : ℝ)) atTop (𝓝 A)) :
    Tendsto (fun N : ℕ => plainSum b N*Real.log N/(N : ℝ)) atTop (𝓝 A) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let C := |A|+1
  have hC : 0 < C := by dsimp [C]; positivity
  let t := C/(C+ε/4)
  have ht : 0 < t := by dsimp [t]; positivity
  have ht1 : t < 1 := (div_lt_one (by positivity : (0 : ℝ) < C+ε/4)).mpr (by linarith)
  have he : (1/t-1)*C = ε/4 := by dsimp [t]; field_simp; ring
  have hpos : 0 ≤ 1/t-1 := by have := one_lt_one_div ht ht1; linarith
  have hbound : ∀ᶠ N : ℕ in atTop, logWeightedSum b N/(N : ℝ) ≤ C := by
    filter_upwards [(Metric.tendsto_nhds.mp hlim) 1 (by norm_num)] with N h
    rw [Real.dist_eq] at h
    have hu := (abs_lt.mp h).2
    dsimp [C]
    linarith [le_abs_self A]
  filter_upwards [hbound,(Metric.tendsto_nhds.mp hlim) (ε/4) (by positivity),
    (Metric.tendsto_nhds.mp (power_log_error_zero t ht1)) (ε/4) (by positivity),
    eventually_ge_atTop (2 : ℕ)] with N hbound hclose herr hN
  rw [Real.dist_eq] at hclose ⊢
  rw [Real.dist_eq,sub_zero] at herr
  have hlo := div_le_div_of_nonneg_right (logWeightedSum_le_plain b (fun n => (hb n).1) N) (Nat.cast_nonneg N)
  have hup := div_le_div_of_nonneg_right (plain_log_sum_power_bound b hb N hN t ht) (Nat.cast_nonneg N)
  rw [add_div] at hup
  have hx := mul_le_mul_of_nonneg_left hbound hpos
  rw [he] at hx
  have htcast : logWeightedSum b N/t/(N : ℝ) =
      logWeightedSum b N/(N : ℝ)+(1/t-1)*(logWeightedSum b N/(N : ℝ)) := by ring
  rw [htcast] at hup
  rw [abs_lt] at hclose herr ⊢
  constructor <;> linarith

#print axioms remove_log_weight
end Erdos371.AbelPrimes
