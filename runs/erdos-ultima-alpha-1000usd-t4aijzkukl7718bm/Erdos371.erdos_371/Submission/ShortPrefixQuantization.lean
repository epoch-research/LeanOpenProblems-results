import Submission.QuantizedComparisonApproximation
import Submission.StableLabelPrimeTransfer

/-! Quantization error at shorter natural endpoints with the original global
cutoff N. The quantization resolution is chosen independently of the bounded
set of multipliers. -/
namespace Erdos371
open Finset Filter FiniteSieve
open FiniteInformation

lemma logRatioEvent_global_to_short (Q T N n : ℕ) (hQ : 0 < Q) (hT : 1 < T)
    (hTN : T ≤ N) (hNT : N ≤ T^2) (hn : 0 < n)
    (hnear : logRatioEvent N (1/(Q : ℝ)) n) : logRatioEvent T (2/(Q : ℝ)) n := by
  have hN : 1 < N := hT.trans_le hTN
  have hlogT : 0 < Real.log (T : ℝ) := Real.log_pos (by exact_mod_cast hT)
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hlog : Real.log (N : ℝ) ≤ 2*Real.log T := by
    have h := Real.log_le_log (by exact_mod_cast (by omega : 0 < N))
      (show (N : ℝ) ≤ (T : ℝ)^2 by exact_mod_cast hNT)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hd := (logRatioEvent_iff_logDifference N n _ hN hn).mp hnear
  apply (logRatioEvent_iff_logDifference T n _ hT hn).mpr
  rw [logDifference, abs_div, abs_of_pos hlogN, div_le_iff₀ hlogN] at hd
  rw [logDifference, abs_div, abs_of_pos hlogT, div_le_iff₀ hlogT]
  have hm := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ 1/Q)
  exact hd.trans (hm.trans_eq (by ring))

lemma quantFactorSign_short_error_sum (Q T N : ℕ) (hQ : 0 < Q) (hT : 1 < T)
    (hTN : T ≤ N) (hNT : N ≤ T^2) :
    (∑ n ∈ range T, |factorSign n-quantFactorSign Q N n|) ≤
      2+2*((logRatioSet T (2/(Q : ℝ))).card : ℝ) := by
  classical
  have hterm (n : ℕ) (hnT : n ∈ range T) : |factorSign n-quantFactorSign Q N n| ≤
      (if n = 0 then (2 : ℝ) else 0) +
        (if logRatioEvent T (2/(Q : ℝ)) n then (2 : ℝ) else 0) := by
    by_cases hn : n = 0
    · rw [if_pos hn]
      exact (quantFactorSign_error_le_two Q N n).trans
        (le_add_of_nonneg_right (by split_ifs <;> norm_num))
    · rw [if_neg hn,zero_add]
      by_cases hnear : logRatioEvent T (2/(Q : ℝ)) n
      · rw [if_pos hnear]
        exact quantFactorSign_error_le_two Q N n
      · have hnearN : ¬logRatioEvent N (1/(Q : ℝ)) n := fun h =>
          hnear (logRatioEvent_global_to_short Q T N n hQ hT hTN hNT (by omega) h)
        rw [if_neg hnear, quantFactorSign_eq_of_not_near Q N n hQ (hT.trans_le hTN)
          (by omega) ((mem_range.mp hnT).trans_le hTN) hnearN, sub_self, abs_zero]
  have hs := sum_le_sum hterm
  simpa only [sum_add_distrib,sum_ite_eq',mem_range,show 0 < T by omega,if_true,
    sum_ite,sum_const_zero,add_zero,sum_const,nsmul_eq_mul,logRatioSet,mul_comm] using hs

/-- Uniformity in every global cutoff between T and T^2. -/
theorem quantFactorSign_global_cutoff_approximation (ε : ℝ) (hε : 0 < ε) :
    ∃ Q₀ > 0, ∀ᶠ T : ℕ in atTop, ∀ Q ≥ Q₀, ∀ N, T ≤ N → N ≤ T^2 →
      prefixMean T (fun n => |factorSign n-quantFactorSign Q N n|) ≤ ε := by
  obtain ⟨δ,hδ,hr⟩ := logRatioSet_uniform_rarity (ε/4) (by positivity)
  obtain ⟨Q₀,hQ₀⟩ := exists_nat_gt (max 1 (2/δ))
  have hQ₀pos : 0 < Q₀ := by
    have h : (1 : ℝ) < Q₀ := (le_max_left _ _).trans_lt hQ₀
    exact_mod_cast (show (0 : ℝ) < Q₀ by linarith)
  have hw : 2/(Q₀ : ℝ) ≤ δ := by
    have hq : 2/δ < (Q₀ : ℝ) := (le_max_right _ _).trans_lt hQ₀
    have hmul := (div_lt_iff₀ hδ).mp hq
    apply (div_le_iff₀ (by exact_mod_cast hQ₀pos : (0 : ℝ) < Q₀)).mpr
    nlinarith
  refine ⟨Q₀,hQ₀pos,?_⟩
  have ht := tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)
  filter_upwards [hr,ht.eventually_lt_const (by positivity : (0 : ℝ) < ε/2),
    eventually_gt_atTop (1 : ℕ)] with T hr ht hT
  intro Q hQ N hTN hNT
  have hwQ : 2/(Q : ℝ) ≤ δ := (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
    (by exact_mod_cast hQ₀pos) (by exact_mod_cast hQ)).trans hw
  have hcard : ((logRatioSet T (2/(Q : ℝ))).card : ℝ) ≤ (logRatioSet T δ).card :=
    Nat.cast_le.mpr (card_le_card (logRatioSet_mono_width T _ _ hT.le hwQ))
  have hcount := div_le_div_of_nonneg_right
    (quantFactorSign_short_error_sum Q T N (hQ₀pos.trans_le hQ) hT hTN hNT)
    (Nat.cast_nonneg (α := ℝ) T)
  have hcount' := div_le_div_of_nonneg_right hcard (Nat.cast_nonneg (α := ℝ) T)
  rw [add_div,mul_div_assoc] at hcount
  unfold prefixMean
  linarith

/-- The resolution Q0 does not depend on the multiplier bound B. Only the
threshold in the natural endpoint N depends on B. -/
theorem quantFactorSign_short_prefix_approximation (ε : ℝ) (hε : 0 < ε) :
    ∃ Q₀ > 0, ∀ B : ℕ, ∀ᶠ N : ℕ in atTop, ∀ Q ≥ Q₀, ∀ p, 0 < p → p ≤ B →
      prefixMean (N/p) (fun n => |factorSign n-quantFactorSign Q N n|) ≤ ε := by
  obtain ⟨Q₀,hQ₀,he⟩ := quantFactorSign_global_cutoff_approximation ε hε
  obtain ⟨T₀,hT₀⟩ := eventually_atTop.mp he
  refine ⟨Q₀,hQ₀,?_⟩
  intro B
  filter_upwards [eventually_ge_atTop (B*max T₀ (B+1))] with N hN
  intro Q hQ p hp hpB
  let T := N/p
  have hTbound : max T₀ (B+1) ≤ T := by
    apply (Nat.le_div_iff_mul_le hp).mpr
    calc
      max T₀ (B+1)*p ≤ max T₀ (B+1)*B := Nat.mul_le_mul_left _ hpB
      _ = B*max T₀ (B+1) := Nat.mul_comm _ _
      _ ≤ N := hN
  have hT₀le : T₀ ≤ T := (le_max_left _ _).trans hTbound
  have hBT : B+1 ≤ T := (le_max_right _ _).trans hTbound
  have hNT : N ≤ T^2 := by
    have hdec : N = p*T+N%p := (Nat.div_add_mod N p).symm
    have hmod : N%p < p := Nat.mod_lt N hp
    have hmul := Nat.mul_le_mul_left T hBT
    have hmul' := Nat.mul_le_mul_right T hpB
    nlinarith
  exact hT₀ T hT₀le Q hQ N (Nat.div_le_self _ _) hNT

#print axioms quantFactorSign_short_prefix_approximation
end Erdos371
