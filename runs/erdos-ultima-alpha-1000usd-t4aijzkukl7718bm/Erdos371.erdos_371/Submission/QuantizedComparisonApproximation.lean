import Submission.PrimeLogQuantization
import Submission.ClippedLogCriterion

/-! The actual comparison sign is approximable by skew comparisons of finitely
many multiplier-stable labels. Quantization ties are controlled by the proved
near-tie rarity, not assumed to have negligible density. -/
namespace Erdos371
open Finset Filter FiniteSieve

noncomputable def orderSkew {A : Type*} [LinearOrder A] (a b : A) : ℝ :=
  if a < b then 1 else if b < a then -1 else 0

lemma orderSkew_abs_le {A : Type*} [LinearOrder A] (a b : A) : |orderSkew a b| ≤ 1 := by
  unfold orderSkew
  split_ifs <;> norm_num

lemma orderSkew_swap {A : Type*} [LinearOrder A] (a b : A) : orderSkew b a = -orderSkew a b := by
  rcases lt_trichotomy a b with h | h | h
  · simp [orderSkew,h,h.not_gt]
  · simp [orderSkew,h]
  · simp [orderSkew,h,h.not_gt]

noncomputable def quantFactorSign (Q N n : ℕ) : ℝ :=
  orderSkew (primeQuantLabel Q N n) (primeQuantLabel Q N (n+1))

lemma quantFactorSign_error_le_two (Q N n : ℕ) : |factorSign n-quantFactorSign Q N n| ≤ 2 := by
  have hs : |factorSign n| = 1 := by unfold factorSign predicateSign; split_ifs <;> norm_num
  have hq := orderSkew_abs_le (primeQuantLabel Q N n) (primeQuantLabel Q N (n+1))
  have ht := abs_sub (factorSign n) (quantFactorSign Q N n)
  change |quantFactorSign Q N n| ≤ 1 at hq
  linarith

lemma quantFactorSign_eq_of_not_near (Q N n : ℕ) (hQ : 0 < Q) (hN : 1 < N)
    (hn : 0 < n) (hnN : n < N) (hnear : ¬logRatioEvent N (1/(Q : ℝ)) n) :
    quantFactorSign Q N n = factorSign n := by
  have hd : 1/(Q : ℝ) < |logDifference N n| := lt_of_not_ge
    (fun h => hnear ((logRatioEvent_iff_logDifference N n _ hN hn).mpr h))
  have hx := normalizedPrimeLog_mem_unit N n hN hnN.le
  have hy := normalizedPrimeLog_mem_unit N (n+1) hN (by omega)
  unfold factorSign predicateSign
  by_cases hp : Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1)
  · rw [if_pos hp]
    have hpos := (logDifference_pos_iff N n hN hn).mpr hp
    rw [abs_of_pos hpos, logDifference_eq_sub] at hd
    have hlt := unitQuantize_lt_of_gap Q hQ _ _ hx.1 hy.1 hy.2 hd
    change primeQuantLabel Q N n < primeQuantLabel Q N (n+1) at hlt
    simp only [quantFactorSign,orderSkew,if_pos hlt]
  · rw [if_neg hp]
    have hnon : logDifference N n ≤ 0 := not_lt.mp
      (fun h => hp ((logDifference_pos_iff N n hN hn).mp h))
    rw [abs_of_nonpos hnon, logDifference_eq_sub] at hd
    have hgap : 1/(Q : ℝ) < normalizedPrimeLog N n-normalizedPrimeLog N (n+1) := by linarith
    have hlt := unitQuantize_lt_of_gap Q hQ _ _ hy.1 hx.1 hx.2 hgap
    change primeQuantLabel Q N (n+1) < primeQuantLabel Q N n at hlt
    simp only [quantFactorSign,orderSkew,if_neg hlt.not_gt,if_pos hlt]

lemma quantFactorSign_error_sum_bound (Q N : ℕ) (hQ : 0 < Q) (hN : 1 < N) :
    (∑ n ∈ range N, |factorSign n-quantFactorSign Q N n|) ≤
      2+2*((logRatioSet N (1/(Q : ℝ))).card : ℝ) := by
  classical
  have hterm (n : ℕ) (hnN : n ∈ range N) : |factorSign n-quantFactorSign Q N n| ≤
      (if n = 0 then (2 : ℝ) else 0) +
        (if logRatioEvent N (1/(Q : ℝ)) n then (2 : ℝ) else 0) := by
    by_cases hn : n = 0
    · rw [if_pos hn]
      exact (quantFactorSign_error_le_two Q N n).trans
        (le_add_of_nonneg_right (by split_ifs <;> norm_num))
    · rw [if_neg hn,zero_add]
      by_cases hnear : logRatioEvent N (1/(Q : ℝ)) n
      · rw [if_pos hnear]
        exact quantFactorSign_error_le_two Q N n
      · rw [if_neg hnear, quantFactorSign_eq_of_not_near Q N n hQ hN (by omega)
          (mem_range.mp hnN) hnear, sub_self, abs_zero]
  have hs := sum_le_sum hterm
  simpa only [sum_add_distrib,sum_ite_eq',mem_range,show 0 < N by omega,if_true,
    sum_ite,sum_const_zero,add_zero,sum_const,nsmul_eq_mul,logRatioSet,mul_comm] using hs

/-- Uniform approximation by all sufficiently fine finite quantizations. -/
theorem quantFactorSign_uniform_approximation (ε : ℝ) (hε : 0 < ε) :
    ∃ Q₀ > 0, ∀ᶠ N : ℕ in atTop, ∀ Q ≥ Q₀,
      (∑ n ∈ range N, |factorSign n-quantFactorSign Q N n|)/N ≤ ε := by
  obtain ⟨δ,hδ,hr⟩ := logRatioSet_uniform_rarity (ε/4) (by positivity)
  obtain ⟨Q₀,hQ₀⟩ := exists_nat_gt (max 1 (1/δ))
  have hQ₀pos : 0 < Q₀ := by
    have h : (1 : ℝ) < Q₀ := (le_max_left _ _).trans_lt hQ₀
    exact_mod_cast (show (0 : ℝ) < Q₀ by linarith)
  have hw : 1/(Q₀ : ℝ) ≤ δ := by
    have hq : 1/δ < (Q₀ : ℝ) := (le_max_right _ _).trans_lt hQ₀
    have hmul := (div_lt_iff₀ hδ).mp hq
    apply (div_le_iff₀ (by exact_mod_cast hQ₀pos : (0 : ℝ) < Q₀)).mpr
    nlinarith
  refine ⟨Q₀,hQ₀pos,?_⟩
  have ht := tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)
  filter_upwards [hr,ht.eventually_lt_const (by positivity : (0 : ℝ) < ε/2),
    eventually_gt_atTop (1 : ℕ)] with N hr ht hN
  intro Q hQ
  have hQpos := hQ₀pos.trans_le hQ
  have hwQ : 1/(Q : ℝ) ≤ δ := (one_div_le_one_div_of_le
    (by exact_mod_cast hQ₀pos) (by exact_mod_cast hQ)).trans hw
  have hcard := card_le_card (logRatioSet_mono_width N (1/(Q : ℝ)) δ hN.le hwQ)
  have hcardR : ((logRatioSet N (1/(Q : ℝ))).card : ℝ) ≤ (logRatioSet N δ).card :=
    Nat.cast_le.mpr hcard
  have hcount := div_le_div_of_nonneg_right
    (quantFactorSign_error_sum_bound Q N hQpos hN) (Nat.cast_nonneg (α := ℝ) N)
  have hcount' := div_le_div_of_nonneg_right hcardR (Nat.cast_nonneg (α := ℝ) N)
  rw [add_div,mul_div_assoc] at hcount
  linarith

#print axioms quantFactorSign_eq_of_not_near
#print axioms quantFactorSign_uniform_approximation
end Erdos371
