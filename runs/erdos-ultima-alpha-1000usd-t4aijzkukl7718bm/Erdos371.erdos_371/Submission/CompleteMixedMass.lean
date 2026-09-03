import Submission.SubpowerTail

/-! The complete rough mixed sum has asymptotic absolute mass one. Thus
roughness alone does not make its absolute average small. This does not
estimate the absolute average after the product cutoff is imposed. -/

namespace Erdos371

lemma roughMobiusTail_zero_cutoff (B n : ℕ) (hB : 1 ≤ B) (hn : 0 < n) :
    roughMobiusTail B 0 n = -(if B < Nat.maxPrimeFac n then 1 else 0) := by
  by_cases hn1 : 1 < n
  · have hterm (d : ℕ) :
        (if 0 < d ∧ B < d.minFac then signedMobius d else 0) =
          leastFactorTerm (fun p => if B < p then 1 else 0) d := by
      rw [leastFactorTerm_eq_moebius]
      unfold signedMobius
      by_cases hd : 1 < d
      · simp [hd, show 0 < d by omega]
      · simp [hd]
    unfold roughMobiusTail
    simp_rw [hterm]
    exact alladi_divisors n hn1 _
  · have hn' : n = 1 := by omega
    subst n
    simp [roughMobiusTail_one, show B ≠ 0 by omega]

lemma roughLargeDivisorTail_zero_cutoff (B n : ℕ) (hn : 0 < n) :
    roughLargeDivisorTail B 0 n =
      if B < Nat.maxPrimeFac (n * (n + 1)) then -factorSign n else 0 := by
  have he : ((n * (n + 1)).divisors.filter fun d => 0 < d ∧ B < d.minFac) =
      ((n * (n + 1)).divisors.filter fun d => B < d.minFac) := by
    ext d
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨h.1, h.2.2⟩,
      fun h => ⟨h.1, Nat.pos_of_mem_divisors h.1, h.2⟩⟩
  rw [roughLargeDivisorTail, he]
  exact orientedDivisorTerm_filter n hn (fun p => B < p)

/-- With no product cutoff, all mixed rough divisors sum to the comparison
sign restricted to the event that both integers have a prime factor above B. -/
theorem complete_rough_mixed_sum_eq (B n : ℕ) (hB : 1 ≤ B) (hn : 0 < n) :
    roughMixedDivisorTail B 0 n =
      if B < Nat.maxPrimeFac n ∧ B < Nat.maxPrimeFac (n + 1) then -factorSign n else 0 := by
  have he := roughLargeDivisorTail_decompose B 0 n hn
  rw [roughLargeDivisorTail_zero_cutoff B n hn,
    roughMobiusTail_zero_cutoff B (n + 1) hB (by omega),
    roughMobiusTail_zero_cutoff B n hB hn,
    Nat.maxPrimeFac_mul hn.ne' (by omega)] at he
  by_cases h₁ : B < Nat.maxPrimeFac n
  · by_cases h₂ : B < Nat.maxPrimeFac (n + 1)
    · simp only [lt_max_iff, h₁, h₂, or_self, and_self, if_true] at he ⊢
      linarith
    · have hs : factorSign n = -1 := by
        simp [factorSign, predicateSign, show ¬Nat.maxPrimeFac n < Nat.maxPrimeFac (n + 1) by omega]
      simp only [lt_max_iff, h₁, h₂, or_false, and_false, if_true, if_false, hs] at he ⊢
      linarith
  · by_cases h₂ : B < Nat.maxPrimeFac (n + 1)
    · have hs : factorSign n = 1 := by
        simp [factorSign, predicateSign, show Nat.maxPrimeFac n < Nat.maxPrimeFac (n + 1) by omega]
      simp only [lt_max_iff, h₁, h₂, false_or, false_and, if_true, if_false, hs] at he ⊢
      linarith
    · simp only [lt_max_iff, h₁, h₂, or_self, and_self, if_false] at he ⊢
      linarith

lemma complete_rough_mixed_norm (B n : ℕ) (hB : 1 ≤ B) (hn : 0 < n) :
    ‖roughMixedDivisorTail B 0 n‖ =
      if B < Nat.maxPrimeFac n ∧ B < Nat.maxPrimeFac (n + 1) then 1 else 0 := by
  rw [complete_rough_mixed_sum_eq B n hB hn]
  split_ifs <;> simp only [norm_neg, factorSign_norm, norm_zero]

lemma complete_rough_mixed_norm_loss (B n : ℕ) (hB : 1 ≤ B) (hn : 0 < n) :
    0 ≤ 1 - ‖roughMixedDivisorTail B 0 n‖ ∧
      1 - ‖roughMixedDivisorTail B 0 n‖ ≤
        (if Nat.maxPrimeFac n ≤ B then 1 else 0) +
        (if Nat.maxPrimeFac (n + 1) ≤ B then 1 else 0) := by
  rw [complete_rough_mixed_norm B n hB hn]
  by_cases h₁ : B < Nat.maxPrimeFac n <;> by_cases h₂ : B < Nat.maxPrimeFac (n + 1) <;>
    simp [h₁, h₂, show (Nat.maxPrimeFac n ≤ B) ↔ ¬ B < Nat.maxPrimeFac n from not_lt.symm,
      show (Nat.maxPrimeFac (n + 1) ≤ B) ↔ ¬ B < Nat.maxPrimeFac (n + 1) from not_lt.symm]

lemma smooth_shifted_indicator_sum_le (B N k : ℕ) :
    (∑ n ∈ Finset.range N, if Nat.maxPrimeFac (n + k) ≤ B then (1 : ℝ) else 0) ≤
      (((Finset.range (N + k)).filter fun n => Nat.maxPrimeFac n ≤ B).card : ℝ) := by
  have he := Finset.sum_range_add (fun n => if Nat.maxPrimeFac n ≤ B then (1 : ℝ) else 0) k N
  have hpos : 0 ≤ ∑ n ∈ Finset.range k, if Nat.maxPrimeFac n ≤ B then (1 : ℝ) else 0 := by
    apply Finset.sum_nonneg
    intro n hn
    split_ifs <;> norm_num
  have hsum : (∑ n ∈ Finset.range (N + k), if Nat.maxPrimeFac n ≤ B then (1 : ℝ) else 0) =
      (((Finset.range (N + k)).filter fun n => Nat.maxPrimeFac n ≤ B).card : ℝ) := by simp
  simp only [Nat.add_comm k] at he
  linarith

lemma smooth_count_add_two_le (B N : ℕ) :
    (((Finset.range (N + 2)).filter fun n => Nat.maxPrimeFac n ≤ B).card : ℝ) ≤
      (((Finset.range N).filter fun n => Nat.maxPrimeFac n ≤ B).card : ℝ) + 2 := by
  have he : (((Finset.range (N + 2)).filter fun n => Nat.maxPrimeFac n ≤ B).card : ℝ) =
      (((Finset.range N).filter fun n => Nat.maxPrimeFac n ≤ B).card : ℝ) +
        (if Nat.maxPrimeFac N ≤ B then 1 else 0) +
        (if Nat.maxPrimeFac (N + 1) ≤ B then 1 else 0) := by
    have h₁ := Finset.sum_range_succ (fun n => if Nat.maxPrimeFac n ≤ B then (1 : ℝ) else 0) N
    have h₂ := Finset.sum_range_succ (fun n => if Nat.maxPrimeFac n ≤ B then (1 : ℝ) else 0) (N + 1)
    simp only [Finset.sum_boole, Nat.add_assoc, Nat.reduceAdd] at h₁ h₂
    linarith
  rw [he]
  split_ifs <;> linarith

lemma complete_rough_mixed_norm_loss_bound (B N : ℕ) (hB : 1 ≤ B) :
    0 ≤ ∑ n ∈ Finset.range N, (1 - ‖roughMixedDivisorTail B 0 (n + 1)‖) ∧
      (∑ n ∈ Finset.range N, (1 - ‖roughMixedDivisorTail B 0 (n + 1)‖)) ≤
        2 * (((Finset.range N).filter fun n => Nat.maxPrimeFac n ≤ B).card : ℝ) + 4 := by
  constructor
  · exact Finset.sum_nonneg fun n _ => (complete_rough_mixed_norm_loss B (n + 1) hB (by omega)).1
  · calc
      _ ≤ ∑ n ∈ Finset.range N,
          ((if Nat.maxPrimeFac (n + 1) ≤ B then (1 : ℝ) else 0) +
          (if Nat.maxPrimeFac (n + 2) ≤ B then 1 else 0)) :=
        Finset.sum_le_sum fun n _ => (complete_rough_mixed_norm_loss B (n + 1) hB (by omega)).2
      _ = (∑ n ∈ Finset.range N, if Nat.maxPrimeFac (n + 1) ≤ B then (1 : ℝ) else 0) +
          (∑ n ∈ Finset.range N, if Nat.maxPrimeFac (n + 2) ≤ B then (1 : ℝ) else 0) :=
        Finset.sum_add_distrib
      _ ≤ 2 * (((Finset.range (N + 2)).filter fun n => Nat.maxPrimeFac n ≤ B).card : ℝ) := by
        have h₁ := smooth_shifted_indicator_sum_le B N 1
        have h₂ := smooth_shifted_indicator_sum_le B N 2
        have hcard : (((Finset.range (N + 1)).filter fun n => Nat.maxPrimeFac n ≤ B).card : ℝ) ≤
            (((Finset.range (N + 2)).filter fun n => Nat.maxPrimeFac n ≤ B).card : ℝ) := by
          exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _
            (Finset.range_mono (show N + 1 ≤ N + 2 by omega)))
        linarith
      _ ≤ _ := by linarith [smooth_count_add_two_le B N]

open Filter in
/-- The complete mixed sum has absolute average one for every admissible
subpower cutoff, even though its signed average is the unresolved question. -/
theorem complete_rough_mixed_absolute_average_one (B : ℕ → ℕ)
    (hB1 : ∀ᶠ N in atTop, 1 ≤ B N)
    (hB : Tendsto (fun N => Real.log (B N + 1 : ℝ) / Real.log N) atTop (nhds 0)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, ‖roughMixedDivisorTail (B N) 0 (n + 1)‖) / N)
      atTop (nhds 1) := by
  have hcount := subpower_smooth_count_tendsto_zero B hB
  have hbound := (hcount.const_mul (2 : ℝ)).add (tendsto_const_div_atTop_nhds_zero_nat (4 : ℝ))
  simp only [mul_zero, add_zero] at hbound
  have hloss : Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, (1 - ‖roughMixedDivisorTail (B N) 0 (n + 1)‖)) / N)
      atTop (nhds 0) := by
    apply squeeze_zero_norm' _ hbound
    filter_upwards [hB1] with N hBN
    have h := complete_rough_mixed_norm_loss_bound (B N) N hBN
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg h.1 (Nat.cast_nonneg N))]
    calc
      _ ≤ (2 * (((Finset.range N).filter fun n => Nat.maxPrimeFac n ≤ B N).card : ℝ) + 4) / N :=
        div_le_div_of_nonneg_right h.2 (Nat.cast_nonneg N)
      _ = _ := by ring
  have ht := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).sub hloss
  simp only [sub_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp
  ring

#print axioms complete_rough_mixed_sum_eq
#print axioms complete_rough_mixed_absolute_average_one
end Erdos371
