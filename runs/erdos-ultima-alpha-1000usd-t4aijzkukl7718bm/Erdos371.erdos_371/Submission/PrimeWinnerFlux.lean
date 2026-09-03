import Submission.PrimeWinnerEnergy
import Submission.BothLargePrimeBound

/-! Exact conservation of prime-label flow and absolute control of high-prime
groups. These results control boundary ranges, not the bulk energy. -/

namespace Erdos371

open Finset Filter
open scoped Topology

def primeLoser (n : ℕ) : ℕ := min (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n + 1))

noncomputable def primeLoserSum (p N : ℕ) : ℝ :=
  ∑ n ∈ (range N).filter (fun n => primeLoser n = p), factorSign n

def bothAboveSet (B N : ℕ) : Finset ℕ :=
  (range N).filter fun n => B < Nat.maxPrimeFac n ∧ B < Nat.maxPrimeFac (n + 1)

noncomputable def primeWinnerL1Above (B N : ℕ) : ℝ :=
  ∑ p ∈ (primeWinnerLabels N).filter (B < ·), ‖primeWinnerSum p N‖

noncomputable def primeWinnerEnergyAbove (B N : ℕ) : ℝ :=
  ∑ p ∈ (primeWinnerLabels N).filter (B < ·), (primeWinnerSum p N)^2

private lemma label_flow_term (a b p : ℕ) (hne : a ≠ b) :
    (if max a b = p then (if a < b then (1 : ℝ) else -1) else 0) -
      (if min a b = p then (if a < b then (1 : ℝ) else -1) else 0) =
      (if b = p then 1 else 0) - (if a = p then 1 else 0) := by
  rcases lt_or_gt_of_ne hne with h | h
  · simp [max_eq_right h.le, min_eq_left h.le, h]
  · simp only [max_eq_left h.le, min_eq_right h.le, if_neg h.not_gt]
    by_cases ha : a = p <;> by_cases hb : b = p <;> simp [ha, hb]

/-- The two group imbalances differ only by a telescoping endpoint term. -/
theorem primeWinnerSum_sub_primeLoserSum (p N : ℕ) :
    primeWinnerSum p N - primeLoserSum p N =
      (if Nat.maxPrimeFac N = p then 1 else 0) -
        (if Nat.maxPrimeFac 0 = p then 1 else 0) := by
  unfold primeWinnerSum primeLoserSum
  rw [sum_filter, sum_filter, ← sum_sub_distrib]
  have he (n : ℕ) := label_flow_term (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n + 1)) p
    (consecutive_maxPrimeFac_ne n).symm
  simp only [primeWinner, primeLoser, factorSign, predicateSign, he]
  exact sum_range_sub (fun n => if Nat.maxPrimeFac n = p then (1 : ℝ) else 0) N

lemma primeWinnerSum_norm_le_loser_count (p N : ℕ) (hp : 0 < p) :
    ‖primeWinnerSum p N‖ ≤
      (((range N).filter fun n => primeLoser n = p).card : ℝ) +
        (if Nat.maxPrimeFac N = p then 1 else 0) := by
  have hf := primeWinnerSum_sub_primeLoserSum p N
  simp only [Nat.maxPrimeFac_zero, if_neg (show ¬0 = p by omega), sub_zero] at hf
  have he : primeWinnerSum p N = primeLoserSum p N +
      (if Nat.maxPrimeFac N = p then 1 else 0) := by linarith
  rw [he]
  apply (norm_add_le _ _).trans
  have hlos : ‖primeLoserSum p N‖ ≤
      (((range N).filter fun n => primeLoser n = p).card : ℝ) := by
    unfold primeLoserSum
    simpa only [factorSign_norm, sum_const, nsmul_eq_mul, mul_one] using norm_sum_le
      ((range N).filter fun n => primeLoser n = p) factorSign
  have hend : ‖(if Nat.maxPrimeFac N = p then (1 : ℝ) else 0)‖ =
      (if Nat.maxPrimeFac N = p then 1 else 0) := by split_ifs <;> norm_num
  exact add_le_add hlos hend.le

/-- All absolute high-prime group imbalances are controlled by the number
of pairs with both factors high, plus a single endpoint correction. -/
theorem primeWinnerL1Above_le_bothAbove (B N : ℕ) :
    primeWinnerL1Above B N ≤ (bothAboveSet B N).card + 1 := by
  let S := (primeWinnerLabels N).filter (B < ·)
  have hpoint : primeWinnerL1Above B N ≤
      (∑ p ∈ S, (((range N).filter fun n => primeLoser n = p).card : ℝ)) +
        ∑ p ∈ S, if Nat.maxPrimeFac N = p then (1 : ℝ) else 0 := by
    rw [← sum_add_distrib]
    exact sum_le_sum fun p hp => primeWinnerSum_norm_le_loser_count p N
      (by have := (mem_filter.mp hp).2; omega)
  have hc : (∑ p ∈ S, (((range N).filter fun n => primeLoser n = p).card : ℝ)) ≤
      (bothAboveSet B N).card := by
    have hh := sum_card_fiberwise_eq_card_filter (range N) S primeLoser
    have hsub : ((range N).filter fun n => primeLoser n ∈ S) ⊆ bothAboveSet B N := by
      intro n hn
      obtain ⟨hnN, hnS⟩ := mem_filter.mp hn
      have hlo := (mem_filter.mp hnS).2
      exact mem_filter.mpr ⟨hnN, by simpa only [primeLoser, lt_min_iff] using hlo⟩
    have hcard := (card_le_card hsub)
    rw [← hh] at hcard
    exact_mod_cast hcard
  have he : (∑ p ∈ S, if Nat.maxPrimeFac N = p then (1 : ℝ) else 0) ≤ 1 := by
    simp only [sum_ite_eq]
    split_ifs <;> norm_num
  linarith

lemma primeWinnerSum_norm_le_multiples (p N : ℕ) :
    ‖primeWinnerSum p N‖ ≤ 2 * ((N / p : ℕ) : ℝ) + 1 := by
  have hnorm : ‖primeWinnerSum p N‖ ≤
      (((range N).filter fun n => primeWinner n = p).card : ℝ) := by
    unfold primeWinnerSum
    simpa only [factorSign_norm, sum_const, nsmul_eq_mul, mul_one] using norm_sum_le
      ((range N).filter fun n => primeWinner n = p) factorSign
  have hs : ((range N).filter fun n => primeWinner n = p) ⊆
      ((range N).filter fun n => p ∣ n) ∪ ((range N).filter fun n => p ∣ n + 1) := by
    intro n hn
    obtain ⟨hnN, he⟩ := mem_filter.mp hn
    rcases max_cases (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n + 1)) with h | h
    · apply mem_union_left
      apply mem_filter.mpr
      refine ⟨hnN, ?_⟩
      have hh : Nat.maxPrimeFac n = p := h.1.symm.trans he
      rw [← hh]
      exact Nat.maxPrimeFac_dvd
    · apply mem_union_right
      apply mem_filter.mpr
      refine ⟨hnN, ?_⟩
      have hh : Nat.maxPrimeFac (n + 1) = p := h.1.symm.trans he
      rw [← hh]
      exact Nat.maxPrimeFac_dvd
  have hzero : ((range N).filter fun n => p ∣ n) ⊆
      ((range (N + 1)).filter fun n => n ≠ 0 ∧ p ∣ n) ∪ {0} := by
    intro n hn
    obtain ⟨hnN, hpn⟩ := mem_filter.mp hn
    by_cases hn0 : n = 0
    · simp [hn0]
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp hnN; omega), hn0, hpn⟩)
  have hleft : ((range N).filter fun n => p ∣ n).card ≤ N / p + 1 := by
    apply (card_le_card hzero).trans
    simpa only [card_singleton, Nat.card_multiples'] using card_union_le
      ((range (N + 1)).filter fun n => n ≠ 0 ∧ p ∣ n) {0}
  have hcard := (card_le_card hs).trans (card_union_le _ _)
  rw [Nat.card_multiples] at hcard
  have hh : ((range N).filter fun n => primeWinner n = p).card ≤ 2 * (N / p) + 1 := by omega
  exact hnorm.trans (by exact_mod_cast hh)

/-- On a fixed cofactor range, the quadratic energy is bounded by a fixed
multiple of the absolute group imbalance. -/
theorem primeWinnerEnergyAbove_bound (B K N : ℕ) (hsize : N ≤ K * (B + 1)) :
    primeWinnerEnergyAbove B N ≤ (2 * K + 1 : ℝ) * primeWinnerL1Above B N := by
  unfold primeWinnerEnergyAbove primeWinnerL1Above
  rw [mul_sum]
  apply sum_le_sum
  intro p hp
  have hpB := (mem_filter.mp hp).2
  have hp0 : 0 < p := by omega
  have hNp : N ≤ K * p := hsize.trans (Nat.mul_le_mul_left K (by omega))
  have hdiv : N / p ≤ K := by
    have hh := Nat.div_mul_le_self N p
    nlinarith
  have hnorm : ‖primeWinnerSum p N‖ ≤ 2 * K + 1 :=
    (primeWinnerSum_norm_le_multiples p N).trans (by exact_mod_cast (show 2 * (N / p) + 1 ≤ 2 * K + 1 by omega))
  have hh := mul_le_mul_of_nonneg_right hnorm (norm_nonneg (primeWinnerSum p N))
  simpa only [← pow_two, Real.norm_eq_abs, sq_abs] using hh

open FiniteSieve in
/-- An O(u^2) bound for the sum of absolute imbalances in the top power band.
For fixed u>0 this bound does not tend to zero. -/
theorem primeWinnerL1Above_top_eventually_le (B : ℕ → ℕ) (u : ℝ)
    (hu0 : 0 ≤ u) (hu : u ≤ 1 / 8)
    (hcut : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (1 - u) ≤ B N)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, primeWinnerL1Above (B N) N / N ≤ largePairConstant * u^2 + ε := by
  have he := tendsto_one_div_atTop_nhds_zero_nat.eventually_lt_const (half_pos hε)
  filter_upwards [hcut, bothLargePrimeSet_eventually_ratio_le u hu0 hu (ε / 2) (half_pos hε), he]
    with N hBN hboth hsmall
  have hsub : bothAboveSet (B N) N ⊆ bothLargePrimeSet N u := by
    intro n hn
    obtain ⟨hnN, hn, hn'⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨hnN, hBN.trans_lt (by exact_mod_cast hn), hBN.trans_lt (by exact_mod_cast hn')⟩
  have hb := div_le_div_of_nonneg_right (primeWinnerL1Above_le_bothAbove (B N) N)
    (Nat.cast_nonneg (α := ℝ) N)
  have hc := div_le_div_of_nonneg_right ((Nat.cast_le (α := ℝ)).mpr (card_le_card hsub))
    (Nat.cast_nonneg (α := ℝ) N)
  rw [add_div] at hb
  linarith

lemma div_cutoff_eventually_ge_power (K : ℕ) (hK : 0 < K) (u : ℝ) (hu : 0 < u) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (1 - u) ≤ ((N / K : ℕ) : ℝ) := by
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ u) atTop atTop :=
    (tendsto_rpow_atTop hu).comp tendsto_natCast_atTop_atTop
  filter_upwards [hpow.eventually_ge_atTop (2 * K : ℝ), eventually_ge_atTop K] with N hp hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hK.trans_le hN
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hdiv : 1 ≤ N / K := (Nat.le_div_iff_mul_le hK).mpr (by simpa using hN)
  have hfloor : N ≤ 2 * K * (N / K) := by
    have hh := Nat.mod_lt N hK
    have he := Nat.mod_add_div N K
    nlinarith
  have hfloor' : (N : ℝ) ≤ 2 * K * ((N / K : ℕ) : ℝ) := by exact_mod_cast hfloor
  have hprod : (N : ℝ) ^ (1 - u) * (N : ℝ) ^ u = N := by
    rw [← Real.rpow_add hN0]
    simp
  have hm := mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg (Nat.cast_nonneg N) (1 - u))
  rw [hprod] at hm
  exact le_of_mul_le_mul_left (by nlinarith : (2 * K : ℝ) * (N : ℝ) ^ (1 - u) ≤
    (2 * K : ℝ) * ((N / K : ℕ) : ℝ)) (by positivity)

open FiniteSieve in
/-- The total absolute imbalance of groups with p>N/K is negligible for
any fixed positive K. The cutoff still has exponent tending to one. -/
theorem primeWinnerL1Above_fixed_cofactor_tendsto (K : ℕ) (hK : 0 < K) :
    Tendsto (fun N : ℕ => primeWinnerL1Above (N / K) N / N) atTop (nhds 0) := by
  apply tendsto_order.mpr
  constructor
  · intro ε hε
    exact Eventually.of_forall fun N => hε.trans_le (by unfold primeWinnerL1Above; positivity)
  · intro ε hε
    have hC : 0 ≤ largePairConstant := by unfold largePairConstant; positivity
    have hden : 0 < 4 * (largePairConstant + 1) := by positivity
    let u : ℝ := min (1 / 8) (ε / (4 * (largePairConstant + 1)))
    have hu0 : 0 < u := lt_min (by norm_num) (div_pos hε hden)
    have hu : u ≤ 1 / 8 := min_le_left _ _
    have huε : u * (4 * (largePairConstant + 1)) ≤ ε :=
      (le_div_iff₀ hden).mp (min_le_right _ _)
    have husq : u^2 ≤ u := by nlinarith [hu0.le]
    have hcu : largePairConstant * u^2 ≤ ε / 4 := by
      have hh := mul_le_mul_of_nonneg_left husq hC
      nlinarith [hu0.le]
    have he := primeWinnerL1Above_top_eventually_le (fun N => N / K) u hu0.le hu
      (div_cutoff_eventually_ge_power K hK u hu0) (ε / 2) (half_pos hε)
    filter_upwards [he] with N hN
    linarith

/-- A genuine quadratic-energy bound in the fixed-cofactor boundary range.
No analogous assertion for the bulk prime range is proved here. -/
theorem primeWinnerEnergyAbove_fixed_cofactor_tendsto (K : ℕ) (hK : 0 < K) :
    Tendsto (fun N : ℕ => primeWinnerEnergyAbove (N / K) N / N) atTop (nhds 0) := by
  have ht := (primeWinnerL1Above_fixed_cofactor_tendsto K hK).const_mul (2 * K + 1 : ℝ)
  simp only [mul_zero] at ht
  apply squeeze_zero (fun _ => by unfold primeWinnerEnergyAbove; positivity) _ ht
  intro N
  have hsize : N ≤ K * (N / K + 1) := by
    have hh := Nat.mod_lt N hK
    have he := Nat.mod_add_div N K
    nlinarith
  have hb := div_le_div_of_nonneg_right (primeWinnerEnergyAbove_bound (N / K) K N hsize)
    (Nat.cast_nonneg (α := ℝ) N)
  simpa only [mul_div_assoc] using hb

#print axioms primeWinnerSum_sub_primeLoserSum
#print axioms primeWinnerL1Above_le_bothAbove
#print axioms primeWinnerEnergyAbove_bound
#print axioms primeWinnerL1Above_top_eventually_le
#print axioms primeWinnerL1Above_fixed_cofactor_tendsto
#print axioms primeWinnerEnergyAbove_fixed_cofactor_tendsto

end Erdos371
