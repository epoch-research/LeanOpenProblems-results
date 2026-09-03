import Submission.BilinearRows
import Submission.CutoffSeparation

/-! Negligibility of fixed cofactor ranges in complete rows of the rough tail. -/

namespace Erdos371

lemma exists_small_totient_ratio_pow (k : ℕ) :
    ∃ M : ℕ, 0 < M ∧ (M.totient : ℝ) / M ≤ (2 / 3 : ℝ)^k := by
  induction k with
  | zero => exact ⟨1, by omega, by norm_num⟩
  | succ k ih =>
    obtain ⟨M, hM, hratio⟩ := ih
    obtain ⟨R, hR, hc, _, ht⟩ := exists_large_prime_modulus M hM
    refine ⟨M * R, by positivity, ?_⟩
    have hr : (R.totient : ℝ) / R ≤ 2 / 3 := by
      apply (div_le_iff₀ (by exact_mod_cast hR)).mpr
      have : (3 : ℝ) * R.totient ≤ 2 * R := by exact_mod_cast ht
      linarith
    rw [Nat.totient_mul hc, Nat.cast_mul, Nat.cast_mul, mul_div_mul_comm, pow_succ]
    exact mul_le_mul hratio hr (by positivity) (by positivity)

open Filter in
lemma exists_small_totient_ratio (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ, 0 < M ∧ (M.totient : ℝ) / M < ε := by
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (show (0 : ℝ) ≤ 2 / 3 by norm_num)
    (show (2 / 3 : ℝ) < 1 by norm_num)
  obtain ⟨k, hk⟩ := ((tendsto_order.mp ht).2 ε hε).exists
  obtain ⟨M, hM, hr⟩ := exists_small_totient_ratio_pow k
  exact ⟨M, hM, hr.trans_lt hk⟩

def roughNumberCount (B N : ℕ) : ℕ :=
  ((Finset.range N).filter fun n => 1 < n ∧ B < n.minFac).card

open Filter in
/-- An unbounded least-prime-factor cutoff leaves a negligible proportion of
integers. This statement is uniform for every sequence of growing cutoffs. -/
theorem growing_roughNumberCount_tendsto (B : ℕ → ℕ) (hB : Tendsto B atTop atTop) :
    Tendsto (fun N : ℕ => (roughNumberCount (B N) N : ℝ) / N) atTop (nhds 0) := by
  apply tendsto_order.mpr
  constructor
  · intro ε hε
    exact Eventually.of_forall fun N => hε.trans_le (by positivity)
  · intro ε hε
    obtain ⟨M, hM, hr⟩ := exists_small_totient_ratio ε hε
    have ht := (density_iff_count (fun n => M.Coprime n) _).mp
      (periodic_predicate_hasDensity (fun n => M.Coprime n) M hM (Nat.periodic_coprime M))
    have hr' : (((Finset.range M).filter fun n => M.Coprime n).card : ℝ) / M < ε := by
      simpa only [← Nat.totient_eq_card_coprime] using hr
    filter_upwards [hB.eventually_ge_atTop M, (tendsto_order.mp ht).2 ε hr'] with N hBN hN
    have hc : roughNumberCount (B N) N ≤ ((Finset.range N).filter fun n => M.Coprime n).card := by
      apply Finset.card_le_card
      intro n hn
      obtain ⟨hnN, _, hmin⟩ := Finset.mem_filter.mp hn
      exact Finset.mem_filter.mpr ⟨hnN, (Nat.coprime_of_lt_minFac hM.ne' (hBN.trans_lt hmin)).symm⟩
    exact (div_le_div_of_nonneg_right (by exact_mod_cast hc) (Nat.cast_nonneg N)).trans_lt hN

lemma roughNumberCount_succ_le (B N : ℕ) : roughNumberCount B (N + 1) ≤ roughNumberCount B N + 1 := by
  unfold roughNumberCount
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs
  · exact Finset.card_insert_le _ _
  · omega

open Filter in
theorem growing_roughNumberCount_succ_tendsto (B : ℕ → ℕ) (hB : Tendsto B atTop atTop) :
    Tendsto (fun N : ℕ => (roughNumberCount (B N) (N + 1) : ℝ) / N) atTop (nhds 0) := by
  have ht := (growing_roughNumberCount_tendsto B hB).add tendsto_one_div_atTop_nhds_zero_nat
  simp only [add_zero] at ht
  apply squeeze_zero (fun _ => by positivity) _ ht
  intro N
  rw [← add_div]
  exact div_le_div_of_nonneg_right (by exact_mod_cast roughNumberCount_succ_le (B N) N)
    (Nat.cast_nonneg N)


lemma fixed_cofactor_count_bound (B K N : ℕ) :
    (∑ n ∈ Finset.range N, ((n + 1).divisors.filter fun a =>
      N < K * a ∧ 1 < a ∧ B < a.minFac).card) ≤ K * roughNumberCount B (N + 1) := by
  rw [← Finset.card_sigma]
  have ht : K * roughNumberCount B (N + 1) =
      (((Finset.range (N + 1)).filter fun a => 1 < a ∧ B < a.minFac) ×ˢ Finset.range K).card := by
    simp [roughNumberCount, mul_comm]
  rw [ht]
  apply Finset.card_le_card_of_injOn (fun x : Σ _n : ℕ, ℕ => (x.2, (x.1 + 1) / x.2))
  · intro x hx
    obtain ⟨hxN, hxdiv, hxK, hx1, hxB⟩ := by
      simpa only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_filter] using hx
    have hxN' := Finset.mem_range.mp hxN
    have hxdiv' := (Nat.mem_divisors.mp hxdiv).1
    have hxa : x.2 ≤ x.1 + 1 := Nat.le_of_dvd (by omega) hxdiv'
    dsimp only
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hx1, hxB⟩, ?_⟩
    apply Finset.mem_range.mpr
    exact (Nat.div_lt_iff_lt_mul (by omega : 0 < x.2)).mpr (by omega)
  · intro x hx y hy he
    obtain ⟨hxN, hxdiv, hxK, hx1, hxB⟩ := by
      simpa only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_filter] using hx
    obtain ⟨hyN, hydiv, hyK, hy1, hyB⟩ := by
      simpa only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_filter] using hy
    have ha : x.2 = y.2 := congrArg Prod.fst he
    have hk : (x.1 + 1) / x.2 = (y.1 + 1) / y.2 := congrArg Prod.snd he
    have hmx := Nat.mul_div_cancel' (Nat.mem_divisors.mp hxdiv).1
    have hmy := Nat.mul_div_cancel' (Nat.mem_divisors.mp hydiv).1
    rw [hk, ha] at hmx
    have hn : x.1 = y.1 := by omega
    exact Sigma.ext hn (heq_of_eq ha)

noncomputable def largeBilinearRows (B D K N n : ℕ) : ℝ :=
  ∑ a ∈ n.divisors with N < K * a,
    ∑ b ∈ (n + 1).divisors, roughBilinearWeight B D a b

lemma largeBilinearRows_norm_le (B D K N n : ℕ) (hD : D ≤ N) (hK : K ≤ B + 1) :
    ‖largeBilinearRows B D K N n‖ ≤
      ((n.divisors.filter fun a => N < K * a ∧ 1 < a ∧ B < a.minFac).card : ℝ) := by
  unfold largeBilinearRows
  calc
    _ ≤ ∑ a ∈ n.divisors with N < K * a,
        ‖∑ b ∈ (n + 1).divisors, roughBilinearWeight B D a b‖ := norm_sum_le _ _
    _ ≤ ∑ a ∈ n.divisors with N < K * a,
        if 1 < a ∧ B < a.minFac then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro a ha
      by_cases h : 1 < a ∧ B < a.minFac
      · rw [if_pos h]
        apply roughBilinearWeight_row_norm_le
        have hNa := (Finset.mem_filter.mp ha).2
        have hmul := Nat.mul_le_mul_right a hK
        nlinarith
      · simp only [if_neg h, roughBilinearWeight_bad_row B D a _ h, Finset.sum_const_zero, norm_zero,
          le_refl]
    _ = _ := by simp [Finset.filter_filter]

lemma largeBilinearRows_prefix_bound (B D K N : ℕ) (hD : D ≤ N) (hK : K ≤ B + 1) :
    ‖∑ n ∈ Finset.range N, largeBilinearRows B D K N (n + 1)‖ ≤
      K * (roughNumberCount B (N + 1) : ℝ) := by
  calc
    _ ≤ ∑ n ∈ Finset.range N, ‖largeBilinearRows B D K N (n + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range N, (((n + 1).divisors.filter fun a =>
        N < K * a ∧ 1 < a ∧ B < a.minFac).card : ℝ) :=
      Finset.sum_le_sum fun n _ => largeBilinearRows_norm_le B D K N (n + 1) hD hK
    _ ≤ _ := by exact_mod_cast fixed_cofactor_count_bound B K N

open Filter in
/-- For every fixed K, complete rows with a > N/K have zero normalized
average. The row estimate retains cancellation inside each complete row. -/
theorem largeBilinearRows_average_zero (K : ℕ) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N,
        largeBilinearRows (roughCutoff N) (nearLinearCutoff N) K N (n + 1)) / N)
      atTop (nhds 0) := by
  have ht := (growing_roughNumberCount_succ_tendsto roughCutoff roughCutoff_atTop).const_mul (K : ℝ)
  simp only [mul_zero] at ht
  apply squeeze_zero_norm' _ ht
  filter_upwards [roughCutoff_atTop.eventually_ge_atTop K] with N hN
  rw [norm_div, Real.norm_natCast]
  calc
    _ ≤ (K * (roughNumberCount (roughCutoff N) (N + 1) : ℝ)) / N :=
      div_le_div_of_nonneg_right (largeBilinearRows_prefix_bound _ _ _ _
        (nearLinearCutoff_le_self N) (by omega)) (Nat.cast_nonneg N)
    _ = _ := by ring


noncomputable def shortBilinearRows (B D K N n : ℕ) : ℝ :=
  ∑ a ∈ n.divisors with K * a ≤ N,
    ∑ b ∈ (n + 1).divisors, roughBilinearWeight B D a b

lemma short_add_large_rows (B D K N n : ℕ) (hn : 0 < n) :
    shortBilinearRows B D K N n + largeBilinearRows B D K N n = roughMixedDivisorTail B D n := by
  rw [shortBilinearRows, largeBilinearRows]
  have h := Finset.sum_filter_add_sum_filter_not (s := n.divisors)
    (fun a => K * a ≤ N) (fun a => ∑ b ∈ (n + 1).divisors, roughBilinearWeight B D a b)
  simpa only [not_le, roughMixedDivisorTail_bilinear B D n hn] using h

open Filter in
/-- Every fixed cofactor range on the first side can be removed. The mean of
the truncated bilinear sum remains an unproved limit. -/
theorem density_iff_short_bilinear_rows (K : ℕ) :
    {n | Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac n}.HasDensity (1 / 2) ↔
      Tendsto (fun N : ℕ =>
        (∑ n ∈ Finset.range N,
          shortBilinearRows (roughCutoff N) (nearLinearCutoff N) K N (n + 1)) / N)
        atTop (nhds 0) := by
  rw [density_iff_growing_rough_mixed_tail]
  have he (N : ℕ) :
      (∑ n ∈ Finset.range N,
        shortBilinearRows (roughCutoff N) (nearLinearCutoff N) K N (n + 1)) / N +
      (∑ n ∈ Finset.range N,
        largeBilinearRows (roughCutoff N) (nearLinearCutoff N) K N (n + 1)) / N =
      (∑ n ∈ Finset.range N,
        roughMixedDivisorTail (roughCutoff N) (nearLinearCutoff N) (n + 1)) / N := by
    rw [← add_div, ← Finset.sum_add_distrib]
    simp_rw [short_add_large_rows _ _ _ _ _ (Nat.zero_lt_succ _)]
  have hlarge := largeBilinearRows_average_zero K
  constructor
  · intro h
    have ht := h.sub hlarge
    simp only [sub_zero] at ht
    apply ht.congr
    intro N
    linarith [he N]
  · intro h
    have ht := h.add hlarge
    simp only [add_zero] at ht
    exact ht.congr he

#print axioms growing_roughNumberCount_tendsto
#print axioms largeBilinearRows_average_zero
#print axioms density_iff_short_bilinear_rows
end Erdos371
