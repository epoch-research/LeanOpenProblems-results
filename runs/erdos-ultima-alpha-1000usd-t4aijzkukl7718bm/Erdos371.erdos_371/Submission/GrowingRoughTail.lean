import Submission.SparseTailExplore
import Submission.RoughDivisorGroups

/-! Growing least-prime-factor cutoffs and a doubly restricted remainder. -/

namespace Erdos371

/-- An explicit unbounded cutoff of logarithmic size. -/
def roughCutoff (N : ℕ) : ℕ := Nat.log 2 N.sqrt.sqrt

lemma maxPrimeFac_count_bound (B N : ℕ) :
    ((Finset.range N).filter fun n => Nat.maxPrimeFac n ≤ B).card ≤
      2 ^ (B + 1) * N.sqrt + 1 := by
  have hsub : ((Finset.range N).filter fun n => Nat.maxPrimeFac n ≤ B) ⊆
      insert 0 (Nat.smoothNumbersUpTo N (B + 1)) := by
    intro n hn
    obtain ⟨hnN, hnB⟩ := Finset.mem_filter.mp hn
    by_cases hn : n = 0
    · simp [hn]
    · apply Finset.mem_insert_of_mem
      apply Nat.mem_smoothNumbersUpTo.mpr
      refine ⟨(Finset.mem_range.mp hnN).le, Nat.mem_smoothNumbers'.mpr ?_⟩
      intro p hp hpn
      exact Nat.lt_succ_of_le ((Nat.le_maxPrimeFac hn hp hpn).trans hnB)
  have hc : (B + 1).primesBelow.card ≤ B + 1 := by
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_range _)
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_insert_le _ _).trans
      ((Nat.add_le_add_right (Nat.smoothNumbersUpTo_card_le N (B + 1)) 1).trans
        (by gcongr; norm_num)))

lemma roughCutoff_count_bound (N : ℕ) (hN : 0 < N) :
    ((Finset.range N).filter fun n => Nat.maxPrimeFac n ≤ roughCutoff N).card ≤
      2 * N.sqrt.sqrt * N.sqrt + 1 := by
  have hs : N.sqrt.sqrt ≠ 0 := by
    simpa only [ne_eq, Nat.sqrt_eq_zero] using hN.ne'
  have hp := Nat.pow_log_le_self 2 hs
  apply (maxPrimeFac_count_bound (roughCutoff N) N).trans
  unfold roughCutoff
  rw [pow_succ]
  nlinarith

open Filter in
lemma nat_sqrt_atTop : Tendsto Nat.sqrt atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (b * b)] with n hn
  exact Nat.le_sqrt.mpr hn

open Filter in
lemma roughCutoff_atTop : Tendsto roughCutoff atTop atTop := by
  have hl : Tendsto (Nat.log 2) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (2 ^ b)] with n hn
    have hn0 : n ≠ 0 := by have := Nat.two_pow_pos b; omega
    exact (Nat.le_log_iff_pow_le (by omega) hn0).mpr hn
  exact hl.comp (nat_sqrt_atTop.comp nat_sqrt_atTop)

lemma roughCutoff_count_ratio_bound (N : ℕ) :
    (((Finset.range N).filter fun n => Nat.maxPrimeFac n ≤ roughCutoff N).card : ℝ) / N ≤
      2 / (N.sqrt.sqrt : ℝ) + 1 / N := by
  by_cases hN : N = 0
  · simp [hN]
  have hr : N.sqrt.sqrt ≠ 0 := by simpa only [ne_eq, Nat.sqrt_eq_zero] using hN
  have hn : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hrp : (0 : ℝ) < N.sqrt.sqrt := by exact_mod_cast Nat.pos_of_ne_zero hr
  have h₁ : (N.sqrt.sqrt : ℝ)^2 ≤ N.sqrt := by exact_mod_cast Nat.sqrt_le' N.sqrt
  have h₂ : (N.sqrt : ℝ)^2 ≤ N := by exact_mod_cast Nat.sqrt_le' N
  have h₃ : (N.sqrt.sqrt : ℝ)^2 * N.sqrt ≤ N := by
    calc
      _ ≤ (N.sqrt : ℝ) * N.sqrt := mul_le_mul_of_nonneg_right h₁ (Nat.cast_nonneg _)
      _ ≤ N := by nlinarith
  have hc : (((Finset.range N).filter fun n => Nat.maxPrimeFac n ≤ roughCutoff N).card : ℝ) ≤
      2 * (N.sqrt.sqrt : ℝ) * N.sqrt + 1 := by
    exact_mod_cast roughCutoff_count_bound N (Nat.pos_of_ne_zero hN)
  calc
    _ ≤ (2 * (N.sqrt.sqrt : ℝ) * N.sqrt + 1) / N := by gcongr
    _ = 2 * (N.sqrt.sqrt : ℝ) * N.sqrt / N + 1 / N := add_div _ _ _
    _ ≤ _ := by
      apply add_le_add _ (le_refl _)
      apply (div_le_div_iff₀ hn hrp).mpr
      nlinarith

open Filter in
/-- Uniform negligibility for an explicit growing smoothness threshold. -/
theorem roughCutoff_smooth_count_tendsto_zero :
    Tendsto (fun N : ℕ =>
      (((Finset.range N).filter fun n => Nat.maxPrimeFac n ≤ roughCutoff N).card : ℝ) / N)
      atTop (nhds 0) := by
  have ht : Tendsto (fun N : ℕ => 2 / (N.sqrt.sqrt : ℝ) + 1 / N)
      atTop (nhds 0) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).comp
      (nat_sqrt_atTop.comp nat_sqrt_atTop)
    simpa only [zero_add] using h.add tendsto_one_div_atTop_nhds_zero_nat
  exact squeeze_zero (fun _ => by positivity) roughCutoff_count_ratio_bound ht

open Filter in
theorem growing_lowLeastDivisorGroup_average_zero :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, lowLeastDivisorGroup (roughCutoff N) n) / N)
      atTop (nhds 0) := by
  apply squeeze_zero_norm (a := fun N : ℕ =>
    (((Finset.range N).filter fun n => Nat.maxPrimeFac n ≤ roughCutoff N).card : ℝ) / N)
    _ roughCutoff_smooth_count_tendsto_zero
  intro N
  rw [norm_div, Real.norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  calc
    _ ≤ ∑ n ∈ Finset.range N, ‖lowLeastDivisorGroup (roughCutoff N) n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range N, (if Nat.maxPrimeFac n ≤ roughCutoff N then (1 : ℝ) else 0) :=
      Finset.sum_le_sum fun n _ => lowLeastDivisorGroup_norm_le_indicator (roughCutoff N) n
    _ = _ := by simp

open Filter in
theorem growing_lowLeastDivisorGroup_shifted_average_zero :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N,
      lowLeastDivisorGroup (roughCutoff N) (n + 1)) / N) atTop (nhds 0) := by
  have he (B N : ℕ) :
      (∑ n ∈ Finset.range N, lowLeastDivisorGroup B (n + 1)) =
        (∑ n ∈ Finset.range N, lowLeastDivisorGroup B n) + lowLeastDivisorGroup B N := by
    have h := Finset.sum_range_succ' (lowLeastDivisorGroup B) N
    rw [Finset.sum_range_succ] at h
    simpa only [lowLeastDivisorGroup_zero, add_zero] using h.symm
  have ht : Tendsto (fun N : ℕ => lowLeastDivisorGroup (roughCutoff N) N / N) atTop (nhds 0) := by
    apply squeeze_zero_norm (a := fun N : ℕ => (1 : ℝ) / N) _ tendsto_one_div_atTop_nhds_zero_nat
    intro N
    rw [norm_div, Real.norm_natCast]
    exact div_le_div_of_nonneg_right (lowLeastDivisorGroup_norm_le_one _ N) (Nat.cast_nonneg N)
  have h := growing_lowLeastDivisorGroup_average_zero.add ht
  simpa only [he, add_div, zero_add] using h


noncomputable def roughSmallDivisorSum (B D n : ℕ) : ℝ :=
  ∑ d ∈ Finset.range (D + 1) with B < d.minFac, orientedDivisorTerm d n

noncomputable def roughLargeDivisorTail (B D n : ℕ) : ℝ :=
  ∑ d ∈ (n * (n + 1)).divisors with D < d ∧ B < d.minFac, orientedDivisorTerm d n

lemma roughSmallDivisorSum_prefix_bound (B D N : ℕ) :
    ‖∑ n ∈ Finset.range N, roughSmallDivisorSum B D (n + 1)‖ ≤
      (D : ℝ) * (2 + Real.log D) + 1 := by
  unfold roughSmallDivisorSum
  rw [Finset.sum_comm]
  have hb :
      ‖∑ d ∈ Finset.range (D + 1) with B < d.minFac,
        ∑ n ∈ Finset.range N, orientedDivisorTerm d (n + 1)‖ ≤
      (D : ℝ) * (harmonic D : ℝ) + D + 1 := by
    calc
      _ ≤ ∑ d ∈ Finset.range (D + 1) with B < d.minFac,
          ‖∑ n ∈ Finset.range N, orientedDivisorTerm d (n + 1)‖ := norm_sum_le _ _
      _ ≤ ∑ d ∈ Finset.range (D + 1) with B < d.minFac, ((d.divisors.card : ℝ) + 1) :=
        Finset.sum_le_sum fun d _ => orientedDivisorTerm_sparse_shifted_bound d N
      _ ≤ ∑ d ∈ Finset.range (D + 1), ((d.divisors.card : ℝ) + 1) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => by positivity)
      _ = (∑ d ∈ Finset.range (D + 1), (d.divisors.card : ℝ)) + D + 1 := by
        simp [Finset.sum_add_distrib]; ring
      _ ≤ _ := by linarith [sum_divisors_card_le_harmonic D]
  have h := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log D) (Nat.cast_nonneg (α := ℝ) D)
  nlinarith

lemma roughSmallDivisorSum_nearLinear_bound (B N : ℕ) :
    ‖(∑ n ∈ Finset.range N, roughSmallDivisorSum B (nearLinearCutoff N) (n + 1)) / N‖ ≤
      2 / (1 + Real.log (N + 1)) + 1 / N := by
  have hlog : 0 ≤ Real.log (N + 1 : ℝ) := Real.log_nonneg
    (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
  have ha : 0 < 1 + Real.log (N + 1 : ℝ) := by positivity
  by_cases hN : N = 0
  · subst N
    simp
  have hDlog : Real.log (nearLinearCutoff N) ≤ Real.log (N + 1 : ℝ) := by
    by_cases hD : nearLinearCutoff N = 0
    · simpa [hD] using hlog
    · apply Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hD)
      have := nearLinearCutoff_le_self N
      exact_mod_cast (show nearLinearCutoff N ≤ N + 1 by omega)
  have hb :
      ‖∑ n ∈ Finset.range N, roughSmallDivisorSum B (nearLinearCutoff N) (n + 1)‖ ≤
      2 * (N : ℝ) / (1 + Real.log (N + 1)) + 1 := by
    calc
      _ ≤ (nearLinearCutoff N : ℝ) * (2 + Real.log (nearLinearCutoff N)) + 1 :=
        roughSmallDivisorSum_prefix_bound _ _ _
      _ ≤ (nearLinearCutoff N : ℝ) * (2 + Real.log (N + 1)) + 1 := by gcongr
      _ ≤ (N : ℝ) / (1 + Real.log (N + 1)) ^ 2 * (2 + Real.log (N + 1)) + 1 := by
        gcongr
        exact nearLinearCutoff_le N
      _ ≤ (N : ℝ) / (1 + Real.log (N + 1)) ^ 2 * (2 * (1 + Real.log (N + 1))) + 1 := by
        gcongr
        linarith
      _ = _ := by field_simp
  rw [norm_div, Real.norm_natCast]
  calc
    _ ≤ (2 * (N : ℝ) / (1 + Real.log (N + 1)) + 1) / N :=
      div_le_div_of_nonneg_right hb (Nat.cast_nonneg N)
    _ = _ := by
      have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN
      field_simp

open Filter in
/-- The small-divisor estimate is uniform in the roughness cutoff. -/
theorem roughSmallDivisorSum_nearLinear_tendsto (B : ℕ → ℕ) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N,
      roughSmallDivisorSum (B N) (nearLinearCutoff N) (n + 1)) / N) atTop (nhds 0) := by
  have harg : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun N => by linarith) tendsto_natCast_atTop_atTop
  have hlog := Real.tendsto_log_atTop.comp harg
  have ha : Tendsto (fun N : ℕ => 1 + Real.log (N + 1)) atTop atTop :=
    tendsto_atTop_mono (fun N => by dsimp only [Function.comp_apply]; linarith) hlog
  have hi := tendsto_inv_atTop_zero.comp ha
  apply squeeze_zero_norm (fun N => roughSmallDivisorSum_nearLinear_bound (B N) N)
  simpa only [div_eq_mul_inv, mul_zero, add_zero, one_mul] using
    (hi.const_mul 2).add tendsto_one_div_atTop_nhds_zero_nat

lemma roughSmallDivisorSum_eq (B D n : ℕ) (hn : 0 < n) :
    roughSmallDivisorSum B D n =
      ∑ d ∈ (n * (n + 1)).divisors with d ≤ D ∧ B < d.minFac, orientedDivisorTerm d n := by
  classical
  have hs : ((Finset.range (D + 1)).filter (fun d => B < d.minFac)).filter
      (fun d => d ∣ n * (n + 1)) =
      (n * (n + 1)).divisors.filter (fun d => d ≤ D ∧ B < d.minFac) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hD, hB⟩, hd⟩
      exact ⟨⟨hd, Nat.mul_ne_zero hn.ne' (by omega)⟩, by omega, hB⟩
    · rintro ⟨⟨hd, _⟩, hD, hB⟩
      exact ⟨⟨by omega, hB⟩, hd⟩
  calc
    _ = ∑ d ∈ Finset.range (D + 1) with B < d.minFac,
        if d ∣ n * (n + 1) then orientedDivisorTerm d n else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      by_cases h : d ∣ n * (n + 1) <;> simp [orientedDivisorTerm, h]
    _ = _ := by rw [← Finset.sum_filter, hs]

lemma rough_small_add_tail_add_low (B D n : ℕ) (hn : 0 < n) :
    roughSmallDivisorSum B D n + roughLargeDivisorTail B D n + lowLeastDivisorGroup B n =
      -factorSign n := by
  rw [roughSmallDivisorSum_eq B D n hn, roughLargeDivisorTail, lowLeastDivisorGroup]
  simp_rw [Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  calc
    _ = ∑ d ∈ (n * (n + 1)).divisors, orientedDivisorTerm d n := by
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hD : d ≤ D <;> by_cases hB : d.minFac ≤ B <;>
        simp [hD, hB, Nat.lt_of_not_ge, not_lt.mpr]
    _ = _ := sum_orientedDivisorTerm n hn

open Filter in
/-- Both logarithmically small least factors and nearly linearly small divisors
can be removed. Cancellation of the remaining rough tail is not asserted. -/
theorem density_iff_rough_large_tail :
    {n | Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac n}.HasDensity (1 / 2) ↔
      Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N,
        roughLargeDivisorTail (roughCutoff N) (nearLinearCutoff N) (n + 1)) / N)
        atTop (nhds 0) := by
  rw [density_iff_shifted_sign_average]
  have herr := (roughSmallDivisorSum_nearLinear_tendsto roughCutoff).add
    growing_lowLeastDivisorGroup_shifted_average_zero
  simp only [add_zero] at herr
  have he (N : ℕ) :
      (∑ n ∈ Finset.range N, roughSmallDivisorSum (roughCutoff N) (nearLinearCutoff N) (n + 1)) / N +
      (∑ n ∈ Finset.range N, lowLeastDivisorGroup (roughCutoff N) (n + 1)) / N +
      (∑ n ∈ Finset.range N, roughLargeDivisorTail (roughCutoff N) (nearLinearCutoff N) (n + 1)) / N =
        -((∑ n ∈ Finset.range N, factorSign (n + 1)) / N) := by
    rw [← add_div, ← add_div, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    have ht (n : ℕ) :
        roughSmallDivisorSum (roughCutoff N) (nearLinearCutoff N) (n + 1) +
        lowLeastDivisorGroup (roughCutoff N) (n + 1) +
        roughLargeDivisorTail (roughCutoff N) (nearLinearCutoff N) (n + 1) = -factorSign (n + 1) := by
      linarith [rough_small_add_tail_add_low (roughCutoff N) (nearLinearCutoff N) (n + 1) (by omega)]
    simp_rw [ht, Finset.sum_neg_distrib, neg_div]
  constructor
  · intro h
    have ht := h.neg.sub herr
    simp only [neg_zero, sub_zero] at ht
    apply ht.congr
    intro N
    linarith [he N]
  · intro h
    have ht := (herr.add h).neg
    simp only [add_zero, neg_zero] at ht
    apply ht.congr
    intro N
    linarith [he N]


noncomputable def roughMobiusTail (B D n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, if D < d ∧ B < d.minFac then signedMobius d else 0

noncomputable def roughMixedDivisorTail (B D n : ℕ) : ℝ :=
  ∑ d ∈ (n * (n + 1)).divisors with D < d ∧ B < d.minFac, mixedOrientedDivisorTerm d n

lemma roughMobiusTail_norm_le (B D n : ℕ) : ‖roughMobiusTail B D n‖ ≤ n.divisors.card := by
  unfold roughMobiusTail
  calc
    _ ≤ ∑ d ∈ n.divisors, ‖if D < d ∧ B < d.minFac then signedMobius d else 0‖ := norm_sum_le _ _
    _ ≤ ∑ _d ∈ n.divisors, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      split_ifs
      · exact signedMobius_norm_le_one d
      · simp
    _ = _ := by simp

lemma roughMobiusTail_one (B D : ℕ) : roughMobiusTail B D 1 = 0 := by
  simp [roughMobiusTail, signedMobius]

lemma roughLargeDivisorTail_decompose (B D n : ℕ) (hn : 0 < n) :
    roughLargeDivisorTail B D n =
      roughMixedDivisorTail B D n + roughMobiusTail B D (n + 1) - roughMobiusTail B D n := by
  classical
  have hm : n * (n + 1) ≠ 0 := Nat.mul_ne_zero hn.ne' (by omega)
  have hterm (d : ℕ) : (if D < d ∧ B < d.minFac then orientedDivisorTerm d n else 0) =
      (if D < d ∧ B < d.minFac then mixedOrientedDivisorTerm d n else 0) +
      (if d ∣ n + 1 then (if D < d ∧ B < d.minFac then signedMobius d else 0) else 0) -
      (if d ∣ n then (if D < d ∧ B < d.minFac then signedMobius d else 0) else 0) := by
    rw [orientedDivisorTerm_decompose]
    by_cases hD : D < d ∧ B < d.minFac <;> by_cases h₁ : d ∣ n <;> by_cases h₂ : d ∣ n + 1 <;>
      simp [hD, h₁, h₂] <;> ring
  unfold roughLargeDivisorTail roughMixedDivisorTail
  rw [Finset.sum_filter, Finset.sum_filter]
  simp_rw [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [sum_divisors_restrict (n + 1) (n * (n + 1)) (by omega) hm (Nat.dvd_mul_left _ _),
    sum_divisors_restrict n (n * (n + 1)) hn.ne' hm (Nat.dvd_mul_right _ _)]
  rfl

lemma rough_one_sided_prefix (B D N : ℕ) :
    (∑ n ∈ Finset.range N,
      (roughLargeDivisorTail B D (n + 1) - roughMixedDivisorTail B D (n + 1))) =
      roughMobiusTail B D (N + 1) := by
  have he (n : ℕ) : roughLargeDivisorTail B D (n + 1) - roughMixedDivisorTail B D (n + 1) =
      roughMobiusTail B D (n + 1 + 1) - roughMobiusTail B D (n + 1) := by
    rw [roughLargeDivisorTail_decompose B D (n + 1) (by omega)]
    ring
  simp_rw [he]
  have h := Finset.sum_range_sub (fun n => roughMobiusTail B D (n + 1)) N
  simpa only [zero_add, roughMobiusTail_one, sub_zero] using h

lemma rough_one_sided_prefix_bound (B D N : ℕ) :
    ‖∑ n ∈ Finset.range N,
      (roughLargeDivisorTail B D (n + 1) - roughMixedDivisorTail B D (n + 1))‖ ≤
      2 * (N.sqrt : ℝ) + 4 := by
  rw [rough_one_sided_prefix]
  apply (roughMobiusTail_norm_le B D (N + 1)).trans
  have hc := divisors_card_le_two_sqrt_add_two (N + 1) (by omega)
  have hs := Nat.sqrt_succ_le_succ_sqrt N
  change (N + 1).sqrt ≤ N.sqrt + 1 at hs
  exact_mod_cast (show (N + 1).divisors.card ≤ 2 * N.sqrt + 4 by omega)

open Filter in
lemma rough_one_sided_average_tendsto_zero (B D : ℕ → ℕ) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, roughLargeDivisorTail (B N) (D N) (n + 1)) / N -
      (∑ n ∈ Finset.range N, roughMixedDivisorTail (B N) (D N) (n + 1)) / N)
      atTop (nhds 0) := by
  have hsqrt (N : ℕ) : (N.sqrt : ℝ) ≤ Real.sqrt N := by
    apply Real.le_sqrt_of_sq_le
    exact_mod_cast Nat.sqrt_le' N
  have hb (N : ℕ) :
      ‖(∑ n ∈ Finset.range N, roughLargeDivisorTail (B N) (D N) (n + 1)) / N -
        (∑ n ∈ Finset.range N, roughMixedDivisorTail (B N) (D N) (n + 1)) / N‖ ≤
      2 * (Real.sqrt N)⁻¹ + 4 / N := by
    rw [← sub_div, ← Finset.sum_sub_distrib, norm_div, Real.norm_natCast]
    calc
      _ ≤ (2 * (N.sqrt : ℝ) + 4) / N := div_le_div_of_nonneg_right
        (rough_one_sided_prefix_bound (B N) (D N) N) (Nat.cast_nonneg N)
      _ ≤ (2 * Real.sqrt N + 4) / N := by gcongr; exact hsqrt N
      _ = _ := by rw [add_div, mul_div_assoc, Real.sqrt_div_self]
  have hi : Tendsto (fun N : ℕ => (Real.sqrt N)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  apply squeeze_zero_norm hb
  simpa using (hi.const_mul 2).add (tendsto_const_div_atTop_nhds_zero_nat (4 : ℝ))

open Filter in
/-- An exact reduction to large, genuinely mixed divisors with a growing
least-prime-factor cutoff. The tail limit remains to be established. -/
theorem density_iff_growing_rough_mixed_tail :
    {n | Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac n}.HasDensity (1 / 2) ↔
      Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N,
        roughMixedDivisorTail (roughCutoff N) (nearLinearCutoff N) (n + 1)) / N)
        atTop (nhds 0) := by
  rw [density_iff_rough_large_tail]
  have he := rough_one_sided_average_tendsto_zero roughCutoff nearLinearCutoff
  constructor
  · intro h
    have ht := h.sub he
    simp only [sub_zero] at ht
    apply ht.congr
    intro N
    ring
  · intro h
    simpa only [sub_add_cancel, add_zero] using he.add h

#print axioms growing_lowLeastDivisorGroup_shifted_average_zero
#print axioms density_iff_growing_rough_mixed_tail
end Erdos371
