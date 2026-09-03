import Submission.RoughCofactors

/-! Truncating both coordinates of the rough bilinear sum, with the
intersection error retained explicitly. No cancellation in the remaining
rectangle is asserted. -/

namespace Erdos371

lemma roughBilinearWeight_norm_le (B D a b : ℕ) : ‖roughBilinearWeight B D a b‖ ≤ 1 := by
  have hμ (n : ℕ) : ‖(ArithmeticFunction.moebius n : ℝ)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, ← Int.cast_abs]
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
  have hs : ‖bilinearSign a b‖ ≤ 1 := by
    unfold bilinearSign
    split_ifs <;> norm_num
  unfold roughBilinearWeight
  split_ifs
  · simp only [norm_mul]
    calc
      _ ≤ (1 : ℝ) * 1 * 1 :=
        mul_le_mul (mul_le_mul (hμ a) (hμ b) (norm_nonneg _) (by norm_num)) hs
          (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  · simp

lemma roughBilinearWeight_bad_column (B D a b : ℕ) (h : ¬(1 < b ∧ B < b.minFac)) :
    roughBilinearWeight B D a b = 0 := by
  rw [roughBilinearWeight_swap B D b a, roughBilinearWeight_bad_row B D b a h, neg_zero]

lemma roughBilinearWeight_rectangle_norm_le (B D : ℕ) (s t : Finset ℕ) :
    ‖∑ a ∈ s, ∑ b ∈ t, roughBilinearWeight B D a b‖ ≤
      ((s.filter fun a => 1 < a ∧ B < a.minFac).card : ℝ) *
        ((t.filter fun b => 1 < b ∧ B < b.minFac).card : ℝ) := by
  classical
  calc
    _ ≤ ∑ a ∈ s, ∑ b ∈ t, ‖roughBilinearWeight B D a b‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => norm_sum_le _ _)
    _ ≤ ∑ a ∈ s, ∑ b ∈ t,
        (if 1 < a ∧ B < a.minFac then (1 : ℝ) else 0) *
        (if 1 < b ∧ B < b.minFac then (1 : ℝ) else 0) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      by_cases h₁ : 1 < a ∧ B < a.minFac
      · by_cases h₂ : 1 < b ∧ B < b.minFac
        · simpa [h₁, h₂] using roughBilinearWeight_norm_le B D a b
        · simp [h₂, roughBilinearWeight_bad_column B D a b h₂]
      · simp [h₁, roughBilinearWeight_bad_row B D a b h₁]
    _ = _ := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
      simp

lemma large_divisor_card_le (K N m : ℕ) (hm : m ≤ N + 1) :
    (m.divisors.filter fun a => N < K * a).card ≤ K + 1 := by
  classical
  have he : K + 1 = (Finset.range (K + 1)).card := by simp
  rw [he]
  apply Finset.card_le_card_of_injOn (fun a => m / a)
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_filter] at ha
    obtain ⟨ha, hKa⟩ := ha
    have ha' := (Nat.mem_divisors.mp ha).1
    have ha0 := Nat.pos_of_mem_divisors ha
    have hprod := Nat.mul_div_cancel' ha'
    apply Finset.mem_range.mpr
    have hma : m ≤ K * a := by omega
    nlinarith
  · intro a ha b hb he
    simp only [Finset.mem_coe, Finset.mem_filter] at ha hb
    obtain ⟨ha, _⟩ := ha
    obtain ⟨hb, _⟩ := hb
    have hpa := Nat.mul_div_cancel' (Nat.mem_divisors.mp ha).1
    have hpb := Nat.mul_div_cancel' (Nat.mem_divisors.mp hb).1
    have hm0 : 0 < m := Nat.pos_of_ne_zero (Nat.mem_divisors.mp ha).2
    have hq : 0 < m / a := by
      have ha0 := Nat.pos_of_mem_divisors ha
      nlinarith
    dsimp only at he
    rw [← he] at hpb
    nlinarith

noncomputable def largeBilinearColumns (B D K N n : ℕ) : ℝ :=
  ∑ a ∈ n.divisors, ∑ b ∈ (n + 1).divisors with N < K * b,
    roughBilinearWeight B D a b

noncomputable def largeBilinearIntersection (B D K N n : ℕ) : ℝ :=
  ∑ a ∈ n.divisors with N < K * a,
    ∑ b ∈ (n + 1).divisors with N < K * b, roughBilinearWeight B D a b

noncomputable def balancedBilinearSum (B D K N n : ℕ) : ℝ :=
  ∑ a ∈ n.divisors with K * a ≤ N,
    ∑ b ∈ (n + 1).divisors with K * b ≤ N, roughBilinearWeight B D a b

lemma balanced_bilinear_decomposition (B D K N n : ℕ) (hn : 0 < n) :
    roughMixedDivisorTail B D n - balancedBilinearSum B D K N n =
      largeBilinearRows B D K N n + largeBilinearColumns B D K N n -
        largeBilinearIntersection B D K N n := by
  rw [roughMixedDivisorTail_bilinear B D n hn]
  unfold balancedBilinearSum largeBilinearRows largeBilinearColumns largeBilinearIntersection
  simp only [Finset.sum_filter]
  have hsum (a : ℕ) (h : Prop) [Decidable h] :
      (if h then ∑ b ∈ (n + 1).divisors, roughBilinearWeight B D a b else 0) =
        ∑ b ∈ (n + 1).divisors, if h then roughBilinearWeight B D a b else 0 := by
    split_ifs <;> simp
  have hsum' (a : ℕ) (h : Prop) [Decidable h] :
      (if h then ∑ b ∈ (n + 1).divisors,
          if N < K * b then roughBilinearWeight B D a b else 0 else 0) =
        ∑ b ∈ (n + 1).divisors,
          if h then (if N < K * b then roughBilinearWeight B D a b else 0) else 0 := by
    split_ifs <;> simp
  have hsum'' (a : ℕ) (h : Prop) [Decidable h] :
      (if h then ∑ b ∈ (n + 1).divisors,
          if K * b ≤ N then roughBilinearWeight B D a b else 0 else 0) =
        ∑ b ∈ (n + 1).divisors,
          if h then (if K * b ≤ N then roughBilinearWeight B D a b else 0) else 0 := by
    split_ifs <;> simp
  simp_rw [hsum, hsum', hsum'']
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases h₁ : K * a ≤ N <;> by_cases h₂ : K * b ≤ N <;>
    simp [h₁, h₂, show (N < K * a) ↔ ¬K * a ≤ N from not_le.symm,
      show (N < K * b) ↔ ¬K * b ≤ N from not_le.symm]

lemma largeBilinearColumns_norm_le (B D K N n : ℕ) (hD : D ≤ N) (hK : K ≤ B + 1) :
    ‖largeBilinearColumns B D K N n‖ ≤
      (((n + 1).divisors.filter fun b => N < K * b ∧ 1 < b ∧ B < b.minFac).card : ℝ) := by
  unfold largeBilinearColumns
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ b ∈ (n + 1).divisors with N < K * b,
        ‖∑ a ∈ n.divisors, roughBilinearWeight B D a b‖ := norm_sum_le _ _
    _ ≤ ∑ b ∈ (n + 1).divisors with N < K * b,
        if 1 < b ∧ B < b.minFac then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro b hb
      by_cases h : 1 < b ∧ B < b.minFac
      · rw [if_pos h]
        apply roughBilinearWeight_column_norm_le
        have hNb := (Finset.mem_filter.mp hb).2
        have hmul := Nat.mul_le_mul_right b hK
        nlinarith
      · simp only [if_neg h, roughBilinearWeight_bad_column B D _ b h,
          Finset.sum_const_zero, norm_zero, le_refl]
    _ = _ := by simp [Finset.filter_filter]

lemma largeBilinearIntersection_norm_le (B D K N n : ℕ) (hn : n ≤ N) :
    ‖largeBilinearIntersection B D K N n‖ ≤
      (((n.divisors.filter fun a => N < K * a ∧ 1 < a ∧ B < a.minFac).card : ℝ)) * (K + 1) := by
  have hc : (((n + 1).divisors.filter fun b => N < K * b).filter
      fun b => 1 < b ∧ B < b.minFac).card ≤ K + 1 :=
    (Finset.card_filter_le _ _).trans (large_divisor_card_le K N (n + 1) (by omega))
  apply (roughBilinearWeight_rectangle_norm_le B D _ _).trans
  simp only [Finset.filter_filter] at hc ⊢
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hc) (by positivity)

lemma roughNumberCount_mono_right (B : ℕ) {N M : ℕ} (hNM : N ≤ M) :
    roughNumberCount B N ≤ roughNumberCount B M := by
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono hNM))

lemma shifted_fixed_cofactor_count_bound (B K N : ℕ) :
    (∑ n ∈ Finset.range N, ((n + 2).divisors.filter fun a =>
      N < K * a ∧ 1 < a ∧ B < a.minFac).card) ≤ (K + 1) * roughNumberCount B (N + 2) := by
  calc
    _ ≤ ∑ n ∈ Finset.range N, ((n + 2).divisors.filter fun a =>
        N + 1 < (K + 1) * a ∧ 1 < a ∧ B < a.minFac).card := by
      apply Finset.sum_le_sum
      intro n hn
      apply Finset.card_le_card
      intro a ha
      obtain ⟨ha, hNa, ha1, hBa⟩ := Finset.mem_filter.mp ha
      exact Finset.mem_filter.mpr ⟨ha, by nlinarith, ha1, hBa⟩
    _ ≤ ∑ n ∈ Finset.range (N + 1), ((n + 1).divisors.filter fun a =>
        N + 1 < (K + 1) * a ∧ 1 < a ∧ B < a.minFac).card := by
      rw [Finset.sum_range_succ']
      simp only [Nat.add_assoc, Nat.reduceAdd]
      omega
    _ ≤ _ := fixed_cofactor_count_bound B (K + 1) (N + 1)

lemma largeBilinearColumns_prefix_bound (B D K N : ℕ) (hD : D ≤ N) (hK : K ≤ B + 1) :
    ‖∑ n ∈ Finset.range N, largeBilinearColumns B D K N (n + 1)‖ ≤
      (K + 1 : ℝ) * roughNumberCount B (N + 2) := by
  calc
    _ ≤ ∑ n ∈ Finset.range N, ‖largeBilinearColumns B D K N (n + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range N, (((n + 2).divisors.filter fun b =>
        N < K * b ∧ 1 < b ∧ B < b.minFac).card : ℝ) := by
      exact Finset.sum_le_sum fun n _ => largeBilinearColumns_norm_le B D K N (n + 1) hD hK
    _ ≤ _ := by exact_mod_cast shifted_fixed_cofactor_count_bound B K N

lemma largeBilinearIntersection_prefix_bound (B D K N : ℕ) :
    ‖∑ n ∈ Finset.range N, largeBilinearIntersection B D K N (n + 1)‖ ≤
      (K : ℝ) * roughNumberCount B (N + 1) * (K + 1) := by
  calc
    _ ≤ ∑ n ∈ Finset.range N, ‖largeBilinearIntersection B D K N (n + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range N, (((n + 1).divisors.filter fun a =>
        N < K * a ∧ 1 < a ∧ B < a.minFac).card : ℝ) * (K + 1) := by
      apply Finset.sum_le_sum
      intro n hn
      exact largeBilinearIntersection_norm_le B D K N (n + 1) (Finset.mem_range.mp hn)
    _ ≤ _ := by
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast fixed_cofactor_count_bound B K N)
        (by positivity)

/-- Unlike the complete-row bound, this estimate accounts for truncation in
both coordinates. The intersection is paid for separately. -/
theorem balancedBilinearSum_error_bound (B D K N : ℕ) (hD : D ≤ N) (hK : K ≤ B + 1) :
    ‖(∑ n ∈ Finset.range N, roughMixedDivisorTail B D (n + 1)) -
        ∑ n ∈ Finset.range N, balancedBilinearSum B D K N (n + 1)‖ ≤
      3 * (K + 1 : ℝ)^2 * roughNumberCount B (N + 2) := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [balanced_bilinear_decomposition B D K N _ (Nat.zero_lt_succ _)]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hR := largeBilinearRows_prefix_bound B D K N hD hK
  have hC := largeBilinearColumns_prefix_bound B D K N hD hK
  have hI := largeBilinearIntersection_prefix_bound B D K N
  have hc : (roughNumberCount B (N + 1) : ℝ) ≤ roughNumberCount B (N + 2) := by
    exact_mod_cast roughNumberCount_mono_right B (show N + 1 ≤ N + 2 by omega)
  calc
    _ ≤ (‖∑ n ∈ Finset.range N, largeBilinearRows B D K N (n + 1)‖ +
        ‖∑ n ∈ Finset.range N, largeBilinearColumns B D K N (n + 1)‖) +
        ‖∑ n ∈ Finset.range N, largeBilinearIntersection B D K N (n + 1)‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ((K : ℝ) * roughNumberCount B (N + 1) +
        (K + 1 : ℝ) * roughNumberCount B (N + 2)) +
        (K : ℝ) * roughNumberCount B (N + 1) * (K + 1) :=
      add_le_add (add_le_add hR hC) hI
    _ ≤ ((K : ℝ) * roughNumberCount B (N + 2) +
        (K + 1 : ℝ) * roughNumberCount B (N + 2)) +
        (K : ℝ) * roughNumberCount B (N + 2) * (K + 1) := by
      have h := mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg K)
      exact add_le_add (add_le_add h le_rfl) (mul_le_mul_of_nonneg_right h (by positivity))
    _ ≤ _ := by
      have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
      have hR0 : (0 : ℝ) ≤ roughNumberCount B (N + 2) := Nat.cast_nonneg _
      have hcoeff : (K : ℝ) + (K + 1) + K * (K + 1) ≤ 3 * (K + 1)^2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hcoeff hR0]

open Filter in
lemma growing_roughNumberCount_succsucc_tendsto (B : ℕ → ℕ) (hB : Tendsto B atTop atTop) :
    Tendsto (fun N : ℕ => (roughNumberCount (B N) (N + 2) : ℝ) / N) atTop (nhds 0) := by
  have ht := (growing_roughNumberCount_tendsto B hB).add
    (tendsto_one_div_atTop_nhds_zero_nat.const_mul (2 : ℝ))
  simp only [mul_zero, add_zero] at ht
  apply squeeze_zero (fun _ => by positivity) _ ht
  intro N
  have h₁ := roughNumberCount_succ_le (B N) N
  have h₂ := roughNumberCount_succ_le (B N) (N + 1)
  have hc : roughNumberCount (B N) (N + 2) ≤ roughNumberCount (B N) N + 2 := by
    simp only [Nat.add_assoc, Nat.reduceAdd] at h₂
    omega
  calc
    _ ≤ ((roughNumberCount (B N) N : ℝ) + 2) / N :=
      div_le_div_of_nonneg_right (by exact_mod_cast hc) (Nat.cast_nonneg N)
    _ = _ := by ring

open Filter in
/-- A cutoff may grow slowly enough that a prescribed vanishing nonnegative
error still vanishes after multiplication by the square of that cutoff. -/
lemma exists_slow_square_cutoff (B : ℕ → ℕ) (f : ℕ → ℝ)
    (hB : Tendsto B atTop atTop) (hf : Tendsto f atTop (nhds 0)) (hf0 : ∀ N, 0 ≤ f N) :
    ∃ K : ℕ → ℕ, Tendsto K atTop atTop ∧
      (∀ᶠ N in atTop, K N ≤ B N + 1) ∧
      Tendsto (fun N => (K N + 1 : ℝ)^2 * f N) atTop (nhds 0) := by
  classical
  let P (N k : ℕ) : Prop := k ≤ B N + 1 ∧ (k + 1 : ℝ)^2 * f N ≤ 1 / (k + 1 : ℝ)
  let K (N : ℕ) := Nat.findGreatest (P N) N
  have hP (k : ℕ) : ∀ᶠ N in atTop, P N k := by
    have ht := hf.const_mul ((k + 1 : ℝ)^2)
    simp only [mul_zero] at ht
    filter_upwards [hB.eventually_ge_atTop k,
      (tendsto_order.mp ht).2 (1 / (k + 1 : ℝ)) (by positivity)] with N hBN hN
    exact ⟨by omega, hN.le⟩
  have hKatTop : Tendsto K atTop atTop := by
    apply tendsto_atTop.mpr
    intro k
    filter_upwards [eventually_ge_atTop k, hP k] with N hNk hPk
    exact Nat.le_findGreatest hNk hPk
  have hPK : ∀ᶠ N in atTop, P N (K N) := by
    filter_upwards [hP 0] with N hN
    exact Nat.findGreatest_spec (Nat.zero_le N) hN
  refine ⟨K, hKatTop, hPK.mono fun N hN => hN.1, ?_⟩
  have hrecip : Tendsto (fun N => 1 / (K N + 1 : ℝ)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hKatTop
  apply tendsto_order.mpr
  constructor
  · intro ε hε
    exact Eventually.of_forall fun N => hε.trans_le (mul_nonneg (sq_nonneg _) (hf0 N))
  · intro ε hε
    filter_upwards [hPK, (tendsto_order.mp hrecip).2 ε hε] with N hN hεN
    exact hN.2.trans_lt hεN

open Filter in
/-- There is an unbounded cofactor cutoff for which both discarded strips,
including their intersection, have zero average. This does not assert that
the bilinear sum in the remaining rectangle has zero average. -/
theorem exists_growing_balanced_cutoff :
    ∃ K : ℕ → ℕ, Tendsto K atTop atTop ∧
      Tendsto (fun N : ℕ =>
        ((∑ n ∈ Finset.range N,
          roughMixedDivisorTail (roughCutoff N) (nearLinearCutoff N) (n + 1)) -
        ∑ n ∈ Finset.range N,
          balancedBilinearSum (roughCutoff N) (nearLinearCutoff N) (K N) N (n + 1)) / N)
        atTop (nhds 0) ∧
      ({n | Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac n}.HasDensity (1 / 2) ↔
        Tendsto (fun N : ℕ =>
          (∑ n ∈ Finset.range N,
            balancedBilinearSum (roughCutoff N) (nearLinearCutoff N) (K N) N (n + 1)) / N)
          atTop (nhds 0)) := by
  obtain ⟨K, hK, hKB, hKe⟩ := exists_slow_square_cutoff roughCutoff
    (fun N => (roughNumberCount (roughCutoff N) (N + 2) : ℝ) / N)
    roughCutoff_atTop (growing_roughNumberCount_succsucc_tendsto roughCutoff roughCutoff_atTop)
    (fun N => by positivity)
  have herr : Tendsto (fun N : ℕ =>
        ((∑ n ∈ Finset.range N,
          roughMixedDivisorTail (roughCutoff N) (nearLinearCutoff N) (n + 1)) -
        ∑ n ∈ Finset.range N,
          balancedBilinearSum (roughCutoff N) (nearLinearCutoff N) (K N) N (n + 1)) / N)
        atTop (nhds 0) := by
    have ht := hKe.const_mul (3 : ℝ)
    simp only [mul_zero] at ht
    apply squeeze_zero_norm' _ ht
    filter_upwards [hKB] with N hKN
    rw [norm_div, Real.norm_natCast]
    calc
      _ ≤ (3 * (K N + 1 : ℝ)^2 * roughNumberCount (roughCutoff N) (N + 2)) / N :=
        div_le_div_of_nonneg_right (balancedBilinearSum_error_bound _ _ _ _
          (nearLinearCutoff_le_self N) hKN) (Nat.cast_nonneg N)
      _ = _ := by ring
  refine ⟨K, hK, herr, ?_⟩
  rw [density_iff_growing_rough_mixed_tail]
  constructor
  · intro h
    have ht := h.sub herr
    simp only [sub_zero] at ht
    apply ht.congr
    intro N
    ring
  · intro h
    have ht := h.add herr
    simp only [add_zero] at ht
    apply ht.congr
    intro N
    ring

#print axioms balancedBilinearSum_error_bound
#print axioms exists_slow_square_cutoff
#print axioms exists_growing_balanced_cutoff
end Erdos371
