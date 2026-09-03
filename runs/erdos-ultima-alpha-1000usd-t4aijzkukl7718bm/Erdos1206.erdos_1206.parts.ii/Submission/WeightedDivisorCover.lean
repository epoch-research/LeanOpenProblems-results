import Submission.SummableDivisorCover
import Submission.Compactness

/-! A weighted sieve criterion only. No weights satisfying its global collision
hypothesis have been constructed. -/

namespace Erdos1206
open Finset Filter
open scoped Topology

noncomputable def divisorWeight (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, w d

def lowDivisorWeight (w : ℕ → ℝ) (t : ℝ) : Set ℕ :=
  {n | 0 < n ∧ divisorWeight w n < t}

lemma divisorWeight_nonneg {w : ℕ → ℝ} (hw : ∀ d, 0 ≤ w d) (n : ℕ) :
    0 ≤ divisorWeight w n := sum_nonneg fun d _ => hw d

lemma lowDivisorWeight_divisorClosed {w : ℕ → ℝ} (hw : ∀ d, 0 ≤ w d) (t : ℝ) :
    PositiveDivisorClosed (lowDivisorWeight w t) := by
  intro n hn m hmn hm
  refine ⟨hm, lt_of_le_of_lt ?_ hn.2⟩
  exact sum_le_sum_of_subset_of_nonneg
    (Nat.divisors_subset_of_dvd (Nat.ne_of_gt hn.1) hmn) (fun d _ _ => hw d)

lemma divisorWeight_sum_bound {w : ℕ → ℝ} (hw : ∀ d, 0 ≤ w d) (N : ℕ) :
    (∑ n ∈ range (N + 1), divisorWeight w n) ≤
      (N : ℝ) * ∑ d ∈ range (N + 1), w d / d := by
  classical
  have heq (n : ℕ) (hn : n ∈ range (N + 1)) :
      divisorWeight w n = ∑ d ∈ range (N + 1),
        if n ≠ 0 ∧ d ∣ n then w d else 0 := by
    have hs : n.divisors = (range (N + 1)).filter (fun d => n ≠ 0 ∧ d ∣ n) := by
      ext d
      simp only [Nat.mem_divisors, mem_filter, mem_range]
      constructor
      · rintro ⟨hd, hn0⟩
        have := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hd
        have := mem_range.mp hn
        exact ⟨by omega, hn0, hd⟩
      · rintro ⟨_, hn0, hd⟩; exact ⟨hd, hn0⟩
    simp only [divisorWeight, hs, sum_filter]
  calc
    _ = ∑ n ∈ range (N + 1), ∑ d ∈ range (N + 1),
        if n ≠ 0 ∧ d ∣ n then w d else 0 := sum_congr rfl heq
    _ = ∑ d ∈ range (N + 1), ∑ n ∈ range (N + 1),
        if n ≠ 0 ∧ d ∣ n then w d else 0 := sum_comm
    _ = ∑ d ∈ range (N + 1), (N / d : ℕ) * w d := by
      apply sum_congr rfl
      intro d hd
      rw [← sum_filter, sum_const, nsmul_eq_mul, Nat.card_multiples']
    _ ≤ ∑ d ∈ range (N + 1), (N : ℝ) / d * w d :=
      sum_le_sum fun d _ => mul_le_mul_of_nonneg_right Nat.cast_div_le (hw d)
    _ = _ := by rw [mul_sum]; apply sum_congr rfl; intros; ring

lemma lowDivisorWeight_positive_of_small_sums {w : ℕ → ℝ} {t : ℝ}
    (hw : ∀ d, 0 ≤ w d) (ht : 0 < t)
    (hs : ∀ N : ℕ, ∑ d ∈ range (N + 1), w d / d ≤ t / 2) :
    0 < (lowDivisorWeight w t).lowerDensity := by
  classical
  apply positive_lowerDensity_of_prefix_bound (δ := 1 / 2) (C := 1) (by norm_num)
  intro N
  cases N with
  | zero => simp
  | succ N =>
    let S := (range (N + 1)).filter (fun n => 0 < n)
    let G := S.filter (fun n => divisorWeight w n < t)
    let B := S.filter (fun n => ¬ divisorWeight w n < t)
    have hS : S.card = N := by
      have heq : S = Icc 1 N := by ext n; simp [S]; omega
      simp [heq, Nat.card_Icc]
    have hcard : G.card + B.card = N := by
      simpa only [G, B, ← hS] using card_filter_add_card_filter_not (s := S)
        (fun n => divisorWeight w n < t)
    have hb : (B.card : ℝ) * t ≤ (N : ℝ) * (t / 2) := by
      calc
        _ = ∑ n ∈ B, t := by simp [mul_comm]
        _ ≤ ∑ n ∈ B, divisorWeight w n := sum_le_sum fun n hn =>
          le_of_not_gt (mem_filter.mp hn).2
        _ ≤ ∑ n ∈ range (N + 1), divisorWeight w n :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _ |>.trans (filter_subset _ _))
            (fun n _ _ => divisorWeight_nonneg hw n)
        _ ≤ (N : ℝ) * ∑ d ∈ range (N + 1), w d / d := divisorWeight_sum_bound hw N
        _ ≤ (N : ℝ) * (t / 2) := mul_le_mul_of_nonneg_left (hs N) (by positivity)
    have hc : (G.card : ℝ) + B.card = N := by exact_mod_cast hcard
    have heq : lowDivisorWeight w t ∩ Set.Iio (N + 1) = (G : Set ℕ) := by
      ext n
      simp [lowDivisorWeight, G, S, and_comm, and_left_comm]
    rw [heq, Set.ncard_coe_finset]
    have : (N : ℝ) / 2 ≤ G.card := by nlinarith
    push_cast
    linarith

lemma small_weight_tail {w : ℕ → ℝ} (hw : ∀ d, 0 ≤ w d)
    (hs : Summable (fun d : ℕ => w d / d)) {t : ℝ} (ht : 0 < t) :
    ∃ M : ℕ, ∀ N : ℕ,
      ∑ d ∈ range (N + 1), (if M < d then w d else 0) / d ≤ t / 2 := by
  classical
  let f : ℕ → ℝ := fun d => w d / d
  have hf : Summable f := hs
  have hf0 (d : ℕ) : 0 ≤ f d := div_nonneg (hw d) (Nat.cast_nonneg d)
  have hev : ∀ᶠ M : ℕ in atTop,
      (∑' d, f d) - t / 2 < ∑ d ∈ range M, f d :=
    hf.hasSum.tendsto_sum_nat.eventually (eventually_gt_nhds (by linarith))
  obtain ⟨M, hM⟩ := hev.exists
  refine ⟨M, fun N => ?_⟩
  let S := (range (N + 1)).filter (fun d => M < d)
  have hdis : Disjoint (range M) S := by
    apply disjoint_left.mpr
    intro d hd hS
    have := mem_range.mp hd
    have := (mem_filter.mp hS).2
    omega
  have hb : (∑ d ∈ range M, f d) + ∑ d ∈ S, f d ≤ ∑' d, f d := by
    rw [← sum_union hdis]
    exact hf.sum_le_tsum _ (fun d _ => hf0 d)
  have heq : (∑ d ∈ range (N + 1), (if M < d then w d else 0) / d) =
      ∑ d ∈ S, f d := by
    dsimp only [S]
    rw [sum_filter]
    apply sum_congr rfl
    intro d hd
    split_ifs <;> simp [f]
  rw [heq]
  linarith

lemma lowDivisorWeight_positive {w : ℕ → ℝ} (hw : ∀ d, 0 ≤ w d)
    (h1 : w 1 = 0) (hs : Summable (fun d : ℕ => w d / d)) {t : ℝ} (ht : 0 < t) :
    0 < (lowDivisorWeight w t).lowerDensity := by
  classical
  obtain ⟨M, hM⟩ := small_weight_tail hw hs ht
  let v : ℕ → ℝ := fun d => if M < d then w d else 0
  have hv : ∀ d, 0 ≤ v d := by intro d; dsimp [v]; split_ifs; exact hw d; positivity
  have hden : 0 < (lowDivisorWeight v t).lowerDensity :=
    lowDivisorWeight_positive_of_small_sums hv ht hM
  let S := (range (M + 1)).filter (fun d => 1 < d)
  have hden' := remove_finite_divisors_preserves_positive_density
    (lowDivisorWeight_divisorClosed hv t) (fun _ hn => hn.1) hden S
    (fun d hd => (mem_filter.mp hd).2)
  have hsub : lowDivisorWeight v t ∩ {n | ∀ d ∈ S, ¬ d ∣ n} ⊆
      lowDivisorWeight w t := by
    intro n hn
    refine ⟨hn.1.1, ?_⟩
    have heq : divisorWeight w n = divisorWeight v n := by
      apply sum_congr rfl
      intro d hd
      by_cases hdM : M < d
      · simp [v, hdM]
      · have hd0 := Nat.pos_of_mem_divisors hd
        have hd1 : d = 1 := by
          by_contra hh
          exact hn.2 d (mem_filter.mpr ⟨mem_range.mpr (by omega), by omega⟩)
            (Nat.dvd_of_mem_divisors hd)
        simp [v, hd1, h1]
    rw [heq]
    exact hn.1.2
  obtain ⟨δ, hδ, C, hpre⟩ := prefix_bound_of_positive_lowerDensity hden'
  apply positive_lowerDensity_of_prefix_bound hδ (C := C)
  intro N
  have hc := Set.ncard_le_ncard (Set.inter_subset_inter_left (Set.Iio N) hsub)
  have hc' : (((lowDivisorWeight v t ∩ {n | ∀ d ∈ S, ¬ d ∣ n}) ∩ Set.Iio N).ncard : ℝ) ≤
      ((lowDivisorWeight w t ∩ Set.Iio N).ncard : ℝ) := by exact_mod_cast hc
  linarith [hpre N]

/-- A fractional divisor cover assigns enough total divisor weight to each
nontrivial collision. This definition counts a divisor once for each root it divides. -/
def IsWeightedCubeDivisorCover (w : ℕ → ℝ) : Prop :=
  ∀ a b c d : ℕ, 0 < a → 0 < b → 0 < c → 0 < d →
    a ^ 3 + b ^ 3 = c ^ 3 + d ^ 3 → a ≠ c → a ≠ d →
    1 ≤ divisorWeight w a + divisorWeight w b + divisorWeight w c + divisorWeight w d

lemma weighted_divisor_cover_suffices {w : ℕ → ℝ} (hw : ∀ d, 0 ≤ w d)
    (h1 : w 1 = 0) (hs : Summable (fun d : ℕ => w d / d))
    (hcover : IsWeightedCubeDivisorCover w) :
    ∃ A : Set ℕ, A.Infinite ∧ 0 < A.lowerDensity ∧
      IsSidon ((fun a : ℕ => a ^ 3) '' A) := by
  let A := lowDivisorWeight w (1 / 4)
  have hden : 0 < A.lowerDensity := lowDivisorWeight_positive hw h1 hs (by norm_num)
  refine ⟨A, ?_, hden, ?_⟩
  · by_contra hf
    have hz : A.lowerDensity = 0 :=
      (Nat.hasDensity_zero_of_finite (Set.not_infinite.mp hf)).liminf_eq
    linarith
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨c, hc, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨d, hd, rfl⟩ heq
    by_cases hac : a = c
    · subst c
      exact Or.inl ⟨rfl, Nat.add_left_cancel heq⟩
    by_cases had : a = d
    · subst d
      exact Or.inr ⟨rfl, by omega⟩
    have hh := hcover a b c d ha.1 hb.1 hc.1 hd.1 heq hac had
    have ha' : divisorWeight w a < 1 / 4 := ha.2
    have hb' : divisorWeight w b < 1 / 4 := hb.2
    have hc' : divisorWeight w c < 1 / 4 := hc.2
    have hd' : divisorWeight w d < 1 / 4 := hd.2
    linarith

/-- A bounded finite-prefix version of the fractional covering condition. -/
def FiniteWeightedCubeDivisorCover (N : ℕ) (w : ℕ → ℝ) : Prop :=
  ∀ a b c d : ℕ, a ∈ Set.Icc 1 N → b ∈ Set.Icc 1 N →
    c ∈ Set.Icc 1 N → d ∈ Set.Icc 1 N →
    a ^ 3 + b ^ 3 = c ^ 3 + d ^ 3 → a ≠ c → a ≠ d →
    1 ≤ divisorWeight w a + divisorWeight w b + divisorWeight w c + divisorWeight w d

/-- A single uniform bound on finite fractional-cover costs yields a global
summable fractional cover. Existence of the uniform bound remains unproved. -/
lemma weighted_cover_of_uniform_finite_weights (C : ℝ)
    (h : ∀ N : ℕ, ∃ w : ℕ → ℝ,
      (∀ d, w d ∈ Set.Icc 0 1) ∧ w 1 = 0 ∧
      (∑ d ∈ range (N + 1), w d / d) ≤ C ∧ FiniteWeightedCubeDivisorCover N w) :
    ∃ w : ℕ → ℝ, (∀ d, 0 ≤ w d) ∧ w 1 = 0 ∧
      Summable (fun d : ℕ => w d / d) ∧ IsWeightedCubeDivisorCover w := by
  classical
  choose W hW h1 hsum hcover using h
  let x : ℕ → ℕ → Set.Icc (0 : ℝ) 1 := fun N d => ⟨W N d, hW N d⟩
  obtain ⟨f, φ, hφ, hf⟩ := SeqCompactSpace.tendsto_subseq x
  let w : ℕ → ℝ := fun d => (f d).val
  have hw (d : ℕ) : 0 ≤ w d := (f d).property.1
  have hv (d : ℕ) : Tendsto (fun j => W (φ j) d) atTop (𝓝 (w d)) := by
    exact continuous_subtype_val.tendsto (f d) |>.comp ((tendsto_pi_nhds.mp hf) d)
  have hsumt (S : Finset ℕ) :
      Tendsto (fun j => ∑ d ∈ S, W (φ j) d / d) atTop (𝓝 (∑ d ∈ S, w d / d)) :=
    tendsto_finset_sum S (fun d _ => (hv d).div_const _)
  have hdivt (n : ℕ) : Tendsto (fun j => divisorWeight (W (φ j)) n) atTop
      (𝓝 (divisorWeight w n)) := tendsto_finset_sum n.divisors (fun d _ => hv d)
  refine ⟨w, hw, ?_, ?_, ?_⟩
  · have hh := hv 1
    simp_rw [h1] at hh
    exact tendsto_nhds_unique hh tendsto_const_nhds
  · apply summable_of_sum_range_le (c := C)
    · intro d; exact div_nonneg (hw d) (Nat.cast_nonneg d)
    · intro M
      apply le_of_tendsto (hsumt (range M))
      filter_upwards [hφ.tendsto_atTop.eventually (eventually_ge_atTop M)] with j hj
      calc
        _ ≤ ∑ d ∈ range (φ j + 1), W (φ j) d / d :=
          sum_le_sum_of_subset_of_nonneg (range_mono (by omega))
            (fun d _ _ => div_nonneg (hW (φ j) d).1 (Nat.cast_nonneg d))
        _ ≤ C := hsum (φ j)
  · intro a b c d ha hb hc hd heq hac had
    apply ge_of_tendsto (((hdivt a).add (hdivt b)).add (hdivt c) |>.add (hdivt d))
    filter_upwards [hφ.tendsto_atTop.eventually
      (eventually_ge_atTop (a + b + c + d))] with j hj
    exact hcover (φ j) a b c d ⟨ha, by omega⟩ ⟨hb, by omega⟩
      ⟨hc, by omega⟩ ⟨hd, by omega⟩ heq hac had

lemma uniform_finite_weighted_covers_suffice (C : ℝ)
    (h : ∀ N : ℕ, ∃ w : ℕ → ℝ,
      (∀ d, w d ∈ Set.Icc 0 1) ∧ w 1 = 0 ∧
      (∑ d ∈ range (N + 1), w d / d) ≤ C ∧ FiniteWeightedCubeDivisorCover N w) :
    ∃ A : Set ℕ, A.Infinite ∧ 0 < A.lowerDensity ∧
      IsSidon ((fun a : ℕ => a ^ 3) '' A) := by
  obtain ⟨w, hw, h1, hs, hc⟩ := weighted_cover_of_uniform_finite_weights C h
  exact weighted_divisor_cover_suffices hw h1 hs hc

#print axioms lowDivisorWeight_positive
#print axioms weighted_divisor_cover_suffices
#print axioms uniform_finite_weighted_covers_suffice
end Erdos1206
