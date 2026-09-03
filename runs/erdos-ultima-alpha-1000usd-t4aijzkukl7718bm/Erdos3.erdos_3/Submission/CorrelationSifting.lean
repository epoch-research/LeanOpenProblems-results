import Submission.CorrelationMoments

/-! Dependent-random-choice sifting for autocorrelation moments.
This file provides an auxiliary finite-group result, not the Erdős conjecture. -/
namespace Erdos3CorrelationSifting
open Finset Erdos3CorrelationMoments
open scoped BigOperators Classical
set_option maxHeartbeats 1000000

/-- Select a sample with substantial weight and small relative cost. -/
lemma select_weight_cost {V : Type*} [Fintype V] [Nonempty V]
    (w b : V → ℝ) {M B : ℝ} (hM : 0 < M) (hB : 0 < B)
    (hb : ∀ v, 0 ≤ b v) (hwmean : M ≤ 𝔼 v, w v) (hbmean : (𝔼 v, b v) ≤ B) :
    ∃ v, M ≤ 2*w v ∧ M*b v ≤ 2*B*w v := by
  let score : V → ℝ := fun v ↦ 2*B*w v - M*b v
  have hm : B*M ≤ 𝔼 v, score v := by
    dsimp only [score]
    rw [expect_sub_distrib, ← mul_expect, ← mul_expect]
    nlinarith
  obtain ⟨v, _, hv⟩ := exists_max_image univ score univ_nonempty
  have hs : B*M ≤ score v := hm.trans (expect_le univ_nonempty hv)
  dsimp only [score] at hs
  refine ⟨v, ?_, ?_⟩
  · have hcost : 0 ≤ M*b v := mul_nonneg hM.le (hb v)
    nlinarith
  · nlinarith [mul_pos hB hM]

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def indicator (A : Finset G) (x : G) : ℝ := if x ∈ A then 1 else 0
noncomputable def density (A : Finset G) : ℝ := (A.card : ℝ) / Fintype.card G
noncomputable def common {I : Type*} [Fintype I] (A : Finset G) (v : I → G) : Finset G :=
  univ.filter (fun x ↦ ∀ i, x+v i ∈ A)
noncomputable def pairDensity (A : Finset G) (q : G → ℝ) : ℝ :=
  𝔼 x : G, 𝔼 y : G, indicator A x * indicator A y * q (y-x)

omit [AddCommGroup G] [Fintype G] in
lemma indicator_nonneg (A : Finset G) (x : G) : 0 ≤ indicator A x := by
  unfold indicator
  split_ifs <;> norm_num

omit [AddCommGroup G] in
lemma expect_indicator (A : Finset G) : (𝔼 x : G, indicator A x) = density A := by
  rw [Fintype.expect_eq_sum_div_card]
  simp [indicator, density]

lemma indicator_common {I : Type*} [Fintype I] (A : Finset G) (v : I → G) (x : G) :
    indicator (common A v) x = ∏ i, indicator A (x+v i) := by
  simp [indicator, common, Fintype.prod_boole]

lemma pairDensity_one (A : Finset G) : pairDensity A (fun _ ↦ 1) = (density A)^2 := by
  unfold pairDensity
  simp only [mul_one, ← Fintype.expect_mul_expect, expect_indicator, sq]

lemma pairDensity_nonneg (A : Finset G) (q : G → ℝ) (hq : ∀ x, 0 ≤ q x) :
    0 ≤ pairDensity A q := by
  apply expect_nonneg
  intro x _
  apply expect_nonneg
  intro y _
  exact mul_nonneg (mul_nonneg (indicator_nonneg A x) (indicator_nonneg A y)) (hq _)

lemma corr_indicator_nonneg (A : Finset G) (x : G) : 0 ≤ corr (indicator A) x := by
  exact expect_nonneg (fun y _ ↦ mul_nonneg (indicator_nonneg A y) (indicator_nonneg A _))

lemma expect_common_pair (A : Finset G) (p : ℕ) (x y : G) :
    (𝔼 v : Fin p → G, indicator (common A v) x * indicator (common A v) y) =
      (corr (indicator A) (y-x))^p := by
  rw [corr_gram, expect_pow_eq]
  simp only [indicator_common, prod_mul_distrib]

lemma expect_pairDensity_common (A : Finset G) (q : G → ℝ) (p : ℕ) :
    (𝔼 v : Fin p → G, pairDensity (common A v) q) =
      𝔼 t : G, (corr (indicator A) t)^p * q t := by
  unfold pairDensity
  calc
    _ = 𝔼 x : G, 𝔼 y : G, 𝔼 v : Fin p → G,
          indicator (common A v) x * indicator (common A v) y * q (y-x) := by
      rw [expect_comm]
      apply expect_congr rfl
      intro x _
      exact expect_comm _ _ _
    _ = 𝔼 x : G, 𝔼 y : G, (corr (indicator A) (y-x))^p * q (y-x) := by
      simp_rw [← expect_mul, expect_common_pair]
    _ = _ := by
      have ht (x : G) : (𝔼 y : G, (corr (indicator A) (y-x))^p * q (y-x)) =
          𝔼 t : G, (corr (indicator A) t)^p * q t := by
        simpa only [sub_eq_add_neg] using
          expect_translate (fun t ↦ (corr (indicator A) t)^p * q t) (-x)
      simp_rw [ht]
      exact Fintype.expect_const _

lemma expect_density_common_sq (A : Finset G) (p : ℕ) :
    (𝔼 v : Fin p → G, (density (common A v))^2) = 𝔼 t : G, (corr (indicator A) t)^p := by
  simpa only [pairDensity_one, mul_one] using expect_pairDensity_common A (fun _ ↦ 1) p

/-- The weighted average of low-autocorrelation differences is bounded by the threshold moment. -/
lemma expect_bad_pairs_le (A : Finset G) (p : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    (𝔼 v : Fin p → G, pairDensity (common A v)
      (fun t ↦ if corr (indicator A) t ≤ L then 1 else 0)) ≤ L^p := by
  rw [expect_pairDensity_common]
  apply expect_le univ_nonempty
  intro t _
  by_cases ht : corr (indicator A) t ≤ L
  · simp only [if_pos ht, mul_one]
    exact pow_le_pow_left₀ (corr_indicator_nonneg A t) ht _
  · simp only [if_neg ht, mul_zero]
    exact pow_nonneg hL _

/-- A large autocorrelation moment produces an intersection of translates with substantial
squared density and few pairs whose differences have low autocorrelation. -/
theorem exists_sifted_intersection (A : Finset G) (p : ℕ) {L M : ℝ}
    (hL : 0 < L) (hM : 0 < M) (hmoment : M ≤ 𝔼 t : G, (corr (indicator A) t)^p) :
    ∃ v : Fin p → G,
      (common A v).Nonempty ∧
      M ≤ 2*(density (common A v))^2 ∧
      M*pairDensity (common A v) (fun t ↦ if corr (indicator A) t ≤ L then 1 else 0) ≤
        2*L^p*(density (common A v))^2 := by
  have hm : M ≤ 𝔼 v : Fin p → G, (density (common A v))^2 := by
    rw [expect_density_common_sq]
    exact hmoment
  obtain ⟨v, hvsize, hvbad⟩ := select_weight_cost
    (fun v : Fin p → G ↦ (density (common A v))^2)
    (fun v ↦ pairDensity (common A v) (fun t ↦ if corr (indicator A) t ≤ L then 1 else 0))
    hM (pow_pos hL p)
    (fun v ↦ pairDensity_nonneg _ _ (fun t ↦ by split_ifs <;> norm_num)) hm
    (expect_bad_pairs_le A p hL.le)
  refine ⟨v, ?_, hvsize, hvbad⟩
  by_contra hn
  have hz : common A v = ∅ := not_nonempty_iff_eq_empty.mp hn
  simp only [hz, density, card_empty, Nat.cast_zero, zero_div, zero_pow (by decide : 2 ≠ 0),
    mul_zero] at hvsize
  linarith

noncomputable def normalized (A : Finset G) (x : G) : ℝ := indicator A x / density A

omit [AddCommGroup G] in
lemma density_nonneg (A : Finset G) : 0 ≤ density A := by unfold density; positivity

lemma density_pos (A : Finset G) (hA : A.Nonempty) : 0 < density A := by
  unfold density
  exact div_pos (by exact_mod_cast hA.card_pos) (by exact_mod_cast Fintype.card_pos)

lemma expect_normalized (A : Finset G) (hA : A.Nonempty) :
    (𝔼 x : G, normalized A x) = 1 := by
  unfold normalized
  rw [← expect_div, expect_indicator, div_self (density_pos A hA).ne']

lemma corr_normalized (A : Finset G) (x : G) :
    corr (normalized A) x = corr (indicator A) x / (density A)^2 := by
  unfold corr normalized
  simp_rw [div_mul_div_comm, ← sq]
  exact (expect_div _ _ _).symm

lemma conv_normalized (A : Finset G) (x : G) :
    conv (normalized A) x = conv (indicator A) x / (density A)^2 := by
  unfold conv normalized
  simp_rw [div_mul_div_comm, ← sq]
  exact (expect_div _ _ _).symm

lemma corr_indicator_eq (A : Finset G) (hA : A.Nonempty) (x : G) :
    corr (indicator A) x = (density A)^2 * corr (normalized A) x := by
  rw [corr_normalized]
  field_simp [(density_pos A hA).ne']

/-- Normalized version of sifting: the bad-pair fraction is bounded by a ratio of moments. -/
theorem exists_normalized_sifted_intersection (A : Finset G) (hA : A.Nonempty)
    (p : ℕ) {L H : ℝ} (hL : 0 < L) (hH : 0 < H)
    (hmoment : H^p ≤ 𝔼 t : G, (corr (normalized A) t)^p) :
    ∃ v : Fin p → G,
      (common A v).Nonempty ∧
      (density A)^(2*p)*H^p ≤ 2*(density (common A v))^2 ∧
      pairDensity (common A v) (fun t ↦ if corr (normalized A) t ≤ L then 1 else 0) ≤
        2*(L/H)^p*(density (common A v))^2 := by
  have hα := density_pos A hA
  have hLraw : 0 < (density A)^2*L := mul_pos (sq_pos_of_pos hα) hL
  have hM : 0 < ((density A)^2*H)^p := pow_pos (mul_pos (sq_pos_of_pos hα) hH) p
  have hm : ((density A)^2*H)^p ≤ 𝔼 t : G, (corr (indicator A) t)^p := by
    simp_rw [corr_indicator_eq A hA, mul_pow, ← mul_expect]
    exact mul_le_mul_of_nonneg_left hmoment (by positivity)
  obtain ⟨v,hvne,hvs,hvb⟩ := exists_sifted_intersection A p hLraw hM hm
  have hfun : (fun t ↦ if corr (indicator A) t ≤ (density A)^2*L then (1 : ℝ) else 0) =
      (fun t ↦ if corr (normalized A) t ≤ L then (1 : ℝ) else 0) := by
    funext t
    simp only [corr_indicator_eq A hA, mul_le_mul_iff_right₀ (sq_pos_of_pos hα)]
  rw [hfun] at hvb
  refine ⟨v,hvne,?_,?_⟩
  · simpa only [mul_pow, ← pow_mul] using hvs
  · apply (mul_le_mul_iff_right₀ hM).mp
    calc
      ((density A)^2*H)^p * pairDensity (common A v)
          (fun t ↦ if corr (normalized A) t ≤ L then 1 else 0) ≤
          2*((density A)^2*L)^p*(density (common A v))^2 := hvb
      _ = ((density A)^2*H)^p * (2*(L/H)^p*(density (common A v))^2) := by
        rw [mul_pow, mul_pow, div_pow]
        field_simp [hH.ne']

#print axioms select_weight_cost
#print axioms expect_pairDensity_common
#print axioms exists_sifted_intersection
#print axioms exists_normalized_sifted_intersection
end Erdos3CorrelationSifting
