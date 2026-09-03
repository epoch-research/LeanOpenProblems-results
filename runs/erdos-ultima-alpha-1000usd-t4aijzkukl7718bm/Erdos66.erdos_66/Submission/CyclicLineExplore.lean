import Submission.FiniteFieldExplore

/-!
# Testing a cyclic-group analogue of the finite-field graph construction

In a quadratic field extension with `α² = ν`, the product of `x+uα` and `y+vα`
has coordinates `(xy+νuv, vx+uy)`. The ambient multiplicative group is cyclic.

The counting identity below explains why replacing additive parameter fibers
by multiplicative fibers does not preserve the earlier cancellation estimate.
This is a limitation of that proposed construction, not a disproof of Erdős 66.
-/

namespace Erdos66CyclicLine

variable {F : Type*} [Field F]

lemma line_product_equation_iff (ν u v t s x y : F) (hu : u ≠ 0) :
    (x * y + ν * u * v = s ∧ v * x + u * y = t) ↔
      (y = (t - v * x) / u ∧ v * x ^ 2 - t * x + u * (s - ν * u * v) = 0) := by
  constructor
  · rintro ⟨hs, ht⟩
    constructor
    · apply (eq_div_iff hu).mpr
      linear_combination ht
    · linear_combination -u * hs + x * ht
  · rintro ⟨rfl, h⟩
    constructor
    · apply (mul_left_cancel₀ hu)
      field_simp
      linear_combination -h
    · field_simp
      ring

lemma line_quadratic_iff (hF : ringChar F ≠ 2) (ν u v t s x : F) (hv : v ≠ 0) :
    v * x ^ 2 - t * x + u * (s - ν * u * v) = 0 ↔
      (2 * v * x - t) ^ 2 = t ^ 2 - 4 * u * v * s + 4 * ν * (u * v) ^ 2 := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  have he : (2 * v * x - t) ^ 2 - (t ^ 2 - 4 * u * v * s + 4 * ν * (u * v) ^ 2) =
      (4 * v) * (v * x ^ 2 - t * x + u * (s - ν * u * v)) := by ring
  conv_rhs => rw [← sub_eq_zero, he, mul_eq_zero]
  simp only [mul_ne_zero h4 hv, false_or]

noncomputable def lineRootEquiv (hF : ringChar F ≠ 2) (ν u v t s : F) (hv : v ≠ 0) :
    {x : F // v * x ^ 2 - t * x + u * (s - ν * u * v) = 0} ≃
      {y : F // y ^ 2 = t ^ 2 - 4 * u * v * s + 4 * ν * (u * v) ^ 2} where
  toFun x := ⟨2 * v * x.val - t, (line_quadratic_iff hF ν u v t s x.val hv).mp x.property⟩
  invFun y := ⟨(y.val + t) / (2 * v), by
    have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
    apply (line_quadratic_iff hF ν u v t s _ hv).mpr
    have he : 2 * v * ((y.val + t) / (2 * v)) - t = y.val := by field_simp; ring
    rw [he]
    exact y.property⟩
  left_inv x := by
    have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
    apply Subtype.ext
    change ((2 * v * x.val - t) + t) / (2 * v) = x.val
    field_simp
    ring
  right_inv y := by
    have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
    apply Subtype.ext
    change 2 * v * ((y.val + t) / (2 * v)) - t = y.val
    field_simp
    ring

variable [Fintype F] [DecidableEq F]

lemma line_product_count (hF : ringChar F ≠ 2) (ν u v t s : F) (hv : v ≠ 0) :
    (Fintype.card {x : F // v * x ^ 2 - t * x + u * (s - ν * u * v) = 0} : ℤ) =
      1 + quadraticChar F (t ^ 2 - 4 * u * v * s + 4 * ν * (u * v) ^ 2) := by
  rw [Fintype.card_congr (lineRootEquiv hF ν u v t s hv)]
  have h := quadraticChar_card_sqrts hF (t ^ 2 - 4 * u * v * s + 4 * ν * (u * v) ^ 2)
  simpa only [Set.toFinset_card, Nat.card_eq_fintype_card, add_comm] using h

noncomputable def productFiber (U : Finset F) (w : F) : ℤ :=
  ∑ u ∈ U, ∑ v ∈ U, if u * v = w then 1 else 0

noncomputable def weightedProductFiber (U : Finset F) (w : F) : ℤ :=
  ∑ u ∈ U, ∑ v ∈ U, if u * v = w then quadraticChar F u * quadraticChar F v else 0

omit [Fintype F] in
lemma productFiber_nonneg (U : Finset F) (w : F) : 0 ≤ productFiber U w := by
  apply Finset.sum_nonneg
  intro u hu
  apply Finset.sum_nonneg
  intro v hv
  split_ifs <;> norm_num

omit [Fintype F] in
lemma productFiber_zero (U : Finset F) (hU : ∀ u ∈ U, u ≠ 0) : productFiber U 0 = 0 := by
  apply Finset.sum_eq_zero
  intro u hu
  apply Finset.sum_eq_zero
  intro v hv
  exact if_neg (mul_ne_zero (hU u hu) (hU v hv))

lemma weightedProductFiber_eq (U : Finset F) (w : F) :
    weightedProductFiber U w = quadraticChar F w * productFiber U w := by
  unfold weightedProductFiber productFiber
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  split_ifs with huv
  · rw [← map_mul, huv, mul_one]
  · rw [mul_zero]

lemma abs_weightedProductFiber (U : Finset F) (hU : ∀ u ∈ U, u ≠ 0) (w : F) :
    |weightedProductFiber U w| = productFiber U w := by
  rw [weightedProductFiber_eq, abs_mul, abs_of_nonneg (productFiber_nonneg U w)]
  by_cases hw : w = 0
  · rw [hw, productFiber_zero U hU, mul_zero]
  · have hsq := quadraticChar_sq_one (F := F) hw
    have habs : |quadraticChar F w| = 1 := by
      rcases quadraticChar_isQuadratic F w with h | h | h <;> simp_all
    rw [habs, one_mul]

lemma sum_productFiber (U : Finset F) : (∑ w : F, productFiber U w) = (U.card : ℤ) ^ 2 := by
  unfold productFiber
  rw [Finset.sum_comm]
  have hinner (u : F) : (∑ w : F, ∑ v ∈ U, if u * v = w then (1 : ℤ) else 0) = U.card := by
    rw [Finset.sum_comm]
    simp
  simp_rw [hinner]
  simp [pow_two]

/-- In contrast to additive parameter fibers, the multiplicative character weights
have constant sign on every product fiber. Their total variation is the full main term. -/
lemma weightedProductFiber_l1 (U : Finset F) (hU : ∀ u ∈ U, u ≠ 0) :
    (∑ w : F, |weightedProductFiber U w|) = (U.card : ℤ) ^ 2 := by
  simp_rw [abs_weightedProductFiber U hU]
  exact sum_productFiber U

noncomputable def lineProductCount (U : Finset F) (ν t s : F) : ℤ :=
  ∑ u ∈ U, ∑ v ∈ U,
    (Fintype.card {x : F // v * x ^ 2 - t * x + u * (s - ν * u * v) = 0} : ℤ)

lemma lineProductCount_identity (hF : ringChar F ≠ 2) (U : Finset F)
    (hU : ∀ u ∈ U, u ≠ 0) (ν t s : F) :
    lineProductCount U ν t s = (U.card : ℤ) ^ 2 +
      ∑ w : F, productFiber U w * quadraticChar F (t ^ 2 - 4 * w * s + 4 * ν * w ^ 2) := by
  have he : lineProductCount U ν t s = (U.card : ℤ) ^ 2 +
      ∑ u ∈ U, ∑ v ∈ U, quadraticChar F (t ^ 2 - 4 * (u * v) * s + 4 * ν * (u * v) ^ 2) := by
    unfold lineProductCount
    calc
      _ = ∑ u ∈ U, ∑ v ∈ U,
          (1 + quadraticChar F (t ^ 2 - 4 * (u * v) * s + 4 * ν * (u * v) ^ 2)) := by
        apply Finset.sum_congr rfl
        intro u hu
        apply Finset.sum_congr rfl
        intro v hv
        simpa only [mul_assoc] using line_product_count hF ν u v t s (hU v hv)
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
        ring
  rw [he]
  congr 1
  symm
  unfold productFiber
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  simp only [ite_mul, zero_mul, one_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

lemma productFiber_character_factor (U : Finset F) (hU : ∀ u ∈ U, u ≠ 0) (ν t s w : F) :
    productFiber U w * quadraticChar F (t ^ 2 - 4 * w * s + 4 * ν * w ^ 2) =
      weightedProductFiber U w * quadraticChar F (t ^ 2 / w - 4 * s + 4 * ν * w) := by
  rw [weightedProductFiber_eq]
  by_cases hw : w = 0
  · rw [hw, productFiber_zero U hU]
    simp
  · have he : t ^ 2 - 4 * w * s + 4 * ν * w ^ 2 =
        w * (t ^ 2 / w - 4 * s + 4 * ν * w) := by
      field_simp
    rw [he, map_mul]
    ring

lemma lineProductCount_weighted_identity (hF : ringChar F ≠ 2) (U : Finset F)
    (hU : ∀ u ∈ U, u ≠ 0) (ν t s : F) :
    lineProductCount U ν t s = (U.card : ℤ) ^ 2 +
      ∑ w : F, weightedProductFiber U w * quadraticChar F (t ^ 2 / w - 4 * s + 4 * ν * w) := by
  rw [lineProductCount_identity hF U hU]
  congr 1
  apply Finset.sum_congr rfl
  intro w hw
  exact productFiber_character_factor U hU ν t s w

/-- The direct analogue of the old triangle-inequality estimate gives an error
as large as the entire main term, rather than a relative error tending to zero. -/
lemma lineProductCount_triangle_bound (hF : ringChar F ≠ 2) (U : Finset F)
    (hU : ∀ u ∈ U, u ≠ 0) (ν t s : F) :
    |lineProductCount U ν t s - (U.card : ℤ) ^ 2| ≤ (U.card : ℤ) ^ 2 := by
  rw [lineProductCount_weighted_identity hF U hU, add_sub_cancel_left,
    ← weightedProductFiber_l1 U hU]
  calc
    _ ≤ ∑ w : F, |weightedProductFiber U w *
        quadraticChar F (t ^ 2 / w - 4 * s + 4 * ν * w)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro w hw
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left
        (Erdos66FiniteField.quadraticChar_abs_le_one _) (abs_nonneg _)).trans_eq (mul_one _)

end Erdos66CyclicLine
