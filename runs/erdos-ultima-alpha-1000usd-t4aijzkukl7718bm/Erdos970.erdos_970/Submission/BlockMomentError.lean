import Submission.BlockMomentObstruction

/-!
Quantitative all-degree intersection errors for the empty-free block model.
These are synthetic probability models, not populations realized by intervals.
The unit-error conclusion retains an explicit numerical budget hypothesis.
-/
namespace Erdos970.BlockMomentObstruction
open Finset Erdos970.FiniteSelberg
variable {β : Type*} [Fintype β] [DecidableEq β]
variable {ι : β → Type*} [∀ j, Fintype (ι j)] [∀ j, DecidableEq (ι j)]

noncomputable def emptyOdds (q : (j : β) → ι j → ℝ) (j : β) : ℝ :=
  (∏ i, (1 - q j i)) / (1 - ∏ i, (1 - q j i))

lemma emptyOdds_nonneg (q : (j : β) → ι j → ℝ)
    (hq : ∀ j i, 0 ≤ q j i ∧ q j i ≤ 1)
    (hless : ∀ j, (∏ i, (1 - q j i)) < 1) (j : β) :
    0 ≤ emptyOdds q j := by
  exact div_nonneg (prod_nonneg (fun i _ => sub_nonneg.mpr (hq j i).2))
    (sub_pos.mpr (hless j)).le

/-- Every nonempty intersection in a single block has a signed moment equal
  to its original mean times minus the odds of the empty atom. -/
lemma signed_hit_moment (q : (j : β) → ι j → ℝ)
    (hless : ∀ j, (∏ i, (1 - q j i)) < 1) (j : β) (T : Finset (ι j)) :
    (∑ v : ι j → Bool,
      ProductMomentObstruction.signedWeight (probability (q j)) (fun _ => false) v *
        hitMonomial T v) =
      if T = ∅ then 0 else -(emptyOdds q j) * ∏ i ∈ T, q j i := by
  classical
  by_cases hT : T = ∅
  · subst T
    simp only [hitMonomial, prod_empty, mul_one, if_true]
    apply ProductMomentObstruction.signed_sum_zero
    · exact probability_sum q j
    · simpa only [probability_empty] using hless j
  · rw [if_neg hT]
    have hzero : hitMonomial T (fun _ => false) = 0 := by
      obtain ⟨i, hi⟩ := nonempty_iff_ne_empty.mpr hT
      rw [hitMonomial_eq, if_neg]
      exact fun h => Bool.noConfusion (h i hi)
    have he (v : ι j → Bool) :
        ProductMomentObstruction.signedWeight (probability (q j)) (fun _ => false) v *
          hitMonomial T v =
        -(emptyOdds q j) * (probability (q j) v * hitMonomial T v) := by
      by_cases hv : v = (fun _ => false)
      · subst v
        rw [hzero]
        ring
      · rw [ProductMomentObstruction.signedWeight, if_neg hv, probability_empty]
        dsimp only [emptyOdds]
        ring
    simp_rw [he]
    rw [← mul_sum]
    change -(emptyOdds q j) * average (q j) (hitMonomial T) = _
    rw [average_hitMonomial]

/-- Exact error formula, without any degree restriction. An omitted block
  contributes a zero factor; otherwise the error factorizes explicitly. -/
theorem all_moment_error_exact (q : (j : β) → ι j → ℝ)
    (hless : ∀ j, (∏ i, (1 - q j i)) < 1) (T : Support (ι := ι)) :
    (∑ v, model q v * test T v) - (∏ j, ∏ i ∈ T j, q j i) =
      -(∏ j, if T j = ∅ then 0 else -(emptyOdds q j) * ∏ i ∈ T j, q j i) := by
  have hh := ProductMomentObstruction.weighted_product
    (fun j => probability (q j)) (fun _ _ => false)
    (fun j => hitMonomial (T j))
  change (∑ v, model q v * test T v) =
    (∏ j, average (q j) (hitMonomial (T j))) -
      ∏ j, ∑ v, ProductMomentObstruction.signedWeight
        (probability (q j)) (fun _ => false) v * hitMonomial (T j) v at hh
  simp_rw [average_hitMonomial, signed_hit_moment q hless] at hh
  linarith only [hh]

lemma nonempty_monomial_le_coordinate {α : Type*} [DecidableEq α]
    (q : α → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (T : Finset α) (i : α) (hi : i ∈ T) : (∏ j ∈ T, q j) ≤ q i := by
  rw [← prod_erase_mul T q hi]
  have he : (∏ j ∈ T.erase i, q j) ≤ 1 :=
    prod_le_one (fun j _ => (hq j).1) (fun j _ => (hq j).2)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right he (hq i).1

/-- A uniform bound on every intersection error. Here `b j` bounds every hit
  probability in block `j`; the product budget is the essential restriction. -/
theorem all_moment_error_le (q : (j : β) → ι j → ℝ)
    (hq : ∀ j i, 0 ≤ q j i ∧ q j i ≤ 1)
    (hless : ∀ j, (∏ i, (1 - q j i)) < 1)
    (b : β → ℝ) (hb : ∀ j, 0 ≤ b j) (hqb : ∀ j i, q j i ≤ b j)
    (T : Support (ι := ι)) :
    |(∑ v, model q v * test T v) - (∏ j, ∏ i ∈ T j, q j i)| ≤
      ∏ j, emptyOdds q j * b j := by
  rw [all_moment_error_exact q hless T, abs_neg, abs_prod]
  apply prod_le_prod (fun _ _ => abs_nonneg _)
  intro j hj
  have ho := emptyOdds_nonneg q hq hless j
  by_cases hT : T j = ∅
  · rw [if_pos hT, abs_zero]
    exact mul_nonneg ho (hb j)
  · rw [if_neg hT, abs_mul, abs_neg, abs_of_nonneg ho,
      abs_of_nonneg (prod_nonneg (fun i _ => (hq j i).1))]
    obtain ⟨i, hi⟩ := nonempty_iff_ne_empty.mpr hT
    exact mul_le_mul_of_nonneg_left
      ((nonempty_monomial_le_coordinate (q j) (hq j) (T j) i hi).trans (hqb j i)) ho

/-- A synthetic population with exact total mass, no empty atom, and ALL
  intersection errors at most one. No assertion about quadratic-scale prime
  budgets or realization as an interval is made. -/
theorem scaled_all_moment_model [Nonempty β] (q : (j : β) → ι j → ℝ)
    (hq : ∀ j i, 0 ≤ q j i ∧ q j i ≤ 1)
    (hhalf : ∀ j, (∏ i, (1 - q j i)) ≤ 1 / 2)
    (b : β → ℝ) (hb : ∀ j, 0 ≤ b j) (hqb : ∀ j i, q j i ≤ b j)
    (X : ℝ) (hX : 0 ≤ X) (hbudget : X * (∏ j, emptyOdds q j * b j) ≤ 1) :
    ∃ w : Pattern (ι := ι) → ℝ, (∀ v, 0 ≤ w v) ∧
      w (fun _ _ => false) = 0 ∧ (∑ v, w v) = X ∧
      ∀ T : Support (ι := ι),
        |(∑ v, w v * test T v) - X * (∏ j, ∏ i ∈ T j, q j i)| ≤ 1 := by
  refine ⟨fun v => X * model q v, (fun v => mul_nonneg hX (model_nonneg q hq hhalf v)),
    by simp [model_empty], ?_, ?_⟩
  · rw [← mul_sum, model_sum q hhalf, mul_one]
  · intro T
    have he : (∑ v, X * model q v * test T v) - X * (∏ j, ∏ i ∈ T j, q j i) =
        X * ((∑ v, model q v * test T v) - (∏ j, ∏ i ∈ T j, q j i)) := by
      simp only [mul_sub, mul_sum, mul_assoc]
    rw [he, abs_mul, abs_of_nonneg hX]
    exact (mul_le_mul_of_nonneg_left (all_moment_error_le q hq
      (fun j => lt_of_le_of_lt (hhalf j) (by norm_num)) b hb hqb T) hX).trans hbudget

/-- The uniform error bound is attained by a test selecting one coordinate in
  every block. Thus a maximizing coordinate in each block gives the exact
  tolerance threshold of this particular model, not merely an upper bound. -/
lemma singleton_moment_error (q : (j : β) → ι j → ℝ)
    (hq : ∀ j i, 0 ≤ q j i ∧ q j i ≤ 1)
    (hless : ∀ j, (∏ i, (1 - q j i)) < 1) (i₀ : (j : β) → ι j) :
    |(∑ v, model q v * test (fun j => {i₀ j}) v) - (∏ j, q j (i₀ j))| =
      ∏ j, emptyOdds q j * q j (i₀ j) := by
  have he := all_moment_error_exact q hless (fun j => {i₀ j})
  simp only [prod_singleton, singleton_ne_empty, ↓reduceIte] at he
  rw [he, abs_neg, abs_prod]
  apply prod_congr rfl
  intro j hj
  rw [abs_mul, abs_neg, abs_of_nonneg (emptyOdds_nonneg q hq hless j),
    abs_of_nonneg (hq j (i₀ j)).1]

/-- For blockwise maximizing coordinates, the displayed numerical budget is
  necessary and sufficient for ALL moments of the scaled model to have error
  at most one. This does not constrain other models or actual interval covers. -/
theorem scaled_all_moments_iff (q : (j : β) → ι j → ℝ)
    (hq : ∀ j i, 0 ≤ q j i ∧ q j i ≤ 1)
    (hless : ∀ j, (∏ i, (1 - q j i)) < 1)
    (i₀ : (j : β) → ι j) (hmax : ∀ j i, q j i ≤ q j (i₀ j))
    (X : ℝ) (hX : 0 ≤ X) :
    (∀ T : Support (ι := ι),
      |(∑ v, X * model q v * test T v) - X * (∏ j, ∏ i ∈ T j, q j i)| ≤ 1) ↔
      X * (∏ j, emptyOdds q j * q j (i₀ j)) ≤ 1 := by
  have he (T : Support (ι := ι)) :
      |(∑ v, X * model q v * test T v) - X * (∏ j, ∏ i ∈ T j, q j i)| =
        X * |(∑ v, model q v * test T v) - (∏ j, ∏ i ∈ T j, q j i)| := by
    have hh : (∑ v, X * model q v * test T v) - X * (∏ j, ∏ i ∈ T j, q j i) =
        X * ((∑ v, model q v * test T v) - (∏ j, ∏ i ∈ T j, q j i)) := by
      simp only [mul_sub, mul_sum, mul_assoc]
    rw [hh, abs_mul, abs_of_nonneg hX]
  constructor
  · intro h
    have hh := h (fun j => {i₀ j})
    rw [he] at hh
    simp only [prod_singleton] at hh
    rwa [singleton_moment_error q hq hless i₀] at hh
  · intro h T
    rw [he]
    exact (mul_le_mul_of_nonneg_left (all_moment_error_le q hq hless
      (fun j => q j (i₀ j)) (fun j => (hq j (i₀ j)).1) hmax T) hX).trans h


/-- Consequently, any global lower polynomial that is nonpositive off the
  empty pattern must pay at least its product mean in coefficient error cost.
  This conclusion is conditional on the same explicit moment budget. -/
theorem global_lower_polynomial_cost {α : Type*} [Fintype α] [Nonempty β]
    (q : (j : β) → ι j → ℝ) (hq : ∀ j i, 0 ≤ q j i ∧ q j i ≤ 1)
    (hhalf : ∀ j, (∏ i, (1 - q j i)) ≤ 1 / 2)
    (b : β → ℝ) (hb : ∀ j, 0 ≤ b j) (hqb : ∀ j i, q j i ≤ b j)
    (X : ℝ) (hX : 0 ≤ X) (hbudget : X * (∏ j, emptyOdds q j * b j) ≤ 1)
    (c : α → ℝ) (T : α → Support (ι := ι))
    (hpoint : ∀ v : Pattern (ι := ι), v ≠ (fun _ _ => false) →
      (∑ t, c t * test (T t) v) ≤ 0) :
    X * (∑ t, c t * ∏ j, ∏ i ∈ T t j, q j i) ≤ ∑ t, |c t| := by
  obtain ⟨w, hw, hwe, hwsum, herr⟩ := scaled_all_moment_model q hq hhalf b hb hqb X hX hbudget
  have hnonpos : (∑ v, w v * (∑ t, c t * test (T t) v)) ≤ 0 := by
    apply sum_nonpos
    intro v hv
    by_cases he : v = (fun _ _ => false)
    · simp only [he, hwe, zero_mul]
      exact le_rfl
    · exact mul_nonpos_of_nonneg_of_nonpos (hw v) (hpoint v he)
  have he : (∑ v, w v * (∑ t, c t * test (T t) v)) =
      ∑ t, c t * (∑ v, w v * test (T t) v) := by
    simp only [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro t ht
    apply sum_congr rfl
    intro v hv
    ring
  rw [he] at hnonpos
  have hdiff : (∑ t, c t * (X * (∏ j, ∏ i ∈ T t j, q j i) -
      (∑ v, w v * test (T t) v))) ≤ ∑ t, |c t| := by
    apply sum_le_sum
    intro t ht
    apply (le_abs_self _).trans
    rw [abs_mul, abs_sub_comm]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (herr (T t)) (abs_nonneg (c t))
  simp only [mul_sub, sum_sub_distrib] at hdiff
  have hm : (∑ t, c t * (X * ∏ j, ∏ i ∈ T t j, q j i)) =
      X * (∑ t, c t * ∏ j, ∏ i ∈ T t j, q j i) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro t ht
    ring
  rw [hm] at hdiff
  linarith

#print axioms all_moment_error_exact
#print axioms scaled_all_moment_model
#print axioms global_lower_polynomial_cost
#print axioms scaled_all_moments_iff
end Erdos970.BlockMomentObstruction
