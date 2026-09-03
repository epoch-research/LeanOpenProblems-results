import FormalConjecturesUtil

/-! Exact finite-dimensional direction test at a tight nonnegative linear
budget. This justifies a diagnostic reformulation, not a covering certificate. -/
namespace Erdos7PositiveLPDirection
open scoped BigOperators
set_option autoImplicit false

/-- A direction pointing into the orthant at each zero coordinate can be
followed for a sufficiently small positive distance. -/
theorem exists_positive_step {J : Type*} [Fintype J]
    (x d : J → ℝ) (hx : ∀ j, 0 ≤ x j) (hd : ∀ j, x j = 0 → 0 ≤ d j) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ j, 0 ≤ x j + ε * d j := by
  classical
  let S : ℝ := ∑ j, |d j| / x j
  have hS : 0 ≤ S := Finset.sum_nonneg (fun j _ => div_nonneg (abs_nonneg _) (hx j))
  have hden : 0 < 1 + S := by linarith
  let ε : ℝ := 1 / (1 + S)
  have he : 0 < ε := div_pos zero_lt_one hden
  refine ⟨ε, he, fun j => ?_⟩
  by_cases hj : x j = 0
  · rw [hj, zero_add]
    exact mul_nonneg he.le (hd j hj)
  have hjp : 0 < x j := lt_of_le_of_ne (hx j) (Ne.symm hj)
  have hratio : |d j| / x j ≤ S :=
    Finset.single_le_sum (fun k _ => div_nonneg (abs_nonneg _) (hx k)) (Finset.mem_univ j)
  have ha : |d j| ≤ S * x j := (div_le_iff₀ hjp).mp hratio
  have hb : ε * |d j| ≤ x j := by
    change 1 / (1 + S) * |d j| ≤ x j
    rw [one_div, inv_mul_eq_div]
    apply (div_le_iff₀ hden).mpr
    nlinarith [hx j]
  have hc := mul_le_mul_of_nonneg_left (neg_abs_le (d j)) he.le
  nlinarith

noncomputable def row {J : Type*} [Fintype J] (a x : J → ℝ) : ℝ := ∑ j, a j * x j

lemma row_step {J : Type*} [Fintype J] (a x d : J → ℝ) (ε : ℝ) :
    row a (fun j => x j + ε * d j) = row a x + ε * row a d := by
  unfold row
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma row_sub {J : Type*} [Fintype J] (a x y : J → ℝ) :
    row a (fun j => x j - y j) = row a x - row a y := by
  simp [row, mul_sub, Finset.sum_sub_distrib]

/-- At a point where all rows are tight, a homogeneous improving direction,
with the correct signs at zero coordinates, gives a genuine nonnegative
strictly improving feasible point. -/
theorem direction_gives_strict_improvement {I J : Type*} [Fintype J]
    (A : I → J → ℝ) (b : I → ℝ) (cost x d : J → ℝ)
    (hx : ∀ j, 0 ≤ x j) (htight : ∀ i, row (A i) x = b i)
    (hsign : ∀ j, x j = 0 → 0 ≤ d j)
    (hd : ∀ i, row (A i) d ≤ 0) (hc : row cost d < 0) :
    ∃ y : J → ℝ, (∀ j, 0 ≤ y j) ∧ (∀ i, row (A i) y ≤ b i) ∧
      row cost y < row cost x := by
  obtain ⟨ε, he, hy⟩ := exists_positive_step x d hx hsign
  refine ⟨fun j => x j + ε * d j, hy, fun i => ?_, ?_⟩
  · rw [row_step, htight]
    have := mul_nonpos_of_nonneg_of_nonpos he.le (hd i)
    linarith
  · rw [row_step]
    have := mul_neg_of_pos_of_neg he hc
    linarith

/-- A failed primal minimization may have the constant budget as its optimum.
The equivalent homogeneous direction problem retains the information needed
for a strict improvement; no numerical feasibility assertion is made here. -/
theorem strict_improvement_iff_direction {I J : Type*} [Fintype J]
    (A : I → J → ℝ) (b : I → ℝ) (cost x : J → ℝ)
    (hx : ∀ j, 0 ≤ x j) (htight : ∀ i, row (A i) x = b i) :
    (∃ y : J → ℝ, (∀ j, 0 ≤ y j) ∧ (∀ i, row (A i) y ≤ b i) ∧
      row cost y < row cost x) ↔
    (∃ d : J → ℝ, (∀ j, x j = 0 → 0 ≤ d j) ∧
      (∀ i, row (A i) d ≤ 0) ∧ row cost d < 0) := by
  constructor
  · rintro ⟨y, hy, hAy, hc⟩
    refine ⟨fun j => y j - x j, fun j hj => ?_, fun i => ?_, ?_⟩
    · simpa [hj] using hy j
    · rw [row_sub, htight]
      exact sub_nonpos.mpr (hAy i)
    · rw [row_sub]
      exact sub_neg.mpr hc
  · rintro ⟨d, hsign, hd, hc⟩
    exact direction_gives_strict_improvement A b cost x d hx htight hsign hd hc

#print axioms exists_positive_step
#print axioms strict_improvement_iff_direction
end Erdos7PositiveLPDirection
