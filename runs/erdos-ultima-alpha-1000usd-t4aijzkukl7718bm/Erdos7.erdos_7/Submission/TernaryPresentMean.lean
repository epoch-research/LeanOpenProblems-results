import Submission.PureProjectionLower

/-! Exact finite lower means for present ternary cylinders. These are
auxiliary finite-measure inequalities, not a noncoverage theorem. -/
namespace Erdos7TernaryPresentMean
open scoped BigOperators
open Erdos7PureProjectionLower
set_option autoImplicit false
set_option maxHeartbeats 2000000

lemma ternary_geom (E : ℕ) :
    geom (1 / 3 : ℝ) E = (1 - (1 / 3 : ℝ)^E) / 2 := by
  induction E with
  | zero => simp [geom]
  | succ E ih =>
    have he : geom (1 / 3 : ℝ) (E + 1) =
        geom (1 / 3 : ℝ) E + (1 / 3 : ℝ)^(E + 1) :=
      Finset.sum_range_succ _ _
    rw [he, ih, pow_succ]
    ring

lemma cylinder_bound_formula (E a : ℕ) (haE : a ≤ E) :
    (1 / 3 : ℝ)^a * (1 - geom (1 / 3 : ℝ) (E-a)) =
      ((1 / 3 : ℝ)^a + (1 / 3 : ℝ)^E) / 2 := by
  rw [ternary_geom]
  have he : (1 / 3 : ℝ)^a * (1 / 3 : ℝ)^(E-a) = (1 / 3 : ℝ)^E := by
    rw [← pow_add, Nat.add_sub_of_le haE]
  nlinarith

lemma tail_sum_formula (n : ℕ) :
    (∑ j ∈ Finset.range (n+1),
      (((1 / 3 : ℝ)^(j+2) + (1 / 3 : ℝ)^(n+2)) / 2)) =
      1 / 12 + ((n : ℝ) / 2 + 1 / 4) * (1 / 3 : ℝ)^(n+2) := by
  have hs : ∀ k : ℕ, (∑ j ∈ Finset.range k, (1 / 3 : ℝ)^(j+2)) =
      (1 - (1 / 3 : ℝ)^k) / 6 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih, show k+2 = (k+1)+1 by omega,
        pow_succ, pow_succ]
      ring
  simp only [← Finset.sum_div, Finset.sum_add_distrib, hs,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  rw [show n+2 = (n+1)+1 by omega, pow_succ]
  ring


/-- The normalization of a convex combination must be kept explicitly. -/
lemma weighted_lower_bound {J : Type*} [Fintype J]
    (w f : J → ℝ) (b : ℝ) (hw : ∀ j, 0 ≤ w j)
    (hf : ∀ j, b ≤ f j) :
    (∑ j, w j) * b ≤ ∑ j, w j * f j := by
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hf j) (hw j))

lemma weighted_strict_lower_bound {J : Type*} [Fintype J]
    (w f : J → ℝ) (b : ℝ) (hw : ∀ j, 0 ≤ w j)
    (hwpos : 0 < ∑ j, w j) (hf : ∀ j, b < f j) :
    (∑ j, w j) * b < ∑ j, w j * f j := by
  rw [Finset.sum_mul]
  apply Finset.sum_lt_sum
  · intro j _
    exact mul_le_mul_of_nonneg_left (hf j).le (hw j)
  · obtain ⟨j, hj, hp⟩ := (Finset.sum_pos_iff_of_nonneg (fun j _ => hw j)).mp hwpos
    exact ⟨j, hj, mul_lt_mul_of_pos_left (hf j) hp⟩

section Finite
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

omit [Fintype Ω] in
lemma integrated_tail_count (μ : Ω → ℝ) (C : ℕ → Finset Ω)
    (U : Finset Ω) (n : ℕ) :
    (∑ x ∈ U, μ x * (∑ j ∈ Finset.range (n+1),
      if x ∈ C (j+2) then (1 : ℝ) else 0)) =
      ∑ j ∈ Finset.range (n+1), mass μ (C (j+2) ∩ U) := by
  simp_rw [Finset.mul_sum, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_ite_mem, Finset.inter_comm]
  rfl


/-- An explicit finite correction accompanies the limiting lower mean 1/6. -/
theorem conditional_tail_mean_bound
    (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hm : (∑ x, μ x) = 1)
    (B C : ℕ → Finset Ω) (n : ℕ)
    (hB : ∀ j, 1 ≤ j → j ≤ n+2 → mass μ (B j) = (1 / 3 : ℝ)^j)
    (hdis : ∀ i j, 1 ≤ i → i ≤ n+2 → 1 ≤ j → j ≤ n+2 →
      i ≠ j → Disjoint (B i) (B j))
    (hC : ∀ a, 2 ≤ a → a ≤ n+2 → mass μ (C a) = (1 / 3 : ℝ)^a)
    (havoid : ∀ a, 2 ≤ a → a ≤ n+2 → ∀ j, 1 ≤ j → j ≤ a →
      Disjoint (C a) (B j)) :
    (1 / 6 + ((n : ℝ) + 1 / 2) * (1 / 3 : ℝ)^(n+2)) /
        (1 + (1 / 3 : ℝ)^(n+2)) ≤
      (∑ j ∈ Finset.range (n+1),
        mass μ (C (j+2) ∩ (Finset.univ \ pureUnion B (n+2)))) /
      mass μ (Finset.univ \ pureUnion B (n+2)) := by
  have hU : mass μ (Finset.univ \ pureUnion B (n+2)) =
      (1 + (1 / 3 : ℝ)^(n+2)) / 2 := by
    rw [pure_complement_mass μ hm B (n+2) (1 / 3) hB hdis, ternary_geom]
    ring
  have hp : 0 < 1 + (1 / 3 : ℝ)^(n+2) := by positivity
  have hh : 1 / 12 + ((n : ℝ) / 2 + 1 / 4) * (1 / 3 : ℝ)^(n+2) ≤
      ∑ j ∈ Finset.range (n+1),
        mass μ (C (j+2) ∩ (Finset.univ \ pureUnion B (n+2))) := by
    rw [← tail_sum_formula]
    apply Finset.sum_le_sum
    intro j hj
    have hjn : j+2 ≤ n+2 := by have := Finset.mem_range.mp hj; omega
    have hb := surviving_cylinder_mass μ hμ B (n+2) (j+2) hjn
      (1 / 3) hB hdis (C (j+2)) (hC _ (by omega) hjn)
      (havoid _ (by omega) hjn)
    rwa [cylinder_bound_formula _ _ hjn] at hb
  rw [hU, div_div_eq_mul_div]
  apply (div_le_div_iff_of_pos_right hp).mpr
  linarith

/-- Every finite complete tail through at least exponent two has mean
strictly above 1/6 under uniform conditioning away from the pure classes. -/
theorem conditional_tail_mean_gt_sixth
    (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hm : (∑ x, μ x) = 1)
    (B C : ℕ → Finset Ω) (n : ℕ)
    (hB : ∀ j, 1 ≤ j → j ≤ n+2 → mass μ (B j) = (1 / 3 : ℝ)^j)
    (hdis : ∀ i j, 1 ≤ i → i ≤ n+2 → 1 ≤ j → j ≤ n+2 →
      i ≠ j → Disjoint (B i) (B j))
    (hC : ∀ a, 2 ≤ a → a ≤ n+2 → mass μ (C a) = (1 / 3 : ℝ)^a)
    (havoid : ∀ a, 2 ≤ a → a ≤ n+2 → ∀ j, 1 ≤ j → j ≤ a →
      Disjoint (C a) (B j)) :
    (1 / 6 : ℝ) <
      (∑ j ∈ Finset.range (n+1),
        mass μ (C (j+2) ∩ (Finset.univ \ pureUnion B (n+2)))) /
      mass μ (Finset.univ \ pureUnion B (n+2)) := by
  apply lt_of_lt_of_le _ (conditional_tail_mean_bound μ hμ hm B C n hB hdis hC havoid)
  apply (lt_div_iff₀ (by positivity : 0 < 1 + (1 / 3 : ℝ)^(n+2))).mpr
  have hp : 0 < (1 / 3 : ℝ)^(n+2) := by positivity
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith

end Finite

#print axioms conditional_tail_mean_bound
#print axioms conditional_tail_mean_gt_sixth
end Erdos7TernaryPresentMean
