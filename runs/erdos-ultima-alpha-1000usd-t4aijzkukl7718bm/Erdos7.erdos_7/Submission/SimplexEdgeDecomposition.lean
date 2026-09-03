import Submission.CappedCurrentGeometry

/-! Positive edge decomposition near a corner of a product of three simplexes.
This module is auxiliary; it does not settle the odd covering conjecture. -/
namespace Erdos7SimplexEdgeDecomposition
open scoped BigOperators
set_option autoImplicit false

/-- A displacement whose nonnegative coefficients sum to ε is a convex
combination of the ε-scaled displacements, using only positive coefficients. -/
theorem small_deficit_mem_convexHull {J E : Type*} [Fintype J]
    [AddCommGroup E] [Module ℝ E] (w : J → ℝ) (hw : ∀ j, 0 ≤ w j)
    (ε : ℝ) (hε : 0 < ε) (hs : ∑ j, w j = ε) (base : E) (d : J → E) :
    base + ∑ j, w j • d j ∈ convexHull ℝ
      ((fun j => base + ε • d j) '' {j | w j ≠ 0}) := by
  classical
  let t : Finset J := Finset.univ.filter (fun j => w j ≠ 0)
  have hsum : ∑ j ∈ t, w j = ε := by
    rw [← hs]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro j _ hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hj
    exact hj
  have hnorm : ∑ j ∈ t, w j / ε = 1 := by
    rw [← Finset.sum_div, hsum, div_self hε.ne']
  have hD : ∑ j ∈ t, w j • d j = ∑ j, w j • d j := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro j _ hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hj
    rw [hj, zero_smul]
  have heq : (∑ j ∈ t, (w j / ε) • (base + ε • d j)) =
      base + ∑ j, w j • d j := by
    simp_rw [smul_add, smul_smul]
    rw [Finset.sum_add_distrib, ← Finset.sum_smul, hnorm, one_smul]
    have hmul (j : J) : w j / ε * ε = w j := div_mul_cancel₀ _ hε.ne'
    simp_rw [hmul]
    rw [hD]
  rw [← heq]
  apply (convex_convexHull ℝ _).sum_mem
    (fun j _ => div_nonneg (hw j) hε.le) hnorm
  intro j hj
  apply subset_convexHull
  exact ⟨j, (Finset.mem_filter.mp hj).2, rfl⟩

noncomputable def atom {J : Type*} (j k : J) : ℝ := by
  classical
  exact if k = j then 1 else 0

lemma atom_nonneg {J : Type*} (j k : J) : 0 ≤ atom j k := by
  classical
  unfold atom
  split_ifs <;> norm_num

lemma atom_le_one {J : Type*} (j k : J) : atom j k ≤ 1 := by
  classical
  unfold atom
  split_ifs <;> norm_num

@[simp] lemma atom_self {J : Type*} (j : J) : atom j j = 1 := by simp [atom]
@[simp] lemma atom_sum {J : Type*} [Fintype J] (j : J) : ∑ k, atom j k = 1 := by
  classical
  simp [atom]

lemma atom_average {J : Type*} [Fintype J] (w : J → ℝ) (k : J) :
    (∑ j, w j * atom j k) = w k := by
  classical
  simp [atom, mul_ite]

noncomputable def offMass {J : Type*} (w : J → ℝ) (a j : J) : ℝ := by
  classical
  exact if j = a then 0 else w j

lemma offMass_nonneg {J : Type*} (w : J → ℝ) (hw : ∀ j, 0 ≤ w j) (a j : J) :
    0 ≤ offMass w a j := by
  classical
  unfold offMass
  split_ifs <;> simp_all

lemma offMass_sum {J : Type*} [Fintype J] (w : J → ℝ) (a : J)
    (hs : ∑ j, w j = 1) : ∑ j, offMass w a j = 1 - w a := by
  classical
  have hsplit (j : J) : offMass w a j = w j - (if j = a then w a else 0) := by
    unfold offMass
    split_ifs with h <;> simp_all
  simp_rw [hsplit]
  rw [Finset.sum_sub_distrib, hs]
  simp

lemma offMass_average {J : Type*} [Fintype J] (w : J → ℝ) (a k : J)
    (hs : ∑ j, w j = 1) :
    ∑ j, offMass w a j * (atom j k - atom a k) = w k - atom a k := by
  classical
  have he (j : J) : offMass w a j * (atom j k - atom a k) =
      w j * (atom j k - atom a k) := by
    unfold offMass
    split_ifs with h
    · subst j
      simp
    · rfl
  simp_rw [he, mul_sub]
  rw [Finset.sum_sub_distrib, atom_average, ← Finset.sum_mul, hs, one_mul]

noncomputable def move {J : Type*} (ε : ℝ) (a j k : J) : ℝ :=
  (1 - ε) * atom a k + ε * atom j k

lemma move_nonneg {J : Type*} (ε : ℝ) (hε : 0 ≤ ε) (hε' : ε ≤ 1) (a j k : J) :
    0 ≤ move ε a j k :=
  add_nonneg (mul_nonneg (sub_nonneg.mpr hε') (atom_nonneg _ _))
    (mul_nonneg hε (atom_nonneg _ _))

lemma move_sum {J : Type*} [Fintype J] (ε : ℝ) (a j : J) : ∑ k, move ε a j k = 1 := by
  simp only [move, Finset.sum_add_distrib, ← Finset.mul_sum, atom_sum]
  ring

open Erdos7CappedCurrentGeometry
namespace Profile
variable {I B C : Type*} [Fintype I] [Fintype B] [Fintype C]
variable (P : Erdos7CappedCurrentGeometry.Profile I B C)

abbrev EdgeIndex := B ⊕ C ⊕ I

noncomputable def mass (x : I) : EdgeIndex (B := B) (C := C) (I := I) → ℝ
  | .inl b => offMass P.y (P.branch x) b
  | .inr (.inl c) => offMass P.z (P.cell x) c
  | .inr (.inr i) => offMass P.t x i

noncomputable def base (x k : I) : ℝ :=
  1 + atom (P.branch x) (P.branch k) + atom (P.cell x) (P.cell k) + atom x k

noncomputable def direction (x : I) : EdgeIndex (B := B) (C := C) (I := I) → I → ℝ
  | .inl b, k => atom b (P.branch k) - atom (P.branch x) (P.branch k)
  | .inr (.inl c), k => atom c (P.cell k) - atom (P.cell x) (P.cell k)
  | .inr (.inr i), k => atom i k - atom x k

lemma mass_nonneg (x : I) (j : EdgeIndex (B := B) (C := C) (I := I)) :
    0 ≤ mass P x j := by
  rcases j with b | (c | i)
  · exact offMass_nonneg _ P.y_nonneg _ _
  · exact offMass_nonneg _ P.z_nonneg _ _
  · exact offMass_nonneg _ P.t_nonneg _ _

lemma mass_sum (x : I) : ∑ j, mass P x j = P.deficit x := by
  simp only [Fintype.sum_sum_type, mass]
  rw [offMass_sum _ _ P.y_sum, offMass_sum _ _ P.z_sum, offMass_sum _ _ P.t_sum]
  unfold Erdos7CappedCurrentGeometry.Profile.deficit
  ring

lemma reconstruct (x : I) : base P x + ∑ j, mass P x j • direction P x j = P.count := by
  ext k
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Fintype.sum_sum_type, mass, direction]
  rw [offMass_average _ _ _ P.y_sum, offMass_average _ _ _ P.z_sum,
    offMass_average _ _ _ P.t_sum]
  unfold base Erdos7CappedCurrentGeometry.Profile.count
  ring

/-- Every profile with a positive corner deficit is a positive convex
combination of ε-scaled incident directions. When ε ≤ 1, these lie on the
actual simplex-product edges, as proved in `edge_realizable` below. -/
theorem count_mem_edge_hull (x : I) (hε : 0 < P.deficit x) :
    P.count ∈ convexHull ℝ
      ((fun j => base P x + P.deficit x • direction P x j) '' {j | mass P x j ≠ 0}) := by
  rw [← reconstruct P x]
  exact small_deficit_mem_convexHull (mass P x) (mass_nonneg P x) _ hε
    (mass_sum P x) (base P x) (direction P x)

/-- Conditional maximum principle for a function convex on a set containing
the relevant scaled edges. Convexity of a particular capped budget on its
subdivision region remains a separate hypothesis. -/
theorem edge_maximum_principle (x : I) (hε : 0 < P.deficit x)
    (S : Set (I → ℝ)) (f : (I → ℝ) → ℝ) (hf : ConvexOn ℝ S f)
    (hS : ∀ j, mass P x j ≠ 0 → base P x + P.deficit x • direction P x j ∈ S) :
    ∃ j, mass P x j ≠ 0 ∧
      f P.count ≤ f (base P x + P.deficit x • direction P x j) := by
  have hsub : ((fun j => base P x + P.deficit x • direction P x j) ''
      {j | mass P x j ≠ 0}) ⊆ S := by
    rintro _ ⟨j, hj, rfl⟩
    exact hS j hj
  obtain ⟨_, ⟨j, hj, rfl⟩, hle⟩ :=
    hf.exists_ge_of_mem_convexHull hsub (count_mem_edge_hull P x hε)
  exact ⟨j, hj, hle⟩

/-- A scaled direction really is a probability-simplex profile when its
scale is in [0,1]; positivity is not inferred merely from the hull identity. -/
theorem edge_realizable (x : I) (ε : ℝ) (hε : 0 ≤ ε) (hε' : ε ≤ 1)
    (j : EdgeIndex (B := B) (C := C) (I := I)) :
    ∃ Q : Erdos7CappedCurrentGeometry.Profile I B C,
      Q.branch = P.branch ∧ Q.cell = P.cell ∧
        Q.count = base P x + ε • direction P x j := by
  rcases j with b | (c | i)
  · refine ⟨{
      branch := P.branch, cell := P.cell
      y := move ε (P.branch x) b, z := atom (P.cell x), t := atom x
      y_nonneg := move_nonneg ε hε hε' _ _, z_nonneg := atom_nonneg _, t_nonneg := atom_nonneg _
      y_sum := move_sum _ _ _, z_sum := atom_sum _, t_sum := atom_sum _ }, rfl, rfl, ?_⟩
    ext k
    simp only [Erdos7CappedCurrentGeometry.Profile.count, base, direction, move,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · refine ⟨{
      branch := P.branch, cell := P.cell
      y := atom (P.branch x), z := move ε (P.cell x) c, t := atom x
      y_nonneg := atom_nonneg _, z_nonneg := move_nonneg ε hε hε' _ _, t_nonneg := atom_nonneg _
      y_sum := atom_sum _, z_sum := move_sum _ _ _, t_sum := atom_sum _ }, rfl, rfl, ?_⟩
    ext k
    simp only [Erdos7CappedCurrentGeometry.Profile.count, base, direction, move,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · refine ⟨{
      branch := P.branch, cell := P.cell
      y := atom (P.branch x), z := atom (P.cell x), t := move ε x i
      y_nonneg := atom_nonneg _, z_nonneg := atom_nonneg _, t_nonneg := move_nonneg ε hε hε' _ _
      y_sum := atom_sum _, z_sum := atom_sum _, t_sum := move_sum _ _ _ }, rfl, rfl, ?_⟩
    ext k
    simp only [Erdos7CappedCurrentGeometry.Profile.count, base, direction, move,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

lemma base_at_corner (x : I) : base P x x = 4 := by norm_num [base]

lemma direction_at_corner (x : I) (j : EdgeIndex (B := B) (C := C) (I := I))
    (hj : mass P x j ≠ 0) : direction P x j x = -1 := by
  classical
  rcases j with b | (c | i)
  · have h : b ≠ P.branch x := by
      intro h
      simp [mass, offMass, h] at hj
    simp [direction, atom, Ne.symm h]
  · have h : c ≠ P.cell x := by
      intro h
      simp [mass, offMass, h] at hj
    simp [direction, atom, Ne.symm h]
  · have h : i ≠ x := by
      intro h
      simp [mass, offMass, h] at hj
    simp [direction, atom, Ne.symm h]

lemma direction_le_one (x k : I) (j : EdgeIndex (B := B) (C := C) (I := I)) :
    direction P x j k ≤ 1 := by
  rcases j with b | (c | i)
  · exact (sub_le_self _ (atom_nonneg _ _)).trans (atom_le_one _ _)
  · exact (sub_le_self _ (atom_nonneg _ _)).trans (atom_le_one _ _)
  · exact (sub_le_self _ (atom_nonneg _ _)).trans (atom_le_one _ _)

lemma base_elsewhere_le_three {x k : I} (hxk : x ≠ k) : base P x k ≤ 3 := by
  have hb := atom_le_one (P.branch x) (P.branch k)
  have hc := atom_le_one (P.cell x) (P.cell k)
  simp only [base, atom, if_neg (Ne.symm hxk)]
  change 1 + atom (P.branch x) (P.branch k) + atom (P.cell x) (P.cell k) + 0 ≤ 3
  linarith

/-- All nonzero-weight edge profiles have the same prescribed count at the
corner, while every other count stays below the first cap in the deep regime. -/
theorem deep_edge_bounds (x : I) (hdeep : 96 / 25 ≤ P.count x)
    (j : EdgeIndex (B := B) (C := C) (I := I)) (hj : mass P x j ≠ 0) :
    (base P x + P.deficit x • direction P x j) x = P.count x ∧
    ∀ k, k ≠ x → (base P x + P.deficit x • direction P x j) k ≤ 79 / 25 := by
  constructor
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      base_at_corner, direction_at_corner P x j hj]
    rw [P.deficit_eq]
    ring
  · intro k hk
    have hb := base_elsewhere_le_three P hk.symm
    have hd := direction_le_one P x k j
    have he := P.deficit_nonneg x
    have hm := mul_le_mul_of_nonneg_left hd he
    have hε := P.deep_deficit_le hdeep
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith

/-- The entire deep edge family lies within the original product of
simplexes, not just its ambient affine space. -/
theorem deep_edge_realizable (x : I) (hdeep : 96 / 25 ≤ P.count x)
    (j : EdgeIndex (B := B) (C := C) (I := I)) :
    ∃ Q : Erdos7CappedCurrentGeometry.Profile I B C,
      Q.branch = P.branch ∧ Q.cell = P.cell ∧
        Q.count = base P x + P.deficit x • direction P x j := by
  apply edge_realizable P x _ (P.deficit_nonneg x) _ j
  linarith [P.deep_deficit_le hdeep]

end Profile
#print axioms small_deficit_mem_convexHull
#print axioms Profile.count_mem_edge_hull
#print axioms Profile.deep_edge_bounds
#print axioms Profile.deep_edge_realizable
#print axioms Profile.edge_maximum_principle
end Erdos7SimplexEdgeDecomposition
