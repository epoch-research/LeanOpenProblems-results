import FormalConjecturesUtil

/-! Elementary geometry of the three-simplex current profile. This is an
auxiliary result only, not an obstruction to an arbitrary odd covering. -/
namespace Erdos7CappedCurrentGeometry
open scoped BigOperators
set_option autoImplicit false

lemma coordinate_le_one {I : Type*} [Fintype I] (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) (i : I) : w i ≤ 1 := by
  rw [← hs]
  exact Finset.single_le_sum (fun j _ => hw j) (Finset.mem_univ i)

lemma pair_sum_le_one {I : Type*} [Fintype I] (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) {i j : I} (hij : i ≠ j) :
    w i + w j ≤ 1 := by
  classical
  rw [← hs]
  calc
    w i + w j = ∑ k ∈ ({i, j} : Finset I), w k := by simp [hij]
    _ ≤ ∑ k, w k := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun k _ _ => hw k)

structure Profile (I B C : Type*) [Fintype I] [Fintype B] [Fintype C] where
  branch : I → B
  cell : I → C
  y : B → ℝ
  z : C → ℝ
  t : I → ℝ
  y_nonneg : ∀ b, 0 ≤ y b
  z_nonneg : ∀ c, 0 ≤ z c
  t_nonneg : ∀ i, 0 ≤ t i
  y_sum : ∑ b, y b = 1
  z_sum : ∑ c, z c = 1
  t_sum : ∑ i, t i = 1

namespace Profile
variable {I B C : Type*} [Fintype I] [Fintype B] [Fintype C]
variable (P : Profile I B C)

noncomputable def count (i : I) : ℝ := 1 + P.y (P.branch i) + P.z (P.cell i) + P.t i

lemma y_le_one (b : B) : P.y b ≤ 1 := coordinate_le_one P.y P.y_nonneg P.y_sum b
lemma z_le_one (c : C) : P.z c ≤ 1 := coordinate_le_one P.z P.z_nonneg P.z_sum c
lemma t_le_one (i : I) : P.t i ≤ 1 := coordinate_le_one P.t P.t_nonneg P.t_sum i

lemma one_le_count (i : I) : 1 ≤ P.count i := by
  have := P.y_nonneg (P.branch i)
  have := P.z_nonneg (P.cell i)
  have := P.t_nonneg i
  unfold count
  linarith

lemma count_le_four (i : I) : P.count i ≤ 4 := by
  have := P.y_le_one (P.branch i)
  have := P.z_le_one (P.cell i)
  have := P.t_le_one i
  unfold count
  linarith

lemma positive_entries_of_three_lt {i : I} (hi : 3 < P.count i) :
    0 < P.y (P.branch i) ∧ 0 < P.z (P.cell i) ∧ 0 < P.t i := by
  have := P.y_le_one (P.branch i)
  have := P.z_le_one (P.cell i)
  have := P.t_le_one i
  unfold count at hi
  constructor
  · linarith
  constructor <;> linarith

lemma distinct_pair_le_seven {i j : I} (hij : i ≠ j) :
    P.count i + P.count j ≤ 7 := by
  have ht := pair_sum_le_one P.t P.t_nonneg P.t_sum hij
  have := P.y_le_one (P.branch i)
  have := P.y_le_one (P.branch j)
  have := P.z_le_one (P.cell i)
  have := P.z_le_one (P.cell j)
  unfold count
  linarith

lemma different_cell_pair_le_six {i j : I} (hc : P.cell i ≠ P.cell j) :
    P.count i + P.count j ≤ 6 := by
  have hij : i ≠ j := fun h => hc (congrArg P.cell h)
  have ht := pair_sum_le_one P.t P.t_nonneg P.t_sum hij
  have hz := pair_sum_le_one P.z P.z_nonneg P.z_sum hc
  have := P.y_le_one (P.branch i)
  have := P.y_le_one (P.branch j)
  unfold count
  linarith

/-- All points reaching the first cap threshold lie in a single cell. -/
theorem high_points_same_cell {i j : I}
    (hi : 16 / 5 ≤ P.count i) (hj : 16 / 5 ≤ P.count j) : P.cell i = P.cell j := by
  by_contra h
  have := P.different_cell_pair_le_six h
  linarith

/-- A point reaching the second threshold is the only point reaching the
first threshold. This uses the stronger pair bound for distinct points. -/
theorem deep_point_unique {i j : I}
    (hi : 96 / 25 ≤ P.count i) (hj : 16 / 5 ≤ P.count j) : i = j := by
  by_contra h
  have := P.distinct_pair_le_seven h
  linarith

noncomputable def deficit (i : I) : ℝ :=
    (1 - P.y (P.branch i)) + (1 - P.z (P.cell i)) + (1 - P.t i)

lemma deficit_eq (i : I) : P.deficit i = 4 - P.count i := by
  unfold deficit count
  ring

lemma deficit_nonneg (i : I) : 0 ≤ P.deficit i := by
  rw [P.deficit_eq]
  linarith [P.count_le_four i]

lemma deep_deficit_le {i : I} (hi : 96 / 25 ≤ P.count i) : P.deficit i ≤ 4 / 25 := by
  rw [P.deficit_eq]
  linarith

/-- For a deep point, every other point stays strictly below the first cap. -/
lemma others_below_first_cap {i j : I} (hi : 96 / 25 ≤ P.count i) (hij : i ≠ j) :
    P.count j ≤ 79 / 25 := by
  have := P.distinct_pair_le_seven hij
  linarith

end Profile

noncomputable def capLevel (a : ℕ) : ℝ := 4 - 4 / (5 : ℝ) ^ a

lemma capLevel_mono : Monotone capLevel := by
  intro a b hab
  have hp : (5 : ℝ)^a ≤ 5^b := pow_le_pow_right₀ (by norm_num) hab
  have hd := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 4)
    (by positivity : (0 : ℝ) < 5^a) hp
  unfold capLevel
  linarith

lemma first_cap_le {a : ℕ} (ha : 1 ≤ a) : (16 : ℝ) / 5 ≤ capLevel a := by
  have := capLevel_mono ha
  norm_num [capLevel] at this ⊢
  exact this

lemma second_cap_le {a : ℕ} (ha : 2 ≤ a) : (96 : ℝ) / 25 ≤ capLevel a := by
  have := capLevel_mono ha
  norm_num [capLevel] at this ⊢
  exact this

/-- Two distinct active cap points force both cap levels to be the first. -/
theorem simultaneous_cap_levels {I B C : Type*} [Fintype I] [Fintype B] [Fintype C]
    (P : Profile I B C) {i j : I} (hij : i ≠ j) {a b : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hi : capLevel a ≤ P.count i) (hj : capLevel b ≤ P.count j) : a = 1 ∧ b = 1 := by
  have hal : a < 2 := by
    by_contra h
    exact hij (P.deep_point_unique ((second_cap_le (by omega)).trans hi)
      ((first_cap_le hb).trans hj))
  have hbl : b < 2 := by
    by_contra h
    exact hij (P.deep_point_unique ((second_cap_le (by omega)).trans hj)
      ((first_cap_le ha).trans hi)).symm
  omega

#print axioms simultaneous_cap_levels
#print axioms Profile.high_points_same_cell
#print axioms Profile.others_below_first_cap
end Erdos7CappedCurrentGeometry
