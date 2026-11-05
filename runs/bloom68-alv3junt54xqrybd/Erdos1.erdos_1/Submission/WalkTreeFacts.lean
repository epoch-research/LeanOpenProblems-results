import Submission.TreeBasic

/-! Elementary path-charge and rational leaf-weight identities for finite trees. -/

namespace ErdosDSS.TreeCode

open scoped BigOperators

namespace Walk

open Tree

noncomputable section

/-- The sum of queried signs on the path to a leaf, without the root's `1`. -/
def displacement : (t : Tree) → t.Leaf → ℤ
  | tip _, _ => 0
  | fork l _, Sum.inl j => 1 + displacement l j
  | fork _ r, Sum.inr j => -1 + displacement r j

lemma path_root (t : Tree) (j : t.Leaf) : t.path t.root j = 1 := by
  cases t with
  | tip a => rfl
  | fork l r => simp [path, root]

lemma path_charge_left (l r : Tree) (j : l.Leaf) :
    charge (fun i => (fork l r).path i (Sum.inl j)) =
      charge (fun i => l.path i j) + 1 := by
  classical
  have hl (i : l.Leaf) : (if i = l.root then 1 else l.path i j) = l.path i j := by
    split_ifs with hi
    · subst i; simp [path_root]
    · rfl
  simp [charge, Leaf, Fintype.sum_sum_type, path, hl]

lemma path_charge_right (l r : Tree) (j : r.Leaf) :
    charge (fun i => (fork l r).path i (Sum.inr j)) =
      charge (fun i => r.path i j) - 1 := by
  classical
  have hr (i : r.Leaf) : (if i = r.root then -1 else r.path i j) =
      r.path i j - (if i = r.root then 2 else 0) := by
    split_ifs with hi
    · subst i; simp [path_root]
    · simp
  simp [charge, Leaf, Fintype.sum_sum_type, path, hr, Finset.sum_sub_distrib]
  ring

/-- The distinguished all-one root row contributes exactly one to every column. -/
theorem path_charge (t : Tree) (j : t.Leaf) :
    charge (fun i => t.path i j) = 1 + displacement t j := by
  induction t with
  | tip a => simp [charge, Leaf, path, displacement]
  | fork l r ihl ihr =>
    cases j with
    | inl j => rw [path_charge_left, ihl]; simp only [displacement]; ring
    | inr j => rw [path_charge_right, ihr]; simp only [displacement]; ring

/-- The fair binary weight of a leaf. -/
def leafWeight (t : Tree) (j : t.Leaf) : ℚ := 1 / (2 : ℚ) ^ t.depth j

lemma leafWeight_nonneg (t : Tree) (j : t.Leaf) : 0 ≤ leafWeight t j := by
  unfold leafWeight
  positivity

lemma leafWeight_left (l r : Tree) (j : l.Leaf) :
    leafWeight (fork l r) (Sum.inl j) = leafWeight l j / 2 := by
  simp [leafWeight, depth, pow_succ, div_mul_eq_div_div]

lemma leafWeight_right (l r : Tree) (j : r.Leaf) :
    leafWeight (fork l r) (Sum.inr j) = leafWeight r j / 2 := by
  simp [leafWeight, depth, pow_succ, div_mul_eq_div_div]

/-- The binary leaf weights partition one unit of mass. -/
theorem sum_leafWeight (t : Tree) : ∑ j, leafWeight t j = 1 := by
  induction t with
  | tip a => simp [Leaf, leafWeight, depth]
  | fork l r ihl ihr =>
    simp only [Leaf, Fintype.sum_sum_type, leafWeight_left, leafWeight_right]
    rw [← Finset.sum_div, ← Finset.sum_div, ihl, ihr]
    norm_num

/-- Expected number of queries, expressed purely by a rational recursion. -/
def expectedDepth : Tree → ℚ
  | tip _ => 0
  | fork l r => 1 + (expectedDepth l + expectedDepth r) / 2

private lemma sum_half_depth {ι : Type*} [Fintype ι] (w d : ι → ℚ) :
    (∑ j, w j / 2 * (d j + 1)) = ((∑ j, w j * d j) + ∑ j, w j) / 2 := by
  simp_rw [div_mul_eq_mul_div, mul_add, mul_one, add_div]
  rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div]

/-- The recursion is the weighted average of the leaf depths. -/
theorem expectedDepth_eq_sum (t : Tree) :
    expectedDepth t = ∑ j, leafWeight t j * (t.depth j : ℚ) := by
  induction t with
  | tip a => simp [expectedDepth, Leaf, depth]
  | fork l r ihl ihr =>
    simp only [Leaf, Fintype.sum_sum_type, leafWeight_left, leafWeight_right, depth,
      Nat.cast_add, Nat.cast_one]
    rw [sum_half_depth, sum_half_depth, sum_leafWeight, sum_leafWeight, ← ihl, ← ihr]
    simp only [expectedDepth]
    ring

private lemma timeout_weight_left (l r : Tree) (j : l.Leaf) :
    (if (fork l r).absorbed (Sum.inl j) then 0 else
      leafWeight (fork l r) (Sum.inl j)) =
        (if l.absorbed j then 0 else leafWeight l j) / 2 := by
  cases hb : l.absorbed j <;> simp [absorbed, leafWeight_left, hb]

private lemma timeout_weight_right (l r : Tree) (j : r.Leaf) :
    (if (fork l r).absorbed (Sum.inr j) then 0 else
      leafWeight (fork l r) (Sum.inr j)) =
        (if r.absorbed j then 0 else leafWeight r j) / 2 := by
  cases hb : r.absorbed j <;> simp [absorbed, leafWeight_right, hb]

/-- The recursive timeout mass is exactly the sum of the timeout leaf weights. -/
theorem tau_eq_sum (t : Tree) :
    t.tau = ∑ j, if t.absorbed j then 0 else leafWeight t j := by
  induction t with
  | tip a => cases a <;> simp [tau, Leaf, absorbed, leafWeight, depth]
  | fork l r ihl ihr =>
    simp only [tau, Leaf, Fintype.sum_sum_type, timeout_weight_left, timeout_weight_right]
    rw [← Finset.sum_div, ← Finset.sum_div, ← ihl, ← ihr]
    ring

/-- A rational first-moment tail bound, with no probability or spectral theory. -/
theorem timeout_mass_mul_le_expectedDepth (t : Tree) (a : ℚ)
    (hdepth : ∀ j, t.absorbed j = false → a ≤ (t.depth j : ℚ)) :
    a * t.tau ≤ expectedDepth t := by
  rw [tau_eq_sum, expectedDepth_eq_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  cases hb : t.absorbed j with
  | false =>
    simpa [hb, mul_comm] using
      mul_le_mul_of_nonneg_left (hdepth j hb) (leafWeight_nonneg t j)
  | true =>
    simp only [↓reduceIte, mul_zero]
    exact mul_nonneg (leafWeight_nonneg t j) (Nat.cast_nonneg _)

end

end Walk

end ErdosDSS.TreeCode
