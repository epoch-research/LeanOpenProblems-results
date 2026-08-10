import FormalConjectures.Util.ProblemImports

open Nat Int Finset

/--
A255916: Number of ways to write $n$ as the sum of a generalized heptagonal number, an octagonal number and a nonagonal number.
$$ a(n) = \# \left\{ (k, x, y) \in \mathbb{Z} \times \mathbb{N} \times \mathbb{N} \mid G_7(k) + P_8(x) + P_9(y) = n \right\} $$
where the generalized heptagonal number is $G_7(k) = \frac{5k^2 - 3k}{2}$, the octagonal number is $P_8(x) = 3x^2 - 2x$, and the nonagonal number is $P_9(y) = \frac{7y^2 - 5y}{2}$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- Generalized heptagonal number G_7(k) for k in Z.
  let generalized_heptagonal_num (k : ℤ) : ℕ :=
    ((5 * k ^ 2 - 3 * k) / 2).toNat

  -- Octagonal number P_8(x) for x in N.
  let octagonal_num (x : ℕ) : ℕ :=
    x * (3 * x - 2)

  -- Nonagonal number P_9(y) for y in N.
  let nonagonal_num (y : ℕ) : ℕ :=
    y * (7 * y - 5) / 2

  -- Bounds for iteration: n+1 is a safe upper bound for all indices.
  let N_bound : ℕ := n + 1
  let Z_bound_pos : ℤ := N_bound

  -- Define finite sets for iteration.
  let K_set : Finset ℤ := Finset.Icc (-Z_bound_pos) Z_bound_pos
  let X_set : Finset ℕ := Finset.range N_bound
  let Y_set : Finset ℕ := Finset.range N_bound

  -- The number of solutions is the sum of 1 for each valid triplet (k, x, y).
  Finset.sum K_set fun k =>
    Finset.sum X_set fun x =>
      Finset.sum Y_set fun y =>
        if generalized_heptagonal_num k + octagonal_num x + nonagonal_num y = n then 1 else 0

-- General polygonal number definitions for the conjecture
section PolygonalNumbers

open Int
open scoped Classical

/-- The m-th generalized polygonal number is G_m(k) = ((m-2)*k^2 - (m-4)*k) / 2.
    We define it as a natural number. -/
noncomputable def generalized_polygonal_num_of_sides (m : ℕ) (k : ℤ) : ℕ :=
  if h : m ≥ 3 then
    let m' := (m : ℤ)
    let val := (m' - 2) * k ^ 2 - (m' - 4) * k
    (val / 2).toNat -- Int division
  else 0

/-- The m-th non-generalized polygonal number (for x ≥ 0) is P_m(x) = ((m-2)*x^2 - (m-4)*x) / 2. -/
noncomputable def polygonal_num_of_sides (m : ℕ) (x : ℕ) : ℕ :=
  if h : m ≥ 3 then
    let m' := (m : ℤ)
    let x' := (x : ℤ)
    let val := (m' - 2) * x' ^ 2 - (m' - 4) * x'
    (val / 2).toNat -- Int division
  else 0

/-- Predicate asserting that n can be written as the sum of a generalized heptagonal number (G_7),
and two non-generalized polygonal numbers P_j and P_k. -/
def is_sum_of_G7_Pj_Pk (n j k : ℕ) : Prop :=
  ∃ (z : ℤ) (x y : ℕ),
    generalized_polygonal_num_of_sides 7 z + polygonal_num_of_sides j x + polygonal_num_of_sides k y = n

/-- The set of ordered pairs (j, k) from the conjecture's statement. -/
def sun_polygonal_pairs_set : Finset (ℕ × ℕ) :=
  -- (3, k) for k = 3..19, 21..24, 26, 27, 29, 30
  let k_vals_j3 : Finset ℕ := (Icc 3 19) ∪ (Icc 21 24) ∪ {26, 27, 29, 30}
  let set3_k := k_vals_j3.image (fun k => (3, k))

  -- (4, k) for k = 4..11, 13, 14, 17, 19, 20, 23, 26
  let k_vals_j4 : Finset ℕ := (Icc 4 11) ∪ {13, 14, 17, 19, 20, 23, 26}
  let set4_k := k_vals_j4.image (fun k => (4, k))

  set3_k ∪ set4_k ∪ {(5, 6), (5, 9), (6, 7), (8, 9)}

end PolygonalNumbers

lemma generalized_polygonal_num_of_sides_seven_eq (z : ℤ) :
    generalized_polygonal_num_of_sides 7 z = ((5 * z ^ 2 - 3 * z) / 2).toNat := by
  simp [generalized_polygonal_num_of_sides]

lemma polygonal_num_of_sides_eight_eq (x : ℕ) :
    polygonal_num_of_sides 8 x = x * (3 * x - 2) := by
  cases x with
  | zero => simp [polygonal_num_of_sides]
  | succ t =>
    unfold polygonal_num_of_sides
    simp
    norm_num
    have hnat : (3 * (t + 1) - 2 : ℕ) = 3 * t + 1 := by omega
    rw [hnat]
    have hdiv : (6 * ((t:ℤ) + 1) ^ 2 - 4 * ((t:ℤ) + 1)) / 2 =
        1 + (t:ℤ) * 4 + (t:ℤ)^2 * 3 := by
      ring_nf
      omega
    rw [hdiv]
    apply Int.ofNat_inj.mp
    rw [Int.toNat_of_nonneg]
    · norm_num
      ring_nf
    · positivity

lemma polygonal_num_of_sides_nine_eq (y : ℕ) :
    polygonal_num_of_sides 9 y = y * (7 * y - 5) / 2 := by
  cases y with
  | zero => simp [polygonal_num_of_sides]
  | succ t =>
    unfold polygonal_num_of_sides
    simp
    norm_num
    have hnat : (7 * (t + 1) - 5 : ℕ) = 7 * t + 2 := by omega
    rw [hnat]
    have hdiv : (7 * ((t:ℤ) + 1) ^ 2 - 5 * ((t:ℤ) + 1)) / 2 =
        (2 + (t:ℤ)*9 + (t:ℤ)^2*7) / 2 := by
      ring_nf
    rw [hdiv]
    have hnat' : (t + 1) * (7 * t + 2) = 2 + t * 9 + t ^ 2 * 7 := by ring
    rw [hnat']
    apply Int.ofNat_inj.mp
    rw [Int.toNat_of_nonneg]
    · rw [Int.natCast_div]
      norm_num
    · positivity

lemma a_pos_imp_is_sum_of_G7_P8_P9 {n : ℕ} (ha : a n > 0) :
    is_sum_of_G7_Pj_Pk n 8 9 := by
  unfold a at ha
  dsimp at ha
  have hne :
      (∑ k ∈ Finset.Icc (-(↑(n + 1) : ℤ)) (↑(n + 1) : ℤ),
        ∑ x ∈ Finset.range (n + 1),
          ∑ y ∈ Finset.range (n + 1),
            if ((5 * k ^ 2 - 3 * k) / 2).toNat + x * (3 * x - 2) + y * (7 * y - 5) / 2 = n then 1 else 0) ≠ 0 := by
    exact Nat.ne_of_gt ha
  rcases Finset.exists_ne_zero_of_sum_ne_zero hne with ⟨k, hk, hkne⟩
  rcases Finset.exists_ne_zero_of_sum_ne_zero hkne with ⟨x, hx, hxne⟩
  rcases Finset.exists_ne_zero_of_sum_ne_zero hxne with ⟨y, hy, hyne⟩
  by_cases hxy : ((5 * k ^ 2 - 3 * k) / 2).toNat + x * (3 * x - 2) + y * (7 * y - 5) / 2 = n
  · refine ⟨k, x, y, ?_⟩
    rw [generalized_polygonal_num_of_sides_seven_eq, polygonal_num_of_sides_eight_eq,
      polygonal_num_of_sides_nine_eq]
    exact hxy
  · simp [hxy] at hyne


/-
Conjecture: (i) a(n) > 0 for all n. Moreover, for k >= j >=3, every nonnegative integer can be
written as the sum of a generalized heptagonal number, a j-gonal number and a k-gonal number,
if and only if (j,k) is among the following ordered pairs:
(3,k) (k = 3..19, 21..24, 26, 27, 29, 30), (4,k) (k = 4..11, 13, 14, 17, 19, 20, 23, 26),
(5,6), (5,9), (6,7), (8,9).
-/

theorem oeis_255916_conjecture_i :
  (∀ (n : ℕ), a n > 0)
  ∧
  (∀ (j k : ℕ),
    3 ≤ j ∧ j ≤ k →
    ((∀ (n : ℕ), is_sum_of_G7_Pj_Pk n j k) ↔ (j, k) ∈ sun_polygonal_pairs_set)) :=
by sorry
