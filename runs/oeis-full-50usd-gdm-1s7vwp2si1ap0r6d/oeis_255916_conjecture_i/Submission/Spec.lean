import FormalConjectures.Util.ProblemImports

open Nat Int Finset

/--
A255916: Number of ways to write $n$ as the sum of a generalized heptagonal number, an octagonal number and a nonagonal number.
$$ a(n) = \# \left\{ (k, x, y) \in \mathbb{Z} \times \mathbb{N} \times \mathbb{N} \mid G_7(k) + P_8(x) + P_9(y) = n \right\} $$
where the generalized heptagonal number is $G_7(k) = \frac{5k^2 - 3k}{2}$, the octagonal number is $P_8(x) = 3x^2 - 2x$, and the nonagonal number is $P_9(y) = \frac{7y^2 - 5y}{2}$.
-/
def a (n : ℕ) : ℕ :=
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
  if _h : m ≥ 3 then
    let m' := (m : ℤ)
    let val := (m' - 2) * k ^ 2 - (m' - 4) * k
    (val / 2).toNat -- Int division
  else 0

/-- The m-th non-generalized polygonal number (for x ≥ 0) is P_m(x) = ((m-2)*x^2 - (m-4)*x) / 2. -/
noncomputable def polygonal_num_of_sides (m : ℕ) (x : ℕ) : ℕ :=
  if _h : m ≥ 3 then
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

def sun_polygonal_pairs_set : Finset (ℕ × ℕ) :=
  -- (3, k) for k = 3..19, 21..24, 26, 27, 29, 30
  let k_vals_j3 : Finset ℕ := (Icc 3 19) ∪ (Icc 21 24) ∪ {26, 27, 29, 30}
  let set3_k := k_vals_j3.image (fun k => (3, k))

  -- (4, k) for k = 4..11, 13, 14, 17, 19, 20, 23, 26
  let k_vals_j4 : Finset ℕ := (Icc 4 11) ∪ {13, 14, 17, 19, 20, 23, 26}
  let set4_k := k_vals_j4.image (fun k => (4, k))

  set3_k ∪ set4_k ∪ {(5, 6), (5, 9), (6, 7), (8, 9)}

end PolygonalNumbers

lemma is_sum_comm (n j k : ℕ) : is_sum_of_G7_Pj_Pk n j k ↔ is_sum_of_G7_Pj_Pk n k j := by
  unfold is_sum_of_G7_Pj_Pk
  constructor
  · rintro ⟨z, x, y, h⟩
    use z, y, x
    rw [← h]
    omega
  · rintro ⟨z, x, y, h⟩
    use z, y, x
    rw [← h]
    omega

lemma polygonal_num_6_eq_3 (y : ℕ) :
    polygonal_num_of_sides 6 y = polygonal_num_of_sides 3 (if y = 0 then 0 else 2 * y - 1) := by
  unfold polygonal_num_of_sides
  have h6 : 6 ≥ 3 := by omega
  have h3 : 3 ≥ 3 := by omega
  rw [dif_pos h6, dif_pos h3]
  split_ifs with hy
  · subst hy
    simp
  · simp only [Nat.cast_ofNat]
    have h_cast : ((2 * y - 1 : ℕ) : ℤ) = 2 * (y : ℤ) - 1 := by omega
    rw [h_cast]
    have h_eq : (6 - 2 : ℤ) * (y : ℤ)^2 - (6 - 4) * (y : ℤ) = (3 - 2 : ℤ) * (2 * (y : ℤ) - 1)^2 - (3 - 4) * (2 * (y : ℤ) - 1) := by
      ring
    rw [h_eq]


lemma is_sum_3_6_to_3_3 (n : ℕ) : is_sum_of_G7_Pj_Pk n 3 6 → is_sum_of_G7_Pj_Pk n 3 3 := by
  unfold is_sum_of_G7_Pj_Pk
  rintro ⟨z, x, y, h⟩
  use z, x, if y = 0 then 0 else 2 * y - 1
  rw [← h, polygonal_num_6_eq_3 y]

lemma is_sum_6_6_to_3_6 (n : ℕ) : is_sum_of_G7_Pj_Pk n 6 6 → is_sum_of_G7_Pj_Pk n 3 6 := by
  unfold is_sum_of_G7_Pj_Pk
  rintro ⟨z, x, y, h⟩
  use z, if x = 0 then 0 else 2 * x - 1, y
  rw [← h, polygonal_num_6_eq_3 x]

lemma polygonal_num_6_def (y : ℕ) : polygonal_num_of_sides 6 y = y * (2 * y - 1) := by
  unfold polygonal_num_of_sides
  have h6 : 6 ≥ 3 := by omega
  rw [dif_pos h6]
  simp only [Nat.cast_ofNat]
  have h_eq : (6 - 2 : ℤ) * (y : ℤ)^2 - (6 - 4) * (y : ℤ) = 2 * ((y * (2 * y - 1) : ℕ) : ℤ) := by
    cases y with
    | zero => simp
    | succ y' =>
      push_cast
      have : ((2 * (y' + 1) - 1 : ℕ) : ℤ) = 2 * (y' : ℤ) + 1 := by omega
      rw [this]
      ring
  rw [h_eq]
  rw [Int.mul_ediv_cancel_left _ (by omega)]
  rfl

theorem oeis_255916_conjecture_i.disproof : ¬ (
  (∀ (n : ℕ), a n > 0)
  ∧
  (∀ (j k : ℕ),
    3 ≤ j ∧ j ≤ k →
    ((∀ (n : ℕ), is_sum_of_G7_Pj_Pk n j k) ↔ (j, k) ∈ sun_polygonal_pairs_set))
) := by
  rintro ⟨h1, h2⟩
  have h36_iff := h2 3 6 (by omega)
  have h36 : ∀ n, is_sum_of_G7_Pj_Pk n 3 6 := h36_iff.mpr (by simp [sun_polygonal_pairs_set])
  have h66_iff := h2 6 6 (by omega)
  have h66_not : ¬ ∀ n, is_sum_of_G7_Pj_Pk n 6 6 := by
    intro h
    have h66_in := h66_iff.mp h
    simp [sun_polygonal_pairs_set] at h66_in

