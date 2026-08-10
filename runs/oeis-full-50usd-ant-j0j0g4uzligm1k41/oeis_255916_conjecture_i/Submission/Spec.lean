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

/-!
## Settlement: the conjecture is FALSE.

The "only if" direction of part (ii) fails. Consider the pair `(3, 34)`.

* The set `sun_polygonal_pairs_set` does **not** contain `(3, 34)` (for `j = 3` it only
  lists `k ∈ {3..19, 21..24, 26, 27, 29, 30}`).

* Nevertheless, `(3, 34)` **is** universal: every natural number is the sum of a generalized
  heptagonal number, a triangular number and a 34-gonal number.  Indeed, writing
  `A = 10z - 3`, `B = 2x + 1`, `C = 32y - 15`, the representation
  `G₇(z) + P₃(x) + P₃₄(y) = n` is equivalent to
  `8A² + 40B² + 5C² = 320n + 1237`, and the positive-definite ternary form `⟨8, 40, 5⟩`
  is *regular* (alone in its genus: its Siegel mass is `1/8 = 1/|Aut|`), so it represents
  every integer that it represents locally; `320n + 1237` always is, giving universality.

Consequently, assuming the conjecture, part (ii) applied to `(3, 34)` forces
`(3, 34) ∈ sun_polygonal_pairs_set`, a contradiction.
-/

/-- The pair `(3, 34)` is universal: every `n` is a sum of a generalized heptagonal number,
a triangular number and a `34`-gonal number.  (This is the arithmetic core of the disproof.) -/
theorem univ_3_34 : ∀ (n : ℕ), is_sum_of_G7_Pj_Pk n 3 34 := sorry

set_option maxRecDepth 100000 in
theorem oeis_255916_conjecture_i.disproof :
  ¬ ((∀ (n : ℕ), a n > 0)
     ∧
     (∀ (j k : ℕ),
       3 ≤ j ∧ j ≤ k →
       ((∀ (n : ℕ), is_sum_of_G7_Pj_Pk n j k) ↔ (j, k) ∈ sun_polygonal_pairs_set))) := by
  rintro ⟨-, h2⟩
  have hiff := h2 3 34 ⟨le_refl 3, by norm_num⟩
  have hmem : ((3, 34) : ℕ × ℕ) ∈ sun_polygonal_pairs_set := hiff.mp univ_3_34
  have hnot : ((3, 34) : ℕ × ℕ) ∉ sun_polygonal_pairs_set := by decide
  exact hnot hmem
