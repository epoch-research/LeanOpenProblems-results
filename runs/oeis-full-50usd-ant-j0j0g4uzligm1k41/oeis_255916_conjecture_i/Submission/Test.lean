import FormalConjectures.Util.ProblemImports
open Nat Int Finset

noncomputable def a (n : ℕ) : ℕ :=
  let generalized_heptagonal_num (k : ℤ) : ℕ := ((5 * k ^ 2 - 3 * k) / 2).toNat
  let octagonal_num (x : ℕ) : ℕ := x * (3 * x - 2)
  let nonagonal_num (y : ℕ) : ℕ := y * (7 * y - 5) / 2
  let N_bound : ℕ := n + 1
  let Z_bound_pos : ℤ := N_bound
  let K_set : Finset ℤ := Finset.Icc (-Z_bound_pos) Z_bound_pos
  let X_set : Finset ℕ := Finset.range N_bound
  let Y_set : Finset ℕ := Finset.range N_bound
  Finset.sum K_set fun k =>
    Finset.sum X_set fun x =>
      Finset.sum Y_set fun y =>
        if generalized_heptagonal_num k + octagonal_num x + nonagonal_num y = n then 1 else 0

noncomputable def generalized_polygonal_num_of_sides (m : ℕ) (k : ℤ) : ℕ :=
  if h : m ≥ 3 then
    let m' := (m : ℤ)
    let val := (m' - 2) * k ^ 2 - (m' - 4) * k
    (val / 2).toNat
  else 0

noncomputable def polygonal_num_of_sides (m : ℕ) (x : ℕ) : ℕ :=
  if h : m ≥ 3 then
    let m' := (m : ℤ)
    let x' := (x : ℤ)
    let val := (m' - 2) * x' ^ 2 - (m' - 4) * x'
    (val / 2).toNat
  else 0

open scoped Classical in
def sun_polygonal_pairs_set : Finset (ℕ × ℕ) :=
  let k_vals_j3 : Finset ℕ := (Icc 3 19) ∪ (Icc 21 24) ∪ {26, 27, 29, 30}
  let set3_k := k_vals_j3.image (fun k => (3, k))
  let k_vals_j4 : Finset ℕ := (Icc 4 11) ∪ {13, 14, 17, 19, 20, 23, 26}
  let set4_k := k_vals_j4.image (fun k => (4, k))
  set3_k ∪ set4_k ∪ {(5, 6), (5, 9), (6, 7), (8, 9)}

-- membership checks
example : ((3,34) : ℕ×ℕ) ∉ sun_polygonal_pairs_set := by decide
example : ((3,30) : ℕ×ℕ) ∈ sun_polygonal_pairs_set := by decide
example : ((8,9) : ℕ×ℕ) ∈ sun_polygonal_pairs_set := by decide
-- polygonal values
example : polygonal_num_of_sides 3 4 = 10 := by decide
example : polygonal_num_of_sides 34 2 = 34 := by decide
example : generalized_polygonal_num_of_sides 7 2 = 7 := by decide
example : generalized_polygonal_num_of_sides 7 (-1) = 4 := by decide
