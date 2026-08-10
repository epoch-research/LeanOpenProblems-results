import FormalConjectures.Util.ProblemImports
open Nat Int Finset

open scoped Classical in
def sun_polygonal_pairs_set : Finset (ℕ × ℕ) :=
  let k_vals_j3 : Finset ℕ := (Icc 3 19) ∪ (Icc 21 24) ∪ {26, 27, 29, 30}
  let set3_k := k_vals_j3.image (fun k => (3, k))
  let k_vals_j4 : Finset ℕ := (Icc 4 11) ∪ {13, 14, 17, 19, 20, 23, 26}
  let set4_k := k_vals_j4.image (fun k => (4, k))
  set3_k ∪ set4_k ∪ {(5, 6), (5, 9), (6, 7), (8, 9)}

set_option maxRecDepth 100000 in
example : ((3,34) : ℕ×ℕ) ∉ sun_polygonal_pairs_set := by decide
set_option maxRecDepth 100000 in
example : ((3,30) : ℕ×ℕ) ∈ sun_polygonal_pairs_set := by decide
