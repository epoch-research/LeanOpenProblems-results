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
  Finset.sum K_set fun k => Finset.sum X_set fun x => Finset.sum Y_set fun y =>
    if generalized_heptagonal_num k + octagonal_num x + nonagonal_num y = n then 1 else 0

section PolygonalNumbers
open Int
open scoped Classical
noncomputable def generalized_polygonal_num_of_sides (m : ℕ) (k : ℤ) : ℕ :=
  if h : m ≥ 3 then
    let m' := (m : ℤ); let val := (m' - 2) * k ^ 2 - (m' - 4) * k
    (val / 2).toNat
  else 0
noncomputable def polygonal_num_of_sides (m : ℕ) (x : ℕ) : ℕ :=
  if h : m ≥ 3 then
    let m' := (m : ℤ); let x' := (x : ℤ); let val := (m' - 2) * x' ^ 2 - (m' - 4) * x'
    (val / 2).toNat
  else 0
def is_sum_of_G7_Pj_Pk (n j k : ℕ) : Prop :=
  ∃ (z : ℤ) (x y : ℕ),
    generalized_polygonal_num_of_sides 7 z + polygonal_num_of_sides j x + polygonal_num_of_sides k y = n
def sun_polygonal_pairs_set : Finset (ℕ × ℕ) :=
  let k_vals_j3 : Finset ℕ := (Icc 3 19) ∪ (Icc 21 24) ∪ {26, 27, 29, 30}
  let set3_k := k_vals_j3.image (fun k => (3, k))
  let k_vals_j4 : Finset ℕ := (Icc 4 11) ∪ {13, 14, 17, 19, 20, 23, 26}
  let set4_k := k_vals_j4.image (fun k => (4, k))
  set3_k ∪ set4_k ∪ {(5, 6), (5, 9), (6, 7), (8, 9)}
end PolygonalNumbers

-- universality of (3,34) : the hard part
theorem univ_3_34 : ∀ (n : ℕ), is_sum_of_G7_Pj_Pk n 3 34 := sorry

theorem foo.disproof :
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
