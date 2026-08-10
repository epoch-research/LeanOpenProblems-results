import FormalConjectures.Util.ProblemImports
open Nat Int Finset

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
def is_sum_of_G7_Pj_Pk (n j k : ℕ) : Prop :=
  ∃ (z : ℤ) (x y : ℕ),
    generalized_polygonal_num_of_sides 7 z + polygonal_num_of_sides j x + polygonal_num_of_sides k y = n

-- n=51 = G7(2)+T(4)+P34(2) = 7+10+34
example : is_sum_of_G7_Pj_Pk 51 3 34 := ⟨2, 4, 2, by decide⟩
-- n=0
example : is_sum_of_G7_Pj_Pk 0 3 34 := ⟨0, 0, 0, by decide⟩
-- n=8 : need G7+T+P34 = 8.  G7(-1)=4? T?  try z x y
example : is_sum_of_G7_Pj_Pk 8 3 34 := ⟨-1, 2, 1, by decide⟩
