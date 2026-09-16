import FormalConjectures.Util.ProblemImports

open Nat

def a (n : ℕ) : ℕ :=
  let p := 207
  let q := 208
  let power_of_10 := 10 ^ (n + 1)
  let I := (p * power_of_10) / q
  I % 10

noncomputable def max_packing_density_truncated_tetrahedra : Real := 414 / 416

theorem oeis_379732_conjecture_0 : max_packing_density_truncated_tetrahedra = (207 : Real) / 208 := by
  unfold max_packing_density_truncated_tetrahedra
  norm_num

theorem oeis_379732_conjecture_0.disproof : ¬ (type_of% @oeis_379732_conjecture_0) := by
  sorry
