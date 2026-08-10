import FormalConjectures.Util.ProblemImports
open scoped BigOperators

noncomputable def A190363_coeffs : Fin 21 → ℤ :=
  fun i =>
    match i.val with
    | 0 => -1
    | 4 => 1
    | 17 => 1
    | _ => 0

example (u : ℕ → ℤ) :
    (∑ i : Fin 21, A190363_coeffs i * u (139 + i.val)) =
      -u 139 + u 143 + u 156 := by
  simp only [Fin.sum_univ_succ, A190363_coeffs, Fin.val_zero, Fin.val_succ]
  ring
