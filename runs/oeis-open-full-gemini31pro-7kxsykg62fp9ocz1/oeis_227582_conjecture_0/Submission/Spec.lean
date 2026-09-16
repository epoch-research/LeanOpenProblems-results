import FormalConjectures.Util.ProblemImports

open BigOperators LinearRecurrence

def A227582_base (n : ℕ) : ℤ :=
  let order := 7
  let coeffs : Fin order → ℤ := ![1, -2, 1, 0, 0, -1, 2]
  let init : Fin order → ℤ := ![2, 7, 14, 23, 35, 50, 67]
  let E : LinearRecurrence ℤ := { order := order, coeffs := coeffs }
  E.mkSol init n

noncomputable def a (n : ℕ) : ℕ :=
  if h : 0 < n then
    (A227582_base (n - 1)).toNat
  else
    0

theorem oeis_227582_conjecture_0 (n : ℕ) (hn : 0 < n) :
    a n = (Int.floor
      (1 / (2 * (↑(harmonic n) : ℝ) -
            (↑(harmonic (n * n + n - 1)) : ℝ) -
            Real.eulerMascheroniConstant))).toNat := by
  sorry

theorem oeis_227582_conjecture_0.disproof : ¬ (type_of% @oeis_227582_conjecture_0) := sorry
