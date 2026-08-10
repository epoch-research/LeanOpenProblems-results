import FormalConjectures.Util.ProblemImports
open PowerSeries BigOperators
set_option linter.unusedVariables false

noncomputable def rootCoeff (d : ℕ → ℤ) : ℕ → ℤ
| 0 => 1
| n+1 =>
    let P : PowerSeries ℤ := PowerSeries.mk fun k => if h : k < n+1 then rootCoeff d k else 0
    ((16 * d (n+1) - PowerSeries.coeff (n+1) (P ^ 8)) / 8)
termination_by n => n

#print rootCoeff
#check rootCoeff.eq_1
#check rootCoeff.eq_2

example (d : ℕ → ℤ) : rootCoeff d 0 = 1 := by
  simp [rootCoeff]
