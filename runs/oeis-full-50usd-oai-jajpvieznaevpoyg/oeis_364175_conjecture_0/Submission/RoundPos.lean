import FormalConjectures.Util.ProblemImports
open Real Nat Int

example (x : ℝ) (hx : 0 < x) : 0 ≤ round x := by
  rw [round_eq]
  apply Int.floor_nonneg.mpr
  linarith

example (x : ℝ) (hx : 0 < x) : ((round x).toNat : ℤ) = round x := by
  exact Int.toNat_of_nonneg (by
    rw [round_eq]
    apply Int.floor_nonneg.mpr
    linarith)
