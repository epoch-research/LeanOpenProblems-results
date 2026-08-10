import FormalConjectures.Util.ProblemImports

#check Mathlib.Tactic.CC.false_of_a_eq_not_a
#check Lean.Grind.false_of_not_eq_self
#check Lean.Grind.Bool.false_of_not_eq_self
#check Lean.Grind.CommRing.one_eq_zero_unsat
#check Lean.Grind.Nat.unsat_le_lo
#check Lean.Grind.Nat.unsat_lo_lo
#check Lean.Grind.Nat.unsat_lo_ro
#check Lean.Grind.Linarith.diseq_unsat
#check Lean.Grind.Linarith.lt_unsat

example : False := by
  exact Lean.Grind.Bool.false_of_not_eq_self (a := true) (by decide)

example : False := by
  exact Lean.Grind.false_of_not_eq_self (a := True) (by simp)

example : False := by
  exact Mathlib.Tactic.CC.false_of_a_eq_not_a (a := True) (by simp)
