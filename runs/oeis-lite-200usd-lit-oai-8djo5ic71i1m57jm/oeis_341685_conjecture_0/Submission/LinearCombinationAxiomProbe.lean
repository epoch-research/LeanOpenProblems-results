import FormalConjectures.Util.ProblemImports
#check Mathlib.Tactic.LinearCombination'.qc
#check Mathlib.Tactic.LinearCombination'.hqc
#print axioms Mathlib.Tactic.LinearCombination'.hqc
example : False := by
  have h : (Mathlib.Tactic.LinearCombination'.qc : ℚ) = 0 := by
    nlinarith [Mathlib.Tactic.LinearCombination'.hqc]
  have h2 : (Mathlib.Tactic.LinearCombination'.qc : ℚ) ≠ 0 := by
    nlinarith [Mathlib.Tactic.LinearCombination'.hqc]
  exact h2 h
