import FormalConjectures.Util.ProblemImports
#check Mathlib.Tactic.LinearCombination'.qc
#check Mathlib.Tactic.LinearCombination'.hqc
#print axioms Mathlib.Tactic.LinearCombination'.hqc
example : Mathlib.Tactic.LinearCombination'.qc = 0 := by
  have h := Mathlib.Tactic.LinearCombination'.hqc
  linear_combination h
#print axioms _example
