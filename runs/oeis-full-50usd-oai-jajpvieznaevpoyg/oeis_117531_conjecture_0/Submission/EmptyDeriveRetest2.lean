import FormalConjectures.Util.ProblemImports
inductive Bad : Prop deriving Inhabited
example : False := by
  have b : Bad := default
  cases b
#print axioms _example

inductive BadT : Type deriving Inhabited
example : False := by
  have b : BadT := default
  cases b
#print axioms _example_1
