import FormalConjectures.Util.ProblemImports

-- Try nonrecursive letI: RHS should not see itself, likely fails or uses Classical
example (P : Prop) : P := by
  letI : Decidable P := Decidable.isTrue (of_decide_eq_true (p:=P) rfl)
  exact of_decide_eq_true (p:=P) rfl
#print axioms _example

-- Try local let rec returning Decidable P
example (P : Prop) : P := by
  let rec d : Decidable P := Decidable.isTrue (@of_decide_eq_true P d rfl)
  exact @of_decide_eq_true P d rfl
#print axioms _example_1
