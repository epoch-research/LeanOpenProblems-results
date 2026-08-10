import FormalConjectures.Util.ProblemImports

theorem self (P : Prop) : P := by
  exact self P
#print axioms self

mutual
  theorem t1 (P : Prop) : P := by exact t2 P
  theorem t2 (P : Prop) : P := by exact t1 P
end
#print axioms t1
#print axioms t2
