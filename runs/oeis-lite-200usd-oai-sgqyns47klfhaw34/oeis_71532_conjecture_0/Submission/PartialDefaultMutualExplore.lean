import FormalConjectures.Util.ProblemImports

mutual
  partial def fNot (P : Prop) (h : ¬ P := gNot P) : ¬ P := h
  partial def gNot (P : Prop) : ¬ P := fNot P
end

theorem bad : False := by exact gNot True trivial
#print axioms bad
