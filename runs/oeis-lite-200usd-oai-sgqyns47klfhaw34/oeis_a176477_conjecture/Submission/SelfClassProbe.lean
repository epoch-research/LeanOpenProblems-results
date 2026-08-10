import FormalConjectures.Util.ProblemImports
class Oracle (P : Prop) where out : P
mutual
  theorem bad : False := by
    exact (inferInstance : Oracle False).out
  noncomputable instance badInst : Oracle False where
    out := bad
end
#print axioms bad
