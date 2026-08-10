import FormalConjectures.Util.ProblemImports
class Oracle (P : Prop) where out : P
mutual
  def badDef : False := by
    exact (inferInstance : Oracle False).out
  instance badInst : Oracle False where
    out := badDef
end
theorem bad : False := badDef
#print axioms bad
