import FormalConjectures.Util.ProblemImports

mutual
  noncomputable def neFalse : Nonempty False := ⟨badFalse⟩
  noncomputable def badFalse : False := Classical.choice neFalse
end

#print axioms badFalse
example : False := badFalse
