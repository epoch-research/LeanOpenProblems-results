import FormalConjectures.Util.ProblemImports

mutual
  noncomputable def badFalse : False := Classical.ofNonempty
  noncomputable instance badNonemptyFalse : Nonempty False := ⟨badFalse⟩
end

theorem t : False := badFalse
#print axioms t
