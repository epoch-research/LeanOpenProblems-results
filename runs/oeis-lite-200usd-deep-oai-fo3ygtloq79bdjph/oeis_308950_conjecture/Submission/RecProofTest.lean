import FormalConjectures.Util.ProblemImports

mutual
  noncomputable def badProof : False := Classical.choice badNonempty
  noncomputable def badNonempty : Nonempty False := ⟨badProof⟩
end

#print axioms badProof
#check badProof
