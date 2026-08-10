import FormalConjectures.Util.ProblemImports
opaque badP : Prop := False
opaque badProof : badP := by
  dsimp [badP]
  sorry

theorem t : badP := badProof
#print axioms badProof
#print axioms t
