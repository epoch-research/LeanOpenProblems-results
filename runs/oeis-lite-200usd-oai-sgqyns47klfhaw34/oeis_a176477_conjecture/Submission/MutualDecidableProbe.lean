import FormalConjectures.Util.ProblemImports
mutual
  def badProof : False := by
    cases badDec with
    | isTrue h => exact h
    | isFalse h => exact False.elim (badProof)
  def badDec : Decidable False := isTrue badProof
end

theorem bad : False := badProof
#print axioms bad
