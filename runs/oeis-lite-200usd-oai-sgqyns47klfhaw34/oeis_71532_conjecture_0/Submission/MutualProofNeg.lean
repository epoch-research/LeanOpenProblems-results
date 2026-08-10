import FormalConjectures.Util.ProblemImports

axiom P : Prop

mutual
  theorem pproof : P := by
    by_cases h : P
    · exact h
    · exact False.elim (nproof h)
  theorem nproof : ¬ P := by
    intro hp
    exact False.elim (nproof hp)
end
#print axioms pproof
