import FormalConjectures.Util.ProblemImports
axiom P : Prop

theorem pproof : P := by
  by_cases h : P
  · exact h
  · exact False.elim (h pproof)
#print axioms pproof

mutual
  theorem pp : P := by
    by_cases h : P
    · exact h
    · exact False.elim (h pp)
  theorem nn : ¬ P := by
    intro hp
    by_cases h : P
    · exact False.elim (nn hp)
    · exact h hp
end
#print axioms pp
