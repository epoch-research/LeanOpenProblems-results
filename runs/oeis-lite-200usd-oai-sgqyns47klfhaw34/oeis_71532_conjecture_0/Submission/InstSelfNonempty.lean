import FormalConjectures.Util.ProblemImports

axiom P : Prop

noncomputable instance instNEP : Nonempty P := ⟨Classical.choice instNEP⟩
#print axioms instNEP
example : P := Classical.choice instNEP
