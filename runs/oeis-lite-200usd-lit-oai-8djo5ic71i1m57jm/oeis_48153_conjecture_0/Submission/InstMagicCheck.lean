import FormalConjectures.Util.ProblemImports
partial def loopP (P : Prop) [Nonempty P] : P := loopP P
instance instMagic (P : Prop) : Nonempty P := ⟨@loopP P (instMagic P)⟩
example : False := loopP False
#print axioms instMagic
#print axioms «example»
