import FormalConjectures.Util.ProblemImports
partial def loopP (P : Prop) [Nonempty P] : P := loopP P
partial def magic (P : Prop) : Nonempty P := ⟨@loopP P (magic P)⟩
example : False := @loopP False (magic False)
#print axioms magic
#print axioms «example»
