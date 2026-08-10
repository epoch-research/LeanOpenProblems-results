import FormalConjectures.Util.ProblemImports

instance (P : Prop) : Nonempty (Nonempty P) := ⟨⟨Classical.ofNonempty⟩⟩
