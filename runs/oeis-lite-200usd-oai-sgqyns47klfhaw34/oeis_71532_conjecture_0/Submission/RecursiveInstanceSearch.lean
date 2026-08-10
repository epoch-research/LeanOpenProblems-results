import FormalConjectures.Util.ProblemImports
axiom P : Prop

@[default_instance 100] instance instNEP [Nonempty P] : Nonempty P := inferInstance
#synth Nonempty P
example : P := Classical.choice (inferInstance : Nonempty P)
