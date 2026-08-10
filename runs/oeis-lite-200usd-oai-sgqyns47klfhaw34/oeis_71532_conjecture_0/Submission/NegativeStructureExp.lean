import FormalConjectures.Util.ProblemImports
structure T (P : Prop) where
  run : T P → P

def omega (P : Prop) : T P := ⟨fun t => t.run t⟩
example (P : Prop) : P := (omega P).run (omega P)
#print axioms NegativeStructureExp._example_1
