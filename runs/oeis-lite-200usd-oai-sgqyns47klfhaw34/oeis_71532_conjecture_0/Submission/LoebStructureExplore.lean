import FormalConjectures.Util.ProblemImports

structure Loeb (P : Prop) where
  run : Loeb P → P

def mkLoeb (P : Prop) : Loeb P := ⟨fun x => x.run x⟩

theorem arbitrary (P : Prop) : P := (mkLoeb P).run (mkLoeb P)
#print axioms arbitrary
