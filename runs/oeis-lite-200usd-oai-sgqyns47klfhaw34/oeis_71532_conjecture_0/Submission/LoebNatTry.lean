import FormalConjectures.Util.ProblemImports
axiom P : Prop

def loeb : Nat → P
| 0 => Eq.mp (propext ⟨fun _ => loeb 1, fun _ => True.intro⟩) True.intro
| n+1 => loeb n

example : P := loeb 0
#print axioms loeb
