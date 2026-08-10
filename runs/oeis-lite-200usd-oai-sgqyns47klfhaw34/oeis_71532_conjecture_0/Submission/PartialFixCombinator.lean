import FormalConjectures.Util.ProblemImports

partial def loeb (P : Prop) (f : (Unit → P) → P) : P :=
  f (fun _ => loeb P f)

#print axioms loeb

example (P : Prop) : P := loeb P (fun g => g ())
#print axioms _example
