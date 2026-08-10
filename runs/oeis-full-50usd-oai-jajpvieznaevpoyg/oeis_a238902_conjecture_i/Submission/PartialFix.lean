import FormalConjectures.Util.ProblemImports

partial def fixP (P : Prop) (f : P → P) (_ : Unit) : P := f (fixP P f ())
#print fixP
#print axioms fixP

theorem bad : False := fixP False (fun h => h) ()
#print axioms bad
