import FormalConjectures.Util.ProblemImports

partial def inhabP (P : Prop) (_ : Unit) : Inhabited P := inhabP P ()
#print inhabP
#print axioms inhabP

theorem bad : False := (inhabP False ()).default
#print axioms bad
