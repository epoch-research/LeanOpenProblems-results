import FormalConjectures.Util.ProblemImports

partial def nonemptyP (P : Prop) (_ : Unit) : Nonempty P := nonemptyP P ()
#print nonemptyP
#print axioms nonemptyP

theorem bad : False := Classical.choice (nonemptyP False ())
#print axioms bad
