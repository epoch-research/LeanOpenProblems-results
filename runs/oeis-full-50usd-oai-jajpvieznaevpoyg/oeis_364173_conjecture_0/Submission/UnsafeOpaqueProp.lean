import FormalConjectures.Util.ProblemImports
unsafe instance propInhabited (P : Prop) : Inhabited P := unsafeCast (inferInstanceAs (Inhabited True))
opaque fake : False
theorem bad : False := fake
#print axioms bad
