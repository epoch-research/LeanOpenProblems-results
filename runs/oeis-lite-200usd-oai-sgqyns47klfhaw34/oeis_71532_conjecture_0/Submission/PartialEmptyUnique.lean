import FormalConjectures.Util.ProblemImports

partial def isEmptyNat (_ : Unit) : IsEmpty Nat := isEmptyNat ()
partial def uniqueNat (_ : Unit) : Unique Nat := uniqueNat ()
partial def inhabitedFalse (_ : Unit) : Inhabited False := inhabitedFalse ()

#print axioms isEmptyNat
#print axioms uniqueNat
#print axioms inhabitedFalse
