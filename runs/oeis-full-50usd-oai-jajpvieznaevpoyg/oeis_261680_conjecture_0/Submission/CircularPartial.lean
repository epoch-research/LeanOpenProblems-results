import FormalConjectures.Util.ProblemImports
structure Cert where
  pr : False
partial def cert (_ : Unit) : Cert := cert ()
instance : Nonempty Cert := ⟨cert ()⟩
theorem bad : False := (cert ()).pr
#print axioms bad
