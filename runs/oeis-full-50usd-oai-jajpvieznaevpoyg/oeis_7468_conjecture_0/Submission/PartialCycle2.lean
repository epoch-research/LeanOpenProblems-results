import FormalConjectures.Util.ProblemImports

mutual
partial def fFalse (_ : Unit) : False := fFalse ()
partial def neFalse (_ : Unit) : Nonempty False := ⟨fFalse ()⟩
end

theorem bad : False := fFalse ()
#print axioms fFalse
#print axioms bad
