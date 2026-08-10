import FormalConjectures.Util.ProblemImports

mutual
partial def fFalse : False := fFalse
partial def neFalse : Nonempty False := ⟨fFalse⟩
end

theorem bad : False := fFalse
#print axioms fFalse
#print axioms bad
