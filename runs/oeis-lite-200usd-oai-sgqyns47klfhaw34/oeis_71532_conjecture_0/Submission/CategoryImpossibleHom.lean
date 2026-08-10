import FormalConjectures.Util.ProblemImports

open CategoryTheory

#check CategoryTheory.WithTerminal.false_of_from_star'
#check CategoryTheory.WithInitial.false_of_to_star'

-- instantiate with Unit category
#check (CategoryTheory.WithTerminal.star.Hom (CategoryTheory.WithTerminal.of (PUnit.unit : PUnit)))
#reduce (CategoryTheory.WithTerminal.star.Hom (CategoryTheory.WithTerminal.of (PUnit.unit : PUnit)))

partial def badHom (_ : Unit) : CategoryTheory.WithTerminal.star.Hom (CategoryTheory.WithTerminal.of (PUnit.unit : PUnit)) := badHom ()

#print axioms badHom
