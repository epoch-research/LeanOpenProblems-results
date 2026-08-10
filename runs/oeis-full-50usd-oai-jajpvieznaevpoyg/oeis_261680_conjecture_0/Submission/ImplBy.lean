import FormalConjectures.Util.ProblemImports

def foo : True := by trivial
@[implemented_by (fun _ => True.intro)] def bar (_ : Unit) : True := by trivial
#print axioms bar
