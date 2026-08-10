import FormalConjectures.Util.ProblemImports

opaque cheat (u : Unit) : Bool

@[implemented_by cheat]
def cheat_impl (u : Unit) : Bool := true

-- Can we prove cheat () = true?
-- If cheat is opaque, cheat () is not definitionally equal to anything, so rfl will fail.
-- But wait! Can we use an axiom? We are not allowed to add new axioms.
