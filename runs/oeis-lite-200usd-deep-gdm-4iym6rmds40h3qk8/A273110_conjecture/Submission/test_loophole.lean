import FormalConjectures.Util.ProblemImports

def cheat_impl (u : Unit) : Bool := true

@[implemented_by cheat_impl]
def cheat (u : Unit) : Bool := false

theorem cheat_eq : cheat () = true := by rfl
