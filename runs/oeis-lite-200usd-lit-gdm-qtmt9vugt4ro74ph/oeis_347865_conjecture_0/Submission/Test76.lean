import FormalConjectures.Util.ProblemImports

def a (n : Nat) : Nat := n

opaque get_nonempty (n : Nat) (hn : n ≥ 745) : Nonempty (a n > 0)
