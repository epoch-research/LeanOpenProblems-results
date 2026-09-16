import FormalConjectures.Util.ProblemImports

def is_evil (k : ℕ) : Bool := (k.bits.count true % 2) = 0
#print is_evil
