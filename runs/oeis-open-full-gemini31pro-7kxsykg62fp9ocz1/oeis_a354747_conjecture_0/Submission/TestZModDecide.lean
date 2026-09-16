import FormalConjectures.Util.ProblemImports

def N : ℕ := 10^100 + 3
def x : ZMod N := 123456789
def y : ZMod N := 987654321
theorem test : x * y = 121932631112635269 := by decide
