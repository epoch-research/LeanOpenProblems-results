import FormalConjectures.Util.ProblemImports

open Rat

def test : ℚ := harmonic 16842
#eval test.num % (16843^3)
