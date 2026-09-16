import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0

def A : ℤ := 12345678901234567890
def B : ℤ := 98765432109876543210

theorem test : Int.gcd A B = 900000000090 := by decide
