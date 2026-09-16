import math
import sys
sys.set_int_max_str_digits(2000000)

a = math.factorial(50000)
b = math.factorial(50000) - 1

print(f"""
import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0

def A : ℤ := {a}
def B : ℤ := {b}

theorem test : Int.gcd A B = 1 := by decide
""")
