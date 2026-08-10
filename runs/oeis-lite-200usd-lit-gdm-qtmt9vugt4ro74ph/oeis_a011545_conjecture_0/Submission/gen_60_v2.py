from fractions import Fraction
from decimal import Decimal, getcontext
import subprocess

getcontext().prec = 150

def generate_and_test(n, k):
    # 1. Generate upper bounds of sqrtTwoAddSeries (for pi_lower_bound)
    # u_i >= sqrt(2 + u_{i-1})
    u = [Fraction(0)]
    u_str = []
    for i in range(1, n + 1):
        v = (Decimal(2) + Decimal(u[-1].numerator) / Decimal(u[-1].denominator)).sqrt()
        target = Decimal(2) - v
        den = 10**(int(i * 0.6) + k)
        num = int(target * den)
        u.append(2 - Fraction(num, den))
        u_str.append(f"2-{num}/{den}")
        
    # 2. Generate lower bounds of sqrtTwoAddSeries (for pi_upper_bound)
    # l_i <= sqrt(2 + l_{i-1})
    l = [Fraction(0)]
    l_str = []
    for i in range(1, n + 1):
        v = (Decimal(2) + Decimal(l[-1].numerator) / Decimal(l[-1].denominator)).sqrt()
        target = Decimal(2) - v
        den = 10**(int(i * 0.6) + k)
        num = int(target * den) + 1
        l.append(2 - Fraction(num, den))
        l_str.append(f"2-{num}/{den}")
        
    lean_code = f"""import FormalConjectures.Util.ProblemImports

open Real Int

theorem pi_gt_60 : 3.141592653589793238462643 < Real.pi := by
  pi_lower_bound [
    {", ".join(u_str)}
  ]

theorem pi_lt_60 : Real.pi < 3.14159265358979323846264339 := by
  pi_upper_bound [
    {", ".join(l_str)}
  ]
"""
    with open("/workspace/leanproject/Submission/Test60.lean", "w") as f:
        f.write(lean_code)

generate_and_test(60, 30)
print("Test60.lean generated!")
