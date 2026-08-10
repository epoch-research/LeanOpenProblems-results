import sympy
from sympy import gamma, S

arguments = set()
for n in range(1, 11):
    n_r = S(n)
    args = [9 * n_r + 1, 2 * n_r + 1, S(3)/2 * n_r + 1, S(9)/2 * n_r + 1, 4 * n_r + 1, 3 * n_r + 1, n_r + 1]
    for arg in args:
        arguments.add(arg)

arguments = sorted(list(arguments))

lines = []
for arg in arguments:
    if arg.is_Integer:
        val = int(sympy.factorial(arg - 1))
        real_str = f"{val}"
    else:
        k = int(arg - S(1)/2)
        num = sympy.factorial(2*k)
        den = (sympy.factorial(k) * (4**k))
        real_str = f"({int(num)} : ℝ) / ({int(den)} : ℝ)"
    
    if arg.is_Integer:
        arg_str = f"{int(arg)}"
    else:
        arg_str = f"{int(arg.numerator)} / {int(arg.denominator)}"
    
    lines.append(f"  else if x = {arg_str} then {real_str}")

print("\n".join(lines))
