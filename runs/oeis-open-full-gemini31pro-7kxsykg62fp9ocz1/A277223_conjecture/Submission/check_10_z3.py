from z3 import *

digits = 15
n_vars = [Int(f"d_{i}") for i in range(digits)]

s = Solver()
for v in n_vars:
    s.add(v >= 0, v <= 9)

s.add(Sum(n_vars) == 10)

def add_S_constraint(s, K, expected, eq=True):
    c = [Int(f"c_{K}_{i}") for i in range(digits + 3)]
    d = [Int(f"res_{K}_{i}") for i in range(digits + 3)]
    s.add(c[0] == 0)
    for i in range(digits + 2):
        if i < digits:
            val = n_vars[i] * K + c[i]
        else:
            val = c[i]
        s.add(d[i] == val % 10)
        s.add(c[i+1] == val / 10)
        s.add(d[i] >= 0, d[i] <= 9)
    s.add(c[digits+2] == 0)
    if eq:
        s.add(Sum(d) == expected)
    else:
        s.add(Sum(d) != expected)

for k in range(11, 40):
    add_S_constraint(s, k, k, False)

if s.check() == sat:
    m = s.model()
    print("Found!", [m[v].as_long() for v in n_vars])
else:
    print("Unsat")
