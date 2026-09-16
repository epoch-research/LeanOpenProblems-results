from z3 import *

digits = 18
n_vars = [Int(f"d_{i}") for i in range(digits)]

s = Solver()
for v in n_vars:
    s.add(v >= 0, v <= 9)

# K = 10
s.add(Sum(n_vars) == 10)

def add_S_constraint(s, K, expected, eq=True):
    c = [Int(f"c_{K}_{i}") for i in range(digits + 4)]
    d = [Int(f"res_{K}_{i}") for i in range(digits + 4)]
    s.add(c[0] == 0)
    for i in range(digits + 3):
        if i < digits:
            val = n_vars[i] * K + c[i]
        else:
            val = c[i]
        s.add(d[i] == val % 10)
        s.add(c[i+1] == val / 10)
        s.add(d[i] >= 0, d[i] <= 9)
    s.add(c[digits+3] == 0)
    if eq:
        s.add(Sum(d) == expected)
    else:
        s.add(Sum(d) != expected)

for k in range(11, 25):
    add_S_constraint(s, k, k, False)

# Try to solve
s.set("timeout", 60000)
if s.check() == sat:
    m = s.model()
    print("Found K=10!", [m[v].as_long() for v in n_vars])
else:
    print("Unsat K=10")

