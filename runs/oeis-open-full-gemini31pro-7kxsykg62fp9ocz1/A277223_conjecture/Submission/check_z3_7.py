from z3 import *

def check_target(target, num_digits):
    s = Solver()
    n_vars = [Int(f"d_{i}") for i in range(num_digits)]
    for v in n_vars:
        s.add(v >= 0, v <= 9)
    s.add(Sum(n_vars) > 0)
    
    # max value of c is 9
    c0 = [Int(f"c0_{i}") for i in range(num_digits + 5)]
    d0 = [Int(f"res0_{i}") for i in range(num_digits + 5)]
    s.add(c0[0] == 0)
    for i in range(num_digits + 4):
        if i < num_digits:
            val = n_vars[i] * target + c0[i]
        else:
            val = c0[i]
        s.add(d0[i] == val % 10)
        s.add(c0[i+1] == val / 10)
        s.add(d0[i] >= 0, d0[i] <= 9)
    s.add(c0[num_digits+4] == 0)
    s.add(Sum(d0) == target)

    def add_S_constraint(s, K, expected, eq=True):
        c = [Int(f"c_{K}_{i}") for i in range(num_digits + 5)]
        d = [Int(f"res_{K}_{i}") for i in range(num_digits + 5)]
        s.add(c[0] == 0)
        for i in range(num_digits + 4):
            if i < num_digits:
                val = n_vars[i] * K + c[i]
            else:
                val = c[i]
            s.add(d[i] == val % 10)
            s.add(c[i+1] == val / 10)
            s.add(d[i] >= 0, d[i] <= 9)
        s.add(c[num_digits+4] == 0)
        if eq:
            s.add(Sum(d) == expected)
        else:
            s.add(Sum(d) != expected)

    for k in range(target+1, 30):
        if k == 9: continue
        add_S_constraint(s, k, k, False)

    s.set("timeout", 10000)
    if s.check() == sat:
        m = s.model()
        res = [m[v].as_long() for v in n_vars]
        print(f"Found target={target}! {res}")
        return res
    else:
        print(f"Unsat target={target}")
        return None

check_target(7, 30)
check_target(8, 30)
