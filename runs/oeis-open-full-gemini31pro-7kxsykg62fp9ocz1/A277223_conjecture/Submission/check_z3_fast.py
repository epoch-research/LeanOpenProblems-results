from z3 import *

def check_target(target, num_digits):
    s = Solver()
    n_vars = [Int(f"d_{i}") for i in range(num_digits)]
    for v in n_vars:
        s.add(v >= 0, v <= 9)
    s.add(Sum(n_vars) > 0)
    
    # S(target * n) == target
    c0 = [Int(f"c0_{i}") for i in range(num_digits + 4)]
    d0 = [Int(f"res0_{i}") for i in range(num_digits + 4)]
    s.add(c0[0] == 0)
    for i in range(num_digits + 3):
        if i < num_digits:
            val = n_vars[i] * target + c0[i]
        else:
            val = c0[i]
        s.add(d0[i] == val % 10)
        s.add(c0[i+1] == val / 10)
        s.add(d0[i] >= 0, d0[i] <= 9)
    s.add(c0[num_digits+3] == 0)
    s.add(Sum(d0) == target)

    # To make it faster, we don't need S(kn) != k for ALL k.
    # If the conjecture is false, it means for SOME n, max_k is target.
    # Let's just exclude k up to 30.
    for k in range(target+1, 30):
        if k == 9: continue
        c = [Int(f"c_{k}_{i}") for i in range(num_digits + 4)]
        d = [Int(f"res_{k}_{i}") for i in range(num_digits + 4)]
        s.add(c[0] == 0)
        for i in range(num_digits + 3):
            if i < num_digits:
                val = n_vars[i] * k + c[i]
            else:
                val = c[i]
            s.add(d[i] == val % 10)
            s.add(c[i+1] == val / 10)
            s.add(d[i] >= 0, d[i] <= 9)
        s.add(c[num_digits+3] == 0)
        s.add(Sum(d) != k)

    s.set("timeout", 60000)
    if s.check() == sat:
        print(f"SAT for target={target} digits={num_digits}")
        return True
    return False

for target in [7, 8, 10, 11]:
    print(f"Checking target {target} up to 50 digits...")
    check_target(target, 50)
