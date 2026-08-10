def E(n, f):
    val_9n_1 = 9*n + 1
    val_2n_1 = 2*n + 1
    val_1_5n_1 = 1.5*n + 1
    val_4_5n_1 = 4.5*n + 1
    val_4n_1 = 4*n + 1
    val_3n_1 = 3*n + 1
    val_n_1 = n + 1
    
    return (f.get(val_9n_1, 0) + f.get(val_2n_1, 0) + f.get(val_1_5n_1, 0) 
            - f.get(val_4_5n_1, 0) - f.get(val_4n_1, 0) - f.get(val_3n_1, 0) - f.get(val_n_1, 0))

all_keys = set()
for n in range(101):
    all_keys.add(9*n + 1)
    all_keys.add(2*n + 1)
    all_keys.add(1.5*n + 1)
    all_keys.add(4.5*n + 1)
    all_keys.add(4*n + 1)
    all_keys.add(3*n + 1)
    all_keys.add(n + 1)
all_keys = sorted(list(all_keys))

try:
    import z3
    s = z3.Solver()
    f_vars = {k: z3.Int(f"f_{k}") for k in all_keys}
    for k in all_keys:
        s.add(f_vars[k] >= 0)
        s.add(f_vars[k] <= 2) # keep them small
        
    def E_z3(n):
        return (f_vars[9*n + 1] + f_vars[2*n + 1] + f_vars[1.5*n + 1] 
                - f_vars[4.5*n + 1] - f_vars[4*n + 1] - f_vars[3*n + 1] - f_vars[n + 1])
                
    for n in range(101):
        s.add(E_z3(n) >= 0)
        
    s.add(E_z3(1) == 1)
    s.add(E_z3(5) == 0)
    
    if s.check() == z3.sat:
        m = s.model()
        f_sol = {k: m[f_vars[k]].as_long() for k in all_keys}
        nz = {k: v for k, v in f_sol.items() if v > 0}
        print("FOUND SOL WITH Z3!")
        print(f"Non-zero: {nz}")
    else:
        print("Z3 UNSAT")
except Exception as e:
    print(f"Failed: {e}")
