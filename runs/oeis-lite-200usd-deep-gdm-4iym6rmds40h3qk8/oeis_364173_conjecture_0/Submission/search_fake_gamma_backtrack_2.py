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

import math
import random

def loss(f):
    l = 0
    for n in range(101):
        en = E(n, f)
        if en < 0:
            l += -en * 100
    l += abs(E(1, f) - 1) * 100
    l += abs(E(5, f) - 0) * 100
    
    # L0 penalty
    num_nz = len([v for v in f.values() if v > 0])
    l += num_nz
    return l

def solve_sa():
    best_loss = 999999
    best_f = None
    
    for run in range(200):
        f = {k: 0 for k in all_keys}
        cur_loss = loss(f)
        T = 20.0
        decay = 0.995
        
        for step in range(10000):
            # pick a key
            k = random.choice(all_keys)
            old_val = f[k]
            new_val = random.choice([0, 1])
            if new_val == old_val:
                continue
            f[k] = new_val
            l = loss(f)
            
            # acceptance
            delta = l - cur_loss
            if delta <= 0 or random.random() < math.exp(-delta / T):
                cur_loss = l
                if cur_loss < best_loss:
                    best_loss = cur_loss
                    best_f = f.copy()
                    num_nz = len([v for v in best_f.values() if v > 0])
                    # If constraints are satisfied (loss < 100)
                    if best_loss < 100:
                        print(f"FOUND VALID SOL on run {run}, step {step}! Non-zero count: {num_nz}")
                        nz = {k: v for k, v in best_f.items() if v > 0}
                        print(f"Non-zero: {nz}")
                        # If count is very small, we can stop
                        if num_nz <= 10:
                            return best_f
            else:
                f[k] = old_val
                
            T *= decay
            if T < 0.01:
                T = 0.01
                
    print(f"SA finished. Best loss found: {best_loss}")
    if best_f is not None and best_loss < 100:
        nz = {k: v for k, v in best_f.items() if v > 0}
        print(f"Best Non-zero: {nz}")
    return best_f

solve_sa()
