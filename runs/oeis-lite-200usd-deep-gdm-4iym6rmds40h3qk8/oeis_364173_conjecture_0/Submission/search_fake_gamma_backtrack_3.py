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

# The support of f will be subset of keys up to 9 * 100 + 1 = 901.
# If we restrict our search to only n <= 600, then for any n > 600:
# 9n+1 > 5401
# 2n+1 > 1201
# 1.5n+1 > 901
# 4.5n+1 > 2701
# 4n+1 > 2401
# 3n+1 > 1801
# n+1 > 601
# So all inputs to f are > 901 except possibly n+1 (which is only <= 901 for n <= 900).
# Actually, if n > 900, all inputs are > 901, so E(n, f) = 0.
# If 600 < n <= 900:
# n+1 can be in the support of f if we have elements in support in [601, 901].
# If we don't have any elements in support in [601, 901], then even for 600 < n <= 900,
# all inputs are > 601, so E(n, f) = 0.
# So if we make sure the support of f is contained in [0, 600],
# then for any n > 600, all inputs to f are > 600, so E(n, f) = 0.
# This is a brilliant observation!
# Let's restrict the keys in the support of f to be <= 600.
# Then for any n > 600, all inputs are > 600, so E(n, f) = 0 is guaranteed.
# Thus we only need to check E(n, f) >= 0 for all n from 0 to 600.

import math
import random

all_keys = set()
for n in range(601):
    # Only allow keys <= 600
    for k in [9*n+1, 2*n+1, 1.5*n+1, 4.5*n+1, 4*n+1, 3*n+1, n+1]:
        if k <= 600:
            all_keys.add(k)
all_keys = sorted(list(all_keys))

def loss(f):
    l = 0
    for n in range(601):
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
    
    for run in range(100):
        f = {k: 0 for k in all_keys}
        cur_loss = loss(f)
        T = 20.0
        decay = 0.995
        
        for step in range(15000):
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
                    if best_loss < 100:
                        print(f"FOUND VALID SOL on run {run}, step {step}! Non-zero count: {num_nz}")
                        nz = {k: v for k, v in best_f.items() if v > 0}
                        print(f"Non-zero: {nz}")
                        if num_nz <= 10:
                            return best_f
            else:
                f[k] = old_val
                
            T *= decay
            if T < 0.01:
                T = 0.01
                
    print(f"SA finished. Best loss found: {best_loss}")
    return best_f

solve_sa()
