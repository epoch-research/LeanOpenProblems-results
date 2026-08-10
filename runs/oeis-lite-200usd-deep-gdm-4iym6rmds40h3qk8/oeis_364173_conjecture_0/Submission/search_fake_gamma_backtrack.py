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

# We can find a solution by backtracking on the values of f.
# Since we only want a few non-zero elements, we can represent f as a dict of non-zero elements.
# To find a solution, we can try to find an assignment to a small set of variables.
# Let's write a recursive function that tries to find a valid f.
# We can prune the search by checking if there's any n where E(n, f) is already guaranteed to be negative
# (i.e. the sum of positive terms assigned so far is less than the sum of negative terms assigned so far,
# and no more positive terms can be assigned).
# Since that might be complex to write, let's write a simple randomized coordinate descent with restarts.
# To make coordinate descent avoid local minima, we can use tabu search or simply randomized restarts.
# Let's try randomized restarts with local search (greedy hill climbing but we allow up-hill steps with some probability, i.e., Simulated Annealing).

import math
import random

def solve_sa():
    best_loss = 999999
    best_f = None
    
    # Run multiple seeds of Simulated Annealing
    for run in range(100):
        f = {k: 0 for k in all_keys}
        # Start with some random non-zero values to break symmetry
        for _ in range(5):
            f[random.choice(all_keys)] = random.choice([0, 1, 2])
            
        cur_loss = loss(f)
        T = 10.0
        decay = 0.99
        
        for step in range(5000):
            # pick a key
            k = random.choice(all_keys)
            old_val = f[k]
            new_val = random.choice([0, 1, 2])
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
                    if best_loss == 0:
                        print(f"FOUND SOL on run {run}, step {step}!")
                        nz = {k: v for k, v in best_f.items() if v > 0}
                        print(f"Non-zero: {nz}")
                        return best_f
            else:
                f[k] = old_val
                
            T *= decay
            if T < 0.01:
                T = 0.01
                
    print(f"SA finished. Best loss found: {best_loss}")
    return None

def loss(f):
    l = 0
    for n in range(101):
        en = E(n, f)
        if en < 0:
            l += -en * 10
    l += abs(E(1, f) - 1)
    l += abs(E(5, f) - 0)
    return l

solve_sa()
