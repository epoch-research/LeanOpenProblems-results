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

import random

def loss(f):
    l = 0
    for n in range(101):
        en = E(n, f)
        if en < 0:
            l += -en * 10  # heavy penalty for negative E(n)
    l += abs(E(1, f) - 1)
    l += abs(E(5, f) - 0)
    return l

def search():
    f = {k: 0 for k in all_keys}
    current_loss = loss(f)
    print(f"Initial loss: {current_loss}")
    
    # Simple simulated annealing / randomized hill climbing
    best_loss = current_loss
    best_f = f.copy()
    
    for iteration in range(500000):
        # make a small change to f
        k = random.choice(all_keys)
        old_val = f[k]
        new_val = random.choice([0, 1, 2])
        if new_val == old_val:
            continue
        f[k] = new_val
        l = loss(f)
        
        # acceptance probability
        if l <= current_loss or random.random() < 0.01:
            current_loss = l
            if l < best_loss:
                best_loss = l
                best_f = f.copy()
                if best_loss == 0:
                    print(f"FOUND! on iteration {iteration}")
                    nz = {k: v for k, v in best_f.items() if v > 0}
                    print(f"Non-zero: {nz}")
                    # verify for all n
                    for n in range(101):
                        assert E(n, best_f) >= 0, f"Failed at {n}"
                    assert E(1, best_f) == 1
                    assert E(5, best_f) == 0
                    return best_f
        else:
            f[k] = old_val # revert
            
    print(f"Finished. Best loss: {best_loss}")

search()
