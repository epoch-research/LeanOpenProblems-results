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

# We want to find a dictionary f mapping float keys (integers and half-integers) to integers >= 0
# such that:
# 1. E(n, f) >= 0 for all n in range(0, 100)
# 2. E(1, f) != E(5, f) mod something, or just 2**E(5, f) != 2**E(1, f) mod 125.

import random

# We can represent f as a dict.
# Let's run a random walk or local search to find a valid f!
# Keys of f are numbers in { 9*n+1, 2*n+1, 1.5*n+1, 4.5*n+1, 4*n+1, 3*n+1, n+1 } for n in 0..100.
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

# Since we want E(n) >= 0, we can start with f(x) = 0 for all x.
# Then E(n) = 0 >= 0 for all n. But then E(1) == E(5) == 0.
# We want to increase some f(x) to make E(1) != E(5) (mod 125), while maintaining E(n) >= 0 for all n.
# Let's do a depth first search or BFS.
# Let's limit the keys to those appearing for n <= 10.
active_keys = set()
for n in range(11):
    active_keys.add(9*n + 1)
    active_keys.add(2*n + 1)
    active_keys.add(1.5*n + 1)
    active_keys.add(4.5*n + 1)
    active_keys.add(4*n + 1)
    active_keys.add(3*n + 1)
    active_keys.add(n + 1)
active_keys = sorted(list(active_keys))

# Let's search!
import sys

def search():
    # We want to find a dict f with keys in active_keys and values in [0, 1, 2, 3]
    # such that E(n, f) >= 0 for all n in range(101)
    # and (2**E(5, f) - 2**E(1, f)) % 125 != 0
    # Actually, let's just make E(n, f) >= 0 for all n.
    # Since active_keys has size ~50, we can try random assignments or a greedy search.
    f = {k: 0 for k in active_keys}
    
    # Let's try to find any solution by randomly incrementing keys and fixing violations.
    # If we increment f[k], we might cause some E(n) to go negative if k is in a negative position for n.
    # But it's easier to just do a random search or genetic algorithm.
    for step in range(100000):
        # random key
        k = random.choice(active_keys)
        f[k] += 1
        if f[k] > 4:
            f[k] = 0
            
        # check if E(n) >= 0 for all n
        ok = True
        for n in range(101):
            if E(n, f) < 0:
                ok = False
                break
        if ok:
            # Check if it gives different a(1) and a(5) mod 125
            val1 = 2**E(1, f)
            val5 = 2**E(5, f)
            if (val1 - val5) % 125 != 0:
                print(f"FOUND! f = {f}")
                print(f"E(1) = {E(1, f)}, a(1) = {val1}")
                print(f"E(5) = {E(5, f)}, a(5) = {val5}")
                # Print non-zero elements
                nz = {k: v for k, v in f.items() if v > 0}
                print(f"Non-zero: {nz}")
                return f

search()
