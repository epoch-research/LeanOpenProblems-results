import random

def S(m):
    return sum(int(c) for c in str(m))

for target in [8, 10, 11]:
    for _ in range(100000):
        p = [random.randint(0, 50) for _ in range(target)]
        val = sum(10**x for x in p)
        if val % target == 0:
            n = val // target
            max_k = 0
            for k in range(1, 100):
                if S(k * n) == k:
                    max_k = k
            if max_k == target:
                print(f"Counterexample! target={target}, n={n}, max_k={target}")
                exit(0)
print("No counterexample in random search.")
