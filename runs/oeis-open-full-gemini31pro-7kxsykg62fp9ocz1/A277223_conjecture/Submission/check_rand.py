import random

def S(m):
    return sum(int(c) for c in str(m))

for _ in range(100000):
    p = [random.randint(0, 100) for _ in range(7)]
    val = sum(10**x for x in p)
    if val % 7 == 0:
        n = val // 7
        max_k = 0
        for k in range(1, 100):
            if S(k * n) == k:
                max_k = k
        if max_k == 7:
            print(f"Counterexample! n={n}, max_k=7")
            exit(0)
print("No counterexample in random search.")
