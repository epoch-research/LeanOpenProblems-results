def S(m):
    return sum(int(c) for c in str(m))

def max_valid(n):
    max_k = 0
    for k in range(1, 100):
        if S(k*n) == k: max_k = k
    return max_k

for n in range(1, 20000):
    for K in range(1, 10):
        if S(K*n) == K:
            M = K*n
            # check if there is some k > K with S(kn) = k
            valid = [k for k in range(K+1, 200) if S(k*n) == k]
            if not valid:
                print(f"Counterexample! n={n}, K={K}")
