from sage.all import is_prime, divisors

for n in range(2, 50000, 6):
    # Check if D_2n has exactly 1 prime > 3
    q_D = []
    for d in divisors(2*n):
        q = d + 1
        if q > 3 and is_prime(q):
            q_D.append(q)
    if len(q_D) == 1:
        print(f"n={n}, q_D={q_D[0]}")
