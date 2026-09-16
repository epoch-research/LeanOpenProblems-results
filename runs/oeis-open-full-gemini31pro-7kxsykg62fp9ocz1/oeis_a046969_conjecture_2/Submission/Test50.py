from sage.all import is_prime, divisors

for n in range(4, 50000, 6):
    q_D = []
    for d in divisors(2*n):
        q = d + 1
        if q > 3 and is_prime(q):
            q_D.append(q)
    if len(q_D) == 0:
        print(f"n={n} has NO primes > 3 in D_2n!")
