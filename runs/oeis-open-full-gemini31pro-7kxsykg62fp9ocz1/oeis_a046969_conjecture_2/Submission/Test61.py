from sage.all import is_prime, divisors

for n in range(4, 50000, 6):
    q_D = [d+1 for d in divisors(2*n) if d+1 > 5 and is_prime(d+1)]
    if len(q_D) == 0:
        print(f"n={n} has NO primes > 5 in D_2n!")
