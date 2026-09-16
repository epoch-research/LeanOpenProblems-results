from sage.all import is_prime, divisors, bernoulli

for n in range(5, 50000, 6):
    q_D = [d+1 for d in divisors(2*n) if d+1 > 3 and is_prime(d+1)]
    if len(q_D) == 1:
        print(f"n={n}, q_D={q_D[0]}")
