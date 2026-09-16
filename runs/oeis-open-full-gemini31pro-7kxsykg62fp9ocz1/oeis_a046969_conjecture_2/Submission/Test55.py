from sage.all import is_prime, divisors, factor, bernoulli

for n in range(7, 20000, 6):
    q_D = [d+1 for d in divisors(2*n) if d+1 > 3 and is_prime(d+1)]
    if len(q_D) == 1:
        q = q_D[0]
        # Check if q == 5 mod 6
        if q % 6 == 5:
            # Check if 2n-1 is completely cancelled
            rem = 2*n - 1
            m = 2*n
            b = bernoulli(m) / m
            num = b.numerator()
            cancelled = True
            for p, e in factor(rem):
                if num % (p**e) != 0:
                    cancelled = False
                    break
            if cancelled:
                print(f"BINGO! n={n}, q={q}")
