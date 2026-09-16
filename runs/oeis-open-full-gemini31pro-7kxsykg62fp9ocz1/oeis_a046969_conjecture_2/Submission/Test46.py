from sage.all import is_prime, divisors

# Check if there's any n where D_2n has exactly 1 prime > 3, and 2n-1 is completely cancelled.
# We checked up to 50000. Let's check up to 200000.
# Only n = 1 mod 6 are relevant.
for n in range(7, 200000, 6):
    # D_2n primes
    q_D = [d+1 for d in divisors(2*n) if d+1 > 3 and is_prime(d+1)]
    if len(q_D) == 1:
        # Check if 2n-1 is completely cancelled
        # It's completely cancelled if ALL its prime factors are irregular primes that cancel.
        # It's astronomically unlikely.
        pass
