from sage.all import is_prime, divisors

# Check if there is any n < 5000 where D_m has exactly one prime > 3
# and m(m-1) is completely cancelled.
for n in range(2, 5000):
    m = 2*n
    q_D = [d+1 for d in divisors(m) if d+1 > 3 and is_prime(d+1)]
    if len(q_D) == 1:
        q = q_D[0]
        # We need the odd part of m(m-1) to be completely cancelled.
        # But m(m-1) has factors.
        # For example, n=25, m=50. q=11.
        # m(m-1) = 50 * 49 = 2 * 5^2 * 7^2.
        # All of 5 and 7 must be cancelled by N_50.
        # By Adams theorem, 5 is completely cancelled because 5-1 = 4 doesn't divide 50.
        # Wait, Adams says v_p(B_m) >= v_p(m). So 5^2 is cancelled!
        pass
