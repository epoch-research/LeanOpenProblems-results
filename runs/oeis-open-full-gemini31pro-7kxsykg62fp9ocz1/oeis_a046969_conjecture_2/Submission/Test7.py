def bernoulli_den_only(n):
    # We only need the denominator of B_{2n}/(2n(2n-1)).
    # We can compute it using von Staudt-Clausen and Adams' theorem.
    # B_{2n} = N_{2n} / D_{2n}
    pass

# We can compute exact denominator much faster
import sympy
from sympy import sieve

def get_a(n):
    if n == 0: return 1
    # D_{2n} is product of primes q where q-1 | 2n
    D = 1
    for q in sieve.primerange(2, 2*n + 2):
        if (2*n) % (q - 1) == 0:
            D *= q
    
    # We need denominator of B_{2n} / (2n(2n-1))
    # which is D * 2n * (2n-1) / gcd(N, D * 2n * (2n-1))
    # We know gcd(N, D) = 1.
    # What about gcd(N, 2n(2n-1))?
    # By Adams' theorem, if p | 2n, and p-1 does not divide 2n, then p doesn't divide denominator of B_{2n}/2n.
    # Wait, B_{2n}/2n = N / (D * 2n).
    # Adams theorem says v_p(B_{2n}/2n) >= 0. But actually v_p(B_{2n}/2n) = v_p(B_{2n}) - v_p(2n).
    # Since p-1 does not divide 2n, v_p(D) = 0, so v_p(B_{2n}) = v_p(N).
    # So v_p(N) - v_p(2n) >= 0 => v_p(N) >= v_p(2n) => 2n | N ? No, only the prime factors of 2n where p-1 doesn't divide 2n.
    # What about p-1 | 2n? Then v_p(D) = 1.
    # v_p(B_{2n}/2n) = -1 - v_p(2n). So these primes stay in denominator.
    # What about p | 2n-1 ?
    # Is it cancelled?
    return None

