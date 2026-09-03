# Divisor-row dispersion investigation — original still unresolved

Spec.lean is unchanged and still contains its original sorry. No prime-pair
lower bound or irrational counterexample has been obtained. No incomplete
proof was submitted.

## New verified file

DivisorRowDispersion.lean, namespace Erdos972DivisorRowDispersion.
The three principal declarations compile and audit with only propext,
Classical.choice, and Quot.sound.

For the existing actual divisor rows

    R_d = sum_{n in S, d|g(n)} a(n),

set

    V_D = sum_{1<=d<=D} (R_d-X/d)^2,
    C_D(x,y) = #{1<=d<=D : d|gcd(x,y)},
    H_D(x) = sum_{1<=d<=D, d|x} 1/d.

The file proves the exact identity

    V_D = sum_n a(n)^2 C_D(g(n),g(n))
          +sum_{n!=m} a(n)a(m) C_D(g(n),g(m))
          -2X sum_n a(n)H_D(g(n))
          +X^2 sum_{1<=d<=D} 1/d^2.

The off-diagonal is over ordered distinct input pairs. Both centering terms
are retained. In particular, a raw gcd second-moment upper bound is not
silently treated as a bound for the centered dispersion.

Two finite Cauchy inequalities are also verified:

    |sum_d c_d (R_d-X/d)|^2 <= (sum_d c_d^2) V_D,
    (sum_d |R_d-X/d|)^2 <= D V_D.

These inequalities do not assert that V_D is small.

## Actual prime-input diagonal

For alpha>=1, S=(0,N], a(n)=1_{n prime} log n, g(n)=floor(alpha*n),
the complete diagonal term is bounded by

    (log N)^2 floor(alpha*N) [1+log(floor(alpha*N))],

uniformly for every divisor cutoff D. The proof uses injectivity of the
Beatty map and the existing first moment of the divisor function; it does
not assume any prime-pair estimate.

Thus the diagonal is O_alpha(N log^3 N). The substantive obstacle to an
improved averaged row estimate is the CENTERED OFF-DIAGONAL contribution.
No estimate establishing its required cancellation at larger divisor levels
was found in this investigation. Consequently no larger useful sieve range
or prime-pair lower bound is asserted.

A further literature-access attempt failed at DNS resolution. No external
settlement of the original conjecture has been independently verified.
