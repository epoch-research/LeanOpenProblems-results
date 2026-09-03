# Four-digit checksum screening

This is exploratory exact-integer computation, not a Lean theorem and not a
settlement of Erdős 773. No new lower or upper exponent was obtained.

For base q, the candidate roots are

    a + q*b + q^2*c + q^3*d(a,b,c),  0 <= a,b,c < q,

with zero excluded. Affine checksums use (1,a,b,c); quadratic checksums use
(1,a,b,c,a^2,ab,ac,b^2,bc,c^2), with coefficients and output reduced modulo q.
Every unordered pair, including repeats, is tested using exact integer squares.
Enumeration of a candidate is stopped once it is worse than the current best;
thus only the final minimum, not every reported intermediate count, is exact.

| q | checksum family | coefficient tuples tested | minimum repeated sums |
|---|---|---:|---:|
| 2 | affine | 2 | 0 |
| 3 | affine | 81 | 3 |
| 5 | affine | 625 | 106 |
| 3 | quadratic | 59049 | 1 |

The base-2 search stopped at its first successful class. It is the checksum
d=c, giving roots {1,2,3,12,13,14,15}. This formula cannot work at any q>=3:
the c=0 slice already contains 1,4,7,8, and 1^2+8^2=4^2+7^2.

At base 3, all 3^10 quadratic coefficient tuples were tested. The best
checksum found is d=2*(a^2+a*c+c^2) mod 3. Its 26 positive roots have
the collision 55^2+79^2=65^2+71^2=9266. Deleting a root from this finite
example does not establish a construction at arbitrarily large scales.

Scripts/results: /tmp/square_checksum_test.py, /tmp/square_checksum_test.log,
/tmp/square_checksum_results.json.

A small-base failure does not exclude success at other bases or a different
checksum family. Conversely, small-base success would not prove asymptotics.

The polynomial-reduction and primorial-sieve routes were also reconsidered.
No valid integer specialization of the formal polynomial construction was
obtained. The primorial upper bound remains compatible with the conjecture;
no near-linear selector was extracted from its counting inequalities.

Spec.lean is unchanged, with its sole admission for 0 < epsilon <= 1/3.
No proof submission has been made.
