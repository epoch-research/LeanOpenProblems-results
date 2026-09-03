# A short formal histogram collision

This does NOT settle Erdős 773. The sole admission in `Spec.lean` remains at
line 1515, covering 0 < epsilon <= 1/3. The conjecture statement and its import
have not been changed.

## Verified construction

`FormalHistogramObstacle.lean` contains four degree-eight digit words, listed
from constant coefficient to leading coefficient:

    [6,18,4,14,22,6,2,4,1]
    [22,14,6,18,6,4,4,2,1]
    [18,6,4,22,14,6,4,2,1]
    [14,22,6,6,18,4,2,4,1]

Every lower coefficient is even, every constant coefficient is 2 modulo 4,
and every leading coefficient is 1. The four lists have identical histograms,
common digit sum 77, and common sum of squared digits 1113.

The identity P0(X)^2 + P1(X)^2 = P2(X)^2 + P3(X)^2 is FORMAL: Lean proves it
by polynomial normalization (`ring`). It is not an identity only at one base.
Consequently every integer base B > 77 yields a nontrivial collision. All digits
are less than B/2, and the common digit sum is less than B.

At B=80 the root gcd is exactly 2. More strongly, at B=308*(t+1), the root gcd
is exactly 2 for every natural t. This is an unbounded-base primitive family.
Its proof uses the polynomial Bezout identity

    (15B+47) P2(B) + (27B+39) P3(B)
      = 308 + (29B+45) P0(B) + (13B+37) P1(B).

Thus the common gcd divides 308. Modulo 308, the four values are respectively
6,22,18,14, forcing gcd 2. All four values are even.

The file compiles with the usual Lean stack setting. Printed axiom audits for
`not_sidon` and `primitive_family` report exactly the three allowed axioms.

## Algebraic origin and important distinction

Let i^2=-1, and put

    Q = X^2 + (3-i)X + (3+i),
    R = X^6 + (5-i)X^3 + (5+i).

Then (1+i)QR=P0+iP1 and (1+i)conj(Q)R=P2+iP3, where conjugation acts on
coefficients. This explains the norm identity and the digit permutations.

Each individual Pj is Eisenstein at 2, but the pair polynomial Pj+iPk need
not be irreducible over Gaussian rationals. The prime 2 ramifies in Gaussian
integers. Consequently a blanket formal-Sidon argument using individual
Eisenstein irreducibility at 2 is invalid.

Do NOT transfer this counterexample to Eisenstein at 3: 3 is inert in Gaussian
integers, and the corresponding pair-polynomial irreducibility argument is
different. The earlier base-81 histogram examples have integer-evaluation
collisions, not formal polynomial collisions. No proof or disproof of the
base-three, small-total-digit-sum construction was obtained in this session.

## Other work completed

`ParametricSphereObstacle.lean`, previously pending, now compiles as a single
file with `lean -j 1 -s 65536`. Its four main audits are clean. The new short
formal example is stronger for testing the base-two candidate, so further
large carry-graph searches for that purpose are unnecessary.

Exploratory exact carry graphs and floating-point LPs at base 81 for the
base-three candidate are in `/tmp/p3_small_sum.py` and
`/tmp/min_sphere_cost.py`. No new counterexample was extracted. An attempted
integer optimization did not return a usable result. These computations are
not proofs of nonexistence and are not used by any Lean theorem.

## Later update: the base-three candidate is also obstructed

`InertSmallSumObstacle.lean` and `InertSmallSumResearchNotes.md` give a short
fixed-degree family at B=864*(t+6), with identical histograms, Eisenstein at 3,
and common digit sum 2305+B/2 < B. Its roots have colliding square sums.
At B=47806848*(u+1), their gcd is exactly 3. The mechanism uses rational
polynomial coefficients shifted into empty adjacent digit positions; it does
not contradict formal Gaussian Eisenstein irreducibility. See the new notes
and audit log for the latest verification status.
