# Joint root-and-square binary digit moments: verified obstruction

The original Erdos 773 conjecture is NOT settled. Spec.lean was not changed
and retains its single admission for 0 < epsilon < 1/3. Its proved eventual
lower bound remains M(N) >= N^(2/3). No proof submission was made.

## New clean module

Submission/JointPrimeDigitMoments.lean imports the already clean
Submission.PrimeMomentCollisions, not the admitted Spec theorem.
It compiles without warnings or admissions and has a built olean.
All six printed axiom audits use only propext, Classical.choice, and
Quot.sound (the square bit-length bound uses only propext).

Log: /tmp/joint-prime-digit-moments.log

## Main quantitative result

For every natural k, put

    L = 2^22 * (k+1)^2 * (log2(k+1)+1)^2.

There exist four distinct primes a,b,c,d, all at least 5 and strictly below
2^L, with

    a^2 + b^2 = c^2 + d^2.

For every j<k, all four roots have equal binary positional moments

    sum_{i<L} bit_i(n) * i^j,

and all four SQUARES have equal binary positional moments

    sum_{i<2L} bit_i(n^2) * i^j.

The square_bit_bound theorem verifies that n<2^L implies n^2<2^(2L).
Thus the square statistic covers the entire square, not just its low L
bits. The words may be padded by leading zeros; no claim of equal
unpadded word length or of base-independent histogram equality is made.

The public theorem is joint_prime_collision_quadratic_log, in namespace
Erdos773.JointPrimeDigitMoments. The definition moments packages the two
statistics as a pair of naturals.

For each FIXED k, eventually_joint_prime_collisions also proves this
phenomenon at EVERY sufficiently large length m+1.

## Formal non-Sidon corollaries

primeJointClass L k a consists of primes n>=5, n<2^L, whose first k joint
moments match those of a. The following are verified:

* collision_class_not_sidon: a collision witness gives a genuinely
  non-Sidon square-value class.
* joint_prime_class_obstruction: such a bad class exists at the displayed
  explicit length L.
* eventually_joint_class_obstruction: for fixed k, a bad class exists at
  every sufficiently large length.

These assertions concern SOME class, not every class. No lower cardinality
for a bad class beyond its four distinct witnesses is asserted. They do
not exclude selecting a specially chosen class or a large Sidon subclass.
In particular they are not a negation of the original conjecture.

## Quantitative proof

For L>=2, each root or square moment is at most L^(2k). Recording k of each
therefore takes at most

    (L^(2k)+1)^(2k) <= L^(2k(2k+1))

colors. Apply the existing prime-color collision theorem, whose entropy
criterion comes from the proved primorial Sidon upper bound.

Writing K=k+1, ell=log2(K)+1 and q=2k(2k+1), the verified estimates are

    q+1 <= 4 K^2,
    log L <= 26 ell,
    log 128 + (q+1) log L <= 111 K^2 ell,
    512 log(L log 2) <= 13312 ell,
    L log 2 >= 2^21 K^2 ell^2.

The strict numerical inequality 111*13312 < 2^21 proves the entropy
condition. This is an exact Lean argument, not a numerical search.

The only development error was a rewrite applying two_mul and pow_add
to an inner exponent before the intended outer exponent. Simultaneous
simp only [two_mul, pow_add] resolved it. The final module has no
elaboration error or unproved hypothesis.

## Submission state

Spec.lean still has SHA-256

    257d2e55d464b8ea5a35ca7f1257dc2f59e682772c2f52fa771ee4bfdf9b8940

Its theorem is at line 17276 and its sole sorry is at line 17287. The
original statement and sole import were not modified. No new actual
Sidon exponent or fixed-power upper bound was obtained.
