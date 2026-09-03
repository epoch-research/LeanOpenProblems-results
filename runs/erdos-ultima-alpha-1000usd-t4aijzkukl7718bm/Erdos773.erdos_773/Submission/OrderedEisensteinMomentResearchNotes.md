# Ordered Gaussian--Eisenstein words with common first two moments

## Main problem still unresolved

This continuation does NOT settle Erdős 773. The statement and admission in
`Submission/Spec.lean` were not edited. The strongest unrestricted lower
exponent remains 2/3. No fixed-power upper bound below one was proved.

Main-file SHA-256:

    f019ff3791c89bbea24fd9b031eb92f7b676baa4b1ff9cebe9f2356121aa6ff0

The new results address the combined digit criterion that the previous
ordered tensor examples did not cover. They are obstructions to that
criterion, not counterexamples to the original asymptotic conjecture.

## Two clean verified modules

Both modules import only `FormalConjecturesUtil`. Both compile without
warnings, errors, admissions, or extra axioms, and have built oleans.
All printed audits use only propext, Classical.choice, and Quot.sound.

1. `OrderedEisensteinMomentCollision.lean` (823 lines)
   Namespace: `Erdos773.OrderedEisensteinMomentCollision`.
   Log: `/tmp/ordered-eisenstein-moment-build.log`.

2. `OrderedEisensteinOneModSix.lean` (992 lines)
   Namespace: `Erdos773.OrderedEisensteinOneModSix`.
   Log: `/tmp/ordered-eisenstein-one-mod-six.log`.

The second module gives the stronger arithmetic scope and a packaged
`combined_prime_obstruction` theorem.

## Exact combined properties

In both modules four canonical words have:

* Constant digit exactly 6.
* Leading digit exactly 1.
* All lower digits positive and divisible by 6.
* Strictly increasing LOWER digits. The final leading digit 1 is excluded
  from this order assertion.
* Equal digit sum and equal squared-digit sum.
* Positive pairwise distinct integer evaluations below the stated height.
* A nontrivial equal sum of their evaluated squares, hence non-Sidonness.

Thus the lower-coefficient and endpoint hypotheses of the previously proved
formal Gaussian--Eisenstein construction hold. The new collisions are carry
collisions, not formal polynomial identities. No automatic specialization of
formal Sidonness is used.

The moments here are powers of DIGIT VALUES, not positional moments. Only
orders zero, one, and two are asserted. No common complete histogram is
asserted: strict order and a common histogram would identify all the words.

## First family: 43 digits

For every natural u >= 10^12 use radix B=600u-1. The degree is 42 and every
root is below B^43. The common digit sum and squared-digit sum are

    606u + 18303030303013,
    78012u^2 + 92160000000000u + 83818397839783995233264809.

The discrepancy at an arbitrary radix X is

    8 f(X) g(X) X^42 (600u-X-1),

where

    f(X)=6X^2-12X^3+6X^4,
    g(X)=100X^12-101X^18+X^24.

The public APIs include `endpoint_digits`, `lower_increasing`,
`lower_divisible`, `canonical`, `common_sum`, `common_norm`,
`root_injective`, `root_positive`, `root_height`, `discrepancy`,
`square_collision`, and `not_sidon`.

## Second family: 50 digits, bases 1 modulo 6, and prime bases

For every natural t use

    u=t+10^24,
    B=6000u+1.

The degree is 49 and every root is below B^50. All properties hold for EVERY
t>=0, with no additional large-parameter hypothesis. `base_mod_six` checks
B mod 6 = 1. In fact all these bases are 1 modulo 6000.

The common digit sum is

    5502t + 5501399939993999399939994001.

The common squared-digit sum is

    8256492t^2 + 16512974200800000000000000000000t
      + 8256482877957028779570287795702877957042333868297405129.

The discrepancy at an arbitrary radix X is

    8 f(X) g(X) X^49 (6000(t+10^24)-X+1),

where

    f(X)=6X^2-18X^3+18X^4-6X^5,
    g(X)=10000X^14-10001X^21+X^28.

`prime_bases_unbounded` proves, for every natural L, the existence of t with
L < base(t) and Nat.Prime(base(t)). It uses Mathlib's proved
`Nat.exists_prime_gt_modEq_one` at modulus 6000, then writes the resulting
prime as 6000(t+10^24)+1. No numerical primality guess is made.

`combined_prime_obstruction` packages, at such an arbitrarily large prime
base, all endpoint, divisibility, order, canonical-digit, common-moment,
root-injectivity, root-height, positivity, and non-Sidon conclusions.
The word length is FIXED at fifty as the prime radix grows.

## Algebraic source

In a commutative ring, write K=X+1 or K=X-1 and put

    A = X^(m+n) + u a X^n + v d X^m + K a d,
    U = f(u X^n + K d),
    V = g(v X^m + K a),
    W = -K f g,
    F(sigma,tau) = A + sigma U + tau V + sigma tau W.

Then

    F(+,+)^2 + F(-,-)^2 - F(+,-)^2 - F(-,+)^2
      = 8 f g X^(m+n) (uv-K).

This follows by expansion, or from the real and imaginary components of
Gaussian products. The Lean files verify the actual digit identities by
`ring`; external symbolic calculations are not trusted certificates.

For the second family m=7, n=42, v=6000, K=X-1, and

    a_i = 6+60 i^2,  i=0,...,6,
    f_i = [0,0,6,-18,18,-6,0],
    d(X) = -sum_{j=0}^5 10000^j X^(7j),
    g(X) = 10000 X^14 - 10001 X^21 + X^28.

The fine perturbation is orthogonal to the quadratic fine background. The
coarse perturbation is orthogonal to the geometric coarse background and
to its neighbor form. These balances produce equal first two digit-value
moments. The strongly separated coarse scales and the offset u>=10^24
make all the lower digits positive and increasing. These inequalities,
like the identities, are proved exactly in Lean.

## Scope that remains open

* Neither family has a common complete histogram or uses every member of
  the exact allowed alphabet. They do NOT refute
  `AllowedAlphabetCandidate.near_linear_of_eventually_sidon`'s hypothesis.
* Pairwise coprimality and primality of the ROOTS are not asserted.
  The primality theorem concerns the RADIX only.
* No higher-order digit-moment obstruction with all these combined
  Gaussian--Eisenstein conditions has been proved here.
* A collision in one class does not exclude another class or a large Sidon
  subclass. These modules provide no unrestricted Sidon exponent gain and
  no negation of the original conjecture.

The final main-file check is `/tmp/spec-ordered-eisenstein-check.log`; its
admission warning is expected and is not completed verification. No proof
submission was made.
