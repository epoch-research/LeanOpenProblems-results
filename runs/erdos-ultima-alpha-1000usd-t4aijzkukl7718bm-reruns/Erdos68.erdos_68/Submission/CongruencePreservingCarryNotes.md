# Carrying the actual target while preserving prime units and congruences

This is verified auxiliary progress, NOT a settlement of Erdős 68.
Spec.lean is unchanged and still contains its original sorry. No proof or
disproof has been obtained or submitted.

Both CongruencePreservingCarry.lean and CarriedRationalPrimePattern.lean
compile without warnings, have built oleans, and contain no proof holes.
Their printed principal axiom audits use only propext, Classical.choice,
and Quot.sound.

## Actual target construction

Let alpha=sum_(n>=2) 1/(n!-1), let a_n be the Lambert coefficients, and put

    L_n=sum_(m=0)^n a_m*n!/m!,
    y_n=n!*sum_(k=2)^n 1/(k!-1)-L_n.

The Lean definitions use r=n-3. Define integer carries h_3=0 and for n>=4

    h_n=n*h_(n-1)                         if n is prime,
    h_n=h_(n-1)+(n-1)*floor((y_n-h_(n-1))/(n-1)) otherwise.

Set z_n=y_n-h_n and

    c_n=a_n+h_n-n*h_(n-1)  for n>=4,
    c_n=a_n               for n<4.

Unlike the earlier comparison constructions, this one preserves the
original sum exactly.

## Verified properties

CongruencePreservingCarry.lean proves:

* the exact natural prefix recurrence L_(n+1)=(n+1)L_n+a_(n+1);
* z_3=16/5 and every z_n>=0;
* at composite indices, 0<=z_n<n-1;
* at prime indices, z_n=n*z_(n-1)+1/(n!-1);
* c_n>0 for all n>=2;
* c_p=1 at every prime p;
* n-1 divides c_n-1 for all n>=4;
* sum c_n/n!=alpha;
* the exact finite-prefix and scaled-tail identities.

Writing T_n=n!*alpha-(L_n+h_n), the original scaled tail U_n gives

    T_n=U_n+z_n,       0<U_n<=3/(n+1).

Consequently

    0<T_n<n^2       for every n>=3,
    0<T_n<n         for every nonprime n>=4.

At a prime p>=5, use T_p=p*T_(p-1)-1 and the composite predecessor bound.
Normalized tails are summable by comparison with n^2/n!, and telescoping
proves the original-sum identity. The initial coefficients sum to 2/3.

## Rationality would force a specific prime-gap pattern

CarriedRationalPrimePattern.lean verifies the following necessary conditions.
If alpha=q is rational, the T_n are integers for n>=q.den. At a prime p
with p>=5 and p-1>=q.den, the congruence at p and the unit recurrence imply
p divides T_(p+1)+2. The bound 1<=T_(p+1)<=p therefore forces

    T_(p+1)=p-2.

In particular the reset value is p-2, NOT p.

For consecutive primes p<s<2p meeting the same size condition, the
congruence and the nonprime linear bounds force

    T_n=2p-1-n               for p<n<s,
    T_s=s*(2p-s)-1.

These are conditional identities. They do NOT themselves contradict
rationality. In particular when s/p is near one, the last tail is near s^2,
which is compatible with the newly verified quadratic upper bound.

## Remaining gap

The construction does not meet the earlier subquadratic-tail criteria.
The general hypothesis package (positive coefficients, prime units,
predecessor congruences, and quadratic tails) is compatible with rational
sums, as verified separately in QuadraticTailComparison.lean.

No argument excluding the displayed prime-gap pattern for these exact
carried coefficients has been proved. No uniform improvement of the prime
tail bound by a fixed factor below one, or other applicable estimate, has
been established. The original conjecture remains unproved and undisproved.

## Sharpness under rationality and a fixed-factor criterion

The same prime-pattern file also verifies `rational_near_quadratic`:
if alpha is rational, then for every K>=1 and M there is a prime s>=M with

    (K-1)*s^2 < K*T_s.

The proof uses divergence of prime reciprocals through the existing
close-prime-pair lemma. Choose a consecutive pair inside such a close pair
and apply the exact formula T_s=s*(2p-s)-1. Thus the quadratic coefficient
one is necessary along a subsequence under rationality, not merely an
artifact of the upper-bound proof.

The contrapositive is formalized as `irrational_of_prime_fraction_bound`:
if there are fixed K>=1,N such that every prime p>=N satisfies

    K*T_p <= (K-1)*p^2,

then the original series is irrational. This is a sufficient condition
only. No proof of its tail-bound hypothesis has been obtained. In
particular the verified estimate T_p<p^2 does not imply any such uniform
fixed-factor improvement.
