# Two-scale signed minorant — not a settlement

Submission/Spec.lean remains unchanged with its original sorry. No proof
of the conjecture, negation, or sufficient prime-pair lower bound has been
obtained.

## New verified file

Submission/SignedSmoothMinorant.lean
Namespace: Erdos972SignedSmoothMinorant.

Write S_t(n)=smoothMangoldt(t,n), with the existing exceptional-unit
subtraction, and define

    F_t(n) = S_t(n)-S_(2t)(n).

### Exact doubling and pointwise sign

For n!=0, expDivisorSum_double proves

    E_(2t)(n) = E_t(n) * product_{p|n, p prime} (1+exp(-t log p)).

If n is neither 0 nor 1 and is not a prime power, it has distinct prime
factors p,q with pq|n. The inequalities

    log p+log q <= log n,
    exp(-t log p)+exp(-t log q) >= 2-t log n

show that the doubling product is at least 2 when t>0 and t log n<=1.
All its remaining factors are at least one.

The following are proved:

* signedSmooth_nonPrimePower_nonpos:
  F_t(n)<=0 for non-prime-powers in this finite parameter window.
* signedSmooth_primePower:
  if n is a prime power, then exactly

      F_t(n) = (1-exp(-t*Lambda(n)))^2/(2t).

* signedSmooth_le_mangoldt:
  F_t(n)<=Lambda(n) whenever t>0 and t log n<=1.
* signedSmooth_pos_iff:
  in the same regime, F_t(n)>0 iff n is a prime power.

The last statement concerns POSITIVE support; it does not assert that F_t
vanishes on all other numbers. Proper prime powers are not identified with
primes. The cases n=0 and n=1 are included correctly.

### Retained signed divisor identity

signedSmooth_divisor_identity proves, for t>0 and every n,

    F_t(n) = -[sum_{d|n} mu(d)*(1-exp(-t log d))^2]/(2t).

This keeps the Mobius signs. It is not a signed mean-value estimate.

The original decaying coefficient, before subtracting its constant part
using the Mobius divisor identity, is proportional to

    exp(-x) - exp(-2x)/2.

signed_coefficient_bounds proves, for x>=0,

    exp(-x)/2 <= exp(-x)-exp(-2x)/2 <= exp(-x).

Thus this subtraction changes that damping coefficient only by a bounded
factor. The statement does not prove a lower bound on an actual signed
arithmetic tail.

### Finite weighted comparison

weighted_signed_minorant sums the pointwise inequality against arbitrary
nonnegative weights and an arbitrary natural output map, provided every
output in the finite sum satisfies t log(output)<=1.

No positive lower bound for this signed sum at prime-input weights is
asserted. In particular, fixed-positive-parameter mean limits cannot be
applied with a varying parameter t bounded by 1/log N without additional
uniform estimates. Neither the positive-support characterization nor the
finite weighted comparison settles the prime-pair conjecture.

## Verification

The new file compiles to
.lake/build/lib/lean/Submission/SignedSmoothMinorant.olean.
All seven principal declarations audit with only propext,
Classical.choice, and Quot.sound. There are no sorry declarations in the
new file. The original conjecture and its imports were not changed.
No incomplete proof was submitted.
