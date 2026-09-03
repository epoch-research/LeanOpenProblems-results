# A rational comparison satisfying the Dold congruences

This is verified auxiliary work, NOT a proof or disproof of Erdős 68.
Spec.lean remains unchanged with its original sorry. The comparison below
is a DIFFERENT series and cannot be used as a disproof of the target.

DoldRationalComparison.lean compiles without warnings, has a built olean,
and its four principal axiom audits use only propext, Classical.choice,
and Quot.sound.

## Construction

Define integral primitive coefficients b_n and integral tails t_n together.
Put b_1=1 and t_1=2. At n>=2 let

    R_n=sum_{d|n,d<n} d*b_d.

At a prime n set

    b_n=(n-1)!,   t_n=n*t_(n-1)-1.

At a composite n set

    v_n=n*t_(n-1)+n!-R_n-2,
    b_n=floor(v_n/n),   t_n=2+(v_n mod n).

The division and remainder are integer Euclidean operations, including
when v_n is negative. Let

    F_n=sum_{d|n} d*b_d,
    c_n=F_n-n!  (n>=2),   c_0=c_1=0.

## Verified properties

* c_n=n*t_(n-1)-t_n for n>=2.
* c_n>0 for n>=2 and c_p=1 at every prime p.
* t_n>=2 for n>=1.
* t_n<=n+1 at every composite n>=2.
* t_n<=n^2 for every n>=2.
* sum_{n>=0} c_n/n!=2.
* The actual factorial-scaled tails of this series equal t_n for n>=1.
* For every prime p, r>=0, and m>0,

      c_(p^(r+1)*m) == c_(p^r*m)+(p^r*m)!  (mod p^(r+1)).

The last congruence has exactly the singleton correction occurring for the
original Lambert coefficients in LambertDoldCongruence.lean.

## Dold congruence proof

For ANY integral sequence b, its divisor transform F_n=sum_{d|n} d*b_d
satisfies F_(p^(r+1)*m)==F_(p^r*m) modulo p^(r+1). Every divisor of the larger
index which is not a divisor of the smaller index is divisible by p^(r+1).
This divisor fact is proved by induction, using primality and cancellation.
The difference of the two divisor sums is therefore divisible by that power.
Subtract the larger singleton factorial to obtain the displayed congruence
for c. No external computation or assumed congruence is used.

The tail bounds make t_n/n! summable. The coefficient recurrence telescopes,
proving the rational sum and the exact tail identity.

Principal declarations:
* divisorTransform_dold
* coeff_dold
* coeff_pos
* coeff_prime
* composite_tail_bounds
* tail_upper
* sum_coeff
* scaledTail_eq

## Precise limitation

This comparison shows that the Dold congruences, prime unit values, positivity,
and these polynomial tail bounds do not suffice for irrationality. It does
NOT preserve the predecessor congruence n-1 | c_n-1, the exact original
coefficients, or the target sum. Its composite bound is n+1, not the sharper
strict bound n of CongruencePreservingCarry. No implication for the exact
conjecture follows from this comparison.

The boundary-lattice route was also reviewed again. Denominator clearing
still does not supply a nonzero value or uniformly controlled useful minima.
No new nonvanishing or irrationality argument resulted from that review.
