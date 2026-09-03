# Joint Dold and predecessor congruences: verified rational comparison

This construction is now Lean-verified in
`Submission/JointDoldPredecessorComparison.lean` (327 lines), but is NOT a
proof or disproof of Erdos 68. The file compiles without warnings, has a
built olean, and contains no proof holes. All seven printed principal axiom
audits use only `propext`, `Classical.choice`, and `Quot.sound`.

Spec.lean remains unchanged with its original sorry. No complete argument
for the original conjecture was found.

This review follows PolynomialModulusRationalNotes.md and
DoldRationalComparisonNotes.md. The former does not preserve all modified
Dold congruences; the latter does not preserve predecessor congruences.
The construction below joins those two types of congruence at the cost of
larger tails. It does NOT retain the original Lambert coefficients.

## Recursive construction

Set b_0=0, b_1=1, and t_1=4. For n>=2 put

    R_n = sum_{d|n, d<n} d*b_d.

If n is prime set

    b_n=(n-1)!,   t_n=n*t_(n-1)-1.

If n is composite put

    M=n*(n-1),
    k=1-R_n+n!,
    v=n*t_(n-1)+n!-R_n-2*n,
    b_n=k+(n-1)*floor((v-n*k)/M),
    t_n=2*n+((v-n*k) mod M).

Here all division and remainders are integer Euclidean operations, with
0<=x mod M<M. These formulas are well-founded because every proper divisor
is smaller than n. Define

    F_n=sum_{d|n} d*b_d,
    c_0=c_1=0,
    c_n=F_n-n! for n>=2.

## Algebraic identities

At every n>=2,

    c_n=n*t_(n-1)-t_n.

For composite n, expand the quotient/remainder identity
M*floor((v-n*k)/M)+((v-n*k) mod M)=v-n*k. For prime n, R_n=b_1=1,
so c_n=1, consistent with the displayed recurrence.

At composite n, b_n=k modulo n-1 and n=1 modulo n-1. Consequently

    c_n=n*b_n+R_n-n! = k+R_n-n! = 1 modulo n-1.

The same predecessor congruence holds at primes because c_n=1.

For any integer sequence b, the divisor transform F_n satisfies

    F_(p^(r+1)*m) = F_(p^r*m) modulo p^(r+1)

for prime p, r>=0 and m>0. This is the existing generic theorem
DoldRationalComparison.divisorTransform_dold; it does not depend on this
particular construction. Since F_n=c_n+n! also at n=1, subtracting the
larger factorial gives exactly the target-style modified Dold congruence

    c_(p^(r+1)*m) = c_(p^r*m)+(p^r*m)! modulo p^(r+1).

## Positivity, tail bounds, rational sum

For composite n>=4, the remainder definition gives

    2*n <= t_n < n^2+n.

Induction gives t_n>=2*n for all n>=1: t_1=4, t_2=7, and a prime
step n>=3 satisfies n*2*(n-1)-1>=2*n. Thus at a composite n>=4,

    c_n = n*t_(n-1)-t_n
        > 2*n*(n-1)-(n^2+n) = n*(n-3) > 0.

At primes c_n=1. Also t_2=7<2^3 and t_3=20<3^3. At a prime n>=5,
n-1 is composite, so

    t_n=n*t_(n-1)-1 < n*((n-1)^2+(n-1))-1 < n^3.

The composite upper bound is also less than n^3. Hence

    0<t_n<n^3 for n>=2.

Telescoping the recurrence, for N>=2,

    sum_(n=2)^N c_n/n! = t_1/1! - t_N/N! = 4-t_N/N!.

Since t_N/N! tends to zero, the sum is 4, and its factorial-scaled tails
are exactly t_n. The coefficients differ from the target already at n=4:
R_4=3, M=12, k=22, v=93, b_4=22, t_4=13, c_4=67; the original Lambert
coefficient is 7.

## Scope

Thus the joint congruences, prime unit coefficients and positivity remain
compatible with a rational sum when cubic tails (quadratic at composites)
are allowed. This does not address the sharper linear composite-tail bound
of the exact target carry. It does not show those congruences are inherited
by that carry, nor prove an infinite failure of its rationality-forced
prime-gap pattern.

## Lean verification

The later continuation formalized the construction in
`JointDoldPredecessorComparison.lean`. Principal declarations include:

* `composite_tail_bounds`
* `tail_lower`, `tail_upper`
* `coeff_recurrence`, `coeff_pos`, `coeff_prime`
* `predecessor_congruence`, `coeff_dold`
* `sum_coeff`, `scaledTail_eq`, `scaledTail_bounds`
* `coefficient_four`, `comparison_properties`

`comparison_properties` packages positivity, both congruence families,
prime units, cubic scaled-tail bounds, and the exact rational sum four.
`coefficient_four` is checked using finite proper-divisor identities and
ordinary kernel-checked arithmetic, not `native_decide`.

No numerical search or submission check was run. All compilation and axiom
audits have completed; nothing is pending. The simultaneous-clearing and
positive-kernel constructions were also reviewed, but no compatible
useful-lift bound or positive small integral-form family was obtained.
There is still no complete proof or disproof of the exact conjecture
awaiting formalization.
