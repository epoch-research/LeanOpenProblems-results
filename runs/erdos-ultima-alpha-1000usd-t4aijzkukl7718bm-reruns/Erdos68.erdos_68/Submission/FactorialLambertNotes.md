# Factorial Lambert regrouping (not a solution)

`FactorialLambert.lean` verifies the following identity, using only the allowed
axioms. Write alpha for the original series and define the natural numbers

    A_m = sum_{d | m, d >= 2} m! / (d!)^(m/d).

The divisions are exact, by multinomial divisibility. Grouping the absolutely
summable family `1/(d!)^j` by `m = d*j` gives

    alpha = sum_{m >= 0} A_m/m!.

The file also verifies:

* `A_p = 1` for every prime `p`;
* `A_(2k) >= (2k)!/2^k` for every positive `k`;
* `A_(2k) >= 2k` for `k >= 2`.

Consequently these coefficients are not eventually factorial-base digits.
Their small values at prime indices do not control the carries from later
indices. This prevents directly applying the usual bounded-digit argument or
treating this regrouping as an irrationality proof.

## Why prime coefficients alone cannot suffice

There is a simple different, rational factorial series with nonnegative integer
coefficients equal to 1 at every prime index. Let

    b_1 = 1,
    b_m = 1        if m is even,
    b_m = m-1      if m >= 3 is odd,
    c_m = m*b_(m-1) - b_m   for m >= 2.

Then `c_2 = 1`, every odd `c_m` is 1, and every even `c_m` with `m >= 4`
is `m*(m-2)-1`. Thus all coefficients are positive integers, and `c_p = 1`
at every prime. Nevertheless telescoping gives

    sum_{m=2}^M c_m/m! = 1 - b_M/M!,
    sum_{m>=2} c_m/m! = 1.

This auxiliary example is not a counterexample to Erdős 68. It explains why a
new carry argument is still necessary. The auxiliary example in this note is
mathematical reasoning, not an additional Lean-verified declaration.

`Submission/Spec.lean` remains unchanged; no proof or disproof of its conjecture
has been obtained.

## Further congruence, now verified

`FactorialCongruence.lean` proves

    A_m = 1 (mod m-1),    m >= 2.

For a proper divisor d of m, put k=m/d >= 2. The multinomial coefficient

    I = (dk-1)! / ((d-1)! (d!)^(k-1))

is an integer. The total of a multinomial divides each multiplicity times
that multinomial, so dk-1 divides both (d-1)I and dI, hence divides I.
The corresponding summand (dk)!/(d!)^k equals kI. Thus every proper-divisor
summand vanishes modulo m-1; the d=m summand is 1. Lean's axiom check for
`lambertCoeff_modEq_pred` lists only propext, Classical.choice, and Quot.sound.

### The stronger coefficient conditions still allow rational sums

The following explicit auxiliary example satisfies all three properties
(prime coefficients 1, the new congruence, and the even-index lower bound).
It is NOT the original coefficient sequence. This example is mathematical
reasoning, not a new Lean theorem.

For even n >= 4 put T_n = n!/2^(n/2) and b_n = T_n+n-3.
For odd n >= 5 put b_n = n*b_(n-1)-1. Define

    c_2 = c_3 = 1, c_4 = 7,
    c_n = n*b_(n-1)-b_n     (n >= 5).

Then c_n=1 at every odd index and at 2. For even n>=6,

    c_n = T_n + n(n-1)(n-5)-2n+3 >= T_n.

The same lower bound holds at n=4. All c_n are positive integers.
For even n, T_n is divisible by n-1 (n-1 is odd, so dividing n! by a
power of 2 does not remove that divisibility). The polynomial part of
c_n is 1 modulo n-1. Thus c_n = 1 (mod n-1) at every n>=2.

Finally b_n/n! tends to zero, and telescoping gives

    sum_(n>=5) c_n/n! = b_4/4! = 7/24,
    sum_(n>=2) c_n/n! = 1/2+1/6+7/24+7/24 = 5/4.

These c_n even agree with the original A_n through n=7. The first difference
is c_8=2675 versus A_8=2591. Consequently the proved congruence, prime-index
values, and even-index growth do not, together, exclude rationality. A new
argument using more of the exact original coefficients is still required.


## A stronger obstruction: cubic perturbations can give a rational sum

The following is another auxiliary construction, NOT a disproof of Erdős 68
and NOT a Lean-verified theorem. It shows that even agreement with the exact
coefficient asymptotics is insufficient for this approach.

There are nonnegative integer coefficients C_n such that

* C_n = A_n at every odd n and at n=0,1,2;
* 0 <= C_n-A_n < n^3 for every n>=2;
* C_n = 1 (mod n-1), for n>=2;
* sum C_n/n! = 3/2.

In particular C_p=1 at every prime p, and C_n >= A_n preserves all of the
proved coefficient lower bounds. Moreover C_n/A_n tends to 1 as n tends
to infinity (with the quotient considered for n>=2).

### Construction

Set delta=3/2-alpha. The already verified bounds on alpha imply

    0 < delta < 1/4.

For the even indices n=4,6,8,... use weights

    w_n = (n-1)/n!.

Their successive ratios are exact integers:

    w_(n-2)/w_n = n(n-3),       n even, n>=6.

Starting with remainder delta, greedily subtract d_n*w_n at each such n,
where d_n is the floor of the current remainder divided by w_n. The new
remainder lies in [0,w_n). Since w_n tends to zero, telescoping gives

    delta = sum_(n>=4, n even) d_n*w_n.

The first digit d_4 is at most 1 because w_4=1/8 and delta<1/4. Every later
digit satisfies

    0 <= d_n < n(n-3).

Now put C_n=A_n+(n-1)d_n at the even indices n>=4 and C_n=A_n elsewhere.
All the stated integer, congruence, positivity, cubic-bound, and summation
claims follow immediately.

At even n, the verified lower bound A_n >= n!/2^(n/2) gives

    0 <= (C_n-A_n)/A_n < n^3 * 2^(n/2)/n! -> 0.

At odd n the difference is zero. This proves the claimed asymptotic
agreement. The construction depends on alpha through delta, but it does
not assume that alpha is either rational or irrational: the greedy
representation exists for every nonnegative real delta.

### Analytic implication and its limitation

The exponential generating function difference

    sum (C_n-A_n) z^n/n!

is entire, since its integer coefficients are O(n^3). Thus adding it to the
meromorphic factorial Lambert function preserves every pole and residue,
while making the value at z=1 rational. These data alone therefore cannot
prove irrationality either. This does not preserve the original function's
more restrictive growth away from its poles, nor its exact coefficients;
no conclusion about the original value follows from this construction.

## Canonical term-by-term carrying does not preserve the congruence

A candidate for reducing the large A_n to bounded coefficients is to take
ordinary factorial digits of each rational summand separately. Define

    F_n = sum_(d=2)^n floor(n!/(d!-1)),
    c_n = F_n - n F_(n-1).

This is NOT the same coefficient sequence as A_n. In particular, the
congruence A_n=1 (mod n-1) cannot simply be transferred to c_n. Already

    F_5 = 120+24+5+1 = 150,
    F_6 = 720+144+31+6+1 = 902,
    c_6 = 902-6*150 = 2,

whereas A_6=1+90+20=111. Hence c_6 is not 1 modulo 5, although A_6 is.
This exact finite calculation rules out that congruence-preserving claim;
it says nothing against the original irrationality conjecture.

## Verified integer-tail descent criterion

`FactorialTailCriterion.lean` now proves the following independent lemma. For
integer coefficients c_k, put

    T_n = n! * (sum_(k>=0) c_k/k! - sum_(k=0)^n c_k/k!).

If, for all sufficiently large n,

    n divides c_(n+1)-1,
    0 < T_n < n-1,

then the sum is irrational. This is the theorem
`FactorialTailCriterion.irrational_of_small_congruent_tails`; its axiom check
lists only propext, Classical.choice, and Quot.sound.

The proof does not assume integrality of the tails: it derives it under the
hypothesis that the total sum is rational, using factorial divisibility to
clear the fixed rational denominator and every finite-prefix denominator.
The recurrence

    T_(n+1) = (n+1)*T_n - c_(n+1)

then gives n | T_(n+1)-T_n+1. Integer tails in the stated interval satisfy
1 <= T_n <= n-2. Thus the divisible difference lies strictly between -n and
n, so it is zero. This forces T_(n+1)=T_n-1 forever, contradicting positivity.
The standalone arithmetic statement is `integer_tail_descent`.

The original Lambert coefficients satisfy the congruence, but NOT the small
tail condition: their large even-index contributions cannot be omitted.
No application of this criterion to the original series has been obtained,
and this auxiliary result does not settle the conjecture.

`LambertTailBarrier.lean` also now verifies that failure explicitly. For the
original coefficients A_m, it proves

    T_(2k+5) >= 2k+5,   for every natural k.

Consequently the small-tail inequality T_n<n-1 cannot hold eventually.
The proof keeps just the d=2 contribution to A_(2k+6), obtaining
T_(2k+5) >= (2k+5)!/2^(k+3), and then uses an elementary factorial bound.
The theorem names are `factorial_lambert_tail_large` and
`factorial_lambert_not_eventually_small_tail`. Both have only the permitted
axioms. This rules out direct use of the new criterion on these coefficients;
it does not rule out another, substantially different representation.



## Verified rowwise representation and small tails

`Submission/RowwiseFloors.lean` now verifies the rowwise construction discussed
above. It is a different coefficient sequence from A_n, but has the SAME sum.
For all N, define

    F_N = sum_(k=2)^N floor(N!/(k!-1)),
    c_0 = F_0 = 0,
    c_(N+1) = F_(N+1) - (N+1) F_N.

The verified results are:

* `rowCoeff_nonneg`: c_N >= 0;
* `rowCoeff_partial`: sum_(k=0)^N c_k/k! = F_N/N!;
* `hasSum_rowCoeff` and `sum_rowCoeff`: the coefficient series sums to alpha;
* `rowCoeff_scaledTail`: its scaled tail is T_N=N!*alpha-F_N;
* `rowCoeff_scaledTail_small`: 0<T_N<N-1 for every N>=3;
* `rowCoeff_six`: c_6=2.

The small-tail proof uses two elementary estimates. Rounding down each of the
N-1 included rows loses at most N-2 in total, because the k=2 row is exactly
N! and has no rounding loss. The original scaled omitted tail is at most
3/(N+1)<1 for N>=3. Positivity follows from the strictly positive omitted tail.
The error after dividing by N! is bounded by 1/(N-1)!, which also gives the
convergence used in the sum identity.

`irrational_of_eventual_rowCoeff_congruence` is only a CONDITIONAL application:
if n divides c_(n+1)-1 eventually, the existing descent criterion proves alpha
irrational. No such eventual congruence is proved. The example c_6=2 refutes
its validity at every index; it does not by itself refute an eventual claim.

All the printed axiom checks for this file list only propext, Classical.choice,
and Quot.sound. The original conjecture in Spec.lean is unchanged.
