# Positive weights on natural-number nodes

This is auxiliary analytic progress, not a settlement of Erdős 68.
`NonSquareFallingWeights.lean` compiles and its olean has been built. Its
four printed principal axiom audits contain only propext, Classical.choice,
and Quot.sound. Spec.lean is unchanged.

## Verified estimates

In original indices n>=2, let

    r_N(n)=(n-2)(n-3)...(n-N-1),

with empty product 1. At natural n this is the descending factorial
(n-2).descFactorial N. It vanishes for 2<=n<=N+1 and is positive thereafter.
It need not be a square or nonnegative at every real input.

For every integer j>=1, the file proves

    0 < sum_(n>=2) r_N(n)^j/(n!)^j
      < 3/((N+1)(N+2))^j.

The exact shifted-term identity is

    r_N(N+k+2)^j/((N+k+2)!)^j
      = [1/((N+k+2)(N+k+1)k!)]^j.

The upper bound follows by comparison with
((N+1)(N+2))^(-j) sum_(k>=0) 1/k!, using exp(1)<3. The finite prefix is
zero. Summability, positivity, and convergence to zero as N increases are
all verified, not inferred from external calculations.

Using 1/(n!-1)<=2/n!, the file also proves

    0 < sum_(n>=2) r_N(n)/(n!-1) < 6/((N+1)(N+2)),

and verifies convergence of these weighted original sums to zero.

Main names:

* `weight_sum_bounds`
* `tendsto_weight_sum`
* `originalWeight_sum_bounds`
* `tendsto_originalWeight_sum`

The Lean indexing is n>=0, original row n+2, with exponent r+1.

## The missing arithmetic link

The weights have integer values at every original row. This does NOT imply
that a weighted infinite sum is an integer, or a rational with fixed
controlled denominator, merely because the unweighted sum is rational.
No representation of this family as A_N*alpha-B_N with integral A_N,B_N
has been established.

For a columnwise telescoping construction, writing

    r_j(n) = A - [n^j H_j(n-1)-H_j(n)]

would impose polynomial-image conditions. The same A must work for every
column, and the total boundary must be integral. The positivity estimates
above do not establish those conditions or control their arithmetic cost.
They must not be treated as a proof of irrationality.

As an elementary comparison (mathematical note, not a new Lean theorem),
the positive rational sequence

    b_0=1,
    b_n=(n+2)/(n+3)! = 1/(n+2)!-1/(n+3)!  (n>=1)

has total sum 7/6. Its descending-factorial-weighted sums are positive and
tend to zero as well: for N>=1 the n=0 term vanishes, and b_n<=1/(n+2)!,
so the verified factorial-weight estimate applies. Thus positivity and
smallness of this kind alone cannot exclude a rational unweighted sum.
This comparison is not the original factorial-minus-one sequence.

No complete proof or disproof of Erdős 68 has been obtained or submitted.
