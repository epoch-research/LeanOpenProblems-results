# Reduced-denominator clearing of fixed-length reciprocal blocks

This is verified auxiliary progress, not a settlement of Erdős 68.
`Submission/Spec.lean` is unchanged and still contains its original sorry.
No proof or disproof of the conjecture has been submitted.

`FiniteBlockClearing.lean` compiles without warnings and has a built olean.
Its printed principal axiom audits use only propext, Classical.choice,
and Quot.sound. It contains no holes.

## A cancellation-aware arithmetic lemma

For nonzero integer denominators b,d_i, if

    N * (1/b + sum_i 1/d_i)

is an integer, then

    b divides N * product_i d_i.

The proof clears the product of the other denominators and isolates 1/b.
It does NOT assume that b, or any other individual denominator, divides N.
This is `first_denominator_dvd`.

## Application to consecutive factorial-minus-one rows

For k>=2 and J>=0 put

    block(k,J) = sum_(i=0)^J 1/((k+i)!-1),
    R(k,J) = product_(i=1)^J (((k+1)...(k+i))-1).

If N*block(k,J) is an integer, then

    k!-1 divides N*R(k,J).

Indeed (k+i)!-1 is congruent to ((k+1)...(k+i))-1 modulo k!-1.
This is `block_integral_forces_dvd`, with no restriction on cancellation
within the block.

If N=(Ck)!, write

    (Ck)! = B(C,k) (k!)^C,
    0<B(C,k)<=2^(C^2*k),

using the existing factorial-block coefficient. Coprimality with k! then
implies

    k!-1 divides B(C,k)*R(k,J).

For fixed J the remaining product is polynomial in k. The formal proof
uses the deliberately coarse exponential bound

    0<R(k,J)<=2^(J^3)*(2^(J^2))^k.

Thus integrality forces

    k!-1 <= 2^(J^3)*(2^(C^2+J^2))^k,

which fails eventually by factorial growth.

## Verified conclusions

* `eventually_block_not_integral`: for fixed C,J, (Ck)!*block(k,J) is
  nonintegral for all sufficiently large k.
* `eventual_reduced_clearing_index_gt_linear`: for fixed C,J, eventually
  every N with denominator(block(k,J)) dividing N! satisfies Ck<N.
  This concerns the actual reduced denominator.
* `eventually_prefix_pair_not_integral`: partial sums whose cutoffs differ
  by J+1 cannot both be integral at scaling (Ck)! eventually.

The partial-sum helper is

    partialSum(k)=sum_(i=0)^(k-1) 1/(i!-1).

The i=0,1 terms are zero in Lean, so for k>=2 this agrees with the original
partial sum through index k-1.

## Moving cutoffs with bounded jumps

`no_bounded_step_cutoff` proves that no K:N->N can satisfy all of:

    K(n) -> infinity,
    K(n)<=K(n+1)<=K(n)+B eventually,
    n<=C*K(n) eventually,
    denominator(partialSum(K(n))) divides n! eventually,

for fixed C,B. Here cancellation within the whole removed prefix is allowed.

A positive cutoff jump has length J+1<=B. Both neighboring prefixes would
be integral at the common scaling ((C+1)K(n))!, contradicting the uniform
finite collection of fixed-block results. The cutoff must therefore be
constant eventually, contradicting its divergence.

## Scope and unresolved step

This closes a cancellation loophole for bounded-step moving-prefix
strategies. It does not exclude unbounded cutoff jumps, variable-length
blocks without the stated bounds, signed corrections, or other coefficient
representations. Rationality of the original infinite sum does not imply
that its finite prefixes have integrally cleared reduced denominators in
the range used here.

Consequently this is an obstruction to one proposed method, NOT an
irrationality proof. No target representation simultaneously satisfying the
known congruence and small-tail hypotheses has been obtained. The original
conjecture remains unproved and undisproved in this work.
