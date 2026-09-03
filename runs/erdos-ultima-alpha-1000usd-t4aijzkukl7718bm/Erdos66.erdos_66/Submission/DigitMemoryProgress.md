# Quantitative variable-width digit-program lower bounds

## Original conjecture status

The conjecture in Submission/Spec.lean remains neither proved nor disproved.
The original import, statement, and sorry have not been changed. No proof
submission has been made.

## New necessary condition

Fix b>=2 and set

    k_j = 64*b*j*2^j.

For every j, allow a DIFFERENT finite state type sigma_j, a different
position-dependent nondeterministic transition relation, and different
initial and accepting states. Assume only that the program recognizes
membership in A for all base-b words of length k_j, with zero padding.
Digits are read least significant first.

If A is an eventual additive basis and

    r_A(n) <= K+C log(n+2), K,C>=0,

then for EVERY sufficiently large j,

    |sigma_j| > b^(2^j).

In particular this holds for any hypothetical witness of the conjecture.
This is stronger than a fixed-width exclusion: widths may grow arbitrarily,
and the theorem imposes a quantitative lower bound on them.

A second checked statement gives

    k_j log(b) log(2)
      < 64*b log(|sigma_j|) log(k_j)

eventually. Thus the logarithm of the state count is at least a positive
constant times k_j/log(k_j), along these selected lengths.

This is a bound for the specified one-pass digit-program model. It is not
a statement about all algorithms, arbitrary multiple-pass computation,
or every possible notion of memory complexity.

## Sharper finite box bound

DigitBoxExponentExplore.lean improves the previous exponent. If b<=2^e,
then a Cartesian base-b digit box contained in A, under a representation
cap M below twice the digit range, has at most M^e elements.

The proof picks a two-point subset in each nonempty digit set D. If |D|>1,
the two-point subset has cardinality two and

    |D| <= b <= 2^e.

Complementing every coordinate gives a single ordinary-integer sum with
as many representations as the two-point box's cardinality. The original
carry-correct ordinary encoding is retained.

Consequently a length-m program of width S in base B<=2^e has

    |accepted| <= S^(m+1) M^e.

Grouping d old digits gives B=b^d and one may take e=b*d, since b<=2^b.
Unlike the previous exponent B, this exponent is only linear in d.

## Parameters and finite count comparison

At k_j=64*b*j*2^j, group digits with

    d_j = 8*2^j,
    m_j = 8*b*j,
    d_j*m_j=k_j.

The logarithmic envelope gives M_j=L(k_j+1) for one natural L. Elementary
polynomial-versus-exponential decay proves, eventually,

    M_j <= b^(2*j).

If S_j<=b^(2^j), then the grouped count bound yields

    count(A,b^k_j) <= b^((24*b*j+1)*2^j).

For j>=1 the square of this bound satisfies

    2*count(A,b^k_j)^2 <= b^k_j.

But eventual-basis status with threshold M gives

    b^k_j <= M+count(A,b^k_j)^2.

Together these force b^k_j<=2M, contradicting its eventual growth. Hence
small width is impossible at every sufficiently large selected length.
The constants are explicit and not optimized.

## Principal declarations

Erdos66DigitMemoryLower:

* grouped_prefix_card_bound
* small_width_count_bound
* eventual_width_lower_of_caps
* eventual_width_lower_of_log_cap
* witness_eventual_width_lower

Erdos66DigitMemoryLog:

* memory_inequality
* witness_eventual_memory_lower

The first general endpoint only needs eventual caps M_j<=b^(2*j) at the
selected lengths. The global logarithmic hypothesis is introduced later.

## Verification

Four production files compile and have current oleans:

* DigitBoxExponentExplore.lean
* DigitMemoryParametersExplore.lean
* DigitMemoryLowerExplore.lean
* DigitMemoryLogExplore.lean

DigitMemoryAudit.lean audits 17 declarations. Its saved log uses only
propext, Classical.choice, and Quot.sound. No production sorry or new
axiom is present.

## Why this does not settle the conjecture

The conjecture places no upper bound on digit-program width. Every finite
prefix can be recognized by a sufficiently large lookup program, so the
new lower bound alone gives no contradiction for an arbitrary set A. No
small-width description has been derived from logarithmic representation
asymptotics.

The unrestricted construction review preceding this result did not close
the finite-template compatibility gap. Distant accurate annuli and
arbitrary short-prefix patches still do not control mixed counts through
a change of template. The weighted completion route still lacks a base
with the correct all-target upper coefficient and sub-square-root deficit
counts at every fixed tolerance. No new implication supplying either
missing condition was proved.
