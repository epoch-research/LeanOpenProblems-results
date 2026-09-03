# Exact full allowed-alphabet candidate: count and conditional transfer

The original conjecture remains UNSETTLED. Spec.lean is unchanged and still
has one admission for 0 < epsilon < 1/3. No proof submission was made.

## New verified module

`AllowedAlphabetCandidate.lean` imports only FormalConjecturesUtil. It
contains no admissions, warnings, or extra axioms. All seven printed audits
use only propext, Classical.choice, and Quot.sound.

Build log: /tmp/allowed-alphabet-candidate.log
Olean: .lake/build/lib/lean/Submission/AllowedAlphabetCandidate.olean

## Exact carrier

For h>=0 let B=6h+7. For each permutation sigma of Fin h, take the
constant-first word

    [6, 6*(sigma(0)+2), ..., 6*(sigma(h-1)+2), 1].

Its lower digits use EVERY allowed positive multiple of six below B,
exactly once. The constant digit is 6 and the leading digit is 1. Define

    height(h) = (6h+7)^(h+2).

`canonical_digits`, `word_length`, `root_pos`, and `root_lt_height` check
that every word is a positive canonical integer representation below this
height. `word_perm` states exact permutation of the common alphabet.
`root_injective` uses canonical radix injectivity. Therefore `roots_card`
and `squares_card` both give exactly h! members. Integer square-Sidonness
is NOT asserted by these facts.

## Quantitative count and interpolation

`factorial_power_lower` proves

    height(h+1)^(1-epsilon) <= h!

under explicit hypotheses h>=3, 0<epsilon<1, epsilon*h>=6, and
 epsilon*log(h)>=74. The proof uses Mathlib's proved Stirling lower bound,
not a numerical asymptotic estimate. `eventual_factorial_power` supplies
these hypotheses eventually for each fixed epsilon in (0,1).

The successor height is deliberate. If height(h)<=N<height(h+1), the h-th
carrier is already available below N, while its cardinality dominates the
desired power of N. The proof obtains this interval using the least index
whose height exceeds N. It does not assume that a sparse-sequence lower
bound automatically holds at all integer heights.

## Conditional theorem and precise remaining gap

`near_linear_of_eventually_sidon` proves:

    (eventually in h, IsSidon (squares h))
      --> the exact original near-linear conjecture.

The Sidon hypothesis is explicit and UNPROVED. `finite_lower` likewise
requires actual Sidonness before comparing h! with maxSidonSubsetCard.
No formal-polynomial-to-integer specialization is silently assumed.

The prior ordinary-alphabet, repeated-histogram, distinct-digit, and
exact-inversion counterexamples do not directly refute this particular
complete allowed alphabet. This continuation produced neither a proof of
its eventual Sidonness nor a counterexample to that exact family. It gave
no new unconditional Sidon exponent and no original-conjecture disproof.
