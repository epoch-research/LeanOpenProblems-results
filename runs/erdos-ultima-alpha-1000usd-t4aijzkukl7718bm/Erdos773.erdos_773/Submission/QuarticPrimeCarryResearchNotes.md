# Quartic carries at arbitrarily large prime bases congruent to one

This does NOT settle Erdos 773. Spec.lean is unchanged, with its sole
admission at line 17287 for 0<epsilon<1/3. The completed unconditional
endpoint remains eventual M(N)>=N^(2/3).

## Verified module

Submission/QuarticPrimeCarry.lean imports the clean FormalGaussianSidon
module, not Spec.lean. It compiles without errors, warnings or admissions,
and has a built olean. All eight printed audits use only propext,
Classical.choice and Quot.sound. Log: /tmp/quartic-prime-carry.log.

For an integer k>=2 set B=540*k+1. The four quartics, listed by their
constant-first canonical digits, are:

    [6,234k+108,462k-42,24,1]
    [6,234k+186,30k+132,360k+42,1]
    [6,234k+180,30k+24,360k+42,1]
    [6,234k+114,462k+138,24,1].

Every lower digit is positive, less than B, and divisible by six. Each
constant digit is exactly 6 and each leading digit is 1. These are
admissible quartics in the proved formal Gaussian-Eisenstein construction,
so their formal square values are Sidon in Z[X].

The exact discrepancy, checked by Lean's ring tactic, is

    E0(X)^2+E1(X)^2-E2(X)^2-E3(X)^2
      =72 X^3 (B-X) (2X^2-4X-1).

It is nonzero formally, but vanishes at X=B. The evaluated roots are
positive and injective, with order value(0)<value(3)<value(2)<value(1).
Every root lies in [B^4,2B^4). The file also transfers the collision and
the negation of Sidonness to NATURAL roots via checked positive toNat casts.

Dirichlet's theorem supplies arbitrarily large PRIME bases in the coprime
progression 540k+1. The proof checks k>=2 before applying the digit bounds.
This is an unbounded prime-base family, not an inference from one numerical
example. The existing cubic prime-509 obstruction and degree-19 prime-base
example are separate results; no claim that degree four is minimal is made.

## Exact algebraic source

Let

    n=6B, m=24B+1,
    u=6+234k B+(30k+1) B^2,
    v=u+6B.

The four evaluated roots are

    (m*u-n*v, n*u+m*v, m*u+n*v, -n*u+m*v).

The norm identity is automatic. The low-to-middle carries are 7 and 13;
both are one modulo six. The top carries supply the leading digit one.
The Lean proof verifies the displayed polynomial discrepancy directly,
rather than trusting a symbolic-computation certificate.

## Scope

This blocks a blanket quartic integer-specialization rule even at
arbitrarily large primes congruent to one modulo six. It does NOT assert
common histograms, common digit sums, or membership in the full-permutation
AllowedAlphabetCandidate carrier. It does not bound the largest Sidon
SUBSET of these digit families or of all squares.

The continuation also reconsidered amplification and residue-fiber
selection. Modular pair matching still does not supply disjoint ACTUAL
positive-difference spectra, and no compatible near-linear selector was
obtained. No improved original-conjecture exponent or fixed-power upper
bound was proved. No incomplete proof was submitted.

Spec.lean SHA-256:
257d2e55d464b8ea5a35ca7f1257dc2f59e682772c2f52fa771ee4bfdf9b8940
