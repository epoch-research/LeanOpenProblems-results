# Prime-row modular injection — not a settlement

Spec.lean remains unchanged with the original sorry. No proof of the
conjecture or irrational counterexample has been found. No incomplete
proof was submitted.

New file: PrimeRowResidueInjection.lean.
Namespace: Erdos972PrimeRowResidueInjection.
The file compiles, and all three principal declarations audit with only
propext, Classical.choice, and Quot.sound.

## Verified result

Assume alpha >= 1, d > alpha, M > 0, and N <= d*M.
For prime inputs M < p <= N with d dividing floor(alpha*p), define

    r(p) = (floor(alpha*p)/d) * p^(-1) in ZMod M.

The inverse exists because p is prime and p > M. The modulus M does NOT
need to be prime.

`cofactorResidue_injective` proves that r is injective on these inputs.
Indeed, a residue collision makes

    k*q-l*p,  k=floor(alpha*p)/d, l=floor(alpha*q)/d,

divisible by M. The existing determinant bounds and p,q <= d*M imply its
absolute value is strictly less than M. Hence it vanishes, contradicting
the nonzero-determinant theorem for distinct prime inputs and d > alpha.

`prime_divisor_row_card_le` therefore proves that at most M such prime
inputs occur in the row.

`two_large_divisor_prime_inputs` specializes M=2: if N <= 2*d and d>alpha,
at most two odd prime inputs up to N have outputs divisible by d. The
input prime 2 is explicitly excluded.

## Limitations

This is an upper multiplicity bound and requires p > M. No irrationality
hypothesis is needed. It does not estimate a centered signed row sum,
prove prime-pair positivity, or supply the strict lower gap in the existing
four-factor reduction. The universal conjecture is still unresolved.
