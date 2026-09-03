# Nonvanishing from a prime last coefficient

This is verified auxiliary progress, not a settlement of Erdős 68.
`Submission/Spec.lean` is unchanged and still contains its original sorry.

`PrimeLeadingForms.lean` compiles without warnings and has a built olean.
All three principal axiom audits use only propext, Classical.choice and
Quot.sound.

## General unit-index statement

Let c_n and w_n be integers, and set

    S_n = sum_(k=0)^n c_k/k!,
    F_N(x) = sum_(n=0)^(N-1) w_n*(x-S_n).

`unit_last_nonzero` proves that for p>0, c_p=1, p not dividing w_p, and
rational x with reduced denominator less than p,

    F_(p+1)(x) != 0.

Indeed, (p-1)! times each x-S_n, n<p, is integral. Write

    G=F_p(x)+w_p*(x-S_(p-1)),  (p-1)!*G=z in Z.

Since S_p=S_(p-1)+1/p!, vanishing of F_(p+1)(x) would imply
p!*G=w_p, hence p*z=w_p, contrary to the weight hypothesis. Primality is not
needed for this general statement.

## Lambert specialization

`lambert_prime_last_nonzero` applies the statement to the Lambert
coefficients, which equal one at every prime. This is a nonvanishing result
UNDER A RATIONALITY HYPOTHESIS, not an unconditional irrationality result.

The file also proves `prime_not_dvd_factorial_product`: a prime p does not
divide a product of d! with every d<p. Thus the leading weight of

    Q_K(E)=product_(d=2)^K(d! E^d-1)

has the needed property at a shifted final index p>K. The expansion of this
particular operator is not itself formalized in this new file; the generic
weight criterion and the factorial-product nondivisibility are verified.

This does not supply a small cleared-error estimate. Nor does it assert that
every nonzero weight vector gives a nonzero form: the final-weight modular
condition is essential. No growing family satisfying both smallness and
nonvanishing has been obtained, and no proof or disproof has been submitted.

## Limitation for integral-boundary combinations, now verified

`unit_integral_value_last_dvd` proves the converse divisibility condition:
if c_p=1, x is rational with denominator less than p, and F_(p+1)(x) is
an integer, then p divides w_p. Its printed axiom audit uses only the three
permitted axioms. Taking x=0 shows that an integral boundary already forces
this divisibility for p>1. Consequently the prime-last-weight nonvanishing
criterion cannot simply be carried over to the new boundary-clearing lattice
combinations. See LambertBoundaryLatticeNotes.md for that unresolved route.
