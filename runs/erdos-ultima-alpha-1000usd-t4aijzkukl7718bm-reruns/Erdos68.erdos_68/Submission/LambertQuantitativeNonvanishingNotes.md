# Quantitative prime detection for growing Lambert operators

This is verified auxiliary progress, NOT a settlement of Erdős 68.
Spec.lean is unchanged with its original sorry. No proof or disproof has
been submitted in this continuation.

## Verified prime-window bound

LambertQuantitativeNonvanishing.lean compiles without warnings and has a
current olean. All five printed principal axiom audits use only propext,
Classical.choice, and Quot.sound. There are no proof holes in this file.

For H>0 and 0<a<(H+1)^r, there is a prime p with

    H < p <= 2^r H,   p does not divide a.

The proof inducts on r. Choose a prime in (2^(r-1)H,2^r H] by Bertrand.
If it divides a, divide a by that prime and apply the induction hypothesis;
any prime found at the earlier stage is distinct from the removed prime.
In particular the conclusion applies to 0<a<=H^r when r>0.

## Growing-operator application

Use the earlier definitions

    c_n = lambertCoeff(n)/n!,
    F_w(n) = sum_(i=0)^D w_i c_(n+i),
    T_w(n,x) = sum_(i=0)^D w_i (x-S_(n+i)).

Suppose D<=H, r>0, and the final coefficient has the factorization

    w_D = P*z,   z!=0,   abs(z)<=H^r,

where no prime above H divides the natural number P. The file proves a
nonzero coefficient form at an index n satisfying

    H-D < n,   n+D <= 2^r H.

It then proves that for every real x there is a nonzero tail form with

    H-D <= n,   n+D <= 2^r H.

This uses the exact difference identity T_w(n-1,x)-T_w(n,x)=F_w(n).
Unlike the earlier frequent-nonvanishing theorem, the bound is quantitative
and uniform over operators meeting the displayed degree/height hypotheses.
For fixed r the window endpoint is a constant multiple of H.

The smooth factor can be the factorial product product_(d in ds) d!:
when sum(ds)<=H it divides H!, so primes above H cannot divide it. This is
formalized in factorialProduct_smooth and factorial_leading_tail_ne_zero.
The latter theorem assumes the stated factorization of w_D. This new file
does not itself expand a raw shift product into a coefficient sequence.

Principal declarations:

* prime_not_dvd_in_dyadic_window
* prime_not_dvd_of_power_bound
* coefficientForm_ne_zero_in_window
* tailForm_ne_zero_in_window
* factorialProduct_smooth
* factorial_leading_tail_ne_zero

## Verified integrality obstruction

The file also strengthens the local prime test: if p=n+D is prime and
F_w(n) is an integer, then p divides w_D. The earlier terms become integral
after multiplication by (p-1)!, while c_p=1/p!.

Consequently, if T_w(n-1,x) and T_w(n,x) are both integers at a prime final
index, then p divides w_D. This holds at every real endpoint x, without a
rationality assumption. Taking x=0 applies it to adjacent integral
boundaries.

These are coefficientForm_integral_last_dvd and
adjacent_tail_integrality_last_dvd. Thus simultaneous integral clearing of
the adjacent forms at a detecting prime cannot retain the prime test's
nondivisibility condition. The new index bound is not an integrality theorem.
It does not exclude other nonvanishing or partial-clearing constructions.

## Further review (informal, no additional theorem)

Sampling on a fixed phase of the first uncancelled Lambert row was
reconsidered. The row then has a geometric ratio, which could give leading-
term dominance if the weights were sufficiently small. Increasing sample
spacing also increases the final boundary-clearing endpoint. The existing
pigeonhole bound does not simultaneously provide the required small digits
and the full-target error bound. Factorially rescaling the weights shifts,
rather than removes, this cost. No compatible parameter choice or general
impossibility theorem was obtained.

No new numerical search was run. No complete informal proof or disproof of
the original conjecture is awaiting formalization. Nothing is pending
compilation or computation.
