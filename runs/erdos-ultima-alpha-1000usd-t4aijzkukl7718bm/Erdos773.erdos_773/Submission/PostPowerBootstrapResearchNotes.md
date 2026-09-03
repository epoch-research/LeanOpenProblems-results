# Arithmetic bootstrap review after the N^(2/3) lower bound

This review did NOT settle Erdős 773. No new exponent, stronger constant,
near-linear selector, or original-conjecture disproof was obtained. Spec.lean
has not been modified, and no proof submission was made.

## What the new lower bound does and does not provide

The strongest completed actual bound remains

    eventually M(N) >= c0*N^(2/3),
    c0=1/(32768*15360000^(1/3)) >=1/10000000.

Its proof is GreedySquarePowerLower. The generic fixed- and growing-horizon
concentration work is complete; those are no longer missing hypotheses.
This lower bound alone gives no exponent-improving amplification. In
particular, substituting a multiplier depending on N into the older
fixed-multiplier eventual theorem is not justified. The growing-horizon
version has explicit bounds and has already been used with those bounds.

## Partial-fiber route

The exact PartialResidueFibers characterization was rechecked. With modular
pair matching, individually Sidon fibers have a Sidon union precisely when
their actual positive-difference sets are pairwise disjoint.

For roots q*i+r and q*j+r with j>i, dividing the positive square difference
by q gives

    (j-i)*(q*(i+j)+2*r).

Thus a cross-fiber equality has the form

    h*(q*t+2*r)=k*(q*u+2*s),

and necessarily r*h=s*k modulo q. The modular equation is NOT sufficient:
the actual t,u equation must also be controlled. Conversely, forbidding all
modular product aliases is unnecessarily strong and incurs the already
proved capacity losses. Nothing in the new power-scale lower bound produces
a high-cardinality family of compatible partial fibers.

Several possible repairs were considered but not established:

* Translate index sets independently: this changes the actual difference
  equation, but requires a proved simultaneous overlap estimate. No useful
  estimate or packing theorem was obtained.
* Use prime or rough gaps/sums to make the product factorization unique:
  such conditions concern EVERY pair in a selected fiber and cannot be
  inferred from individual-root primality or coprimality. They impose a
  new selector problem, not a solved step.
* Use a two-digit finite-field parabola to make product coordinates injective:
  ordinary integer products have carries. Replacing them by carry-free field
  coordinates is invalid without an additional argument. The existing
  carry-aware parabola theorem supplies pair matching, not cross-fiber
  compatibility.
* Iterate full-fiber lifting: the existing full-fiber and short-product
  bounds still prevent these sufficient criteria from providing the needed
  exponent improvement. They do not bound arbitrary partial fibers.

No new impossibility result for all partial-fiber constructions is claimed.

## Bounded multiplicity and general additive methods

The fixed-capacity selection theorem supplies roots of size
N^(2g/(2g+1)-epsilon), but capacity one remains the required conclusion.
No near-linear conversion for capacity g>1 was found or assumed.

It is important not to confuse bounds on representations of a SUM with
bounds on representations of a POSITIVE DIFFERENCE. For example, a grid
of formal values x_i+y_j, with independent x and y coordinates, has very
few representations of each sum, while a difference y_j-y_k repeats in
every row. This observation is not a square construction or a disproof of
any proposed difference-capacity theorem. No general conversion theorem or
counterexample to a near-linear difference-capacity conversion was proved
in this review.

Independent Bernoulli selection, generic linear-hypergraph extraction, and
the already verified weighted alterations still give the 2/3 exponent when
applied with the available square-collision counts. A new arithmetic input
would be needed to improve that exponent. A formal-polynomial Sidon
construction still cannot be evaluated at a small integer base without
controlling its carries; the previous exact specialization obstructions
remain applicable to the blanket rules already tested.

## Current project state

No Lean source was changed during this bootstrap review. The prior combined
audit remains /tmp/greedy-square-power-combined-audit.log, with 191 clean
permitted-axiom checks across 41 modules. The main file's sole sorry remains
at line 2031; its import and conjecture statement are unchanged.

Spec.lean SHA-256:
917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14.

The remaining task is a genuine square-specific exponent improvement (and
ultimately the near-linear bound), or an upper bound with a fixed positive
exponent loss along an unbounded sequence. Neither has been established.
