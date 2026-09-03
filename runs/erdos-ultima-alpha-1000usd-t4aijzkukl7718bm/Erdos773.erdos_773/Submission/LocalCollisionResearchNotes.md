# Local collision saving and local Sidon extraction

The conjecture is NOT settled. There is no improvement to the actual global
Sidon exponent, and Spec.lean was left unchanged with its sole admission at
line 2031. No proof submission has been made.

## New verified modules

* `LocalCollisionBounds.lean` imports OrderedCollisionDefect and DivisorBound.
* `LocalSidonSelection.lean` imports LocalCollisionBounds and LowCollisionSelection.

Neither imports the admitted Spec theorem. Their eight printed axiom audits
use only propext, Classical.choice, Quot.sound. Both compile without warnings
or admissions. Final logs are `/tmp/local-collision-bounds-final.log` and
`/tmp/local-sidon-selection-final.log`; the corresponding `.olean` files
are in `.lake/build/lib/lean/Submission/`.

## Exact local count

`Erdos773.LocalCollisionBounds.collisions L H` counts strictly increasing
quadruples a<b<c<d in the CLOSED root interval [L,L+H] satisfying

    a^2+d^2=b^2+c^2.

It includes only four distinct roots, not three-root progressions and not
trivial ordered presentations. Each such quadruple has unique parameters

    z=d-c, y=c-b, t=(b+c-a-d)/2,
    b=a+z+2t, c=a+z+2t+y, d=a+2z+2t+y,
    2t(a+t)=z(z+y).

The existing span identity yields

    t(8L+4) <= H^2,     2t(a+t) <= H^2.

The factor TWO in the product identity is preserved. The first root a, the
positive defect t, and the divisor z determine the original quadruple
injectively. This is proved, not just a many-to-one parameter count.

Public results:

* `parameter_bounds`
* `divisor_sum_bound`
* `uniform_divisor_bound`
* `local_collision_subpower`

Write T=floor(H^2/(8L+4)). The exact upper bound is

    E(L,H) <= sum_{a=L}^{L+H} sum_{t=1}^T
                 [2t(a+t)<=H^2] tau(2t(a+t)).

In particular, if tau(D)<=K for all 0<D<=H^2, then

    E(L,H) <= (H+1) T K.

For every delta>0, a constant C_delta>0 works uniformly in L and H:

    E(L,H) <= C_delta (H+1) T H^(2 delta).

All formulas allow L=0 and H=0. The integer floor T is retained. Away from
L=0 the scale is H^(3+2delta)/L for H large; this is a local saving compared
with an unrestricted collision count at the upper endpoint.

## Local Sidon subsets, including repeated-middle-root obstructions

Public results in `Erdos773.LocalSidonSelection`:

* `fourSupports_card_le`
* `local_alteration`
* `local_divisor_alteration`
* `local_finite_lower`

The first theorem maps each four-entry obstruction support in the square
values to a strictly ordered root collision. It loses NO factor of 24 or
other ordering multiplicity. The normalization first orders each pair,
then compares the pair minima; the norm equality forces the maxima into
the opposite order. Squaring is injective on natural roots.

The second theorem, with m=H+1 and 0<=p<=1, gives

    M([L,L+H]^2) >= (p m-p^4 E(L,H))/4.

Here the notation means the maximum Sidon subset of the squares of the
roots in that interval. It is NOT the square of the interval as a set of
all integers. The weak-Sidon extraction from LowCollisionSelection includes
and removes all three-entry obstructions at constant cost; no AP-free
hypothesis is omitted and no Behrend loss is incurred.

The optimized explicit bound, under the uniform divisor hypothesis, is

    M([L,L+H]^2) >= 7(H+1)/(64 max(1,T K)^(1/3)).

This uses p=1/(2 max(1,TK)^(1/3)). For L and H of comparable size, it still
only gives the global 2/3-o(1) exponent. For shorter intervals it supplies
an actual local lower bound, but it does not bound mixed collisions when
several intervals are combined.

## Remaining gap

The interval-packing, modular-fiber, and multiscale approaches were reviewed
again. No argument was found that combines sufficiently many short-interval
sets while retaining subpower loss. Within-interval saving alone cannot be
used as a bound for the union: a collision can have its roots in multiple
intervals. Ordinary sampling of one long interval has optimized scale
(LH)^(1/3), at most N^(2/3) when both L,H are at most the ambient root scale N.
These observations are limitations of the attempted constructions, not an
upper bound on arbitrary Sidon subsets and not a conjecture disproof.

The latest main check is `/tmp/spec-local-collision-check.log`. The unchanged
main-file hash is
917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14.
