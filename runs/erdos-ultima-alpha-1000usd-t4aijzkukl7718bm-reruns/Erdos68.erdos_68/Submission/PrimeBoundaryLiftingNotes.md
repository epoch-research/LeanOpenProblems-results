# Exact prime-endpoint boundary lifts

Verified auxiliary arithmetic, NOT a proof or disproof of Erdos 68.
Submission/Spec.lean is unchanged with its original sorry. No settlement
has been obtained or submitted.

PrimeBoundaryLifting.lean compiles without warnings and has a built olean.
Its printed principal axiom audits contain only propext, Classical.choice,
and Quot.sound. It contains no proof holes or numerical premises.

## General finite factorial-series lift

Let c_n be integers, S_n=sum_(j<=n)c_j/j!, and let integer weights w_n
be supported on the window 0,...,p. Set

    A=sum_(n<=p) w_n,
    B=sum_(n<=p) w_n*S_n.

Assume p>0 and c_p=1. Changing the weights by

    w'_p=w_p+k,    w'_(p-1)=w_(p-1)-k

(and leaving the others unchanged) preserves A and changes B to B+k/p!.
Since p!*B is an integer, EVERY prescribed integer b can be attained by

    k=p!*(b-B) in Z.

The exact correction size is

    |k|=p!*|b-B|.

This cost is proved, not suppressed in the existence assertion.
The main declarations are lift_integer_boundary and correction_cost.

## Actual Lambert rows

The exact Lambert coefficients satisfy c_p=1 at primes. For prime p and
2<=d<p, d does not divide p, so

    floor(p/d)=floor((p-1)/d).

Consequently the geometric row values

    1/[(d!)^floor(n/d)*(d!-1)]

are equal at n=p and n=p-1. The opposite endpoint weights preserve the
weighted sum of EVERY row d<p, hence all existing annihilation constraints
for those rows. The theorem lambert_lift packages this preservation with
an arbitrary prescribed integral boundary and the exact correction cost.

## Essential limitations

This is a lift for one finite window of unfiltered Lambert prefixes. It
neither clears all translated output phases nor asserts a useful bound
for a prescribed boundary pair. If a row has been annihilated in this
window, its cancellation is preserved; the theorem does not construct
the initial annihilator or control its weights.

Most importantly, integrality is not the missing small-error result:
for the full target alpha the correction changes the form A*alpha-B by
exactly -(b-B). The factor p! in the correction can be large, and choosing
an integer b does not by itself make |A*alpha-b| tend to zero or exclude
its being zero under rationality. No nonzero small integer-form family or
controlled useful lattice lift follows here.

Other reviews in this continuation (direct Pade congruences, carry dynamics,
modified Engel coordinates, and determinant normalization) did not produce
a new complete argument. No numerical search was run. An external literature
request failed at DNS resolution; no paper or claimed resolution was retrieved.

The compilation log is /tmp/prime_boundary_lifting.log. All compilation
has completed. No proof or computation is pending, and no complete informal
solution is waiting to be formalized.
