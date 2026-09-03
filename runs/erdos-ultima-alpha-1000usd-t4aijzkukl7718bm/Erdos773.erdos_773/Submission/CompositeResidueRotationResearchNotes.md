# Two-row restrictions over composite moduli

This continuation does NOT settle Erdos 773. The original statement and sole
import in Spec.lean are unchanged, as is its one admission for 0<epsilon<1/3.
The proved endpoint remains eventually M(N)>=N^(2/3).

## New clean module

Submission/CompositeResidueRotation.lean imports only FormalConjecturesUtil.
It has no admissions or warnings. Its five printed axiom audits use only
propext, Classical.choice, and Quot.sound. The olean is built.

Log: /tmp/composite-residue-rotation.log.

Let l be a nonzero integer with IsCoprime l 2. Suppose all four integer
coordinates a,b,c,d are congruent to 1 modulo l, and both rotation rows hold:

    p*a+r*b=q*c,
    -r*a+p*b=q*d.

* rows_divisibility proves l divides r and l divides q-p. No prime or
  squarefree hypothesis is used. Both rows are essential to this argument.
* square_divides_gap additionally assumes IsCoprime p r and
  q^2=p^2+r^2, and proves l^2 divides q-p. This lemma is stated directly
  from the leg and gap divisibility, independently of the root coordinates.
* denominator_lower, for q>0 and r nonzero, gives l^2<2*q.
* positive_denominator_lower adds positivity of all four coordinates and
  strengthens this to l^2<q. The dot-product identity shows p>0.

The lifting step writes r=l*t and q-p=l*k. The Pythagorean equation gives
2*q*k=l*(k^2+t^2). Primitivity and the residue relation imply that q is
coprime to l, so k is divisible by l. This is a genuine composite-modulus
extension, not multiplication of prime-specific inequalities.

## Exact scope and remaining gap

The rotation equations, Pythagorean identity, and primitivity are explicit
hypotheses. No universal collision-to-rotation transfer or denominator
upper bound is asserted in this new module. In particular, do not confuse
its q with the normalized small Gaussian factor in the endpoint machinery
without checking the orientation and normalization.

This is still only a denominator cutoff. It neither controls the number
of larger-denominator collisions nor constructs a compatible sparse-fiber
family. It gives no improved exponent for the original maximum and is not
a disproof of the conjecture.

A preceding review of finite-field/checksum and partial-fiber constructions
also yielded no new selector. Existing counterexamples to other digit
criteria do not by themselves refute every full allowed-alphabet family.
No such family was proved to be Sidon or to have a useful collision bound.

Spec.lean remains at SHA-256
257d2e55d464b8ea5a35ca7f1257dc2f59e682772c2f52fa771ee4bfdf9b8940.
No incomplete proof was submitted.

## Explicit limitation of iterating the lift

The new theorem positive_primitive_square_gap proves, for every natural
parameter t>0 and m=2t+1, an actual positive primitive rotation with q-p=m^2
and hence m^3 not dividing q-p. Put

    a = 2*m+1,
    b = 5*m^2+5*m+1,
    c = 4*m^2+4*m+1,
    d = 3*m^2+3*m+1,

and

    p = 6*t^2+10*t+4,
    r = 8*t^2+10*t+3,
    q = 10*t^2+14*t+5.

Lean verifies 0<a<d<c<b, all four roots congruent to one modulo m,
IsCoprime m 2, IsCoprime p r, q>0, r nonzero, both rotation rows, the
Pythagorean identity, and a^2+b^2=c^2+d^2. Primitivity has the explicit
integer Bezout certificate

    (40*t+22)*p + (-30*t-29)*r = 1.

This rules out unconditional third-power lifting even with positive,
four-distinct roots and a primitive rotation. It is a family of collisions
at quadratic root height, not a fixed-power upper bound for the largest
Sidon subset. It supplies no disproof of the original conjecture.

A review of sparse-fiber amplification, modular higher-rank encodings,
and multiscale digit restrictions yielded no new compatible family or
collision-count bound. No improved main-gap exponent was obtained.
