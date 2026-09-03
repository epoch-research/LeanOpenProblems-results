# Bounded-denominator rotation lifting

This continuation does NOT settle Erdos 773. Spec.lean is unchanged at
SHA-256 257d2e55d464b8ea5a35ca7f1257dc2f59e682772c2f52fa771ee4bfdf9b8940.
It still has its sole admission at line 17287 for 0<epsilon<1/3.
The proved endpoint remains eventually M(N)>=N^(2/3).

## New clean module

Submission/SmallRotationLifting.lean imports only FormalConjecturesUtil.
It contains no admissions and builds with an olean. Its five printed
main audits use only propext, Classical.choice, and Quot.sound.

For an integer digit vector a, define value(B,a)=sum_i a_i B^i.

* signed_zero: if B>0, all |a_i|<B, and value(B,a)=0, every a_i=0.
  This uses divisibility of the constant digit and induction, not an
  unverified formal-to-integer specialization rule.
* linear_lift: a scalar relation p*value(a)+r*value(b)=q*value(c)
  lifts coordinatewise if every |p*a_i+r*b_i-q*c_i|<B.
* orthogonal_of_equal_norm: if q^2=p^2+r^2, p and r are nonzero,
  a,b,c have identical squared Euclidean norms, and p*a+r*b=q*c
  coordinatewise, then sum_i a_i*b_i=0. Only one rotation row is needed.
* no_small_rotation: the scalar relation is impossible if this inner
  product is positive, all digit absolute values are <=H, and
  (|p|+|r|+|q|)*H<B.
* no_bounded_denominator: the sufficient bound can be replaced by
  3*Q*H<B when 0<q<=Q and H>=0. The Pythagorean equation supplies
  |p|<=q and |r|<=q.

## Scope and unresolved step

This establishes a valid bounded-coefficient version of the digit-sphere
argument, not an unrestricted square-Sidon criterion. The previously
verified carry counterexamples do not contradict it: the explicit
no-carry hypothesis is essential.

It does not supply a useful bound for the large-denominator collisions.
The available harmonic direction-count estimate still has quadratic-order
scale when a small power cutoff is removed. No fixed-power saving for
that remaining collision family, no Sidon exponent improvement, and no
original-conjecture disproof were established.

The main file was compiled again without errors (but with its expected
admission warning). The original statement and sole import were not changed.
No incomplete result was submitted.

Logs:
  /tmp/small-rotation-lifting.log
  /tmp/spec-small-rotation-check.log
