# One-shift collision savings and actual root height

This is NOT a settlement of Erdős 773. Spec.lean is unchanged and still has
its sole admission for 0 < epsilon <= 1/3. No proof has been submitted.

## Ordered affine collision parameters

File: AffineCollisionBounds.lean

Assume q>0 and gcd(q,2r)=1. For indices a<b<c<d with

  (qa+r)^2+(qd+r)^2=(qb+r)^2+(qc+r)^2,

normalized_parameters supplies positive integers z,y,u such that

  b=a+z+2qu,
  c=a+z+2qu+y,
  d=a+2z+2qu+y,
  2u(q(a+qu)+r)=z(z+y).

Thus the positive index pair-sum defect is 2qu, and the actual root
pair-sum defect is 2q^2u. Both factors of 2 are retained.

For all indices in [1,N], the encoding (a,u,z) is injective and satisfies

  1 <= a <= N,
  1 <= u <= T,
  z divides D=2u(q(a+qu)+r),
  0 < D <= N^2,

where

  T = min(floor(N/(2q)), floor(N^2/(8r+4q))).

The second bound on u follows from the exact span identity

  4u(2qa+2r+2qz+3q^2u+qy)+y^2=(2z+2qu+y)^2.

Consequently the strictly ordered four-index collision count E(N,q,r)
satisfies

  E <= sum_{a=1}^N sum_{u=1}^T
         1_{2u(q(a+qu)+r)<=N^2} tau(2u(q(a+qu)+r)).

In particular E<=NTK whenever tau(D)<=K for 0<D<=N^2. The divisor argument
is bounded by N^2, NOT by the larger affine root height squared.
For each delta>0, uniformly in N,q,r satisfying the unit assumptions,

  E <= C_delta N T N^(2 delta).

Public theorems: normalized_parameters, parameter_bounds,
divisor_sum_bound, uniform_divisor_bound, collision_subpower.

## Generic increasing-image extraction

File: MonotoneSidonSelection.lean

The previous local extraction was generalized to any finite root set A and
strictly increasing map f : Nat -> Nat. Its ordered four-entry collision
count dominates the fourSupports count without an ordering-factor loss.
The weak-Sidon extraction includes all three-entry obstructions.

Public theorems: fourSupports_card_le, alteration, finite_lower.

If E is the ordered collision count, then

  maxSidon(A.image f) >= (p |A|-p^4 E)/4,  0<=p<=1.

If E<=|A|D, the optimized bound is

  maxSidon(A.image f) >= 7|A|/(64 max(1,D)^(1/3)).

No AP-free hypothesis is omitted.

## Actual one-shift Sidon lower bounds

File: AffineSidonSelection.lean

For q>0, gcd(q,2r)=1, and the divisor bound K above,

  maxSidon({(qn+r)^2 : 1<=n<=N})
    >= 7N/(64 max(1,TK)^(1/3)).

The finite alteration inequality is also public. More explicitly, for every
epsilon>0, eventually uniformly for all 1<=q<=N and all r>=0 satisfying the
unit condition,

  maxSidon({(qn+r)^2 : 1<=n<=N})
    >= N^(2/3-epsilon) q^(1/3).

The threshold for N depends on epsilon, not on q or r. This is the theorem
uniform_denominator_lower.

## Height accounting and remaining gap

The affine roots can be as large as H=qN+r. The denominator saving does
not in this estimate improve the exponent at the actual root height.
The auxiliary theorem denominator_term_le_height_power verifies

  N^(2/3-epsilon) q^(1/3) <= (qN+r)^(2/3)

for N,q>=1 and epsilon>=0. This is ONLY an upper bound on the displayed
GUARANTEED LOWER-BOUND EXPRESSION. It is not an upper bound on the actual
Sidon maximum and does not preclude a better construction in a progression.

Thus choosing a large denominator gives near-linear cardinality in the
index length but also increases root height. No unshifted lower exponent
above 2/3-o(1), or fixed-power upper bound, was obtained. Controlling all
shifts at capacity one remains too strong by the previous continuation;
controlling a single one with this collision estimate does not close the
height gap either.

## Verification

All twelve printed audits in the three modules use only propext,
Classical.choice, Quot.sound. There are no admissions or warnings. All
three olean files were built. Logs:

* /tmp/affine-collision-final.log
* /tmp/monotone-selection-final.log
* /tmp/affine-selection-final.log

Main check: /tmp/spec-affine-count-check.log. It retains the old harmless
linter warnings and the original admission warning. Spec.lean hash:

917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14
