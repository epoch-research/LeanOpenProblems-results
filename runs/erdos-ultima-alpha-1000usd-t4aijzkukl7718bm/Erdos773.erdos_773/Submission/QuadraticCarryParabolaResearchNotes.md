# Quadratic-shear carry targets: a positive finite construction criterion

This does not settle Erdős 773. Spec.lean remains unchanged with its one
admission for 0<epsilon<1/3, and the established actual endpoint is still
M(N)>=N^(2/3) eventually.

## New clean module

QuadraticCarryParabola.lean imports the already clean ParabolaSquareLift.
All seven printed principal axiom checks use only propext, Classical.choice,
and Quot.sound. The module has no warnings or admissions and a built olean.
Log: /tmp/quadratic-carry-parabola.log.

Let p be an odd prime, and let kap,lam,mu be elements of ZMod p with lam!=0.
Define

  g(b) = kap*b^2+lam*b+mu in ZMod p,
  T(b) = (b^2 mod p)+p*g(b).val,
  a(b) = ((g(b)-floor(b^2/p))/(2*b) in ZMod p).val,
  r(b) = b+p*a(b).

For 0<b<p, the checked lift has 0<r(b)<p^2, r(b)%p=b, and
r(b)^2 congruent to T(b) modulo p^2.

## Pair matching and actual Sidonness

`target_pair_matching` proves that square-sum congruences of these targets
identify unordered label pairs when all low digits b^2%p are in one common
half-band. The half-band step first makes the low-digit sums equal as
integers. Cancelling them gives equality of the high-digit sums modulo p.
The kap terms then cancel using the square-sum congruence; lam!=0 gives
the label sum, which together with the square sum identifies the pair.

`chosen_pair_matching` allows ANY representative f(b) satisfying
f(b)^2 congruent to T(b) modulo p^2, not just the canonical r(b).
`squares_sidon_of_pair_matching` and `lift_squares_sidon` give ordinary
Sidonness, including repeated-entry obstructions.

`chosen_root_card` proves injectivity on a half-band directly from the
targets. No residue-sign assumption on the chosen representatives is
needed.

`finite_lower` transfers representatives of height at most N to

  |B| <= M(N),

assuming one common half-band. `height_count_transfer` partitions arbitrary
canonical labels into the two half-bands and proves

  |B| <= 2*M(N).

It requires 0<f(b)<=N and the square congruences for every label. All these
hypotheses remain explicit; no small-representative count is assumed proved.

## Remaining issue and scope

No parameters giving N^(1-o(1)) small representatives, or even a new actual
Sidon exponent above 2/3, have been constructed. Canonical height <p^2 alone
only yields the familiar square-root scale. The affine-target height ceiling
proved in the preceding modules does not automatically apply when kap!=0;
no such extension is asserted here. Conversely, the absence of that ceiling
is not evidence that suitable representative counts exist.

This is a positive finite criterion and a conditional height transfer, not a
proof or disproof of the original conjecture. Nothing from this auxiliary
module has been inserted into the final submission file.
