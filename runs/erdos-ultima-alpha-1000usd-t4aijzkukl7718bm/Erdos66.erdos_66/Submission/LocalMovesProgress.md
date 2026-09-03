# Local-repair identities

## Status

The conjecture is still **not proved or disproved**. `Spec.lean` is unchanged
and retains its original `sorry`. No convergent repair algorithm is claimed.

## Checked in `LocalMovesExplore.lean`

Let C be a common core and let a,b lie outside C. For A=C union {a} and
B=C union {b}, the exact representation-count change is

    r_B(n)-r_A(n)
      = 2(1_{b+C}(n)-1_{a+C}(n)) + 1_{n=2b}-1_{n=2a}.

Here translates are interpreted in the natural numbers, so the shifted
indicator is zero when the target is below the shift.

- `move_exact` proves this identity.
- `move_bound` proves |r_B(n)-r_A(n)| <= 2 at every target.
- `move_unchanged_outside` proves no change outside the two translates and
  the two diagonal targets.
- `squaredError_change` proves the exact energy identity for any finite set
  of targets S, reference q, and two sets A,B:

      E(B)-E(A) = sum_{n in S} [2(r_A(n)-q(n)) d(n) + d(n)^2],
      d(n)=r_B(n)-r_A(n).

## Unresolved step

These formulas do not provide the improving moves needed to obtain uniformly
small normalized errors. In particular, fixing one deficient target also
changes other targets, and minimizing an aggregate squared error would not
by itself imply a uniform o(log n) bound.

No compatible infinite sequence of repairs, nor the required uniform finite
prefix feasibility assertion, has been proved.
