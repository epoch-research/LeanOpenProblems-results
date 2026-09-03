# Finite carry averaging

The original conjecture in `Spec.lean` remains unsolved and unchanged.

## New checked results

`CarryAveragingExplore.lean`:
- `triangle K z = max 0 (min (z+1) (2*K-1-z))`, with integer arguments.
- `triangle_count`: the exact ordered count of indices in `[0,K)` summing to `z`.
- `triangle_step`: changing the argument by one changes the count by at most one.
- `triangle_period`: `triangle K q + triangle K (q+K) = K` for `q<K`.
- `two_fiber_error`: the abstract carry-weight error bound.

`CyclicThickeningExplore.lean`:
- Exact digit and block equivalences.
- `cyclicEncode_sub`: subtraction with its low-digit borrow.
- `lift_convolution_formula`: the exact weighted convolution formula.
- `thickenedSet_error`: for `B ⊆ (ZMod p)^2` with all ordered sum counts
  within `E` of `μ`, constructs an actual set `C ⊆ ZMod ((p*K)^2)` with

  `|r_C(z) - K^2*μ| ≤ K^2*E + 2*K*(μ+E)` for every `z`.

Here `p,K>0`; primality is not needed for the transfer itself.

The set consists of the encodings
`a.val + p*i + (p*K)*(b.val + p*j)` for `(a,b)∈B` and `i,j<K`.
For target low digit `t.val+p*q`, the number of low block lifts not borrowing
is `q+1` if `a.val≤t.val`, and `q` otherwise. This gives the triangular weights.

All four principal results checked in `CheckCarryAveraging.lean` use only
`propext`, `Classical.choice`, and `Quot.sound`.

## Limitations

This is a finite cyclic transfer. It does not construct a single infinite
natural-number set, nor the uniformly compatible prefixes required by the
compactness reduction. In particular, cyclic flatness cannot simply be
asserted for actual prefixes (see `CyclicPrefixExplore.lean`).

The proposed prime-field flat construction by prescribed interval Legendre
signs remains unformalized. Even with that input, an infinite inhomogeneous
construction is still missing.
