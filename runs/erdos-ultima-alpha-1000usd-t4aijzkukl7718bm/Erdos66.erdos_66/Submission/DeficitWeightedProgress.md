# Actual-deficit weighted completion

## Status

The conjecture in `Submission/Spec.lean` is still unproved and undisproved.
That file is unchanged and retains the original `sorry`. No proof submission
has been made. In particular, **no base satisfying the criterion below has
been constructed**.

The new files compile, have current oleans, and pass the permitted-axiom
checks in `DeficitWeightedAxiomCheck.lean`:

- `MultiplicityMatchingSpikesExplore.lean`
- `DeficitWeightedCompletionExplore.lean`

## Direct nonnegative multiplicities

The previous repeated-center machinery required a list of positive
multiplicities. The old sparse-exception application used `correction + 1`
to ensure positivity, even when a target did not actually need a repair.

`Erdos66MultiplicityMatchingSpikes.asymptotic_multiplicity_spikes` now takes
an arbitrary function `m : Nat -> Nat`, allowing zeros, with

```
sum_n m(n) * sqrt(log(n+2)) / sqrt(n+1) < infinity.
```

For any O(log)-bounded base A it constructs B containing A such that,
eventually,

```
r_A(n)+2*m(n) <= r_B(n) <= r_A(n)+2*m(n)+o(log n).
```

If the positive support of m is finite, no changes are needed asymptotically.
Otherwise the proof enumerates that support by `Nat.Subtype.orderIsoOfNat`,
uses the positive-multiplicity repetition equivalence, and applies the
existing summable matching-spikes theorem. It charges no dummy packet at a
zero-multiplicity target.

## Completion from an actual deficit

Let L(n)=log(n+2). Suppose A has the asymptotic upper bound

```
for every epsilon>0, eventually r_A(n) <= (c+epsilon)*L(n).
```

Let d(n)>=0 be a uniformly sublogarithmic allowance:

```
d(n)/L(n) -> 0.
```

Define the actual positive deficit

```
D(n) = max(0, c*L(n)-d(n)-r_A(n)).
```

If

```
sum_n D(n) * sqrt(L(n)) / sqrt(n+1) < infinity,
```

then there is B containing A with

```
r_B(n)/log n -> c.
```

No exceptional-target list or separate global upper envelope is needed.
The global envelope follows from the asymptotic upper bound and the elementary
`r_A(n)<=n+1` bound on the finite prefix.

The repair multiplicity is the existing floor-clipped correction, without
adding one. Its target is `c*L(n)-d(n)`, which is permitted to be negative at
small indices. The checked profile inequalities hold for arbitrary real
r,t:

```
t-2 < r+2*correction(r,t) <= max(r,t).
```

The loss of at most two representations is asymptotically negligible.

Main names, namespace `Erdos66DeficitWeightedCompletion`:
- `correction_profile_bounds`
- `correction_le_deficit`
- `deficit`
- `completion_of_summable_deficit`
- `global_envelope_of_upper_tail`
- `completion_of_upper_tail_and_summable_deficit`

## What this does not accomplish

The actual-deficit criterion is more flexible than charging O(log n) at every
listed exception, and allows dense sublogarithmic errors through d. It still
requires a summable weighted cost for the remaining macroscopic shortfalls.
No checked finite-annulus, floor-rounding, random, or scale-changing
construction has been shown to meet that requirement. The new theorem is
conditional, not a solution to `Spec.lean`.
