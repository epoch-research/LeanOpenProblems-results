# Varying cancellation orders and separated errors

Informal mathematical review only, NOT a Lean theorem and NOT a settlement
of Erdos 68. Spec.lean remains unchanged with its original sorry.

## Proposed construction

Instead of taking consecutive shifts of one raw Lambert operator, choose
forms from different cancellation orders K_i and starting indices H_i.
For each order the verified full-period detector supplies a phase at which
the full-target raw error epsilon_i is nonzero. Its retained coefficient
is integral and its boundary is rational.

A possible scalar nonvanishing argument would arrange the absolute errors
in rapidly decreasing order. If every error dominates Q times the sum of
all later absolute errors, then any nonzero integer combination with
weights bounded by Q is nonzero: inspect its earliest nonzero weight.
One could then try scalar modular pigeonholing to clear the aggregate
boundary, rather than simultaneously clearing all phases of one operator.

## Unresolved size compatibility

For the raw operator cancelling rows 2,...,K, write

    M = 2+...+K,
    P = product_(d=2)^K d!,
    T = H+M.

The known individual boundary clearing bound is C=T!/P. Its leading
logarithmic size, when H is comparable with K^2, is approximately

    log C = (2H+K^2/2) log K + O(H+K^2),

whereas the raw error decay supplied by the row-rate estimates is on the
scale H log K. This is an informal asymptotic comparison, not a newly
formalized bound. A common denominator for several chosen orders would
also have to be supplied; it cannot be silently replaced by the smallest
individual one.

Scalar pigeonholing for D weights would require (Q+1)^D>C_common.
First-term dominance, in contrast, requires a cumulative separation on
roughly the scale (D-1) log Q, in addition to controlling the first error
and the errors at the selected phases. No choices meeting all these
requirements were obtained using the available clearing and row-rate
bounds. The full-period detector alone does not supply the required
separation ratios between different orders.

This does NOT rule out other normalizations, better reduced-denominator
bounds, varying coefficient budgets, or other forms. It is not an
asymptotic impossibility theorem for the actual aggregate boundaries.

## Status of other recent reviews

The exact carry recurrence, common-coefficient factorial-column forms,
and the modified Engel algorithm were reconsidered. No infinite carry
violation, controlled one-sided common-coefficient family, or rational
height descent was proved. A proposed separate rational chain with
linearly growing multipliers was NOT constructed; its existence must not
be asserted from the earlier bounded-multiplier comparison.

There is no new Lean declaration or complete informal settlement from
this pass. No computation or compilation is pending, and no proof or
disproof has been submitted.
