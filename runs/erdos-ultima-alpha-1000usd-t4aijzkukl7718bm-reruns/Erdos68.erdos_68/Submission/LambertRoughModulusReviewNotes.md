# Review of larger Lambert divisibility moduli

This is a research-status note, not a Lean theorem and not a settlement.
Spec.lean is unchanged and still contains its original sorry.

The latest review considered using prime-power parts of n! rather than only
the product of primes in (n/2,n]. A finite collection of low Lambert rows
can indeed be subtracted rationally, and eventually its relevant scaled
row tails are integral. This observation does not provide a small remaining
tail: every fixed remaining row still gives factorial-scaled exponential
growth, as covered by the existing fixed-cutoff barriers.

For higher geometric columns j>=J, the finite Lambert prefix involves only
row indices d<=n/J. Primes larger than n/J therefore do not occur in these
row factorial denominators. This suggests larger rough-factorial moduli.
However the omitted low-column tails must also be included in the analytic
error. Keeping J fixed leaves the same large-tail problem. Letting J grow
changes the collection of factorial-power constants being subtracted and
does not yield an integer linear form in the single original sum. No
uniform elimination or nonvanishing argument was obtained.

These are informal observations only. No new compatible representation,
nonzero integer-form sequence, or infinite carry-change argument was proved
in this pass. No new Lean declarations were added. A renewed attempt to
fetch https://www.erdosproblems.com/68 failed with DNS resolution failure,
so no current literature update was retrieved.
