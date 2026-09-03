# Prefix-copy budgets and nonstationary padding chains

The original conjecture remains unresolved. Spec.lean is unchanged.
These results concern restricted copying constructions, not arbitrary sets.

## New checked counting budget

`PrefixCopyExplore.lean` proves, for every hypothetical witness A and every
fixed positive integer m,

    count A (m*N) / count A N -> sqrt(m).

The input is the earlier exact Tauberian counting profile. No new Tauberian
or analytic axiom is assumed.

Let copiedPrefix(A,N) consist of those a<N for which a and a+N both belong
to A. Its translate injects into the next block, so

    count A N + card(copiedPrefix(A,N)) <= count A (2*N).

Consequently, for every epsilon>0, eventually

    card(copiedPrefix(A,N))/count A N < sqrt(2)-1+epsilon.

In particular, copying the ENTIRE prefix into the next adjacent block is
eventually impossible. This holds at arbitrary scales; no fixed radix,
finite automaton, or fixed repetition period is assumed.

## Nonstationary repetition-chain theorem

`RepetitionChainExplore.lean` defines a chain with finite prefixes B_k,
periods P_k, and integer repetition factors K_k>=1, such that

    B_k subset [0,P_k),
    P_(k+1) >= K_k*P_k,
    B_(k+1) = union_{j<K_k} (j*P_k+B_k).

The amount of empty padding above K_k*P_k is arbitrary and may vary at
every stage. The union of this chain cannot have a nonzero finite
logarithmic representation limit.

Proof: future stages preserve the exact prefix below each P_k. A stage
with K_k>=2 therefore copies the entire limiting prefix below P_k. If the
union were a witness, this would be prohibited once P_k is large enough.
Infinitude supplies such a large period. Every later K_k is then 1, making
the finite prefixes constant and the union finite, a contradiction.

## Principal declarations

Namespace Erdos66PrefixCopy:
- count_multiple_ratio
- copiedPrefix_bound
- eventual_copy_fraction_bound
- eventually_no_full_prefix_copy
- no_log_limit_of_frequent_prefix_copies

Namespace Erdos66RepetitionChain:
- repeatPrefix
- chainSet_below
- copying_stage
- chainSet_finite_of_eventually_one
- no_nonzero_log_limit

Both production files compile and have built oleans. PrefixCopyAxiomCheck.lean
reports only propext, Classical.choice, and Quot.sound for the main theorems.

## Scope

This rules out obtaining a witness solely by iterating the checked
repeat-and-pad cyclic transfer. It does not rule out substantially thinning,
rearranging, or replacing the copied patterns. The budget shows that even
partial copying in the adjacent block must retain at most a sqrt(2)-1
fraction asymptotically. It does not provide a way to select that fraction
with the required mixed representation counts.

No compatible infinite witness or universal logarithmic-scale obstruction
has been obtained. Spec.lean still contains its original sorry.
