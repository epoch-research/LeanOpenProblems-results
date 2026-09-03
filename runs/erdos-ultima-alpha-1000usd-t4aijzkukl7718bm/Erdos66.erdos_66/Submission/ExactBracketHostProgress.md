# Exact brackets, joint triple/boundary host, and one-target downward clipping

## Conjecture status

The original existential conjecture is still neither proved nor disproved.
`Submission/Spec.lean` is unchanged and retains `sorry`.

## Verified files

1. ExactBracketPatternCompactnessExplore.lean
2. ExactBracketPatternCostsExplore.lean
3. ExactBracketPatternHostExplore.lean
4. ExactBracketHostEnvelopeExplore.lean
5. FlexibleRankDownwardRepairExplore.lean
6. RankDownwardEligibilityExplore.lean
7. ExactBracketDownwardClippingExplore.lean
8. ExactBracketHostClippingExplore.lean

All eight compile without warnings and have current oleans.
`ExactBracketPatternAudit.lean` audits all 18 theorem/lemma declarations;
every one depends only on propext, Classical.choice, and Quot.sound.
The old APIs have not been changed.

## Exact infinite brackets retained

The previous positive-pattern compactness theorem weakened finite brackets
to absolute prefix discrepancy at most one. Its new analogue retains the
closed floor/ceiling inequalities separately. The finite pattern selector
already supplied these exact brackets, so all finite potential estimates
are unchanged.

The exact-bracket cost and power-cost APIs retain countably many positive
pattern budgets and every reciprocal-integer two-sided representation
power-potential row. The polynomial pattern wrapper and joint boundary/
triple wrapper now expose the stronger brackets too.

`Erdos66ExactBracketHostEnvelope.exists_exact_bracket_host` constructs ONE
A, K>=0, and threshold functions NB, NT such that:

* Every original harmonic floor/ceiling prefix bracket holds.
* r_A(z) <= K + 34 log(z+2) globally.
* Every original reciprocal-integer power-cost row is summable.
* (j+1) boundary(A,cutoff(j),n) <= 20 log(n+1), eventually for each j.
* For fixed C,h, eventually T, if n<=C*T, z<=T^h, n!=z, then
  fiber(A,T,n,z) <= tripleCap(h).

The global envelope is extracted from the SAME host's j=0 cost row, not
from another existential witness.

## Flexible boundary cutoff

`Erdos66FlexibleRankDownwardRepair.uniformly_eventually_downward_rank_repair`
separates the lower cutoff T in endpoints/fibers from the relocation scale N.
The central target is in [4N,5N]; all edits are in [N,6N]. The triple
certificate is checked at cutoff T, which can be much smaller than N.
All other conclusions of the prescribed-rank downward theorem are retained.

This change is proved by the full finite selection and tail argument; it
is not an extrapolation of the old theorem's restricted statement.

## Endpoint eligibility

For w=ceil(log(N)^8), eventually w*profile(N)<=1/4. If n>=4N, at most TWO
old upper endpoints can satisfy n<2a<=n+2w: the interval has width w, and
exact brackets give occupancy at most 2+1/4, hence at most two.

After excluding these points, the eligible endpoints satisfy

    r_A(n) <= 2|eligible| + 2|boundary(A,d,n)| + 5.

Thus every integer cap q>=2|boundary|+6 has an eligible deletion set whose
exact central decrement clips the old representation count into

    [min(r_A(n),q-1), q].

`uniformly_eventually_downward_clipping` relocates that set to preserve ALL
exact original brackets and controls the signed collateral globally.

## Main one-host corollary

`Erdos66ExactBracketHostClipping.exists_exact_bracket_host_with_downward_clipping`
produces one exact-bracket host A with all the power-cost rows. For EVERY
positive cap coefficient c and collateral coefficient epsilon, eventually
in the individual target n there are finite D,F such that:

* |D|=|F| and F is disjoint from A.
* All edits are in [floor(n/5),2n].
* Every original bracket holds for (A\D) union F.
* Its count at n lies in [min(r_A(n),floor(c log n)-1), floor(c log n)].
* For EVERY z!=n, the count changes by at most epsilon log(z+2).

The proof uses a sufficiently small boundary coefficient, a triple bound
at cutoff floor(n/d^2), and polynomial horizon exponent 34. The finite
relocation selector tests through N^33 and its far-tail theorem covers all
remaining natural targets.

## Quantifier limitation

The finite modifications D,F can depend on n. This is NOT one modified set
satisfying all caps at once, and NOT a convergence theorem. The output is a
clip: an already deficient target is not raised to the requested cap.
Neither triple sparsity nor the cost bounds are asserted for an arbitrarily
updated host. Infinite dense iteration remains unproved.

The positive coordinated theorem still requires total packet demand
S(N) log(N)/sqrt(N) -> 0. The existing shrinking-tolerance exceptional-set
bounds do not verify that condition. These local improvements do not close
that central mathematical gap.
