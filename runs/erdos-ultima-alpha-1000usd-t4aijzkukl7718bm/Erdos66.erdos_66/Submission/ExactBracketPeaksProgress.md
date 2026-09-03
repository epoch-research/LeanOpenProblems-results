# Exact harmonic prefix brackets still permit unbounded representation peaks

## Original task status

The existential conjecture is still unproved and undisproved. Spec.lean is
unchanged with its original sorry. No proof or disproof has been submitted.
The new results concern particular bad roundings, NOT every candidate set.

## Checked production files

* CenteredCumulativeRoundingExplore.lean
* LinearRoundingPeakExplore.lean
* ChordPeakExtensionExplore.lean
* ExactBracketPeaksExplore.lean
* BracketLookaheadObstructionExplore.lean

All five compile and have current oleans. ExactBracketPeaksAudit.lean audits
47 declarations. Its log reports only propext, Classical.choice, Quot.sound.
There are no production sorries or new axioms.

## Stronger infinite counterexample within the rounding class

Let P(N)=sum_(i<N) profile(i), for the exact harmonic profile p*p(n)=H_(n+1).
The new endpoint exists_exact_bracket_unbounded_peaks constructs ONE set A
such that:

    floor(P(N)) <= count(A,N) <= ceil(P(N)),  for EVERY N;
    |count(A,N)-P(N)| <= 3/4,               for EVERY N;

and for every natural M,N there is n>=N with

    r_A(n)/log(n) >= M.

Consequently its normalized representation function has no finite limit.
Its actual quadratic rounding error e*e/log does not tend to zero either.
These are actual 0/1 coefficients, not an arbitrary signed sequence.

This strengthens the earlier bounded-discrepancy peak example, whose bound
was 11. More importantly, it retains the EXACT floor/ceiling constraints
used in the newly completed bracket-preserving extension theorem.

## Construction

1. For any cumulative F with F(0)=1/2 and increments in [0,1], define

       A_F={n: floor(F(n+1))-floor(F(n))=1}.

   Its counting function is exactly floor(F(N)). If

       |F(N)-(P(N)+1/2)|<=1/4,

   the counting discrepancy is <=3/4 and the original integer brackets hold.

2. Replace P+1/2 on a window [L,R] by its affine chord, keeping both endpoint
   values EXACT. Its slope lies in [p(R),p(L)], so the increments remain in
   [0,1]. Its cumulative error is at most (R-L)(p(L)-p(R)). The old values
   outside the window are unchanged.

3. Existing harmonic flat windows are shortened from length 2k^20 to k^19.
   This gives L>=k^32, L+k^19<=3k^32, integrated oscillation <=1/4, and
   expected window mass at least k/2.

4. An exactly affine cumulative segment rounds to a Beatty-type set. Pair
   its first and last mass-crossing ranks, second and penultimate, and so on.
   All these paired sums lie in one interval of length TWO. Thus at least
   one of at most two adjacent natural targets has at least half as many
   representations as there are mass crossings.

   The crossing positions, their membership, injectivity, paired-rank sum
   bound, and the representation-count pigeonhole step are all checked.

5. The resulting peak has r_A(n)>=k/4-1 and 2L<=n<2(L+k^19)<=6k^32.
   Since log(n)=O(log k), the normalized peak can be arbitrarily large.

6. Each state agrees exactly with P+1/2 beyond its cutoff. New windows are
   placed after that cutoff; the cutoff is then moved beyond the new peak.
   The cumulative functions stabilize at every coordinate, preserve the
   same quarter-unit allowance, and retain every previous peak. Rounding
   the limiting cumulative function gives the asserted single set.

## Finite prescribed-prefix consequence

exists_exact_bracket_prefix_forcing_peak proves: for every real R and every
starting bound N0, there is N>=max(N0,2) and finite C subset [0,N) such that

* every prefix through N satisfies the exact original harmonic brackets;
* every such prefix has discrepancy <=3/4;
* EVERY superset B of C has r_B(N)/log(N)>R.

The peak is already forced at the VERY FIRST target not determined by
membership strictly below N. Truncating an arbitrary A at N loses at most
two representations at N, which transfers the infinite peaks to C.

This finite theorem does NOT claim that the past representation counts of C
are accurate. The earlier PrefixLookaheadExplore theorem supplies accurate
annular histories with bad lookahead, but does not assert exact brackets.
No combined past-accuracy-plus-exact-brackets statement has been inferred.

## Implication for the current positive approach

The clamped continuation really does regenerate the original brackets;
that positive result remains valid. However, exact brackets alone cannot
supply its missing transition quadratic estimate or a next-target upper
bound. A successful iteration needs a genuinely stronger invariant or
another mechanism controlling these peaks.

Neither this bad example nor its finite-prefix consequence proves the
negation of the original existential conjecture. No valid main submission
is available yet.
