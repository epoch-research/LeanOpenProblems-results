# Power-size representation peaks for automatic additive bases

## Original task status

The conjecture in Spec.lean is still unproved and undisproved. Its import,
statement, and original sorry are unchanged. No final proof was submitted.

## New checked endpoint

Let A be recognized, including zero-padded words, by a finite DFA in any
base b>=2. Assume A is an eventual additive basis: r_A(n)>=1 for all
sufficiently large n. Then there is an integer e>=1 such that

    for every N, some n>=N satisfies n <= r_A(n)^e.

Equivalently these are at least fixed-positive-power peaks; no logarithmic
limit or upper bound is assumed. The exponent is not optimized.

Two checked consequences are:

* It is impossible that r_A(n)^e/n tends to zero for every natural e.
* For every real K and natural d, the eventual cap

      r_A(n) <= K log(n+2)^d

  is impossible.

Thus a uniformly polylogarithmic AUTOMATIC additive basis cannot provide
a larger smooth profile for a later thinning construction. This conclusion
does not concern arbitrary nonautomatic sets or all thinning constructions.

## Proof ingredients

The existing digit-loop injection is extracted as a standalone peak lemma:
two distinct equal-length loops in a common accepting context produce,
for every k, a target n<=D B^k with r_A(n)>=2^k. The ordinary integer digit
encoding and its actual sums are retained.

If all productive equal-length loops were unique, the existing last-visit
coding bound would make count(A,b^k) polynomial in k. The existing elementary
basis-count bound excludes that for an eventual basis. Hence such branching
loops exist.

For the power conclusion choose K with B<=2^K. At a sufficiently late
peak, D<=r_A(n), and therefore

    n <= D B^k <= r_A(n)^(K+1).

The bound r_A(n)<=n+1 ensures these targets are arbitrarily late. Finally,
any fixed power of log(n+2) is o(n), which contradicts the peak inequality
under the asserted polylogarithmic upper cap.

## Verification and scope

DfaPowerPeakExplore.lean compiles without warnings and has a current olean.
DfaPowerPeakAudit.lean and its saved log audit all five declarations, using
only propext, Classical.choice, and Quot.sound.

No automaticity or finite-memory assumption appears in Erdos66.erdos_66,
and none has been deduced from it. This is not a negation of that conjecture
and cannot replace its sorry. The all-target construction and universal
obstruction gaps remain unresolved.
