# Exact ordered defect and short intervals

This continuation does NOT settle Erdős 773. It does not improve the known
2/3 lower exponent, and no construction of near-linear size was obtained.

## Verified statements

`OrderedCollisionDefect.lean` proves:

1. If a<b<c<d and a^2+d^2=b^2+c^2, then there are positive integers z,y,t with

       b=a+z+2t, c=a+z+2t+y, d=a+2z+2t+y,
       2t(a+t)=z(z+y).

   In particular, the pair-sum defect b+c-a-d=2t is positive and even.
   The factor 2 in the product identity is retained.

2. The exact span identity is

       (d-a)^2 = 4t(a+d+t) + y^2.

   Consequently every strictly ordered collision satisfies

       (d-a)^2 >= 4(a+d+1)+1.

3. For nonnegative integers L,H, if H^2<8L+4, the squares of ALL roots in
   [L,L+H] form a Sidon set. This theorem includes possible three-root
   collisions (repeated middle root), not just four-distinct-root ones.
   Its proof compares pair sums, whose parity agrees in an equal-square-sum
   relation. Distinct pair sums differ by at least two; their squared
   difference cannot fit within the available squared span.

4. The four-root family, for every u>=1,

       a=2u^2+u-1, b=2u^2+3u+1,
       c=2u^2+3u+2, d=2u^2+5u+2

   is strictly ordered, has a^2+d^2=b^2+c^2, and attains the bound in (2):

       (d-a)^2=4(a+d+1)+1.

   Writing L=a and H=d-a=4u+3 gives H^2-8L=16u+17. For every real eta>0,
   the file verifies the existence of a non-Sidon full interval satisfying
   H^2<(8+eta)L. Thus the leading constant 8 cannot be increased uniformly
   in a criterion for FULL intervals. No analogous upper bound on arbitrary
   subsets is asserted. This is not a counterexample to the conjecture.

## Verification

The module compiles without warnings. Its four printed main axiom audits
use only propext, Classical.choice, and Quot.sound. Build/audit log:
`/tmp/ordered-collision-defect.log`.

## Construction review

The normalized equation was reconsidered for a compatible factor-pair
selector and for combining short root intervals. No such selector or
near-linear packing theorem was proved. Disjoint within-fiber difference
sets alone would still leave collisions involving three or four different
fibers. Demanding enough coarse separation to exclude those interactions
reintroduces the previously noted fixed-power loss. These observations are
method analysis, not universal impossibility theorems.

The main conjecture in Spec.lean is unchanged and still has its sole
admission for 0<epsilon<=1/3. No proof submission has been made.
