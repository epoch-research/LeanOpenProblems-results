# Symmetry-preserving square-Sidon alteration

The original conjecture remains UNSETTLED. Spec.lean was not edited and
still contains its single admission. The result below is not an exponent
improvement for the unrestricted maximum.

## Completed module

Submission/SymmetricSquareAlteration.lean, namespace
Erdos773.SymmetricSquareAlteration, has 579 lines and builds without errors,
warnings, or admissions. All five printed axiom audits use only propext,
Classical.choice, and Quot.sound. Its imports are clean auxiliary modules,
not the admitted Spec theorem. A built olean is available.

Log: /tmp/symmetric-square-alteration.log

## Main result

For every epsilon>0, eventually for EVERY integer s there is C subset [1,s]
such that C is preserved by a |-> s-a, its integer squares are Sidon, and

    |C| >= s^(2/3-epsilon).

The reflection center is s/2. No primality assumption is required. The set
omits s and the fixed midpoint when s is even.

## Selection units

The labels are [1,floor((s-1)/2)]. Each selected label represents its whole
reflection pair {a,s-a}. The carrier is the union of all such pairs. The
orbit label of a is min(a,s-a), and closure(B)=B union (s-B). For B in the
label interval, closure is symmetric and has exactly 2|B| members.

Three-root AP supports project to at least two labels. A four-distinct-root
square collision projects to either three or four labels, never two. In
the two-label case the four roots would be two full reflection pairs.
Relabeling the square identity shows that each of its three pairings forces
two roots to agree. This argument does not require prime s.

## Explicit finite bound

If every pair codegree at height s is at most K>=0, and 0<=p<=1, there is
such a symmetric square-Sidon C with

    |C| >= 2*(p*floor((s-1)/2) - p^2*|squareAPs(s)|
              - p^3*s*K - p^4*s^2*K).

Four-root supports projected to three labels contain a reflection pair.
Covering them by pairEdges(a,s-a), for 1<=a<=s, bounds their count by s*K.
The total four-root count is bounded by s^2*K. Image-sum inequalities account
for duplicate projected supports, and union/intersection sums account for
overlap between the two kinds of forbidden supports. Ambient alteration
selects labels avoiding all these projected supports. Taking their full
closure gives actual Sidonness, including repeated-summand obstructions.

## Asymptotics

Put delta=epsilon/8, p=s^(-1/3-delta), K=s^delta and S=s^(2/3-delta).
The divisor codegree bound and the AP estimate give K and
|squareAPs(s)|<=s^(1+delta) eventually. There are at least s/4 labels.
The three costs before doubling are bounded respectively by

    S*s^(-1/3), S*s^(-2/3-delta), S*s^(-2delta).

Each decay factor is eventually at most 1/24. Thus |C|>=S/4. The remaining
factor s^(-(epsilon-delta)) is eventually at most 1/4, giving the theorem.

## Scope

This strengthens the construction by imposing reflection symmetry, but
retains the same two-thirds barrier. It neither supplies a near-linear
construction nor a fixed-power upper bound for symmetric sets. In
particular it does not resolve the conditional symmetric reduction, and
no original proof or disproof has been submitted.
