# Every finite graph has an integer-square residual realization

## Main task is NOT settled

Spec.lean is unchanged, with its sole sorry at line 2031, for
0 < epsilon <= 1/3. The strongest actual asymptotic lower bound remains
M(N) >= N^(2/3)/500 eventually. No coefficient-one endpoint, new exponent,
or disproof was obtained. Nothing has been submitted.

Spec SHA-256:
917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14

## New completed theorem

Namespace Erdos773.SquareGraphRealization, theorem `realize`.

Given ANY finite simple graph E on Fin n (edges are increasing endpoint
pairs), there is an injective positive natural-valued map f on the carrier

    Vertex E = Fin n + (E x Bool)

with the following properties:

- The four-root square-collision hypergraph is exactly H E. Its edge for
  (a,b) consists of the two core vertices a,b and its two private labels.
- H E is four-uniform and linear: distinct edges meet in at most one vertex.
- For EVERY subset J of the carrier, the square values f(J)^2 are Sidon
  if and only if J is independent in H E. Thus three-root/repeated-entry
  obstructions have not been silently discarded.
- Let I be all private labels. Its square values are Sidon.
- Every ordering of selecting the private labels is legal. More explicitly,
  after any J subset I, every unchosen member of I is available.
- After all labels are chosen, the available vertices are exactly the core.
  Each original edge has residual pair {a,b}, so the residual two-graph is
  exactly E, with original-edge indexing retained.

This shows that the class of finite square-collision carriers does not impose
an a priori restriction on which finite residual graphs can occur. In
particular the previously considered complete bipartite obstruction is not
excluded merely because the hypergraph comes from integer squares.

## Four clean modules

### QuadraticRotationTrade.lean

For independent variables X_a, define formal roots

    core(a) = 5 X_a,
    plus(a,b) = 3 X_a + 4 X_b,
    minus(a,b) = 4 X_a - 3 X_b.

Their squares satisfy the exact trade

    plus(a,b)^2 + minus(a,b)^2 = core(a)^2 + core(b)^2.

A polarization probe at the two endpoints extracts +24 or -24 from the
corresponding private squared root and zero from all other edge indices
and from core squares. Increasing endpoints exclude the swapped-edge alias.

Generic delta-function lemmas identify equal sums and differences of two
unit indicator functions. These are used instead of assuming independence
of formal coefficients without proof.

### QuadraticRotationPairs.lean

`pair_classification` proves that every formal equality of two pair-square
sums is either the ordinary unordered matching or has precisely one of the
prescribed four-root supports.

The type check evaluates every variable at one: core, plus, and minus
squares have values 25,49,1. Their unordered pair sums are distinct except
25+25=49+1, the desired trade. Polarization identifies all private edge
indices, and one-coordinate evaluation identifies core pairs. All cases,
including repeated entries and complementary private pairs, are proved.

`value_injective` verifies injectivity of the formal squared roots.

### QuadraticRotationSpecialization.lean

A finite set of nonzero multivariate polynomials has a simultaneous
nonvanishing rational evaluation with every coordinate in (1,4/3).
The proof uses the nonzero product and MvPolynomial.funext_set on a box
with infinite sides. It is not an unverified genericity assertion.

Apply this to ALL nonzero differences of formal pair-square sums. Every
formal root is positive on this box: in particular 4 X_a-3 X_b>0.
A common positive denominator turns the finitely many rational roots into
positive natural roots. The common scaling preserves every square-pair
relation in BOTH directions.

`exists_integer_model` supplies positive injective integer roots and the
full biconditional between actual and formal square-pair equalities.

There is deliberately NO quantitative root-height estimate. The evaluation
is chosen after the finite family of unwanted relations is specified; this
is not the invalid blanket small-base specialization refuted in older work.

### SquareGraphRealization.lean

Restrict the formal model to the core and the private labels for the
prescribed graph E. An injective embedding into the complete formal model
transfers the classification. Presence of a private label forces its edge
index to belong to E, so no extra prescribed trades survive the restriction.

Public results include `linear`, `four_uniform`, `relation_support`,
`squareEdges_eq`, `sidon_iff_independent`, and `realize`.

## Scope restrictions

1. This concerns a suitable FINITE SUBCARRIER of the positive integers, not
   the entire interval of all roots 1,...,N. Other roots outside the carrier
   may remain available in a process on the full interval.
2. The initial hypergraph is not claimed to be regular. Private labels have
   degree one; core degrees are the graph degrees.
3. This is a finite existence theorem with no useful height/density bound.
   It does not construct near-linear Sidon sets or improve the 2/3 exponent.
4. A rare legal residual state does not refute a high-probability estimate
   for a specified random process. Quantitative trajectory or sampling
   hypotheses can still rule out or control such states.
5. The earlier BipartiteDegreeEnergy theorem gives gap ratio
   1/(2k(k+1)) for K_(k,k+1). Arbitrary-graph realization permits that graph
   here, but no new explicit combined stochastic-energy theorem was added.
6. No claim that every linear four-uniform hypergraph can be realized is
   made. The realized original hypergraphs have two private vertices per
   graph edge and consequently have a large easy independent set.

## Verification

All four modules build cleanly and have oleans. All 23 printed main audits
use only propext, Classical.choice, Quot.sound. There are no admissions or
native_decide calls, and none imports admitted Spec.lean.

Fresh logs:

    /tmp/QuadraticRotationTrade-final.log
    /tmp/QuadraticRotationPairs-final.log
    /tmp/QuadraticRotationSpecialization-final.log
    /tmp/SquareGraphRealization-final.log
    /tmp/spec-rotation-realization-check.log

The temporary RotationCheck.lean was removed. The main file's import and
conjecture statement remain unchanged.
