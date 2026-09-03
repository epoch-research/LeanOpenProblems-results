# Square-modulus polynomial graph capacity

## Original task status

The original conjecture in `Submission/Spec.lean` remains unresolved. Its
import, statement, and original `sorry` are unchanged. No proof/disproof was
submitted. SHA256:

    32d7caa914aad816045b3efa978ba8171e246a4dc01a8e77f192008b25ff41a0

## Motivation

Nested prime-power rings were considered as an alternative to incompatible
prime-field periods. Compatible reductions do not preserve the relevant
finite-field curve bounds: square-zero directions make every polynomial
locally affine. The results below quantify this obstruction even after
arbitrary within-curve deletion. They are restricted-class results, NOT a
negation of the original existential conjecture.

## Production files and audit

1. PolynomialSquareZeroFiberExplore.lean
2. RadixPlaneSumSupportExplore.lean
3. PolynomialRingGraphCapacityExplore.lean
4. PolynomialRingCoverCapacityExplore.lean
5. PolynomialRingAnnulusExplore.lean

All five compile without warnings and have current oleans. The audit
`PolynomialRingCapacityAudit.lean` checks 26 declarations. Its saved log
contains only `propext`, `Classical.choice`, and `Quot.sound`. The production
files contain no placeholders or additional axioms. `PrimePowerGraphChecks`
and `PolynomialCoverChecks` are API scratch files, not dependencies.

## Exact square-zero calculation

Let q>0, M=q^2, and P be ANY polynomial over ZMod M. No prime or degree
hypothesis occurs. If x has residue r modulo q, then

    (x-r)^2=0 in ZMod M,
    P(x)=P(r)+P'(r)(x-r).

For two inputs in this residue class,

    (x,P(x))+(y,P(y))
      = (x+y, 2P(r)+P'(r)(x+y-2r)).

There are at most q possible values of x+y, because its residue modulo q
is fixed. Thus pairs within one input class occupy at most q plane-group
sum targets.

## Ordinary integer carries are included

Use the existing standard encoding

    code_M(x,y)=x.val+M*y.val.

For two plane points, their ordinary sum is

    code_M(x+y)+M*c_0+M^2*c_1,
    c_0,c_1 in {0,1}.

This is an exact identity, not an additive embedding assumption. A plane
sum support of size t therefore gives an ordinary sum support of size at
most 4t. Natural translation by a merely adds 2a to the target.

The general `encoded_pair_mass_bound` injects input pairs into actual
natural representations and proves

    |S|^2 <= L V

when their encoded sums occupy at most L targets, each with representation
count at most V. All cardinality and injectivity hypotheses are explicit.

## Arbitrarily thinned polynomial graphs

Namespace `Erdos66PolynomialRingGraphCapacity` defines

    encodeGraph(q,P,a,x)=a+code_(q^2)(x,P(x)).

This is injective in x and lies in [a,a+q^4). Suppose B is ANY selected
subset of inputs, all its encoded points lie in A, and

    r_A(n)<=V for 2a<=n<2(a+q^4),   V>=0.

Then `polynomial_graph_capacity` proves

    |B|^2 <= 4q^3 V.

Proof: one of the q input residue classes has at least |B|/q selected
points. Its pair sums have at most 4q ordinary values, so its squared
cardinality is at most 4qV. Multiplying by q^2 gives the result.

Neither whole-graph retention nor reflection closure is assumed. This
therefore also applies to arbitrary annular clipping or deletion of the
chosen graph. The polynomial coefficients and degree may vary freely.
A global logarithmic-envelope specialization is also checked.

## Finite families of charts

`Erdos66PolynomialRingCoverCapacity.polynomial_cover_capacity` allows h
polynomials P_i and independent natural translations a_i<=aMax. If a finite
S subset A is covered by their encoded graphs, then under the corresponding
sum cap V,

    |S|^2 <= 4h^2 q^3 V.

The covered part of each chart is selected by membership in S. Overlap
between charts causes no difficulty. The proof bounds the union cardinality
by h times the largest chart contribution; it does not assume the chart
pieces are disjoint or that their entire images lie in A.

## Necessary number of charts for a hypothetical witness

For q=2^J, put

    annulus(A,q)=A intersect [q^4,4q^4).

The already checked positive counting profile of a hypothetical witness
implies that for some gamma>0, eventually

    |annulus(A,q)|^2 >= gamma q^4 J.

The logarithmic cap at targets below 10q^4 is O(J). Combining this with
the finite family bound gives:

`Erdos66PolynomialRingAnnulus.witness_cover_lower`:

For every hypothetical nonzero logarithmic-limit witness A there is eta>0
such that, for ALL sufficiently large J, every cover of annulus(A,2^J) by
h polynomial graphs over ZMod((2^J)^2), with natural translations at most
4(2^J)^4, satisfies

    eta*2^J <= h^2.

The polynomials, degrees, translations, and h may all depend on J.
In particular,
`subcritical_chart_cover_excludes_witness` excludes such covers when

    h(J)^2 / 2^J -> 0.

A logarithmic or polynomial-in-J number of charts is far below this scale.

## Scope and remaining problem

No polynomial-chart cover hypothesis is present in the original conjecture,
and none has been deduced for an arbitrary candidate set. The required
number of charts may grow much faster than sqrt(q). The theorem also does
not cover arbitrary nonpolynomial functions on ZMod(q^2), arbitrary field
basis encodings, or a different spatial construction.

This closes the simple nested-ring polynomial-template idea, including
attempts to rescue it only by deleting a small or moderate portion of each
curve. It does NOT show nonexistence of a logarithmic-limit set.

Further reviews of colored coefficient compression, recursive fine/coarse
operators, and global moment amplification did not produce a sufficient
new theorem. Their previously documented obstacles remain: integer coarse
profiles, mixed-period transitions, cutoff-independent finite feasibility,
and the gap between square-root-logarithmic necessary fluctuations and
logarithmic-order fluctuations. No valid proof for Spec.lean is available.
