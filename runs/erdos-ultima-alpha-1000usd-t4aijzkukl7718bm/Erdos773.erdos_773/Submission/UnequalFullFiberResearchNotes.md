# Shorter and unequal full-fiber lengths

This continuation does NOT settle Erdős 773. `Spec.lean` remains unchanged,
with the same admission at line 2031 for 0<epsilon<=1/3. No original lower
exponent or upper bound for the actual square-Sidon maximum has improved.

## Short full fibers

`ShortFullFiberOverlap.lean` extends the earlier gap injection to full index
intervals [0,H], H<=q. For L>0 and 10L<=H, the explicit endpoints from
`FullFiberOverlap.small_gap_collision` lie inside [0,H]. Endpoint uniqueness
in the containing full unit fiber [0,q] still proves injectivity.

The weighted pigeonhole result is unchanged in form:

    (K*T)^2 <= q*(K*U+2*C),   K=L+1,
    T=sum_r p_r^2, U=sum_r p_r^4,

but C is now the actual weighted cross-difference cost for

    V_r = {(qk+r)^2 : 0<=k<=H}.

For prime q, the needed small gaps are units automatically. The canonical
label and full-fiber unit hypotheses remain explicit.

`ShortFullFiberWeightedCeiling.lean` chooses L=floor(H/10) when H>=10 and
proves

    H^2*S^4 <= 40*q^2*H*S + 400*q^2*C,  S=sum_r p_r.

This is `quartic_mass_bound`. The eightfold mass expression

    F = 8*(H+1)*S-C

satisfies, for EVERY 0<=H<=q,

    F^3 <= 320^3 * (q*(H+1))^2,
    F <= 320 * (q*(H+1))^(2/3).

For H>=10 and F>0, C<=16HS and HS^3<=8000q^2 prove the cubic bound. H<10 is
handled separately using |R|^2<=2q and |R|<=q. Nonpositive F is also handled.
The eightfold allowance is intentional; it is used in the length grouping.

## Unequal lengths without a logarithmic loss

`UnequalFullFibers.lean` defines

    cost(R,V,p) = sum_{k in crossKeys(R,V)} p_{k.r}^2*p_{k.s}^2.

It proves monotonicity in labels and fibers, and `cost_partition_le`: the sum
of within-bin costs is at most the global cost. The latter uses disjointness
of cross-key sets from different label bins. Cross-bin costs are nonnegative
and are not erroneously counted twice.

For 0<=H_r<=Hmax<=q, bin r by

    j = floor(log_8(H_r+1)).

Thus 8^j<=H_r+1<8^(j+1). Replace the full fiber in a bin by its full prefix of
index length 8^j-1. Its mass is at most eight times the prefix mass and its
cost is at least the prefix cost. Apply the eightfold certificate bound.

The bin contribution is at most

    320 * (q*8^j)^(2/3) = 320*q^(2/3)*4^j.

The verified geometric estimate sum_{j=0}^J 4^j <= (3/2)*4^J yields

    sum_r p_r*(H_r+1) - cost(R,V,p)
      <= 480 * (q*(Hmax+1))^(2/3).

This is `expression_height_bound`; `actual_expression_height_bound` writes
the mass using the actual value-fiber cardinalities, each proved to equal
H_r+1. No common-length requirement and no logarithmic factor remain.

## Arbitrarily long individually Sidon full fibers

`AllLengthFullFiberCeiling.lean` imports the earlier verified long-fiber
collision and proves the individual bound

    IsSidon(V_r), 0<=r<q  ==>  H_r<15q.

Here V_r is the FULL prefix fiber from index zero. No bound Hmax<=q is needed
in this module. Truncate each H_r to H'_r=min(H_r,q); then

    H_r+1 <= 15*(H'_r+1),
    cost(truncated fibers,p) <= cost(original fibers,p).

Rescale probabilities to p_r/3. Its mass is one third of the old mass, and its
four-vertex cost is one eighty-first. In particular,

    15*M-C <= 27*M-C = 81*(M/3-C/81),

where M is the truncated mass and is nonnegative. The unequal short-fiber
bound gives, for any Hmax bounding all H_r,

    sum_r p_r |V_r| - cost(R,V,p)
      <= 38880 * (q*(Hmax+1))^(2/3).

Public theorem: `AllLengthFullFiberCeiling.actual_expression_height_bound`.
Hypotheses include prime q, canonical unit residues, PairMatching q R,
individual Sidonness of every full fiber, and probabilities in [0,1].

## Restricted construction-size corollary

`sidon_full_union_card_bound` assumes the ENTIRE full-fiber union is Sidon.
The exact compatibility criterion then makes its cross-key set empty. With
p_r=1, the certificate equals the actual union cardinality, so the same
38880*N^(2/3) bound holds for the size of this restricted full-fiber Sidon
construction, N=q*(Hmax+1).

This strengthens the earlier three-quarters construction ceiling under the
ADDITIONAL prime-modulus and unit-residue hypotheses. It is still NOT an
upper bound for arbitrary Sidon subsets of the first N squares.

## Scope and what is still missing

* These are full PREFIX index intervals 0,...,H_r, with canonical r<q.
* Arbitrary partial index sets can omit the forced collision endpoints; none
  of these bounds establishes a comparable ceiling for them.
* Arbitrarily shifted index intervals are not covered by simply calling
  their residues canonical; their starts would have to be handled separately.
* Prime q is used for the unit property of the short gaps. A general composite
  modulus version is not proved here.
* The expression bound does NOT bound the maximum Sidon-subset cardinality of
  a nonsidon full-fiber union. The genuine size corollary requires the union
  itself to be Sidon.
* The construction's height N=q*(Hmax+1) is a bound, not necessarily its exact
  maximum root. No claim using a smaller unspecified height is made.

The unconstructed object needed for progress is still an actual near-linear
square-value family with sufficiently small collision cost (or a genuinely
different selection theorem), not merely adjustable full-fiber probabilities.

## Verification

All four modules compile without warnings or admissions, with built `.olean`
files and printed audits using only propext, Classical.choice, and Quot.sound.
None imports the admitted Spec.lean. Logs:

* /tmp/short-full-fiber-overlap.log
* /tmp/short-full-fiber-weighted-ceiling.log
* /tmp/unequal-full-fibers.log
* /tmp/all-length-full-fiber-ceiling.log

Spec.lean SHA-256 remains
917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14.
No proof has been submitted.
