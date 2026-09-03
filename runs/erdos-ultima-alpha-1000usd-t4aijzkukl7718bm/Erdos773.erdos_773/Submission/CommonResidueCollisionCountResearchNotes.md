# Quadratic collision counts in complete common-residue carriers

The original Erdős 773 conjecture remains UNSETTLED. Spec.lean has not been
changed. Its sole admission remains at line 2035. The active file proves the
range epsilon>1/3; the clean separate endpoint still covers epsilon=1/3.
The actual mathematical gap remains 0<epsilon<1/3.

## New verified module

Submission/CommonResidueCollisionCount.lean imports only FormalConjecturesUtil.
It compiles without warnings, errors, or admissions. All three printed audits
use only propext, Classical.choice, and Quot.sound. Its olean is built.

Log: /tmp/common-residue-count.log
Namespace: Erdos773.CommonResidueCollisionCount

`collisions Q r N` is the finite set of integer quadruples a<d<c<b in [1,N]
with a^2+b^2=d^2+c^2 and all four roots congruent to r modulo Q. Positive
integer roots are used throughout. Each strictly ordered quadruple is counted
once; this is not a count of all ordered presentations of the same support.

For Q>=1, 0<=r<=Q and T>=1, `quadratic_count` proves

    T^2 <= |collisions Q r (20 Q^2 T)|.

Take independent i,j in {0,...,T-1}, and put

    u=Q(2T+i)+r, v=Q(3T+j)+r, m=2Q+1,
    a=mu-Qv, d=mv-Qu, c=mu+Qv, b=mv+Qu.

The bounds u<v<2u ensure 0<a<d<c<b. All four roots are r modulo Q,
all are at most 20 Q^2 T, and their square identity is an exact polynomial
identity. The pair (a,c) recovers u and v, so the parameter map is injective.
No primality assumption on Q or coprimality assumption on r is needed.

`count_at_height` interpolates with T=floor(N/(20Q^2)). For every N>=20Q^2,

    N^2 <= 1600 Q^4 |collisions Q r N|.

`eventual_uniform_count` proves, for every 0<epsilon<=1, eventually in N,
UNIFORMLY for every Q>=1 and r<=Q with Q<=N^(epsilon/8),

    N^(2-epsilon) <= |collisions Q r N|.

The threshold is independent of Q and r. The proof absorbs the coefficient
1600 with N^(epsilon/8), and uses a separate diverging power to ensure the
height condition 20Q^2<=N.

## Scope

This proves that FULL common-residue carriers of subpower modulus still have
nearly quadratically many collisions. It does not give a collision lower
bound for arbitrary sparse selected subsets, and is not an upper bound on
maxSidonSubsetCard. It therefore supplies neither a new actual Sidon exponent
nor a disproof of the original near-linear conjecture.

The direct reflection/rotation review yielded no such arbitrary-subset
estimate. Reflecting a difference is not itself a new equal-sum collision;
using that implication would leave a proof gap. External access to the
problem page again failed at DNS resolution.

No changes were made to the original theorem statement or import. The active
Spec.lean hash is

    f019ff3791c89bbea24fd9b031eb92f7b676baa4b1ff9cebe9f2356121aa6ff0.

A previous submission of this admitted file was rejected. It has not been
resubmitted as a completed proof in this continuation.
