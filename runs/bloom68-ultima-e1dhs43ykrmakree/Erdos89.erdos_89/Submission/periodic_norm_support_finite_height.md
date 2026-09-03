# Finite-height limits of the periodic norm theorem

## Scope

The fixed-modulus theorem in `periodic_norm_support_audit.md` is valid. This
note records what can and cannot be transferred to finite sets. In particular,
it gives an exact actual-endpoint cyclic-gap lemma, but **does not prove or
disprove** the requested universal contraction

    K(Q)^2 >= K(P)^2-C,        K(P)=|P|/D(P),
    2<=|Q|<=|P|/2,

whether Q is an ideal-coset/convex-window selection or an arbitrary subset.
No solution of the sharp distinct-distance problem is claimed.

Write F_B(X) for actual Gaussian norms in residues B, C_B(X) for sums of two
squares satisfying the exact local conditions, and lambda_B for their limiting
Landau probability. Always F_B<=C_B. These two populations are not equal in
general, even at a fixed modulus.

## 1. A genuine local/global failure, and a fixed-modulus quantitative barrier

Let M=13, b=2+6i, A={0,b}, and B={0,b,-b}. The nonzero residues have norm image
1+13Z_13, because N(b)=40==1 mod 13 and the norm map is a submersion there.
The zero residue has norm image 169Z_13. Thus

    delta=2/169,    lambda_B=1/13+1/169=14/169,
    C_B(X)=#{m in S, m<=X : m==1 mod 13 or 169|m}.                (1.1)

Norm 1 is genuinely locally attainable in b, not just a solution of an
insufficient congruence test. Nevertheless its only Gaussian representations
are the four units, none of which is 0 or +/-b modulo 13. Therefore

    C_B(1)=1,       F_B(1)=0.

The smallest actual positive norm in B is 40. Further exact failures include
313=N(-12+13i) and 677=N(1+26i): their representations reduce to global-unit
residues modulo 13, not to B.

### Infinitely many failures of order at least X/log X

The ray group modulo (13) has order

    |(O/(13))^*|/4 = 12^2/4 = 36.

The identity ray class contains asymptotically Li(X)/36 prime ideals of norm
at most X. Up to O(sqrt(X)) degree-two ideals, these come in conjugate pairs
above rational split primes q. Each such q has a generator congruent to a
global unit modulo 13, so q==1 mod 13. All representations of q reduce to
the four global-unit residues, and none belongs to B. Hence

    C_B(X)-F_B(X) >= (1/72+o(1)) X/log X.                        (1.2)

In particular an O_M(X/(log X)^(3/2)) saturation error is **false**, even for
this one fixed difference mask. The little-o relative error in the audited
theorem cannot simply be upgraded to the accuracy needed for a constant
squared-potential transfer.

This has an actual-set consequence. For the corresponding fixed periodic
disks P_R, let X=4R^2, n=|P_R|, and L=log X. Then

    n ~ (delta pi/4)X,   C_B(X) ~ lambda_B kappa X/sqrt(L),
    D(P_R) <= F_B(X) <= C_B(X).

With E=C_B-F_B, the elementary inequality (1-u)^(-2)>=1+2u gives

    K(P_R)^2 - (n/C_B(X))^2
       >= 2 n^2 E/C_B(X)^3
       >> sqrt(log X).                                        (1.3)

Thus **even the exact local-admissibility capacity**, rather than merely its
leading asymptotic, differs from actual support by an unbounded squared-ratio
amount on this fixed family. Using that capacity as the denominator in a
localization theorem cannot be transferred to actual K with an O(1) loss.

This does not refute contraction: the deficits at parent and child scales
might cancel in a support-sensitive argument. It identifies a missing
quantitative comparison, not an impossibility theorem for all selectors.

Exact enumeration for this B gives:

| X | S(X) | C_B(X) | F_B(X) | missing |
|---:|---:|---:|---:|---:|
| 1 | 1 | 1 | 0 | 1 |
| 40 | 20 | 2 | 1 | 1 |
| 1,000 | 330 | 30 | 21 | 9 |
| 10,000 | 2,749 | 237 | 189 | 48 |
| 100,000 | 24,028 | 2,029 | 1,649 | 380 |
| 1,000,000 | 216,341 | 18,153 | 15,059 | 3,094 |

The table is not used to infer (1.2); the ray-prime argument proves it.

## 2. Varying M and R: an explicit primitive obstruction to uniform saturation

There is also a simple actual-set family on which the complete fixed-modulus
asymptotic cannot be made uniform. Let p tend through primes 1 mod 4, put
r=floor(p/5), and choose m=o(p) with m>=2 (for example m=floor(sqrt(p))). Set

    P={0,...,m-1} union {r,...,r+m-1} subset Z subset Z[i],
    R=r+m-1,       M=p,       A=P mod p,       B=A-A.

For all sufficiently large p, r>2m and p>4R. The set is Gaussian-primitive,
since 1 is a difference. Its periodic disk is exactly P, and its positive
lengths are

    1,...,m-1     and     r-m+1,...,r+m-1.

Thus n=2m and D(P)=3m-2. For any finite P in a radius-R disk and any M>4R,
a vector z of length <=2R reducing to a difference v of P must equal v:
otherwise 0!=z-v in MO has length >=M but <=4R. Consequently

    F_B(4R^2)=D(P)=3m-2.                                        (2.1)

Here all differences are real, and their distinct positive lengths are less
than p/2. Their nonzero squares are therefore distinct modulo p. At the split
prime p every such residue contributes a scalar Haar cylinder of mass 1/p;
the zero vector contributes p^2 Z_p of mass 1/p^2. Hence exactly

    lambda_B=(3m-2)/p+1/p^2.

But, with X=4R^2~4p^2/25,

    [lambda_B kappa X/sqrt(log X)] / F_B(X)
       ~ (4 kappa/25) p/sqrt(2 log p) -> infinity.               (2.2)

So not even a universal positive-constant lower comparison with that main
term can hold at arbitrary M,R. Taking m~sqrt(p) makes n tend to infinity;
this is not merely a bounded-cardinality endpoint issue. It refutes uniformity
of the *complete* main term, without needing to assign the failure separately
to progression counting or to orientation switching.

This family has K(P)=2m/(3m-2) bounded. It is **not** a counterexample to
contraction or to a possible low-D refinement. A theorem could still use a
bounded-K versus support-rich dichotomy, but the audited local proof supplies
no such dichotomy.

The m=2 cases were checked exactly:

    (M,R,n,D,lambda) = (101,21,4,4,405/10201),
                       (1009,202,4,4,4037/1018081),
                       (10009,2002,4,4,40037/100180081).

More generally, the encoding observation preceding (2.1) shows that arbitrary
finite Gaussian sets appear as periodic masks at their original height. One
must not hide that height problem in an o_M term. Nor may one assume
log R=O(log n) for general primitive sets.

## 3. Why the p-adic pinning step is not an actual-endpoint map

In the local proof, an entire residue fiber is filled with arbitrary p-adic
lifts, and its Y-coordinate is reset to b_Y-g **exactly**, not just modulo
p^e. This is legitimate for the cylinder C, but not for a given finite P.

Already at a single split prime, identify the second coordinate of u+vi as
u-s_p v, with s_p^2=-1 in Z_p. If an actual Gaussian integer satisfies

    u-s_p v=-g

exactly, with g an ordinary integer, then v=0 and u=-g: otherwise s_p would
be rational. Thus the infinite local slice with Y=-g is emphatically not a
large slice of actual Gaussian displacement vectors. The global saturation
argument can find another vector with the same scalar norm; it does not
preserve this pinned vector or these chosen endpoints.

At finite height there are two separate losses:

1. scalar norms need sufficiently many orientation-switch prime factors to
   attain the local residue (Section 1 already exhibits many exceptions);
2. a vector in a permitted residue still needs both actual endpoints in P.
   Full periodic disks supply this only with the covering-radius margin
   sqrt(2)M in the audited endpoint sandwich.

The switch proof fixes finite prime reservoirs and then lets the height grow.
The required number of switches and the supply of primes depend on the ray
group modulo M. It provides no n-dependent, height-free control of a selected
finite endpoint set.

## 4. A valid finite cyclic-gap/large-ideal lemma

The following part of the suggested mechanism **does** survive for actual
endpoints, with no height hypothesis and no independence assumptions.

Let L be any product of powers of split rational primes. Choose the two
coordinates X,Y modulo L by CRT so that N(z)==X(z)Y(z) mod L. For a finite
P with at least two occupied Y-residues, let F_r={a in P:Y(a)=r}, m_r=|F_r|.
Order the occupied residues cyclically. Their positive gaps sum to L, so
some r, with next residue r+g, satisfies

    m_r/g >= |P|/L.                                            (4.1)

Fix an **actual** b in the next fiber. Let d=gcd(g,L). For every a in F_r,

    N(a-b) == -g(X(a)-X(b)) mod L.                              (4.2)

Multiplication by g has kernel of size d on Z/LZ. Therefore, putting

    t=|{X(a) mod L/d : a in F_r}|,

we obtain the exact support-sensitive bound

    |{N(a-b):a in F_r}| >= t,        hence t<=D(P).              (4.3)

All these norms are positive because the two Y-fibers are distinct. This is
an injection of *residue labels into possible norm labels*, not a Haar
comparison or a statement that the pinned norms themselves are uniform.

Partition F_r by X modulo L/d. The resulting t subsets are full intersections
of P with cosets of the Gaussian ideal

    J=product_(p^e||L) P_p^(e-min(v_p(g),e)) conjugate(P_p)^e,
    N(J)=L^2/d,                                                 (4.4)

where P_p is the prime ideal corresponding to X. In particular some actual
ideal fiber Q satisfies

    |Q| >= m_r/t >= m_r/D(P).                                   (4.5)

All its squared distances are divisible by N(J); dividing by a generator of
J is a genuine Gaussian similarity and preserves |Q|, D(Q), and K(Q).
If there is just one occupied Y-residue, the whole P is in one ideal coset
of norm L and can instead be normalized directly with no point loss.

This permits arbitrarily large ideal rescalings and keeps endpoint
correlations. The verification script checks (4.1)--(4.4) on 400 finite actual
sets. However, (4.5) supplies **no adequate upper bound on D(Q)** in terms of
D(P). It is therefore not the desired contraction lemma.

## 5. The entropy budget and the precise remaining Hartley requirement

For any actual point-partition tree ending in singletons, write m_v for a
node's cardinality and p_(w|v)=m_w/m_v for its child probabilities. Then

    sum_(internal v) (m_v/n) H((p_(w|v))_w)=log n.                (5.1)

This is an exact height-free endpoint budget. Unary ideal refinements cost
zero. Their ideal norms can be arbitrarily large: the primitive set
{0,1,2^h,2^h+1} splits into two pairs modulo 1+i, followed by arbitrarily many
unary refinements inside a pair. Thus log N(J) is not automatically an entropy
charge. Large unary rescaling is allowed and harmless for K; the missing
estimate concerns *support loss when points are discarded*.

For an actual child Q with theta=|Q|/|P| and K(P)^2>C, the target contraction
is exactly equivalent to

    log D(P)-log D(Q)
       >= log(1/theta) + (1/2)log(1-C/K(P)^2).                   (5.2)

A balanced child's Hartley-support drop must match its point-mass drop to
accuracy O(1/K(P)^2), not merely within O(1). On extremal-scale lattice
families K(P)^2 is of order log n. A relative support error epsilon can cost
order epsilon K(P)^2 in potential, so an unquantified o(1) does not suffice.
Section 1 shows that even fixed-modulus local-capacity substitution can have
far too large a loss.

The prior notes `adaptive_ideal_entropy_obstruction.md`,
`disk_capacity_localization.md`, and `lattice_energy_obstruction.md` explain
why replacing this order-zero support by positive-order norm entropy, ambient
capacity, or uncoupled ideal collision counts is not justified. The finite
lemma above retains actual support in (4.3), but does not establish (5.2) or
couple its deficit to (5.1).

**Remaining positive task:** control the actual normalized norm-support drop
along endpoint-consistent ideal/window selections, possibly using a bounded-K
versus rich-switch dichotomy and cancellation of parent/child saturation
errors. No such uniform estimate was obtained here. The saved positive
results are the complete fixed-modulus theorem, the exact H=1 saturation
criterion, and the actual finite residue/ideal lemma (4.1)--(4.5); none is
presented as a solution of the original contraction or distance problem.
