# Erdős 371: what the skew-adjacency / expansion strategy can and cannot prove

## Status

This note does **not** establish the natural density of `P(n+1)>P(n)`. It gives exact obstructions to several proposed operator/moment arguments, an arithmetic cycle-rigidity lemma, and a precise remaining operator target. No Lean file has been edited, in particular not `Submission/Spec.lean`.

The main new conclusions are:

1. Row balance holds for a **complete** partition of the integer path, not for the induced graph on large primes. The omitted class can carry the entire balancing current.
2. Even an almost perfectly expanding undirected graph, polynomially large class sizes, exact balance, and realization as a projected path do not imply small skew norm or rectangular current. There is an explicit Eulerian-tournament counterexample.
3. A cycle-product identity proves genuine rigidity. But equality of cofactor products does not force skew cancellation: a verified four-prime example inside the `a=.6, b=.9` rectangle survives that rigidity and contributes positively to an even moment.
4. The elementary rigidity range and the useful raw-trace moment range are disjoint throughout the supercritical regime. At dyadic exponents `.6/.9`, an ideal square-root-degree trace argument needs order at least 14 for a power saving, whereas product-size rigidity stops at the order-4 threshold.
5. **Untrimmed** normalized operator-norm convergence to zero is actually false, unconditionally, by an application of Maynard's theorem for admissible linear forms. This obstruction uses bounded-multiplicity vertices near X, not the polynomial-degree interior. Trimming them is legitimate, with a quantified cost.
6. Helfgott–Radziwiłł 2103.06853 does not provide the missing interior estimate: its operator, harmonic-degree parameter, size restrictions, and locality mechanism differ in essential ways.

None of the graph counterexamples is an arithmetic counterexample to Erdős 371. The moment-range comparison is an obstruction to the specified **raw trace plus elementary product-rigidity mechanism**, not a theorem excluding every possible arithmetic high-moment method.

## 1. Exact normalization and the missing row-balance term

Let X be an integer and fix a>1/2. Take X large enough that X^(2a)>2X+2. On the positions 1,...,X+1 define a color c(n): the unique prime p>X^a dividing n, if it exists; otherwise color 0. Include primes through X+1. Replacing the user's upper prime endpoint X by X+1 changes the requested rectangle by at most an endpoint term.

Let F(n,v)=1_{c(n)=v}, let S(n,n+1)=1 for n<=X, and write

    C=F^T S F,    A=C-C^T,    D=F^T F=diag(m_v).

For a large-prime color, m_p=floor((X+1)/p), and A(p,q) is exactly the CRT skew count in the question. Put E=F D^(-1/2). Its columns are orthonormal, so

    K=D^(-1/2) A D^(-1/2)=E^T(S-S^T)E,    ||K||<=2.             (1)

The same compression identity holds if only some large-prime columns are retained.

For prime sets U,V,

    |sum_{p in U,q in V} A(p,q)|
       <= ||K|| sqrt((sum_U m_p)(sum_V m_q)).                  (2)

Each mass sum is O(X). Thus an o(1) normalized norm on the appropriate trimmed prime space would suffice, and would give considerably more than fixed exponent-cutoff cancellation.

For a complete partition, telescoping gives the exact identity

    sum_v A(u,v)=1_{c(1)=u}-1_{c(X+1)=u}.                      (3)

For the induced large-prime graph, however,

    sum_{q large prime} A(p,q)
       =-1_{p | X+1}-A(p,0).                                 (4)

There is no reason for A(p,0) to be O(1). It can have the scale of m_p. A current from one prime box into another can be balanced through the omitted class, rather than by cycles contained entirely in the large-prime graph.

Also distinguish **class multiplicity** from **retained graph degree**. The assertion m_p~X/p is elementary. A comparable number of neighbors in a prescribed q-box is not an established row-by-row consequence. For all large-prime neighbors one has only the immediate upper bound

    sum_q |A(p,q)| <= 2 m_p.

The heuristic degree X/(p log X) is appropriate to one dyadic q-block. Across a fixed power interval, the harmonic prime mass is a constant instead of 1/log X. Polynomially many multiples of p do not by themselves prove polynomial degree into the chosen q-set.

## 2. A projected-path graph can expand perfectly and retain linear current

Let m be odd. Partition 3m vertices into U,V,W, each of size m. Orient every cross edge cyclically

    U -> V,    V -> W,    W -> U,

and orient each internal complete graph as a regular tournament. Every vertex has equal in- and out-degree

    d=(3m-1)/2.

The directed graph is connected and Eulerian. Follow an Euler tour and color the positions of an ordinary directed path by the successive tour vertices. Its projected adjacency is exactly this tournament. The length of the path is

    L=3m d=(9m^2-3m)/2.

Every color occurs d times, apart from the one extra occurrence of the starting color at the final endpoint. Thus the color masses are polynomially large in L. Its skew adjacency A has entries in {0,+1,-1} and A 1=0, but

    sum_{u in U,v in V} A(u,v)=m^2 ~ (2/9)L.                 (5)

The unsigned adjacency |A| is J-I. Its normalized nonconstant eigenvalues are all -1/(3m-1): the undirected graph is as strongly expanding as possible.

On block-constant vectors, A acts as

    m * [[0,1,-1],[-1,0,1],[1,-1,0]],

with eigenvalues 0,+i sqrt(3)m,-i sqrt(3)m. With cyclic color masses d, the normalized skew norm is at least sqrt(3)m/d -> 2/sqrt(3). For the ordinary path's one changed endpoint mass it is at least sqrt(3)m/(d+1), with the same limit.

This is an exact obstruction to inferring skew cancellation from projected-path structure, balance, large degree, and even optimal **undirected** expansion. It deliberately does not reproduce divisibility by primes.

## 3. What cycle rigidity actually proves

A closed walk in the support of A is described by

    p_i a_i + sigma_i = p_(i+1) b_i,    sigma_i in {+1,-1},
    p_(r+1)=p_1,

where both endpoints of every edge lie in [1,X+1]. Set n_i=p_i a_i. Multiplying all the equations and telescoping the difference of the two products gives

    (product_i p_i) (product_i b_i-product_i a_i)
       = product_i(n_i+sigma_i)-product_i n_i,

and therefore

    |product b_i-product a_i|
       <= r (X+1)^(r-1)/(product p_i).                       (6)

In particular, if product p_i>r(X+1)^(r-1), then

    product a_i=product b_i.                                (7)

An all-forward directed cycle has every sigma_i=+1, making the right side of the product identity strictly positive. Such a directed cycle is therefore impossible in this range. For instance, if all p_i>X^c, there are no all-forward cycles of a fixed length r with r(1-c)<1, once X is large enough.

But even spectral moments do not count only all-forward directed cycles. They also count mixed-orientation walks and backtracks. For real skew A,

    tr((A A^T)^k)=(-1)^k tr(A^(2k)).                         (8)

Reversing a closed walk of length 2k multiplies its A-entry product by (-1)^(2k)=1. The reversed walk contributes the **same**, not the opposite, sign. Odd traces vanish automatically and give no norm information.

### A positive non-backtracking prime cycle survives (7)

Take X=10,000,000 and the four primes

    p=31,729, r=32,063, q=2,284,489, s=2,030,657.

They satisfy the exact equations

    72 p + 1 = q,
    285 r + 1 = 4 q,
    190 r + 1 = 3 s,
    64 p + 1 = s.                                           (9)

All four lower consecutive endpoints are <=X. Every relevant prime product exceeds 2X+1, so the opposite CRT solution lies above X. Hence

    A(p,q)=A(r,q)=A(r,s)=A(p,s)=+1.

Both p,r are between X^.6 and X^.9, and both q,s exceed X^.9. The walk p,q,r,s,p contributes +1 to tr(A^4), and equivalently to the appropriate rectangular fourth moment. Its reverse also contributes +1.

For this walk the cofactor lists are

    a=(72,4,190,1), b=(1,285,3,64), sigma=(+1,-1,+1,-1),

and both products of cofactors are 54,720. Moreover,

    p q r s = 4,719,393,428,913,071,984,071
       > 4 (X+1)^3 = 4,000,001,200,000,120,000,004.

Thus the example is inside the very regime in which (6) forces equality of the products. It rules out an algebraic claim that this equality itself kills, pairs off, or forbids the relevant positive even-cycle contributions. It makes no assertion about an asymptotic abundance of these four-cycles.

Primality of all four numbers was checked by trial division through their square roots. Both CRT residues for each edge were also computed exactly.

## 4. The raw trace method needs moments beyond elementary rigidity

Take a dyadic rectangular block R=A|_(P,Q), where p~P=X^alpha and q~Q=X^beta, with 1/2<alpha<=beta<1. Write

    r=#rows, s=#columns, E=sum_{p,q}|R(p,q)|.

Since entries are 0,+1,-1, E=tr(R R^T). For E>0 put

    T=(sqrt(r s)/E) R.

The target ||T||=o(1) gives a relative rectangular saving:

    |1^T R 1| <= E ||T||.

The following inequality is unconditional, by convexity applied to the r nonnegative eigenvalues of R R^T:

    tr((T T^T)^k) >= r (s/E)^k.                             (10)

A raw bound ||T||<=[tr((T T^T)^k)]^(1/(2k)) cannot beat this dimension cost.

In the favorable natural-size regime E~X/(log X)^2, with r~P/log X and s~Q/log X, the lower bound in (10) has order

    X^[alpha-k(1-beta)] (log X)^(k-1).                      (11)

This regime is used as a benchmark, not asserted as an unconditional asymptotic for every prime block. Even ideal square-root-degree moment upper bounds need

    k>alpha/(1-beta)                                       (12)

to produce a power-saving norm; at equality the natural-size logarithmic factor in (11) is already unfavorable. For alpha=.6,beta=.9 this means k>=7, i.e. a moment of order at least 14. Using just E<=2X gives the same power threshold, without any conjectural edge-count estimate.

For a walk alternating k primes near P with k near Q, (6) forces product equality by size only when

    (P Q)^k >> X^(2k-1), or k(2-alpha-beta)<1.               (13)

For .6/.9 this is k<2, with k=2 depending on constants; it says nothing of this form at k>=7. More generally the ranges are disjoint, since

    alpha/(1-beta) - 1/(2-alpha-beta)
       = (1-alpha)(alpha+beta-1)
           / ((1-beta)(2-alpha-beta)) > 0.                 (14)

This does **not** prove that refined divisor counting at higher moments is useless. It proves that the small-product integer-rigidity argument is exhausted before a plain trace argument becomes effective.

### Absolute-value cycle counting can never give the relative norm saving

Put U=(sqrt(r s)/E)|R|. Testing against the normalized constant vectors gives ||U||>=1, so

    tr((U U^T)^k)>=1                                       (15)

for every k. Termwise absolute values in the walk expansion bound the signed moment by this unsigned moment. Thus an argument that only counts allowed cycles and discards their signs cannot obtain ||T||=o(1): the unsigned Perron contribution is exactly at the scale one needs to save. A genuinely sign-sensitive arithmetic input, not merely an upper bound on unsigned cycles, is indispensable.

## 5. An additional arithmetic obstruction: the untrimmed normalized norm does not vanish

For any fixed a<1, consider K_X=D^(-1/2) A_X D^(-1/2) on all primes X^a<p<=X, where D(p,p)=floor((X+1)/p). Then

    limsup_(X->infinity) ||K_X|| > 0.                       (16)

Here is an unconditional proof using Maynard's theorem for admissible linear forms.

First construct, for any prescribed finite k, distinct positive integers a_1,...,a_k such that

    |a_i-a_j|=gcd(a_i,a_j) for all i!=j.                    (17)

Start with {1}. Given a finite set S with this property, take M divisible by every element of S and every nonzero difference of its elements. Then {M} union {M+s:s in S} again has the property and has one extra element: each pairwise difference divides either member, so equals their gcd.

The fixed forms L_i(t)=a_i t+1 are admissible, since t=0 avoids every possible fixed prime divisor. For k sufficiently large, Maynard's theorem gives infinitely many t for which at least two forms are prime. Choose such a pair with a_j>a_i, let delta=a_j-a_i=gcd(a_i,a_j), and set

    u=a_j/delta, v=a_i/delta, p=a_i t+1, q=a_j t+1.

Then u-v=1 and

    u p-v q=1.

At X=v q=u p-1, the edge q->p is present. For large t, pq>2X+1, so its opposite CRT edge is absent. Also

    m_p=u, m_q=v, |K_X(p,q)|=1/sqrt(u v).

There are only finitely many possible pairs (u,v), and X tends to infinity. Both p and q are comparable to X and eventually exceed X^a. This proves (16).

The exact input is the fixed-linear-form consequence of James Maynard, *Dense clusters of primes in subsets*, arXiv:1405.2593, Theorem labelled `thrm:ShortIntervals`, taking m=2 and y=x (local source `Subsets.tex:82-88`). Its applicability here does not require the full prime-tuple conjecture.

This obstruction is confined to vertices with **bounded class multiplicity**. It does not refute a small-norm conjecture on X^a<p<=X^(1-epsilon), or the bounded-weight cut estimate, much less Erdős 371.

There is also a rigorous infinite-family supplement to the four-cycle example. Apply the same linear-form theorem with m=4 instead of m=2. Infinitely often, four of the forms are prime, and every pair of these primes is joined by an edge with fixed bounded cofactors. All arrows point from the larger slope to the smaller one. Put the two smaller primes on one side and the two larger on the other: the alternating four-cycle has sign product +1. Now take X=floor(t^(5/4)), rather than X comparable to t. The four primes are of size X^(.8+o(1)), their class multiplicities have size X^(.2+o(1)), all the bounded-cofactor edges remain below X, and the prime product exceeds 4(X+1)^3. Thus positive, product-degenerate non-backtracking four-cycles occur infinitely often even at polynomially large class multiplicities. This does not create a nonvanishing trimmed norm: a fixed number of such edges is far too sparse, and the normalized entries tend to zero. It only refutes a proposed algebraic elimination of those cycles.

### Legitimate trimming

For fixed 0<epsilon<1/2, the number of integers <=X+1 with a prime factor >X^(1-epsilon) is

    sum_{p>X^(1-epsilon)} floor((X+1)/p)
       = X log(1/(1-epsilon))+o(X).                         (18)

Uniqueness of such a prime factor and Mertens' theorem give this directly; the aggregate floor error is O(pi(X))=o(X). Each such position touches at most two path edges. Therefore removing all these prime classes changes any bounded-weight skew sum by O(epsilon X)+o(X). One can fix epsilon, work at the original scale X, and let epsilon decrease only after taking a limsup.

Thus the correct strong operator target would be an o(1) norm on the **trimmed**, polynomial-multiplicity space, or a still weaker cut-specific assertion. Equation (16) explains why an entirely untrimmed operator theorem is the wrong goal.

## 6. What Helfgott–Radziwiłł actually supplies

The local source of arXiv:2103.06853 is `/corpus/src/2103.06853/trace.tex`. The following were checked directly.

- Lines 102-113 and 186-202: the vertices are integers N<n<=2N, and the centered operator is

      H f(n)=sum_{ell in P, sigma=+/-1}
                (1_{ell|n}-1/ell) f(n+sigma ell),

  with endpoints restricted to the interval. The edges have short additive lengths ell. This is not the prime-class compression of the length-one shift.

- Lines 208-229: the Main Theorem requires harmonic degree L=sum_(ell in P)1/ell>=e,

      log H <= sqrt(log N/L),
      1<=K<=log N/(L (log H)^2),

  as well as a lower-prime-cutoff condition. Its restricted operator has norm O(sqrt(K L)), with exceptional-set bound

      |V minus good set| << N exp(-K L log K)+N/sqrt(H_0).

  For suitable parameters this is a density-near-one restriction. The normalized relative error is useful as L grows.

- In a fixed interval of primes above X^(1/2), harmonic mass is at most log 2+o(1), not a growing parameter; primes of polynomial size also violate the theorem's upper H range. The many multiples in one projected class do not supply the theorem's harmonic degree L.

- Lines 498-552 describe both the locality-to-eigenvalue-multiplicity argument and the cancellation for singleton prime edge lengths produced by centering. The projection onto a prime class averages positions spread across the whole interval, so the compressed operator no longer has their short-edge locality. Skew-symmetrization alone is not their singleton-centering mechanism.

- Lines 328-360 display the correlation consequence as a sum over intervals N/ell<n<=2N/ell. No passage from this scale average to a fixed natural-density scale is made here.

- Lines 7556-7563 explicitly discuss a different division-type graph with edges {n,n/p+1} and note the difficulty of nonlinear divisibility relations. This is a useful warning against treating the result as a black-box expansion theorem for all prime-factor graphs.

## 7. Outcome

A new successful moment strategy would need a quantitative estimate for **signed mixed-orientation cofactor systems at moment orders beyond the range (13)**, or a new arithmetic substitute for the HR locality/multiplicity argument. The displayed cycle identity, positive prime four-cycle, and unsigned Perron obstruction identify exactly what such an estimate must overcome.

The fixed `.6/.9` rectangular estimate is not proved in this note. What has been proved is that the suggested automatic inferences from row balance, undirected expansion, directed-cycle scarcity, or product-equality rigidity are invalid; that the raw-trace and elementary-rigidity ranges do not overlap; and that untrimmed normalized norm decay is actually false. The remaining trimmed, sign-sensitive operator/cut question is distinct and is not excluded by these obstructions.

## Verification

- The four-prime cycle was checked with exact integer multiplication, trial-division primality tests, and both CRT residues.
- The Eulerian-tournament formulas were checked numerically for m=3,5,11,51, including row balance, unsigned adjacency, cut mass, and normalized skew norm.
- The slope-set recursion used in (17) was checked on its first six sizes; its proof above is independent of that finite check.
- No inference from those finite computations to asymptotic prime-cycle cancellation is made.
- `Submission/Spec.lean` SHA-256: `d48bb112dcd4fd5c98dae80077b7384df62a14ef9a919fe7d476b9c5ace427bb`.
