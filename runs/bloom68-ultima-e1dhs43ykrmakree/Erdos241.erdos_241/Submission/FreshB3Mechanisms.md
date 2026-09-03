# Fresh strong-B3 mechanisms: two proved obstructions, not a resolution

## Status

The conjecture `f(N) ~ N^(1/3)` is **not resolved** here. No improvement on the stated general upper bound `n^3 <= (7/2 + o(1))N` is claimed. No unbounded family with fixed cubic excess greater than one is constructed.

This note records two independently derived, fully elementary partial results:

1. An exact exceptional-pencil description for a proposed two-line Bose construction, giving bounds for both cyclic and actual integer versions. It is not enough merely to find a cyclic collision: the integer bound below explicitly allows three different integer lifts of a residue.
2. An explicit unbounded strong B3 family for which a nonzero difference-graph common-neighbor count is at least `2n-4`. This disproves a tempting pointwise route to a sharp upper bound. Its diameter is exponential, so it has **no** asymptotic cubic excess.

Repeated summands are included everywhere. These are independent derivations, not assertions of priority. `Spec.lean` and `Reductions.lean` are unchanged; neither admitted declaration in `Spec.lean` is used.

## 1. A two-line candidate in a genuinely cyclic group

Let `K/F_q` have degree three, and choose `alpha,beta` such that `1,alpha,beta` are linearly independent over `F_q`. Both alpha and beta have degree three. Let `g` generate `K*`, and put `M=q^3-1`.

For `s,t in F_q`, define integers in `[0,M-1]` by

    g^b(s) = alpha-s,
    g^c(t) = (beta-t)^(-1).

For subsets `S,T of F_q`, of sizes `m,n`, consider the actual integer set

    A(S,T) = {4b(s)+1 : s in S} union {4c(t)+2 : t in T}.       (1)

The two parts are disjoint modulo four and are internally injective, so `|A|=m+n`. It lies in `[1,4M]`. The factor four makes the number of second-part summands in a triple recoverable modulo four, including the possibilities 0 and 3. Thus a cyclic B3 certificate modulo `4M` is a valid efficient integer certificate, with no hidden noncyclic embedding assumption.

The full two-line set would have approximately `2q` elements in an interval of length `4q^3`, giving cubic ratio two. The following theorem rules that out even after taking arbitrary parameter subsets.

### Theorem 1 (cyclic and integer bounds)

Write `v=q+1` and `u=m+n`.

* If (1) is B3 modulo `4M`, then

      n(2m-v) <= 2q,       m(2n-v) <= 2q,                    (2)
      u(u-v) <= 4q,       u <= q+4.                        (3)

* If (1) is only assumed to be B3 as an integer set, then

      n(2m-v) <= 6q,       m(2n-v) <= 6q,                    (4)
      u(u-v) <= 12q,      u <= q+12.                       (5)

In particular, for the stated ambient length `4(q^3-1)`, either version has

    limsup |A|^3 / (4(q^3-1)) <= 1/4.

This last normalization concerns the proposed full-length construction. It does **not** by itself rule out selecting and translating a subset into a much shorter interval.

### Proof: exceptional values

Use `1,alpha,alpha^2` as a basis for K. Let `ell` be the coefficient of `alpha^2`, and let

    L = ker ell = span(1,alpha),
    P = {z : ell(z)=1} = alpha^2 + L,
    E = {u in L : ell(beta*u)=1}.

Since beta is not in L, the functional `u -> ell(beta*u)` is nonzero on L. Thus E is an affine line containing exactly q nonzero elements.

A triple with two first-part elements and one second-part element has underlying field product

    u = (alpha-a)(alpha-b)/(beta-t),                       (6)

where `{a,b}` is an unordered multiset pair from S and `t in T`. The numerator is a monic quadratic evaluated at alpha, hence belongs to P.

If `ell(u) != 0`, applying ell to `u(beta-t)` determines t uniquely:

    t = (ell(beta*u)-1)/ell(u).

It then determines the monic quadratic and its root multiset uniquely. Thus all nonunique representations (6) occur at `u in E`; conversely E is exactly the exceptional locus available for such nonuniqueness.

For each fixed t, the products `u(beta-t)` with `u in E` form an affine pencil of monic quadratics

    Q_0(X) + z Q_1(X),       z in F_q,                    (7)

where Q_0 is monic quadratic and Q_1 is nonzero of degree at most one. This is a pencil whose polynomials have no common root, even over an algebraic closure. Here is the needed elementary argument.

Choose `u_* in E` and nonzero `u_0 in L` with `ell(beta*u_0)=0`. The two elements `u_*,u_0` are independent. If Q_0 and Q_1 had a common root, then Q_1 would be linear and its root r would lie in F_q. Since Q_0 is monic, for some h in F_q and nonzero c in F_q,

    Q_1=c(X-r),        Q_0=(X-r)(X-h).

Evaluating and taking a quotient gives

    u_*/u_0 = (alpha-h)/c.

Both u_* and u_0 lie in span(1,alpha). Comparing the alpha-squared coefficient shows that u_0 is a nonzero scalar. But `ell(beta*u_0)=0` would then force beta into L, a contradiction. If Q_1 is constant, coprimality is immediate. There is also no common projective root at infinity, since Q_0 is monic quadratic.

### Proof: the involution and the count

For completeness, a coprime pencil (7) determines a nondegenerate involution on `P^1(F_q)` pairing its two roots. Write

    Q_0=X^2+cX+d,       Q_1=aX+b.

A pair of finite roots r,s belongs to the pencil exactly when

    a r s + b(r+s) + bc-ad = 0.                           (8)

The associated projective fractional-linear involution is

    r -> (-b r-bc+ad)/(a r+b).

Its determinant, up to sign, is `b^2-abc+a^2 d`, nonzero because this expression is `a^2 Q_0(-b/a)` when a is nonzero, and is b squared otherwise. This argument works also in characteristic two; fixed points correspond to repeated roots and are not discarded.

For any involution J on a v-element set and any m-element subset S,

    |S intersect J(S)| >= 2m-v.

Each unordered pair-orbit contained in S accounts for at most two elements of this intersection. Consequently (7) contains at least `m-v/2` unordered multiset pairs from S. A negative right side is simply a harmless lower bound.

Summing over `t in T`, at least `n(m-v/2)` mixed triples have their product in the q-element set E. Under cyclic B3, each element of E can receive at most one such triple. This proves the first inequality of (2).

For integer B3, write the unscaled logarithmic sum of a mixed triple as

    b(a)+b(b)+c(t),

which lies in `[0,3M-3]`. For each fixed residue modulo M there are at most three such integer values. Two triples giving the same one of these integer values would give equal sums in (1). Hence each element of E can receive at most three mixed triples, not necessarily just one. This proves the first inequality of (4). This is the step that handles actual integer embeddings rather than conflating cyclic and integer failure.

Invert the products of triples having one first-part and two second-part elements, and interchange alpha with beta. The same proof gives the other inequalities in (2) and (4), since `1,beta,alpha` are also independent.

Assume without loss that m>=n and set `d=m-n`. Since `0<=d<=q<v`,

    2 n(2m-v) = u(u-v)+d(v-d) >= u(u-v).

Equations (3) and (5) follow. More explicitly, the cyclic bound is

    u <= (v + sqrt(v^2+16q))/2 < v+4,

and the integer bound is

    u <= (v + sqrt(v^2+48q))/2 < v+12.

Taking integer parts yields the claimed `q+4` and `q+12`. QED.

### Exact cyclic criterion, not just a necessary condition

The all-first and all-second triples are individually B3 by the usual Bose argument: equal products of three linear factors give equal monic cubics, because their difference has degree at most two and vanishes at a degree-three element. Inverting the second products does not change uniqueness.

For the two mixed types, the calculation above proves uniqueness away from the corresponding affine exceptional line. Therefore (1) is B3 modulo `4M` **if and only if** no exceptional value has two representations in either of the two pencils. All root choices and triples in this criterion are multisets.

### Explicit pencil for beta=alpha squared

If

    f(X)=X^3+f_2 X^2+f_1 X+f_0

is the minimal polynomial of alpha, then

    E = {1+y(alpha+f_2) : y in F_q},
    Q_{t,y}(X)=X^2-y(f_1+t)X-t-y(f_0+f_2 t).

The root-pair condition is

    (f_1+t)(ab+t)+(f_0+f_2 t)(a+b)=0.                    (9)

Its involution determinant, up to sign, is

    (f_0+f_2 t)^2 - t(f_1+t)^2.

It is nonzero: for a square root r of t in F_(q^2), this expression is `f(r)f(-r)`, and an irreducible cubic has no root in a quadratic extension. This supplies a particularly short direct audit of the exceptional-pair mechanism, including repeated roots.

## 2. An explicit obstruction to a pointwise common-neighbor bound

For a finite strong B3 set A in the integers, let

    D=(A-A) minus {0},       mu(x)=|D intersect (x+D)|.

A tempting strengthening of elementary difference counting is `mu(x) <= (1+o(1))|A|` for every nonzero x outside D. It is false, even for unbounded strong B3 sets in the integers.

### Theorem 2

For every odd integer `r>=5`, put `B=7`, `L=3r`, `Z=L B^r`, and, with subscripts taken modulo r, define

    y_i=L B^i,
    x_i=Z+i-y_(i-1)-y_i                 (0<=i<r),
    A_r={x_i,y_i : 0<=i<r}.                             (10)

Then A_r is a strong B3 set of cardinality `n=2r`, contained in `[1,Z]`. Also

    1 notin A_r-A_r,
    mu(1) >= 4(r-1)=2n-4.                              (11)

There is no fixed cubic excess: indeed `n^3/Z = (8/3)r^2/7^r -> 0`.

### Proof of strong B3

Suppose two multiset triples have the same sum. Let u_i be the difference of their multiplicities at x_i, and v_i the difference at y_i. Then

    sum_i (|u_i|+|v_i|) <= 6.

Expansion in the scaled base B gives

    L[U B^r + sum_i (v_i-u_i-u_(i+1)) B^i] + C = 0,
    U=sum_i u_i,       C=sum_i i u_i.                    (12)

We have `|C|<=3(r-1)<L` and `|v_i-u_i-u_(i+1)|<=6<B`. Reduce (12) modulo L to get C=0 and divide by L. Successively reducing modulo B and dividing by B then proves

    C=0,       v_i=u_i+u_(i+1),       U=0.              (13)

Define integer potentials t_i on the cyclic indices by `t_0=0` and

    u_i=t_i-t_(i+1).

This is consistent because U=0. Equations (13) give

    v_i=t_i-t_(i+2),       sum_i t_i=C=0.                (14)

Consider the undirected graph on these r indices consisting of the step-one and step-two cycles. Because r is odd and at least five, these are edge-disjoint Hamilton cycles. Every nonempty proper vertex subset has at least two boundary edges in each cycle, hence at least four in their union.

If the potentials are nonconstant, their zero sum and integrality imply `min t<=-1` and `max t>=1`. The discrete level-set identity now gives

    sum_i (|u_i|+|v_i|)
      = sum_edges |t_a-t_b|
      = sum_(k=min t)^(max t-1) |boundary {i:t_i>k}|
      >= 4(max t-min t) >= 8,

contradicting the bound six. Thus all potentials, and hence all u_i,v_i, vanish. The triples were identical as multisets. This proves the repeated-summand B3 property.

It also proves that all the displayed x_i,y_i are distinct: an equality between two differently labeled elements can be padded to an equality of triples of labels, to which the same proof applies. Positivity and the upper bound Z follow directly from `B>=4` and `L>r`.

### Proof of the common-neighbor count

For every `1<=i<r`, direct cancellation gives

    x_i+y_i-x_(i-1)-y_(i-2)=1.                           (15)

The four elements in each equation are distinct. If 1 were a difference a-b from A_r, (15) would give the triple equality

    x_i+y_i+b=x_(i-1)+y_(i-2)+a.

The B3 property would equate these multisets, impossible since the disjoint pair `{x_i,y_i}` could not both be matched by the single extra element a. Thus 1 is outside D.

Each equation (15) gives four ordered representations of 1 as the sum of two members of D, using the two bijections between its positive and negative pairs and the two orders. All four are distinct. The representations from different i are also distinct: B3 implies B2, so every nonzero oriented difference identifies its ordered endpoint pair; the two differences would therefore recover the positive pair `{x_i,y_i}`, and hence i.

Since D is symmetric, the number of these ordered representations is `|D intersect (1+D)|`. This proves (11). QED.

### The pointwise factor two is asymptotically sharp

For every strong B3 set A of size n, the elementary pointwise estimate

    mu(x) <= 2n       for x outside (A-A)                 (16)

is valid. To see this, write x as `sum(P)-sum(Q)` for unordered multiset pairs P,Q. Their supports must be disjoint, since otherwise x would belong to A-A. The positive pairs belonging to different representations have disjoint supports: if P and P' share a, cancel a from the equation `sum(P)+sum(Q')=sum(P')+sum(Q)`. The resulting equality of triples, together with disjointness of P from Q and of P' from Q', forces the representations to be identical.

A representation using P,Q contributes `|supp(P)| |supp(Q)| <= 2|supp(P)|` ordered sums of two nonzero differences. The nonzero oriented differences have unique endpoint pairs by B2. Summing over the disjoint positive supports proves (16). Equation (11) attains `2n-O(1)` in unbounded integer B3 sets. Thus no smaller universal leading constant is possible in this pointwise statement.

### Interpretation

This family has many near-equal pair sums but no equal triple sums. The construction uses the cut bound of a graph consisting of two Hamilton cycles to prevent short additive relations. Its exponential diameter is essential to the proof as given. A useful global upper bound would have to incorporate density or averaged structure; the pointwise assertion above cannot be used without an additional hypothesis.

## 3. The Bose-Chowla lower bound remains valid with repetitions

For clarity, choose a generator theta of `F_(q^3)*`, put `M=q^3-1`, and define `b_t in [0,M-1]` by

    theta^b_t=theta-t,       t in F_q.

The q logarithms are distinct and none is zero. If two multiset triples of these logarithms have equal sums modulo M, then the corresponding products of three factors are equal. The difference of their monic cubic polynomials has degree at most two and vanishes at theta. Since theta has degree three over F_q, the difference is zero. Unique factorization, including root multiplicities, recovers the same parameter multiset.

Thus there is a q-element strong B3 integer set in `[1,q^3-2]`. This proves the lower constant one along prime-power scales. Taking a prime `q=(1-o(1))N^(1/3)` below `(N+1)^(1/3)` (using the standard fact that consecutive primes have ratio tending to one) gives `f(N)>=(1-o(1))N^(1/3)` for all large N. No claim is made that this supplies the missing upper bound.

## 4. Verification and remaining gap

`fresh_b3_mechanisms_audit.py` verifies (10) by direct enumeration of all multiset triples and checks the common-neighbor counts, independently of the graph proof.

`fresh_b3_pencils_audit.sage` verifies the exceptional-line calculation, the involution/pair counts, and the exact mixed-collision criterion over the specified finite fields, including a non-prime field. It also enumerates all parameter subsets for the smallest examples using separate triple-collision tests.

The scripts write JSON summaries. The completed audits checked:

* 245,916 repeated triples in eight sets (10 through 102 elements) from (10). The observed common-neighbor counts were exactly `2n-4` in each case; the theorem only needs the proved lower bound.
* The pointwise inequality (16) at 3,080 nontrivial values across all 314 strong B3 subsets of `{0,...,12}`.
* The pencils in both directions for `q=2,3,4,5,7,8,9,11,13,16,17,19`, including characteristics two and three and non-prime fields.
* Every beta with `1,alpha,beta` independent for `q=3,5,7`: respectively 18, 100, and 294 choices. Together the pencil tests checked 939,292 subset/involution inequalities.
* All 345,424 parameter subsets across `q=2,3,4,5,7,8,9`, separately in the cyclic and integer models. Direct triple collision masks agreed exactly with the algebraic exceptional-pencil criterion in the cyclic model. Returned integer maximizers were independently rechecked in Python. For example the cyclic/integer maxima for these specified bases at q=5 are 7/8, and at q=9 are 11/13, demonstrating why cyclic failure alone cannot be used to exclude an integer candidate.

These are finite audits of the stated identities and constructions, not extrapolated proofs of an asymptotic. Hash checks confirmed that `Spec.lean` and `Reductions.lean` were unchanged.

The unresolved gap remains exactly the original one: either prove a genuinely global estimate `|A|^3 <= (1+o(1))N` for arbitrary strong B3 sets in `[1,N]`, or construct an unbounded efficient integer family with `limsup |A|^3/N>1`. Theorem 1 only excludes a particular algebraic doubling mechanism. Theorem 2 invalidates one pointwise upper-bound route and has cubic ratio tending to zero. Neither settles the conjecture.
