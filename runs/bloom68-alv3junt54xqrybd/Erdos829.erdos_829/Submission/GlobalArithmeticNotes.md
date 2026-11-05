# Global arithmetic investigation for Erdős 829

## Status and scope

This does **not** prove or disprove the existential polylogarithmic statement in
`Submission/Spec.lean`. No conjecture declaration is used below, and the spec is
unchanged. The strongest quantitative conclusion obtained here is

\[
r(n)\leq\exp\!\left((0.4695030883+o(1))\frac{\log n}{\log\log n}\right).
\]

This is an improvement over the maximal-order constant `log 2` from the divisor
bound, not a polylogarithmic bound. It is derived below without a uniformity
assumption on prime allocations. No claim of bibliographic novelty is made.

`GlobalProducts.lean` contains proved arithmetic and weighted-quadratic lemmas
used in the argument. The prime classification, finite-code double counting,
Stirling estimates, and the final counting theorem below are mathematical proofs
in these notes, **not yet complete Lean formalizations**. There are no unproved
declarations in the new Lean file.

Let `r_+(n)` count ordered positive integer pairs, and `r_prim(n)` the pairs with
`gcd(x,y)=1`. Let `u_prim(n)` count unordered primitive pairs. The spec counts
nonnegative roots; for positive `n` its count differs from `r_+(n)` by at most two.
All logarithms are natural.

## 1. Exact two- and three-representation identities

If `a^3+b^3=c^3+d^3=n`, set `D=ad-cb`. Then

\[
D\big((ad)^2+(ad)(cb)+(cb)^2\big)=n(d^3-b^3).                 \tag{1}
\]

This is just the difference-of-cubes identity after replacing the two cube sums.
For distinct positive points on the same fibre, `D != 0` and

\[
|D|^3<n^2.                                                \tag{2}
\]

Indeed `|ad-cb|` is at most either `ad` or `cb`, and each coordinate cube is
strictly below `n`. If both points are unordered representatives (`a<=b,c<=d`),
then `2a^3<=n,2c^3<=n`, giving the stronger bound

\[
2|D|^3<n^2.                                              \tag{3}
\]

For three positive representations `(a,b),(c,d),(e,f)` put `T=ace+bdf`. There is
an exact sum-of-squares identity

\[
6(n-T)=(a+c+e)((a-c)^2+(c-e)^2+(e-a)^2)
       +(b+d+f)((b-d)^2+(d-f)^2+(f-b)^2).                  \tag{4}
\]

Thus `0<T<=n`, with equality precisely when the three ordered representations
are identical. In particular

\[
n\mid T\quad\Longleftrightarrow\quad(a,b)=(c,d)=(e,f).     \tag{5}
\]

These claims are proved in Lean, including the equality case and the natural-
number divisibility equivalence. Notice that (4) genuinely couples different
representations; it is not just a divisor congruence test.

## 2. Exact prime-allocation separation

A primitive representation has both coordinates coprime to `n`: if a prime
shared a coordinate and `n`, it would divide the other coordinate too.
Consequently

\[
z=-x/y\pmod n\quad\text{satisfies}\quad z^3=1.
\]

For each prime power `p^e || n`:

* `p == 2 mod 3`: there is exactly one cube root of unity modulo `p^e`.
  For odd `p` this follows from the cyclic group of units; for `p=2` its order
  is a power of two. All representations therefore agree at this prime power.
* `p == 1 mod 3`: there are exactly three roots modulo `p^e`, with distinct
  reductions modulo `p`; the three simple roots lift uniquely.
* If `v_3(n)=1`, there is no primitive representation. If `v_3(n)=e>=2`, all
  roots are `1+3^(e-1) j` modulo `3^e`, `j in {0,1,2}`. All agree modulo
  `3^(e-1)`, and agreement of the label supplies one extra factor of `3`.
  The actual primitive points occupy only the two nonidentity labels here,
  but using three labels gives a valid upper bound. The root description
  also follows directly from `v_3(z^3-1)=v_3(z-1)+1` when `z==1 mod 3`.

Define

\[
A(n)=\prod_{p\equiv2\ (3)}p^{v_p(n)}\,
\begin{cases}3^{v_3(n)-1},&v_3(n)\ge2,\\1,&v_3(n)=0.\end{cases}
\]

(The case `v_3(n)=1` is empty.) Introduce one ternary coordinate of weight
`log(p^e)` for each split prime power `p^e`, and an extra coordinate of weight
`log 3` when `v_3(n)>=2`. Let these prime-power factors be `q_1,...,q_k`. Then

\[
\prod_iq_i=n/A(n),\qquad \sum_i\log q_i\leq\log n.
\]

For two points `P,Q`, the integer `D=x_P y_Q-x_Q y_P` is divisible by

\[
A(n)\prod_{i:z_i(P)=z_i(Q)}q_i.
\]

Use (2), and divide `n` by this agreement product. The resulting weighted
Hamming distance between allocation vectors satisfies

\[
d(P,Q):=\sum_{i:z_i(P)\ne z_i(Q)}\log q_i
                  >\tfrac13\log n.                     \tag{6}
\]

This gives an injection of primitive representations into a ternary weighted
code, with a quantitative separation condition that arbitrary balanced unitary
divisor families need not satisfy. In particular it is stronger than simply
counting their supports.

## 3. Weighted Elias packing: a sub-divisor estimate

Write `W=log n`, `w_i=log q_i`, so `sum w_i<=W`. Let `C` be a ternary code with
minimum weighted distance strictly greater than `W/3`.
For `0<rho<rho_0`, where

\[
\rho_0=(2-\sqrt2)/3=0.1952621459\ldots,
\]

let

\[
V_\rho=\sum_{J:\sum_{i\in J}w_i\le\rho W}2^{|J|},
\qquad K_\rho=\frac1{1-6\rho+(9/2)\rho^2}.
\]

Every weighted ball of radius `rho W` contains at most `K_rho` codewords.
Here is a proof that works even when the weights are very unbalanced.

Translate the centre to zero. For a set of `M` codewords in the ball, let `u_i`
be the fraction whose coordinate is nonzero, and split that fraction into the
two possible nonzero labels. The ordered-pair disagreement fraction at this
coordinate is at most

\[
2u_i-\tfrac32u_i^2.
\]

Indeed the sum of squares of the two nonzero frequencies is at least `u_i^2/2`.
Set `R=sum w_i u_i<=rho W`. Weighted Cauchy-Schwarz, with possible fixed mass
`W-sum w_i` added as a zero coordinate, gives

\[
\sum_iw_i u_i^2\ge R^2/W.
\]

The average ordered-pair distance is therefore at most

\[
2R-\tfrac32R^2/W\le W(2\rho-\tfrac32\rho^2),
\]

where the last quadratic is increasing for `R/W<=rho<2/3`. On the other hand
it is at least `(1-1/M)W/3`, by minimum distance. Rearranging proves `M<=K_rho`.
The coordinate inequality, weighted Cauchy-Schwarz, radius quadratic, and final
numerical rearrangement are all proved in `GlobalProducts.lean`.

Double-count codeword/ball-centre incidences in the entire ternary space:

\[
|C|V_\rho\le K_\rho 3^k.                                \tag{7}
\]

For an integer `0<=ell<rho k`, a uniformly random `ell`-subset has expected
weight at most `(ell/k)W`. Markov's inequality shows that at least a fraction
`1-ell/(rho k)` of these subsets have weight at most `rho W`. Thus the explicit
finite estimate is

\[
|C|\le\frac{K_\rho 3^k}
 {(1-\ell/(\rho k))\,2^\ell {k\choose\ell}}.             \tag{8}
\]

There is no assumed distribution or independence of the prime factors here.

Take `rho=rho_0-1/k` and `ell=floor(rho k)-1`, treating the bounded small `k`
separately. Then `K_rho=O(k)`, the Markov fraction is at least a constant times
`1/k`, and Stirling gives

\[
V_\rho\gg k^{-3/2}\exp(k(h(\rho_0)+\rho_0\log2)),
\quad h(t)=-t\log t-(1-t)\log(1-t).
\]

Consequently, with an absolute constant,

\[
r_{\rm prim}(n)\ll(k+1)^{5/2}b^k,\qquad
 b=3\exp(-h(\rho_0)-\rho_0\log2)
  =1.5991993348\ldots.                                  \tag{9}
\]

For comparison, plain disjoint balls of radius `W/6` give the weaker base
`(3125/128)^(1/6)=1.7032301726...`. The Elias averaging is what improves it to
`1.5992...`.

## 4. All representations, and the maximal-order constant

Removing the gcd is exact:

\[
r_+(n)=\sum_{d^3\mid n}r_{\rm prim}(n/d^3).              \tag{10}
\]

Let `k_1(n)` be the number of distinct split prime factors. The optional 3-label
in (9) can be absorbed in an absolute constant. Therefore

\[
r(n)\le2+C(k_1(n)+2)^{5/2}F(n),                         \tag{11}
\]

where `F` is multiplicative and, for `e>=1`,

\[
F(p^e)=
\begin{cases}
 b\lceil e/3\rceil+\mathbf1_{3\mid e},&p\equiv1\ (3),\\
 \lfloor e/3\rfloor+1,&p\not\equiv1\ (3).
\end{cases}                                             \tag{12}
\]

This simply sums `b^{k_1(n/d^3)}` over all possible gcds. The factor at `3`
overgenerously counts some empty primitive fibres, which is harmless.

For every `e>=1`, `F(p^e)<=b^e`, and also `F(p^e)<=C_0(e+1)` with absolute
`C_0`. To verify the first claim: `b>3/2`, hence `b^3>b+1` and `b^3>2`.
The split factors at `e=1,2,3` obey the claim, and replacing `e` by `e+3`
adds `b`, at most multiplying by `b^3`. The other factors add `1`, again at
most multiplying by `b^3`. The inequality `b>3/2` can be checked without
numerical approximations: `rho_0<1/5`, the entropy expression is increasing
below `2/3`, and
`exp(5(h(1/5)+(1/5)log2))=3125/128<2^5`.

Here is an elementary uniform maximal-order estimate, requiring no prime-
number theorem. Set `L=log n`, `lambda=log log n`, and
`P=L/lambda^3`. For primes `p<=P`, there are at most `P` possibilities and
`e<=L/log2`, so their total contribution to `log F(n)` is
`O(P log L)=O(L/lambda^2)`. For primes `p>P`, use `F(p^e)<=b^e` and
`sum e<=L/log P`. Thus

\[
\log F(n)\le (\log b+o(1))\frac{\log n}{\log\log n}.
\]

The polynomial factor in (11) has logarithm `O(log log n)`. Hence

\[
\boxed{r(n)\le\exp\!\left((0.4695030883+o(1))
                \frac{\log n}{\log\log n}\right).}       \tag{13}
\]

The `o(1)` here is uniform in `n`. This is still much larger than every fixed
power of `log n`, so it does not resolve Erdős 829.

## 5. A genuine logarithmic subcase: enough forced inert mass

For unordered primitive points, combine (3) with primewise collision counts.
If there are `m` points, then at each ternary coordinate the number of pairs
with equal labels is at least

\[
\sum_{j=0}^2{m_j\choose2}\ge m(m-3)/6.
\]

All pairs share the factor `A(n)`. Therefore, for the product of their nonzero
cross determinants,

\[
{m\choose2}(\tfrac23\log n-\tfrac13\log2)
 \ge {m\choose2}\log A(n)
       +\frac{m(m-3)}6\log(n/A(n)).
\]

Rearrangement gives the exact inequality

\[
\boxed{m\log(2A(n)^2/n)\le\log(2n).}                    \tag{14}
\]

Whenever `2A(n)^2>n`, this is a nontrivial upper bound. In particular

\[
 A(n)\ge\sqrt n\quad\Longrightarrow\quad
 u_{\rm prim}(n)\le\log(2n)/\log2.
\]

If `A(n)>=n^(1/2+epsilon)`, it gives a bounded number, asymptotically at most
`1/(2epsilon)`. This is a primitive subcase, not a uniform assertion about the
sum over all gcd fibres in (10). The difficult family with mostly split primes
has `A(n)=1`, so (14) is vacuous there.

## 6. The global three-product gives a cap set, but not a polynomial-size code

Equation (5) has the following precise group-theoretic consequence. The labels
`z_i=-x_i/y_i mod n` form a cap set in the group of cube roots of unity:

\[
z_i z_j z_k=1\quad\Longleftrightarrow\quad i=j=k.
\]

The group is a ternary vector space on the variable coordinates above. The
ordered representation set is centrally symmetric (`z` and `z^(-1)` correspond
to swapping roots). This cap condition is in addition to (6), and uses the exact
common cube sum, not just independent local conditions.

Nevertheless, these extracted conditions still admit exponentially many
allocation patterns. This can be proved, rather than merely suggested.
Consider the equal-weight ternary allocation model, with `k` divisible by six.
Greedily choose a family `F` of `k/3`-subsets `Z` of `{1,...,k}` with
`|Z intersect Z'|<k/6` for distinct members. A fixed `Z` excludes at most

\[
B_k=\sum_{j=0}^{k/6}{k/3\choose j}{2k/3\choose j}
\]

other candidates. Hence

\[
|F|\ge{k\choose k/3}/B_k
 =\exp\left((c+o(1))k\right),\quad
c=h(1/3)-\tfrac13\log2-\tfrac23h(1/4)
 =\tfrac16\log(19683/16384)
 =0.0305750117\ldots>0.
\]

For each `Z`, let `v_Z` be zero on `Z` and one elsewhere, and use the code
`S={v_Z,-v_Z : Z in F}`.

* Each zero pattern occurs precisely in its global inversion pair.
* Every word has `k/3` zeros, the cube-root divisor weight in this model.
* Same-sign distances are `2(k/3-|Z intersect Z'|)>k/3`.
* Opposite-sign distances are `k-|Z intersect Z'|>=2k/3`.
* A same-sign zero-sum triple in the binary cube must consist of three equal
  words. A mixed-sign zero-sum triple would require the supports of two
  positive words to be disjoint; both supports have size `2k/3`, so that is
  impossible. Thus `S` is also a centrally symmetric cap set.

If a **strict** positive-root window is desired rather than its closed boundary,
give the main coordinates a common weight `w>=log7` and append two coordinates:
a fixed zero of weight `log7`, and a label of weight `log13` that is `1` on
positive words and `2` on their inverses. Total weight is `W=kw+log91`, and
the zero-coordinate weight is `L=(k/3)w+log7`. Hence
`3L-W=log(49/13)` lies strictly between zero and `log4`, as required by
`n<s^3<4n`. Same-sign distances had an integer gap of at least `2w` above
`kw/3`, so remain greater than `W/3`; opposite-sign distances are even larger.
The cap and support-uniqueness properties also survive. This eliminates the
possible objection that the unaugmented model only meets the lower window
boundary. Equal main weights still describe an abstract allocation model, not
literal distinct prime factors with equal logarithms.

This is **not** a construction of integer representations or a counterexample
to the conjecture. It is an obstruction to proving polynomial-in-`k` cardinality
from weighted allocation separation, cube-root window weights, support
uniqueness, and the three-product cap condition alone. The exact global square
condition is additional arithmetic not realized by this model.

## 7. What adaptive small good primes do and do not supply

There is a quantitative barrier for the scalar larger sieve using the full
local square-allowed residue sets. Work already in the hard squarefree case
`gcd(n,6)=1`, and let `S` be the exact constrained divisors, `R=|S|>=2`.
Every `s` lies in `[n^(1/3),(4n)^(1/3)]`.

At a prime `q not dividing 6n`, the allowed nonzero residues satisfy

\[
(4n/a-a^2)/3\text{ is a square modulo }q.
\]

Let their number be `nu_q(n)`. Multiplying the square argument by `a^2`
turns its character into that of `(4na-a^4)/3`. This is a separable quartic
with a nonsingular genus-one double cover (and rational point `(0,0)`). Hasse's
bound, and the at most three nonzero roots of `a^3=4n`, yield

\[
|\nu_q(n)-q/2|\le\sqrt q+3/2.                           \tag{15}
\]

This estimate is uniform in the residue of `n`. If any good prime has
`nu_q(n)=0`, the constrained-divisor set is empty. Under the standing assumption
`R>=2`, therefore, all these allowed-set counts are positive.

Bad-prime collisions do provide extra saving. Write `a_p=|{s in S:p|s}|`,
`W=log n`, and `L=sum_{s in S}log s>=RW/3`. Weighted Cauchy-Schwarz gives

\[
\sum_{p\mid n}\log p{a_p\choose2}
 \ge\tfrac12(L^2/W-L)
 \ge(R^2/18-R/6)W.                                     \tag{16}
\]

For a set `P` of good primes put
`A_P=sum_{q in P}log q/nu_q(n)` and `T_P=sum_{q in P}log q`.
The good-prime collision contribution is at least
`R^2 A_P/2-R T_P/2`. Compare both contributions with the Vandermonde upper
bound using interval diameter `c_0 n^(1/3)`, where `c_0=4^(1/3)-1<1`.
If the denominator is positive, this proves

\[
\boxed{R\le
 \frac{T_P-\log c_0}{A_P-(2/9)\log n-\log c_0}.}         \tag{17}
\]

By (15) and the standard elementary Mertens estimate,

\[
\sum_{q\le Q,\ q\nmid6n}\frac{\log q}{\nu_q(n)}
 \le2\log Q+O(1).
\]

Thus even an `n`-dependent choice of a subset of good primes below
`Q=(log n)^B` cannot make the denominator of (17) positive for large `n`.
The crude threshold is `Q>n^(1/9+o(1))`, still a power of `n` rather than a
polylogarithm.

This is a limitation of **this precise larger-sieve majorant**. It does not
rule out proving that the *actually occupied* divisor residues are much fewer
than the full allowed sets, or a genuinely coupled global sieve. Such a result
would be new arithmetic input, not a consequence of (15).

## 8. Formal verification and remaining gap

The new module proves: the pair resultant; exact triple deficit; triple upper
bound and equality characterization; `dvd_triple_product_iff`; primitive
coordinate coprimality; determinant injectivity and both height bounds; ternary
coordinate disagreement; weighted Cauchy-Schwarz; the radius quadratic; and
the numerical Elias rearrangement.

The allocation-code theorem (8), its asymptotic consequence (13), and the
sieve/coding limitations are supplied above as complete ordinary proofs, not
asserted as unproved Lean theorems. Completing a Lean formalization of (13)
would improve the existing divisor bound but would **not** close the requested
polylogarithmic goal. The remaining issue for these mechanisms is to prove that
only polylogarithmically many of the exponentially many **combinatorially
admissible** allocation patterns can satisfy the global square equation in the
mostly-split-prime case. No exponential family satisfying that global equation
has been constructed. The abstract models show why the extracted separation
and cap conditions cannot by themselves supply the needed estimate.
