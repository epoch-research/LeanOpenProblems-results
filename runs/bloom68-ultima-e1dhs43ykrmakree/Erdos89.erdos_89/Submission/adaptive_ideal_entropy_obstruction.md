# Adaptive ideal branching: a valid extension and an actual-set entropy obstruction

## Status and scope

Put

\[
 D(P)=|\{N(x-y):x,y\in P,\ x\ne y\}|,\qquad
 K(P)=|P|/D(P),\qquad \Phi_0(P)=K(P)^2
\]

for a finite Gaussian-integer set with at least two points. For n=|P|>=4
(or above a fixed threshold), the requested statement is

\[
 \Phi_0(P)-\max_{Q\subset P,\ 2\le |Q|\le |P|/2}\Phi_0(Q)\le C. \tag{C0}
\]

**This investigation does not prove or disprove (C0). In particular, it does
not supply a counterexample to the original unrestricted ideal-plus-convex
selector problem.** It establishes the following precise obstructions and
valid extensions instead:

1. The split-prime parity lemma extends to an arbitrary *valuation alphabet*.
   There is an adaptive cover by at most
   \(q^{|V\cap[0,k-1]|}\) ideal cosets of norm \(q^k\). Consequently
   \(|A|\le q^{|V|}\), without a height hypothesis. This is sharp for every
   valuation alphabet whose consecutive entries differ by at least two,
   with genuinely correlated Gaussian-integer realizations.
2. **Every positive-order Renyi-entropy replacement of norm-support size
   makes a logarithmic squared-ratio budget false on actual square grids.**
   For random distinct endpoints in an \(L\)-by-\(L\) grid, \(n=L^2\),
   \[
   H_\alpha(N(X-Y))=\log n-c_\alpha\log\log n+O_\alpha(1),
   \]
   where
   \[
   c_\alpha=\frac{2^{\alpha-1}-1}{\alpha-1}\quad(\alpha\ne1),
   \qquad c_1=\log2.
   \]
   Here \(c_0=1/2\), but **\(c_\alpha>1/2\) for every fixed \(\alpha>0\)**.
   Thus the corresponding squared entropy ratio is superlogarithmic.
   No universal constant-loss contraction for any of these positive-order
   surrogates is possible, even with *all* subsets available as selectors.
3. Simply making the norm labels uniform does not fix this for free. On the
   same genuine grids, every joint endpoint law with uniform norm label
   must lose an unbounded amount of product-point entropy:
   \[
   (\log n-H(X))+(\log n-H(Y))+I(X;Y)
   \ge (3/2-\sqrt2)\log\log n-O(1). \tag{U}
   \]
   More generally, any constant strictly smaller than
   \((1-\log2)/2\) can replace \(3/2-\sqrt2\).

These are not fake autocorrelations or abstract edge-colorings. The entropy
obstruction uses the exact autocorrelation of a square grid. It rules out a
specified entropy shortcut, not every possible support-sensitive inverse
sieve. The unbounded Hartley-to-Shannon gap has to be retained, rather than
silently discarded. No Lean files were changed.

## 1. Arbitrary valuation alphabets: the correct branching generalization

Let \(E/F\) be quadratic, and let
\(\mathfrak p\mathcal O_E=\mathfrak P\overline{\mathfrak P}\) split, with
\(N_F(\mathfrak p)=q\). Let \(A\subset\mathcal O_E\) be finite. Suppose

\[
 v_{\mathfrak p}(N_{E/F}(x-y))\in V\subset\mathbb Z_{\ge0}
 \quad(x\ne y\in A), \tag{1}
\]

where \(V\) is finite. No product or independence assumption is made on A.

### Theorem 1

For every integer \(k\ge0\), A is covered by at most

\[
 \boxed{q^{|V\cap\{0,\ldots,k-1\}|}}
 \tag{2}
\]

cosets of ideals \(\mathfrak P^a\overline{\mathfrak P}^{\,b}\) with
\(a+b=k\). The choice of a,b and the next direction can depend on the node.
In particular,

\[
 \boxed{|A|\le q^{|V|}.} \tag{3}
\]

### Proof

At depth k a node lies in \(c+I\), where
\(I=\mathfrak P^a\overline{\mathfrak P}^{\,b}\), \(a+b=k\).

* If \(k\in V\), partition that node modulo \(I\mathfrak P\). This gives
  at most q children of ideal norm \(q^{k+1}\).
* If \(k\notin V\), encode the node in
  \[
  I/(I\mathfrak P)\times I/(I\overline{\mathfrak P})
  \cong\mathbb F_q^2.
  \]
  Two distinct residue points differing in both coordinates would give a
  difference with valuations exactly a,b, hence norm valuation k. This is
  forbidden. A set of points in a product for which every pair shares a
  coordinate is contained in one row or one column. Therefore the entire
  node is in a *single* coset of \(I\mathfrak P\) or of
  \(I\overline{\mathfrak P}\).

For the row-or-column assertion, two points in different rows have the same
column; any point in another column would have to share both different rows.
This is impossible. Repeated residue points cause no problem.

Thus only levels in V can increase the number of nodes, and each increases
it by at most q. This proves (2). If V is empty then |A|<=1 already.
Otherwise, once k exceeds max V, every node is a singleton: two points in
it would have norm valuation at least k. This proves (3). The proof does
not require the ideals to be principal. QED.

### Recovering parity and the height bound

If all allowed valuations are even, (2) at depth 2j gives at most \(q^j\)
cosets of ideals of norm \(q^{2j}\), exactly the proposed adaptive lemma.
For

\[
 H=\max_{x\ne y}|N_{E/\mathbb Q}(x-y)|,
\]

choose the least j with \(q^{2j}>H\). Every such coset contains at most one
point, since a nonzero difference in its ideal has absolute norm divisible
by \(q^{2j}\). Hence \(|A|\le q^j\le q\sqrt H\).

For a general V, the valid height form is

\[
 |A|\le q^{|V\cap[0,\lfloor\log_q H\rfloor]|}. \tag{4}
\]

This depends on which valuations are absent, not merely on the number of
positive norm values.

### Sharp correlated examples

In \(\mathbb Z[i]\), fix a split prime \(p=\pi\bar\pi\), and let

\[
 V=\{v_0<\cdots<v_{t-1}\},\qquad v_{j+1}-v_j\ge2.
\]

Put \(a_j=j\), \(b_j=v_j-j\); both sequences strictly increase. For a word
\(d=(d_0,\ldots,d_{t-1})\in\mathbb F_p^t\), prescribe the local digits

\[
 z_d\equiv\sum_j[d_j]\pi^{a_j}\pmod{\pi^t},\qquad
 z_d\equiv\sum_j[\sigma_{j,d_{<j}}(d_j)]\bar\pi^{b_j}
              \pmod{\bar\pi^{b_{t-1}+1}}. \tag{5}
\]

Here each \(\sigma_{j,d_{<j}}\) is an arbitrary permutation of \(\mathbb F_p\),
and brackets denote digit representatives. CRT gives actual Gaussian integers
satisfying (5). If two words first differ at position j, their two local
valuations are exactly a_j,b_j; their norm valuation is v_j. Consequently
these \(p^t\) distinct actual points attain equality in (3). Prefix-dependent
permutations make clear that no independence of the two local coordinates
is available or needed.

### Why this does not convert low D into parity

Let \(G_L=\{0,\ldots,L-1\}+i\{0,\ldots,L-1\}\). Then

\[
 D(G_L)\asymp L^2/\sqrt{\log L}=o(|G_L|). \tag{6}
\]

For every fixed split p, its norm-valuation alphabet nevertheless contains
all integers

\[
 0\le k\le\lfloor\log_p((L-1)^2)\rfloor:
\]

the vector \(\pi^k\) lies in \(G_L-G_L\). Thus it has no missing valuation
levels throughout a range of length \(\log_p n-O(1)\). In particular,
odd valuations are present. All fixed finite residue quotients of the points
are full once L is large enough. The same is true inside a fixed ideal
fiber in a fixed macroscopic interior window after normalization.

This is an actual low-D obstruction to inferring a parity-like local
restriction from global support cardinality. It is **not** a contraction
counterexample: grids have useful smaller geometric windows and ideal fibers.

## 2. What a height-free adaptive budget does and does not say

For any adaptive partition tree with singleton leaves, let m_v be the number
of points at node v, and \(p_{w|v}=m_w/m_v\) for its children. Uniformly
sampling a point gives the exact chain rule

\[
 \boxed{\sum_{v\ {
m internal}}\frac{m_v}{n}
 H((p_{w|v})_w)=\log n.} \tag{7}
\]

This remains true for partitions made by geometric windows. Unary ideal
rescalings have zero entropy cost. Equation (7) is a genuine height-free
budget, but does not yet charge any change in D or K to that budget.

The logarithm of the ideal norm is **not** this entropy cost. For example,

\[
 P_h=\{0,1,2^h,2^h+1\}\subset\mathbb Z[i]
\]

is Gaussian-primitive. Modulo \(1+i\) it splits into the two pairs
\(\{0,2^h\}\), \(\{1,2^h+1\}\). Inside either pair there are arbitrarily
many unary refinements before the two points separate, because
\(v_{1+i}(2^h)=2h\). The point entropy stays \(\log4\), while the accumulated
log ideal norm is arbitrarily large. This example has bounded K; it rules
out a height-to-entropy substitution without an additional low-D argument,
not the original contraction.

For n>=4 there is no cardinality obstacle to balanced ideal selection:
following the larger child of the binary \((1+i)\)-adic partition until first
reaching size at most n/2 gives an actual ideal fiber Q with

\[
 n/4<|Q|\le n/2. \tag{8}
\]

Its index can be arbitrarily large. The missing assertion is a bound on its
*actual normalized norm support*, not its size or existence.

For clarity, a single surviving branch of arbitrary ideal-coset selections,
Gaussian similarities used for normalization, and convex-window cuts has
exactly the form

\[
 Q=P\cap(a+I)\cap C, \tag{9}
\]

where I is a Gaussian ideal (possibly the unit ideal), and C is convex.
Indeed, the preimage of a convex set under a similarity is convex, and a
subsequent ideal fiber replaces I by its product with another ideal.
Intersections remain convex. Conversely (9) is obtained with one ideal
selection and one convex cut. This convention concerns one retained branch,
not arbitrary unions of branches.

## 3. Actual-grid obstruction to positive-order norm entropy

For a set P of size n, let (X,Y) be a uniformly chosen ordered *distinct*
pair. Define

\[
 r_d=|\{(x,y)\in P^2:x\ne y,\ N(x-y)=d\}|,\quad
 M=n(n-1),\quad \mu(d)=r_d/M.
\]

Write \(H_0(\mu)=\log D(P)\), \(H_1(\mu)=-\sum_d\mu(d)\log\mu(d)\), and

\[
 H_\alpha(\mu)=\frac{1}{1-\alpha}\log\sum_d\mu(d)^\alpha
 \quad(\alpha>0,\ \alpha\ne1).
\]

All logarithms in this note are natural, except explicitly written \(\log_2\).

### Theorem 2

For \(P=G_L\), \(n=L^2\), and every fixed finite \(\alpha\ge0\),

\[
 \boxed{H_\alpha(\mu)=\log n-c_\alpha\log\log n+O_\alpha(1),} \tag{10}
\]

where

\[
 c_\alpha=\frac{2^{\alpha-1}-1}{\alpha-1}\quad(\alpha\ne1),
 \qquad c_1=\log2. \tag{11}
\]

In particular,

\[
 H_0(\mu)-H_1(\mu)
   =(\log2-1/2)\log\log n+O(1)\longrightarrow\infty. \tag{12}
\]

### Proof for alpha not equal to 1

Put \(R(d)=r_2(d)/4\), where \(r_2(d)\) counts all Gaussian integers of norm d.
The standard multiplicative-function moment estimate is

\[
 \sum_{1\le d\le T}R(d)^\alpha
 \asymp_\alpha T(\log T)^{2^{\alpha-1}-1}. \tag{13}
\]

At alpha=0, interpret the summand as \(\mathbf1_{R(d)>0}\).
Here is a check of the analytic input. The prime-power factors are

\[
 R(2^j)=1,\quad R(p^j)=j+1\ (p\equiv1\pmod4),\quad
 R(p^j)=\mathbf1_{2\mid j}\ (p\equiv3\pmod4).
\]

For \(f=R^\alpha\), the prime mean parameter in Wirsing's theorem is
\(\kappa=2^{\alpha-1}>0\). The sum of the prime-power terms with exponent
at least two, weighted by \(p^{-j}\), converges. The supplementary prime-power
sum hypothesis for \(\kappa\le1\) also holds: the j=1 terms are O(T/log T)
and the j>=2 terms are \(O_\alpha(\sqrt T(\log T)^{\alpha+2})\).
The Euler product is \(\asymp_\alpha(\log T)^\kappa\), by Mertens' theorem
in the two reduced classes modulo 4. Wirsing gives (13). Thus these exponents
are not obtained by an invalid interpolation of the first two moments.

The grid has the exact, genuine translation multiplicities

\[
 a(u+iv)=(L-|u|)(L-|v|)\quad(|u|,|v|<L).
\]

Therefore

\[
 r_d\le n r_2(d),\qquad r_d=0\quad(d>2n),\qquad
 r_d\ge(n/4)r_2(d)\quad(1\le d\le n/4). \tag{14}
\]

Applying (13) to the inner and outer ranges in (14), for alpha>0,

\[
 \sum_d\mu(d)^\alpha
 \asymp_\alpha n^{1-\alpha}(\log n)^{2^{\alpha-1}-1}. \tag{15}
\]

The definition of Renyi entropy proves (10) for alpha not equal to 1.
The same inner/outer argument at alpha=0 proves the asserted Hartley value.

### Shannon case, without differentiating an uncontrolled error term

Let \(Z=X-Y\). Its nonzero point probabilities are at most \(1/(n-1)\), and
its support has fewer than 4n elements. Hence

\[
 H(Z)=\log n+O(1). \tag{16}
\]

We claim

\[
 \mathbb E\log r_2(NZ)=(\log2)\log\log n+O(1). \tag{17}
\]

For a Gaussian ideal J of norm m, the number of nonzero elements of J of
length at most \(\sqrt{2n}\) is O(n/m), or zero if m>2n. Since each possible
Z has probability O(1/n),

\[
 \Pr(Z\in J)\ll1/m. \tag{18}
\]

For a split prime \(p=\pi\bar\pi\), the condition \(p^j\mid NZ\) is covered
by the j+1 ideals \((\pi^a\bar\pi^{j-a})\). Consequently

\[
 \Pr(v_p(NZ)\ge j)\ll(j+1)/p^j. \tag{19}
\]

The sum of (19) over p and j>=2 converges. Thus all contributions from
higher valuations to
\(\log R(NZ)-\log2\sum_{p\equiv1(4)}\mathbf1_{p\mid NZ}\)
have bounded expectation. Primes exceeding \(L^{1/4}\) also make a bounded
contribution: their total multiplicity in an integer at most 2n is bounded.

For \(p\le L^{1/4}\), direct counting of the grid in residues modulo pi and
bar-pi, and inclusion-exclusion, gives

\[
 \Pr(p\mid NZ)=2/p-1/p^2+O(p/n). \tag{20}
\]

For example, each residue modulo pi has \(n/p+O(L)\) points, so its collision
probability is \(1/p+O(p/n)\); the intersection is congruence modulo the
rational ideal (p), with probability \(1/p^2+O(p/n)\). Conditioning away
X=Y changes this by only O(1/n). The errors in (20) are summable up to
\(L^{1/4}\). Mertens in the class 1 modulo 4 now proves (17).

To pass from representation capacity to *actual conditional entropy*, let
U be uniform on all nonzero Gaussian integers of norm at most
\(2(L-1)^2\). The point likelihood ratio \(\Pr(Z=z)/U(z)\) is bounded above
by an absolute constant. Therefore \(D_{KL}(Z\|U)=O(1)\). The chain rule for
relative entropy, after applying N, gives

\[
 \mathbb E_d D_{KL}\bigl(Z\mid NZ=d\ \|\ {\rm Unif}\{z:Nz=d\}\bigr)=O(1).
\]

Consequently

\[
 H(Z\mid NZ)=\mathbb E\log r_2(NZ)+O(1).
\]

Combining this with (16) and (17) proves the Shannon instance of (10).
This step uses the actual endpoint autocorrelation; it does not pretend that
orientations are exactly uniform on every grid circle. QED.

## 4. No positive-order entropy contraction, even with unrestricted selectors

Define the surrogate

\[
 \Phi_\alpha(P)=\exp\bigl(2[\log|P|-H_\alpha(\mu_P)]\bigr).
\]

Only \(\Phi_0\) is the potential in the question. Theorem 2 says

\[
 \Phi_\alpha(G_L)\asymp_\alpha(\log n)^{2c_\alpha}. \tag{21}
\]

The function \(c_\alpha\) is strictly increasing: it is the secant slope of
the strictly convex function \(2^x\), with one endpoint fixed at x=0.
Since \(c_0=1/2\), for every fixed alpha>0,

\[
 \boxed{\Phi_\alpha(G_L)/\log n\longrightarrow\infty.} \tag{22}
\]

Suppose an absolute constant-loss contraction for \(\Phi_\alpha\) held for
all sufficiently large Gaussian-integer sets, with any subset of size between
2 and half available. Iterating it gives

\[
 \Phi_\alpha(P)\le C\log_2|P|+O(1),
\]

because small sets have \(\Phi_\alpha(P)\le |P|^2\). This contradicts (22).
The endpoint alpha=infinity fails as well, since \(H_\infty\le H_2\), so
\(\Phi_\infty(G_L)\ge\Phi_2(G_L)\gg(\log n)^2\).
Allowing geometric windows, any ideals, rescaling, or all subsets cannot
repair this contradiction.

There is also a finite actual-set construction of arbitrarily large
**surrogate** defects. Fix B>0 and a cardinality threshold N0. Choose a grid
G so large that

\[
 \Phi_\alpha(G)-2B\log_2|G|>N_0^2.
\]

Among its subsets of size at least two choose F maximizing
\(\Phi_\alpha(F)-2B\log_2|F|\), with a fixed lexicographic tie-break. Then
\(|F|>N_0\), and for every \(Q\subset F\) of size between 2 and |F|/2,

\[
 \Phi_\alpha(F)-\Phi_\alpha(Q)
 \ge2B\log_2(|F|/|Q|)\ge2B. \tag{23}
\]

Thus these are actual Gaussian-integer counterexamples for the positive-order
entropy surrogate, including unrestricted ideal-plus-convex selectors.
**Equation (23) is not claimed for \(\Phi_0\).** Nor is the maximizing F
claimed to have low D; it is a counterexample to the proposed entropy
replacement, not to the original Hartley-support problem.

## 5. Uniformizing norm labels has an unavoidable endpoint-entropy cost

The preceding obstruction cannot be evaded by saying that one may simply
make the D labels uniform while retaining independent, high-entropy endpoints.
There is an exact cost identity for this change of measure.

For any finite P, let U be uniform on its M ordered distinct pairs, with
norm pushforward mu. Let nu be any other law on these pairs for which the
norm label T is uniform on the same support S. Relative-entropy chain rule
implies

\[
 D_{KL}(\nu\|U)\ge D_{KL}({\rm Unif}(S)\|\mu).
\]

Equivalently,

\[
 \boxed{
 (\log n-H_\nu(X))+(\log n-H_\nu(Y))+I_\nu(X;Y)
 \ge \log\frac{n}{n-1}
       +D_{KL}({\rm Unif}(S)\|\mu).} \tag{24}
\]

Equality holds when nu is uniform within each norm class. Indeed the left
side equals \(2\log n-H_\nu(X,Y)\), and
\(D_{KL}(\nu\|U)=\log M-H_\nu(X,Y)\). In particular the minimum cost is
exactly the right side, with

\[
 D_{KL}({\rm Unif}(S)\|\mu)
 =\log M-\log D-\frac1D\sum_{d\in S}\log r_d. \tag{25}
\]

This reverse relative entropy is also exactly the derivative at the Hartley
endpoint: direct differentiation of the finite sum defining Renyi entropy gives
\(\left.\frac{d}{d\alpha}H_\alpha(\mu)\right|_{\alpha=0}
=-D_{KL}({\rm Unif}(S)\|\mu)\).
Thus the cost in (24) is the first-order obstruction to treating a positive
entropy order as a bounded-cost regularization of support size.

### Lower bound for the actual grid

For \(G_L\), (14), Jensen, and (13) give, for every fixed t>0,

\[
 \begin{aligned}
 \frac1D\sum_{d\in S}\log r_d
 &\le\log(4n)+\frac1t
     \log\left(\frac1D\sum_{d\in S}R(d)^t\right)\\
 &\le\log n+
     \frac{2^{t-1}-1/2}{t}\log\log n+O_t(1).
 \end{aligned} \tag{26}
\]

Using \(\log D=\log n-\tfrac12\log\log n+O(1)\) in (25),

\[
 D_{KL}({\rm Unif}(S)\|\mu)
 \ge\left(\frac12-\frac{2^{t-1}-1/2}{t}\right)\log\log n-O_t(1). \tag{27}
\]

Take t=1/2 to obtain the positive coefficient \(3/2-\sqrt2\), proving (U).
Letting t be a sufficiently small fixed positive number gives any coefficient
strictly below \((1-\log2)/2\).

Thus a law with uniform colors must have an unbounded marginal-entropy loss,
unbounded endpoint mutual information, or a combination of the two. In
particular, there is no O(1)-cost passage from independent uniform endpoints
to uniform norm-support measure. The usual off-diagonal conditioning costs
only \(\log(n/(n-1))\); that is not the obstruction.

## 6. The specific Hartley gap still needing a theorem

The valid point-tree budget (7) and the valuation cover (2) do not couple
that budget to the empirical cardinalities of actual normalized norm supports.
The positive-order entropy surrogate would need an inequality which is false
by (22). Its correction is not a bounded constant:

\[
 \Phi_0(P)=\Phi_\alpha(P)
 \exp\{-2[H_0(\mu_P)-H_\alpha(\mu_P)]\}. \tag{28}
\]

On grids the bracket is
\((c_\alpha-1/2)\log\log n+O_\alpha(1)\), so it changes the logarithmic
*power*, not just a constant. Uniformizing the labels introduces the real
endpoint cost (24) instead.

For a proposed balanced child Q, write \(\theta=|Q|/|P|\in(1/4,1/2]\),
and assume \(K(P)^2>C\). The exact support loss needed for the original
contraction is

\[
 \boxed{
 \log D(P)-\log D(Q)
 \ge \log(1/\theta)+\tfrac12\log(1-C/K(P)^2).} \tag{29}
\]

Thus the Hartley norm-support drop must match the point-entropy drop to
accuracy \(O(1/K(P)^2)\), not merely within O(1). Equations (2), (7), or
representation capacities do not supply (29). Nor may \(H_\alpha\) replace
\(H_0\) in it at bounded cost.

What remains unresolved is either:

* an actual-fiber/window theorem establishing the required Hartley-support
  extraction (with the support/entropy correction retained), or
* a Gaussian-integer family whose defect for \(\Phi_0\), for all selectors
  (9) or for all subsets, tends to infinity.

No such family for \(\Phi_0\) is asserted here. This investigation supplies a
precise actual-set obstruction to positive-order entropy substitution, not an
impossibility theorem for all adaptive inverse sieves.

## Verification and analytic references

`verify_adaptive_ideal_entropy_obstruction.py` checks exact Gaussian arithmetic,
the arbitrary-alphabet adaptive cover on actual sets, sharp correlated CRT
examples, the genuine grid radial multiplicities, the relative-entropy chain
identities, and finite entropy values. Floating-point logarithms are used only
for entropy checks. The asymptotic statements are proved above, not inferred
from the numerical table.

The analytic input (13) was checked against the statement of Wirsing's theorem
in `/corpus/src/1306.0537/` (Proposition `prop:wirsing`), with all its extra
hypotheses for kappa<=1 verified above. The square-grid support and energy
normalizations agree with `/corpus/src/1306.0242/lattices.tex`. Standard
inverse-sieve results such as Walsh, `/corpus/src/1105.1551/`, use a height
parameter and hypotheses about local occupancies; they do not by themselves
supply (29) from low global D. No claim of historical priority is made for
the standard moment theorem or entropy chain rule.
