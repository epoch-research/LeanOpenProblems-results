# Lattice distance energy: exact arithmetic reductions and a relaxation obstruction

## Status and scope

The proposed inequality

\[
 E(P)D(P)^2\ge c|P|^5
 \tag{T}
\]

is **not proved or disproved here for finite lattice point sets**. We assume
\(n=|P|\ge2\): with positive distances only, a singleton is an irrelevant but
literal exception to (T).

The main new result below is an explicit asymptotic counterexample to a
*relaxation* of (T), not a point-set counterexample. It preserves integer
translation multiplicities, their total mass, quarter-turn symmetry, all
Gaussian norm representation capacities, and even diameter of order
\(\sqrt n\). A primitive, large-height refinement also satisfies **every
global Gaussian-ideal collision lower bound** and matches actual endpoint
congruence data modulo all ideals dividing \(n!\). Both constructions fail
positive definiteness, as proved by exact finite quadratic-form witnesses.
Thus discarding the autocorrelation constraint really can lose the desired
conclusion; representation capacities and global ideal-collision lower
bounds do not by themselves suffice.

Also proved are a Gaussian-gcd normalization lemma, exact local incidence
formulas, and a restricted rotation-energy lower bound. None of these is
claimed to supply the missing uniform support-sensitive estimate.

## 1. Normalization and the precise missing estimate

Identify \(\mathbb Z^2\) with \(\mathbb Z[i]\), and put

\[
 a_P(z)=|P\cap(P-z)|,\qquad
 r_d=\sum_{N(z)=d}a_P(z),\qquad N(z)=z\bar z.
\]

Then

\[
 a_P(0)=n,\quad \sum_z a_P(z)=n^2,\quad
 M:=\sum_{d>0}r_d=n(n-1),\quad E=\sum_{d>0}r_d^2.
\]

If \(S=\{d:r_d>0\}\) and \(D=|S|\), Cauchy--Schwarz gives

\[
 ED\ge M^2.
\]

In particular, if \(D\ge\alpha n\), then
\(ED^2\ge(\alpha/4)n^5\). An asymptotic counterexample to (T) must have
\(D=o(n)\). With

\[
 \operatorname{CV}^2=\frac{D\sum_{d\in S}(r_d-M/D)^2}{M^2},
\]

we have exactly

\[
 \frac{ED}{M^2}=1+\operatorname{CV}^2.
\]

The requested amplification is therefore

\[
 1+\operatorname{CV}^2\ge c\frac{n^3}{D(n-1)^2},
 \tag{1}
\]

which is comparable to \(n/D\), uniformly for \(n\ge2\).

## 2. Common distance divisibility is exactly Gaussian similarity

### Lemma 2.1

Fix \(p_0\in P\), and let \(\alpha\) generate the Gaussian ideal generated
by all \(p-p_0\), \(p\in P\). Then

\[
 \boxed{\gcd\{N(p-q):p,q\in P,\ p\ne q\}=N(\alpha).}
 \tag{2}
\]

Consequently \(Q=(P-p_0)/\alpha\subset\mathbb Z[i]\) has gcd of its positive
squared distances equal to one. Passing from \(P\) to \(Q\) preserves
\(n,D,E\) exactly.

### Proof

Every difference is divisible by \(\alpha\), so it suffices to prove that
a Gaussian-primitive set \(Q\), containing zero, has no rational prime
common to all its squared distances.

* If \(p\equiv3\pmod4\), then \(p\mid N(z)\) implies \(p\mid z\) in
  \(\mathbb Z[i]\). If all distances were divisible by \(p\), applying this
  to differences from zero would give a common Gaussian factor \(p\).
* If \(p=2\), then \(2\mid N(z)\) is equivalent to \((1+i)\mid z\), with
  the same consequence.
* If \(p\equiv1\pmod4\), write \(p=\pi\bar\pi\). The quotient is
  \(\mathbb Z[i]/(p)\cong\mathbb F_p\times\mathbb F_p\), and the norm is
  the product of the two coordinates. If every pairwise difference has norm
  zero, every two residue points share a coordinate. Such a set lies in one
  row or one column: if two points have different first coordinates, their
  second coordinates coincide; any point with another second coordinate
  would have to share both of their different first coordinates, impossible.
  Thus all points lie in one coset of \((\pi)\) or of \((\bar\pi)\).
  Since zero belongs to the set, this is a common Gaussian factor, again a
  contradiction.

This proves (2), including all prime powers, by first dividing by the full
Gaussian gcd. In particular, the gcd of the squared distances is itself a
sum of two squares. The assertion concerns **all pairwise distances**, not
just distances from one anchor; the latter version would be false.

## 3. Exact divisor incidences and what they fail to control

For any nonzero Gaussian integer \(\beta\), write
\(n_c=|P\cap(c+(\beta))|\). There are \(N(\beta)\) residue classes. Exactly,

\[
 \sum_{\substack{z\ne0\\\beta\mid z}}a_P(z)
  =\sum_c n_c(n_c-1)
  \ge \frac{n^2}{N(\beta)}-n.
 \tag{3}
\]

The right side can be negative; (3) is not silently being used as a
positive lower bound for large ideals.

For a split rational prime \(p\), let \(n_{uv}\) be the point counts in
\(\mathbb F_p\times\mathbb F_p\), with row totals \(R_u\) and column totals
\(C_v\). Inclusion--exclusion gives the exact norm-divisibility formula

\[
 \boxed{
 \sum_{p\mid d}r_d=
 \sum_u R_u^2+\sum_v C_v^2-\sum_{u,v}n_{uv}^2-n.}
 \tag{4}
\]

For an inert prime \(p\equiv3\pmod4\), the corresponding formula is
\(\sum_{p\mid d}r_d=\sum_c n_c^2-n\), where \(c\) ranges over residues
modulo \(p\) in \(\mathbb Z[i]\).

These formulas do not justify replacing the two split-prime collision
probabilities by independent events. For example, a uniform distribution
on a permutation graph in \(\mathbb F_p^2\) has norm-zero probability
\(1/p\), whereas uniform measure on the full quotient has probability
\(2/p-1/p^2\). Here these probabilities include equal sampled points.

### An exact support-sensitive consequence

For any partition \(S=\bigsqcup_j S_j\) into nonempty cells, put

\[
 \lambda_j=|S_j|/D,\qquad \theta_j=M^{-1}\sum_{d\in S_j}r_d.
\]

Cauchy--Schwarz in each cell gives

\[
 \frac{ED}{M^2}\ge\sum_j\frac{\theta_j^2}{\lambda_j}
   =1+\sum_j\frac{(\theta_j-\lambda_j)^2}{\lambda_j}.
 \tag{5}
\]

In particular, for a two-cell divisibility partition with support fraction
\(\lambda\) and pair-mass fraction \(\theta\), the gain is
\((\theta-\lambda)^2/[\lambda(1-\lambda)]\).

Equation (5) is valid without any height bound. The missing theorem is a
lower bound of order \(n/D\) for an appropriate discrepancy, or another
way of exploiting the full endpoint information. Counts of allowed norm
values in an ambient interval cannot replace the empirical fractions
\(\lambda_j\) for an arbitrary set of distance labels. If a divisibility
condition holds for every distance, Lemma 2.1 removes it by similarity;
it does not supply a variance gain.

## 4. Explicit asymptotic obstruction to the translation-profile relaxation

Let

\[
 r_2(d)=|\{z\in\mathbb Z[i]:N(z)=d\}|,\qquad R(d)=r_2(d)/4
 \quad(d\ge1).
\]

The integer \(R(d)\) counts quarter-turn orbits. It is multiplicative, with

\[
 R(2^a)=1,\quad
 R(p^a)=a+1\ (p\equiv1\pmod4),\quad
 R(p^a)=\begin{cases}1&a\text{ even},\\0&a\text{ odd}\end{cases}
 \ (p\equiv3\pmod4).
 \tag{6}
\]

### Theorem 4.1 (relaxation obstruction, not a lattice counterexample)

There is an explicit sequence of finitely supported functions
\(A_X:\mathbb Z[i]\to\mathbb Z_{\ge0}\), and integers \(n_X\to\infty\),
such that, writing

\[
 \widetilde r_d=\sum_{N(z)=d}A_X(z),\quad
 \widetilde D=|\{d>0:\widetilde r_d>0\}|,\quad
 \widetilde E=\sum_{d>0}\widetilde r_d^2,
\]

all of the following hold:

1. \(A_X(0)=n_X\), \(\sum_z A_X(z)=n_X^2\), and
   \(A_X(iz)=A_X(z)=A_X(-z)\).
2. \(0\le A_X(z)\le n_X/8\) for \(z\ne0\).
3. Every \(\widetilde r_d\) is an even integer, and
   \(\sum_{d>0}\widetilde r_d=n_X(n_X-1)\).
4. The positive radial support is **exactly all sums of two squares at
   most \(X\)**, and
   \(\widetilde r_d\le n_X r_2(d)/8\).
5. \(n_X\sim\pi X/8\), \(\operatorname{supp}(A_X)\subset\{N(z)\le X\}\), and
   \[
    \boxed{\frac{\widetilde E\widetilde D^2}{n_X^5}
      =O((\log X)^{-1/8})\longrightarrow0.}
    \tag{7}
   \]

Nevertheless these functions are not autocorrelations of finite point
sets: on the explicit subsequence \(X=(24\cdot3^j)^2\), \(j\ge1\), a
512-by-512 principal kernel matrix has a negative quadratic form, as
proved in Section 5.

### Analytic input and clipping estimate

We use the classical Landau--Ramanujan bound

\[
 B_0(X):=|\{d\le X:R(d)>0\}|\asymp X/\sqrt{\log X},
 \tag{8}
\]

and the standard multiplicative-function moment bound

\[
 \sum_{d\le X}R(d)^{3/2}\ll X(\log X)^{\sqrt2-1}.
 \tag{9}
\]

For clarity, (9) is not an assumption about subsets of grids. It follows
from Wirsing's mean-value theorem applied to \(f=R^{3/2}\):
\(f(p)=2\sqrt2\) on primes \(1\bmod4\), zero on primes \(3\bmod4\),
\(f(2)=1\), and \(\sum_p\sum_{a\ge2}f(p^a)/p^a<\infty\).
The prime mean parameter is \(\kappa=\sqrt2>1\). Its Euler product is
\(\asymp(\log X)^{\sqrt2}\), giving (9). Thus the nonintegral exponent in
(9) follows from the explicit prime factors (6), not interpolation between
the first and second moments.

Set

\[
 T=\lfloor(\log X)^{7/8}\rfloor,\qquad b_d^{(0)}=\min(R(d),T),
 \qquad B^{(0)}=\sum_{d\le X}b_d^{(0)}.
\]

The elementary lattice-point estimate gives
\(\sum_{d\le X}R(d)=\pi X/4+O(\sqrt X)\). Also,

\[
 0\le\sum_{d\le X}R(d)-B^{(0)}
 \le\sum_{R(d)>T}R(d)
 \le T^{-1/2}\sum_{d\le X}R(d)^{3/2}
 \ll X(\log X)^{\sqrt2-23/16}=o(X),
 \tag{10}
\]

since \(\sqrt2<23/16\). Therefore \(B^{(0)}\sim\pi X/4\).

### Exact integral construction

Use the fixed list of 15 split primes

\[
 5,13,17,29,37,41,53,61,73,89,97,101,109,113,137.
\]

For sufficiently large \(X\), their initial \(b_p^{(0)}\) values are all
2. Let \(h\in\{0,\ldots,15\}\) be the residue of \(B^{(0)}-14\) modulo
16. Decrease \(b_p^{(0)}\) by one at the first \(h\) primes on the list,
and leave all other values unchanged. Call the results \(b_d\), and put

\[
 B=\sum_{d\le X}b_d=B^{(0)}-h\equiv14\pmod{16},\qquad n=B/2+1.
\]

Then \(8\mid n\), \(B=2(n-1)\), and all originally represented norms
remain in the support. For every represented \(d\), choose exactly \(b_d\)
of its \(R(d)\) quarter-turn orbits, for example the first ones in
lexicographic order of canonical integer-coordinate representatives. Set

\[
 A_X(0)=n,\qquad
 A_X(z)=\begin{cases}
 n/8,&z\text{ is in one of the selected nonzero orbits},\\
 0,&\text{otherwise}.
 \end{cases}
 \tag{11}
\]

This is a fully specified integer-valued, quarter-turn-invariant function.
It satisfies

\[
 \sum_{z\ne0}A_X(z)=(n/8)\,4B=n(n-1),\qquad
 \widetilde r_d=(n/2)b_d.
\]

In particular all radial multiplicities are even. Moreover

\[
 \widetilde E=(n^2/4)\sum_db_d^2
 \le(n^2/4)TB=(n^2/2)(n-1)T.
 \tag{12}
\]

Equations (8), (10), and (12) prove all assertions, including (7).
This construction suppresses the high-representation tail while losing
only \(o(X)\) displacement vectors. The total pair mass and the full norm
support remain of the same orders as for a dense grid.

### Even an abstract colored complete graph realizes the radial counts

The profile is not failing because its multiplicities cannot count edges.
Since \(8\mid n\), one-factorize \(K_n\) into \(n-1\) perfect matchings,
and split every matching into two sets of \(n/4\) edges. This gives
\(2(n-1)=B\) blocks. Assign \(b_d\) blocks to label \(d\). Label \(d\)
then has ordered multiplicity \((n/2)b_d\), and every vertex has at most
\(b_d\le R(d)=r_2(d)/4\) incident edges of this label.

This is only an abstract edge coloring. It does not impose geometric
circle intersections, simultaneous residue embeddings, or an endpoint
realization of the chosen displacement vectors.

## 5. Exact positive-definiteness failure: why it is not a counterexample

Every genuine autocorrelation is positive definite:

\[
 \sum_{j,k}c_jc_k a_P(z_j-z_k)
 =\sum_{x\in\mathbb Z[i]}\left(\sum_jc_j\mathbf1_P(x-z_j)\right)^2
 \ge0
 \tag{13}
\]

for real \(c_j\) and arbitrary \(z_j\in\mathbb Z[i]\).

We give an exact violation of (13) for (11). Let

\[
 a=3^j,\quad X=(24a)^2,\quad z_\ell=\ell a\quad(0\le\ell<512),
\]

and put

\[
 v_\ell=\begin{cases}
 1,&\ell\bmod32\in\{0,\ldots,15\},\\
 -1,&\ell\bmod32\in\{16,\ldots,31\}.
 \end{cases}
\]

For \(1\le k\le24\), formula (6) gives

\[
 R((ka)^2)=R(k^2)\le3.
\]

Indeed the only split primes dividing such \(k\) are \(5,13,17\), at most
one of them divides any one such \(k\), and its exponent is one.
For \(j\ge1\), these squared norms are divisible by 9, hence none was
changed by the fixed-prime adjustment. Also \(T\ge3\). Thus every orbit at
these norms was selected, so

\[
 \frac{A_X(ka)}n=
 \begin{cases}1,&k=0,\\1/8,&1\le|k|\le24,\\0,&|k|\ge25.\end{cases}
 \tag{14}
\]

The following finite calculation is exact:

\[
 \boxed{
 \frac1n\sum_{\ell,m=0}^{511}v_\ell v_m A_X(z_\ell-z_m)
 =512+\frac14\sum_{k=1}^{24}\sum_{\ell=0}^{511-k}
          v_\ell v_{\ell+k}
 =-25.}
 \tag{15}
\]

For a hand-check of the last equality, for general \(N\ge32\) divisible
by 32 let \(C(k)\) denote the periodic correlation averaged over one period.
Then

\[
 C(k)=1-k/8\ (0\le k\le16),\qquad
 C(k)=k/8-3\ (16\le k\le32).
\]

We have \(\sum_{k=1}^{24}C(k)=-9/2\). The sum of the omitted end terms
\(\sum_{k=1}^{24}\sum_{\ell=N-k}^{N-1}v_\ell v_{\ell+k}\), with the last
factor interpreted periodically, is \(-156\): for \(k\le16\) the inner
sum is \(-k\); for \(17\le k\le24\) it is \(3k-64\). Consequently the
quadratic form divided by \(n\) is \(-N/8+39\), which is \(-25\) for
\(N=512\).

Therefore these integer translation profiles **cannot** be the
\(a_P\) of any finite point set. This is an exact asymptotic obstruction
to the relaxation, not numerical evidence against (T), and not an
obstruction to every argument retaining positive definiteness.

## 6. Exact rotation identity and the limitation of a box-energy bound

For a rational rotation \(\rho\in\mathbb Q(i)\), \(N(\rho)=1\), let

\[
 m_{\rho,t}=|\{p\in P:\rho p+t\in P\}|.
\]

The ordered normalization gives exactly

\[
 E=\sum_{\rho}\sum_t m_{\rho,t}(m_{\rho,t}-1)
  =\sum_{\rho}\sum_{z\ne0}a_P(z)a_P(\rho z),
 \tag{16}
\]

where \(a_P\) is zero off \(\mathbb Z[i]\). Only finitely many terms
with \(m_{\rho,t}\ge2\) contribute. Every pair of directed equal-length
segments determines one direct isometry, proving the first identity.
The second follows by sorting pairs of matched endpoints by their difference.

For \(\rho=\alpha/\bar\alpha\) with
\((\alpha,\bar\alpha)=1\), the inner sum can also be written

\[
 \sum_{v\ne0}a_P(\bar\alpha v)a_P(\alpha v).
 \tag{17}
\]

The ideal-incidence lower bounds (3) give lower bounds on the two separate
sums in (17), not on their overlap. For example, if \(P\) is collinear and
\(\rho\ne\pm1\), the overlap is zero. Collinear sets have \(D\ge n-1\),
so this observation does not refute (T); it identifies why an argument
using (3) must make additional use of the small support \(D\).

### Restricted lemma

If \(P\subset[0,L]^2\cap\mathbb Z^2\), \(L\ge1\), then

\[
 E(P)\gg \frac{n^4}{L^2}\log(2+n/L).
 \tag{18}
\]

**Proof.** For \(\rho=\alpha/\bar\alpha\) as above, put \(q=N(\alpha)\).
Translations with nonempty overlap lie in \(\bar\alpha^{-1}\mathbb Z[i]\)
and in a disk of radius \(O(L)\). There are at most \(C L^2q\) of them,
for an absolute \(C\). Since \(\sum_t m_{\rho,t}=n^2\),

\[
 \sum_t m_{\rho,t}(m_{\rho,t}-1)
 \ge\frac{n^4}{CL^2q}-n^2.
\]

For \(q\le n^2/(2CL^2)\), this is at least
\(n^4/(2CL^2q)\). Choose \(\alpha=u+iv\) with \(u,v>0\),
\(\gcd(u,v)=1\), and opposite parities. These give distinct rotations,
\((\alpha,\bar\alpha)=1\), and

\[
 \sum_{N(\alpha)\le Q}\frac1{N(\alpha)}\gg\log Q
\]

for sufficiently large \(Q\), by elementary primitive lattice-point
counting and partial summation. Summing proves (18) when \(n/L\) is large.
For the remaining range, the translation contribution in (16) satisfies

\[
 \sum_{z\ne0}a_P(z)^2\ge\frac{[n(n-1)]^2}{O(L^2)}\gg n^4/L^2,
\]

which supplies the bounded logarithmic factor.

For a fixed positive-density subset of a square, (18) forces energy of
order at least \(n^3\log n\), with a density-dependent constant. But (18)
is **not** a solution of (T): its dependence on \(L\) can be arbitrarily
bad, and it does not furnish the required lower bound on \(D\). It cannot
be applied to arbitrary lattice subsets by assuming polynomial height.

## 7. A primitive variant passing every global ideal-collision lower bound

The preceding construction need not satisfy the ideal-incidence inequalities
(3). The following refinement **does** satisfy all those lower bounds, and
has gcd-one norm support. Moreover, its reductions modulo every ideal
dividing a specified very large integer are genuine autocorrelations of
one simultaneously consistent endpoint residue multiset. It still is not
a point-set autocorrelation. This distinguishes global congruence tests
from adaptive arguments that retain and renormalize the points inside a
large residue class.

Start with a profile \(A_X\) from Theorem 4.1, with parameter \(n_0\) in
place of \(n\). Put

\[
 n=n_0+1,\qquad K=n!,\qquad s=\lceil\log_2 n_0\rceil,
 \qquad \gamma_j=1+iKj\quad(1\le j\le s).
\]

For \(n_0\ge8\), we have \(2s\le n\). The rational integers
\(N(\gamma_j)=1+K^2j^2\) are pairwise coprime. Indeed any common prime
factor for indices \(j\ne k\) divides \((j-k)(j+k)\), hence is at most
\(2s\) and divides \(K\), whereas \(N(\gamma_j)\equiv1\pmod K\).
Also \(\gamma_j\) and \(\bar\gamma_j\) are coprime Gaussian integers:
a common divisor divides their sum 2, but their norms are odd.

It follows that the \(2^s\) products obtained by independently choosing
\(\gamma_j\) or \(\bar\gamma_j\) are distinct. They all have the same
norm

\[
 d_* = \prod_{j=1}^s(1+K^2j^2),
\]

and all are congruent to 1 modulo \(K\). Choose the first \(n_0\) of these
products in lexicographic order of their sign choices, calling them
\(z_1,\ldots,z_{n_0}\). Their negatives are different from all of them,
since \(K>2\). Define

\[
 A'(0)=n,\qquad A'(Kz)=A_X(z)\quad(z\ne0),\qquad
 A'(z_j)=A'(-z_j)=1,
 \tag{19}
\]

and set all remaining entries to zero. The specified supports are disjoint.
This is a nonnegative integer-valued symmetric function. It need not retain
quarter-turn symmetry; that is not a necessary condition for an arbitrary
point-set autocorrelation.

The off-diagonal mass is

\[
 n_0(n_0-1)+2n_0=n(n-1).
\]

The radial distribution is the old one with labels multiplied by \(K^2\),
plus the single new label \(d_*\) of multiplicity \(2n_0\). Therefore

\[
 D'=\widetilde D+1,\qquad E'=\widetilde E+4n_0^2,
 \qquad E'(D')^2/n^5\longrightarrow0.
 \tag{20}
\]

All capacities \(r'_d\le n r_2(d)/8\) still hold. For old labels, use
\(r_2(K^2d)\ge r_2(d)\). For the new label, the selected products already
give at least \(2n_0\) representations, sufficient since \(n\ge8\).
The old support contains \(K^2\), and \(d_*\equiv1\pmod K\), so

\[
 \gcd\{d:r'_d>0\}=1.
 \tag{21}
\]

Thus Lemma 2.1 cannot remove the large scale by one global similarity.

**Every global ideal-collision lower bound holds.** If
\(1<q=N(\beta)<n\), then \(\beta\mid q\mid K\). All old differences
are divisible by \(\beta\), and none of the new differences is. Hence

\[
 \sum_{\substack{z\ne0\\\beta\mid z}}A'(z)=n_0(n_0-1)
  \ge n^2/q-n.
 \tag{22}
\]

For the last inequality it suffices to take \(q=2\); the difference is
\((n_0-1)^2/2\ge0\). For \(q\ge n\) the right
side is nonpositive, and for \(q=1\) equality holds with the full pair
mass. This proves the analogue of (3) for **every** Gaussian ideal.

There is more consistency than just these inequalities. Modulo every
nonunit ideal \((\beta)\) with \(\beta\mid K\), periodizing \(A'\) gives
exactly

\[
 (n_0\delta_0+\delta_1)*
 (n_0\delta_0+\delta_{-1}).
 \tag{23}
\]

The formula includes the possibility \(1=-1\) in the quotient. These
endpoint residue distributions are simultaneously realized by the actual
set

\[
 P_* = \{1\}\ \cup\ \{1-z_j:1\le j\le n_0\}.
\]

In particular, all such coarse quotient Fourier-positivity tests and exact
split/inert residue-incidence formulas agree with an actual endpoint set.
We are **not** asserting that \(A'=a_{P_*}\): their internal differences
inside the large residue class have been replaced by the fake profile.

Finally, on \(X=(24\cdot3^j)^2\), use the test locations from (15)
multiplied by \(K\). The new cross-differences are not multiples of \(K\),
so they do not enter the quadratic form. The only change to (15) is the
increase of the diagonal by one. The new quadratic form is exactly

\[
 -25n_0+512<0.
 \tag{24}
\]

For this subsequence \(n_0>21\), already following from the number of
squared norms at most \(X\) and the at-most-15 adjustment. Thus (19) is
again certainly not a genuine autocorrelation.

**Scope of this stronger obstruction.** Global divisor-collision lower
bounds, global primitive normalization, and the full congruence data at
all ideals dividing \(K\) still do not force (T). This does not rule out
using other moduli adaptively, the full positive-definite kernel, or a
Gaussian-ideal density increment that retains the actual large fiber and
then divides it by \(K\). Those are precisely the types of additional
endpoint information absent from this construction. Its large height is
intentional; it does not invoke an ambient-diameter bound.

## 8. Verification and references

`verify_lattice_energy_obstruction.py` performs exact finite checks of:

* Gaussian gcd normalization, including exhaustive small triples;
* the split and inert residue-incidence identities;
* the support-partition inequality with rational arithmetic;
* the rotation identity, with rational complex arithmetic;
* the integral clipping construction, pair mass, capacities, energy bound,
  and a colored-complete-graph realization of its radial counts;
* the exact negative quadratic form (15), including the orbit-selection
  and norm-factorization conditions used in (14);
* the primitive refinement (19): explicit distinct circle products, mass,
  energy, gcd, every ideal with norm below the sample cardinality, and
  full periodizations agreeing with one actual endpoint residue set;
* the diagonal-change identity yielding the negative witness (24).

The finite computations verify identities and construction details, not the
asymptotic limit in (7). That limit is proved by (8)--(12).

External analytic inputs checked against local sources:

* Cilleruelo--Sharir--Sheffer, *On lattices, distinct distances, and the
  Elekes--Sharir framework*, arXiv:1306.0242, Section 1: ordered distance
  energy, Landau--Ramanujan support count, and the square-grid Cauchy loss.
* *Variations on a theorem of Davenport concerning abundant numbers*,
  arXiv:1306.0537, Section 3.1, Proposition `prop:wirsing`: the stated
  Wirsing mean-value theorem. Its hypotheses for \(R^{3/2}\) are checked
  above. Mertens' estimates in the two reduced classes modulo 4 give the
  Euler-product exponent used in (9).

No Lean files or existing conjecture specifications were changed.

## Conclusion

A proof of (T) still needs a theorem that couples the *actual* additive
autocorrelation and its radial support. The exact construction in Section 4
shows that even the entire divisor-capacity profile, correct integer mass,
and very regular displacement support do not force the amplification.
Section 5 identifies the lost condition explicitly. Section 7 shows that
global primitive normalization and all global ideal-collision lower bounds
can hold even for an asymptotically failing profile with consistent coarse
endpoint residues. This leaves genuine autocorrelation positivity and
adaptive, rescaled endpoint fibers as substantive additional constraints,
not optional bookkeeping. No actual asymptotic lattice counterexample is
supplied, and the original inequality remains unresolved.
