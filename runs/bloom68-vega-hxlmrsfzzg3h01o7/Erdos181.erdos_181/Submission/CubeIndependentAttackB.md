# Independent attack B: full square graphs, and the unresolved dense-cube bound

## Status

**The requested theorem is not proved or disproved here.** In particular, this
report does not establish an absolute `C` for which

\[
 e(F)\ge |F|(|F|-1)/4,\qquad |F|\ge C2^d
 \quad\Longrightarrow\quad Q_d\subseteq F.
\]

There is no new upper bound for `R(Q_d)` in this report.

The independent result is a global obstruction to two possible ways of using
**actual, full square graphs**, not arbitrary endpoint-labelled graphs:

* Even choosing a matching adaptively, after inspecting the entire host,
  cannot in general produce a half-dense matching restriction of the square
  graph. All sufficiently large matching restrictions can have density only
  `1/4 + o(1)`.
* Among the ordinary **injective** auxiliary cube embeddings, the fraction
  with disjoint original endpoints can be `2^{-Omega(d 2^d)}`, not merely
  the birthday-type `exp(-Theta(2^d))` loss of a complete bipartite host.
  This can happen when the square graph is spectrally quasirandom.

The same examples satisfy the original half-density hypothesis and explicitly
contain the required cube. Thus these are **not counterexamples to the
problem**, or to an estimate which assumes that the original graph is
`Q_d`-free. They show why those two transfer strategies do not finish it.
The precise remaining cube-free estimate is stated in Section 7.

All copies in this report are ordinary, not necessarily induced, and
injectivity is stated explicitly. No Lean files, including `Spec.lean`, were
changed. No priority claim is made for the auxiliary results.

## 1. Definitions and a quantitative full-square-graph stress test

For a bipartite graph `G=(A,B)`, write `S(G)` for the graph on `E(G)` in which

\[
 (x,y)\sim (x',y')
 \iff x\ne x',\ y\ne y',\ xy',x'y\in E(G).
\]

In particular, **every** rectangle present in `G` supplies both diagonals in
`S(G)`. No squares are selectively deleted.

Let `I_k(G)` count labelled injective embeddings `Q_k -> S(G)`, and let
`D_k(G)` count those embeddings whose labels are pairwise endpoint-disjoint.
Thus distinct edge labels are required in both counts; `D_k` additionally
requires distinct row labels and distinct column labels.

**Theorem.** Fix a real `C>=1`. Suppose

\[
 k\ge \max\{256,\lceil16\log_2(C+1)\rceil\},\quad
 d=k+1,\quad m=2^k,\quad t=\lceil Cm\rceil,\quad N=2t.
\]

There exist a simple graph `F` on `N` vertices and a partition `A,B`, with
`|A|=|B|=t`, such that, for `G=F[A,B]`, all the following hold.

1. **The densities are in the requested range:**
   \[
   e(F)\ge N(N-1)/4,\qquad e(G)\ge t^2/2\ge N(N-1)/8.
   \]
   Moreover `G` contains an explicitly planted `Q_d`. In particular,
   `D_k(G)>0`.

2. **Nearly balanced degrees:** for every relevant vertex,
   \[
   |\deg_F(v)-(N-1)/2|\le3N^{3/4},\qquad
   |\deg_G(v)-t/2|\le3t^{3/4}.
   \]

3. **All large matching restrictions are sparse, simultaneously.** For
   every partition `A',B'` of `V(F)` and every matching `M` of
   `F[A',B']` of size `r>=m`,
   \[
   e\bigl(S(F[A',B'])[M]\bigr)
    \le(1/4+\delta_k)\binom r2,
   \tag{1}
   \]
   where
   \[
   \delta_k=2^{-k/8}
       +\frac{2(2^{3k/4}+k+1)}{2^k-1}<1/12,
   \qquad \delta_k\longrightarrow0.
   \tag{2}
   \]
   The partition and the matching may both depend on the entire graph.

4. **A superlinear entropy loss for the actual auxiliary cube counts:**
   \[
   0<D_k(G)\le 2^{-km/4} I_k(G).
   \tag{3}
   \]

5. **Even the full auxiliary graph is quasirandom at the usual scale.**
   If `e=e(G)`, `A_S` is the adjacency matrix of `S(G)`, and `J_e` is
   the all-ones matrix, then
   \[
   \|A_S-\tfrac14J_e\|_{\rm op}\le3t^{15/8}=o(e)
   \tag{4}
   \]
   as `k -> infinity` with `C` fixed.

Here `N>=C2^d` and `N<C2^d+2`. This is a dimension-uniform construction on
exactly the scale relevant to the question, not a fixed-size obstruction.

### Construction

Start with `H~G(N,1/2)` on the fixed partition `A,B`. Set

\[
 u=\lfloor m^{3/4}\rfloor.
\]

Choose `A_0 subset A`, `B_0 subset B`, each of size `u`, and plant the complete
bipartite graph `P=K_{A_0,B_0}`. Also plant a copy `T` of `Q_d`, with its two
parities in `A,B`. This is possible since `t>=m`. Define

\[
 F=H\cup P\cup T,\qquad G=F[A,B].                 \tag{5}
\]

The planted union has maximum degree at most

\[
 \Gamma=u+d,
\]

contains at least `u^2` edges, and is fixed before sampling `H`. Its two
pieces may overlap. We prove below that the desired events have positive
joint probability.

## 2. Adaptive matchings: an exact independent-edge calculation

Fix any ordered list of oriented disjoint pairs

\[
 M=((x_1,y_1),\ldots,(x_r,y_r))
\]

of host vertices. At this point the pairs need not be edges. Put

\[
 X_H(M)=\sum_{1\le i<j\le r}
      1_{x_i y_j\in H}\,1_{x_j y_i\in H}.
\]

The `2 binom(r,2)` host edges used here are all different. Hence the summands
are independent Bernoulli variables of parameter `1/4`, and

\[
 X_H(M)\sim\operatorname{Bin}(\tbinom r2,1/4).       \tag{6}
\]

Hoeffding's inequality gives, for `eta=m^{-1/8}`,

\[
 \Pr\{X_H(M)>(1/4+\eta)\tbinom r2\}
       \le \exp(-\eta^2r(r-1)).                    \tag{7}
\]

There are at most `N^{2r}` such ordered oriented lists. Consequently the
probability that the upper bound fails for any list of size at least `m` is
at most

\[
 \sum_{r=m}^{t}\exp(2r\log N-\eta^2r(r-1)).         \tag{8}
\]

Throughout probability estimates, `log` is natural logarithm.
Our restrictions imply `C+1<=m^{1/16}`, `t<=m^{17/16}` and
`eta^2(m-1)>=4 log N`. Thus (8) is at most

\[
 t\exp(-m^{7/4}/4).                               \tag{9}
\]

Now add the planted edges. For a fixed list `M`, each newly added host edge
can turn on **at most one** summand of `X_H(M)`: its endpoints determine the
two members of the matching involved. Among the `2r` endpoints of `M`, the
planted union has at most `Gamma r` edges. Therefore, deterministically,

\[
 X_F(M)\le X_H(M)+\Gamma r.                         \tag{10}
\]

If `M` is a matching in `F[A',B']`, oriented from `A'` to `B'`, then
`X_F(M)` is exactly `e(S(F[A',B'])[M])`. Equations (7)--(10), and
`r>=m`, prove (1). The bound in (2) follows from `u<=m^{3/4}`; it is
less than `1/12` for `k>=256`.

**Important scope:** this rules out a procedure whose desired output is a
single large matching restriction with density at least `1/2`. It does not
rule out finding a sparse cube inside such a restriction, or a method which
uses many restrictions together with further structure.

## 3. Upper bound for the endpoint-disjoint count

There is an exact bijection between the maps counted by `D_k(G)` and the
bipartition-preserving injective maps `Q_d -> G`, for a fixed choice of the
last cube coordinate. Given an auxiliary label `(x_z,y_z)` at `z in Q_k`,
put `x_z` at `(z,0)` and `y_z` at `(z,1)` when `z` has even parity, and
reverse these placements when `z` has odd parity. The vertical edges and
the two cross edges supplied by each auxiliary adjacency are precisely the
edges of `Q_d`. Endpoint disjointness is precisely injectivity. The inverse
reads the last-coordinate edges of a bipartition-preserving cube embedding.

We need two elementary global estimates for this count.

### 3.1 How many cube edges can lie in the small planted biclique?

For every `W subset V(Q_d)`,

\[
 e(Q_d[W])\le\tfrac12|W|\log_2|W|.                 \tag{11}
\]

Here `0 log 0=0`. For completeness, split `W` according to one cube
coordinate, with part sizes `a<=b`. Induction bounds the internal edges by
`(a log_2 a+b log_2 b)/2`; at most `a` edges cross. The needed inequality

\[
 a\log_2a+b\log_2b+2a\le(a+b)\log_2(a+b)
\]

is equivalent to `H_2(a/(a+b))>=2a/(a+b)`, which follows from concavity of
binary entropy on `[0,1/2]` and its endpoint values `0,1`.

An injective cube map uses at most `2u` vertices of `A_0 union B_0`.
Thus the number `a_P` of its required edges belonging to `P` satisfies

\[
 a_P\le u\log_2(2u).                              \tag{12}
\]

### 3.2 A matching-factorization bound for the other planted edges

Let `a_T(phi)` count cube edges mapped into `T`. Sum now over **all** maps
of the two cube parities to `A,B`, with repetitions allowed. Then

\[
 \sum_\phi 2^{a_T(\phi)}
 \le \bigl(t^2+(2^d-1)e(T)\bigr)^m
 =\bigl(t^2+(2m-1)dm\bigr)^m.                     \tag{13}
\]

To prove this, choose `phi` uniformly from these `t^{2m}` maps. The edges of
`Q_d` split into `d` coordinate perfect matchings, each of size `m`. Let
`Z_i` be the product of the factors `2^{1_{phi(v)phi(w) in T}}` along
matching `i`. Hölder gives

\[
 \mathbb E\prod_{i=1}^dZ_i
 \le\prod_{i=1}^d(\mathbb E Z_i^d)^{1/d}.
\]

Within one coordinate matching the image pairs are independent, so

\[
 \mathbb E Z_i^d
   =\left(1+(2^d-1)\frac{e(T)}{t^2}\right)^m.
\]

Multiplying by `t^{2m}` proves (13). This estimate is used only as an upper
bound; allowing repetitions here does not purport to construct an embedding.

### 3.3 Combine the estimates

A fixed injective parity-preserving cube map requires `dm` different host
edges. Its probability of occurring in (5) is at most
`2^{-dm+a_P+a_T}`. Equations (12)--(13) imply

\[
 \mathbb E D_k(G)\le U,
 \qquad
 U=2^{-dm+u\log_2(2u)}
       \bigl(t^2+(2m-1)dm\bigr)^m.                \tag{14}
\]

In particular, with probability at least `3/4`,

\[
 D_k(G)\le4U.                                     \tag{15}
\]

For fixed `C`,

\[
 \log_2 U\le km+O_C(m\log(k+1))+O(km^{3/4})
             =(1+o(1))km.                        \tag{16}
\]

## 4. Many injective auxiliary cubes, all confined to too few endpoints

The full square graph on the planted biclique is an induced subgraph of
`S(G)` on `u^2` edge labels. List the vertices of `Q_k` in any order, and
let `r_i<=k` be the number of neighbours of vertex `i` that precede it,
with indices starting at zero. After placing its predecessors, at least

\[
 (u-r_i)^2-i
   \ge u^2\left(1-\frac{2r_i}{u}-\frac{i}{u^2}\right)           \tag{17}
\]

labels are available. This enforces adjacency to all preceding neighbours
and avoids every previously used edge label; it does not require distinct
row or column labels at nonadjacent vertices.

For the present parameters every loss in parentheses is at most `1/2`:
indeed it is at most `4k 2^{-3k/4}+4 2^{-k/2}`, which is below `1/2`
for `k>=256`. Use `log(1-x)>=-2x`, together with `sum_i r_i=km/2`, to obtain

\[
 I_k(G)\ge L,
 \qquad
 L=u^{2m}\exp\left(-\frac{2km}{u}-\frac{m(m-1)}{u^2}\right).
 \tag{18}
\]

Since `u<m`, none of these particular embeddings is endpoint-disjoint.
For fixed `C`,

\[
 \log_2 L=(3/2+o(1))km.                           \tag{19}
\]

Here is a finite check of the constant in (3), not just a comparison of
asymptotic leading terms. From `u>=m^{3/4}/2`, `u<=m^{3/4}`,
`t<=(C+1)m`, and `d=k+1`, equations (14) and (18) give

\[
\begin{split}
 \frac{\log_2(4U/L)}{km}
 \le{}&-\frac12+\frac1k+\frac{2\log_2(C+1)}k
        +\frac{\log_2(2k+3)}k\\
 &+(3/4+1/k)2^{-k/4}
   +\frac{4\,2^{-3k/4}+(4/k)2^{-k/2}}{\log 2}
   +\frac{2}{k2^k}.                              \tag{20}
\end{split}
\]

For `k>=256`, the second term is at most `1/256`, the third at most
`1/8`, the fourth at most `1/16`, and the last three terms together are
less than `1/64`. For the fourth and the last three terms, their displayed
functions of `k` are decreasing on this range, so their endpoint values
suffice. The sum of these error bounds is less than `1/4`. Thus

\[
 4U/L\le2^{-km/4},
\]

which proves (3) on event (15). Notice the scale:
`km/4=(d-1)2^d/8`, which cannot be absorbed in a fixed multiple of `2^d`.

## 5. The full square graph also has a small nontrivial spectral scale

This section retains the exact square-completion geometry.
Let `M_G` be the `t` by `t` bipartite adjacency matrix, and write

\[
 M_G=\tfrac12 J_t+W.
\]

On the **full** label universe `A x B`, define the symmetric kernel

\[
 K_{(x,y),(x',y')}=(M_G)_{xy'}(M_G)_{x'y}.
\]

Identifying a vector with a `t` by `t` matrix `X`, its operator is

\[
 X\longmapsto M_G X^{\mathsf T} M_G.
\]

The Frobenius norm inequality for matrix products, expanded around
`M_G=J_t/2`, gives

\[
 \|K-\tfrac14 J_{t^2}\|_{\rm op}
       \le t\|W\|_{\rm op}+\|W\|_{\rm op}^2.       \tag{21}
\]

Restrict this kernel to the actual labels `E(G)`. To obtain `A_S`, remove
exactly those entries whose labels share a row or a column, including the
diagonal. This removed symmetric matrix is nonnegative and has row sums
at most `2t-1`. Hence

\[
 \|A_S-\tfrac14J_e\|_{\rm op}
    \le t\|W\|_{\rm op}+\|W\|_{\rm op}^2+2t-1.    \tag{22}
\]

For the random bipartite matrix before planting, let `W_0=M_H-J_t/2`.
Its entries are independent signs of magnitude `1/2`, and direct expansion
shows

\[
 \mathbb E\operatorname{tr}((W_0W_0^{\mathsf T})^2)
       =(2t^3-t^2)/16.
\]

Only terms with equal row indices or equal column indices survive.
Since the trace dominates `||W_0||_op^4`, Markov gives

\[
 \Pr\{\|W_0\|_{\rm op}>t^{7/8}\}\le1/(8\sqrt t). \tag{23}
\]

The added-edge matrix has every row and column sum at most `Gamma`;
its operator norm is at most `Gamma`. On the complementary event in (23),

\[
 \|W\|_{\rm op}\le t^{7/8}+u+d\le2t^{7/8}.
\]

Substituting in (22), using `t>=2^{256}`, proves (4).
As `e>=t^2/2`, the error divided by `e` is at most `6t^{-1/8}`.
In particular, the auxiliary graph has cut discrepancy `o(e^2)`.
This does **not** supply a counting lemma for a cube whose order is growing
with the host; (3) exhibits that distinction directly.

## 6. Positive probability and the remaining properties

Let `q=binom(N,2)` and let `s>=u^2` be the number of distinct planted edges.
Then `e(F)` has law `s+Bin(q-s,1/2)`. The probability that `e(F)<q/2` is at
most

\[
 \exp(-u^4/(2q)).
\]

The same argument in the fixed cut bounds the probability that
`e(G)<t^2/2` by

\[
 \exp(-u^4/(2t^2)).
\]

Hoeffding and a union bound ensure that all degrees of `H` differ from
`(N-1)/2` by at most `N^{3/4}`, except with probability at most
`2N exp(-2 sqrt(N))`. All degrees in its fixed cut differ from `t/2` by
at most `t^{3/4}`, except with probability at most
`4t exp(-2 sqrt(t))`. Planting changes each degree by at most `Gamma`,
which proves the degree assertions on these events.

Using `u>=m^{3/4}/2`, `t<=m^{17/16}`, and the monotonicity of
`x exp(-2 sqrt(x))` for `x>1`, the combined failure probability for the two
density events, the degree events, (1), and (4) is at most

\[
 e^{-m^{7/8}/64}+e^{-m^{7/8}/32}
 +8m e^{-2\sqrt m}
 +m^{17/16}e^{-m^{7/4}/4}
 +\frac1{8\sqrt m}.                              \tag{24}
\]

For `m>=2^{256}` this is less than `1/8` (each term is decreasing there,
and each is already less than `2^{-64}` at the endpoint).
Event (15) fails with probability at most `1/4`. A union bound now gives
positive probability for all required events. The planted cube is present
in every outcome. This completes the theorem's proof.

## 7. Exactly what remains open in this attack

The known, exact square count is

\[
 s:=e(S(G))=2C_4(G)
   \ge \frac{8e(G)^4}{N^4}-\frac{(N-1)e(G)}2.       \tag{25}
\]

The endpoint-disjoint lift is also exact. What is missing is an upper bound
under **cube-freeness of the original graph**, not a lower bound on `s`.
For example, the following statement would suffice and is **not proved**:

> There are absolute `epsilon in (0,2)`, `K>=0`, `C_0`, and `d_0` such
> that every `Q_d`-free bipartite `G`, with
> `d>=d_0`, `N>=C_0 2^d`, and `e>=N(N-1)/8`, satisfies
> \[
> s\le(2-\epsilon)e^{\,2-2/(d+1)}+K2^{d-1}Ne.       \tag{26}
> \]

For clarity, its sufficiency can be checked without suppressing the error.
Put `h=2^d`, `m=h/2`, and take

\[
 C\ge\max\{C_0,6,128(K+1)/\epsilon\},\qquad N\ge Ch.
\]

The density condition implies `e>=4h^2`, so `e^{2/(d+1)}>=16`. The lower
and proposed upper bounds would give, respectively,

\[
 \frac{s}{e^2}\ge\frac18-\frac{17}{4N},
 \qquad
 \frac{s}{e^2}\le\frac18-\frac\epsilon{16}
                         +\frac{8Km}{N-1}.
\]

But

\[
 \frac{8Km}{N-1}+\frac{17}{4N}
 \le\frac{8K+17/8}{C}<\frac\epsilon{16},
\]

a contradiction. A maximum cut of a graph of the requested half-density
supplies exactly `e>=N(N-1)/8`. Finitely many dimensions below `d_0` can
be absorbed in a larger constant using the elementary fixed-bipartite-graph
extremal theorem. Thus (26) really would prove the desired density result
and hence the Ramsey result.

**No step above proves (26).** The theorem in this report deliberately
plants a cube, so it cannot contradict (26) either. It proves that the
following proposed substitutes do not work:

* “Full square completion lets us choose a large matching restriction
  with density at least `1/2`.” Equation (1) disproves this even with an
  arbitrary, globally adaptive choice of cut and matching.
* “The full square graph has sufficiently many ordinary injective cubes,
  so an `exp(-O(2^d))` fraction can be made endpoint-disjoint.” Equation
  (3) disproves this, even together with (4) and balanced original degrees.

A balanced supersaturation theorem may discard the concentrated family in
Section 4, or choose an entirely different distribution of embeddings.
Neither possibility is ruled out. What has not been shown is that, in every
cube-free original graph in the density range, enough well-distributed
square configurations remain to force an endpoint-disjoint cube or the
upper bound (26). The analogous uniform extremal estimate with leading
coefficient below `1` and controlled lower-order terms is likewise absent.

## 8. Verification and provenance

`check_cube_independent_attack_b.py` checks the independent cross-edge law,
the planted-edge perturbation inequality, the cube induced-edge bound on
all subsets through dimension four, the Hölder overlap estimate on small
host matrices, the endpoint-lift counting bijection, the finite coefficient
bounds used above, and the full-square kernel identity. These are checks of
the proved statements, not evidence for the unproved statement (26).

The checks passed; output is saved in `CubeIndependentAttackBVerification.txt`.
They include 4,096 augmentation patterns, all 65,814 subsets of the cubes in
dimensions zero through four, 1,072 exact Hölder comparisons, 661
endpoint-lift count comparisons, and 530 full-square matrix checks. Four
small planted-host expected counts were also evaluated exactly. The
coefficient and probability checks complement the all-dimension estimates
in the proof; they are not numerical verification of the asymptotic theorem
by construction of its enormous witnesses.

The two specified background reports were used to retain the exact
square-graph definition and the correct critical coefficient/error scale.
The earlier occupancy and independent-A reports were also consulted to
compare the scope of homomorphism-counting obstructions. The proof above
is self-contained apart from standard Hölder, Hoeffding, and elementary
matrix-norm inequalities. It uses no ordinary-cube extremal assertion for
an unrestricted square graph, no generic endpoint-label substitution, and
no tensor-power assertion of injectivity.

`Spec.lean` SHA-256 remains
`9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b`.
