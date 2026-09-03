# Spectral cube benchmark: an all-dimensional positive bound, with the endpoint gap explicit

## Status

**The requested bound with `N >= C_K 2^d` is not proved here.** Nor is it disproved. The uniform Ramsey assertion is not proved. No Lean specification is changed.

The positive result proved below is

> **Theorem.** Let `d >= 1`, `h = 2^d`, and let `G` be a simple graph on `N` vertices. Put
> \[
> p=\frac{e(G)}{\binom N2}\ge\frac12,\qquad
> B=A_G-p(J-I).
> \]
> If `||B||_op <= K sqrt(N)` and
> \[
> \boxed{N\ge 10^6(K+4)^2d^2\,2^d,}                         \tag{T}
> \]
> then `G` contains an ordinary, injective copy of `Q_d`.

All constants are independent of `d`. The **factor `d^2` in (T) is real and has not been removed**. Equivalently, this gives cubes of dimension `log_2 N - 2 log_2 log_2 N - O_K(1)`, not `log_2 N - O_K(1)`.

The main analytic input is an exact, nonnegative, **all-orders Gram decomposition** for the variance of a random common-neighbourhood size. This is not an estimate of individual signed graph products by `N^{-v/2}`. A second input is a dimension-sensitive sparsity bound for distance-two supports in the cube; using only their maximum degree would introduce an additional logarithmic loss.

The proof route is different from a completed activity expansion: after the Gram decomposition, a variable local lemma simultaneously supplies good common-neighbourhood lists, injectivity on one cube parity class, and a column-load bound. Hall's theorem completes the embedding. The precise obstruction to obtaining the constant-multiplier benchmark by this argument is recorded at the end and in `CubeSpectralBenchmarkGaps.md`.

Companion files:

* `CubeSignedActivityLemmas.md`: exact collision contraction into quotient **multigraphs**, the positivity criterion, and an all-orders whole-star resummation.
* `CubeSpectralStarControl.md`: after degree pruning, the entire induced-star activity subfamily has load `O((K^2+1)d^2/N)` at the desired linear `N/2^d` scale. This controls all star sizes, but not the remaining non-star/overlapping cores.
* `check_cube_spectral_benchmark.py` and `CubeSpectralBenchmarkVerification.txt`: independent checks of identities, support estimates, constants, and actual embedding certificates.

All logarithms in analytic estimates below are natural unless `log_2` is written.

## 1. A legitimate reduction to reference density one half

The reduction takes a **subgraph** of the original host. It does not assume that the actual density of the subgraph is exactly one half or at least one half.

### Lemma 1 (spectral thinning)

Under the theorem's hypotheses there is a spanning subgraph `G_0` of `G` such that, with `kappa = K+4`,

\[
 \|A_{G_0}-\tfrac12(J-I)\|_{op}\le\kappa\sqrt N.              \tag{1}
\]

**Proof.** Retain every edge independently with probability `theta=1/(2p)`. Write

\[
 A_{G_0}-\tfrac12(J-I)=\theta B+W,
\]

where `W` is symmetric, has zero diagonal, and has independent centred entries above the diagonal, each with range of length at most one.

For a fixed real unit vector `x`,

\[
 x^TWx=2\sum_{i<j}x_ix_jW_{ij}.
\]

The sum of the squared lengths of the summands' ranges is at most
`4 sum_{i<j} x_i^2 x_j^2 <= 2`. Hoeffding's inequality therefore gives

\[
 \Pr(|x^TWx|>t)\le2e^{-t^2}.
\]

A Euclidean `1/4`-net of the unit sphere has at most `9^N` members. For a symmetric matrix, its operator norm is at most twice the maximum absolute quadratic form on this net. Thus

\[
 \Pr(\|W\|_{op}>4\sqrt N)\le2\,9^Ne^{-4N}<1.
\]

Some outcome satisfies `||W|| <= 4 sqrt(N)`. Since `theta <= 1`, it satisfies (1). Containment in `G_0` implies containment in `G`. □

For the rest of the proof use `A=A_{G_0}` and `B_0=A-(J-I)/2`. The auxiliary reference `1/2` is not redefined as the actual edge density.

## 2. A large rectangular host with balanced columns

Take any partition `L dot-union R_0=V(G_0)` with `M=|L|=floor(N/2)`. For `v in R_0`, let

\[
 q_v=\frac{|N_{G_0}(v)\cap L|}{M}.
\]

Because the two parts are disjoint, their adjacency matrix is exactly
`A[L,R_0]=J/2+B_0[L,R_0]`. Consequently

\[
 \sum_{v\in R_0} (M q_v-M/2)^2
 \le\kappa^2NM.
\]

Delete from `R_0` vertices for which
`|q_v-1/2|>1/(20d)`. Since `M >= N/3`, at most `1200 kappa^2 d^2` vertices are deleted. Let `R` be the remaining set and `n=|R|`. Hypothesis (T), for `d>=2`, ensures

\[
 M,n\ge N/3,\qquad
 q_-:=\tfrac12(1-\tfrac1{10d})\le q_v\le
 q_+:=\tfrac12(1+\tfrac1{10d}).                              \tag{2}
\]

There is no need to prune row degrees on `L`.

Let `D` be the column-centred rectangular matrix

\[
 D=A[L,R]-\mathbf1 q^T
   =(I-J_M/M)B_0[L,R].
\]

Then

\[
 \|D\|_{op}\le\kappa\sqrt N,\qquad
 \|D\|_F^2=M\sum_{v\in R}q_v(1-q_v)\le Mn/4.                \tag{3}
\]

## 3. An exact all-orders nonnegative Gram decomposition

This lemma is stated separately because it is useful beyond the cube.

### Lemma 2 (common-neighbourhood variance, exact identity)

Let `A` be any zero-one `M` by `n` matrix. Write

\[
 q_v=M^{-1}\sum_i A_{iv},\quad D=A-\mathbf1q^T,\quad
 R=D^TD/M,\quad c_{vw}=M^{-1}\sum_i A_{iv}A_{iw}.
\]

Choose `d` independent uniform rows `X_1,...,X_d` and let

\[
 Z=\sum_v\prod_{j=1}^d A_{X_jv}.
\]

Thus `Z` is the number of common neighbours, with repeated selected rows allowed. Its mean is `mu=sum_v q_v^d`. For `d>=2`, put `a_v=q_v^{d-1}`. Then

\[
\boxed{
 \operatorname{Var}Z
 =d\,a^TRa+
 \sum_{v,w}R_{vw}^{\,2}
 \sum_{i=0}^{d-2}(i+1)(q_vq_w)^i c_{vw}^{\,d-2-i}.
}                                                               \tag{4}
\]

**Every displayed summand, including the whole Gram term `a^TRa`, is nonnegative.** The individual entries `R_vw` need not be nonnegative.

**Proof.** We have `c_vw=q_vq_w+R_vw` and

\[
 E Z^2=\sum_{v,w}c_{vw}^{\,d},\qquad
 (E Z)^2=\sum_{v,w}(q_vq_w)^d.
\]

For nonnegative `x,a`, the exact polynomial identity

\[
 x^d-a^d-da^{d-1}(x-a)
 =(x-a)^2\sum_{i=0}^{d-2}(i+1)a^i x^{d-2-i}                  \tag{5}
\]

applies even when `x-a<0`. Summing it with `x=c_vw`, `a=q_vq_w` gives (4). The linear term is `d a^T R a`, and `R=D^TD/M` is positive semidefinite. □

### Lemma 3 (spectral variance bound at the endpoint)

For the rectangular host in Section 2, for every `d>=2`, put `mu_0=n/2^d`. Then

\[
 \frac9{10}\mu_0\le E Z\le\frac{10}{9}\mu_0,
 \qquad
 \boxed{\operatorname{Var} Z\le25\kappa^2\mu_0.}             \tag{6}
\]

In particular, writing `C=N/2^d`,

\[
 \boxed{\Pr(Z<\mu_0/2)\le500\kappa^2/C.}                   \tag{7}
\]

**Proof.** Bernoulli's inequality and `exp(1/10)<10/9` give

\[
 q_-^d\ge\frac9{10}\,2^{-d},\qquad
 q_+^d\le\frac{10}{9}\,2^{-d},
\]

which prove the mean bounds. By (3),

\[
 \|R\|_{op}\le\kappa^2N/M\le3\kappa^2,
 \qquad
 \sum_{v,w}R_{vw}^2
 \le\frac{\|D\|_{op}^2\|D\|_F^2}{M^2}
 \le\frac34\kappa^2 n.                                    \tag{8}
\]

In (4), `0<=c_vw<=q_+`, `0<=q_vq_w<=q_+^2`, and `q_+<=11/20`. Therefore

\[
 \sum_{i=0}^{d-2}(i+1)(q_vq_w)^i c_{vw}^{d-2-i}
 \le\frac{q_+^{d-2}}{(1-q_+)^2}
 \le20q_+^d.                                                \tag{9}
\]

Here `q_+>=1/2` is used only for the numerical last bound. The first term in (4) is at most `3 kappa^2 n d q_+^{2d-2}`. Since

\[
 q_+^{2d-2}\le5\,4^{-d},\qquad d2^{-d}\le1/2,
\]

this is at most `(15/2) kappa^2 mu_0`. Equations (8)--(9) bound the remaining term by `(50/3) kappa^2 mu_0`. Their sum is less than `25 kappa^2 mu_0`.

The distance from the mean to `mu_0/2` is at least `2mu_0/5`. Chebyshev gives at most `(625/4) kappa^2/mu_0`. Since `n>=N/3`, this is less than `500 kappa^2/C`. □

This uses a whole Gram contribution and a nonnegative Taylor remainder. It does not throw away the signs of contracted spectral cores and does not assert a false uniform bound for arbitrary signed graph products.

## 4. Dense distance-two supports in the cube

For `T subset V(Q_d)`, let `e_2(T)` count unordered pairs in `T` at Hamming distance two.

### Lemma 4 (distance-two support sparsity)

For every nonempty `T subset V(Q_d)`,

\[
 \boxed{e_2(T)\le\frac{d-1}{2}|T|\log_2|T|.}                \tag{10}
\]

In particular, if `T` lies in one cube parity class, it contains a set `S` whose cube neighbourhoods are pairwise disjoint and

\[
 \boxed{|S|\ge \frac{|T|}{1+(d-1)\log_2|T|}.}              \tag{11}
\]

**Proof.** Induct on `d`; the assertion for `d=1` is immediate. Split `T` by its last coordinate into sets of sizes `t_0,t_1`, viewed in `Q_{d-1}`, and put `t=t_0+t_1`. Distance-two pairs crossing the split number at most `(d-1)min(t_0,t_1)`. The induction hypothesis gives

\[
 e_2(T)\le\frac{d-2}{2}\sum_i t_i\log_2t_i
                 +(d-1)\min(t_0,t_1).
\]

With `0 log 0=0`, binary entropy satisfies

\[
 t\log_2t-\sum_i t_i\log_2t_i\ge2\min(t_0,t_1).
\]

Substitution proves (10), since `sum_i t_i log_2 t_i>=0`.

On a single parity class, two distinct vertices have intersecting cube neighbourhoods exactly when they are at distance two. The graph of these conflicts on `T` has average degree at most `(d-1)log_2|T|`. Every graph on `t` vertices and average degree `a` has an independent set of size at least `t/(a+1)`: order its vertices randomly, take those preceding all their neighbours, and use `sum_v 1/(deg(v)+1)>=t/(a+1)`. This proves (11). □

The bound is useful for sets of size polynomial in `d`, whereas the maximum conflict degree `binom(d,2)` alone would lose a further logarithmic factor in the following argument.

## 5. A variable local lemma with an explicit load bound

We use the usual finite asymmetric Lovasz local lemma: for events with a dependency graph, if numbers `0<=x_i<1` satisfy

\[
 \Pr(E_i)\le x_i\prod_{j\sim i}(1-x_j),
\]

then their simultaneous avoidance has positive probability. Independence outside the neighbourhood, required in the standard inductive proof, holds for events depending on disjoint sets of independent variables.

A convenient sufficient version is the following. Give event `E_i` a set `V_i` of determining variables, a probability upper bound `b_i`, and put

\[
 x_i=b_i e^{\alpha|V_i|}.
\]

If `x_i<1` and, for every variable `u`,

\[
 \sum_{i:u\in V_i}-\log(1-x_i)\le\alpha,                    \tag{12}
\]

the local lemma applies. Indeed, the product over neighbours of `E_i` is at least `exp(-alpha |V_i|)` by summing (12) over its variables. Overcounting events only weakens this lower bound.

## 6. The simultaneous good-list, injection, and overload construction

Let `X,Y` be the cube parity classes, each of size `m=h/2`. Choose independent uniform variables `F_x in L`, `x in X`. For `y in Y` define the candidate list

\[
 L_y=\bigcap_{x\in N_{Q_d}(y)}(N_{G_0}(F_x)\cap R).
\]

Write `C=N/h`, and set

\[
 k=\lceil8\log C+20\rceil,\qquad \alpha=1/d.
\]

We forbid three sorts of event.

1. **Small list:** for each `y`, `|L_y|<n/(2h)`. It involves `d` variables and has probability at most `500 kappa^2/C`, by Lemma 3.
2. **Collision on `X`:** for each pair `x!=x'`, `F_x=F_x'`. It involves two variables and has probability `1/M`.
3. **Disjoint-star overload witness:** for each `v in R` and `S subset Y` of size `k` with pairwise disjoint cube neighbourhoods, require `v in L_y` for every `y in S`. It involves exactly `dk` variables and has probability `q_v^{dk}`. If there is no such `S`, this family of events is empty.

Take the corresponding `x_i=b_i exp(|V_i|/d)` in (12). We bound their sum at any fixed source variable `x`.

* There are `d` events of the first kind, with total at most
  `1500 kappa^2 d/C`.
* The collision events have total at most `5/C`, using `d>=2`, `m=h/2`, and `M>=N/3`.
* For the third kind, at most `d binom(m-1,k-1)` choices of `S` use this variable. Also `q_v^d<=exp(1/10)/h`. Summing over `v` gives at most
  \[
  2Cd\,\frac{2^k}{(k-1)!}\le2Cd\,2^{-k}.                  \tag{13}
  \]
  The last inequality uses `(k-1)!>=4^k` for `k>=20`, checked at `20` and then preserved inductively. The count is zero if `k>m`.

Thus the total load at a variable is at most

\[
 L_*:=1500\kappa^2d/C+5/C+2Cd\,2^{-k}.                       \tag{14}
\]

Under (T), `C>=10^6 kappa^2 d^2`, `kappa>=4`, and `C>=d^2`. Since

\[
 2^{-k}\le2^{-20}C^{-5},
\]

(14) gives

\[
 L_*<\frac1{100d}.                                         \tag{15}
\]

Every `x_i` is at most the load at any variable in its nonempty support, so is less than `1/2`. Using `-log(1-x_i)<=2x_i`, (15) proves (12), with substantial room to spare. The local lemma gives an assignment simultaneously avoiding all three sorts of event.

For this assignment:

* `F:X -> L` is injective;
* every candidate list has size at least `ell:=n/(2h)`;
* for every `v in R`, the set
  \[
  T_v=\{y\in Y:v\in L_y\}
  \]
  contains no `k` vertices with disjoint cube neighbourhoods.

## 7. Hall's condition and verification of the constants

We claim that `|T_v|<ell` for every `v`. First note

\[
 \ell\ge C/6,
 \qquad
 \frac{C}{6(1+d\log_2 C)}>k.                               \tag{16}
\]

Here is a dimension-uniform verification of the second inequality. The present lower bound on `C` implies `k<=10 log C` and `C>=2`. Hence

\[
 6k(1+d\log_2C)
 \le\frac{120}{\log2}\,d(\log C)^2
 <174d(\log C)^2
 \le522d\sqrt C
 < C.                                                       \tag{17}
\]

We used the elementary inequality `(log C)^2<=3 sqrt(C)` for `C>=1` (its ratio has maximum `16/e^2<3`), and
`sqrt(C)>=1000 kappa d>=4000d`.

For `t>=e`, the function `t/(1+(d-1)log_2 t)` is increasing. If `|T_v|>=ell`, Lemma 4 would give an independent family of neighbourhoods of size at least

\[
 \frac{\ell}{1+(d-1)\log_2\ell}
 \ge\frac{C}{6(1+d\log_2 C)}>k,
\]

because `C/6<=ell<=C/2` and `ell>=e`. This contradicts avoidance of the third kind of event. Thus `|T_v|<ell`.

Form the bipartite incidence graph with rows `Y`, columns `R`, and edges `yv` exactly when `v in L_y`. Its minimum row degree is at least `ell` and its maximum column degree is less than `ell`. Counting incidences from any subset `S subset Y` yields `|N(S)|>=|S|`. Hall's theorem supplies a matching saturating `Y`.

Map `Y` by this matching. Its images are distinct and lie in `R`, disjoint from the distinct images of `X` in `L`. By the definition of the lists, every cube edge maps to an edge of `G_0`, hence of `G`. This is an ordinary injective cube embedding. The case `d=1` follows directly from the positive density. This completes the proof of (T). □

## 8. Exactly what is still missing

The all-orders variance lemma has a lower-tail consequence of order

\[
 \Pr(\text{small common neighbourhood})\lesssim K^2h/N.
\]

A small-list event uses `d` variables, and each variable belongs to `d` such events. In the local lemma, this produces the requirement

\[
 \boxed{K^2d^2h/N\ll1.}                                    \tag{18}
\]

The distance-two support bound removes a further logarithmic loss from the overload/Hall portion; it does **not** remove (18). Also, the sufficient bounded-column certificate used here requires (16), which is not dimension-free at fixed `C`. Direct Hall-core control could be weaker than that certificate, but is not proved here. Taking a larger constant depending only on `K` cannot absorb `d^2` for unbounded `d`.

No signed regrouped polymer family is constructed here whose negative load is bounded uniformly when `N/h` is constant. The exact activity contraction and the whole-star resummation in the companion file remain compatible with that goal, but do not prove it for overlapping cube cores.

Thus the positive checkpoint is a proved `O_K(d^2 2^d)` spectral embedding theorem, based on a genuinely signed/nonnegative Gram regrouping valid for every `d`. The constant-multiplier spectral benchmark and the arbitrary-colouring Ramsey conjecture both remain unresolved by this work.
