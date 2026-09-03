# Anchor capacity renewal: a complete punctured-state theorem

## Status and scope

**The constant-multiplier full spectral cube embedding theorem is not proved here.**
The capacity-renewal investigation did not produce an invariant that can be
iterated until at most one odd label is anchored. Neither the original Ramsey
statement nor its negation is proved. `Submission/Spec.lean` is unchanged.

The previously unchecked **punctured-state lemma is proved in full below**.
In particular, the distributional step is not assumed: a uniform permutation
conditioned to avoid explicitly defined bad canonical events satisfies a proved
bound for **every partial injection**, including a full injection. A
nonnegative-polynomial comparison and a proved read-`d` inequality then control
all actual row loads in one state. No averaged-state matching is used.

There is also a deterministic, dimension-uniform choice of **exactly `2t`
syndrome classes**: every even label has between `t` and `2t` neighbors in their
union, whose size is at most `2tm/d`.

The proof and the endpoint distinction are self-contained. The companion audit
is `check_cube_anchor_capacity_renewal.py`; its recorded output is
`CubeAnchorCapacityRenewalVerification.txt`. This is a paper proof with
executable finite audits, not a Lean formalization.

---

## 1. The theorem actually established

Let the bipartite host have disjoint parts `L,B`, both of size `N`, and zero-one
adjacency matrix `P`. Suppose, for `K >= 0`,

\[
 \|P-J/2\|_{\rm op}\le K\sqrt N.
\]

Let `X,Y` be the even and odd classes of the **original** cube `Q_d`, and put

\[
 m=2^{d-1},\quad C=N/m,\quad \kappa=K^2+1,
 \qquad C\ge 10^4\kappa.
\]

Fix an anchor `b_* in B` with `U=N_P(b_*)` of size at least `N/3`. Set

\[
 t=\left\lceil3\log_2(d+1)+20\right\rceil,
 \qquad 2t<d.                                                 \tag{1}
\]

Let `T subset Y` be **any** set such that every `x in X` has at least `t`
neighbors in `T`. Write

\[
 J_0=Y\setminus T,\qquad S_x=N_{Q_d}(x)\cap J_0,
 \qquad h_x=|S_x|\le H:=d-t.
\]

### Theorem 1 (punctured state, including actual capacity)

There are a row set `A subset U`, `M=|A| >= N/4`, and an injection

\[
 g:J_0\longrightarrow B\setminus\{b_*\}
\]

such that the **actual** domains

\[
 D_x=A\cap\bigcap_{y\in S_x}N_P(g(y))
\]

satisfy, simultaneously,

\[
 \boxed{|D_x|\ge {M\over2}\,2^{-h_x}\quad(x\in X),}
 \qquad
 \boxed{\max_{a\in A}\sum_{x:a\in D_x}{1\over|D_x|}< {1\over64}.}  \tag{2}
\]

In fact, the set `A` can be chosen before `T` is specified. The remaining
column pool and the injection are allowed to depend on `T`.

Consequently the domains admit a simultaneous matching saturating `X`. Thus
`Q_d-T` embeds injectively, with its even images in `A` and odd images avoiding
`b_*`. Mapping all of `T` to the anchor gives a full cube homomorphism whose
only possible collisions are among these `|T|` odd labels.

The proof also works for a bipartite target with at most `m` vertices on each
side, maximum degree at most `d`, and the same bound `h_x <= d-t`. Only those
size and incidence bounds are used before the syndrome construction.

The condition `2t<d` is a restriction on the theorem, not an omitted
small-dimension argument for the full embedding problem. Its first admissible
dimension is 79 (dimension 80 fails the condition because of the ceiling;
every use below retains the condition itself). For the elementary inequalities
below, it suffices to note that it implies `d>=41`, and hence

\[
 m\ge24d^2,\quad N\ge240000\kappa d^2.                         \tag{3}
\]

Indeed, `2^{40}>24*41^2`, and the ratio `2^{d-1}/d^2` increases for `d>=3`.
An anchor of the specified size also exists automatically: the total number
of host edges is at least `N^2/2-K N^{3/2}`, and (3) implies `N>=36K^2`.
Some column therefore has degree at least `N/3`. The theorem works for any
anchor with that degree bound.

---

## 2. Degree pruning and a uniform small-domain probability

Put `B_0=B\{b_*}` and `n_0=N-1`. For a host row `a`, let

\[
 q_a={|N_P(a)\cap B_0|\over n_0}.
\]

The spectral hypothesis, restricted to these columns, implies

\[
 \sum_{a\in L}(q_a-1/2)^2\le {K^2N\over n_0}.
\]

Delete from `U` every row with `|q_a-1/2|>1/(100d)`, and call the remaining
set `A`. At most

\[
 10^4K^2d^2N/n_0\le 20000K^2d^2\le N/12
\]

rows are deleted, by (3). Therefore `M=|A|>=N/4` and, on `A`,

\[
 q_-={1\over2}\left(1-{1\over50d}\right)
 \le q_a\le
 q_+={1\over2}\left(1+{1\over50d}\right).                    \tag{4}
\]

### 2.1 All-orders variance, with its signed Gram term retained

Choose `h` independent uniform columns of `B_0`, with replacement, where
`1<=h<=d`, and let `Z_h` be their common-neighborhood size in `A`.
Put

\[
 D=P[A,B_0]-q\mathbf1^T,
 \quad R=DD^T/n_0,
 \quad c_{ab}=n_0^{-1}\sum_{v\in B_0}P_{av}P_{bv}.
\]

Right multiplication by `I-J/n_0` shows that

\[
 \|D\|\le K\sqrt N,
 \quad\|R\|\le2K^2,
 \quad\sum_{a,b}R_{ab}^2
 \le\|R\|\operatorname{tr}R\le K^2M/2.                    \tag{5}
\]

Here `tr R=sum_a q_a(1-q_a)<=M/4`. Also `c_ab=q_a q_b+R_ab`.
For `h>=2`, writing `v_a=q_a^{h-1}`, the exact identity is

\[
 \operatorname{Var}Z_h
 =h\,v^TRv+
 \sum_{a,b}R_{ab}^2
 \sum_{i=0}^{h-2}(i+1)(q_aq_b)^i c_{ab}^{h-2-i}.              \tag{6}
\]

To verify it, use `E Z_h=sum_a q_a^h`, `E Z_h^2=sum_ab c_ab^h`, and

\[
 z^h-u^h-hu^{h-1}(z-u)
 =(z-u)^2\sum_{i=0}^{h-2}(i+1)u^iz^{h-2-i}.
\]

The whole first term in (6) is nonnegative because `R` is positive
semidefinite. Every remainder term is nonnegative; individual entries of `R`
need not be. No estimate of individual signed diagrams is involved.

Put `mu_0=M2^{-h}`. From (4),

\[
 {49\over50}\mu_0\le E Z_h\le e^{1/50}\mu_0.
\]

For completeness, `q_+<=0.51`, and

\[
 \sum_{i=0}^{h-2}(i+1)(q_aq_b)^ic_{ab}^{h-2-i}
 \le {q_+^{h-2}\over(1-q_+)^2}\le20q_+^h,
 \qquad q_+^{2h-2}<5\,4^{-h}.
\]

Together with (5) and `h2^{-h}<=1/2`, these give

\[
 \operatorname{Var}Z_h\le25K^2\mu_0.                          \tag{7}
\]

For `h=1`, the variance is `1^T R1<=2K^2M`, which also satisfies (7).
For `h=0`, the domain is deterministically `A` and no bad event is needed.
Chebyshev, using a gap of at least `(12/25)mu_0` to `mu_0/2`, gives

\[
 \Pr(Z_h<\mu_0/2)\le125K^2\,2^h/M.                           \tag{8}
\]

### 2.2 Pass to distinct columns, with the normalization paid

For `h<=d`, independent sampling has distinct columns with probability at
least `1-h(h-1)/(2n_0)>=1/2`, by (3). Conditioning on that event is exactly
uniform injection sampling. Hence, for every `x`, the fraction of injections
`phi:S_x -> B_0` for which

\[
 \left|A\cap\bigcap_{y\in S_x}N_P(\phi(y))\right|
       <(M/2)2^{-h_x}                                       \tag{9}
\]

is at most

\[
 250K^2 2^{h_x}/M\le {2000K^2\over C2^t}\le
 p:={2000\kappa\over C2^t}.
\]

In particular,

\[
 \boxed{p\le {1\over5\,2^t}
       \le {1\over5\,2^{20}(d+1)^3}.}                        \tag{10}
\]

These are probabilities for the original row-pruned matrix and the specified
random injection; they are not assertions about adaptively frozen domains.

---

## 3. Prune range incidences before applying the permutation local lemma

A **bad canonical event** indexed by `(x,phi)` specifies the injection
`phi:S_x -> B_0` and satisfies (9). Its probability in a uniform permutation
of `n_0` positions is `1/(n_0)_{h_x}`; `(n)_h` denotes the falling factorial.
Use dummy source positions for the unused host positions.

For `b in B_0`, define the *original* range-incidence mass

\[
 w(b)=\sum_x\sum_{\substack{\phi\text{ bad for }x\\
                                  b\in\operatorname{im}\phi}}
                  {1\over(n_0)_{h_x}}.
\]

There are no bad events with `h_x=0`, and

\[
 \sum_b w(b)\le mdp.
\]

Delete columns with `w(b)>100md^2p/n_0`. Write the remaining set as `B_1`,
its size as `n`, and the number deleted as `r`. Then

\[
 r<{n_0\over100d},\qquad n\ge(1-1/(100d))n_0.                 \tag{11}
\]

Keep just the bad canonical events with range contained in `B_1`, and give
such an event its **new**, correct probability `b_E=1/(n)_{h_x}`. For
`h<=d`, (3) implies `n-h+1>=n_0/2`, so

\[
 {(n_0)_h\over(n)_h}
 \le\exp\left({hr\over n-h+1}\right)
 \le e^{1/50}<2.                                             \tag{12}
\]

Consequently the total `b_E` mass incident to a specified source position is
at most `2dp`, and the mass incident to a specified range point is at most

\[
 200md^2p/n_0\le400d^2p/C.                                   \tag{13}
\]

The factor `d` in the range-pruning threshold is intentional. Deleting a
constant fraction of columns instead would destroy the required
`1/2+O(1/d)` row-degree control.

---

## 4. A self-contained conditional permutation bound

This section supplies the entire distributional argument; no output-law
proposition for a resampling algorithm is assumed.

### 4.1 The required negative-dependency fact

A canonical event in a uniform permutation prescribes a partial bijection.
Join two canonical events if their prescribed source sets intersect **or**
their prescribed range sets intersect. For any event `E` and any family
`F` of its nonneighbors,

\[
 \Pr(E\mid\text{avoid all of }F)\le\Pr(E)                    \tag{14}
\]

whenever the conditioning event has positive probability.

**Proof.** Starting with a uniform permutation, enforce the prescribed pairs
of `E` successively. To enforce `u -> b`, swap the current image at `u` with
the image at the current preimage of `b`. Previously enforced pairs are not
disturbed. At each step the output is uniform conditional on the pairs
already enforced: each permissible output has exactly the same number of
preimages under the swap operation. Thus the final permutation is uniform
conditional on `E`.

A canonical event disjoint from both the source and the range of `E`, if
true before this procedure, remains true. Its source positions are not
positions of `E`; and while it is true, none can be a preimage of a range
point of `E`. So no swap changes its required images. Therefore enforcing
`E` cannot turn a permutation with some event in `F` true into one avoiding
all of `F`. It follows that
`Pr(avoid F | E)<=Pr(avoid F)`. Bayes' formula proves (14). QED.

The same statement holds for an additional canonical *query* event, whether
or not it belongs to the bad family. Extra edges in this graph are harmless.

### 4.2 Conditional local-lemma estimate, proved here

Suppose a finite event family has (14), and numbers `0<=z_E<1` satisfy

\[
 \Pr(E)\le z_E\prod_{F\sim E}(1-z_F).                         \tag{15}
\]

Then simultaneous avoidance has positive probability. In addition, for any
canonical query event `Q`, under the uniform law conditioned on avoiding all
bad events,

\[
 \Pr_*(Q)\le\Pr(Q)\prod_{E\sim Q}(1-z_E)^{-1}.               \tag{16}
\]

Here is the standard short induction, included to specify all conditioning.
For a bad event `E` and a set `S` of other bad events, induct on `|S|` to prove
`Pr(E | avoid S)<=z_E`. Split `S` into nonneighbors `S_0` and neighbors `S_1`.
The numerator is at most `Pr(E | avoid S_0)<=Pr(E)` by (14). The denominator
`Pr(avoid S_1 | avoid S_0)` is at least
`product_{F in S_1}(1-z_F)`, by exposing those avoidances successively and
using the induction hypothesis. Equation (15) completes the induction.
All such avoidance probabilities are positive by the same chain rule. For a
query, use (14) on its nonneighbors and this already proved denominator
bound on its neighbors, giving (16).

### 4.3 Apply it to the punctured target, for every query size

Choose a uniform permutation on `n` positions, with `J_0` among the real
source positions, and put `z_E=2b_E`. Since `n>=4` and every bad event has
nonempty support, `z_E<=1/2`. From (13) and its source counterpart, and using
`-log(1-z)<=2z`, the logarithmic incidence budgets are

\[
 \begin{array}{ll}
  \text{at a source position:}&8dp,\\
  \text{at a range point:}&1600d^2p/C.
 \end{array}
\]

A query fixing `k` images therefore has total adjacent logarithmic weight at
most `k ell`, where

\[
 \ell=8dp+1600d^2p/C\le {1\over100d}.                         \tag{17}
\]

Indeed, (10) and `C>=10000` give

\[
 d\ell\le {8/5+1600/(5\cdot10000)\over2^{20}}
            <{2\over2^{20}}<{1\over100}.
\]

For a bad event, `k=h_x<=d`, and its neighbor product is at least
`e^{-h_x ell}>=e^{-1/100}>1/2`. Thus (15) holds with `z_E=2b_E`.
Let `P_*` be the law of the restriction to `J_0` of this permutation,
conditioned on avoiding all bad events. It exists, is supported on actual
injections, and every domain satisfies the first part of (2).

Most importantly, (16)-(17) give, for **every** `W subset J_0` and every
specified injection `psi:W -> B_1`,

\[
 \boxed{\Pr_*(g|_W=\psi)
       \le {\exp(|W|/(100d))\over(n)_{|W|}}.}                \tag{18}
\]

There is no restriction such as `|W|=O(d)` in (18). The full-injection case
is included. We will sum this bound over injections into a fixed row
neighborhood, retaining the falling factorial in the numerator; replacing
it by `n^{|W|}` would lose the useful estimate.

---

## 5. Turn the conditional law into an actual load bound

Fix `a in A` and put

\[
 V_a=N_P(a)\cap B_1,\quad s_a=|V_a|,\quad q'_a=s_a/n,
 \quad \theta_a=q'_a e^{1/(100d)}.
\]

Degree pruning and (11) imply

\[
 q'_a\le{q_+\over1-1/(100d)},\qquad
 \log(2q'_a)
 \le {1\over50d}+{1\over100d-1}<{1\over25d}.
\]

Thus

\[
 0\le\theta_a\le {1\over2}e^{1/(20d)}<1.                    \tag{19}
\]

Sum (18) over injections from a set `W` of `k` real source positions into
`V_a`. With the value zero when `s_a<k`, this gives

\[
 \Pr_*(g(W)\subset V_a)
 \le e^{k/(100d)}{(s_a)_k\over(n)_k}
 \le\theta_a^k.                                             \tag{20}
\]

The last inequality is the exact finite-population comparison
`(s)_k/(n)_k <= (s/n)^k`. No independent-column law for the chosen `g` is
being claimed.

### 5.1 Nonnegative-polynomial domination

Put

\[
 I_x(a)=\mathbf1[g(S_x)\subset V_a],\qquad
 u_x={2^{h_x+1}\over M},\qquad
 L_a=\sum_x u_x I_x(a).
\]

The first part of (2) ensures that the actual normalized load at `a` is at
most `L_a`.

Let independent Bernoulli variables `xi_y`, `y in J_0`, have parameter
`theta_a`, and put `I'_x=product_{y in S_x} xi_y` (empty product one).
For any family `F subset X`, equation (20), applied to `union_{x in F} S_x`,
gives

\[
 E_*\prod_{x\in F}I_x(a)\le E\prod_{x\in F}I'_x.             \tag{21}
\]

For any `v>=0`, expand the finite product

\[
 e^{vL_a}=\prod_x\bigl[1+(e^{v u_x}-1)I_x(a)\bigr].
\]

Every coefficient is nonnegative, so (21) proves

\[
 E_* e^{vL_a}\le E\exp\left(v\sum_xu_xI'_x\right).           \tag{22}
\]

This is a comparison for a particular positive polynomial, not a
replacement of the conditional law by an unconditioned random law.

### 5.2 Read-`d` exponential moment, including its proof

If nonnegative functions `F_i` of independent variables each read a set of
variables, and each variable occurs in at most `d` functions, then

\[
 E\prod_i F_i\le\prod_i(E F_i^d)^{1/d}.                      \tag{23}
\]

To prove it, integrate one variable first. Apply Holder with exponent `d` to
the at most `d` functions that use it, padding by constant functions one.
Replace each such function by its conditional `L^d` norm in that variable.
Now induct on the remaining variables. The final `d`-th moment of a
replacement is the full `d`-th moment of the original function. This proves
(23), also for constant functions.

Each odd cube variable occurs in at most `d` sets `S_x`. Apply (23) to the
right side of (22). Since `Pr(I'_x=1)=theta_a^{h_x}`,

\[
 \log E_*e^{vL_a}
 \le {1\over d}\sum_x\theta_a^{h_x}(e^{vd u_x}-1).
\]

Set

\[
 W_0={2^{H+1}\over M}\le{16\over C2^t},\qquad
 \mu_a=\sum_xu_x\theta_a^{h_x}
 \le {2e^{1/20}m\over M}<{12\over C}.                       \tag{24}
\]

As `0<u_x<=W_0`, convexity gives

\[
 \boxed{\log E_*e^{vL_a}
 \le {\mu_a\over dW_0}(e^{vdW_0}-1).}                       \tag{25}
\]

Use `v=1/(dW_0)` and threshold `rho=1/64`. Since `e-1<2`, `C>=10000`,

\[
 \rho-(e-1)\mu_a\ge {1\over64}-{24\over C}>{1\over128}.
\]

Chernoff's bound and (24) yield

\[
 \Pr_*(L_a\ge1/64)
 \le\exp\left(-{1\over128dW_0}\right)
 \le\exp\left(-{C2^t\over2048d}\right).                     \tag{26}
\]

The union bound over all `M<=N` rows is strictly below one. Explicitly,

\[
 {C2^t\over2048d}\ge512C(d+1)^3/d\ge512Cd^2,
 \quad \log N=\log C+(d-1)\log2\le C+d\le2Cd^2.
\]

Thus some single injection in the support of `P_*` satisfies all the lower
domain bounds and every strict load bound in (2). This proves Theorem 1.

### 5.3 Hall is applied to that one state

For any `F subset X`, sum its uniform domain weights over its actual union:

\[
 |F|=\sum_{a\in\cup_{x\in F}D_x}
                  \sum_{\substack{x\in F\\a\in D_x}}{1\over|D_x|}
 \le {1\over64}\left|\bigcup_{x\in F}D_x\right|.
\]

In particular Hall's condition holds. Its matching is a simultaneous
injection of all even labels in the already chosen domain system. The
anchor adjacency and the odd injection then give the stated homomorphism.
The proof never selects different even matchings for different Hall sets.

---

## 6. Exactly `2t` deterministic syndrome classes suffice

Let `r=ceil(log_2 d)` and `q=2^r`. Label coordinate `i`, for `0<=i<d`, by
its binary vector `v_i in F_2^r`; in particular `v_0=0`. Define

\[
 \sigma(z)=\sum_{i=0}^{d-1}z_i v_i.
\]

Let `H_0` be the hyperplane of vectors whose highest bit is zero.
Because `q/2<d<=q`, the coordinate-label set contains the whole of `H_0`.
Choose any `t`-element set `R_0 subset H_0`, possible since `t<d/2<=q/2`,
and let `e` be the highest-bit vector. Put

\[
 S=R_0\cup(R_0+e),\qquad T=\{y\in Y:\sigma(y)\in S\}.       \tag{27}
\]

For an even label `x`, its `d` neighbor syndromes are the **distinct**
vectors `sigma(x)+v_i`. They contain the whole coset `sigma(x)+H_0`.
The set `S` has exactly `t` points in each coset of `H_0`, so

\[
 \boxed{t\le |N_{Q_d}(x)\cap T|\le2t<d\quad(x\in X).}       \tag{28}
\]

The map `(parity,sigma):F_2^d -> F_2^{r+1}` is onto: the coordinate of label
zero supplies `(1,0)`, and the coordinates labelled by the `r` basis vectors
supply `(1,e_j)`. These coordinates exist since `d>q/2`. Their sums span
`(0,e_j)`. Consequently each odd syndrome class has exactly `m/q` labels,
and

\[
 \boxed{|T|={2tm\over q}\le{2tm\over d}.}                    \tag{29}
\]

Two different odd labels in one class cannot have distance two: the
syndrome of their difference would be `v_i+v_j != 0`. Their distance is
therefore at least four. Equivalently, each even label meets a class at
most once, as also follows directly from its distinct neighbor syndromes.

This is a deterministic construction, not a probabilistic covering with
unchecked constants. Double-counting the edges from `T` shows that any
such cover has `d|T|>=tm`, so (29) is within a factor two of the minimum
possible size. When `d=q`, one may instead take just `t` classes, attaining
`|T|=tm/d`, since every even label then meets every class exactly once.

Only original odd labels have been deleted. No quotient or alternative
product graph has replaced the cube, and every edge in the partial
embedding is an original coordinate edge.

---

## 7. What the renewal attempt does, and does not, justify

The positive result here is the complete construction of a highly slack,
**actual** punctured state. Its consequence is an injective `Q_d-T` with
`|T|<=2tm/d` and a full homomorphism having only anchor collisions. It is
not a full embedding at a constant multiplier.

The renewal attempt allowed arbitrary fractional matching weights on the
current domains (rather than fixing their uniform weights), global even
rematching, and unfreezing old odd batches. This does not justify carrying
(18) through another conditioning or through an arbitrary reconfigured
state. The proof above gives (18) for its specified law only. Likewise,
freeing constraints enlarges domains but says nothing by itself about the
capacities after imposing all the new constraints again.

Quantitatively, the proved local-lemma budget depends on the common
neighborhood reserve: replacing `t` by a remaining reserve `s` would replace
`p` in (10) by the available bound `2000 kappa/(C2^s)`. The sufficient
budget in (17) then has terms proportional to `d^2/2^s` and `d^3/(C2^s)`.
It is not bounded for fixed `C,s` as `d` grows. This diagnoses a loss in
this **proof**, not a lower bound or a counterexample to a renewed law.
No claim that maximum-entropy reweighting repairs that loss is made.

The saved deterministic batch lemma does apply to three syndrome classes:
`r_x<=3` and (2) give `Gamma<4^3/64=1`. Also its minimum initial domain is
at least `C2^t/16`, so

\[
 \Lambda\le {4096K^2Nd\over C2^t}<N-m
             \le N-|J_0|-|Z|.
\]

(The last inequality assumes `Z subset T`.) This gives actual sequential
odd augmentation and even rematching, exactly as proved there. But the
proof supplies no renewed `1/64` load certificate afterwards. Counting
this as a repeatedly available three-class gain would be invalid.

**Unresolved endpoint:** construct a reconfiguration or conditional law
that renews actual matching capacity and whose proved invariant survives
until at most one odd label remains anchored. Neither a full
constant-`C` spectral embedding nor a disproof is obtained here. In
particular no dimension dependence has been hidden inside `C`, and no
change to the original arbitrary-coloring specification is warranted.

---

## 8. Executable verification

Run from `/workspace/leanproject`:

```sh
python3 -u Submission/check_cube_anchor_capacity_renewal.py
```

The audit independently checks:

* the all-orders Gram identity against direct sampling, including `h=0,1`;
* the permutation forcing coupling, including its exact conditional output
  multiplicities and preservation of all nonneighbor canonical events;
* the conditional local-lemma bound on **all** partial injections in small
  permutation spaces, not just single-coordinate queries;
* finite-population, range-pruning, nonnegative-polynomial and read-`d`
  comparisons, with exact rational arithmetic where applicable;
* the theorem's constant budget and tail comparison, including dimensions
  too large to allocate `2^d` vertices;
* the deterministic syndrome construction and its exact fiber, distance,
  and neighbor-count properties;
* an actual partial-cube/anchor certificate and all five even-matching
  prefixes of a batch completion in an explicitly defined Hadamard host;
  the final `Q_5` has all 80 edges and 80 coordinate squares checked. This
  is a small-dimension implementation check, **not** an instance of the
  large-`d` theorem or a general completion argument. The saved JSON is
  independently replayed using GF(2) ranks to compute its domain sizes.

All audits passed. They include 3,840 exact Gram/direct-sampling cases,
267,548 conditional-LLL queries covering **all partial injections** in each
of 48 small instances, 308 exact read-`d` checks, and 35,112 constant-budget
checks in 2,926 admissible dimensions, up to `d=2^512+1`. The syndrome
checks include 92,844 explicitly enumerated even-neighbor cases and 7,936
shift cases with the actual theorem values of `t`.

The recorded results are in `CubeAnchorCapacityRenewalVerification.txt`;
the explicit images and prefix matchings are in
`CubeAnchorCapacityRenewalCertificates.json`. Finite checks supplement the
all-dimensional proof; they do not test the unresolved renewal assertion.

`Submission/Spec.lean` retains SHA-256
`9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b`.
