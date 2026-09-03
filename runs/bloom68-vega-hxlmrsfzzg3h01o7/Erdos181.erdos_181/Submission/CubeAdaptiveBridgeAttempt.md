# Adaptive bridge checkpoint: global certificates obtained, core-to-capacity implication not closed

## Outcome

**This attempt does not complete `R(Q_d)=O(2^d)`. It does not prove the requested global core lemma.** No absolute Ramsey constant is obtained.

The attempted route was

> optimize actual coherent partial block packings globally, dualize the conditional capacity problem without averaging away the boundary, and project a global obstruction to a literal low-waste host cut.

The first two operations can be made exact. The last implication is still missing. In particular, this report does **not** replace that implication by a statement about an arbitrary fixed boundary, an independent-domain model, or a new inverse-codegree dichotomy.

There are three proved, globally quantified certificate statements below:

1. **Unrestricted batch exchange.** A globally optimal packing satisfies an exact exchange inequality for *every* actual coherent replacement batch, including batches changing both outer parity classes. There is also an exact residual exponential-capacity inequality for equal-size exchanges.
2. **Conditional global capacity dual.** A finite flow LP simultaneously considers all eligible colours, boundaries, list choices, and actual embedding histories. It retains the conditional moment constraints separately at each history. Either it has a feasible adaptive flow, or it has a state-indexed potential/row-weight certificate. A feasible flow with the stated budgets produces a fully injective cube. Only positive-flow histories need support the kernels.
3. **Lossless host-cut thresholding.** The robust-cut constant has an exact nonlinear, vertex-potential variational formula. A potential violating its displayed inequality yields an actual pair `A,Z` violating the core condition, with **no rounding loss**.

These are certificate reductions, **not a capacity-existence theorem for robust cores**. The missing operation is to connect (1) or (2) to (3), while retaining the two-colour information. Section 8 records the full gap ledger.

The Hamming-ball boundary is included in the exchange accounting. Its size is `O(h/sqrt(d))`, but dropping it is not a valid augmentation when a maximum packing is only one block short.

No Lean file was changed. The mathematical statements here are paper proofs with finite audits, not newly Lean-formalized theorems.

---

## 1. Exact input and quantifiers

Put

\[
 h=2^d,\qquad D=\left\lfloor\frac{h}{16d}\right\rfloor,
 \qquad \alpha=\frac18,\qquad N=|U|,
\]

with `d>=1`. The input is an arbitrary red-blue complete graph on `U`, with `N>=C h`, satisfying, in **both** colours,

\[
 H^U_{c,D}(A,Z)+|Z|>\frac{|A|}{8},                         \tag{1.1}
\]

for every nonempty `A subset U` with `|A|<=N/2` and every `Z subset U\A`, where

\[
 H^U_{c,D}(A,Z)
 =|\{v\in A:\deg_c(v,U\setminus(A\cup Z))\ge D+1\}|.
\]

`D` will denote only this host-cut degree cap. The list-column load below is denoted `rho`; confusing the two parameters would change the problem.

The extraction in `CubeDirectRamseyProgress.md`, Theorem 3 and its constant-expansion specialization, really supplies this input. It retains the two pools, wastes at most `(h-2)/7`, and leaves a core of size at least `N_initial-8(h-2)/7`. Thus a theorem for all cores of order at least `C h` would give the Ramsey result after adding the displayed constant overhead. The extraction itself is not the missing step.

Fix a blocking

\[
 Q_d=Q_t\mathbin\square Q_k,\qquad t=d-k\ge1,\qquad b=2^k.
\]

The argument permits, for example, `k` growing like `log d`, and does not assume `k` is an absolute constant. All block maps are **labelled injective embeddings of the actual `Q_k`**. Coordinate labels are never replaced by arbitrary matching permutations.

A hypothetical countercolouring has no full packing in either colour, for **any** choice of boundary or host cut. Failure for one boundary, or even global failure in just one colour, is not the hypothesis needed for the Ramsey conclusion.

---

## 2. A genuine global rebuild invariant

### 2.1 The configuration space

For a colour `c`, let

\[
 \Omega_c=\{g:Q_k\hookrightarrow U:\text{every required edge has colour }c\}.
\]

A configuration is a pair `(x,g)` with `x in Q_t` and `g in Omega_c`. Two configurations `(x,g),(y,g')` are incompatible if at least one of the following holds:

* `x=y`;
* their host images intersect;
* `x` and `y` are adjacent in `Q_t`, and some edge `g(a)g'(a)` fails to have colour `c`.

A packing `P` is a set whose distinct configurations are pairwise compatible. Write `dom(P)` for its occupied outer positions and `im(P)` for its used host vertices. In particular, `|im(P)|=b|P|`.

This is an exact conflict-graph encoding, not a relaxation:

\[
 |P|=2^t\quad\Longleftrightarrow\quad
 (x,a)\longmapsto g_x(a)\text{ is a colour-}c\text{ injective }Q_d.
                                                               \tag{2.1}
\]

Internal edges come from `Omega_c`, outer edges are tested at the same label `a`, and incompatibility excludes collisions even between nonadjacent blocks.

Maximizing `|P|` over this entire finite space changes the host partition, the boundary, and both outer parity classes. It is not maximality under a bounded collection of moves.

### Theorem 2.1 — arbitrary-batch exchange

Let `P` maximize `|P|` in colour `c`. For **any** coherent packing `B`, put

\[
 C_P(B)=\{p\in P:p\text{ is incompatible with some }q\in B\}.
\]

Here a configuration conflicts with itself through the same-position rule. Then

\[
 \boxed{|B|\le |C_P(B)|.}                                  \tag{2.2}
\]

More generally, fix *before optimization* a finite host-set family `S_r`, nonnegative weights `lambda_r`, and `theta>0`. Set

\[
 R(P)=\sum_r\lambda_r e^{\theta|\operatorname{im}(P)\cap S_r|}.
\]

Choose `P` lexicographically maximizing `(|P|,-R(P))` over all actual packings. If `|B|=|C_P(B)|`, then, writing `C=C_P(B)`,

\[
 \boxed{
 \sum_r\lambda_r e^{\theta|\operatorname{im}(P)\cap S_r|}
 \left(e^{\theta(|\operatorname{im}(B)\cap S_r|
                    -|\operatorname{im}(C)\cap S_r|)}-1\right)
 \ge0.}                                                     \tag{2.3}
\]

**Proof.** The replacement

\[
 P'=(P\setminus C_P(B))\cup B
\]

is a coherent packing: all possible conflicts with the retained old blocks were included in `C_P(B)`. It has size `|P|-|C_P(B)|+|B|`, proving (2.2).

For an equal-size exchange, lexicographic optimality gives `R(P')>=R(P)`. The images of `B` are disjoint from the retained old images. Consequently, for every row set,

\[
 |\operatorname{im}(P')\cap S_r|
 =|\operatorname{im}(P)\cap S_r|
  -|\operatorname{im}(C)\cap S_r|
  +|\operatorname{im}(B)\cap S_r|.
\]

Substitution proves (2.3). This identity remains correct if new blocks reuse vertices of removed blocks. QED.

For completeness, maximizing `eta|P|-R(P)` instead gives the exact inequality

\[
 \eta(|B|-|C_P(B)|)\le R(P')-R(P)                           \tag{2.4}
\]

for every batch. No useful dimension-uniform value of `eta` is asserted.

**What this does and does not supply.** Equations (2.2)–(2.3) are valid for global rebuilds of unrestricted size. They correctly credit released capacity. They do not produce an improving batch. In (2.3), the sets and weights must stay fixed during optimization. Choosing new dual weights after reaching an optimum and optimizing again does not preserve a common monotone potential. Even taking the fixed set family to be all subsets of `U` does not solve that weight-selection problem.

---

## 3. The exact local moment dual, with actual blocks retained

This is the local constraint that must be nested inside a global argument.

At a history `s`, suppose the current block has available coordinate lists, and let `G_s` be the finite set of actual injective labelled `Q_k` embeddings in those lists. For every original row set `S_r`, prescribe a moment upper bound `B_{s,r}`. Define

\[
 a_{s,r}(g)=e^{\theta|\operatorname{im}(g)\cap S_r|}-B_{s,r}.
                                                               \tag{3.1}
\]

### Lemma 3.1 — weighted-hit alternative

If `G_s` is nonempty, the following are equivalent:

1. there is a distribution `mu_s` on `G_s` with `E_mu a_{s,r}<=0` for every row `r`;
2. for every nonnegative row-weight vector `lambda`, some **single actual block** `g in G_s` satisfies
   
   \[
   \sum_r\lambda_r e^{\theta|\operatorname{im}(g)\cap S_r|}
       \le\sum_r\lambda_r B_{s,r}.                          \tag{3.2}
   \]

If the distribution does not exist, there are `lambda_r>=0`, `sum lambda_r=1`, and `delta>0` such that

\[
 \sum_r\lambda_r a_{s,r}(g)\ge\delta\qquad(g\in G_s).      \tag{3.3}
\]

A feasible distribution can be chosen with at most `number_of_rows+1` blocks in its support. If `G_s` is empty, it is an empty-block obstruction, not a probability distribution.

**Proof.** Take the convex hull of the finite vectors `(a_{s,r}(g))_r`. A feasible kernel exists exactly when this compact convex set meets the nonpositive orthant. Separation from that orthant gives a nonnegative normal; normalization gives (3.3). Conversely, averaging (3.3) contradicts any feasible kernel. Equivalently, finite minimax gives

\[
 \min_{\mu\in\Delta(G_s)}\max_r E_\mu a_{s,r}
 =\max_{\lambda\in\Delta(\text{rows})}\min_{g\in G_s}
       \sum_r\lambda_r a_{s,r}(g).
\]

Caratheodory's theorem gives the support bound. QED.

The order of the quantifiers in (3.2) is important. One favorable block for each *individual* row is insufficient. On the other hand, the favorable block is allowed to depend on the whole nonnegative weight vector.

Nothing in this lemma estimates the minimum in (3.2) from the robust-cut hypothesis.

---

## 4. Globalizing the conditional capacity problem correctly

### 4.1 Roots: no prescribed boundary or host cut

Let `E_t,O_t` be the outer parity classes. A root `F` consists of:

* a colour `c` and a blocking `t+k=d`;
* an injection `f:E_t x Q_k -> U` giving actual internal colour-`c` cubes;
* a reservoir `V_F subset U\im(f)`;
* for every `r=(y,a) in O_t x Q_k`, a list `S_r` of the same even size `L`, satisfying
  
  \[
  S_{y,a}\subseteq V_F\cap\bigcap_{x\sim y}N_c(f(x,a));    \tag{4.1}
  \]
* a column-load bound
  
  \[
  |\{r:v\in S_r\}|\le\rho\qquad(v\in V_F),              \tag{4.2}
  \]
  where `rho` is a positive integer, `L>4e rho`, and
  
  \[
  \varepsilon_F=\frac h2
      \left(\frac{4e\rho}{L}\right)^{L/2}<1.             \tag{4.3}
  \]

The parameters may depend on the root. Put `theta=log(L/(4rho))` for that root.

The family of roots can contain **every** choice satisfying these conditions in both colours and every allowed `k`. It is finite: `L<=N` and `rho<L/(4e)` bound the integer parameters, and the subsets, embeddings, and blockings range over finite sets. There is no fixed host cut. All permutations of an outer-block processing order may also be included as root data.

Unlike the independent-coordinate version of the stopped greedy lemma, the theorem below does **not** need lists within a block to be disjoint. Every chosen block is already required to be injective; all row memberships are counted in (4.2).

Existence of an internal block packing is not being confused with existence of such a root. The large simultaneous lists and the load bound are additional, presently unproved, requirements for arbitrary cores. The root family is allowed to be empty; this is a real initialization gap.

### 4.2 Histories and safe stopping

At a root, process its odd outer positions in the specified order. A history consists of previous, mutually disjoint actual block embeddings, all satisfying (4.1).

* If the next block has a coordinate list with fewer than `L/2` unused vertices, the history is a **stopped leaf**.
* If all odd blocks have been filled, it is a **successful leaf**.
* Otherwise it is an internal state `s`. Its choices `G_s` are all actual injective labelled embeddings in the current unused lists.

A safe state with `G_s` empty is **not** declared an allowed stopped leaf. It must carry zero flow if the proposed construction is to work.

For a state processing block `y`, use exactly the hit budget from the existing block criterion:

\[
 B_{s,r}=B_{y,r}
 =\exp\left(\frac{2(e^\theta-1)}L
                  \sum_{a\in Q_k}|S_{y,a}\cap S_r|\right). \tag{4.4}
\]

The graph is fixed throughout. Inspecting its edges later does not create random edges.

### 4.3 The finite flow system

Keep different roots and their histories separate. Let `p_F>=0` be the root masses and `x_{s,g}>=0` the transition masses. Require:

\[
 \sum_Fp_F=1;                                             \tag{4.5}
\]

at every internal state, outgoing mass equals incoming mass (or `p_F` at a root); and, at every internal state and every row,

\[
 \sum_{g\in G_s}x_{s,g}a_{s,r}(g)\le0,                    \tag{4.6}
\]

where (3.1) uses (4.4). Leaves absorb mass.

All constraints are linear in the flow variables. In particular, (4.6) is the homogeneous form of a **conditional** inequality. At a positive-mass state, division by its mass supplies the required distribution on actual choices. It is not a bound on moments averaged over different boundaries.

### Theorem 4.1 — global flow or global potential certificate

Exactly one of the following holds:

**Flow:** the system (4.5)–(4.6) is feasible.

**Certificate:** there are real state potentials `V_s` and nonnegative multipliers `lambda_{s,r}` such that

\[
 \begin{aligned}
 V_\ell&=0 &&\text{at every leaf},\\
 V_{s_F}&\ge1 &&\text{at every root},\\
 V_s&\le V_{s g}+\sum_r\lambda_{s,r}a_{s,r}(g)
       &&\text{for every actual transition }s\longrightarrow s g.
 \end{aligned}                                            \tag{4.7}
\]

An internal state with no choices has no transition inequalities. The certificate must cover **all** roots in the family, not just a selected unsuccessful one.

**Proof.** Suppose both existed. Multiply each transition inequality by `x_{s,g}` and sum. Conservation and `V_leaf=0` telescope the state-potential terms to `-sum_F p_F V_{s_F}`. The moment terms have nonpositive sum by (4.6). Thus

\[
 0\le\sum_{s,g}x_{s,g}
       \left(V_{s g}-V_s+\sum_r\lambda_{s,r}a_{s,r}(g)\right)
 \le-\sum_Fp_FV_{s_F}\le-1,
\]

a contradiction.

Conversely, apply the finite Farkas alternative to conservation, normalization (4.5), nonnegativity, and the inequalities (4.6). The multipliers on conservation are unrestricted state potentials, the multipliers on (4.6) are nonnegative, and the positive separating coefficient of normalization can be scaled to one. Nonnegativity of the coefficient of each transition variable is precisely the last line of (4.7); nonnegativity of each root-mass coefficient is `V_root>=1`. Leaves have no conservation multiplier and hence potential zero. This gives (4.7). QED.

The theorem is valid for the full root family. If that family is empty, infeasibility is immediate and the certificate is vacuous at the roots; it does not manufacture a useful host cut.

### Theorem 4.2 — a feasible global flow gives a fully injective cube

Under (4.1)–(4.4), the Flow alternative implies a monochromatic `Q_d` in `U`.

**Proof.** A finite acyclic unit flow defines a probability process from its roots to its leaves. At each positive-mass internal state, normalize its outgoing transition masses. This produces kernels on actual embeddings satisfying (4.4). Zero-mass histories do not need kernels.

Condition on a positive-mass root. Fix an original row `r`. Record the hits on `S_r` by earlier chosen blocks, setting later increments to zero after stopping or after the block containing `r` has been processed. Iterated conditional expectation and (4.4) give

\[
 E\exp\left(\theta\sum_j I_{j,r}\right)
 \le\exp\left(\frac{2(e^\theta-1)}L
                       \sum_u|S_u\cap S_r|\right)
 \le\exp(2\rho(e^\theta-1)),                              \tag{4.8}
\]

because, exactly,

\[
 \sum_u|S_u\cap S_r|
   =\sum_{v\in S_r}|\{u:v\in S_u\}|
   \le\rho L.                                             \tag{4.9}
\]

A stopped leaf has some next row that lost at least `L/2` distinct resources. All previous images were disjoint, so this loss is its cumulative hit count, not just an upper bound that ignores collisions. Exponential Markov gives, for each row,

\[
 \Pr\left(\sum_j I_{j,r}\ge L/2\right)
 \le e^{-\theta L/2+2\rho(e^\theta-1)}
 \le\left(\frac{4e\rho}{L}\right)^{L/2}.                  \tag{4.10}
\]

There are `h/2` rows. The probability of a stopped leaf is at most `epsilon_F<1`. A positive-flow safe state cannot strand mass: conservation forces mass zero there if it has no choices. Thus some positive probability reaches a successful leaf.

At that leaf, use `f` on `E_t x Q_k` and the selected maps on `O_t x Q_k`. Each map is an internal cube. Equation (4.1) gives every outer edge at its original coordinate label. The reservoir avoids the even images and the histories enforce disjointness between all odd images. The resulting map is a fully injective colour-`c` `Q_d`, by (2.1). QED.

This slightly relaxes the quantification in the sufficient criterion of `CubeBlockAmplification.md` §7.1: kernels are needed only on histories reached by a feasible strategy, not on every possible valid history. It also permits overlapping lists within a block because the kernels are on actual injective blocks.

**Dimension-loss audit.** For example, if `b>=d`, `L=128b`, and `rho=4b`, then

\[
 \theta=\log8,\qquad
 \varepsilon_F=2^{d-1}(e/8)^{64b}<1.                      \tag{4.11}
\]

Indeed, `e<sqrt(8)` makes this at most `2^{d-1-96b}`. This is only arithmetic for the rounding implication. No claim is made that a core supplies those lists, loads, or a feasible flow. The missing loss is **not** hidden in the final conversion from an actual feasible flow to an ordinary cube.

Also, the Certificate alternative does not mean the graph is cube-free: a graph with a cube might fail this stronger sufficient capacity scheme. It means exactly that the displayed scheme has no feasible flow.

---

## 5. Why two tempting global shortcuts still fail

### 5.1 Mixing boundaries is not a conditional capacity construction

Suppose two boundary choices have only one available cost vector each:

\[
 (4,1),\qquad(1,4),
\]

against coordinatewise budgets `(5/2,5/2)`. Neither boundary admits a feasible kernel. Their equally weighted mixture meets the budgets exactly. For every nonnegative row weight vector, one of the two boundaries meets the corresponding weighted budget.

Thus

\[
 \forall\lambda\ \exists(F,g)\text{ meeting a weighted budget}
\]

cannot be substituted for

\[
 \exists F\ \forall\lambda\ \exists g
     \text{ meeting the conditional weighted budget}.
\]

This is a quantifier test, not a model claimed to represent a robust core. The state-specific rows in (4.6) prevent precisely this erroneous averaging. The same issue appears if one independently optimizes a parity injection for each Hall set.

### 5.2 Reducing exponential hit weights to vertex prices has a real loss

For one local dual vector, put

\[
 F(g)=\sum_r\lambda_r(e^{\theta j_r(g)}-1),\quad
 T=\sum_r\lambda_r(B_{s,r}-1),\quad
 j_r(g)=|\operatorname{im}(g)\cap S_r|.
\]

A failed kernel gives `F(g)>T` for every actual choice. The natural vertex price is

\[
 w_v=\sum_{r:v\in S_r}\lambda_r,
 \qquad \sum_{v\in\operatorname{im}(g)}w_v=\sum_r\lambda_rj_r(g).
\]

For integers `0<=j<=b`,

\[
 (e^\theta-1)j\le e^{\theta j}-1
       \le\frac{e^{\theta b}-1}{b}\,j.                   \tag{5.1}
\]

The lower bound goes in the **wrong direction** for inferring a lower bound on the additive vertex price from `F(g)>T`. The valid inference uses the upper bound, and loses

\[
 \frac{e^{\theta b}-1}{b}.                               \tag{5.2}
\]

For the useful stopped-greedy regime `L>4e rho`, one has `theta>1`; (5.2) is not a dimension-uniform loss when `b` grows. Equivalently,

\[
 e^{\theta j}-1
   =\sum_{\varnothing\ne J\subseteq\operatorname{im}(g)\cap S_r}
                     (e^\theta-1)^{|J|}
\]

contains positive higher-order hit terms which cannot be discarded in an upper bound. No inverse-codegree dichotomy controlling these terms has been proved here.

Equation (2.3) correctly retains the exponential **net** hit change under a batch rebuild. But no argument was found which matches the state-dependent multipliers in (4.7) to one fixed globally optimized potential in (2.3). Rechoosing prices after every obstruction supplies neither a monotone invariant nor termination.

---

## 6. A literal, lossless host-cut target for the projection

This section gives an exact target rather than calling a weighted obstruction a “cut.”

For a fixed colour define

\[
 \kappa_{c,D}(U)
 =\min_{\substack{\varnothing\ne A\subseteq U,
                         |A|\le N/2\\Z\subseteq U\setminus A}}
       \frac{H^U_{c,D}(A,Z)+|Z|}{|A|}.                    \tag{6.1}
\]

Take finite nonnegative vertex potentials `a_v,p_v`, with `p_v>=a_v`, `sum a_v>0`, and `|supp(a)|<=N/2`. Let `q_v(p)` be the `(D+1)`-st smallest value of `p_u` among the colour-`c` neighbours `u` of `v`; set it to infinity if there are fewer than `D+1` such neighbours. Define `(a_v-infinity)_+=0`, and set

\[
 \mathcal C_c(a,p)
 =\sum_v(a_v-q_v(p))_++\sum_v(p_v-a_v).                   \tag{6.2}
\]

### Theorem 6.1 — exact threshold variational formula

\[
 \boxed{
 \kappa_{c,D}(U)
 =\inf_{\substack{0\le a\le p,\ \sum a>0\\
                           |\operatorname{supp}(a)|\le N/2}}
       \frac{\mathcal C_c(a,p)}{\sum_v a_v}.}             \tag{6.3}
\]

The infimum is attained by zero-one potentials from a minimizing cut. In particular, if

\[
 \boxed{\mathcal C_c(a,p)\le\frac18\sum_v a_v,}           \tag{6.4}
\]

then one of at most `2N` threshold intervals supplies a literal nonempty `A,Z` violating (1.1).

**Proof.** For `tau>=0`, let

\[
 A_\tau=\{v:a_v>\tau\},\qquad
 Z_\tau=\{v:a_v\le\tau<p_v\}.
\]

These sets are disjoint, `|A_tau|<=N/2`, and their complement is exactly `{v:p_v<=tau}`. A vertex is counted by `H(A_tau,Z_tau)` precisely when

\[
 q_v(p)\le\tau<a_v.
\]

Integrating the indicators therefore gives the exact layer-cake identities

\[
 \begin{aligned}
 \int_0^\infty H^U_{c,D}(A_\tau,Z_\tau)\,d\tau
       &=\sum_v(a_v-q_v(p))_+,\\
 \int_0^\infty|Z_\tau|\,d\tau&=\sum_v(p_v-a_v),\\
 \int_0^\infty|A_\tau|\,d\tau&=\sum_va_v.               \tag{6.5}
 \end{aligned}
\]

For thresholds with `A_tau` nonempty, (6.1) bounds the cut cost below by `kappa|A_tau|`; for empty `A_tau` the cost is nonnegative. Integration proves that the right side of (6.3) is at least `kappa`.

Conversely, for any cut use `a=1_A`, `p=1_(A union Z)`. Equation (6.2) is exactly `H(A,Z)+|Z|`, and `sum a=|A|`. This proves equality and attainment.

If (6.4) holds while every nonempty threshold cut satisfies (1.1), the first two integrals in (6.5) have sum strictly larger than `(1/8)sum a`: there are finitely many constant threshold intervals, and the nonempty ones have positive total length. The other intervals contribute nonnegative cost. This is a contradiction. Test the intervals between successive distinct values among the `a_v,p_v`; their sets are constant, and their number in the nonnegative range is at most `2N`. One violating interval yields the required `A,Z`. QED.

Thus the core input says, equivalently,

\[
 \mathcal C_R(a,p)>\tfrac18\sum a,
 \qquad \mathcal C_B(a,p)>\tfrac18\sum a
\]

for all the respective admissible potentials.

**Important limitation.** Formula (6.3) is nonlinear through the order statistic `q_v`; it is not a newly discovered convex LP dual of the packing problem. No construction of `a,p` satisfying (6.4) from (4.7) is proved. Summing configuration weights into vertex marginals does not establish (6.4), its support restriction, or even the correct direction of the needed inequalities.

---

## 7. Hamming-ball rebuilding: pinned boundary and capacity charged exactly

### 7.1 Geometry at block scale

Choose an odd outer root `y`. With `r=2s+1`, let

\[
 \begin{aligned}
 Z_s&=\{z\in O_t:d_H(y,z)\le2s\},\\
 U_s&=N_{Q_t}(Z_s)=\{x\in E_t:d_H(y,x)\le2s+1\},\\
 I_s&=Z_s\cup U_s.
 \end{aligned}
\]

Then

\[
 \begin{aligned}
 |Z_s|&=\sum_{j=0}^s\binom t{2j},\qquad
 |U_s|=\sum_{j=0}^s\binom t{2j+1},\\
 |U_s|-|Z_s|&=\binom{t-1}{r}.                            \tag{7.1}
 \end{aligned}
\]

The last identity is the alternating binomial-sum identity. The set `I_s` is the outer Hamming ball of radius `r`.

When odd images outside `Z_s` are frozen, only the even sphere at distance `r` can have frozen odd neighbours; each such vertex has `t-r` neighbours outside the ball. Interior even vertices are unpinned before the new odd assignment. The number of **physical** potentially pinned vertices in the product batch `I_s x Q_k` is at most

\[
 b\binom tr.                                             \tag{7.2}
\]

The external outer boundary of `I_s` is the sphere of radius `r+1`, of size `binom(t,r+1)`. Evicting it instead of preserving its constraints costs up to that many old blocks.

Choose an odd `r` nearest `t/2`. Both parity portions have size `2^{t-2}+O(2^t/sqrt(t))`. The elementary central-binomial estimate

\[
 \max_j\binom tj\le 2^t\sqrt{\frac2{t+1}}                \tag{7.3}
\]

implies that either physical boundary cost is at most `h sqrt(2/(t+1))`, hence at most `2h/sqrt(d)` when `t>=d/2`.

One proof of the loose bound (7.3) is to write
`binom(2u,u)/4^u=product_{i=1}^u(2i-1)/(2i)` and use
`((2i-1)/(2i))^2<=i/(i+1)`; the odd case follows by comparison with the preceding even central coefficient. No boundary is being assumed empty.

### 7.2 The global deficit inequality

For any set of outer positions `I`, let `partial I=N(I)\I`. Suppose `P` is globally maximum in colour `c` and `B` is any actual coherent packing in the same colour filling **all** positions of `I`. Define

\[
 K_P(B)=|\{p\in P:\operatorname{pos}(p)\notin I\cup\partial I,
                      \operatorname{im}(p)\cap\operatorname{im}(B)
                         \ne\varnothing\}|.
\]

A conflict outside `I union partial I` can only be a resource collision. Hence

\[
 C_P(B)\subseteq
 \{p\in P:\operatorname{pos}(p)\in I\cup\partial I\}
 \ \cup\ \{\text{the }K_P(B)\text{ outside colliders}\}.
\]

Applying (2.2) gives the literal inequality

\[
 \boxed{
 |I\setminus\operatorname{dom}(P)|
 \le |\operatorname{dom}(P)\cap\partial I|+K_P(B).}       \tag{7.4}
\]

This already allows the whole moving batch to be rebuilt, with no fixed host cut. Averaging over any distribution on such **actual coherent batches** also gives

\[
 E K_P(B)\ge |I\setminus\operatorname{dom}(P)|
                  -|\operatorname{dom}(P)\cap\partial I|. \tag{7.4a}
\]

Thus a batch kernel beating this explicit hit budget would give an augmentation; no independence assumption is needed for that implication. But it also shows the limitation of boundary eviction: if the deficit is one, an `O(2^t/sqrt(t))` boundary is not negligible in an augmentation argument.

If instead `B` satisfies every required adjacency to retained old blocks outside `I`, only source-position conflicts and resource collisions need be removed. If it also avoids all their images, a batch filling `I` with even one previously missing position is an augmentation. **Constructing that pinned, capacity-respecting batch is exactly what is not proved.**

The parity reserve-matroid reduction in `CubeGlobalHallReduction.md` correctly permits rematching the entire independent even side. It does not imply that a family of internally constrained `Q_k` blocks is a transversal matroid. No such promotion to a “block reserve matroid” is made here; (2.2) and (7.4) retain the actual block constraints instead.

### 7.3 Why source boundary size is not automatically host-cut waste

If a proposed host cut pays for a set `F_pin` of physical pinned images by putting them in its separator `Z`, this uses `|F_pin|` of the literal waste budget. Even before any other charge, it requires

\[
 |A|\ge8|F_{\rm pin}|.                                    \tag{7.5}
\]

For a spare half of the cut budget it requires `|A|>=16|F_pin|`. A dual witness is not known to supply a host set of this size, nor to be disjoint from the charged separator.

Furthermore, unmapping a boundary block in a rebuild is not the same operation as deleting its vertices from the host core. The former changes the coherence and capacity constraints; the latter must obey the waste accounting of (1.1). These two costs cannot be identified without an argument.

Finally, allowing a sequence of rebuilds inside the stochastic construction changes the row lists and can recharge old resources. The proof of (4.8) uses a fixed original row family and processes each block once. No amortization theorem permits resetting that budget after arbitrary boundary changes. Global choice among roots is legitimate; unaccounted resets are not.

---

## 8. Where the attempted bridge stops: full gap ledger

Under a hypothetical cube-free core, both colours have deficient global packing optima. For every eligible root family with (4.3), Theorem 4.2 rules out a feasible flow, so Theorem 4.1 supplies a global certificate (possibly vacuous because there are no roots). The core simultaneously rules out every potential pair satisfying (6.4).

A closing proof would have to use the **joint two-colour global information** to do one of the following:

* construct a feasible conditional flow, hence a cube;
* construct a batch violating the global exchange inequality (2.2), with all retained adjacencies and released capacity accounted for;
* construct `c,a,p` satisfying (6.4), hence an actual low-waste cut by Theorem 6.1.

**None of these three constructions has been obtained from (1.1) and `N>=C h`.**

| Obligation | What is proved | What remains unproved |
|---|---|---|
| Coherent initialization | Root data, if present, are actual labelled disjoint internal cubes; all boundaries and host reservoirs can be considered globally. | Some boundary in an arbitrary core must have sufficiently large simultaneous lists and usable aggregate loads, or an alternative capacity layout. Packing isolated small cubes alone is not this assertion. |
| Actual-block capacity | Lemma 3.1 is the exact all-nonnegative-row-weights alternative. Theorems 4.1–4.2 keep the constraints conditional and prove full injectivity from a viable flow. | Robust cuts force a viable flow, or exclude every state-indexed certificate (4.7). Neither nonempty local lists nor many unconditioned block copies proves it. |
| Global rebuild | Equations (2.2)–(2.4) cover arbitrary actual batches and exactly credit released exponential capacity. | A batch violating them can be found from the core condition. A local obstruction's newly chosen prices have not been matched to one fixed optimized potential. No strict common potential prevents cycling when prices or boundaries are changed. |
| Projection to a host cut | Theorem 6.1 converts a suitable vertex-potential inequality to a literal `A,Z` without loss. | A global configuration certificate produces those potentials with nonnegative order, support at most `N/2`, and budget at most `sum(a)/8`. Exponential hit terms, conditional normalization, and state-potential differences cannot simply be dropped. |
| Half-source batch | The physical pinned boundary is at most `2h/sqrt(d)` when `t>=d/2`; (7.4) includes the exact eviction and collision charges. | The boundary can be retained or restored at no net cardinality loss. A one-block deficit need not pay for an entire boundary. The host set needed to afford (7.5) is not supplied. |
| Two colours | The global root family and the countercolouring hypothesis range over both colours. | Obstructions in the two colours can be combined into one useful host cut or one augmentation. A globally deficient optimum in only one colour is insufficient. |
| Distribution transfer | No independent random-edge law is assumed for a fixed host. All moment constraints concern actual embeddings. | The core supplies the required conditional hit moments. The existing spectral theorem still has its `d^2` loss, and a spectral hypothesis is not supplied by core extraction anyway. |
| Final output | Any successful leaf is a full injective `Q_d`, not an almost-cube; any (6.4) witness gives an actual violating cut. | No such leaf or potential witness has been produced for general cores. There is no proved recurrence for the actual Ramsey numbers. |

### Stress tests respected

* **Fixed-boundary obstructions do not settle the global problem.** The conflict optimization changes all blocks, and the flow dual must obstruct all eligible roots.
* **Boundary mixtures do not fake conditional kernels.** Section 5.1 and the per-history constraints explicitly prevent this.
* **The symplectic warning is not bypassed.** For the `B(v_i,w)=1` colour, an odd linear dependence among the `v_i` makes their common-neighbour system inconsistent: summing the equations gives `0=1`. The single-coordinate lower bound `1/(16C2^k)` supplied in the checkpoint is therefore not replaced here by an independent-binomial tail. Its quantitative law is not reproved or assumed to persist under a new adaptive conditioning. The point used here is that no uniform-random-block transfer has been established.
* **Thin source separators are not free.** Their exact costs appear in (7.4)–(7.5).
* **Global certificates alone, without the size-dependent bridge, are not a contradiction.** As a small sanity check, the two complementary `C_5` colour classes on five vertices satisfy (1.1) for `d=2`, `D=0`, yet neither contains `Q_2`. This is a genuinely global deficit and a core, but at `N/h=5/4`, not a counterexample to a sufficiently large absolute `C`. It checks the need to use the quantitative host-size hypothesis rather than treating the formal dual itself as a cut.

The substantial missing inequality can now be stated without terminology shortcuts:

> From the simultaneous absence of a successful global flow/augmentation in a two-colour core of order `C h`, construct vertex potentials obeying (6.4), or prove that such global absence is impossible.

This has **not** been proved. In particular, this report must not be cited as a proof that cut-resilient cores force cubes.

---

## 9. Verification and specification audit

Run from `/workspace/leanproject`:

```sh
python3 -u Submission/check_cube_adaptive_bridge.py
```

Recorded output: `Submission/CubeAdaptiveBridgeVerification.txt`.

The completed finite audits are:

* **4,096 fully optimized colour/blocking instances**, using every colouring of `K_5`, both colours, and both `Q_2=Q_2 square Q_0` and `Q_2=Q_1 square Q_1` blockings. All actual partial packings were enumerated. **403,456 arbitrary batches** satisfied the global exchange and boundary/collision inequalities; **148,698 equal-size exchanges** satisfied the residual exponential invariant. There were **2,192 deficient optima**.
* **4,096 exhaustive host-cut minima** for degree caps zero and one; **49,152 multilevel potential identities** checked the order-statistic formula against threshold integration. Seven sampled potentials actually triggered a violating threshold cut. Both complementary `C_5` cores were checked independently.
* **511 actual-block minimax games**, one for each nonempty `3 x 3` partite edge set. Each option was an actual labelled `Q_1`. The primal and dual solutions were converted to rational numbers and their saddle-point equality was checked **exactly**. There were **64 feasible kernels** and **447 strict separating certificates**.
* **20 multi-root conditional-flow systems**, with **9,138 history states** and **14,476 actual-block transitions**: 15 had a flow and 5 had a global Farkas certificate. These systems test actual block jobs and the general flow alternative, not a claim that their arbitrary list layouts arise in robust cores. LP equalities, inequalities, signs, and root normalization were audited numerically to `1e-7`; the all-dimensional alternative has the paper proof above. These small systems are not tests at a useful asymptotic `L/rho` ratio.
* **200 central Hamming-ball parameter choices** through outer dimension 200, with direct set-boundary checks through dimension 12; **12,000 exact row-overlap budgets**, allowing overlapping lists within a block.

The script does not assume or test the missing core-to-flow/cut implication. Passing these audits is not evidence that the Ramsey conjecture has been settled.

The required source reductions were read directly:

* `CubeDirectRamseyProgress.md`, especially the exact cut condition, extraction accounting, and constant-expansion specialization;
* `CubeBlockAmplification.md` §7.1 and the stopped greedy proof it invokes;
* `CubeGlobalHallReduction.md`, including optimization over cuts, the arbitrary-batch reserve criterion, and its Hamming-ball boundary.

The auxiliary occupancy, inverse-codegree, and spectral reports were used as scope checks, not as missing premises. The only general duality input added here is finite convex/linear-programming separation. No inverse-codegree dichotomy is postulated.

`Submission/Spec.lean` still has SHA-256

```text
9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b
```

**Final checkpoint status:** the global certificate machinery and literal cut-rounding target are proved; the adaptive robust-core bridge, and therefore `R(Q_d)=O(2^d)`, remain open in this work.
