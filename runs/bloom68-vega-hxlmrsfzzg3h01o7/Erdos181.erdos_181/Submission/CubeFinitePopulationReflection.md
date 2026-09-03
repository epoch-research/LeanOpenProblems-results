# Finite-population cube reflection: an unweighted, baseline-scale obstruction

## Status and the new conclusions

**This does not prove or disprove a uniform bound `R(Q_d) <= C 2^d`, or the proposed absolute injective lower bound.** It does refute a substantially more restricted error estimate that might otherwise be used to prove it.

The main result below is an explicit family of ordinary red-blue colourings with the following properties simultaneously:

* both colour graphs are exactly regular, of degree `(N-1)/2`, and quasirandom;
* `N/h` tends to a fixed constant, where `h=2^d`;
* the boundary and each half in the coordinate-swap reflection are individually **injective**;
* a large family of monochromatic boundary embeddings has many half-extensions but **no pair of disjoint half-extensions**;
* the sum of the negative Kneser spectral contributions over actual, unweighted cube extension families is at least

  `[(N)_h 2^(1-dh/2)] exp((h/6) log h - O(h))`;

* the same lower bound holds for monochromatic homomorphisms with **exactly one collision**, where the two identified source vertices have **no common neighbour**.

Thus one cannot bound this negative reflection error by the random baseline times `exp(Kh)`, even after imposing exact degree balance and ordinary quasirandomness. Nor can one charge all nearly injective configurations to that baseline with an `exp(O(h))` loss. The obstruction is not a weighted delta-list example, not an appeal to an oversized actual homomorphism count, and not a many-to-one mesoscopic collapse of the whole cube.

Section 11 strengthens the construction further: every selected half-extension law satisfies `max_v Pr(v in S) <= 12r/M`, yet has no disjoint pair, and the same super-exponential error lower bound holds. For example this refinement works at `N=7h+1`. Section 12 optimizes the excess to `exp((h/2) log h - 2h log log h - O(h))`, and extends the capped obstruction to every fixed multiplier `C>=13`. Thus even a constant-factor bound relative to uniform conditional occupancy does not repair the absolute-error approach.

An additional exact identity shows that isolated signed edges really can be eliminated deterministically in a degree-balanced colouring. The obstruction above survives despite that identity. What is not established is a signed cancellation argument across different boundaries that leaves a positive injective baseline.

All counts are labelled. Logarithms are natural. No Lean files or specifications are changed.

## 1. The exact reflection functional being obstructed

Write

`d=k+2`, `r=2^k`, `h=4r`.

Swap the first two coordinates of `Q_d`. Its fixed boundary is

`F = {00z,11z : z in Q_k}`,

and its two interiors are `{01z}` and `{10z}`, each a copy of `Q_k`. Each interior vertex indexed by `z` is adjacent to both boundary vertices indexed by `z`. There are no edges between the two interiors.

Fix a colour `c` and an injection `f:F -> [N]` whose boundary edges have colour `c`. Put `M=N-2r`. For an `r`-subset `S` of the remaining vertices, let `w_(c,f)(S)` count injective half-extensions with image exactly `S`. Internal half-edges and both boundary incidences at each vertex must have colour `c`. Put

\[
 Z_{c,f}=\sum_S w_{c,f}(S).
\]

The number of full injective extensions of `f` is exactly

\[
 Q(w)=\sum_{S\cap T=\varnothing}w(S)w(T).                         \tag{1}
\]

Let `L=binom(M,r)`, `D=binom(M-r,r)`, and `P=K/D`, where `K` is the Kneser disjointness matrix. Use the uniform inner product on the `L` subsets. Its eigenvalues are

\[
 \eta_j=(-1)^j{(r)_j\over(M-r)_j},\qquad 0\le j\le r.             \tag{2}
\]

For the orthogonal decomposition `w=sum_j w_j`, with `w_0=mu=Z/L`, define the negative contribution in **counting units** by

\[
 \mathcal N(w)=LD\sum_{j\ {\rm odd}}|\eta_j|\|w_j\|_2^2.
\]

Then

\[
 Q(w)=LD\left(\mu^2+
        \sum_{j\ge2\ {\rm even}}\eta_j\|w_j\|_2^2\right)
        -\mathcal N(w).                                         \tag{3}
\]

In particular, if `Q(w)=0`,

\[
 \boxed{\mathcal N(w)\ge {D\over L}Z^2.}                         \tag{4}
\]

Let `N_d(G)` be the sum of `N(w_(c,f))` over both colours and all injective monochromatic boundary maps. Thus the **actual** injective cube count is a sum of the positive terms in (3), minus `N_d(G)`. The theorem concerns precisely this negative part, not an unspecified error term.

Write

\[
 \mathcal B_d(N)=(N)_h2^{1-dh/2}                                \tag{5}
\]

for the two-colour random baseline.

## 2. Main theorem

Let `q>=2` be a prime power. Put

\[
 b=q^2+q+1,\qquad \ell=q+1,\qquad D_*=b\ell.
\]

Fix any real `C>2b+1`. For all sufficiently large integers `a`, set

\[
 k=3a,\quad d=3a+2,\quad m=2^a,\quad u=2^{2a},\quad r=mu,
 \quad h=4r,\quad N=4\lceil Cr\rceil+1.
\]

There is a red-blue colouring `G_a` of `K_N` such that:

1. Both colours are `(N-1)/2`-regular. Its signed adjacency matrix `S_a` satisfies `||S_a||_op=o(N)`, so both colours are quasirandom.
2. In each colour there is a family `Gamma_c` of injective monochromatic boundary maps of size

   \[
   |\Gamma_c|={(u!)^{2m}\over u^{2D_*}}.                         \tag{6}
   \]

   Every member has the same half-extension count

   \[
   Z=b\,{((2u)!/u!)^m\over(u+1)^\ell}.                         \tag{7}
   \]

   None has a full injective extension.
3. For two independent uniformly chosen half-extensions of any such boundary, their images always intersect, and

   \[
   \Pr(|S\cap T|=1)=1-1/b.                                    \tag{8}
   \]

   Every individual remaining host vertex has occupancy probability at most

   \[
   \max_v\Pr(v\in S)=\ell/b.                                  \tag{9}
   \]

   This upper bound can be arbitrarily small by choosing a larger fixed `q`.
4. Put `p_M=binom(M-r,r)/binom(M,r)`, `M=N-2r`. The negative reflection contribution satisfies the explicit inequality

   \[
   \boxed{
   \mathsf N_d(G_a)\ge
    {2p_M b^2((2u)!)^{2m}\over
       u^{2D_*}(u+1)^{2\ell}}.}                                \tag{10}
   \]

5. Let `H_(1,0)(G_a)` count monochromatic maps of `Q_d` having exactly `h-1` distinct images, whose unique identified pair of source vertices has no common neighbour in `Q_d`. Then

   \[
   \boxed{
   H_{1,0}(G_a)\ge
    {2b(b-1)((2u)!)^{2m}\over
       u^{2D_*}(u+1)^{2\ell}}.}                                \tag{11}
   \]

Both right sides, divided by `B_d(N)`, are

\[
 \exp\left({h\over6}\log h-O_{C,q}(h)\right).                  \tag{12}
\]

For example, the Fano plane (`q=2`, `b=7`) permits any fixed `C>15`, including `C=16`. Once `q` is fixed, the construction works at every larger fixed multiplier, not just along multipliers tending to infinity.

### Consequence

For these fixed multipliers there is **no** constant `K` such that all colourings satisfy

\[
 \mathsf N_d(G)\le \mathcal B_d(N)e^{Kh}.                        \tag{13}
\]

This refutes an absolute-baseline bound on the negative part of the finite-population reflection, even for unweighted complementary graph counts. It does **not** refute a proof which cancels appropriate positive and negative configurations before estimating the remainder.

## 3. The source quotient, markers, and phase lists

Use the balanced graph homomorphism

\[
 \pi:Q_{3a}\longrightarrow Q_a,\qquad
 \pi(x,z)=x+\left(\sum_i z_i\right)e_1,
 \quad x\in\mathbb F_2^a,\ z\in\mathbb F_2^{2a}.                \tag{14}
\]

Every fibre has size `u`. Every source edge maps to an edge. Moreover, for each source vertex, its neighbour images include **all** `a` neighbours of its image in `Q_a`.

Take a projective plane of order `q`. Its `b` lines each contain `ell` points; its `b` points each lie on `ell` lines; two different lines meet at exactly one point.

For each incident pair `(L,p)`, choose a different even-parity vertex `alpha_(L,p)` of `Q_a`. This is possible once `m/2>=D_*`. Mark the source vertex

\[
 z_{L,p}=(\alpha_{L,p},0^{2a}).
\]

Let `Z_*` be these `D_*` marked vertices. They are independent. Also `Q_(3a)-Z_*` is connected: the vertices outside the face with last `2a` coordinates zero form `Q_a` times `Q_(2a)-{0}`, a connected graph, and every surviving vertex of that face has a neighbour outside it.

For one colour gadget, make candidate vertices of two sorts:

* a private pool `U_(L,j)` of size `2u` for each line `L` and each `j in Q_a`;
* one shared vertex `v_p` for each projective point `p`.

Specify the following intended half-extension lists:

* at an unmarked source vertex `z`, the list is `union_L U_(L,pi(z))`;
* at `z_(L,p)`, the list is

  ` {v_p} union union_(L' != L) U_(L',alpha_(L,p)) `.

Specify colour `c` between private pools on adjacent quotient cells exactly when their line labels agree. Specify colour `c` between `v_p` and `U_(L,j)` exactly when

\[
 p\in L\quad\hbox{and}\quad j\in N_{Q_a}(\alpha_{L,p}).          \tag{15}
\]

Other candidate edges will not be used by the half-constraints and need not be controlled. In Section 5 these are realized by **ordinary edge colours**, and the lists by actual common neighbourhoods of boundary vertices.

### Phase lemma

Every injective half-extension satisfying these lists has a unique line `L` such that:

* it uses `v_p` at every marked vertex `z_(L,p)` for `p in L`;
* it uses private vertices from `U_(L,pi(z))` at every other source vertex;
* it uses no other shared point.

**Proof.** At every unmarked vertex the choice is private. Since the unmarked induced graph is connected, the prescribed private-pool edges force the same line label throughout it.

Consider a marked vertex `z_(L',p)`. All its neighbours are unmarked. A private choice of the fixed line `L` is available exactly when `L != L'`. A shared choice `v_p` would require `p in L` and

\[
 N_{Q_a}(\alpha_{L',p})\subseteq N_{Q_a}(\alpha_{L,p}).
\]

For `a>=3`, distinct cube vertices have at most two common neighbours, whereas both displayed neighbourhoods have size `a`. Thus this inclusion forces equality of their centres. All the marker cells were distinct, so it forces `L=L'`. This proves the assertion. Conversely, all the described assignments satisfy every required edge colour. □

For a fixed phase `L`, there are `ell` cells with `u-1` private source vertices and `m-ell` cells with `u`. Consequently its exact number of injective assignments is

\[
 Z_L=((2u)_u)^{m-\ell}((2u)_{u-1})^\ell
     ={((2u)!/u!)^m\over(u+1)^\ell}.                            \tag{16}
\]

All phases have the same count. Their image sets contain all their line's shared points. This proves that two half-images always intersect. Different phases intersect at exactly their unique common projective point, since their private pools are disjoint. Equations (7) and (8) follow.

For a uniformly random extension, the phase is uniform. A shared point is occupied with probability `ell/b`; a private vertex is occupied with probability either `1/(2b)` or `(u-1)/(2ub)`. This proves (9).

## 4. Many injective boundary maps

For each colour and each quotient cell `j`, create `u` pairs of boundary vertices, denoted `i^+,i^-`. These are `2r` boundary vertices per colour gadget. A cell containing a marker has one distinguished pair; all its other pairs are called ordinary. There is at most one marker in a quotient cell.

Send `00z` to a plus vertex and `11z` to a minus vertex in the block indexed by `pi(z)`. At a marked source vertex use its distinguished pair. In each block, independently permute the unmarked `00` positions onto the ordinary plus vertices and the unmarked `11` positions onto the ordinary minus vertices.

Every such map uses **all** the gadget's `2r` boundary vertices. Force the colour `c` on the plus-plus and minus-minus edges between adjacent quotient blocks. All these maps are injective and monochromatic on the boundary.

A block with no marker contributes `(u!)^2` maps; a marked block contributes `((u-1)!)^2`. This gives (6).

Ordinary pairs in one quotient block will have identical common-neighbour lists outside the boundary, even if the plus vertex and minus vertex chosen for one source position have **different** pair indices. Distinguished pairs have the corresponding marked lists. Thus every map just counted has exactly the list problem of Section 3, not merely a chosen subfamily of its extensions. The next section verifies this without weighted edges or externally imposed lists.

## 5. Exact realization in regular quasirandom complementary graphs

This construction is also a useful general device for realizing pinned list constraints. All signs below are actual `+1/-1` edge colours.

### 5.1 A balanced paired host

Write `N=2n+1`, where `n=2 ceil(Cr)` is even. The host vertices are

\[
 \{i^+,i^-:1\le i\le n\}\cup\{\infty\}.
\]

Choose signs `t_i` with `sum_i t_i=0`. Colour the within-pair edge by sign `t_i`, and both edges from that pair to `infinity` by sign `-t_i`.

For each two different pair indices `i,j`, initially use a checkerboard block

\[
 \begin{pmatrix}s_{ij}&-s_{ij}\\-s_{ij}&s_{ij}\end{pmatrix},
 \qquad s_{ij}=s_{ji}\in\{-1,1\}.                              \tag{17}
\]

Every checkerboard has zero row and column sums. The within-pair sign cancels the apex sign at each vertex, and the apex has signed degree `-2 sum_i t_i=0`. Thus the initial signed adjacency matrix has every row sum zero.

Allocate disjoint pair indices for the red and blue gadgets:

* `r` boundary pairs for each gadget;
* `2br` private-candidate pairs for each gadget (use their plus vertices as candidates);
* `b` shared-point pairs for each gadget (again use their plus vertices);
* a common bank of `u` correction pairs;
* padding.

Each boundary quotient block occupies a block of `u` pair indices; each private pool occupies two such blocks. The main allocation uses `(4b+2)r` pair indices. The points and correction bank fit in two additional blocks once `u>=2b`. Since `C>2b+1`, this fits in `n=2 ceil(Cr)` for all sufficiently large `a`.

Set `t_i=+1` on red boundary pairs and `t_i=-1` on blue boundary pairs. These requirements balance each other; choose the remaining `t_i` equally positive and negative.

### 5.2 A concrete quasirandom initial matrix

Partition pair indices into blocks of size `u`, except possibly the last padding block. Choose a power of two `T>=ceil(n/u)` with `T<2 ceil(n/u)`. Let `H` be the symmetric Walsh matrix of order `T`:

\[
 H_{x,y}=(-1)^{x\cdot y},\qquad HH^T=T I.
\]

For `i!=j` set `s_ij=H_(g(i),g(j))`, where `g(i)` is its block. The matrix `W=(s_ij)` with zero diagonal is a principal submatrix of `H tensor J_u` after a diagonal correction of norm at most one. Hence

\[
 \|W\|_{op}\le u\sqrt T+1.
\]

The full initial signed adjacency matrix satisfies

\[
 \|S_0\|_{op}\le2u\sqrt T+3+\sqrt{2n}=o(N),                    \tag{18}
\]

because `T=O_C(m)` and `m` tends to infinity. Crucially, all ordinary boundary indices in the same quotient block have the same signs towards every external pair index.

### 5.3 Realizing the lists and repairing degrees exactly

Let `sigma=+1` for red and `sigma=-1` for blue. For a boundary pair `i` of that gadget, give its pair index the intended ordinary or distinguished candidate list `L_i` from Section 3.

For every candidate plus vertex `v^+` in `L_i`, replace the block from boundary pair `i` to candidate pair `v` by

\[
 \begin{pmatrix}\sigma&-\sigma\\\sigma&-\sigma\end{pmatrix}.     \tag{19}
\]

This changes neither boundary signed degree. It gives the two candidate vertices signed-degree changes `+2 sigma` and `-2 sigma`.

Let `f_v` be the number of boundary pair lists containing candidate `v^+`. For a private candidate, `f_v` is `u` or `u-1`; for a shared point it is `ell`. Thus `f_v<=u` for large `a`.

For this candidate pair, select `f_v` different pairs from the common correction bank, and replace each candidate-to-correction block by

\[
 \begin{pmatrix}-\sigma&-\sigma\\\sigma&\sigma\end{pmatrix}.     \tag{20}
\]

This cancels its signed-degree changes exactly and changes neither correction vertex's signed degree. The same correction bank can be reused by different candidates and by both gadgets: each such block separately has zero column sums.

Force all the required boundary and candidate compatibility signs by **checkerboard** blocks (17), which preserve every signed degree. The sets of blocks used for list modifications, degree repairs, boundary edges, and candidate edges are disjoint.

The final matrix therefore still has every row sum zero. Both colours are exactly `(N-1)/2`-regular.

### 5.4 No unintended half-extensions

For a distinguished boundary pair, all unchanged external blocks are checkerboards, so its two vertices have no common colour-`sigma` neighbour there. The apex has colour `-sigma` to both. Block (19) contributes exactly the intended candidate plus vertex, and not its minus partner.

For two possibly different ordinary boundary pair indices in the same quotient block, their unmodified external signs are identical before reversing the sign for the minus endpoint. Their lists are also identical. Hence the same common-neighbour assertion holds.

There can be additional common neighbours **inside the gadget's boundary**, but every boundary map in Section 4 uses that entire boundary, so all these vertices are excluded from the available population. Neither degree repairs nor candidate-edge modifications involve any boundary pair. Modifications for the other colour gadget do not touch these boundary-to-external blocks.

It follows that the remaining common colour neighbourhood for every source position is **exactly** the intended list. The phase lemma therefore describes all half-extensions, not only planted ones. In particular there are no disjoint pairs of them.

### 5.5 Quasirandomness survives

The number of modified pair blocks is bounded by

\[
 O_b(a r u+r u+r)=O_b(a r u).
\]

Indeed:

* boundary edges use `O(a m u^2)=O(a r u)` blocks;
* lists and degree repairs use `O_b(r u)` each;
* private-pool compatibilities use `O(b^2 a m(2u)^2)=O_b(a r u)`;
* shared-point compatibilities use `O_b(r)`.

Each block changes a bounded number of signed matrix entries by at most two. Thus

\[
 \|S-S_0\|_{op}\le\|S-S_0\|_F
     =O_b(\sqrt{a r u})=O_b(r\sqrt{a/m})=o(N).                  \tag{21}
\]

Together with (18), this proves quasirandomness of both colours, uniformly over cuts. This is ordinary quasirandomness, not a claim of uniform common-neighbour estimates for **every** pair of host vertices. The deliberately exceptional common neighbourhoods are essential.

## 6. Negative reflection mass and single collisions

For each of the `2|Gamma_c|` colour-boundary pairs, equation (1) is zero. Applying (4) and (7) gives

\[
 \mathsf N_d(G_a)\ge2p_M|\Gamma_c| Z^2
  ={2p_M b^2((2u)!)^{2m}\over u^{2D_*}(u+1)^{2\ell}},
\]

which proves (10).

For a fixed boundary, choose the two half-extensions in two **different** phases. Their images intersect in exactly one point. Therefore the combined map has precisely `h-1` distinct images. The two identified source vertices are `01 z_(L,p)` and `10 z_(L',p)`. Their marker cells are distinct and both even, so the residual Hamming distance is at least two; their full Hamming distance is at least four. They have no common neighbour in the cube.

There are `b(b-1) Z_L^2=(1-1/b) Z^2` such ordered extension pairs per boundary. Summing over both colours and all the selected boundaries gives (11). No edge of the cube is collapsed to a loop, and no two cube edges are identified by this unique collision, because its source vertices have no common neighbour.

This is a particularly direct obstruction to charging collision errors using only the cube's bounded codegree. The maps counted in (11) are injective except at one zero-codegree pair.

## 7. Comparison with the random baseline

Stirling's formula gives

\[
 2m\log((2u)!)=4r\log u+O(r)
              ={8\over3}r\log r+O(r).
\]

The powers of `u` and `u+1` in (10)--(11) have constant exponents once `q` is fixed, so their logarithms are `O_q(log r)`. Also

\[
 \log p_M=-O_C(r),
\]

since `M/r` tends to `4C-2>2`.

On the other hand,

\[
 \log\mathcal B_d(N)
  =\log(N)_{4r}+(1-(6a+4)r)\log2
  =2r\log r+O_C(r).
\]

The difference is

\[
 {2\over3}r\log r-O_{C,q}(r)
 ={h\over6}\log h-O_{C,q}(h),
\]

as asserted in (12). In particular the negative mass is not merely somewhat larger than the random baseline: it exceeds that baseline times **every** fixed `exp(Kh)`.

## 8. A smaller single-forced-point version

The same construction with one phase and one shared forced point needs only `C>3`. Use one marked source vertex. Then

\[
 |\Gamma_c|={(u!)^{2m}\over u^2},\qquad
 Z={((2u)!/u!)^m\over u+1}.
\]

Both colours again have no full completion of any selected boundary, and

\[
 \mathsf N_d(G_a)\ge
 {2p_M((2u)!)^{2m}\over u^2(u+1)^2}.                            \tag{22}
\]

This has the same exponent (12), but its forced point has occupancy one.

There are also many combined maps having just that one collision: inject the private vertices of the two halves disjointly into the `2u` vertices in each pool. This gives `((2u)!)^m/2` maps per boundary and colour, hence a total of at least

\[
 {(u!)^{2m}((2u)!)^m\over u^2}.                                \tag{23}
\]

Here the colliding source pair is at distance two, rather than at least four. Section 2 supplies the stronger small-occupancy and zero-codegree conclusions.

## 9. What deterministic isolated-edge cancellation does give

There is an exact cancellation identity; its existence is not the missing point.

Let `S` be any symmetric zero-diagonal sign matrix. Put

\[
 D(x)=\sum_yS_{xy},\qquad T=\sum_xD(x).
\]

For a labelled simple graph `F` on vertex set `V`, define

\[
 J_F(S)=\sum_{\phi:V\hookrightarrow[N]}
            \prod_{ab\in E(F)}S_{\phi(a)\phi(b)}.
\]

For each fixed injection of `V`, whose image is `A`, the sum of signs on ordered edges outside `A` is exactly

\[
 \sum_{x\ne y\notin A}S_{xy}
    =T-2\sum_{a\in A}D(a)+\sum_{a\ne b\in A}S_{ab}.             \tag{24}
\]

Thus when the colouring is degree-balanced (`D(x)=0`),

\[
 \boxed{J_{F\sqcup K_2}(S)
       =2\sum_{\{a,b\}\subset V}J_{F\triangle ab}(S).}          \tag{25}
\]

The vertex set on the right remains `V`; `triangle ab` toggles the edge because `S_ab^2=1`. In normalized injective densities, for `v=|V|`,

\[
 \boxed{t_{\rm inj}(F\sqcup K_2,S)
    ={2\over(N-v)(N-v-1)}
       \sum_{\{a,b\}\subset V}t_{\rm inj}(F\triangle ab,S).}   \tag{26}
\]

Similarly, if `z` is a leaf of `F` with neighbour `u`, degree balance gives

\[
 \boxed{J_F(S)=-\sum_{a\in V\setminus\{z,u\}}
                  J_{(F-z)\triangle ua}(S).}                   \tag{27}
\]

These identities follow just by summing the last endpoint(s), excluding occupied vertices. They retain exact falling-factorial normalization and do not average over random hosts. For example,

\[
 t_{\rm inj}(P_3,S)=-{1\over N-2},\qquad
 t_{\rm inj}(2K_2,S)={2\over(N-2)(N-3)}.                        \tag{28}
\]

The important qualification is that (25) creates toggled edges between arbitrary already occupied vertices. It is not positivity of the remaining connected terms. All the colourings in the main theorem satisfy the degree-balance hypothesis of (25)--(28), while still satisfying the lower bound (10).

## 10. Interpretation and limitations

1. **What is ruled out.** A local multiplicative reflection inequality, or a global bound on its negative spectral part by the random baseline times `exp(O(h))`, cannot be repaired using just unweightedness, complementarity, exact global degrees, ordinary quasirandomness, and bounded source codegree. The counterexample uses literal cube extensions satisfying all of those conditions.
2. **Small marginals are also insufficient.** For every desired fixed small occupancy bound, the projective-phase variant has it at a sufficiently large fixed host multiplier. Almost all pairs of half-extensions then overlap in just one vertex, with no new-part edge overlap at all.
3. **Why this does not contradict Riordan.** In a random host the second-moment overlap distribution comes from uniform placements and exchangeable edge sampling. Here the placements are biased by the requirement that they extend a monochromatic boundary. The biased law can be supported on an intersecting family even though its first marginals are small. Removing isolated *edge* overlaps does not remove this one-vertex obstruction.
4. **What remains possible.** A deterministic proof could cancel whole phase families, including their matching positive contributions, before comparing the remainder with the random baseline. A different SOS or hard-capacity argument might do this. The theorem does not show that such a remainder fails to be positive.
5. **What is not claimed.** No upper bound on the global injective cube count of these examples is proved, and no Ramsey counterexample is claimed. Indeed the refined examples in Section 11 can explicitly be made to contain a red cube without changing their bad extension families. The proposed general theorem for regular weakly norming bounded-codegree graphs with `Delta<=log_2 v` is neither proved nor refuted: the present source graphs are cubes, but the conclusion here concerns an error functional, not the global injective count. No claim about all bipartite graphs having uniformly linear Ramsey number is made.
6. **Exact host size.** The extra apex only makes exact degree balance possible at odd `N`. It is never used by the selected extensions. For an integer multiplier `C`, deleting it gives the same obstruction on exactly `Ch` vertices; both colours then have degrees `Ch/2` or `Ch/2-1`, with equal edge counts. Quasirandomness and all displayed asymptotic excesses survive.

## 11. Refinement: even an O(r/M) bound on every conditional occupancy is insufficient

The phase need not be encoded at every source vertex. Encoding it on a small connected subcube gives a stronger occupancy conclusion.

**Refined theorem.** Fix a prime power `q>=2`, and put

\[
 b=q^2+q+1,\quad \ell=s=q+1,\quad C=q+5=s+4.
\]

For the same sequence `k=3a`, `r=2^k`, `h=4r`, there are regular quasirandom two-colourings on `N=Ch+1` for which (12) holds for both the negative reflection contribution and the zero-codegree one-collision count. In addition, for every selected boundary and either colour,

\[
 \boxed{\max_v\Pr(v\in S)\le {12r\over M},\qquad
        \Pr(S\cap T=\varnothing)=0,\quad M=N-2r.}              \tag{29}
\]

Thus a constant-factor bound relative to **uniform occupancy** is not enough, even with the actual unweighted half-extension law. This refinement does not retain the exact one-intersection probability (8); it retains an `exp(-O_q(r))` fraction of one-intersection pairs, which suffices for the same baseline exponent.

### 11.1 Encoding the phase on a small connected subcube

Let `tau=2^t` be the least power of two at least `b`; assume `a>t`. Replace (14) by

\[
 \pi(x,z)=x+\left(\sum_i z_i\right)e_{t+1}.
\]

This preserves the first `t` coordinates. Let `J` be the quotient subcube where those coordinates are zero, with `m_T=m/tau` cells. Its preimage `T_*` is a connected source subcube, containing `r/tau` vertices.

Choose the `D_*=b ell` marker cells `alpha_(L,p)` to have their first `t` coordinates equal to `e_1` and their total parity even. They are all distinct. There are `m/(2 tau)` such cells, enough for large `a`. Mark `(alpha_(L,p),0)` in the source. The markers are independent and outside `T_*`. Each has exactly **one** neighbour in `T_*`, in quotient cell

\[
 \beta_{L,p}=\alpha_{L,p}+e_1.
\]

All these `beta` cells are different.

Use the following candidate pools, separately for each colour:

* for each `j in J` and line `L`, a private tagged pool `U_(L,j)` of size `2u`;
* for each `j notin J`, a shared ordinary pool `V_j` of size `su`;
* for each marker `(L,p)`, a private replacement pool `W_(L,p)` of size `u`;
* one shared vertex `v_p` for each projective point.

At a tagged source vertex the list is `union_L U_(L,pi(z))`. At an ordinary unmarked source vertex it is `V_(pi(z))`. At marker `(L,p)` it is **only** `W_(L,p) union {v_p}`.

Set the required colour on edges as follows:

1. Between tagged pools on adjacent quotient cells, it occurs exactly when the line labels agree.
2. Between ordinary pools on adjacent cells, and between a tagged and ordinary pool on adjacent cells, it always occurs.
3. Every replacement pool `W_(L0,p)` has the required colour to every ordinary pool. To a tagged pool with line label `L`, it has that colour exactly when `L != L0`.
4. The shared point `v_p` has the required colour to every ordinary pool. Its edge to a tagged pool `U_(L,j)` has that colour exactly when `p in L` and `j=beta_(L,p)`.

Other candidate edges are irrelevant to the prescribed source positions.

Because `T_*` is connected, all tagged choices have one line label `L`. At a marker `(L0,p)`, its unique tagged neighbour makes `W_(L0,p)` permissible precisely when `L != L0`. The point is permissible precisely when `L=L0`, since the `beta` cells are distinct. Hence the phase again forces exactly its `ell` projective points. The other markers use their replacement pools. This describes **all** extensions.

### 11.2 Exact counts and occupancies

Every phase has the same number of injective half-extensions:

\[
 Z_L=((2u)_u)^{m_T}
     ((su)_u)^{m-m_T-D_*}
     ((su)_{u-1})^{D_*}u^{D_*-\ell}.                           \tag{30}
\]

The boundary family is unchanged: `|Gamma_c|=(u!)^(2m)/u^(2D_*)`. Its normal lists are constant within each quotient block; each marked block has one distinguished pair.

Under a uniformly chosen extension, the phase is uniform. The occupancy probabilities are:

* shared point: `ell/b`;
* tagged private vertex: `1/(2b)`;
* ordinary shared-pool vertex: `1/s` or `(u-1)/(su)`;
* replacement-pool vertex: `(1-1/b)/u`;
* unused vertex: zero.

For large `u`, their maximum is `ell/b`. With `C=q+5` and `M=(4C-2)r+1`,

\[
 {M\over r}{\ell\over b}
 \le {(4q+19)(q+1)\over q^2+q+1}\le12 \quad(q\ge2).
\]

The last inequality is `8q^2-11q-7>=0`. Every pair of phase point sets intersects, so the disjointness probability is still zero. This proves (29).

### 11.3 Realization and quasirandomness

Use exactly the paired host of Section 5. The main candidate allocation per colour uses

\[
 {2b\over\tau}r+s(1-1/\tau)r\le(s+2)r
\]

pair indices. Boundary pairs add `r`. The replacement pools and shared points use `D_*u+b=o(r)` more. Since `n=2Cr=2(s+4)r`, both gadgets, a correction bank of `u` pairs, and padding fit for all large `a`.

A tagged or ordinary candidate appears in `u` or `u-1` boundary-pair lists. A replacement candidate appears in one; a shared point appears in `ell`. The exact degree repair (19)--(20) therefore still applies with a bank of `u` correction pairs. The common-neighbour argument of Section 5.4 applies without change.

All modified blocks number `O_q(a r u)`: adjacency between large private/ordinary pools is only prescribed on quotient edges; the replacement pools have total size `D_*u=o(r)`, so prescribing all of their incident compatibilities costs only `O_q(r u)` blocks. Point compatibilities cost `O_q(r)`. Thus (18)--(21) again prove exact regularity and quasirandomness.

One may additionally ensure that the host contains a red `Q_d`. Indeed, since `tau>=b`, the unused padding has at least `(2+2s/tau)r-o(r)>2r` pair indices. Choose `2r` such indices, indexed by `Q_(k+1)`, set their within-pair signs `t_i=+1`, and set checkerboard signs `s_ij=+1` along that cube's edges. The plus and minus vertices then form a red `Q_(k+2)`. There is ample freedom to keep `sum_i t_i=0`, since the required positive signs use only `3r` indices (these padding indices and the red boundary) while `n/2=Cr>=7r`. This adds `O(k r)` checkerboard modifications, does not touch any relevant common-neighbour list, and preserves all asserted properties. Thus these refined examples can be certified not to be Ramsey counterexamples.

### 11.4 The error remains super-exponential relative to the baseline

Equation (30) gives `log Z_L = r log u + O_q(r)`. Therefore

\[
 \mathsf N_d(G)\ge2p_M|\Gamma_c|b^2Z_L^2
    =\mathcal B_d(N)\exp\left({h\over6}\log h-O_q(h)\right).
\]

For completeness, one-collision maps can still be counted exactly. Choose different phases for the two halves, use their disjoint tagged pools, and inject their ordinary vertices disjointly in each shared pool. At a marker belonging to one of the two phases, only the other half uses its replacement pool. At every other marker, choose two different replacement vertices. For each ordered pair of different phases the count per boundary is

\[
 Y=((2u)_u)^{2m_T}
   ((su)_{2u})^{m-m_T-D_*}
   ((su)_{2u-2})^{D_*}
   u^{2\ell}\bigl(u(u-1)\bigr)^{D_*-2\ell}.                  \tag{31}
\]

These maps have just the forced shared-point collision, between source vertices at distance at least four. Since `log Y=2r log u+O_q(r)`,

\[
 H_{1,0}(G)\ge2|\Gamma_c|b(b-1)Y
   =\mathcal B_d(N)\exp\left({h\over6}\log h-O_q(h)\right).
\]

This proves the refined theorem. It rules out a uniform-occupancy-cap repair of the absolute negative-error estimate, but still does not rule out a fully signed cancellation proof of the injective baseline.

## 12. Parameter optimization: an almost maximal leading excess

The choice `k=3a` was only for a clean exponent. Every construction and exact counting formula above works with independent integers `k>=a+2`,

\[
 r=2^k,\quad m=2^a,\quad u=2^{k-a},\quad h=4r,
\]

provided the finitely many marker cells fit and `u` is sufficiently large for the fixed `q`. In (14) and Section 11 replace the `2a` extra coordinates by `k-a` extra coordinates. The quasirandomness estimate only requires `a/m -> 0` and `m -> infinity`. The phase and marker proofs are unchanged.

For example choose `a=ceil(2 log_2 k)`. Then `k^2<=m<2k^2`, and the tagged construction has

\[
 \|S\|_{op}/N=O_q(\sqrt{\log k}/k)=o(1).
\]

The exact factorial formulas give, for both the negative mass and the zero-codegree one-collision lower bound, logarithm `4r log u+O_q(r)`. Subtracting the baseline logarithm `2r log r+O_q(r)` now gives the stronger inequalities

\[
 \boxed{
 \begin{aligned}
 \mathsf N_d(G)&\ge\mathcal B_d(N)
   \exp\left(\tfrac12h\log h-2h\log\log h-O_q(h)\right),\\
 H_{1,0}(G)&\ge\mathcal B_d(N)
   \exp\left(\tfrac12h\log h-2h\log\log h-O_q(h)\right).
 \end{aligned}}                                               \tag{32}
\]

Here `C=q+5` remains fixed, and the conditional cap `12r/M` and optional red cube in the padding remain valid. Thus the excess is `exp((1/2-o(1))h log h)`, not just the `exp((1/6-o(1))h log h)` furnished by the simpler parameter sequence. For the one-collision count the leading coefficient `1/2` is maximal up to lower-order terms, since there are at most `binom(h,2) N^(h-1)` maps with exactly one collision.

The capped version also works at **every fixed real multiplier `C>=13`**, not just at `C=q+5`. Choose the largest power of two `q<=C-5`, so `q>=8` and `C<2q+5`, and add padding to reach `N=4 ceil(Cr)+1`. The lists and their occupancies do not change. For large `r`,

\[
 {M\over r}{q+1\over q^2+q+1}
 \le {(8q+19)(q+1)\over q^2+q+1}\le12,
\]

since `4q^2-15q-7>=0` for `q>=8`. All the lower bounds persist, with the `O(h)` constant allowed to depend on this fixed multiplier.

## Verification

`check_cube_finite_population_reflection.py` checks the original paired-host construction, exact degree repair, common-neighbour list realization including mismatched ordinary plus/minus indices, the quotient and phase lemma, factorial counts, and the signed cancellation identities. The companion `check_cube_flat_occupancy.py` checks the tagged refinement, its occupancy cap and pair counts, and an explicit red cube in unused padding that leaves the bad extension families unchanged. Both check the asymptotic ratios using high-precision log-gamma arithmetic; the refinement is also compared with independently derived first-order Stirling constants.

The original dense host checks use `N=129` and `N=2049`; the tagged dense host check uses `N=6145`. Fano-plane phase, count, and occupancy calculations are checked separately without constructing its much larger dense adjacency matrix. The recorded outputs are `CubeFinitePopulationReflectionVerification.txt` and `CubeFlatOccupancyVerification.txt`. These are checks of the proved formulas, not computational evidence for the unresolved Ramsey assertion.

`Submission/Spec.lean` is unchanged; its SHA-256 remains `9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b`.
