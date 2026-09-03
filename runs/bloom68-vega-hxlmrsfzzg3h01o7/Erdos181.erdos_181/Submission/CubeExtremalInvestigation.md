# Complete-host cube extremal bounds: a dimension-sensitive audit

## Outcome and scope

This does **not** prove `R(Q_d) = O(2^d)`, nor the corresponding half-density embedding statement. It supplies verified complete-host results, explicit dimension-dependent consequences, a quantitative test for the proposed coefficient, and an exact square-lift calculation identifying both a plausible mechanism and its missing ingredient.

Write `h=2^d`, `m=h/2`, and `ell=dh/2`. Here `ex(N,Q_d)` always means `ex(K_N,Q_d)`: ordinary, injective, not necessarily induced copies. No results about `ex(Q_N,H)`, cube posets, or cube minors are being used as ordinary subgraph theorems. No Lean files were edited.

The exact majority-colour threshold is `N(N-1)/4`, rather than `N^2/4`. The coefficient tests below produce margins of order `N^2/d` or `N^2`, so this finite correction is harmless there; a bare inequality `ex(N,Q_d)<N^2/4` with no margin should not silently be substituted for the exact threshold.

The search used the local corpus (including a narrow full-text search across its 49,918 math.CO records). Network access was unavailable. Statements below are results verified in this corpus, not a claim to have checked all more recent literature.

## 1. The actual Erdős–Simonovits cube theorem

Füredi, **On a theorem of Erdős and Simonovits on graphs not containing the cube**, arXiv:1307.1062, gives

\[
 \operatorname{ex}(N,Q_3)\le N^{8/5}+(2N)^{3/2},
\]

and, using the stronger bipartite hexagon bound,

\[
 \operatorname{ex}(a,b,Q_3)
 \le 2^{1/5}(ab)^{4/5}+9(a\sqrt b+b\sqrt a),
\]
\[
 \operatorname{ex}(N,Q_3)
 \le 2^{-2/5}N^{8/5}+13N^{3/2}.
\]

These are explicit complete-host/bipartite-host inequalities, not just fixed-dimension O-notation. The paper denotes this 8-vertex graph by `Q` or `Q_8`; its subscript 8 is the vertex count, not the dimension.

### Where the exponent and coefficient come from

Let `G` be bipartite, with part sizes `a,b` and `e` edges, and first suppose its minimum degree is at least 2. The number of unoriented length-three paths with one endpoint in each part satisfies

\[
 P_3(G)\ge \frac{e(e-a)(e-b)}{ab}.
\]

For each `x` and `y` in opposite parts, the graph between `N(x)\{y}` and `N(y)\{x}` is `C_6`-free: a hexagon there, together with `x,y`, forms a `Q_3`. If

\[
 \operatorname{ex}(u,v,C_6)\le c(uv)^{2/3}+k(u+v),
\]

then summing the corresponding upper bounds on paths and applying Hölder gives

\[
 P_3(G)\le c e^{4/3}(ab)^{1/3}+k(a+b)e,
\]
\[
 (e-a)(e-b)\le c e^{1/3}(ab)^{4/3}+k(a+b)ab.                 \tag{1}
\]

The leading term is therefore `c^(3/5)(ab)^(4/5)`. Passing through a maximum cut, and using `ab<=N^2/4`, makes the ordinary-host leading coefficient

\[
 A_3=(c/2)^{3/5}.
\]

The elementary bound has `c=2,k=2`, giving `A_3=1`; the stronger bound has `c=2^(1/3),k=16`, giving `A_3=2^(-2/5)`.

For completeness, (1) also gives an elementary slightly smaller error term than the displayed published bound. Put `P=ab`, `S=a+b`, `T=a sqrt(b)+b sqrt(a)`, and `X=c^(3/5)P^(4/5)`. If `e>X+tT`, then

\[
 e^2-c e^{1/3}P^{4/3}\ge e(e-X),\qquad T\ge S,\quad T^2\ge SP.
\]

Consequently the left side minus right side of (1) is greater than

\[
 t(t-1)T^2+P-kSP>0
\]

whenever `t(t-1)>=k`. Vertices of degree at most one can be removed inductively, since the bound `X+tT` decreases by at least one when a nonempty part loses a vertex (`t>=1`). Thus `c=2^(1/3), k=16, t=5` yields the valid corollary

\[
 \operatorname{ex}(a,b,Q_3)\le 2^{1/5}(ab)^{4/5}+5(a\sqrt b+b\sqrt a),
\]
\[
 \operatorname{ex}(N,Q_3)\le 2^{-2/5}N^{8/5}+5\sqrt2\,N^{3/2}. \tag{2}
\]

This is only a simplification of a lower-order constant, not a claim of a new dimension-uniform result.

### Why this is not a cube-dimension recursion

For `Q_3`, deleting two antipodal vertices leaves a hexagon, and every remaining vertex is adjacent to one of the two deleted vertices. For `d>=4`, the two neighbourhoods cover at most `2d` of the `2^d-2` other vertices. The same local hexagon obstruction cannot force a higher-dimensional cube.

The Erdős–Simonovits reduction theorem in the Füredi–Simonovits survey, arXiv:1306.5167, says

\[
 \operatorname{ex}(N,L)=O(N^{2-\alpha})
 \Longrightarrow
 \operatorname{ex}(N,K_{t,t}*L)=O(N^{2-\beta}),\quad
 \beta^{-1}=\alpha^{-1}+t.
\]

The operation `*` adds complete bipartite joins; it is not the Cartesian product defining successive cubes.

## 2. “Generalized cubes” are a different family

Jiang–Newman, **Small dense subgraphs of a graph**, arXiv:1502.02602, Section 6, state

\[
 \operatorname{ex}(N,H_{t,t})\le 2^{16}t\,N^{4t/(2t+1)}
\]

for `N` sufficiently large as a function of `t`. Here

\[
 H_{s,t}=K_{s,t}\square K_2;
\]

in particular `H_{2,2}=Q_3`. Jiang–Ma–Yepremyan, **On Turán exponents of bipartite graphs**, arXiv:1806.02838, Theorem 1.6, extend this to

\[
 \operatorname{ex}(N,H_{s,t})=O_{s,t}(N^{2-2/(2s+1)}),\qquad t\ge s\ge2.
\]

One legitimate application to ordinary cubes is

\[
 Q_d=Q_{d-1}\square K_2\subseteq K_{2^{d-2},2^{d-2}}\square K_2.
\]

It gives only

\[
 \operatorname{ex}(N,Q_d)
 \le 2^{d+14}N^{2-2/(2^{d-1}+1)}                         \tag{3}
\]

above an unspecified dimension-dependent threshold. For `d>=4`, even the exponent in (3) is weaker than `2-1/d`, and at `N=C2^d` its right side is vacuous.

There is also an explicit threshold loss in the proof, not just its leading coefficient. One of its displayed prerequisites is

\[
 N^{1/[t(2t+1)]}
 >\frac{2^{12}(8t!)^{1/t}}{t}.
\]

The bracket tends to `2^12/e`; this stage alone asks for `log N=Omega(t^2)`. The later proof needs `C=8t^3` in the regularization lemma where an earlier line prints `8t`; making that correction only enlarges this prerequisite by a factor `t^(2/t)` inside the bracket and does not change the exponent comparison. In either reading, substituting `t=2^(d-2)` is far outside the linear-host regime. This explicit comparison is not claimed to be a complete sufficient formula for all of the paper's thresholds.

The useful structural ingredient in the later Jiang–Ma–Yepremyan proof is its correlated-matching lemma: for an `H_(s,t)`-free graph and an `(s-1)`-matching `M`, the number of suitably `2t`-correlated `s`-matchings in its common-neighbourhood graph is at most

\[
 (s-1)(t-1)e(N(M))^{s-1}v(N(M)).
\]

It really does control overlap. But its neighbourhood relation requires all the relevant cross edges, rather than just the sparse commuting-square pattern of `Q_d`.

## 3. A nearly sharp explicit generic coefficient is already available

Lee, **Ramsey numbers of degenerate graphs**, arXiv:1505.04773, Theorem 1.3 and Section 2, proves the following density theorem. Let `H` have `h` vertices, with one bipartition class of maximum degree `d`, and let the other class have size `m`. If

\[
 \rho^{d(d-2)}\le\varepsilon<1,\qquad
 \frac{m^d}{(m)_d}\le 1+\varepsilon,
\]

then every graph of density at least `rho` on at least `(1+epsilon)rho^(-d)h` vertices contains `H` (with the usual integer rounding). A more precise bipartite form requires respective host-part sizes

\[
 (1+\varepsilon)\rho^{-d}|W_1|,
 \quad ((1+\varepsilon)/\varepsilon)^{1/d}\rho^{-2}|W_2|.
\]

### Fully explicit uniform corollary for cubes

For every `d>=8`, `h=2^d`, and even integer `N>=4h`,

\[
 \boxed{\operatorname{ex}(N,Q_d)
 <\binom N2\left(\frac{h+2d^2}{N}\right)^{1/d}.}          \tag{4}
\]

Proof: put `epsilon=2d^2/h<=1/2`. With `m=h/2`,

\[
 \prod_{j=0}^{d-1}(1-j/m)
 \ge 1-\frac{d(d-1)}h\ge1-\frac{d^2}h,
\]

so `m^d/(m)_d<=1+2d^2/h`. Set `rho=((h+2d^2)/N)^(1/d)`. Since `N>=4h`,

\[
 \rho^{d(d-2)}\le (3/8)^{d-2}\le4/h\le\varepsilon.
\]

Lee's hypotheses follow. For exact integrality, take a random balanced bipartition of the `N` vertices: some such cut has bipartite density at least the original density, and both part sizes equal `N/2`. Apply Lee's bipartite form; its second part-size requirement is at most its first under the displayed condition.

In the normalization proposed in the question, (4) has

\[
 \operatorname{ex}(N,Q_d)
 \le a_d h^{1/d}N^{2-1/d},\qquad
 a_d=\tfrac12(1+2d^2/h)^{1/d}
     =\tfrac12(1+O(d/2^d)).                             \tag{5}
\]

Thus the coefficient is already essentially `1/2`, but on the wrong exponent. At `N=Ch`, (4) only gives

\[
 \frac{\operatorname{ex}(N,Q_d)}{N^2}
 <\frac12(1-1/N)\left(\frac{1+2d^2/h}{C}\right)^{1/d}
 \longrightarrow\frac12,
\]

not `1/4`. The same paper explicitly obtains `R(Q_d)<=4^d+d^2 2^d` for sufficiently large `d`. This is a verified bound, not a claim that it is the current best Ramsey bound.

For comparison, Fox–Sudakov, arXiv:0909.3271, give the all-graph sufficient condition `N>=8d rho^(-d)h`; Conlon–Fox–Sudakov, arXiv:1507.00547, Section 3, remove the polynomial degree loss and prove `R(H)<=2^(Delta+6)|H|`. Neither changes the exponent relevant here.

### The proof loss in defect language

Lee uses `omega_theta(S)=0` for `|N(S)|>=theta` and `theta/|N(S)|` otherwise. Two-vertex DRC produces a large set with bounded average defect. After embedding one parity class, a total defect at most `m` permits embedding the other class by handling the smallest candidate neighbourhoods first: the i-th neighbourhood has at least i vertices. This is an actual injectivity argument, not merely a homomorphism count.

Its budget is nevertheless `theta<=rho^d |V_1|/(1+epsilon)`, with `theta=m`. That is the source of the `rho^(-d)h` scale. It does not use the special fact that distinct cube neighbourhoods intersect in at most two vertices.

## 4. Fixed-dimension exponent improvements are not uniform estimates

Sudakov–Tomon, **Turán number of bipartite graphs with no K_(t,t)**, arXiv:1910.11048, Theorem 1.4, prove

\[
 \operatorname{ex}(N,H)=o_H(N^{2-1/t})
\]

when one side has degree at most `t` and `H` has no `K_(t,t)`. Since cube pairs have at most two common neighbours, this implies

\[
 \operatorname{ex}(N,Q_d)=o_d(N^{2-1/d})\quad(d\ge3).       \tag{6}
\]

The order of the quantifiers matters: for every fixed `d,eta` there is a threshold `N_0(d,eta)`. There is no stated `N_0(d,eta)<=C2^d`.

An explicit audit of that proof shows why this is not a uniform route. Its universal target `H_k` needs `k>=h/2` to contain a cube. After regularization, write the host size as `q`; let `Delta=R_d(k)` and

\[
 A=2\Delta((d-1)/\eta)^{d-1}2^{3d-4}.
\]

Its sampling probability is `A q^(-1/d)`, already requiring `q>A^d`. More decisively, its final comparison is

\[
 \#\text{all copies}\ge\delta(A/2)^k q^{(d-1)k/d},
\qquad
 \#\text{bad copies}\le(2A)^k q^{((d-1)k-1)/d},
\]

where `delta` is a hypergraph removal constant. To certify a good copy this calculation requires

\[
 q^{1/d}>4^k/\delta,
 \qquad q>(4^k/\delta)^d\ge 2^{dh}.                    \tag{7}
\]

The last inequality uses `k>=h/2` and `delta<=1`. It is a requirement of this proof's estimates, not a lower bound for the true embedding threshold. It is already doubly exponential in dimension without estimating the removal constant.

There is a further legitimate cube-specific deduction from the paper's final theorem. If `d=2^r>=4`, colour the even cube vertices by

\[
 c(x)=\bigoplus_{i:x_i=1}i\in\mathbb F_2^r,
\]

where the d coordinate labels are all vectors of `F_2^r`. The d neighbours of every odd vertex have distinct colours. Thus the neighbourhood hypergraph is d-partite and d-uniform. The final theorem on subdivisions of partite hypergraphs gives

\[
 \operatorname{ex}(N,Q_d)=O_d(N^{2-1/d-\mu_d})
\]

for some `mu_d>0`, on these dimensions. The result gives neither `mu_d` of order `1/d` nor the constants needed at `N=Ch`. Such a d-colouring can exist only when `d` is a power of two, since each colour class must have size `h/(2d)`. This distinction prevents applying the partite theorem unqualified to every dimension.

## 5. Exact coefficient test at N=C2^d

Suppose a proposed **uniform** estimate, with nonnegative error term and actually valid at `N=Ch`, is

\[
 \operatorname{ex}(N,Q_d)\le a_d h^{1/d}N^{2-\alpha_d}+E_d(N).
\]

Since `h^(1/d)=2`,

\[
 \frac{\operatorname{ex}(Ch,Q_d)}{(Ch)^2}
 \le 2a_d C^{-\alpha_d}2^{-d\alpha_d}
       +\frac{E_d(Ch)}{(Ch)^2}.                         \tag{8}
\]

If `d alpha_d -> 2`, the leading term tends to `a/2` when `a_d->a`. Thus:

* `a<1/2`: there is a constant margin below the desired threshold, provided the error and validity range are controlled.
* `a>1/2`: no fixed C makes this estimate prove half-density embedding.
* `a=1/2`: the first-order terms decide; crossing below the limit is not necessary.

The coefficient directly in front of `N^(2-alpha_d)` is `A_d=2a_d`; its critical limiting value is **1**, not `1/2`.

More precisely, if

\[
 \alpha_d=2/d-\beta/d^2+o(d^{-2}),\qquad
 a_d=\tfrac12\exp(\kappa/d+o(d^{-1})),
\]

then the logarithm of four times the leading term in (8) is

\[
 \frac{\kappa+\beta\log2-2\log C}{d}+o(1/d).
\]

Therefore `C>exp(kappa/2) 2^(beta/2)` suffices, assuming `E_d(Ch)=o(N^2/d)` and uniform validity. An uncontrolled `o(1)` in the coefficient is not enough. For example, a residual factor `d^c` inside the d-th root forces a factor `d^(c/2)` in C.

An instructive **unproved benchmark** is to replace just the exponent in (5) by `2-2/(d+2)`:

\[
 \operatorname{ex}(N,Q_d)
 \stackrel{?}{\le}\tfrac12(h+2d^2)^{1/d}N^{2-2/(d+2)}.    \tag{9}
\]

At `N=Ch`, four times its right side divided by `N^2` equals

\[
 (1+2d^2/h)^{1/d}(4/C)^{2/(d+2)}.
\]

Every fixed `C>4` eventually makes this less than one, with margin of order `1/d`. Thus this exponent with a coefficient as good as Lee's really would give a linear result, if proved uniformly with a small enough error. **No such theorem has been found or proved here.**

A lower-order term in a fixed-d asymptotic can destroy this implication. At the critical coefficient, an additive `B_d N` needs `B_d=o(h/d)` for the displayed sufficient error condition; `B_d N^(3/2)` needs `B_d=o(2^(d/2)/d)`. An exponent gap of order `1/d` between two terms does not make their ratio tend to zero at `N=2^d`.

## 6. Two rigorous limitations on the proposed shape

### The exact exponent 2-2/d is impossible for fixed d

The cube has `h` vertices, `ell=dh/2` edges and automorphism group of order `h d!`. For `N>=h`, choose

\[
 p=((d-1)!)^{1/(\ell-1)}N^{-(h-2)/(\ell-1)}\le1.
\]

In `G(N,p)`, the expected number of cube copies is at most `N^h p^ell/(h d!)=pN^2/(2ell)`. Deleting one edge from each copy gives

\[
 \boxed{\operatorname{ex}(N,Q_d)\ge
 \frac12(1-1/N-1/\ell)((d-1)!)^{1/(\ell-1)}
 N^{2-(h-2)/(\ell-1)}.}                                \tag{10}
\]

But

\[
 \frac2d-\frac{h-2}{\ell-1}
 =\frac{4(d-1)}{d(dh-2)}>0\quad(d\ge2).
\]

Consequently no finite coefficient, even with arbitrary dependence on d, can give `ex(N,Q_d)=O_d(N^(2-2/d))` for all large N. An exponent such as `2-2/(d+2)` avoids this obstruction.

At `N=C2^d`, (10) gives `ex(N,Q_d)/N^2 >= 1/8-o(1)`. Therefore an upper bound in (8) with `d alpha_d->2` must have `liminf a_d>=1/4` (if it applies on this joint scale). This leaves a genuine interval between the random lower-bound obstruction `1/4` and the target `1/2`; known lower bounds here do not rule out a coefficient below the target for a sufficiently large fixed C.

### The desired coefficient cannot hold uniformly down to N=h

The graph `K_(h-1)` plus one isolated vertex is cube-free and has `(h-1)(h-2)/2` edges. If a bound with `d alpha_d->2` and no additive correction held at `N=h`, it would force `liminf a_d>=1`, not `1/2`. A successful theorem of the proposed form must restrict its validity range or include finite-size corrections.

More generally, for fixed `1<C<2`, the cube-free graph

\[
 K_{h-1}\ \dot\cup\ K_{N-h+1},\qquad N\sim Ch,
\]

has limiting edge ratio

\[
 \frac{1+(C-1)^2}{2C^2}>\frac14.
\]

Thus **any uniform half-density embedding constant must be at least 2 asymptotically**. This is not a Ramsey lower bound, because the complement of this construction contains cubes.

## 7. Exact square-lift calculation: a meaningful innovation target

Let `G=(A,B)` be bipartite, with part sizes a,b, `N=a+b`, and e edges. Define `S(G)` with vertex set `E(G)`. Distinct vertices `xy,x'y'` are adjacent when `x!=x'`, `y!=y'`, and `xy',x'y` are edges of G: they are opposite edges of a square.

The following are exact, proved statements:

1. `v(S(G))=e` and `e(S(G))=2 C_4(G)`.
2. `G` contains `Q_d` iff `S(G)` contains a copy of `Q_(d-1)` whose e-labelled vertices are pairwise vertex-disjoint edges of G. In the reverse direction, alternate the orientation of each pair according to the parity in `Q_(d-1)`.
3. With `c(x,x')=|N(x) intersect N(x')|`,

\[
 4C_4(G)=\sum_{x,x'\in A}c(x,x')^2
          -\sum_{x\in A}d(x)^2-\sum_{y\in B}d(y)^2+e.
\]

Two applications of Cauchy–Schwarz and the degree bounds give the all-size lower bound

\[
 e(S(G))\ge \frac{e^4}{2a^2b^2}-\frac{(N-1)e}{2}
          \ge\frac{8e^4}{N^4}-\frac{(N-1)e}{2}.          \tag{11}
\]

At positive density the error in (11) is negligible. For sparse fixed-d use, degree regularization or sharper degree-moment control may be needed; it cannot be ignored for uniform constants.

### Why the tempting induction fails

Take `G=K_(2,t)`, t>=4. It is `Q_3`-free. Nevertheless `S(G)` is `K_(t,t)` minus a perfect matching, so it contains many ordinary `Q_2`'s. Every such copy repeats one of the two original vertices in the small side. Thus `Q_d`-freeness does not imply ordinary `Q_(d-1)`-freeness of `S(G)`. Merely inserting `ex(e,Q_(d-1))` as an upper bound on `e(S(G))` is false, even up to any fixed multiplicative factor as t grows.

### Why this mechanism is still quantitatively interesting

If a **new overlap-controlled** argument permitted the leading-term comparison

\[
 e(S(G))\lesssim L_d A_{d-1}e^{2-\alpha_{d-1}}
\]

after accounting for concentration and endpoint collisions, then (11) and a maximum cut would give the formal bookkeeping

\[
 \alpha_d=\frac{2\alpha_{d-1}}{2+\alpha_{d-1}},\qquad
 A_d=2^{1-3/(2+\alpha_{d-1})}
          (L_d A_{d-1})^{1/(2+\alpha_{d-1})}.             \tag{12}
\]

Starting with `alpha_2=1/2` or `alpha_3=2/5`, the exponent recursion is precisely

\[
 \alpha_d=\frac2{d+2}.
\]

This is a structural explanation for the hoped-for near-`2-2/d` exponent, not a known extremal theorem. In this formal constant recursion, if `L_d->L` and the coefficients have a finite positive limit, then `A_d->L/2`; the half-density test needs `A<1`, so a limiting loss below 2 would leave a constant margin. At loss 2, first-order constants and error terms again become decisive.

The missing argument is not the definition of the auxiliary graph. It is a **balanced, endpoint-disjoint supersaturation/extension estimate** for the commuting-square pattern, with concentration alternatives and uniform constants. The correlated-matching lemma in generalized-cube proofs and the two-sided, codegree-controlled extension families in Bradač–Janzer–Sudakov–Tomon, **The Turán number of the grid**, arXiv:2203.05485, provide relevant models. The latter proves `ex(N,T square P)=Theta_(T,P)(N^(3/2))` for a tree T and a path P, each with at least one edge, not a theorem about higher-dimensional cubes. Direct tensor-power arguments do not by themselves preserve injectivity.

A productive attack would need to retain the *distribution* of square/half-cube extensions and bound the fraction using any forbidden original endpoint. Total square counts or total cube homomorphism counts alone do not give that. Removing one vertex from every colliding copy or treating all endpoint labels as generic colours incurs losses that the linear-scale calculation cannot afford.

## Source locations

* `/corpus/src/1307.1062/1307.1062.tex`: lines 217–225 (3-path bound), 337–355 (hexagon constants), 390–472 (cube proof and explicit bounds).
* `/corpus/src/1306.5167/FureSimSurvE_arXiv_v2_.tex`: lines 3625–3745 (reduction theorem), 4405–4421 (homomorphism/copy distinction).
* `/corpus/src/1502.02602/1502.02602.tex`: lines 819 onward (generalized cubes), especially 915–935 (explicit coefficient and threshold comparison).
* `/corpus/src/1806.02838/1806.02838.tex`: lines 229–271 (definition and theorem), 401–504 (correlated matchings proof).
* `/corpus/src/1505.04773/1505.04773.tex`: lines 172–198 and 244–401 (Lee's sharp density and defect theorems).
* `/corpus/src/0909.3271/0909.3271.tex`: lines 519–533 and 537–634 (explicit generic DRC bound).
* `/corpus/src/1507.00547/1507.00547.tex`: lines 183–277 (LLL density improvement).
* `/corpus/src/1910.11048/1910.11048.tex`: lines 35–38, 83–160 and 164–171 (little-o theorem, threshold audit, partite case).
* `/corpus/src/2203.05485/2203.05485.tex`: lines 22–51 (tree–path products and balanced extensions).

## Verification

`check_cube_extremal_investigation.py` checks the finite algebra, square-count identity and lower bound on all bipartite graphs with parts at most 3 and 4, explicit failed uncoloured lift, canonical disjoint lifts of cubes, exact Lee parameter inequalities, the Hamming-label partite construction, and the exponent/coefficient substitutions. These checks complement the proofs above; they are not evidence for the unproved estimate (9) or a proof of the Ramsey conjecture.
