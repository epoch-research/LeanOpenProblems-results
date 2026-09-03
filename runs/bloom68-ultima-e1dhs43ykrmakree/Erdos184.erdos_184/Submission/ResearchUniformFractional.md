# Uniform-code fractional circuit cost

## Status: the unrestricted constant question is still open here

Let `Z <= F_2^E` be the cycle code of a finite binary matroid, with `1_E in Z`, and let

\[
 a(M)=2^{-\dim Z}\sum_{F\in Z}c_f(F).
\]

**This note does not prove or refute the existence of a universal finite `K` in `c(E) <= K a(M)`. In particular, it does not settle `K=4` or `K=8` for arbitrary binary matroids.** No graphic Erdős–Gallai proof is claimed.

The proved results are:

1. **An exact universal reduction and stronger lower bounds.** For every `K>=2`, the proposed universal inequality is equivalent to
   \[
   \boxed{c(M)-1\le K\bigl(a(M)-\tfrac12\bigr)}
   \tag{0.1}
   \]
   on all **nonempty** Eulerian binary matroids. A retained-anchor gluing preserves these shifted quantities additively and preserves regularity. Gluing Fano matroids gives
   \[
   |E|=6t+1,\quad \dim Z=3t+1,\quad
   c=t+1,\quad a=\frac{31t+32}{64}.
   \]
   Gluing `R10`s gives the regular analogue with `|E|=9t+1`, `dim Z=4t+1`, and `a=(47t+48)/96`. Consequently
   \[
   \boxed{K\ge\frac{64}{31}=2.064516\ldots\quad\text{for binary matroids},
   \qquad K\ge\frac{96}{47}\quad\text{even for regular matroids}.}
   \tag{0.2}
   \]
   These are proved full-family lower bounds, not numerical extrapolations. The binary threshold is stronger than the supplied synchronized-clique threshold. Repeated direct sums and these gluings cannot amplify beyond the maximum of **two** and their building blocks' affine ratios.

2. **A universal minimum-mean lemma, with exact equality case.** Every nonempty Eulerian binary matroid whose ground set is not a circuit satisfies `a>=63/64`. Equality holds precisely for the Fano matroid `F7`, with arbitrary nonempty series expansions of its elements. In particular `c=2` implies the sharp bound `c/a<=128/63`. This also proves the sharp constant `64/31` for the entire class generated from arbitrary `c<=2` matroids by direct sums and retained-anchor gluings. The lemma is a constant lower bound on `a`, **not** a bound growing with arbitrary `c`.

3. **A tight full-code mean sandwich for all `M(H,n)`.** Put `q=|V(H)|`, `h=|E(H)|`, `b=2^(n-2)`, and let `nu(H[S])` be the cycle nullity of the induced graph on a uniformly chosen vertex subset `S`. For `4|n`, `n>=8`, set `beta=8(n-2)/n^2`. Then
   \[
   \boxed{
   \frac q2-\frac{h}{4b}+\mathbb E_S\nu(H[S])
   \ \le a(M(H,n))\ \le
   \frac q2-\frac{(1-\beta)h}{4b}+\mathbb E_S\nu(H[S]).}
   \tag{0.3}
   \]
   In particular this **entire family**, not just a few examples, satisfies
   \[
   c=q\le \frac{2b}{b-1}\,a\le\frac{128}{63}\,a.
   \tag{0.4}
   \]
   For a tree the leading term is `q/2`; for a clique it is `h/4+1-2^(-q)`. Thus the old minimum-partition subunion obstruction does not persist under full-code averaging.

4. **A large-kernel theorem for recursive tensor coupling.** For the code
   \[
   Z_{H,K,n}=\langle D_v:v\in V(H)\rangle+(K\otimes U_0),
   \]
   write `d=dim K` and `s=dim U_0=n-2`. If `s>=d`, then
   \[
   \boxed{c(E)\le\frac{2}{\rho(d,s)}a(M),\qquad
     \rho(d,s)=\prod_{i=0}^{d-1}(1-2^{i-s}).}
   \tag{0.5}
   \]
   This implies `c<=7a` when `s>=d`, and `c<=4a` when `s>=d+1`. If the outer matroid `K` is connected, its actual full partition number collapses to **two** in this regime, regardless of its old partition number. More generally `c<=k+1`, where `k` is the number of outer matroid components.

5. **The hereditary maximum cannot be recovered from the mean within any constant.** There is an explicit family with
   \[
   \boxed{c(E)=2,\qquad a(M)\longrightarrow1,\qquad p(M)\ge t\longrightarrow\infty.}
   \tag{0.6}
   \]
   It also has Eulerian restrictions `W` with `a(M|W)=t/2`. This is an unbounded `p/a` and hereditary-monotonicity obstruction, **not** an unbounded `c/a` counterexample. Both the rare expensive restrictions and the collapse of the actual full minimum are proved.

All computations are targeted exact audits of these statements. The checker is **`/workspace/leanproject/Check.py`**. It uses only the standard library, reads the existing hereditary checker as a library without changing it or generating bytecode, and writes no files. The only new files for this investigation are that checker and this note. `Spec.lean` and all other existing files are preserved.

---

## 1. Definitions and elementary facts

Words are identified with supports. Circuits are nonzero support-minimal words of `Z`. For every `F in Z`,

\[
\begin{split}
 c(F)&=\min\{\text{number of circuits in a disjoint partition of }F\},\\
 c_f(F)&=\min\left\{\sum_C x_C:
       \sum_{C\ni e}x_C=1\ (e\in F),\quad x_C\ge0,
       \quad C\subseteq F\text{ a circuit}\right\}.
\end{split}
\]

Both values at zero are zero. The dual prices are **unrestricted in sign**. Every nonzero word has fractional value at least one. Also every disjoint circuit family is linearly independent, so

\[
 c_f(F)\le c(F)\le\dim Z_F\le\dim Z,
 \qquad Z_F=\{G\in Z:G\subseteq F\}.                 \tag{1.1}
\]

Complementation is a bijection of `Z`, and

\[
 c(E)\le c(F)+c(E\setminus F),\qquad
 c(E)\le 2\mathbb E_F c(F).                           \tag{1.2}
\]

There is no use of an XOR triangle inequality, or of an unproved average integrality-gap bound. For direct sums, **all three** of `c(E)`, `a`, and `p` are additive. Uniform sampling separates over the two code factors.

A nonempty matroid has `a>=1-2^(-dim Z)>=1/2`. Equality `a=1/2` occurs exactly when its whole ground set is a circuit: then `dim Z=1` and `c=1`.

---

## 2. Retaining one common anchor: exact factorization formulas

### 2.1 Construction and all circuits

Take nonempty Eulerian binary codes `Z_i` on `E_i`, and distinguish an element `p_i` of each. Replace these distinguished elements by one shared coordinate `p`, but require their word bits to agree. More explicitly the new code consists of

\[
 (g;F_1\setminus\{p_1\},\ldots,F_t\setminus\{p_t\}),
 \quad F_i\in Z_i,\quad 1_{p_i\in F_i}=g.
 \tag{2.1}
\]

The anchor `p` is **retained**. Deleting it is a different operation and invalidates the argument below. Since every `p_i` occurs in the all-ones word, each coordinate functional is nonzero, and

\[
 \dim Z_{\rm glue}=1+\sum_i(\dim Z_i-1).
\]

Its circuits are exactly:

* one circuit avoiding `p_i` in one factor, with all other traces zero;
* the anchor `p` together with one circuit containing `p_i` in **each** factor, with the `p_i` removed from their traces.

Indeed, an anchor-zero minimal word lives in one factor. An anchor-one word is nonminimal if any factor contains a nonzero subcycle avoiding its anchor. If a factor word is not a circuit, its circuit partition has exactly one anchor-containing part and at least one anchor-avoiding part. Conversely, if all factor words are circuits, no proper subword fits.

### 2.2 Exact costs of every word

For a word of (2.1),

\[
 \boxed{
 c_{\rm glue}=\sum_i c_i(F_i)-(t-1)g,\qquad
 (c_f)_{\rm glue}=\sum_i(c_f)_i(F_i)-(t-1)g.}
 \tag{2.2}
\]

For `g=0` these are direct-sum identities. For `g=1`, every integral partition has exactly one anchor-containing global circuit. Projecting its parts to each factor gives factor partitions, and conversely the unique anchor-containing parts of any factor partitions can be glued. This proves the integer identity.

For the fractional identity, the anchor equation forces total global-circuit mass **one**. Projecting any feasible primal gives feasible exact-load factor primals. If the global mass is one and the total local mass is `L`, the sum of projected costs is `t+L`, whereas the glued cost is `1+L`. This proves the lower bound. Conversely, in an optimal factor primal its anchor-containing circuits have coefficients summing to one. Couple these probability distributions, for example by their product, to form global circuits of total mass one. Keep the anchor-avoiding local circuits. This attains the lower bound.

There is also an explicit signed-dual proof: retain each factor's prices off its anchor and give the shared anchor price

\[
 y_p=\sum_i y^{(i)}_{p_i}-(t-1).
 \tag{2.3}
\]

A global circuit has price at most `t-(t-1)=1`; local circuit constraints are inherited. The anchor price can be negative.

### 2.3 Uniform sampling and the affine reduction

In a uniform glued word, `g` is fair, and conditional on `g` the factor words are independent and uniform in their indicated fibers. Each factor word therefore has its original unconditional uniform marginal. Thus

\[
 \boxed{
 c(E_{\rm glue})=1+\sum_i(c_i(E_i)-1),\qquad
 a(M_{\rm glue})=\tfrac12+\sum_i(a(M_i)-\tfrac12).}
 \tag{2.4}
\]

For `t` copies of one matroid this becomes

\[
 c_t=t(c-1)+1,\qquad a_t=t(a-\tfrac12)+\tfrac12.
 \tag{2.5}
\]

If `c<=Ka` holds universally, apply it to (2.5), divide by `t`, and let `t` tend to infinity. This yields (0.1). Conversely, for `K>=2`, (0.1) gives

\[
 c\le Ka+1-K/2\le Ka.
\]

The empty matroid is handled separately by `c=a=0`; the affine formulation is only for nonempty matroids. In particular, universal `K=4` is **equivalent** to

\[
 a(M)\ge (c(M)+1)/4
 \quad\text{for every nonempty Eulerian binary matroid}. \tag{2.6}
\]

This is a reformulation, not a proof of (2.6).

### 2.4 Fano zero-sum atoms give a stronger binary threshold

Represent `F7` by the seven distinct nonzero columns of `F_2^3`. Their sum is zero, the cycle dimension is four, and its nonzero words consist of seven 3-circuits, their seven 4-circuit complements, and the full 7-element word. There is no smaller nonzero word; a 4-word cannot contain a 3-word, since their difference would be a 1-word. Thus every proper nonzero word is a circuit.

Each element lies in four of the seven 4-circuits. Coefficient `1/4` on each of them and uniform dual price `1/4` certify

\[
 c(F7)=2,\qquad c_f(E(F7))=7/4,\qquad
 a(F7)=\frac{14+7/4}{16}=\frac{63}{64}.
 \tag{2.7a}
\]

Use the gluing of Section 2.1 on `t` copies. It gives connected simple binary matroids `S_t` with

\[
 |E(S_t)|=6t+1,\quad r(S_t)=3t,\quad\dim Z(S_t)=3t+1,
\]
\[
 c(S_t)=t+1,\quad c_f(E(S_t))=1+3t/4,\quad
 a(S_t)=(31t+32)/64.
 \tag{2.7b}
\]

Therefore

\[
 \frac{c(S_t)}{a(S_t)}=\frac{64(t+1)}{31t+32}
       \nearrow\frac{64}{31}.
 \tag{2.7c}
\]

These matroids have `F7` as a contraction minor: in the block representation (2.7) below, contract the nonanchor columns of all but one factor. Those columns span the other block row spaces, leaving the chosen Fano representation. Thus this is not a regular family. The next construction supplies a separate regular lower threshold.

### 2.5 Regularity and a sharper regular lower-bound family

The construction preserves regularity. To see this directly, write a TU representation of each factor as `[v_i | A_i]`, where `v_i` is its anchor column. A representation of (2.1) is

\[
 \begin{bmatrix}
 v_1&A_1&0&\cdots&0\\
 v_2&0&A_2&\cdots&0\\
 \vdots&&&&\vdots\\
 v_t&0&0&\cdots&A_t
 \end{bmatrix}.                                       \tag{2.7}
\]

This matrix is TU. A square minor not using the common column factors into block minors, or vanishes. In a potentially nonzero square minor using it, each block has at least as many selected rows as local columns, and the total excess is one. Exactly one block has one extra row. Expansion gives a product of block minors, using the anchor column just in that block, all in `{0,1,-1}`. Its binary kernel is precisely (2.1).

Use `R10` as the factor. Its explicit TU matrix is `[I_5|B]`, with

\[
 B_{i,i}=-1,\qquad B_{i,i-1}=B_{i,i+1}=1
 \quad(i\bmod5),
\]

and other entries zero. As in the existing notes, its 30 proper nonzero words are circuits, its whole fractional value is `5/3`, and its dimension is five. Hence

\[
 a(R10)=\frac{30+5/3}{32}=\frac{95}{96}.
\]

Gluing `t` copies gives a connected simple regular family `T_t` with

\[
\begin{split}
 |E(T_t)|&=9t+1,& r(T_t)&=5t,&\dim Z(T_t)&=4t+1,\\
 c(T_t)&=t+1,& c_f(E(T_t))&=1+2t/3,&
 a(T_t)&=(47t+48)/96.
\end{split}                                                     \tag{2.8}
\]

Simplicity follows from the circuit list. Connectedness follows since any element and the anchor lie in a global circuit, using connectedness of `R10`. Therefore

\[
 \frac{c(T_t)}{a(T_t)}=
 \frac{96(t+1)}{47t+48}\nearrow\frac{96}{47}.
 \tag{2.9}
\]

This supplies an asymptotic lower threshold **within regular matroids**, not within graphic matroids. It is not an unbounded-ratio family.

### 2.6 Why iterating this operation does not multiply a gap

For a non-circuit nonempty matroid define

\[
 R(M)=\frac{c(M)-1}{a(M)-1/2}.
\]

Gluing makes `R` a weighted average of the factors' `R`, with weights `a_i-1/2`. Circuit factors have zero numerator and denominator and cause no difficulty. For a direct sum of `t` nonempty factors,

\[
 c-1=\sum_i(c_i-1)+(t-1),\quad
 a-1/2=\sum_i(a_i-1/2)+(t-1)/2.
\]

Thus its affine ratio is a weighted average of the factor ratios and the number **two**. In particular, direct sums and retained-anchor gluings of `R10` and circuits all satisfy the sharp constant `96/47`. This is an exact obstruction to this particular recursive amplification strategy.

### 2.7 Universal minimum mean away from a single circuit

**Theorem.** If `E` is nonempty and is not a circuit, then

\[
 \boxed{a(M)\ge63/64.}                                \tag{2.10}
\]

Equality holds if and only if the code is obtained from the Fano cycle code by repeating coordinates, equivalently replacing elements by nonempty series classes.

Here is a proof by information sets and a small affine-geometry argument, not an enumeration of arbitrary matroids.

**Information-set lower bound.** If `F` is nonempty and is not a circuit, and `r=dim Z_F`, choose an information set `J` of `r` coordinates for `Z_F`. Every nonzero word of `Z_F` meets `J`. For every circuit `C subseteq F`, the nonzero complementary word `F\C` therefore meets `J`, so `|C intersect J|<=r-1`. Price `1/(r-1)` on `J` is feasible and gives

\[
 c_f(F)\ge r/(r-1).                                  \tag{2.11}
\]

If `F` is proper, then `r<=d-1`, where `d=dim Z`: an omitted coordinate supplies a nonzero linear equation, since `1_E in Z`.

There are `2^d-1` nonzero words, each of cost at least one. For `d>=6`, this already gives `a>=63/64`, strictly because the full non-circuit word has cost greater than one. If `3<=d<=5` and there is any **proper nonzero** non-circuit word, apply (2.11) to it and to the full word. This gives

\[
 a\ge1-2^{-d}+2^{-d}\left(\frac1{d-1}+\frac1{d-2}\right),
\]

which for `d=3,4,5` is respectively `17/16`, `95/96`, `379/384`, all strictly greater than `63/64`.

It remains to consider `2<=d<=5` when **every proper nonzero word is a circuit**.

**Affine model.** Merge coordinates that agree in every codeword. This preserves `d`, all circuit partitions, all fractional costs, and the uniform mean. Choose the all-ones word as one generator row. The distinct generator columns are then the points

\[
 (1,v),\quad v\in A\subseteq\mathbb F_2^{d-1},
\]

where `A` affinely spans the ambient space. Codewords are the supports of affine functions on `A`. The proper-word antichain condition is equivalent to `A` meeting every affine subspace of codimension two. Indeed, a missed two-bit pattern gives a strict containment between supports of two affine functions with independent linear parts. Conversely, any strict containment of proper supports gives a missed two-bit pattern; equal linear parts only give equal or complementary supports.

* `d=2`: affine spanning forces both points of `F_2`, giving two disjoint circuit classes and `a=1`.
* `d=3`: the codimension-two subspaces of `F_2^2` are points, so all four points occur. Proper circuits have size two, `c_f(E)=2`, and `a=1`.
* `d=4`: codimension-two subspaces of `F_2^3` are pairs of distinct points. Thus `A` omits at most one of the eight points. Every proper circuit has at most four coordinates, giving `c_f(E)>=7/4` and hence
  \[
  a=(14+c_f(E))/16\ge63/64.
  \]
  Equality requires seven points, which is exactly the Fano cycle code up to an affine change of coordinates. Its exact certificate was given in Section 2.4. With all eight points the mean is one.
* `d=5`: put `B=F_2^4\A`, `b_0=|B|`. The set `B` contains no affine plane, i.e. no four distinct points with xor zero. All its unordered-pair differences are therefore distinct nonzero vectors. Hence `binom(b_0,2)<=15` and `b_0<=6`. Each half of an affine hyperplane partition has only seven possible nonzero differences, so it contains at most four points of `B`. Every hyperplane consequently meets `A` in at most
  \[
  L=8-\max(0,b_0-4)
  \]
  points. Uniform prices `1/L` give
  \[
  c_f(E)\ge(16-b_0)/L\ge3/2.
  \]
  Equality in the last inequality is possible only for `b_0=4`. Those four points are affinely independent, or they would be an affine plane. They span a unique hyperplane; its complement is the **unique** hyperplane disjoint from `B`. Thus there is only one 8-element circuit. A primal of cost `12/8` would have to use only 8-element circuits and could not cover the other four points of `A`. Hence in fact `c_f(E)>3/2` and `a=(30+c_f(E))/32>63/64`.

This exhausts all dimensions. Reintroducing repeated coordinates gives exactly the claimed series-expansion equality cases. ∎

**Sharp two-atom construction class.** For every matroid with `c=2`, (2.10) implies

\[
 \frac{c-1}{a-1/2}\le\frac{64}{31}.
\]

By the weighted-average identities in Section 2.6, every matroid obtained from arbitrary `c<=2` building blocks by direct sums and retained-anchor gluings satisfies

\[
 \boxed{a\ge\frac{31c+1}{64},\qquad c\le\frac{64}{31}a.}
 \tag{2.12}
\]

The family `S_t` attains equality in the affine inequality, and its `c/a` tends to `64/31`. Thus neither repeated use of a two-atom gadget nor optimization over **all** two-atom base codes can make this construction class unbounded. Equation (2.12) is **not asserted for arbitrary binary matroids**.

---

## 3. Uniform averaging on the entire `M(H,n)` code

Here `H=(V,L)` is a connected simple bookkeeping graph without isolated vertices, `q=|V|`, `h=|L|`. The construction and all integer optima are proved in `ResearchHereditaryFollowup.md`. The following recalls the necessary structure and proves the new averaging statements.

### 3.1 Local code and complete word distribution

On `B=E(K_n)`, for even `n>=6`, let

\[
 U_0=\{\delta(T):|T|\text{ even}\},\quad s=\dim U_0=n-2,
 \quad A=\delta(\{0\}),\quad B'=1_B+A.
\]

Every local word has the unique form `x_u A+x_v B'+u`, `u in U_0`. For `n>=5`, every nonempty proper word of `Cut(K_n)+<1_B>` is a circuit. Briefly: nontrivial cuts and their complements are each antichains; two nontrivial cuts are not disjoint; and two cuts cannot cover `K_n`, since two shore bits would give a four-coloring.

The global code has trace

\[
 F|_{B_{uv}}=x_u A+x_v B'+u_{uv},
 \qquad x\in\mathbb F_2^V,\quad u_{uv}\in U_0.
 \tag{3.1}
\]

The labels recover `x`, so this parameterization is injective. **Uniform full-code sampling means that all `x_v` are independent fair bits and all `u_e` are independent uniform elements of `U_0`.** Write `b=|U_0|=2^(n-2)` and `S={v:x_v=1}`.

The circuits are local nonzero even cuts, and vertex-set circuits whose vertex set is connected in `H` and whose incident traces are proper local words of the prescribed labels. A full partition is specified by a partition of `V` into connected induced parts and has cost

\[
 q+\sum_T\bigl(|L(H[T])|-|T|+1\bigr).
\]

Consequently its actual minimum is `c(E)=q`.

For a general word let

* `P` be the full blocks: edges internal to `S` with `u_e=0`;
* `Q` be the nonzero even-cut blocks outside `S`: edges internal to `V\S` with `u_e!=0`;
* `k_0=cc(H[S])`, counting isolated selected vertices and setting `cc(empty)=0`.

Then

\[
 \mathbb E|Q|=\frac h4(1-1/b),\qquad
 \mathbb E|P|=\frac{h}{4b}.                            \tag{3.2}
\]

### 3.2 Pointwise fractional lower and upper certificates

The slightly stronger lower bound needed here is

\[
 \boxed{|Q|+k_0\le c_f(F)\le |Q|+k_0+\beta|P|.}
 \tag{3.3}
\]

For the lower bound, each `Q` block is its forced local circuit. The remaining support splits into nonempty disjoint regions, one per component of `H[S]`, and no contained circuit meets two such regions. Put price one on one element of every region and every `Q` circuit, and zero elsewhere. Every circuit has price at most one. This certifies `|Q|+k_0`, even when a region has full blocks. It is not an inference that `c_f` is monotone under arbitrary deletion.

For `4|n`, `n>=8`, put `m=binom(n,2)`, `a_0=2(n-2)`, `U=n^2/4`, and `beta=a_0/U`. For each component of `H[S]`, give mass one to vertex-set circuits keeping its frozen traces and independently taking complements of uniform two-vertex cuts in its full blocks. Each full-block element gets load `1-a_0/m`. Fill it with local uniform balanced-even cuts of mass `beta`; their load is `beta U/m=a_0/m`. Use each `Q` circuit with mass one. This is an exact-load primal of the upper value in (3.3), including when `F=E`.

For any even `n>=6`, the same statement holds if `U` is the largest even-shore cut size and `beta=a_0/U`. Then `beta<=1`. At `n=6`, `U=8` and `beta=1`. This variant is used for one small cyclic audit, not substituted silently into the main numerical constants.

### 3.3 Mean formula and cycle-nullity term

Set `Gamma(H)=E_S cc(H[S])`. Taking uniform means in (3.3) gives

\[
 L:=\frac h4(1-1/b)+\Gamma(H)
 \ \le a\le L+\frac{\beta h}{4b}.                    \tag{3.4}
\]

The graph identity `cc(J)=|V(J)|-|E(J)|+nu(J)` yields

\[
 \Gamma(H)=q/2-h/4+\mathbb E_S\nu(H[S]).
\]

This proves (0.3). In particular, for fixed `H`,

\[
 a(M(H,n))\longrightarrow q/2+\mathbb E_S\nu(H[S])
 \quad(n\longrightarrow\infty,\ 4|n).                \tag{3.5}
\]

This counts **all** `2^(q+h(n-2))` words via their uniform parameters, not the `2^q` old subunions.

For the uniform constant, use both

\[
 h/4+\Gamma(H)\ge q/2,\qquad
 \Gamma(H)\ge1-2^{-q}.
\]

Then

\[
 L=(1-1/b)(h/4+\Gamma)+\Gamma/b
 \ge (1-1/b)q/2+(1-2^{-q})/b.                          \tag{3.6}
\]

Dropping the last positive term gives (0.4). In the even-`n>=6` variant the corresponding universal family constant is `32/15` since `b>=16`.

For a tree, `nu(H[S])=0` for every `S`, so the interval is

\[
 q/2-(q-1)/(4b)\le a\le q/2-(1-\beta)(q-1)/(4b).
\]

For `H=K_q`, `Gamma=1-2^{-q}`, and the interval is

\[
 (1-1/b)h/4+1-2^{-q}
 \le a\le (1-1/b)h/4+1-2^{-q}+\beta h/(4b).
\]

Thus along the old obstruction `H=K_q,n=4q^2`, the full mean is asymptotic to `q(q-1)/8+1`, rather than remaining below two.

---

## 4. Tensor-coupled kernels: generic restrictions are integral

### 4.1 Construction and full-rank event

Keep `H`, `A`, `B'`, and `U_0` above. Let `K<=F_2^L` be any Eulerian outer binary code, with `d=dim K`. Replace the independent kernel variables by

\[
 Z=\langle D_v:v\in V\rangle+(K\otimes U_0),
 \tag{4.1}
\]

where `D_v` has the `A` or `B'` trace at its endpoint on each incident block. Quotient labels imply the direct parameterization `dim Z=q+sd`.

Choose an outer basis `a_1,...,a_d`. A uniform kernel tensor has the form

\[
 W=\sum_{j=1}^d a_j\otimes u_j,
 \quad u_j\text{ independent uniform in }U_0.
\]

The associated linear map `phi:F_2^d -> U_0`, `e_j -> u_j`, is injective with probability

\[
 \rho(d,s)=\prod_{i=0}^{d-1}(1-2^{i-s})\quad(s\ge d).
 \tag{4.2}
\]

Every outer generator column is nonzero, because `1_L in K`. On this event every block trace of `W` is nonzero. Consequently every block trace of `F=D_x+W` is a **nonempty proper** base word, for every vertex pattern `x`.

### 4.2 The multiplier lemma

Let

\[
 \mathcal B(K)=\{z\in\mathbb F_2^L:z\cdot a\in K\text{ for every }a\in K\},
 \tag{4.3}
\]

where the product is coordinatewise. Then `B(K)` consists exactly of the unions of the matroid components of `K`.

Indeed, if `C` is an outer circuit and `z in B(K)`, the word `z·C` is supported in `C`, so it is zero or `C`. Thus `z` is constant on every circuit, hence on every matroid component. Conversely, component indicators preserve `K`, since the cycle code splits over components. This argument also covers singleton loop components; there are no coloops because the code contains `1_L`.

### 4.3 Exact supported-subcode classification on the full-rank event

Let the outer components be `L_1,...,L_k`. Form a graph on these `k` component labels as follows: for every selected vertex `v in S={x_v=1}`, identify all labels of outer components containing edges incident with `v`. Let `k(S)` be the number of resulting equivalence classes. Isolated outer labels count.

On the injective event,

\[
 \boxed{c(F)=c_f(F)=k(S).}                            \tag{4.4}
\]

**Proof.** Any subcycle `F' subseteq F` must use each nonzero proper block trace either wholly or not at all. Thus it is described by a block indicator `z`. Its kernel part is `z·W`. Since the coordinate coefficient rows of `W` span all of `K` when `phi` is injective, membership of `z·W` in `K tensor U_0` is equivalent to `z in B(K)`.

By the multiplier lemma, `z` selects whole outer components. At a vertex with `x_v=0`, the new label is forced to zero. At a selected vertex, its new label must equal the selected/omitted status of **every** incident outer component. These are exactly the equivalences defining `k(S)`.

Hence the entire supported subcode consists of the unions of `k(S)` disjoint nonzero words, one per equivalence class. Each is a circuit and these are the **only** contained circuits. Their coefficients must all be one in any exact fractional partition. Equivalently, one price-one anchor per piece is a matching dual. This proves (4.4). ∎

This is the place where full-code randomness is used: not to assume an average integrality gap, but to identify a positive-probability set of restrictions whose **whole supported code** is Boolean on disjoint atoms.

### 4.4 Constant bound and collapse of the old minimum

Complementation sends `(x,phi)` to `(1+x,phi)`, so it preserves the injective event. For each such pair, (1.2) and (4.4) give

\[
 c(E)\le k(S)+k(V\setminus S).
\]

Averaging over `x` and then retaining just the injective event gives

\[
 a(M)\ge\rho(d,s)\,2^{-q}\sum_S k(S)
       \ge\rho(d,s)c(E)/2.
\]

This proves (0.5). The probability constants need no decimal approximation. For `s>=d`,

\[
 \rho(d,s)\ge\prod_{j=1}^d(1-2^{-j})\ge147/512>2/7.
\]

For `d>=3`, retain the first three factors and use
`product(1-x_j)>=1-sum x_j` on the tail, whose sum is at most `1/8`:
`(1/2)(3/4)(7/8)(7/8)=147/512`. The cases `d=1,2` are larger. If `s>=d+1`, retaining the first factor of the product starting at `j=2` gives

\[
 \rho(d,s)\ge(3/4)(1-1/4)=9/16>1/2.
\]

Thus `c<7a` for nonempty codes in the first regime, and `c<4a` in the second.

There is a stronger integral-collapse statement. Choose any injective map. For `x=0`, (4.4) gives `k` disjoint circuits partitioning `W`. For `x=1_V`, all outer component labels become connected, since `H` is connected. Thus `E\W` is a single circuit. Therefore

\[
 c(E)\le\min(q,k+1).                                 \tag{4.5}
\]

If `K` is connected, `W` and `E\W` are complementary circuits. The whole word is not a circuit, because it contains a proper nonzero `D_v`. Hence **`c(E)=2`**.

The condition here is `dim U_0>=dim K`, not merely `dim U_0>=c_K(L)`. The latter, weaker size condition in the prior note gave a hereditary lower witness but does not imply injectivity. The present argument does not settle coupling with `s<d`.

---

## 5. A rare hereditary witness can be arbitrarily larger than the mean

The preceding theorem makes a useful distinction between `a` and `p` rigorous.

### 5.1 Explicit family

For `t>=2`, take the connected outer code consisting of `t-1` synchronized `K_5` cut blocks from the supplied family:

\[
 K_t=\left(\bigoplus_{i=1}^{t-1}\operatorname{Cut}(K_5)\right)
          +\langle1_L\rangle.
\]

It has

\[
 h=|L|=10(t-1),\qquad d=4t-3,\qquad c_{K_t}(L)=t.
\]

For completeness, its local circuits are nontrivial cuts in one block, and its global circuits are proper cut complements in every block. Two such global circuits intersect. A full partition therefore has one global circuit and one complementary local cut per block, giving exactly `t` parts. Any two elements can be put into one global star-complement circuit, so the outer matroid is connected.

Let `H` be a path with these `h` edges, put `q=h+1`, and choose

\[
 s=2d,\qquad n=s+2=8t-4.
\]

Use the coupled code (4.1). Its dimension is

\[
 D_t=q+2d^2=10(t-1)+1+2(4t-3)^2,
\]

and its number of elements is `h binom(n,2)`. By Section 4, **`c(E)=2`**.

### 5.2 The uniform mean tends to one

On the injective event, the connectedness of `K_t` makes **every** vertex pattern a circuit, so the conditional fractional value is exactly one. The elementary union bound gives

\[
 1-\rho(d,2d)\le (2^d-1)2^{-2d}<2^{-d}.
\]

Off that event use (1.1), `c_f(F)<=D_t`. Also only the zero word has cost zero. Thus

\[
 \boxed{1-2^{-D_t}\le a(M_t)
       \le1+(D_t-1)2^{-d}.}                          \tag{5.1}
\]

Since `D_t=O(t^2)` and `d=4t-3`, this proves `a(M_t)->1`.

### 5.3 An exact expensive restriction

Let `A_1,...,A_t` be the displayed minimum circuit partition of `L` in `K_t`, and choose linearly independent `u_1,...,u_t in U_0`. This is possible since `s=2d>=t`. Define

\[
 W_{\rm col}=\sum_{i=1}^t A_i\otimes u_i.
 \tag{5.2}
\]

It has a nonzero proper `00` trace in every block. A contained cycle has each trace either zero or the original `u_i`, and all its quotient labels vanish. Applying a linear functional on `U_0` that picks out `u_i` shows that the selected block indicator inside `A_i` must be an outer word supported in the circuit `A_i`. It is therefore zero or all of `A_i`.

Consequently the entire supported code of (5.2) is the span of the **disjoint** circuits `A_i tensor u_i`. In particular

\[
 c_f(W_{\rm col})=c(W_{\rm col})=t,\quad
 a(M_t|W_{\rm col})=t/2,\quad p(M_t)\ge t.
 \tag{5.3}
\]

Equations (5.1)–(5.3) prove unbounded `p/a` and unbounded `a(M|W)/a(M)`. They do **not** refute `c(E)<=Ka(M)`: here `c(E)/a(M)->2`. This is also a structural reason not to count a retained old partition as the new full optimum after kernel coupling.

---

## 6. Exact verification and its limits

Run from `/workspace/leanproject`:

```sh
python3 Check.py
```

The checker uses integer Gaussian elimination, exact rational primal/dual certificates, and complete enumeration only on the specified small codes. There are no random graph tables, numerical LP tolerances, or inferred optima from a failed search.

### Fano, the minimum-mean lemma, and retained-anchor gluing

* It reconstructs the 16-word Fano code and verifies exact fractional primal/dual pairs for every word, obtaining `a=63/64`. For two retained-anchor Fano copies it independently checks all **128 words and 63 circuits**, every integer optimum, and every exact fractional primal/dual pair. It obtains `c=3`, `c_f(E)=5/2`, and `a=47/32`.
* For the dimension-five part of the minimum-mean proof, it exhaustively checks the plane-free subsets of the **single 16-point affine geometry**. Their counts by size `0,...,6` are `1,16,120,560,1680,2688,448`. Every hyperplane bound and the unique-largest-circuit obstruction in the size-four equality case is verified. This is a targeted finite-geometry audit of the proved lemma, not a search over random graphs or matroids.
* It verifies all **3,002** nonempty square minors of the displayed `R10` matrix are `0,1,-1`.
* It reconstructs the 32-word base code and all its circuits and verifies exact fractional primal/dual pairs for every word.
* For two glued copies it reconstructs **all 512 words and 255 circuits** on 19 elements, independently computes all integer minima, and verifies the glued exact rational primal/dual pair for **every word**. It obtains
  \[
  c=3,\qquad c_f(E)=7/3,\qquad a=71/48.
  \]
  The full-word dual has shared-anchor price `-2/3`; it is not a nonnegative-cover certificate.

### Independent-kernel full means

For every word in each of the following codes, it checks the new lower dual against **all** contained circuits and checks the exact loads of the upper primal:

| `H,n` | all words | all circuits | exact `c(E)` | certified interval for `a` |
|---|---:|---:|---:|---:|
| `P_3,8` | 32,768 | 16,383 | 3 | `[191/128, 767/512]` |
| `K_3,6` | 32,768 | 15,708 | 3 | `[101/64, 13/8]` |

These intervals are not mislabeled as exact optima. The `n=6` row uses the explicitly stated even-shore variant. Their endpoints equal the independently counted uniform formula (3.4).

### Coupled kernels

* For `H=P_5`, `K=<0011,1100>`, and `n=6`, it reconstructs the complete **8,192-word** code. The actual full minimum is three. It checks **all 6,720 full-rank-event words** by supported-subcode rank: the only atoms are the predicted disjoint pieces. The event probability is `105/128`, its exact conditional mean is `3/2`, and its contribution to the unconditional mean is `315/256`.
* It separately enumerates small linear maps to check the full-rank counting formula and checks the rational constants against their proved product bounds.
* For the rare-witness family at `t=3`, it constructs the **3,800-element, dimension-183** code and verifies by exact supported-subcode ranks a complementary circuit pair and the three-colored restriction with exactly eight subwords. It certifies
  \[
  c(E)=2,\qquad p\ge3,\qquad a\le347/256.
  \]
  It does **not** enumerate `2^183` words or assert the exact value of `p` or `a`. The infinite-family conclusions use the proofs in Section 5.

The checker fingerprints all **231 pre-existing project files outside `.lake`** before and after execution, excluding the two permitted new files, and compares against the starting fingerprint. The `.lake` dependency/cache tree is not part of this fingerprint and was not modified or used. The protected specification hash is

```
429c12b5b471b0098bbc8ded194d7c22a4b99c083841d9a549f2bc3cc87dafde
```

---

## 7. Remaining mathematical burden

The following are proved, not conjectural: the gluing identities and affine equivalence; the binary lower threshold `64/31` and regular lower threshold `96/47`; the universal non-circuit minimum mean `63/64` with Fano equality; the sharp bound for the two-atom construction class; the full mean sandwich and constant bound on all `M(H,n)`; the large-kernel bound and connected-outer collapse; and the explicit unbounded `p/a` family with bounded `c/a`.

What remains unresolved is **whether every finite Eulerian binary code satisfies any finite constant bound `c(E)<=Ka(M)`**, equivalently the affine bound of Section 2. No unbounded full-family `c/a` example was obtained.

In particular:

* No reverse comparison `p<=C a` is available: Section 5 disproves every such constant comparison.
* The positive-probability integral-restriction event in Section 4 is a proved property of that coupling regime, not a universal property of codes. Even for direct sums of `R10`, the probability that **both** complementary restrictions have integral fractional optima is `(15/16)^t`, tending to zero.
* The prior `p<=graphic rank` input still combines with a hypothetical universal `c<=Ka` because `a<=p`, but neither that input nor the results here supply the missing universal inequality.

The lower-dimensional coupled-kernel regime and arbitrary binary codes remain genuine open parts of this investigation. No unsupported average rounding lemma is assumed.
