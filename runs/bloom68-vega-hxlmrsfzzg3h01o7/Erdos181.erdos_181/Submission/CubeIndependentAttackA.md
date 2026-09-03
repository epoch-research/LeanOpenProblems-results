# Independent attack A: the Ramsey statement remains unresolved

## Status and scope

I have **not proved or disproved** the existence of an absolute constant
\(C\) such that every red/blue coloring of
\(K_{\lceil C2^d\rceil}\) contains an injective monochromatic ordinary
\(Q_d\). This report does not establish an improved Ramsey bound.

The rigorous result obtained here is a **quantitative obstruction to a
natural global entropy strategy**. It is substantially stronger than the
observation that unrestricted homomorphisms can repeat vertices:

* it applies even after one cube parity is embedded injectively;
* the images of the two parities are required to be disjoint;
* collisions are forbidden between all cube vertices at distance up to
  \(d/2-O(\sqrt{d\log d})\);
* both color graphs have all degrees \((1/2+o(1))N\);
* both colors actually contain planted, fully injective copies of \(Q_d\).

Nevertheless, in each color the proportion of fully injective maps in the
resulting relaxed homomorphism space can be at most
\(2^{-d2^d/4}\). Thus a dimension-uniform \(\exp(-O(2^d))\) conversion
from these relaxed counts to injective counts is false. The complete proof
of this obstruction is below. No claim of priority relative to the
literature is made.

Section 6 states one precise, capacity-sensitive inequality that would
suffice for the original conjecture. That inequality is **unproved** here
and is quantitatively stronger than the original existence statement.

The existing report archive was not read. `Spec.lean` was not edited.

## 1. Definitions and the obstruction theorem

Write
\[
 n=2^d,\qquad m=n/2,\qquad M=|E(Q_d)|=dn/2.
\]
The parity classes of \(Q_d\) are denoted by \(O\) and \(E\), each of
size \(m\). All counts below are counts of maps from this fixed, labeled
cube, not counts modulo automorphisms.

For a color \(c\), let \(I_c\) be the number of fully injective maps
\(\phi:V(Q_d)\to V(K_N)\) that take every cube edge to color \(c\).

For an integer \(r\ge 0\), let \(Z_c^{(r)}\) count maps taking all cube
edges to color \(c\), subject to the following additional conditions:

1. \(\phi|_O\) is injective;
2. \(\phi(O)\cap\phi(E)=\varnothing\);
3. if \(u\ne v\) and their Hamming distance is at most \(r\), then
   \(\phi(u)\ne\phi(v)\).

Repeats within \(E\) at larger Hamming distances are still allowed.
In particular, \(I_c\le Z_c^{(r)}\le Z_c^{(0)}\).

Define, using the natural logarithm inside the square root,
\[
 r_d=\left\lfloor \frac d2-
       \sqrt{\frac d2\log(8d)}\right\rfloor.
\]

**Theorem (failure of an \(O(n)\)-entropy conversion).**
Fix a real constant \(C>1\). For every integer
\[
 d\ge\max\left\{128,\lceil8\log_2(C+1)\rceil,
                        \left\lceil\frac{2}{C-1}\right\rceil\right\},
 \qquad N=\lceil C2^d\rceil,
\]
there is a red/blue coloring of \(K_N\) with all the following properties.

**(a) Nearly balanced degrees.** For every host vertex \(v\) and each
color \(c\),
\[
 \left|\deg_c(v)-\frac{N-1}{2}\right|\le \frac{N}{d}.
\]

**(b) Genuine cubes exist in both colors.** In particular,
\(I_{\mathrm R},I_{\mathrm B}>0\).

**(c) A large entropy gap remains even after the local injectivity
conditions.** For each color,
\[
 \boxed{\quad
 \frac{I_c}{Z_c^{(r_d)}}\le 2^{-dn/4}.
 \quad} \tag{1}
\]
Consequently the same upper bound holds with \(Z_c^{(0)}\) in the
denominator, and
\[
 I_{\mathrm R}+I_{\mathrm B}
 \le 2^{-dn/4}\bigl(Z_{\mathrm R}^{(r_d)}+
                         Z_{\mathrm B}^{(r_d)}\bigr).
\]

This theorem is emphatically **not a counterexample to the Ramsey
conjecture**: property (b) explicitly guarantees the desired copies.
It is a counterexample to a proposed way of deducing such copies from
large relaxed counts with only a dimension-uniform linear entropy loss.

## 2. An overlap estimate for a planted sparse graph

The following estimate lets us plant actual cubes without invalidating
an upper bound for the total number of injective copies.

**Lemma.** Let \(F\) be a graph on \(N\) vertices of maximum degree at
most \(\Delta\). For a map \(\phi:V(Q_d)\to V(F)\), let
\[
 a_F(\phi)=\bigl|\{uv\in E(Q_d):\phi(u)\phi(v)\in E(F)\}\bigr|.
\]
Here \(a_F\) counts cube edges, even when \(\phi\) is not injective.
If
\[
 \eta:=\frac{4d\Delta\sqrt n}{N}\le\frac12,
\]
then
\[
 \sum_{\phi:V(Q_d)\to V(F)}2^{a_F(\phi)}
 \le N^n\exp\left(\frac{24nd\Delta}{N}\right). \tag{2}
\]

**Proof.** Expand
\[
 2^{a_F(\phi)}
 =\prod_{uv\in E(Q_d)}
   \bigl(1+\mathbf 1_{\phi(u)\phi(v)\in E(F)}\bigr).
\]
For an edge subset \(J\subseteq E(Q_d)\), let
\(\rho(J)\) be the sum of \(|U|-1\) over its nontrivial connected
components with vertex sets \(U\). Choose a spanning tree in each such
component. Giving an image to each tree root and then to each successive
vertex shows that the number of maps taking all edges of \(J\) into
\(F\) is at most
\[
 N^{n-\rho(J)}\Delta^{\rho(J)}.
\]
Therefore
\[
 N^{-n}\sum_\phi2^{a_F(\phi)}
 \le\sum_{J\subseteq E(Q_d)}(\Delta/N)^{\rho(J)}. \tag{3}
\]

For every connected vertex set \(U\subseteq V(Q_d)\) of size \(k\ge2\),
put
\[
 w(U)=(\Delta/N)^{k-1}2^{e(Q_d[U])}.
\]
Grouping edge sets \(J\) according to their nontrivial connected
components bounds the right side of (3) by the sum of
\(\prod_Uw(U)\) over collections of disjoint connected sets. Dropping
disjointness can only increase that sum. Hence it is at most
\[
 \prod_U(1+w(U))\le\exp\left(\sum_Uw(U)\right). \tag{4}
\]

The cube edge-isoperimetric inequality gives
\[
 2^{e(Q_d[U])}\le k^{k/2}.
\]
In a graph of maximum degree \(d\), the number of connected vertex sets
of size \(k\) is at most \(n(4d)^{k-1}\): use a rooted ordered spanning
tree, at most \(4^{k-1}\) rooted ordered tree shapes, \(n\) choices
for its root, and at most \(d\) choices at each subsequent tree edge.
Every connected set has such a representation; overcounting is harmless.

Set \(b=4d\Delta/N\), so \(\eta=b\sqrt n\). Since
\(k^{k/2}\le k n^{(k-2)/2}\), we get
\[
\begin{aligned}
 \sum_Uw(U)
 &\le n\sum_{k=2}^n b^{k-1}k^{k/2}\\
 &\le nb\sum_{j=0}^{\infty}(j+2)\eta^j\\
 &=nb\frac{2-\eta}{(1-\eta)^2}
 \le6nb=\frac{24nd\Delta}{N}.
\end{aligned}
\]
Equations (3)--(4) prove (2). \(\square\)

## 3. Construction and the upper bound for injective maps

Set
\[
 s=\lfloor n/d\rfloor.
\]
Choose pairwise disjoint host sets
\[
 B,D,S_{\mathrm R},S_{\mathrm B}
\]
with
\[
 |B|=|D|=m,\qquad |S_{\mathrm R}|=|S_{\mathrm B}|=s.
\]
They fit because the dimension hypothesis gives
\[
 n+2s\le n+2n/d\le Cn\le N.
\]

We first plant edge-disjoint cubes of both colors on the **same** vertex
set \(T=B\cup D\). Identify \(T\) with \(\mathbb F_2^d\). The red
cube uses the usual coordinate differences \(e_1,\ldots,e_d\). The
blue cube uses the differences
\[
 a_i=e_i+e_{i+1}\quad(1\le i<d),
 \qquad a_d=e_1+e_2+e_3.
\]
The first \(d-1\) vectors form a basis for the even-coordinate-sum
subspace, and \(a_d\) has odd coordinate sum. Thus the \(a_i\) form a
basis of \(\mathbb F_2^d\), and the blue graph is also an injective
ordinary \(Q_d\). No \(a_i\) equals an \(e_j\), so the two cube edge
sets are disjoint. Each vertex of \(T\) has exactly \(d\) planted red
edges and \(d\) planted blue edges.

In addition prescribe the following colors:

* \(S_{\mathrm R}\)--\(B\) and \(S_{\mathrm B}\)--\(D\) are red;
* \(S_{\mathrm B}\)--\(B\) and \(S_{\mathrm R}\)--\(D\) are blue.

Color every other host edge independently red or blue with probability
\(1/2\). These prescriptions do not conflict. The planted cubes already
give property (b).

Let \(S=S_{\mathrm R}\cup S_{\mathrm B}\). Let \(F\) consist of the
two planted cube edge sets on \(T\), ignoring their colors. Thus
\(\Delta(F)=2d\).

Fix an injective map \(\phi:V(Q_d)\to V(K_N)\). At most \(2s\) cube
vertices map to \(S\), so at most \(2sd\) cube edges can map to a
prescribed edge incident to \(S\). At most \(a_F(\phi)\) more cube
edges map to prescribed edges in \(F\).

If any prescribed image edge has the wrong color, the probability that
\(\phi\) is monochromatic in color \(c\) is zero. Otherwise every
remaining required host edge is a distinct independent fair random
edge, because \(\phi\) is injective. In either case that probability
is at most
\[
 2^{-M+2sd+a_F(\phi)}.
\]
The lemma, with \(\Delta=2d\), therefore implies
\[
 \mathbb E I_c
 \le N^n2^{-M+2sd}\exp(48nd^2/N)
 \le N^n2^{-dn/2+2n}\exp(48d^2). \tag{5}
\]
Its hypothesis holds: \(N\ge n\), and for \(d\ge128\),
\[
 \frac{8d^2\sqrt n}{N}\le\frac{8d^2}{\sqrt n}\le\frac12.
\]
By Markov's inequality, for each color the probability of violating
\[
 I_c\le8N^n2^{-dn/2+2n}\exp(48d^2) \tag{6}
\]
is at most \(1/8\).

### Simultaneously nearly balanced degrees

Every host vertex has equally many prescribed red and blue incident
edges. At a hub vertex this follows from \(|B|=|D|\); at a vertex of
\(T\), it follows from \(|S_{\mathrm R}|=|S_{\mathrm B}|\) and from
the two planted cubes each having degree \(d\). Consequently
\[
 \mathbb E\deg_{\mathrm R}(v)=\frac{N-1}{2}
 \qquad\text{for every }v.
\]
The random part of each degree is binomial. Hoeffding's inequality and
a union bound give
\[
 \Pr\left(\exists v:
  |\deg_{\mathrm R}(v)-(N-1)/2|>N/d\right)
 \le2N\exp(-2N/d^2)<\frac14. \tag{7}
\]
For completeness, the last numerical inequality holds throughout our
range: \(x\mapsto2x\exp(-2x/d^2)\) is decreasing for
\(x\ge n\), and \(n=2^d\ge d^3\), so its value at \(N\ge n\) is
at most \(2^{d+1}e^{-2d}<1/4\).

The complement of the event in (7) implies property (a); the blue degree
assertion follows from
\(\deg_{\mathrm R}(v)+\deg_{\mathrm B}(v)=N-1\).

The sum of the failure probabilities for (6) in the two colors and
for (7) is less than \(1/2\). Fix a realization satisfying all three
requirements. It has (a), (b), and (6) in both colors.

## 4. Many locally injective relaxed maps, and completion of the proof

The lower bound for \(Z_c^{(r_d)}\) holds for every realization of the
random edges.

Consider the graph on the even cube vertices in which two distinct
vertices are adjacent when their Hamming distance is at most \(r_d\).
Its maximum degree is at most
\[
 L_d:=\sum_{j=0}^{r_d}\binom dj.
\]
The elementary binomial lower-tail bound gives
\[
 L_d
 \le n\exp\left(-\frac{2(d/2-r_d)^2}{d}\right)
 \le\frac{n}{8d}. \tag{8}
\]
Here the definition of \(r_d\) gives the second inequality.

Map \(O\) bijectively onto \(B\), in any of the \(m!\) ways. For the
red color, map \(E\) to \(S_{\mathrm R}\), properly coloring the
auxiliary graph just defined. A greedy ordering gives at least
\((s-L_d)^m\) choices. Each resulting map satisfies all three relaxed
injectivity conditions and takes every cube edge to a prescribed red
edge. The blue construction uses \(S_{\mathrm B}\) instead.

Since \(s\ge n/(2d)\), (8) gives \(s-L_d\ge n/(4d)\). The standard
factorial estimate \(m!\ge(m/e)^m\) now yields, for either color,
\[
 Z_c^{(r_d)}
 \ge m!\left(\frac n{4d}\right)^m
 \ge\left(\frac{n^2}{8ed}\right)^{n/2}
 =\frac{n^n}{(8ed)^{n/2}}. \tag{9}
\]

Combine (6) and (9), using \(N\le(C+1)n\). Then
\[
\begin{aligned}
 \frac1n\log_2\frac{I_c}{Z_c^{(r_d)}}
 \le{}&-\frac d2+\log_2(C+1)
       +\frac12\log_2(8ed)+2
       +\frac{3+48d^2/\log 2}{2^d}.
                                                        \tag{10}
\end{aligned}
\]
For \(d\ge128\),
\[
 \frac{3+48d^2/\log2}{2^d}\le1,
 \qquad
 \frac12\log_2d+\frac{11}{2}\le\frac d8.
\]
The first follows, for example, from
\(3+48d^2/\log2\le128d^2\le2^d\); the second holds at \(128\) and
the difference between right and left is increasing thereafter.
Since \(e<4\), all terms in (10) apart from
\(-d/2+\log_2(C+1)\) are at most \(d/8\).
Finally the hypothesis on \(d\) gives
\(\log_2(C+1)\le d/8\). Equation (10) is therefore at most \(-d/4\),
proving (1). \(\square\)

## 5. What the theorem rules out

### 5.1 No dimension-uniform birthday-type conversion

There cannot be constants \(C>1\) and \(K\) such that in every
coloring at this scale one of the two colors satisfies
\[
 I_c\ge e^{-Kn} Z_c^{(0)}.
\]
The same is false even if \(Z_c^{(0)}\) is replaced by the much smaller
\(Z_c^{(r_d)}\), and even under the degree conditions in the theorem.
Indeed \((d\log2)/4\) eventually exceeds any fixed \(K\).

The obstruction is global capacity, not a failure of the local
codegree calculation. The small sets \(S_c\) have size about \(n/d\)
and support enormous numbers of choices with repeats. Enforcing local
injectivity still leaves those choices plentiful, because the relevant
Hamming balls have size at most \(n/(8d)\). But a fully injective map
can use a small reservoir only once per host vertex.

### 5.2 An explicit relative-entropy lower bound

Let \(\mu_c\) be the uniform distribution on the maps counted by
\(Z_c^{(r_d)}\). For every distribution \(\nu\) supported on fully
injective monochromatic maps in color \(c\),
\[
 D(\nu\Vert\mu_c)
 =\log Z_c^{(r_d)}-H(\nu)
 \ge\log\frac{Z_c^{(r_d)}}{I_c}
 \ge\frac{\log2}{4}\,dn. \tag{11}
\]
Such distributions exist because the cubes were planted. Thus the
entropy cost is genuinely \(\Omega(d2^d)\), not merely an artifact
of an empty injective set.

### 5.3 Bounded vertex reweighting does not fix this example

Give each host vertex a positive weight in \([a,b]\), and weight a
map by the product of the weights of its \(n\) images, counting
multiplicities. The weighted injective-to-relaxed ratio is at most
\[
 (b/a)^n2^{-dn/4}.
\]
In particular a dimension-uniform bound on \(b/a\) cannot change the
conclusion. The same elementary argument applies to position-dependent
vertex factors, provided each factor lies in \([a,b]\).

These statements do not rule out deleting exceptional structures,
unbounded or nonlocal reweighting, or a genuinely capacity-aware
embedding argument. They only prohibit a specific, broad entropy
shortcut. No Ramsey lower bound or improved Ramsey upper bound follows
from them.

## 6. Exactly what is still missing: a Hall-capacity lower bound

Here is a precise sufficient analytic lemma for a global entropy route.
It is included to identify the missing input, **not** as a proved claim.

Fix a coloring and an injection \(f:O\hookrightarrow V(K_N)\). Put
\[
 X_f=V(K_N)\setminus f(O).
\]
For an even cube vertex \(u\), define its color-\(c\) list by
\[
 A_{c,f}(u)=
 \{x\in X_f:\ xf(v)\text{ has color }c
                    \text{ for every }v\in N_{Q_d}(u)\}.
\]
The uncapacitated parity partition function is exactly
\[
 Z_c^{(0)}=\sum_{f:O\hookrightarrow V(K_N)}
                     \prod_{u\in E}|A_{c,f}(u)|. \tag{12}
\]

To retain the global injectivity constraint, define instead
\[
 \operatorname{Cap}_c(f)
 :=\inf_{\substack{0<z_x\le1\\x\in X_f}}
   \frac{\displaystyle\prod_{u\in E}
                          \left(\sum_{x\in A_{c,f}(u)}z_x\right)}
        {\displaystyle\prod_{x\in X_f}z_x}.             \tag{13}
\]
An empty list makes this capacity zero. The denominator charges for
host-vertex capacity; it must not be omitted.

### Why positive capacity enforces injectivity

This elementary verification is useful because it prevents a
homomorphism/injection gap from being hidden inside the proposed lemma.

If the lists have distinct representatives \(g(u)\), the numerator in
(13) contains the monomial \(\prod_u z_{g(u)}\). After division by the
denominator this monomial is at least \(1\), since all unused
\(z_x\le1\). Thus \(\operatorname{Cap}_c(f)\ge1\).

Conversely, suppose Hall's condition fails on \(U\subseteq E\), and
write \(W=\bigcup_{u\in U}A_{c,f}(u)\), with \(|W|<|U|\).
Set \(z_x=t\) on \(W\) and \(z_x=1\) elsewhere. The expression in
(13) is at most
\[
 |X_f|^m t^{|U|-|W|},
\]
which tends to zero as \(t\downarrow0\). Hall's theorem therefore
shows
\[
 \operatorname{Cap}_c(f)>0
 \quad\Longleftrightarrow\quad
 f\text{ extends to a fully injective color-}c\ Q_d. \tag{14}
\]
Also, evaluating at \(z_x=1\) gives
\[
 0\le\operatorname{Cap}_c(f)
 \le\prod_{u\in E}|A_{c,f}(u)|.
\]

### Unresolved lemma HC: capacity-sensitive commonness

> There exist absolute constants \(C_0\ge4\) and \(K\ge0\) such that,
> for every \(d\ge1\), every \(N\ge\lceil C_0 2^d\rceil\), and every
> red/blue coloring of \(K_N\),
> \[
> \boxed{\quad
> \sum_{c\in\{\mathrm R,\mathrm B\}}
> \sum_{f:O\hookrightarrow V(K_N)}\operatorname{Cap}_c(f)
> \ \ge\ e^{-K2^d}\,2^{1-d2^{d-1}}(N)_{2^d}.
> \quad}                                                 \tag{HC}
> \]
> Here \((N)_n=N(N-1)\cdots(N-n+1)\).

The right side is positive and has the independent-fair-color
injective-count scale, up to an exponential loss linear in the number
of cube vertices. If (HC) were proved, (14) would immediately yield the
conjectured absolute Ramsey constant \(C_0\).

However:

* **No proof of (HC) is supplied.** Its universal validity is not
  established by this attack.
* It is a quantitative strengthening of the Ramsey existence statement;
  its failure would not by itself disprove the Ramsey conjecture.
* Positivity alone in (14) is just Hall's exact reformulation, not an
  advance on the original existence problem.
* A homomorphism inequality for (12) does not prove (HC). The capacity
  minimization is performed separately for each \(f\), inside the sum.
  Moving an infimum outside a sum gives an upper bound in the wrong
  direction for the desired conclusion.
* The theorem above rules out repairing this gap by asserting that
  enforcing injectivity costs only \(e^{-O(n)}\) relative to the
  uncapacitated count, even after strong local injectivity conditions.

Thus the genuinely unresolved task for this route is a direct global
lower bound that already accounts for all host-vertex capacities. The
present work establishes a rigorous obstruction to dropping those
capacities; it does not establish the needed lower bound.

## 7. Verification

The proof uses only elementary counting, cube edge-isoperimetry,
Markov's inequality, binomial concentration, and Hall's theorem. The
planted-copy step is covered by the proved overlap estimate rather than
by an unproved assertion about random hypercube embeddings.

As additional checks (not substitutes for the proof):

* the overlap expansion and its spanning-forest bound were exhaustively
  checked for \(Q_1\) and \(Q_2\) with several small host graphs;
* the numerical inequalities used at the dimension cutoff were checked
  through dimension 4096; their stated monotonicity arguments cover all
  larger dimensions;
* the two planted edge-disjoint cube constructions were checked in
  dimensions 3 through 12; their basis argument proves the claim for all
  larger dimensions;
* the construction's forced edge sets are disjoint, the random edges
  used by an injective map are distinct, and both planted copies persist
  in every realization.

**Bottom line:** original conjecture unresolved; no improved Ramsey
bound claimed. The completed result is the entropy-conversion
obstruction (1), including its stronger local-injectivity version and
relative-entropy consequence (11). The exact sufficient lemma still
unproved is (HC).
