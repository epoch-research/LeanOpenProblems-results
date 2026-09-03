# Rotation-fibre support capacity and sharp carrier-completion obstructions

## Status

**The amplification `E D^2 >= c n^5` and the sharp planar distinct-distance conjecture remain unresolved.**

The proved results here are:

1. A logarithm-free, zero-order **rotation-fibre support bound**, using endpoint coherence and the full GK tail rather than just its energy consequence.
2. A sharp actual-planar obstruction to obtaining supported translations by taking commutators of motions in one endpoint carrier. A square-grid carrier has `Theta(log n)` rich scales, but every commutator of two distinct non-quarter-turn members has **zero** surviving points.
3. Actual low-distance grids with arbitrarily many arbitrarily rich motions in one carrier, whose distinct pairwise quotients have **exactly one** surviving point. This makes the missing second endpoint literal.
4. A coherent finite-field comparison with flat colors, all the affine-group laws, and `E = Theta(n^3 log n)`, but amplification failing by a logarithm. Its GK tail constant is `Theta(log n)`, not bounded. A first-moment theorem shows that this failure of the tail is unavoidable, not a defect removable by a better sample.

A new, precisely stated **unproved** reverse support inequality would combine with result 1 to prove amplification. Its proof is the remaining gap; none of the obstructions is a counterexample to amplification for real planar sets. No claim of historical priority is made for the elementary inequalities.

No Lean files are changed.

---

## 1. Notation: keep the one-point motions in a fixed rotation fibre

Let `P subset C`, `n=|P|>=2`. Distances below are positive **squared** distances. Write

\[
S=\{|p-q|^2:p,q\in P,\ p\ne q\},\quad D=|S|,\quad
r_d=|\{(p,q)\in P^2:|p-q|^2=d\}|,\quad E=\sum_{d\in S}r_d^2.
\]

Put `M=n(n-1)`. Thus `sum_d r_d=M` and `E D>=M^2`.

Write a direct isometry as

\[
g_{u,t}(z)=uz+t,\qquad |u|=1,
\quad k(u,t)=|\{p\in P:up+t\in P\}|.
\]

For a fixed linear part `u`, define its **entire translation support**

\[
\sigma(u)=|P-uP|.
\]

This counts all motions in that fibre with at least one surviving point, not merely the motions appearing in the positive-edge table. Exact endpoint coherence gives

\[
\boxed{\sum_{t\in P-uP} k(u,t)=n^2,}\qquad
\boxed{n^2-\sigma(u)=\sum_t(k(u,t)-1).} \tag{1}
\]

Every ordered source/target point pair contributes to exactly one `t` for this `u`.

Define the actual rich-motion tail constant

\[
\kappa(P)=\max_{2\le j\le n}
\frac{j^2}{n^3}|\{g:k_g\ge j\}|. \tag{2}
\]

All isometries with at least two incidences form a finite set. GK, including the usual elementary treatment of translations, gives an absolute upper bound for `kappa(P)`.

For a real `T<n^2`, put

\[
\mathcal A_T(P)=\{u\in S^1:\sigma(u)\le T\}.
\]

This set is finite: if `sigma(u)<n^2`, (1) gives a two-point motion with linear part `u`, and such a linear part is the quotient of two equal-length nonzero differences of `P`.

### Group/double-coset formulation

Let `N` be the translation subgroup, `H` the rotations fixing zero, and `A={tau_p:p in P} subset N`. Then

\[
\sigma(u)=|A\rho_u A^{-1}|.
\]

Indeed, `tau_p rho_u tau_{-q}` has translation part `p-uq`. The positive double cosets `H tau_{q-p} H` are exactly the squared-distance classes. Thus the new support statistic is a finite *sandwich product support*, coupled to the actual double-coset distance palette. It is not the support of an invented numerical row.

---

## 2. Proved: zero-order rotation-fibre support capacity

### Theorem 2.1

For every finite `U subset S^1`, write `m=|U|` and `s=sum_{u in U} sigma(u)`. Then

\[
\boxed{m n^2\le s+2\sqrt{\kappa n^3s}.} \tag{3}
\]

Consequently, for `T<n^2`,

\[
\boxed{|\mathcal A_T(P)|\le
\frac{4\kappa n^3T}{(n^2-T)^2}.} \tag{4}
\]

In the useful range there is a better constant:

\[
\boxed{T\le n^2/2\quad\Longrightarrow\quad
|\mathcal A_T(P)|\le \frac{4\kappa T}{n}.} \tag{5}
\]

In particular, under GK, only `O(T/n)` rotation angles can have `|P-uP|<=T<=n^2/2`.

#### Proof

Set `B=kappa n^3`. Among the `s` motions in the selected fibres with positive incidence count, let `N_j` count those with `k>=j`. For `j>=2`,

\[
N_j\le\min(s,B/j^2),\qquad
mn^2-s=\sum_{j\ge2}N_j.
\]

The function `min(s,B/x^2)` is decreasing. Hence

\[
\sum_{j\ge2}N_j\le\int_1^\infty\min(s,B/x^2)\,dx
=\begin{cases}
B,&B<s,\\
2\sqrt{Bs}-s,&B\ge s.
\end{cases} \tag{6}
\]

In either case this is at most `2 sqrt(Bs)`, proving (3). Apply (3) to `U=A_T`, with `s<=mT`, to get

\[
m(n^2-T)\le2\sqrt{BmT}.
\]

Squaring proves (4).

If `T<=n^2/2` and `m>0`, then `mn^2-s>=s`. The first case of (6), which would give `mn^2-s<=B<s`, is impossible. Thus `B>=s`, and the second case gives the sharper estimate `mn^2<=2 sqrt(Bs)`. Therefore

\[
m^2n^4\le4Bs\le4BmT,
\]

which is (5). The case `m=0` is immediate. QED.

### Why using the whole tail matters

With only the energy bound, Cauchy in each fibre gives

\[
E_u:=\sum_t k(u,t)(k(u,t)-1)
\ge \frac{n^4}{\sigma(u)}-n^2.
\]

The disjoint linear-part fibres partition the equal-distance quadruples, so `sum_u E_u=E`. Consequently

\[
\boxed{|\mathcal A_T(P)|\le
\frac{ET}{n^2(n^2-T)}.} \tag{7}
\]

For `T<=n^2/2`, using `E=O(n^3 log n)` in (7) gives only `O(T log n/n)`. The full tail removes exactly that logarithm in (5).

This is a genuine additional use of coherent linear-part fibres and their one-point support. The edge table and its source-domain intersection moments do not specify (1) or `sigma(u)`.

---

## 3. A precise sufficient reverse inequality — not proved

The following is a concrete group/support target, not a theorem of this investigation.

### Proposed reverse support inequality (RS)

There exist absolute constants `C0>=1`, `c0>0` such that, whenever `C0 D^2<=n^2/2`,

\[
\boxed{
E(P)\,\big|\{u\in S^1:|P-uP|\le C_0D(P)^2\}\big|
\ge c_0 n^4.
} \tag{RS}
\]

Equivalently, the distance double-coset support should force at least `c0 n^4/E` linear parts with small *entire* sandwich support `|A rho_u A^{-1}|`.

### Proposition 3.1: RS would suffice for amplification

Assuming RS and the GK tail, there is an absolute `c>0` with `E D^2>=c n^5`.

#### Proof

In the range of RS, apply (5) with `T=C0 D^2`:

\[
c_0n^4\le E|\mathcal A_T|
\le\frac{4\kappa C_0}{n}ED^2.
\]

Thus `E D^2 >= c0 n^5/(4 kappa C0)`.

In the complementary range, `D>n/sqrt(2 C0)`, and ordinary Cauchy gives

\[
ED^2\ge M^2D\ge\frac{n^5}{4\sqrt{2C_0}},
\]

using `n>=2`. GK bounds `kappa` absolutely. Finally, its energy consequence `E<=C n^3 log n` would yield `D>=c' n/sqrt(log n)`. QED.

### What RS does and does not assume

* It is a zero-order support assertion about coherent point-set products. It is not entropy uniformization and uses no KL comparison.
* It does not say that rich motions form an approximate group.
* It does not force any fixed positive fraction of `P` to survive a nonidentity motion. A fibre with `sigma(u)<=C0 D^2` has average incidence count at least `n^2/(C0 D^2)`, which can be only logarithmic or smaller than any macroscopic scale.
* It would exclude a flat realization with `D=n/t`, `E~n^3 t`: RS requires `Omega(n/t)` such angles, whereas (5) allows only `O(n/t^2)` when `kappa=O(1)`.
* The missing direction is RS itself. Neither PSD composition nor a large second moment lets one reverse Cauchy and conclude that a whole fibre has small support. A set consisting of a long interval plus many generic isolated real points already has translation energy `Omega(n^3)` but difference support `Theta(n^2)`; it illustrates that elementary reversal failure, though its distance support is large and it does not refute RS.

Section 6 checks that square grids attain the scales in both (5) and RS. This is calibration, not a proof of RS for general `P`.

---

## 4. Proved: common-carrier commutators expand but need not survive

Fix distinct `p,q in P`. Parameterize the carrier `p -> q` by

\[
g_u(z)=u(z-p)+q,\qquad u\in S^1.
\]

Use `[g,h]=g h g^{-1}h^{-1}`.

### Theorem 4.1: a two-to-one commutator map

\[
\boxed{[g_u,g_v]=\tau_{(u-v)(q-p)}.} \tag{8}
\]

For `u!=v`, every fixed nonzero translation occurs for **at most two** ordered pairs `(u,v)` in the whole unit circle.

Consequently, for every finite angle set `U` of size `m`,

\[
|\{[g_u,g_v]:u,v\in U,\ u\ne v\}|\ge m(m-1)/2. \tag{9}
\]

For every nonnegative finitely supported function `F` on translations,

\[
\boxed{\sum_{u\ne v\in U}F((u-v)(q-p))
\le2\sum_{t\ne0}F(t).} \tag{10}
\]

In particular,

\[
\boxed{\#\{(u,v):u\ne v,\ k_{[g_u,g_v]}\ge1\}
\le2|(P-P)\setminus\{0\}|,} \tag{11}
\]

\[
\boxed{\sum_{u\ne v\in U}k_{[g_u,g_v]}\le2n(n-1).} \tag{12}
\]

For each positive squared distance `d`, there is also the color-resolved bound

\[
\sum_{\substack{u\ne v\in U\\|(u-v)(q-p)|^2=d}}
 k_{[g_u,g_v]}\le2r_d. \tag{13}
\]

#### Proof

The group law is `(u,t)(v,s)=(uv,t+us)`, so the commutator translation is `(1-v)t+(u-1)s`. Substituting `t=q-up`, `s=q-vp` gives (8).

Given a nonzero `t`, put `w=t/(q-p)`. A pair producing `t` has `v=u-w` with `|u|=|u-w|=1`. Two distinct unit circles meet in at most two points. This proves the multiplicity assertion and (9)–(10).

Take `F(t)=1_{t in (P-P)\{0}}` for (11). For (12), use

\[
\sum_{t\ne0}k_{\tau_t}=n(n-1).
\]

For (13), restrict that equality to `|t|^2=d`, when its right side is exactly `r_d`. QED.

### A support-normalized version

For the weights `W_g=sum_d a_{g,d}/r_d^2` in the supplied notes,

\[
\boxed{\sum_{u\ne v\in U}W_{[g_u,g_v]}
\le2(n-2)W_{id}.} \tag{14}
\]

To verify this, write `b(z)=|P intersect (P-z)|`. Equal-displacement ordered edges are exactly those related by translations, whence

\[
\sum_t a_{\tau_t,d}=\sum_{|z|^2=d}b(z)^2.
\]

For nonzero `z`, a finite set cannot be invariant under translation by `z`, so `b(z)<=n-1`. Removing `t=0`, whose contribution is `r_d`, gives

\[
\sum_{t\ne0}a_{\tau_t,d}\le(n-2)r_d.
\]

Apply (10), multiply by `r_d^{-2}`, and sum over `d` to obtain (14).

These are upper capacity inequalities, not the desired positive completion estimate. The next theorem shows that a positive completion estimate can fail as strongly as possible.

---

## 5. Proved: an entire low-distance grid carrier has unsupported commutators

Let

\[
P_L=\{a+ib:a,b\in\mathbb Z,\ |a|,|b|\le L\},
\qquad n=(2L+1)^2,
\]

and consider the carrier `0 -> 1`, namely `g_u(z)=uz+1`.

### Lemma 5.1

If distinct `u,v in Q(i)` have modulus one and `u-v in Z[i]`, then **both** `u` and `v` are Gaussian units. In particular, if at least one is not a Gaussian unit, then

\[
u-v\notin\mathbb Z[i]. \tag{15}
\]

#### Proof

Suppose `z=u-v` is a nonzero Gaussian integer. Then `|z|<=2`, so `|z|^2` is `1`, `2`, or `4`. The equation `|u-z|=|u|=1` gives `2 Re(u conjugate(z))=|z|^2`.

If `|z|^2=1`, rotating by a Gaussian unit makes one coordinate of `u` equal to `1/2`, and its other coordinate is `+/-sqrt(3)/2`, contradicting `u in Q(i)`.

If `|z|^2=2`, the two solutions are `u=z(1+i)/2` and `u=z(1-i)/2`, both Gaussian units. If `|z|^2=4`, the sole solution is `u=z/2`, again a Gaussian unit. In either case `v=u-z` is also a Gaussian integer of modulus one, hence also a Gaussian unit. QED.

### Theorem 5.2

Every motion in the `0 -> 1` carrier with `k_g>=2` has rational Gaussian linear part. If `g_u,g_v` are two distinct such motions whose linear parts are not in `{1,-1,i,-i}`, then

\[
\boxed{k_{[g_u,g_v]}=0.} \tag{16}
\]

This applies to the **whole** rich carrier after deleting four exceptional linear parts, not just to a selected subfamily.

#### Proof

A second incidence `x -> y`, with nonzero `x in P_L`, gives `u=(y-1)/x in Q(i)`. By (8), the commutator translates by `u-v`. Lemma 5.1 says this is not a Gaussian integer. No translation by a non-Gaussian-integer vector can take even one lattice point to another. QED.

### Richness is present on logarithmically many scales

Take coprime positive integers `a,b` of opposite parity and put

\[
s=a+ib,\qquad u=s/\bar s,\qquad h=|s|^2.
\]

In `Z[i]`, `gcd(s,bar s)=1`: a common divisor divides `2a` and `2ib`; coprimality leaves only the possible prime over two, and opposite parity excludes it. Therefore

\[
\boxed{g_u(z)\in\mathbb Z[i]\quad\Longleftrightarrow\quad \bar s\mid z.} \tag{17}
\]

Writing `z=bar s w`, the endpoint conditions become

\[
\bar s w\in P_L,\qquad s w+1\in P_L.
\]

All Gaussian integers `w` with `|w|<=(L-1)/sqrt(h)` satisfy them, while every possible `w` has `|w|<=sqrt(2)L/sqrt(h)`. Elementary lattice-point counting in disks yields, uniformly for `h<=c L^2`,

\[
\boxed{k_{g_u}\asymp L^2/h\asymp n/h.} \tag{18}
\]

For completeness, there are `Theta(M^2)` choices with `M<=a,b<2M`, `a` even, `b` odd, and `gcd(a,b)=1`. Möbius inversion gives their number as

\[
\frac{M^2}{4}\sum_{d\text{ odd}}\frac{\mu(d)}{d^2}+O(M\log M)
=\frac{2}{\pi^2}M^2+O(M\log M).
\]

The error follows by counting each parity-restricted multiple of an odd `d` as `M/(2d)+O(1)`; truncation beyond `2M` changes the main term by `O(M)`. The Euler product is positive. The rotations are distinct because the positive primitive slope `b/a` determines `s/bar s`. None is a Gaussian unit.

For dyadic `M` from a sufficiently large constant to `L/10`, these rotations have

\[
\#\{u\}\asymp M^2,\qquad k_{g_u}\asymp n/M^2.
\]

Each stratum contributes `Theta(n)` to `sum_u(k_{g_u}-1)`. The strata have only bounded overlap in dyadic richness scale. Thus the carrier has `Theta(log n)` scales of that size, and its total is at least `c n log n`.

There is also a matching upper bound. Write an arbitrary rational unit rotation in reduced Gaussian form `u=alpha/beta`, with equal numerator and denominator norms. Coprimality and `beta | alpha conjugate(alpha)` imply `beta | conjugate(alpha)`; equality of norms makes `alpha` an associate of `conjugate(beta)`. There are only `O(H)` possible rotations with `|beta|^2<=H`. A second incidence forces `|beta|^2<=2L^2`, by (17) in reduced form. Also

\[
k_{g_u}\le C(1+L^2/|\beta|^2).
\]

It follows that the number with `k_g>=k` is `O(n/k)`; the preceding construction supplies the reverse bound for `2<=k<=c_1n`, with absolute constants. In particular,

\[
\boxed{\sum_{u:k_{g_u}\ge2}(k_{g_u}-1)=\Theta(n\log n).} \tag{19}
\]

All the nonexceptional commutators still have zero incidence count. In fact the whole rich carrier has **exactly twelve supported ordered off-diagonal commutators**: the pairs of distinct Gaussian-unit linear parts. All four unit linear parts are rich when `L>=1`, and their twelve differences belong to `P_L-P_L`. Lemma 5.1 excludes every other pair, including a pair with just one nonunit. Their total surviving-point count is exactly `48 L^2-4`: the four axial differences of length two contribute `4(4L^2-1)`, and the four diagonal differences, each with multiplicity two, contribute `8(4L^2)`.

This also obstructs the natural carrier-richness weighting, not just uniform counting. With `w_u=k_{g_u}-1` on the full rich carrier, (19) gives `sum w_u=Theta(n log n)`, while its `O(n/k)` tail gives `sum w_u^2=O(n^2)`. Therefore the total ordered off-diagonal pair weight is `Theta(n^2 log^2 n)`. Only the twelve Gaussian-unit pairs survive, and their total weight is `Theta(n^2)`. The supported fraction for the product weights `w_u w_v` is consequently `Theta(1/log^2 n)`.

### Why this is a low-distance example

All squared distances of `P_L` are sums of two integer squares at most `8L^2`. One can prove `D(P_L)=o(n)` without invoking a quantitative asymptotic. If a prime `p=3 mod 4` divides a sum of two squares, it divides both coordinates, so that sum is zero modulo `p^2`. Thus `p-1` of the `p^2` residues are forbidden. For any fixed finite set of such primes, CRT bounds the upper density by

\[
\prod_p(1-1/p+1/p^2).
\]

This product tends to zero because `sum_{p=3 mod 4}1/p` diverges. One standard short verification of this divergence is to compare the Euler products of `zeta(s)` and `L(s,chi_4)` as `s` decreases to one: `L(1,chi_4)=pi/4` is finite and nonzero, and the difference of their logarithms is `2 sum_{p=3 mod4}p^{-s}+O(1)`. First let `L` grow with the finite prime set fixed, then enlarge that prime set. This proves `D=o(n)`.

The standard Landau–Ramanujan theorem gives the sharper familiar estimate

\[
D(P_L)\asymp n/\sqrt{\log n}. \tag{20}
\]

Here it applies in both directions: all distances are represented numbers up to `8L^2`, and every represented positive integer up to `L^2` occurs between zero and a point of the grid. The quantitative number-theoretic theorem in (20) is a cited classical input, not a new result proved here.

Thus even the actual low-distance configurations calibrating the sharp conjecture do not permit a positive commutator-support fraction in an arbitrary rich carrier.

---

## 6. Grid sharpness for the new angular support capacity

For `u=s/bar s` as above,

\[
P_L-uP_L=(\bar sP_L-sP_L)/\bar s.
\]

The numerator lies in a disk of radius `2 sqrt(2)L sqrt(h)` in `Z[i]`. Hence

\[
\boxed{\sigma(u)\le C n h.} \tag{21}
\]

There are `Omega(H)` such rotations with `h<=H`, by the primitive-pair count above. Taking `H=T/(Cn)` shows

\[
|\mathcal A_T(P_L)|\ge cT/n
\]

for `C_1n<=T<=n^2/2`, after adjusting fixed constants. Theorem 2.1 and GK give the reverse bound. Therefore

\[
\boxed{|\mathcal A_T(P_L)|\asymp T/n} \tag{22}
\]

throughout this range. The order in the proved capacity bound is sharp.

Also `E(P_L)=Theta(n^3 log n)`. For a self-contained lower bound up to constants, apply the construction of Section 5 to every carrier `p -> q` with `p,q` in the central half-size square. The same disk argument gives `Omega(n log n)` for each carrier. There are `Omega(n^2)` such ordered pairs, and exactly

\[
E=\sum_{p,q\in P}\ \sum_{g:g(p)=q}(k_g-1).
\]

This proves `E>=c n^3 log n`; GK supplies the upper bound.

Combining this with the classical quantitative palette count (20) and (22),

\[
T\asymp D^2\asymp n^2/\log n,
\quad |\mathcal A_T|\asymp n/\log n\asymp n^4/E.
\]

Thus both sides of the proposed RS have the correct order for square grids. Any subset of the grid inherits the upper bound (21) on its difference supports; in particular the mechanism does not require macroscopic motion overlap in a sparse sample. No universal RS assertion for arbitrary subsets is inferred from that inclusion alone.

There is a further support obstruction on lower richness scales. Since `|P_L-P_L|=O(n)`, (11) implies that a carrier subfamily of `m` motions has at most `O(n)` supported ordered commutators. At a grid carrier scale `m~n/k`, the supported fraction is at most `O(k^2/n)`, which tends to zero for `k=o(sqrt(n))`. The exact zero statement for the `0 -> 1` carrier is stronger still.

### A sparse-grid test of RS, without an overlap assumption

Here use `N=|P_L|` for the ambient grid size and `n=|P|` for a subset. Fix `eta>0`. If

\[
D(P)\ge\eta N/\sqrt{\log N},\qquad
T=C_0D(P)^2\le n^2/2,
\]

then, for sufficiently large `N`,

\[
E(P)|\mathcal A_T(P)|\ge c_{\eta,C_0}n^4. \tag{22a}
\]

This is a verified restricted case of RS, not a universal assertion about all grid subsets.

Indeed, support inclusion and (21) give `sigma_P(u)<=C N h`. The same primitive-angle count gives

\[
|\mathcal A_T(P)|\ge c T/N.
\]

Also, summing the elementary fibre estimate

\[
E_u(P)\ge n^4/(C N h)-n^2
\]

on dyadic denominator norms `h<=c n^2/N` yields

\[
E(P)\ge c\frac{n^4}{N}\log(n^2/N)
\]

when `n^2/N` grows. This is the restricted rotation-energy calculation already recorded in Section 6 of `lattice_energy_obstruction.md`, not a separately claimed new energy theorem. For clarity, each denominator stratum contains `Omega(h)` distinct angles; in this range each contributes at least `c n^4/(N h)`, so each stratum contributes `Omega(n^4/N)`.

The hypotheses imply `n^2/N>=2 C0 eta^2 N/log N`, so `log(n^2/N)~log N`. Multiplying the last two lower bounds gives

\[
E(P)|\mathcal A_T(P)|
\ge c C_0 n^4\frac{D(P)^2\log N}{N^2}
\ge c C_0\eta^2n^4,
\]

as asserted.

For example, retain each ambient grid point with probability `delta=(log N)^(-1/4)`. With probability tending to one, every difference vector in a fixed central fraction of `P_L-P_L` occurs in `P-P`: for each such nonzero vector there are `cN` vertex-disjoint candidate pairs, so its absence probability is at most `exp(-c delta^2 N)`; a union bound over `O(N)` vectors applies. The zero vector is automatic once the sample is nonempty. Landau–Ramanujan then gives `D(P)~N/sqrt(log N)` up to absolute factors, while `n~delta N`. Thus `D(P)=o(n)` and the hypotheses above hold. These are precisely a sparse regime in which a positive macroscopic motion-overlap assumption would be inappropriate; the support-fibre condition passes this test without making that assumption.

---

## 7. Proved: pairwise quotients can retain exactly one endpoint

### Theorem 7.1

For every pair of integers `m,K>=2`, there is a square grid `P_L` and distinct direct motions `g_1,...,g_m`, all carrying `0` to `1`, such that

\[
k_{g_j}\ge K\quad(1\le j\le m),
\]

but for every `j!=l`,

\[
\boxed{k_{g_j^{-1}g_l}=k_{g_lg_j^{-1}}=1,\qquad
k_{[g_j,g_l]}=0.} \tag{23}
\]

#### Proof

Choose a sufficiently large even integer `T` divisible by `100 m!`, and put

\[
\beta_j=Tj-i,\quad u_j=\bar\beta_j/\beta_j,
\quad g_j(z)=u_jz+1,\quad L=T^2/100.
\]

Every `beta_j` is coprime to its conjugate, since its real coordinate is even and its imaginary coordinate is `-1`.

The denominators `beta_j` are pairwise coprime in `Z[i]`. A common divisor of `Tj-i` and `Tl-i` divides `T(j-l)` and is coprime to `T`; it therefore divides `j-l`. But `j-l` divides `T`, because `T` is a multiple of `m!`. The common divisor must be a unit.

Thus the quotient rotation

\[
u_l/u_j=\frac{\bar\beta_l\beta_j}{\beta_l\bar\beta_j}
\]

is in reduced Gaussian form, with denominator `B=beta_l conjugate(beta_j)`. Its modulus is at least `T^2 j l`. The quotient `g_j^{-1}g_l` fixes zero; its lattice incidences require `B | z`. The quotient `g_lg_j^{-1}` fixes one; its lattice incidences require `B | (z-1)`. Every nonzero vector in `B Z[i]` has length at least `|B|>=T^2 j l`, whereas all `z` and `z-1` for `z in P_L` have length less than `2(L+1)`. Only the fixed point can survive. Both fixed points belong to `P_L`, so the counts are exactly one.

On the other hand, the disk count from (18) gives, uniformly in `1<=j<=m` once `T` is sufficiently large,

\[
k_{g_j}\ge c\frac{L^2}{|\beta_j|^2}
\ge c'\frac{T^2}{m^2}.
\]

Choose `T` larger if necessary to make this at least `K`. The commutator conclusion follows from Theorem 5.2. QED.

### Exact density mechanism

More generally, for two primitive coprime Gaussian denominators of norms `h_1,h_2`, the quotient fixing zero or one has denominator norm `h_1 h_2`. The same disk argument gives

\[
k_{\rm quotient}\asymp1+\frac{n}{h_1h_2}.
\]

When each original carrier is in the range `k_j~n/h_j`, this is

\[
k_{\rm quotient}\asymp1+\frac{k_1k_2}{n}. \tag{24}
\]

It can be exactly one when the first lattice step is longer than the diameter of the grid. This is a lattice arithmetic completion loss, not a failure of coherent composition. Indeed the source domains in the construction intersect only at zero, and the image domains intersect only at one.

For comparison, point-domain counting in any carrier gives, with `L_0=sum_g(k_g-1)`,

\[
\sum_{g\ne h}(|Q_g\cap Q_h|-1)
\ge L_0^2/(n-1)-L_0.
\]

The examples do not contradict it: their total coverage of the other source points is sparse. A proof of amplification must use more than absolute carrier richness or arbitrary pairwise completion.

---

## 8. A coherent flat finite-field boundary: energy is not the GK tail

This section concerns **finite-field norm colors, not Euclidean distances in the real plane**. It is not a countermodel to the joint hypotheses including an absolute GK tail.

Let `q` tend to infinity through odd prime powers with `q=3 mod4`. Identify `F_q^2` with `F_{q^2}` and use the anisotropic norm

\[
N(x+iy)=x^2+y^2.
\]

Let

\[
H=\{u:N(u)=1\},\quad |H|=q+1,
\qquad G=F_{q^2}\rtimes H.
\]

Translations commute, `H` is cyclic, and the affine law is exactly `(u,t)(v,s)=(uv,t+us)`. Nonzero norm colors are the double cosets of `H`. Every equal-norm ordered-edge correspondence determines the unique motion `u=(y'-x')/(y-x)`, `t=x'-ux`. Thus all the endpoint, inverse, composition, column, row, domain-moment, and real-valued Gram-counting identities in the supplied notes hold. Two circles with distinct centers have at most two common points, by subtracting their equations and solving a quadratic on a line.

### Theorem 8.1

There are subsets `P subset F_q^2` with `t=log q` for which, uniformly over all nonzero norm colors,

\[
n=(1+o(1))qt,\quad D=q-1,
\quad r_d=(1+o(1))qt^2,
\]

\[
E=(1+o(1))q^3t^4=(1+o(1))n^3\log n,
\]

\[
\boxed{\frac{ED^2}{n^5}=\frac{1+o(1)}t,\qquad
\kappa(P)=(1+o(1))t.} \tag{25}
\]

Every nonidentity motion has `k_g=(1+o(1))t^2`. Thus this is a coherent, almost perfectly flat `D~n/log n` model with the scalar GK energy bound; its rich-motion tail is worse by exactly a logarithm.

#### Proof

Retain each of the `q^2` points independently with probability `delta=t/q`. Then `n=(1+o(1))qt` with probability tending to one.

For any nonzero `d`, the full norm-`d` graph is `(q+1)`-regular on `q^2` vertices. If `xi_x` are the independent retention indicators, its ordered count is twice the sum of `xi_x xi_y` over unordered edges. Therefore

\[
\mu_d=\mathbb E r_d=q^2(q+1)\delta^2=(1+o(1))qt^2.
\]

Only pairs of graph edges sharing a vertex contribute covariance, so

\[
\operatorname{Var}(r_d)
\le C(q^3\delta^2+q^4\delta^3)
\le Cq(t^2+t^3).
\]

Set `epsilon=t^{-1/4}`. Chebyshev followed by a union bound over `q-1` colors bounds the probability of any relative error above `epsilon` by

\[
O\big(1/(\epsilon^2t)\big)=O(t^{-1/2})=o(1).
\]

Hence all colors are present and the stated uniform counts, energy, and amplification ratio follow.

For completeness, incidence counts also concentrate uniformly over all nonidentity motions. Such a motion has at most one fixed point. The undirected graph formed by the pairs `{x,gx}` has maximum degree two and can be decomposed into three matchings. A two-cycle contributes weight two to its edge; all other edges have weight one. Within each matching the variables `xi_x xi_y` are independent Bernoulli variables with parameter `delta^2`, and their weights are at most two. Each matching sum has mean at most `t^2` and variance at most `2t^2`. The elementary bounded-variable Bernstein/Chernoff estimate gives, for a fixed motion,

\[
\Pr(|k_g-\mathbb E k_g|>\epsilon t^2)
\le6\exp(-c\epsilon^2t^2),
\]

after absorbing its at most one fixed-point contribution. Its expectation is `t^2+O(delta)`. There are `q^2(q+1)-1=O(q^3)` such motions, and `epsilon^2t^2=t^{3/2}>>log q`. A union bound proves `k_g=(1+o(1))t^2` uniformly. The identity has `k=n`.

Taking the tail threshold near `t^2` gives `kappa>=(1-o(1))t`. Below the largest nonidentity count, `j^2 #G/n^3<=(1+o(1))t`; above it only the identity remains, contributing at most `1/n`. This proves the last assertion in (25). All the required high-probability events occur simultaneously. QED.

### The tail failure cannot be repaired within this ambient plane

For any `P subset F_q^2`, each ordered point pair has exactly `q+1` carriers, so

\[
\sum_{g\in G}k_g=(q+1)n^2,
\qquad |G|=q^2(q+1).
\]

The same layer-cake argument as (3), allowing the zero-incidence motions, gives

\[
(q+1)n^2\le q^2(q+1)+2\sqrt{\kappa n^3q^2(q+1)}.
\]

Thus, whenever `n>q`,

\[
\boxed{\kappa\ge
\frac{(q+1)(n^2-q^2)^2}{4n^3q^2}.} \tag{26}
\]

If `n/q` tends to infinity, the right side is asymptotic to `n/(4q)`. In particular no choice of `P` with `n~q log q` can have an absolute GK tail. An absolute tail forces `n=O(q)`.

This distinguishes three statements that must not be conflated:

* abstract tables plus an absolute GK tail are insufficient, as in the supplied notes;
* coherent affine-group laws plus the scalar energy bound are also insufficient in a field-independent formulation, as above;
* neither construction is a counterexample to coherent **real Euclidean** motions plus the absolute GK tail.

---

## 9. Remaining gap and verification boundary

The proved capacity theorem gives a sharp upper bound for the number of small-support rotation fibres. The desired amplification would follow from the **opposite, palette-sensitive direction RS**. No proof of that direction is supplied.

The common-carrier route cannot be completed by claiming that many rich motions have supported commutators, or that arbitrary distinct carrier motions have a second endpoint surviving in their quotient. The counterexamples above use actual Euclidean motions and actual low-distance square grids, not incoherent tables. They do not rule out an averaged argument over suitably selected different carriers, a carefully aligned family of common linear parts, or a new double-coset support theorem such as RS.

`verify_support_sensitive_motions.py` performs exact small-grid checks of the fibre identities, motion energy decomposition, tail-capacity inequalities, full-carrier commutator obstruction, color-resolved commutator capacities, and the quotient construction using Gaussian-integer denominators. It also checks the full finite-field table and first-moment identities on deterministic random samples. Small computations are sanity checks of the proofs, not evidence for an unproved universal RS.
