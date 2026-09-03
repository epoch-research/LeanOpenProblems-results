# Eventual-hole contradiction attempt: proper-divisor matching and periodic factorial cofactors

## Outcome

**No contradiction to an arbitrary eventual missing band was obtained. Erdős #5 is not proved or disproved here.**

This attempt uses a different inverse arithmetic mechanism: allocate the prime powers of a binomial coefficient to the actual integers in a forced composite block, and then try to exhaust their supply of proper prime divisors. It does not use a prime-pair lower bound, a relative parity estimate, or the admitted declarations in `Submission/Spec.lean`.

The principal proved consequence is the following. Fix

\[
0<\delta<\min(B-A,1/4),\qquad A<c<B-\delta,
\]

put `L=log X`, `H=floor(delta L)`, `u=floor(cL)`, and let `M=|E_X|`. For every sufficiently large `X`, the eventual-hole hypothesis gives, for **every** `p in E_X`, a canonical factorization

\[
p+u+i=\alpha_i(p+u)\,\beta_i(p+u),\qquad 1\le i\le H,
\tag{O1}
\]

with all of the following properties:

* `alpha_i>1`, and the `alpha_i` are pairwise coprime within each block.
* With `Q_H=lcm(1,...,H)`, every `beta_i` divides `Q_H`, and
  \[
  \prod_{i=1}^H\beta_i=H!,\qquad
  \prod_{i=1}^H\alpha_i=\binom{p+u+H}{H}.
  \tag{O2}
  \]
* The **whole cofactor vector** `(beta_1,...,beta_H)` is periodic in its argument with period
  \[
  W_H=Q_H\prod_{\substack{q\le H\\q\text{ prime}}}q
      =X^{2\delta+o(1)}.
  \tag{O3}
  \]
  In particular this period is smaller than a fixed power of `X` below `X^(1/2)`.
* Choosing a prime divisor of each `alpha_i` gives `H` **distinct proper prime divisors** of the original composite integers. Each is smaller than the anchor `p`. Their CRT residue for the anchor is reduced.

There is also a quantitative consequence, not just a representation. Fix an integer `D>=2`. Let `G` count positions in these disjoint blocks for which

\[
\beta_i\le H^D,\qquad P^-(\alpha_i)>H,
\qquad \omega(\alpha_i)\ge2.
\]

Here `omega` counts distinct prime factors. We prove

\[
G\ge
\left(1-\frac1D-o(1)\right)MH
 -(D+o(1))\frac{X\log H}{L}.
\tag{O4}
\]

Each counted position supplies two distinct proper prime factors greater than `H`, and no such factor can occur at another position of the same block. A finite, non-asymptotic version is given in (24). No lower bound on `M` is assumed in this inequality. For example, if `M >> X loglog X/log^2 X` with the ratio tending to infinity, it yields `G >= (1-1/D-o(1))MH`. This last example is **not** an assertion that the hole hypothesis supplies such an `M`.

A further exact lemma identifies a substantial source of false prime outputs: if `n=kq`, `q>H` is prime, and `2<=k<=sqrt(H)`, then **in any containing length-`H` block** its canonical allocated part is `q` and its cofactor is `k`. Such actual composites number `(1/2+o(1))X log H/L` in `(X,2X]`. This quantifies, rather than merely names, one failed route to a contradiction.

The elementary binomial allocation underlying (O1)–(O2) is known; it is re-proved below. The periodic compression, exact CRT discrepancy calculation, universal small-cofactor lemma, and inventory inequality are the additional calculations of this attempt. No claim of literature priority is made.

---

## 1. Exact passage from the hole to the integer blocks

Assume that for some `0<a<b` and all sufficiently large global prime indices `n`,

\[
p_{n+1}-p_n\notin(a\log n,b\log n).
\]

Choose `a<A<B<b`. Uniformly for primes `X<p<=2X`, ordinary PNT gives

\[
\log\pi(p)=L-\log L+O(1),\qquad L=\log X.
\tag{1}
\]

Consequently, for sufficiently large `X`, a gap in `(AL,BL)` would be in the forbidden index-normalized band. Thus

\[
E_X=\{p:X<p\le2X-BL,\ p\text{ prime},\ p^+-p>AL\}
\]

has `p^+-p>=BL` at every member. In particular every integer strictly between `p` and `p+BL` is composite. This is an exact statement, not an asymptotic zero.

For the fixed `delta,c,H,u` above, all offsets `u+1,...,u+H` lie strictly between `AL` and `BL` for large `X`. Therefore

\[
I_p=\{p+u+1,\ldots,p+u+H\}\subset(X,2X]
\tag{2}
\]

consists entirely of composites. These blocks are disjoint: consecutive members of `E_X` are separated by at least `BL`, whereas `H<BL`.

Let `m=p+u`. PNT at the much smaller scale `H` gives

\[
\log Q_H=\psi(H)=(1+o(1))H=(\delta+o(1))L<L.
\tag{3}
\]

Hence `m>Q_H`. This strict inequality is the only height condition in the elementary allocation theorem.

---

## 2. Exact prime-power allocation, including the cofactor bound

### Lemma 1: canonical factorial allocation

For integers `m>=0`, `H>=2`, define a canonical allocation as follows. For every prime `q`, put

\[
T_q=\max_{1\le i\le H}v_q(m+i),\qquad
s_q=\lfloor\log_q H\rfloor,
\]

where `s_q=0` for `q>H`. Let `i_q` be the **first** index attaining `T_q`, and put

\[
e_q=v_q\binom{m+H}{H},\qquad
\alpha_i=\prod_{q:i_q=i}q^{e_q},\qquad
\beta_i=\frac{m+i}{\alpha_i}.
\tag{4}
\]

Factors with `e_q=0` do not affect the product. Then these are positive integers and

\[
\gcd(\alpha_i,\alpha_j)=1\ (i\ne j),\quad
\prod_i\alpha_i=\binom{m+H}{H},\quad
\prod_i\beta_i=H!,\quad \beta_i\mid Q_H.
\tag{5}
\]

If `m>Q_H`, then every `alpha_i>1`.

### Proof

For `j>=1`, set

\[
c_{q,j}(m)=
\left\lfloor\frac{m+H}{q^j}\right\rfloor
-\left\lfloor\frac m{q^j}\right\rfloor
-\left\lfloor\frac H{q^j}\right\rfloor.
\]

Each `c_{q,j}` is `0` or `1`, and Legendre's valuation formula gives

\[
e_q=\sum_{j\ge1}c_{q,j}(m).
\]

Since a block of `H` consecutive integers contains a multiple of `q^(s_q)`, we have `T_q>=s_q`. For `j>s_q`, the interval has length less than `q^j`. It contains exactly one multiple of `q^j` if `j<=T_q`, and none otherwise. Therefore, with

\[
C_q(m)=\sum_{j=1}^{s_q}c_{q,j}(m),\qquad 0\le C_q\le s_q,
\]

we have the exact formula

\[
e_q=T_q-s_q+C_q(m),\qquad 0\le e_q\le T_q.
\tag{6}
\]

Thus the assigned prime power divides `m+i_q`, proving that the `beta_i` are integers. Different `alpha_i` receive disjoint sets of primes. Their product is the binomial coefficient, so their complementary product is exactly `H!`.

At the assigned index,

\[
v_q(\beta_{i_q})=T_q-e_q=s_q-C_q\le s_q.
\tag{7}
\]

Every other index has valuation at most `s_q`: two integers in the block cannot both be divisible by `q^(s_q+1)>H`. For `q>H`, equation (6) gives `e_q=T_q`, and the sole occurrence of that prime is entirely allocated to its index. Thus all `beta_i` have prime-power exponents bounded by those of `Q_H`. This proves `beta_i | Q_H`, which is stronger than merely `beta_i | H!`.

Finally, if `m>Q_H`, every `m+i>Q_H` has a prime-power divisor `q^t>H`; otherwise it would divide `Q_H`. That prime-power divisor occurs at a unique index of the block. Formula (6) gives `e_q>=1` at that index, so its `alpha_i>1`. ∎

### Corollary 1: exact proper-divisor matching rank

Make a bipartite graph with left vertices `1,...,H` and right vertices the primes. Join `i` to the **proper** prime divisors of `m+i`, namely primes `q<m+i` dividing it. If `m>Q_H`, its maximum matching size is exactly

\[
\nu(m,H)=H-\#\{1\le i\le H:m+i\text{ is prime}\}.
\tag{8}
\]

Indeed prime positions have no neighbors. At every composite position choose a prime divisor of its nontrivial `alpha_i`; it is proper, and pairwise coprimality makes all the chosen primes distinct. This saturates every composite position.

Thus, on every forced block (2), the proper-divisor graph has a perfect matching. This conclusion requires neither a presumed supply of power-rough endpoints nor a density hypothesis on `E_X`.

---

## 3. First attempted contradiction: overdetermined reduced CRT codes

Choose canonically

\[
q_{p,i}=P^-(\alpha_i(p+u)),\qquad
\mathcal Q(p)=\prod_{i=1}^Hq_{p,i}.
\]

Because every `p+u+i` is composite,

\[
q_{p,i}\le\frac{p+u+i}{2}<p.
\tag{9}
\]

The prime anchor also gives

\[
q_{p,i}\nmid(u+i),
\tag{10}
\]

since otherwise it would divide `p`. The simultaneous congruences

\[
p\equiv-u-i\pmod{q_{p,i}},\qquad 1\le i\le H,
\tag{11}
\]

therefore specify a **reduced** class modulo `mathcal Q(p)`.

The `H` witness primes are distinct. Even the elementary bound that their increasing rearrangement has its `j`th member at least `j+1` gives

\[
\mathcal Q(p)\ge(H+1)!,\qquad
\log\mathcal Q(p)\ge H\log H-O(H)
 =(\delta+o(1))L\log L.
\tag{12}
\]

So the witness modulus exceeds every fixed power of `X`. This suggested a first inverse argument: too many independent congruences should leave no anchor below `2X`.

**That inference is false, and its error can be calculated exactly.** Let `mathscr C_X` be the family of these observed canonical witness tuples, one per selected anchor. For large `X`, no two anchors give the same tuple, since their difference would be divisible by a modulus larger than `X`. For each tuple `C`, let `N_X(C)` count all integers in `(X,2X]` satisfying its congruences. There is exactly one: its actual anchor. Hence

\[
\begin{aligned}
\sum_{C\in\mathscr C_X}N_X(C)&=M,\\
0\le\sum_{C\in\mathscr C_X}\frac X{\mathcal Q(C)}
 &\le\frac{X^2}{(H+1)!}=o(1),\\
\sum_{C\in\mathscr C_X}
\left(N_X(C)-\frac X{\mathcal Q(C)}\right)&=M-o(1).
\end{aligned}
\tag{13}
\]

The selected CRT errors are therefore not an unestimated small remainder: their total is necessarily essentially `M`. This is an assertion about the actual integer congruences, not a fabricated prime process. It is not a contradiction to an arithmetic-progression theorem, since no such theorem supplies a relative main term at these moduli.

### Truncating the independent-witness code does not fix its count

For any subset `S` of the chosen witness primes satisfying

\[
\prod_{i\in S}q_{p,i}\le X^\kappa
\]

with fixed `kappa`, at most `pi(H)` selected primes can be at most `H`. Thus

\[
|S|\le\pi(H)+\frac{\kappa L}{\log H}
      =O_{\delta,\kappa}\left(\frac L{\log L}\right)=o(H).
\tag{14}
\]

This truncation sees only a vanishing fraction of the independent witnesses. This is **not** a claim that every composite covering or every sieve has this limitation: a different certificate can reuse small factors. That observation motivates the next repair.

---

## 4. Repair: compress the repeated factors to a small periodic profile

### Lemma 2: the whole cofactor vector has an explicit period

For the canonical first-maximum allocation in Lemma 1,

\[
(\beta_1(m+W_H),\ldots,\beta_H(m+W_H))
 =(\beta_1(m),\ldots,\beta_H(m))
\tag{15}
\]

for every `m>=0`, where

\[
W_H=\prod_{q\le H}q^{s_q+1}=Q_H\prod_{q\le H}q.
\]

### Proof

Fix `q<=H`, and write `s=s_q`. The values

\[
\min(v_q(m+i),s+1),\qquad 1\le i\le H,
\]

are determined by `m mod q^(s+1)`. If one of these equals `s+1`, its index is unique, and it is the index of the actual valuation maximum, whatever the larger valuation may be. If none equals `s+1`, the maximum is `s`, and its first index is determined by the same residue.

Furthermore `C_q(m)` in (6) depends only on `m mod q^s`. Formula (7) determines the cofactor exponent at the chosen index as `s-C_q(m)`. At every other index the exponent is the ordinary valuation, which is at most `s` and is determined by the residue already retained. Thus the entire `q`-part of the cofactor vector is periodic modulo `q^(s+1)`. There are no cofactor prime factors greater than `H`. Combining these periods proves (15). ∎

By PNT,

\[
\log W_H=\psi(H)+\vartheta(H)=(2+o(1))H,
\qquad W_H=X^{2\delta+o(1)}.
\tag{16}
\]

So the repair genuinely compresses the small-cofactor information to a modulus below `X^(1/2-epsilon)` for some fixed `epsilon>0`. This is only a size statement; no masked distribution theorem is being inferred from it.

### The compressed cofactor forms are genuinely admissible

Fix a residue of `m mod W_H` and a representative `m_0>Q_H`. The integers `beta_i` are now fixed, and along that row

\[
F_i(t)=\frac{m_0+i+W_Ht}{\beta_i}
      =\frac{W_H}{\beta_i}t+\frac{m_0+i}{\beta_i}
\tag{17}
\]

are integer linear forms. Let

\[
J=\{i:\gcd(F_i(0),W_H)=1\}.
\]

Pairwise coprimality of the allocated parts implies

\[
|J|\ge H-\pi(H).
\tag{18}
\]

Indeed each prime at most `H` can exclude at most one index. Since `beta_i | Q_H`, every prime at most `H` divides `W_H/beta_i`. Therefore, for `i in J`, each such prime has **no** root of `F_i` modulo that prime. Also these forms are primitive: any common divisor of their slope and constant would divide `W_H`.

For a prime `q>H`, the root of `F_i mod q` is

\[
t\equiv-(m_0+i)W_H^{-1}\pmod q.
\]

These roots are distinct for different indices, since `0<|i-j|<q`. Thus the product of the forms indexed by `J` has exactly `|J|<q` roots modulo `q`. The family is admissible, with **exact** root counts `0` at primes at most `H` and `|J|` at larger primes.

This checks the local arithmetic; it does not assert simultaneous prime values of these growing families.

### Where the compression loses the desired implication

An actual endpoint is prime exactly when

\[
\mathbf1_{\mathbb P}(m+i)
 =\mathbf1_{\{\beta_i(m)=1\}}\,
  \mathbf1_{\mathbb P}(\alpha_i(m)),\qquad m>Q_H.
\tag{19}
\]

A prime value of a primitive cofactor form with `beta_i>=2` is still a composite original endpoint. In fact the indices with `beta_i=1` that are primitive are precisely

\[
J\cap\{i:\beta_i=1\}
 =\{i:\gcd(m_0+i,W_H)=1\}.
\tag{20}
\]

For the forward inclusion use `m_0+i=F_i(0)`; for the reverse inclusion use `beta_i | W_H` and `beta_i | m_0+i`. Thus compression does not turn the numerous admissible cofactor forms into numerous eligible *unit*-cofactor forms.

There is an actual integer example of this distinction. At the prime anchor `37`, with `H=3`, the block `38,39,40` has

\[
(\alpha_1,\alpha_2,\alpha_3)=(19,13,40),\quad
(\beta_1,\beta_2,\beta_3)=(2,3,1).
\]

Both primitive cofactor forms have prime values, but both corresponding endpoints are composite. The unit-cofactor position has a fixed factor `2`. This is a finite check of the proposed inference, not a counterexample to the global conjecture.

---

## 5. Second repair: use the factorial budget to count the non-unit outputs

Instead of stopping at the distinction in (19), one can bound quantitatively how much of the selected family the non-unit prime outputs can occupy.

Fix an integer `D>=2` and set `K=H^D`. From the exact product of cofactors,

\[
\#\{i:\beta_i>K\}
 \le\frac{\log(H!)}{D\log H}
 <\frac HD
\tag{21}
\]

in **each** block. Also, at most `pi(H)` of the allocated parts in a block have a prime factor at most `H`.

### An actual composite reservoir, with an asymptotic

Let

\[
\mathcal C(X,K)=\{n\in(X,2X]:n=kq,\ 2\le k\le K,\ q\text{ prime}\}.
\]

Since `K` is a fixed power of `log X`, every such `q` exceeds `sqrt(2X)` for large `X`. The representations are therefore unique. Ordinary PNT, uniformly over `k<=K`, gives

\[
\begin{aligned}
|\mathcal C(X,K)|
 &=\sum_{2\le k\le K}
   \left(\pi(2X/k)-\pi(X/k)\right)\\
 &=(1+o(1))\frac XL\sum_{2\le k\le K}\frac1k\\
 &=(D+o(1))\frac{X\log H}{L}.
\end{aligned}
\tag{22}
\]

For completeness, `log(X/k)=L+O_D(log H)` uniformly, and both endpoints tend to infinity uniformly. This justifies the uniform PNT substitution and its summation. No prime-pair input is present.

The upper bound (22) alone does not show how often these integers have *prime canonical allocated parts*. That issue can be repaired on a substantial, block-position-independent subset.

### Lemma 3: universal small-cofactor prime outputs

Suppose `q>H` is prime and `1<=k<=sqrt(H)`. In **any** block of `H` consecutive positive integers containing `n=kq`, the canonical allocation at the position of `n` satisfies

\[
\alpha(n)=q,\qquad \beta(n)=k.
\tag{22a}
\]

Indeed, if `ell^v || k`, then `ell^(v+1)<=k^2<=H`. Every `H`-block contains an integer divisible by `ell^(v+1)`. Thus the position `n=kq` cannot be the valuation maximum for `ell`, and none of its small prime factors is allocated to that position. Conversely `q>H` divides just this one integer in the block and does not divide `H!`, so its full first power is allocated there. These are all the factors of `n`, proving (22a). The case `k=1` is immediate by the same allocation rule. No height condition on the other positions is needed for this lemma. ∎

Applying the same one-prime count as in (22) gives an actual set of composites of size

\[
|\mathcal C(X,\lfloor\sqrt H\rfloor)|
 =\left(\frac12+o(1)\right)\frac{X\log H}{L}.
\tag{22b}
\]

**Every one of them has a prime canonical allocated part with non-unit cofactor, in whichever length-`H` block contains it.** Thus an unmasked `o(X/L)` bound for all these false prime outputs is genuinely false, not just unproved. This statement is independent of a choice of block position. It does **not** assert that the `E_X`-selected blocks meet this set with any prescribed frequency.

Let also

\[
\mathcal T(X,K)=\{n\in(X,2X]:n=kq^e,\ 1\le k\le K,
                       \ q\text{ prime},\ e\ge2\}.
\]

An elementary count, summing over at most `O(L)` exponents and at most `sqrt(2X)` bases, gives

\[
|\mathcal T(X,K)|\ll K\sqrt X\,L=o(X/L).
\tag{23}
\]

There is no uniqueness assertion needed for this upper bound.

### Lemma 4: two-private-factor inventory

Let `G` be as in (O4). For any disjoint collection of forced blocks (2), the following finite inequality holds:

\[
G\ge MH
 -M\frac{\log(H!)}{D\log H}
 -M\pi(H)
 -|\mathcal C(X,H^D)|
 -|\mathcal T(X,H^D)|.
\tag{24}
\]

### Proof

Discard positions with `beta_i>H^D`, using (21). Discard those whose allocated part has a prime factor at most `H`, using pairwise coprimality. For a remaining position, `alpha_i>1` is `H`-rough.

If `alpha_i` is prime, the original endpoint is composite, so necessarily `beta_i>=2`. Its endpoint lies in `mathcal C(X,H^D)`. If `alpha_i` is a non-prime prime power, its endpoint lies in `mathcal T(X,H^D)`. Disjointness of the blocks makes each endpoint occur only once, so these two sets bound the total number of those discarded positions, even though the allocation depends on the block.

Every position left has `omega(alpha_i)>=2`. Both of two distinct prime divisors are proper divisors of its composite endpoint. They exceed `H`, and no such prime can divide a second endpoint in that block, whose distance is less than `H`. This proves (24). ∎

Stirling's formula, `pi(H)=O(H/log H)`, (22), and (23) give (O4). The finite inequality is valid also when `M=0`; no division by `M` is used.

This repair produces a genuine necessary factor inventory, rather than an assumed rough-mass lower bound. It nevertheless points in the opposite direction from an immediate contradiction: after removing the relatively scarce small-cofactor prime outputs, the surviving allocated parts can be composites with multiple private factors. The factorial identity does not force one of these allocated parts to be prime, nor force a prime allocated part to have unit cofactor.

A second actual check illustrates this remaining alternative. The prime `113` is followed by the prime `127`. In its forced composite subblock at offsets `6,7,8`, namely `119,120,121`, one obtains

\[
(\alpha_1,\alpha_2,\alpha_3)=(119,20,121),\qquad
(\beta_1,\beta_2,\beta_3)=(1,6,1).
\]

All three allocated parts are composite, they are pairwise coprime, and the cofactor product is `3!`. Again this tests a pointwise inference only; it says nothing against a global limit-point theorem.

---

## 6. Exact unclosed implication

The genuinely successful parts of the inverse attempt are:

1. Every selected logarithmic composite block has a full proper-prime-divisor matching, with an exact factorial cofactor budget.
2. The whole small-cofactor profile has the explicit period `W_H=X^(2delta+o(1))`, despite the independent-prime witness code having super-polynomial modulus.
3. The primitive cofactor forms have explicitly verified admissibility and exact local root counts.
4. The non-unit prime-output reservoir has the proved size (22); the subset (22b) gives canonical prime allocated parts independently of the containing block. The selected blocks obey the quantitative two-private-factor bound (24).

The proposed contradiction from oversized witness moduli fails by the **exact** calculation (13), not merely by lack of an error estimate. The periodic compression repairs that height problem for the cofactors, but it does not repair the unit-cofactor issue in (19). The second repair quantifies the proper-cofactor outputs and proves a new factor inventory; it still gives no forced prime at a unit-cofactor position.

More explicitly, the unresolved integer intersection is

\[
Z_X=\sum_{p\in E_X}\sum_{i=1}^H
 \mathbf1_{\{\beta_i(p+u)=1\}}
 \mathbf1_{\mathbb P}(\alpha_i(p+u)).
\tag{25}
\]

The hole hypothesis makes `Z_X=0` exactly. Nothing proved here forces it to be positive on an unbounded set of scales. The unclosed step is to use the **actual factor systems across the different selected prime anchors**, beyond their periodic cofactor profiles and factorial budgets, to force a prime allocated value specifically in a unit-cofactor slot. Counting primes among the other primitive forms cannot replace that step, as (19), (22), and the actual examples demonstrate.

Equation (25) is stated to delimit the failure, **not** offered as a new sufficient-condition theorem or as a proof. No assertion that the conjecture is false follows from this attempt.

---

## 7. Sources, finite verification, and integrity

### Sources and scope

* The basic binomial factor allocation appears in Shaohua Zhang, *A Refinement of the Function g(x) on Grimm's Conjecture*, arXiv:0811.0966. The checked corpus file is `/corpus/src/0811.0966/0811.0966.tex`, Theorem 1 at lines **112–116** and its allocation argument at **172–209**. Lemma 1 above includes an independent valuation proof; the period, root-count analysis, and estimates (13), (22), (24) are derived explicitly here.
* A stronger known distinct-prime matching theorem at lengths much larger than `log X` is recorded in Laishram–Murty, *Grimm's Conjecture and Smooth Numbers*, `/corpus/src/1306.0765/1306.0765.tex`, **54–68**, citing Ramachandra–Shorey–Tijdeman. It was checked during exploration but is **not used** in any proof above. In particular neither the full Grimm conjecture nor any conditional improvement of it is an input.
* The only asymptotic prime input used in the proofs is ordinary PNT: for index normalization, the sizes of `Q_H,W_H`, and the one-prime count (22). The local root calculations do not assume a prime-tuple asymptotic.

### Checks on actual integers

Run:

```bash
cd /workspace/leanproject
python3 Submission/check_eventual_hole_factorial_matching.py
```

The checker uses actual integer factorizations, an independent residue-only calculation of the cofactor profile, and an independent augmenting-path maximum-matching calculation. It passed:

* **5,409** allocation/cofactor cases, including the exact binomial product, pairwise coprimality, `beta_i | Q_H`, cofactor product `H!`, and nontriviality where `m>Q_H`;
* **1,080** proper-matching rank identities (8);
* **195** period tests, each comparing `m`, `m+W_H`, and `m+2W_H`;
* **180** primitive-cofactor-form root-count/admissibility tests;
* **3,111** small-cofactor universality cases, testing every position of each chosen block;
* the inventory classification on **1,121 disjoint actual prime-anchored composite blocks** in `(25000,50000]`, including the injectivity of endpoints, the proper-factor CRT congruences, and the finite reservoir bounds;
* both actual-prime examples above.

The finite tests do not verify asymptotic constants or postulate an eventual prime-gap hole. The proofs, not numerical samples, justify those assertions that are proved.

No Lean file was changed, no admitted statement in `Spec.lean` was used, and `Submission/Spec.lean` retains SHA-256

```
47104279c0cb871e0a255d81fffde6a4a6ea7e71c3eec5c5b57e0bc7c0654123
```

## Independent follow-up check

The main assistant independently checked the remaining arguments and the cited binomial-allocation source passages. In particular the truncated valuations determine the first maximum and the complementary exponents modulo `q^(s_q+1)`, proving the full vector period. The slope of each primitive retained form is divisible by every prime at most `H`; the roots at primes greater than `H` are distinct. This establishes local admissibility only.

The PNT error in (22) is uniform for `k≤H^D` since `X/k→∞` uniformly and `log(X/k)/log X→1`. Uniqueness of the large prime factor prevents duplicate reservoir representations. Lemma 3 correctly removes each factor of `k` from the allocated part because a higher prime power occurs elsewhere in every containing block. Disjointness of the selected blocks then justifies (24) and its asymptotic (O4). The malformed LaTeX in (O3) was corrected; no mathematical statement was changed.

The earlier independent checker run passed all reported finite cases. No result here proves that a prime allocated part occurs in a unit-cofactor slot of a selected block. In particular local admissibility and the factorial budget cannot replace this unproved intersection. Neither target theorem has been proved.
