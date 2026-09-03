# Growing-pool residue exclusion: cost, rare events, and the size obstruction

## Outcome

**No actual-prime proof closes; Erdős #5 is not proved.** The growing-pool objection to the independent model is valid: its total number of forbidden shared-prime collisions diverges. It cannot be dismissed using a fixed-tuple Euler product or total variation on a few coordinates.

The following stronger statements are verified here.

1. There is an exact, all-pool residue conditioner, including coincident roots. Its entropy/acceptance cost is of order `M² sum p^(-2)`, but its effect on a specified prime-like *void* of `r` labels is multiplicative `exp(O(r M sum p^(-2)))`. For fixed `r`, this is `1+o(1)`, **even at probability `B^(-r)`**.
2. A separate sparse-dependency argument works with **actual factorizations of auxiliary integers in `(N,2N]`**, not Bernoulli prime flags. It conditions the entire growing pool to satisfy every squarefree cross-label root constraint, including synchronized hits when offsets coincide modulo a prime. Section 4.5 strengthens this to **all prime-power valuation constraints**. Its genuine prime-pattern probabilities have uniform relative error `o(1)`. A branchwise-normalized parity mixture still has within-pool pair coefficient `2+o(1)` and no cross-pool primes.
3. Neither construction has the joint law of the actual translates. Exact CRT independence through the square-root sieve already gives the wrong **one-prime** constant. Requiring the auxiliary factorizations to be those of `n+h` at the prescribed height imposes affine equalities whose cost is vastly greater than the collision cost.

Statement 2 is not a new realization of **all** the old weighted kernel identities after conditioning. The uniform local domination proved below is one-sided for general weights; a rare weighted mass can need additional analysis. In particular, no weighted actual-prime pair multiplier below 2, and no actual cross-pool lower bound, is obtained. These conclusions are not an impossibility theorem for using exclusion **together with** new size-sensitive arithmetic information.

`Submission/Spec.lean` was neither changed nor used as a premise.

## 1. Setup and checked inputs

Keep the protected pools and common mask from `AveragedPairWeightAttempt.md`:

\[
 L=\log N,\quad z=\eta L,\quad
 W=\prod_{p\le z,\ p\ne Z}p,\quad B=\frac{\phi(W)}W L,
 \quad M=M_1+M_2\asymp B\asymp\frac z{\log z}.
\]

Write `H=T_1 union T_2`, `D=max H-min H <= A z`, with `A` fixed, and `T=max(z,D)`. All offsets are distinct. In particular `M=o(z)`, and eventually a nonzero difference has at most one prime divisor exceeding `z`. The actual row contains

\[
 R=\#\{N<n\le2N:n\equiv b\pmod W\}=N/W+O(1)
\]

integers. Constants below can depend on the fixed geometry. We distinguish **uniform complete-CRT residues**, **auxiliary size-N integers**, and **the actual finite row** throughout.

Sources read directly, with local TeX line numbers:

* **Axler**, `/corpus/src/1703.08032/1703.08032.tex`: 16–34, ordinary PNT and its classical error; 105–124, `theta(x)~x`; 888–900, Mertens' product with constant `e^(-gamma)`. Partial summation gives
  \[
  S_2(x):=\sum_{p>x}p^{-2}\sim\frac1{x\log x},\qquad
  \sum_{p>x}p^{-3}\ll\frac1{x^2\log x}.
  \tag{1}
  \]
* **Fujisawa–Minamide**, `/corpus/src/1212.4348/1212.4348.tex`: 34–62, definitions and Landau's bound for summatory Möbius/Liouville; 65–82, a stronger version; 131–137 and 249–281, Dirichlet series and contour argument. Only the weaker unconditional `K=Q` bound
  `sum_(m<=x) lambda(m) << x exp(-c (log x)^(1/12))`
  is needed. No translated Liouville estimate is used.
* **BFM**, `/corpus/src/1404.5094/banks-freiberg-maynard-limit-points-of-normalized-prime-gaps-arXiv.tex`: 694–715 and 770–784, exceptional prime and `Z/phi(Z)=1+o(1)`; 786–814, modified BV and its parameter dependence; 1240–1276, divisor lemma; 1315–1414, mass, first moment, and elementary CRT count.
* **M18**, `/corpus/src/1811.03008/limitp2.tex`: 218–225, modified BV; 353–399, the actual weights, smooth-difference hypothesis, pair upper bound `3.99+O(delta)`, and prime-coordinate freezing.
* **Ford**, `/corpus/src/2101.03440/HR_shift.tex`: 87–90, uniform-constant convention; 265–280, the ordinary two-linear-form upper sieve. This is the input to the **offset-label** bad-pair count already proved in §2 of `AveragedPairWeightAttempt.md`, not a weighted prime-pair estimate at height `N`.

The PNT/Mertens inputs concern one-dimensional counts. The modified BV theorem is used only for the already established actual-row **one-prime** asymptotic, with the small-mask parameter chosen sufficiently small. The probability lemmas below have self-contained proofs; no growing-dimension sieve or new prime-pair distribution theorem is invoked.

## 2. Exact local law, including shared roots

For a prime `p` outside `W`, partition `H` into its `nu_p` nonempty residue classes `C_(p,a)` modulo `p`. For uniform `n mod p`, the hit set

\[
 \{h:p\mid n+h\}
\]

is empty with probability `1-nu_p/p`, and is **the entire class** `C_(p,a)` with probability `1/p`, for each class. Thus, for `I_(p,h)=1_(p|n+h)`,

\[
 \operatorname{Cov}(I_{p,h},I_{p,k})=
 \begin{cases}
 p^{-1}-p^{-2},&h\equiv k\pmod p,\\
 -p^{-2},&h\not\equiv k\pmod p.
 \end{cases}                                                    \tag{2}
\]

For any finite prime set `P`, the complete-CRT log moment generating function is exactly

\[
 \log\mathbb E\exp\left(\sum_{p\in P,h}u_{p,h}I_{p,h}\right)
 =\sum_{p\in P}\log\left[1+\frac1p\sum_a
              \left(e^{\sum_{h\in C_{p,a}}u_{p,h}}-1\right)\right].
 \tag{3}
\]

This specifies every cumulant for the **whole growing pool**. For `r` different root classes at one prime the joint cumulant of their indicators is
`(-1)^(r-1)(r-1)!/p^r`; across different primes the cumulants vanish in this complete-CRT law. Shared-root cumulants are obtained from (3), not by treating coincident labels independently.

On the actual finite row, a prescribed compatible squarefree divisor pattern has count `N/(Wq)+O(1)`, with the appropriate lcm `q`; an incompatible pattern has count zero. Consequently the single-prime version of (2) has error `O(1/R)` where a nonzero count is involved. This elementary error is **not** summable over arbitrary growing sets of prime products.

### Calibrated Bernoulli construction

At each `p>z`, independently mark its **root classes**, not its labels, with probability

\[
 t_p=\frac1{p-\nu_p+1}.
\]

Condition on at most one marked class. Its acceptance probability is

\[
 a_p=(1-t_p)^{\nu_p-1}(1+(\nu_p-1)t_p)
     =\frac{p(p-\nu_p)^{\nu_p-1}}{(p-\nu_p+1)^{\nu_p}}.       \tag{4}
\]

The conditional mass of each class is exactly `1/p`; the empty mass is `(p-nu_p)/p`. Independent conditioning at different primes gives precisely (3). Every finite collection of these residues is compatible by CRT.

Two important qualifications:

* Starting with parameter `1/p`, rather than `t_p`, gives conditional class marginal `1/(p+nu_p-1)`, **not** `1/p`.
* For `z<p<=D`, conditioning independent **label** hits to be empty or one full root class does not give this law. A class of size `m` has relative weight `(t/(1-t))^m`; unequal class sizes are biased differently. Root-class sampling, or a genuine synchronization repair, is necessary. The omitted prime `1<Z<=z` is likewise handled as a root-class law; no assumption `M<Z` is made. If `nu_Z=Z`, choose a uniform class directly (there is no empty outcome).

## 3. Diverging entropy versus rare-event influence

For `p>z`, uniformly since `nu_p<=M=o(z)`,

\[
 -\log a_p=\binom{\nu_p}{2}p^{-2}
                  +O(M^3p^{-3}).                         \tag{5}
\]

For the distinct-root tail `p>T`, and a cutoff large enough to capture that tail,

\[
 \Lambda=\binom M2 S_2(T)\asymp\frac z{\log^3z}\longrightarrow\infty,
 \qquad -\log\prod_{p>T}a_p=(1+O(M/T))\Lambda.             \tag{6}
\]

One can use an infinite product of the **acceptance events** in (6), since `sum(1-a_p)<infinity` for each fixed `N`; void events below always have a finite cutoff. Also, the relative entropy of the conditioned product law with respect to its unconditioned Bernoulli parent is exactly `-sum log a_p`. Thus global closeness of the two laws is false: the parent's probability of satisfying all exclusions tends to zero. This confirms, rather than evades, the collision objection.

Now specify a set `S` of `r` labels, possibly within this growing pool. Let `s_p=nu_p(S)<=r`. For the event `V_S` that these labels have no hit at any `z<p<=y`, the conditional/unconditioned probability ratio is exactly

\[
 \frac{\Pr(V_S\mid\text{all exclusions})}{\Pr(V_S)}
   =\prod_{z<p\le y}\frac{1-s_p/p}{(1-t_p)^{s_p}}.          \tag{7}
\]

If `p>=2nu_p`, each factor satisfies

\[
 0\le\log\frac{1-s_p/p}{(1-t_p)^{s_p}}
       \le\frac{2s_p\nu_p}{p^2}.
 \tag{8}
\]

For the lower bound, the log ratio is concave as a function of `s` on `[0,nu]`, is zero at 0, and equals `-log a_p>=0` at `nu`. For the upper bound use `log(1-s/p)<=-s/p` and
`-log(1-t)=log(1+1/(p-nu))<=1/(p-nu)`.

Therefore, **uniformly in the entire pool, in `S`, and in the finite cutoff `y`**,

\[
 1\le\frac{\Pr(V_S\mid\text{all exclusions})}{\Pr(V_S)}
 \le \exp(2r M S_2(z)),\qquad M S_2(z)\asymp\frac1{\log^2z}=o(1).
 \tag{9}
\]

This is relative error, not total variation: if the denominator is of order `B^(-r)`, the absolute error is `O(r M S_2(z) B^(-r))` for bounded `r`. In particular it is `o(B^(-2))` for a pair. Conditioning slightly **increases** these void probabilities; it does not generate a constant-factor pair saving.

There is a second exact comparison, independent of the pool size. Set `q_y=prod_(z<p<=y)(1-1/p)`. Under complete CRT,

\[
 \Pr(V_S)=\prod_{z<p\le y}(1-s_p/p)
       =q_y^r\exp\left(O\left(r^2S_2(z)
                         +\sum_{p>z}\frac{r-s_p}{p}\right)\right).
 \tag{10}
\]

Here `sum_(p>z)(r-s_p)/p <= binom(r,2)/z`: assign each duplicate class membership to a pair whose nonzero difference is divisible by that prime; each pair has at most one such prime. Thus for fixed `r` the factor is `1+O_r(1/z)`, uniformly even for the bad-difference selections. An omitted prime adds `1+O_r(1/Z)` when present. This includes the whole `p in (z,D]` issue; it is not legitimate to delete those primes.

**Scale answer.** The global free-energy cost is `Lambda`; the effect of fixing finitely many potential prime endpoints is its local/deletion scale `Lambda/M`, not `Lambda`. Formula (9) proves that assertion at rare-event accuracy for the residue conditioner. It does not identify a void flag with a prime.

## 4. A uniform growing-pool conditioning theorem for auxiliary actual integers

We next retain genuine size-N integer factorizations and genuine primality flags. This is different from the product-over-primes construction.

### 4.1 Independent input and exact root compatibility

For the moment suppose there is no omitted prime below `z`. Independently at each label choose `Y_h` uniformly from one of the two parity sectors

\[
 \{N<m\le2N:(m,W)=1,\quad\lambda(m)=\sigma_h\},
 \qquad \sigma_h\in\{-1,+1\}.
\]

The signs may be any fixed assignment, including the two-pool parity branch. The one-dimensional Liouville bound and inclusion–exclusion imply that both sectors have `(1/2+o(1)) N phi(W)/W` elements, with an error smaller than any fixed logarithmic power relatively. Indeed each inner summatory-Liouville argument after removing `e|W` has size at least `N/W>N^(1-2eta)`, and the reciprocal-divisor cost is `prod_(p|W)(1+1/p)<<log z`.

If `1<Z<=z`, first choose **one** residue `a mod Z`. At label `h` additionally require

\[
 Z\mid Y_h\quad\Longleftrightarrow\quad a+h\equiv0\pmod Z.
 \tag{11}
\]

Conditional on `a` and the signs, still sample independently. The sector sizes are uniformly `(1/2+o(1))N(phi(W)/W)c_h`, where `c_h=1/Z` on a hit class and `c_h=1-1/Z` otherwise. Inclusion–exclusion with the extra divisor `Z=O(z)` proves this as well. Choose `a` uniformly only when forming the final mixture. This avoids the invalid assumption that every label can simultaneously avoid `Z` when its roots fill the modulus.

For distinct labels `i,j`, call `E_ij` bad if, at some prime `p>z`, either

* `p` does not divide `h_i-h_j` and divides both `Y_i,Y_j`; or
* `p` divides `h_i-h_j` and divides **exactly one** of `Y_i,Y_j`.

Let `E` mean that none of the `E_ij` occurs. This is conditioning on the **whole growing pool**, at every relevant prime up to `2N`; larger primes divide none of the samples. On `E`, the hit set at every prime is empty or one whole offset root class. For `p>z`, a residue avoiding all classes exists because `p>M`. At the primes of `W` use the protected row `b`; at `Z` use (11). Consequently every sample has compatible common residues at every prime, and hence at every finite squarefree product. This asserts compatibility, **not uniform CRT marginals** or existence of a size-N common translate.

### 4.2 Small dependency per label, despite a large total cost

Uniformly in the signs and in (11), elementary rough-number counting gives

\[
 \Pr(p\mid Y_h)\le3/p\quad(z<p\le N^{1/3}),
 \qquad \Pr(p\mid Y_h)\ll z\log z/p\quad(p>N^{1/3}),
 \tag{12}
\]

and every point mass is at most `m_* << z log z/N`. For the first bound, count multiples using inclusion–exclusion with error `O(2^(pi(z)))=N^o(1)`; its main term dominates uniformly, even in a `Z`-hit sector. Dividing by its parity-sector size costs at most `2+o(1)`. For the second use the trivial multiple count and that sector size. Thus we may take

\[
 \Pr(E_{ij})\le b_{ij}:=q_N+
                  6\sum_{\substack{p>z\\p\mid h_i-h_j}}\frac1p,
 \quad q_N=9S_2(z)+O(N^{-1/4}),                            \tag{13}
\]

with a fixed positive error bound in `q_N`. The large-prime contribution follows by summing `(C z log z/p)^2` over integers `p>N^(1/3)`. Applying the same parity cancellation also to the numerator for `p | Y_h` gives `(1+o(1))/p` uniformly for `p<=N^(1/3)`, with fixed slack in `2eta+1/3<1`. Thus the expected number of distinct-root collision **pair/prime incidences** in this independent integer input is indeed `(1+o(1)) binom(M,2) S_2(T)`. The large-prime tail is negligible. No independence across primes of one integer is being asserted.

Put

\[
 s=\max_i\sum_{j\ne i}b_{ij}
 \ll M S_2(z)+M/z=o(1).                                  \tag{14}
\]

The `M/z` term treats shared roots uniformly without a sieve estimate for offset pairs. If there are no shared roots in the primes under consideration, it is absent and `s<<1/log²z`. For arbitrary offsets of the stipulated diameter, `s<<1/log z` suffices. The explicit row sum in (14) is stronger than this worst-case simplification.

Here is the elementary local-lemma bound we need. For independent vertex variables and edge bad events with bounds `b_ij`, if `s<=1/16`, set `x_ij=2b_ij`. Neighboring edges share a vertex, and

\[
 \prod_{f\sim e}(1-x_f)\ge1-4s\ge\tfrac12,
 \qquad \Pr(E_e)\le x_e\prod_{f\sim e}(1-x_f).
\]

The usual induction on a conditioning set gives
`Pr(E_e | avoidance of any other edge set) <= x_e`: separate the nonneighbors (independent of `E_e`) and expose the neighbors successively; their avoidance denominators are bounded below by the displayed factors. In particular,

\[
 \Pr(E)\ge\prod_e(1-2b_e)\ge\exp(-4\sum_e b_e)>0.          \tag{15}
\]

For the particular protected pools, the established bad-difference count is `O(z²/log³z)` pairs. Each contributes at most `1/z` to the sum in (13), so `sum_e b_e=O(z/log³z)=O(Lambda)`. Thus synchronization can also be imposed at global acceptance cost at most `exp(O(Lambda))`. This is a lower bound on acceptance, not a claimed asymptotic for its probability under the size-constrained input. The worst-case bound (14) remains uniform label by label.

For **any** nonnegative function `F` of a label subset `S`, `|S|=r`, the same argument gives the rare-event-uniform, one-sided bound

\[
 \mathbb E(F\mid E)\le e^{4rs}\mathbb EF.                 \tag{16}
\]

Proof: let `E_0` exclude only edges disjoint from `S`. Then `F` is independent of `E_0`, and `Pr(E)/Pr(E_0)>=prod_(edges touching S)(1-2b_e)`. Dropping the touching-edge restrictions in the numerator proves (16). It must **not** be converted into a two-sided bound for an arbitrary rare `F`.

### 4.3 Two-sided relative bounds for actual prime flags

Let `F_S` be the event that all `Y_h`, `h in S`, are prime. If its unconditioned probability is zero, it remains zero. Otherwise, uniformly in the whole pool and in `S`,

\[
 \begin{split}
 \Pr(F_S\mid E)&\le e^{4rs}\Pr(F_S),\\
 \Pr(F_S\mid E)&\ge
 \left[1-O\left(rs+rM m_*+r^2L/N\right)\right]\Pr(F_S).
 \end{split}                                             \tag{17}
\]

In particular the error is relative `o(1)` whenever the displayed quantities tend to zero, and need not be compared with `Pr(F_S)` afterward.

For completeness, condition on `F_S` and `E_0`. A prime at a tagged label has no divisor `p<=D`. A touching-edge failure at a shared-root prime therefore only requires the other label to hit that prime; by (12) and the one-site version of (16), their total probability is `O(rs)`. A failure at any other prime must mean **equality** of the tagged prime and another auxiliary integer, since both integers lie in `(N,2N]`. This costs at most `O(rM m_*)`, again using (16) on the outside label. Two tagged primes coincide with probability at most `1/(pi(2N)-pi(N))=O(L/N)` per pair. These estimates give `Pr(E | F_S,E_0)>=1-error`. Finally use the exact deletion identity

\[
 \frac{\Pr(F_S\mid E)}{\Pr(F_S)}
 =\frac{\Pr(E_0)}{\Pr(E)}\Pr(E\mid F_S,E_0),
 \qquad \Pr(E_0)/\Pr(E)\ge1.                              \tag{18}
\]

This proves the lower bound. No division of an uncontrolled `o(1)` error by `B^(-r)` occurs.

### 4.4 What survives of the parity branch

Choose a fair global bit selecting the odd-parity sector in one pool and the even sector in the other. **Within each branch and each chosen residue (11), normalize the conditioning on `E` separately.** This is legitimate by (15). It is not a claim that literal conditioning of the original mixture leaves its mixing probabilities unchanged; those posterior probabilities have not been estimated.

An inactive pool still has no primes on every sample. An active, unhit label has base prime probability `(2+o(1))/B`, or `(2+o(1))/(B(1-1/Z))` in (11); a `Z`-hit label has none. Averaging the uniform residue `a` gives the factor `1-nu_Z(S)/Z`. Hence (17) implies, uniformly for every fixed set of distinct labels,

\[
 \mathbb E\prod_{h\in S}1_{\mathbb P}(Y_h)=
 \begin{cases}
 (2^{r-1}+o(1))B^{-r},&S\text{ is contained in one pool},\\
 0,&S\text{ meets both pools}.
 \end{cases}                                             \tag{19}
\]

The relative correction at the exceptional prime is `O_r(1/Z)=o(1)`. The estimates are uniform over **all** label choices while `M~B` grows. Thus, for example, the error in a normalized or summed pool-pair statistic is controlled by summing these relative bounds, not by a fixed-tuple assertion. The auxiliary integers have full genuine factorizations and the flags in (19) mean actual primality of those integers.

Literal conditioning also cannot create cross-pool primes: that event had zero probability in either branch. The substantive content of (15)–(19) is that the exclusions are simultaneously satisfiable, and can be imposed with correct *relative* prime-pattern accuracy after branchwise normalization, despite the large total collision count.

### 4.5 Optional strengthening: full prime-power compatibility

The same conclusion can retain all cross-label **valuations**, not just squarefree hits. For `p>z`, eventually `p²>D`; hence a difference divisible by `p` has valuation exactly 1. Add to `E_ij` the event `p² | gcd(Y_i,Y_j)` when `p | h_i-h_j`. Its probability is at most `9/p⁴`, by the same multiple count. Replace 6 in (13) by 7; (14)–(19) still hold. Within a hit class at most one label can now have valuation greater than 1. If one does, its congruence forces valuation 1 at every other class member. If all have valuation 1, there is a lift modulo `p²` avoiding the class's finitely many forbidden lifts, because its size is less than `p`.

At an omitted `Z<=z`, instead choose a uniform residue modulo `q_Z=Z^a`, where `a` is the least positive integer with `Z^a>D`. Thus `q_Z<=Z max(D,1)=O(z²)`. Require `v_Z(Y_h)=v_Z(a_0+h)` when this valuation is below `a`, and require `Z^a | Y_h` otherwise. There is at most one label of the latter kind. Its higher valuation can always be accommodated by lifting the common residue. The parity-sector counts remain uniform by the same inclusion–exclusion argument with a divisor at most `O(z²)`; replace `m_*` by `O(z² log z/N)` and the trivial large-prime bound correspondingly. The tail in (13) is still `O(N^(-1/4))`. Primes are allowed exactly when `a_0+h` is nonzero modulo `Z`, so (19) is unchanged.

Consequently the strengthened model has a common residue matching **all sampled valuations at every prime**, for every finite collection of prime powers. Equivalently these data can be completed to one profinite integer. There is still no assertion that this profinite integer is an ordinary integer at the required height, or that its residues have the uniform CRT law.

**Limits of this theorem.** Even the strengthening does not impose the exact joint residue distribution or all the old kernel main terms. Formula (16) applies to a fixed local source square, also with prime flags, but supplies no general lower bound for its rare weighted mass. It cannot on its own reestablish the mass and one-prime identities after this conditioning. For a `K`-label source square the pair benchmark is `B^(-K) L_2` in the row mean, not merely `B^(-2)`; (17) does not control the retained core at that scale. Nor does (19) imply anything about prime counts on the actual common row. These are substantial limitations, not a claimed disproof by a prime-count model.

## 5. Why neither conditioned law transfers to actual translates

### 5.1 The exact finite-row distribution budget

Let `Q` be a finite squarefree product coprime to `W`. In the parameterization `n=b+Wm`, the row consists of `R` consecutive values of `m`. Every residue modulo `Q` occurs `R/Q+O(1)` times. Consequently any nonnegative observable `G` modulo `Q` satisfies

\[
 \left|\mathbb E_R G-\mathbb E_{\mathrm{CRT}}G\right|
 \le\frac QR\mathbb E_{\mathrm{CRT}}G.                    \tag{20}
\]

This is a useful **multiplicative** bound when `Q=o(R)`, including for rare events. A cruder TV bound is `min(1,Q/(4R))`; using that alone would require an error `o(B^(-2))`, not merely `o(1)`. At very large `Q`, (20) is true but useless. Expanding a void or weighted prime event through all primes is not licensed by the small-modulus CRT counts or the modified BV theorem.

This failure is visible before considering two primes. Let `y=sqrt(2N+max H)`. On the actual row,

\[
 1_{\mathbb P}(n+h)=\prod_{\substack{p\le y\\p\nmid W}}
                               (1-I_{p,h}),
 \tag{21}
\]

since the protected integer has size between `N+O(log N)` and `2N+O(log N)`. For complete independent CRT residues, Mertens gives the mean of the right side as

\[
 \frac{\prod_{p\le y}(1-1/p)}{\phi(W)/W}
       =\frac{2e^{-\gamma}+o(1)}B,                       \tag{22}
\]

whereas the actual one-prime estimate is `(1+o(1))/B`. Since `2e^(-gamma) != 1`, there is already a discrepancy of order `B^(-1)`, despite exact local marginals `1/p`. Here `log Q~y`, immensely beyond `log R=O(log N)`. The prime-like flags of §3 are therefore **not actual primes**. Cross-prime dependence created by the integer-size constraint is essential even at one label, before a two-prime problem is reached.

### 5.2 Full auxiliary factorizations still do not give a size-N common n

The integers in §4 each have the correct total size and genuine factorization, but generally do not satisfy

\[
 Y_h-h=Y_k-k\quad\text{for all }h,k.                      \tag{23}
\]

Matching valuations leaves the **unit parts** of the cofactors free. In particular, auxiliary coprimality with `W` is not the equality `Y_h=b+h mod W`. The full residues of the already sampled integers would require `Y_h-h = Y_k-k mod p` even at primes dividing neither integer. At a prime greater than `2N+D`, this congruence already forces (23). Valuation compatibility must not be renamed full residue compatibility of the integers themselves.

The strengthening in §4.5 ensures `gcd(Y_h,Y_k) | h-k`, hence solvability of the divisibility congruences `n=-h mod Y_h`; the lcm modulus can nevertheless be enormous. It does not put a solution at height `N`. If `Y_h>N` and `N<n+h<=2N`, then `Y_h | n+h` forces **equality**, so the required size restriction recovers precisely (23), not merely coprimality.

There is a quantitative support gap. Conditional on a branch and (11), a specified auxiliary vector has probability at most `m_*^M` before exclusion. At most `R` such vectors are actual translates from the prescribed row (restrict to the part where all entries belong to `(N,2N]`). By (15),

\[
 \Pr(\exists n\text{ in the row}:Y_h=n+h\ \forall h\mid E)
 \le R\left(\frac{Cz\log z}{N}\right)^M
                   \exp(4\sum_e b_e)
 \le \exp\big(-(M-1)L+O(M\log z+M^2/z)\big).              \tag{24}
\]

For the prime-power strengthening replace `z` by `z²` in the middle bound of (24); its final bound is unchanged. This tends to zero extraordinarily rapidly, uniformly in the branches. Changing the endpoint intervals by `O(log N)` does not alter the conclusion. Thus this model and the genuine translate law have almost disjoint support; they are not an `o(B^(-2))` coupling, nor even a TV-`o(1)` coupling. The affine/height cost is of order `M log N`, compared with the distinct-root collision cost `M²/(z log z)`. Even after all valuation compatibilities are repaired, (23) alone prevents transfer.

This also explains the failure of a naive switching argument. In the product or auxiliary ensemble one can repair a label/root collision locally. Changing the residue of a real `n` at one prime while retaining all the other observed residues changes its CRT class modulo their product. There need not be another representative in the allowed interval. The switch is no longer a local operation on size-N factorizations.

## 6. Actual arithmetic conclusion and verification

The actual missing assertion is still positivity of a cross-pool prime count on the retained row, possibly with a nonnegative common-core source weight. Equivalently for existence one needs some actual row with a prime in each pool. The cover would then make the last prime of the first pool and the first prime of the second globally consecutive, and ordinary PNT would convert `log N` to the logarithm of their **global** index. No such positivity or weighted factor below 2 has been established here.

The new calculations do establish that a diverging global collision count does not itself imply a constant-factor correction for finitely many rare prime endpoints. They also specify what is not resolved: simultaneous control of the **size-constrained common-translate factorization law**, at weighted two-prime accuracy. They do not rule out a new argument exploiting exactly that missing law.

`python3 Submission/check_growing_residue_exclusion.py` **passes** with exact rational arithmetic: 540 calibrated-void checks, 53 cumulants, 16 multi-prime voids, 24,576 finite-row relative bounds, 273 local-lemma checks, and 59 exceptional-prime lift/void checks. It enumerates 294,912 full-factorization auxiliary samples; each parity branch has 30,008 samples surviving all root and prime-power compatibility tests. It also verifies the deletion identities and exhibits a squarefree-compatible pattern that fails at a prime square. The flags are primality of the enumerated auxiliary integers, not a proposed prime-gap construction. The analytic bounds and asymptotics are supplied by the proofs above, not by this finite test. Python compilation, display/equation-label checks, and the file-integrity check also pass.

The SHA-256 of the untouched `Submission/Spec.lean` is
`47104279c0cb871e0a255d81fffde6a4a6ea7e71c3eec5c5b57e0bc7c0654123`.

## 7. Independent verification

The main worker read the complete report and independently reconstructed the calibrated root-class law, the concavity proof of (8), the local-lemma induction and deletion identity, the two-sided tagged-prime estimate, and the prime-power lifting argument. In (17), a touching-edge collision away from a shared-root prime indeed reduces to equality of two auxiliary integers: a tagged prime exceeds `N`, so it has no other multiple in `(N,2N]`. This justifies the rare-event-relative bound but gives no estimate for a retained weighted core.

The PNT, Mertens, one-dimensional Liouville, exceptional-prime, modified-BV, and offset-sieve source passages listed in §1 were cross-checked directly. No translated Liouville estimate is inferred from the one-dimensional source. The independently checked small-modulus estimate (20) retains its factor `Q/R`; the all-primes cutoff in (21) lies far outside the useful range.

The supplied exact checker and Python byte-compilation were rerun successfully. A separate enumeration independently checked 28,160 prime-power valuation profiles against actual residue classes, and 408 exceptional-prime lifting cases (including `Z=2`). All passed. These finite checks validate the algebraic compatibility criteria, not the analytic asymptotics or the existence of a prime pair in the actual row.

The common-translate constraint (23) remains unproved at the required two-prime scale. Neither the auxiliary conditioning theorem nor its full-valuation strengthening is a proof or disproof of the target conjecture.
