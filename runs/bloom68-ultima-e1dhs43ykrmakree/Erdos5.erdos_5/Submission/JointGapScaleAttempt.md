# Joint prime-gap chains: checked scale control and the remaining shape obstruction

## Outcome

**Neither theorem in `Spec.lean` is proved.** This continuation does establish two arithmetic deductions from known prime estimates:

1. An endpoint-aware chain detector, combined with Merikoski's published weighted pair bound, gives the finite-point joint conclusion with `M=floor(7.98 m²)+1` positions for `m≥2`. A safe simpler count is `M=8m²`, with positive main-term margin `m/400`.
2. Absolute constants `c0,c1,C>0` exist such that, for every fixed `m≥1`, there are arbitrarily late chains of `m` globally consecutive prime gaps whose joint normalized limit vector satisfies

   `min λ_i ≥ c0/m`,  `c1 m ≤ sum λ_i ≤ C m`.

The second claim has a simple proof from PNT and an **unmasked** pair upper sieve, given below. No prescribed relative shape is asserted. These joint conclusions still do not force an individual gap into every prescribed band.

The initial research agent was read-only and could not save its report. This file is the main assistant's independently checked reconstruction; it also includes the simpler global counting proof developed during verification.

## 1. Notation and exact published joint theorem

Let `d_j=p_(j+1)-p_j`, and let `L_m` be the finite joint limit set of

`(d_j/log p_j, ..., d_(j+m-1)/log p_(j+m-1))`.

For bounded vectors and fixed `m`, PNT permits replacing these denominators by the logarithms of the respective global prime indices. The finite joint set is closed.

Sources:

- **BFM:** `/corpus/src/1404.5094/banks-freiberg-maynard-limit-points-of-normalized-prime-gaps-arXiv.tex`.
- **M18:** `/corpus/src/1811.03008/limitp2.tex`.
- **FMT:** `/corpus/src/1511.04468/1511.04468.tex`.
- **Ford:** `/corpus/src/2101.03440/HR_shift.tex`.

BFM's theorem at **256–297** says that, for `m≥2`, among any `8m²+8m` ordered nonnegative real positions `β_j`, there is an increasing subsequence `J_1<...<J_(m+1)` whose successive differences belong jointly to `L_m`.

The proof at **2463–2613** fixes all geometric parameters before the height tends to infinity. Its covered shifts satisfy

`h=(β_j+ε+o(1)) log N`

in group `j`. Actual prime endpoints lie in `[N,3N]`; **there is no unknown dilation factor** on the limiting differences. The total normalized chain diameter is at most `β_last-β_first`. What is unspecified is the selected subsequence.

A caution about occupancy is warranted: `/corpus/src/1510.04577/1510.04577.tex:157–160` explicitly corrects BFM's original (4.20) from `=1` to `≥1`. A theorem merely asserting many occupied groups cannot silently be used as a singleton-interior theorem. The following detector handles that issue directly.

## 2. A pointwise detector allowing heavy endpoint groups

Fix `m≥2`. Let `X_j` be the numbers of primes in spatially ordered groups. Write

`T=sum_j X_j`,  `Q=sum_j binom(X_j,2)`.

Assume every prime between the groups is among their entries. Then

> `T-mQ>m` implies the existence of `m+1` globally consecutive primes lying in distinct groups.

The first and last groups may contain extra primes outside the chosen chain; every occupied interior group of the chain is a singleton.

### Proof

Ignore empty groups. Let `r` count groups with at least two primes, and let `q` count singleton groups. If `r=0` and there is no desired chain, then `q≤m`.

Suppose `r≥1` and still no desired chain exists. There can be at most `m-1` singleton groups before the first heavy group or after the last. Between two consecutive heavy groups there can be at most `m-2` singleton groups: otherwise the last prime of the left heavy group, `m-1` singletons, and the first prime of the right heavy group already give the desired consecutive chain. Therefore

`q ≤ 2(m-1)+(r-1)(m-2) = m+(m-2)r`.

For every integer `v≥2`,

`v-m binom(v,2) ≤ 2-m`.

Consequently `T-mQ≤q+(2-m)r≤m`, proving the contrapositive. No prime is deleted or merged to manufacture a gap.

## 3. Apply the actual weighted arithmetic estimates

Take `K` shifts divided into `M` equal ordered groups. Use the CRT residue, admissibility, smooth-difference, and exceptional-prime hypotheses of M18. The required published inputs are:

- weighted prime-pair upper coefficient `A=3.99`, at **353–390**;
- weighted mass and first moment, and symmetric test-function estimates, at **752–777**;
- the all-interior covering with smooth differences, at **780–817**.

The checked common-mesh and exceptional-prime-omission lemmas in `InitialIntervalAmplificationAttempt.md` give an alternative compatible cover at every fixed geometric precision.

Let `u=ρδ log K`, and divide by the common positive weighted mass. The weighted sum of `T-m-mQ` is bounded below by

`u-m-(A m/2)(1/M-1/K)u² + error`.

The exact pair count here is

`M binom(K/M,2) = (K²/2)(1/M-1/K)`.

For fixed `m,M,u`, the error can be made arbitrarily small in the same parameter order as M18: choose the support parameter `δ` sufficiently small, then `K` sufficiently large and divisible by `M`, then the pre-sieving exponent sufficiently small, and finally the height large. Choose `ρ=u/(δ log K)<1`.

There is no hidden need for a uniform theorem in a changing prime tuple dimension. All of `m,M,K,ρ,δ` are fixed before `N→∞`. The test-function construction is by scaling a fixed-dimensional function: if `s=ρδ`, using `F_K(t/s)` multiplies the ratios `J/I` and `L/I` by `s` and `s²`. It has support inside `sum t_i≤s<δ`, and smooth approximation can be made as accurate as needed. BFM **1749–1776** has these integral scaling factors; its printed argument `F_K(ρδ t)` is reversed relative to those factors. The correctly scaled argument just given is the one yielding them.

Set `u=2m`. The limiting certified main term is

`m-2A m³/M`,

which is positive whenever `M>2A m²`. Thus one may take

`M=floor(7.98 m²)+1`.

For `M=8m²`, the margin is exactly `m/400`. Fixed positive margins absorb the `O(δ)` and approximation errors. The `1/K` correction is favorable.

The positive weighted sum supplies a row satisfying the pointwise detector in §2. Because the cover accounts for **all** primes in the intervening interval, the chain is globally consecutive. Placing the `M` groups near prescribed `β_j log N`, and taking limits, proves:

> Among any `M=floor(7.98 m²)+1` ordered positions there is an increasing subsequence of length `m+1` whose successive differences belong jointly to `L_m`.

Coincident positions can be handled by an arbitrarily small ordered perturbation and closedness of the finite joint limit set. Finitely many subsequence patterns permit passage to a single pattern. The prime indices tend to infinity and the PNT normalization error tends to zero uniformly over this fixed chain.

This is a deduction from the published estimates, not a claim that M18 states this precise corollary, nor a claim of literature priority. It leaves the selected shape unspecified.

## 4. A simpler proof of uniform positive mean scale

The scale-control claim does not require a Maier matrix. Here is a complete argument using only PNT and an ordinary unmasked pair upper bound.

Put `L=log X`. Let `P_X(t)` count unordered prime pairs `X<p<q≤2X` with `q-p≤tL`. There is an absolute constant `B≥1` such that, for every fixed `t>0` and sufficiently large `X`,

`P_X(t) ≤ B t X/L`.                                      (1)

For example, the standard two-linear-form sieve quoted with parameter-independent constants in Ford **265–280** gives, for nonzero even `h≪log X`,

`#{X<p≤2X : p+h prime} ≪ (h/φ(h)) X/L²`.

Odd `h` gives no pairs once `X>2`. The averaging constant is absolute, since

`h/φ(h) = sum_(d|h) μ²(d)/φ(d)`

and hence

`sum_(h≤H) h/φ(h) ≤ H product_p (1+1/(p(p-1)))`.

The Euler product converges. This proves (1); no pair asymptotic or vacancy condition is being used. Ford's stated convention at **87–90** makes the implied constants parameter independent unless indexed otherwise.

### Three exact finite inequalities

List all primes in `(X,2X]` as `q_1<...<q_s`. For fixed `m`, there are `s-m` starts of a full `m`-gap chain inside this list. Define its span `D_j=q_(j+m)-q_j`.

1. Each adjacent gap occurs in at most `m` spans, so

   `sum_j D_j ≤ m(q_s-q_1) ≤ mX`.

2. If `D_j≤h`, the start `q_j` has `m` distinct later prime partners at distance at most `h`. These anchored pairs are distinct for distinct starts. Thus

   `m * #{j:D_j≤h} ≤ #{prime pairs at distance≤h}`.

3. Each adjacent gap occurs in at most `m` starts. Therefore

   `#{j:some gap of chain j is≤h}`

   `≤ m * #{adjacent gaps≤h}`

   `≤ m * #{prime pairs at distance≤h}`.

These inequalities retain every intermediate prime. They hold for any finite increasing point set, not just primes.

### Selection with absolute constants

Choose

`c0=c1=1/(16B)`,  `C=8`.

The following bad starts have combined cardinality at most `X/(4L)`:

- `D_j>CmL`: at most `X/(8L)` by inequality 1;
- `D_j≤c1 mL`: at most `B c1 X/L=X/(16L)` by inequality 2 and (1);
- some gap is at most `(c0/m)L`: at most `B c0 X/L=X/(16L)` by inequality 3 and (1).

PNT gives `s-m=(1+o(1))X/L` for every fixed `m`. Consequently, at every sufficiently large `X`, at least `(3/4-o(1))X/L` starts have

`min gap > (c0/m) log X`,

`c1 m log X < total span ≤ C m log X`.                    (2)

All the primes of each selected chain lie in `(X,2X]`, so every adjacent pair in the list is globally consecutive. Extracting a bounded joint subsequence, and using PNT for the global prime indices, yields the finite vector asserted in the Outcome section.

In particular, the constants are independent of `m`; only the large-height threshold depends on fixed `m`. The proof supplies positive mean normalized scale, but no prescribed relative shape.

## 5. The research agent's alternative scale repair: all reduced columns

For comparison, the initially returned research argument repairs the earlier sparse-Maier-row first-moment collapse by changing the columns. Its arithmetic steps also check out, but §4 is simpler.

Use the FMT progression lemma at **228–267**, with `P` the primorial through `x` after omitting its optional exceptional prime `B0`. Put

`y=c x log x log_3 x/log_2 x`.

Use residue zero for every prime divisor of `P`, and retain **all** columns `t∈(x,y]` coprime to `P`. They are precisely the primes in `(x,y]`, together with possible powers of `B0`. Indeed, `y<x²`, `y/x=o(log x)`, and `B0≫log x`; a surviving composite cannot have either two factors above `x`, or both such a factor and `B0`. The exceptional powers contribute only `O(log x)` columns. Thus `|T|~y/log x` by PNT, with the analogous uniform upper counts on any fixed finite mesh.

For fixed `R≥1`, take `X=exp(y/R)` and `Z=floor(X/P)`. Eventually `Z≥P^D`, as required by FMT. Choose a row `zP+(x,y]` with `1≤z≤Z`. Every prime in it is among the retained columns. FMT's one-prime lower bound and pair upper bound, with Brun–Titchmarsh for the one-prime upper bound, give absolute positive constants such that

`a0 R≤E N_z≤a1 R`, `E N_z²≤a2 R²`,

`E Q_h≤a3 hR²`,

where `Q_h` counts pairs at distance at most `hy`. The last estimate follows by covering `(0,y]` with `O(1/h)` intervals of length `2hy`, and using the fixed-mesh column upper counts. All parameters `R,h` are fixed before `x→∞`.

Paley–Zygmund and Markov then give rows with `≍R` primes, full span `≫y`, and minimum pair distance `≫y/R²`; one can additionally exclude a fixed initial fraction of the rows to keep the height comparable to `X`. Taking `R` a fixed absolute multiple of `m` and selecting `m` consecutive gaps proves the same type of scale statement as §4. This does not preserve a prescribed sparse geometry. Increasing `R` also increases the prime count; it is not a free dilation of one fixed realized vector.

The source's constants are not numerically evaluated here. No assertion about an effective numerical value of `c0,c1` is needed for either proof.

## 6. Ratio and fixed-pattern statements do not provide the missing shape

The following source passages were independently checked:

- `/corpus/src/1311.7003/1311.7003.tex:139–154` gives an infinitely recurring **fixed** subtuple of consecutive primes. The monotonic-gap construction at **326–377** uses shifts `2^j`. Every fixed such vector has total diameter bounded independently of the occurrence height, so its logarithmically normalized vector tends to zero. No controlled recurrence height for growing tuples is supplied.
- `/corpus/src/1504.06860/1504.06860.tex:99–125` proves an isolated gap dominates finitely many neighbors by a power of `log n`. Its displayed increments at **230–245** have exponents between `1/k` and `1/2`; with fixed dimension the resulting tuple diameter is `O_k(sqrt(log N))`. The relative dominance argument at **250–288** therefore does not give a positive finite logarithmic scale.
- `/corpus/src/1406.2658/1406.2658.tex:433–475` describes bounded prime clusters surrounded by gaps at least a constant times an Erdős–Rankin function. It gives no finite logarithmic upper bound on those outside gaps.

Prescribed shape at the controlled positive scale of §4 has not been derived from any of these statements.

## 7. Why the combined checked conclusions still allow a hole

For any fixed `r>0`, put

`S_r=[0,r] union [2r,infinity)`,  `J_m=S_r^m`.

Among any `M` positions, some `ceil(M/3)` have **all** pairwise distances in `S_r`: retain residues in a moving interval of length `r` modulo `3r`, and average. Distances within one retained period are at most `r`, and distances between periods are at least `2r`. Therefore the family `J_m` satisfies every finite-point chain conclusion above whenever `M≥3(m+1)`, including the value in §3. The total-diameter bound telescopes automatically.

The family is compatible with contiguous projections and extensions. It also contains uniform-scale vectors of the type in §4: for example, with `r=1`, the vector `(1,...,1)` has minimum one and total `m`, meeting all the displayed inequalities since `B≥1`.

It even contains every positive relative shape at **some** finite scale: for positive `v_i`, take `s≥2r/min_i v_i`; then `sv∈J_m`. That scale may depend arbitrarily badly on the smallest component or aspect ratio, which destroys the proposed multiplicative-net amplification.

Even the positive-proportion conclusion (2), viewed only as a statement about gap sequences, is compatible with a hole. For example, independent gaps with density

`f(t)=(4/5) 1_(0,1)(t)+(1/5) exp(-(t-2)) 1_(2,infinity)(t)`

have mean one, density at most `4/5`, and joint support `S_1^m`. For every `c0,c1≤1/16`, the chance that an `m`-tuple has minimum at most `c0/m` is at most `(4/5)c0≤1/20`. Its chance of total at most `c1 m` is at most `((4/5)c1 m)^m/m!≤1/20` (use the direct bound for `m=1`, and `m!≥(m/e)^m`, `e<3`, for `m≥2`). Markov bounds the chance of total above `8m` by `1/8`. Hence at least `31/40>3/4` of its chains satisfy the same scale inequalities. This is a probability-law check, not an assumption about prime statistics.

Nevertheless `S_r` misses the entire open band `(r,2r)`. These are structural non-implications only, not models of the actual arithmetic of primes or conjecture disproofs.

## Verification and exact remaining task

`python3 Submission/check_joint_gap_scale.py` passed:

- 87,380 occupancy/chain cases;
- 499 exact rational finite-point thresholds, including the `m/400` margin;
- 197,587 finite span, close-pair, and minimum-gap cases.

These finite checks supplement the general proofs; they do not certify the published analytic inputs or prove an asymptotic by experiment. Main independently read the cited arithmetic source passages and checked their use, including global consecutivity and the order of fixed parameters.

The remaining unproved implication is not merely finite positive mean scale. It is control of the **selected shape/occupancy** strong enough to place an individual globally consecutive gap in every fixed positive normalized band. Neither the new chain detector nor the scale argument gives that. `Spec.lean` has not been edited, and no proof or disproof is submitted.
