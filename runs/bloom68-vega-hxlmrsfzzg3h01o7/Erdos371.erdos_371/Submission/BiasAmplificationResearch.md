# Erdős 371: a tensorization barrier to bias amplification

## Outcome and scope

This note does **not** prove natural ordering density `1/2`, and does **not** construct a countersequence satisfying the entire all-integer uniform-stability package. It gives a concrete obstruction to several proposed amplification steps, including one that persists even if genuinely independent copies are granted.

The main new inequality is a **dimension-free bound for scalar orderings of independent tensor copies**. Hildebrand-type positive lower densities imply that every fixed finite quantization of every natural-prefix pair law of the actual largest-prime-factor sequence has a uniform positive product minorization. Consequently, for some `eta > 0` depending on the quantization, any common scalar function H of any number of independent copies satisfies

```
Pr(H(Y) > H(X)) <= 1 - eta/4,
|E sgn(H(Y)-H(X))| <= 1 - eta/2.                         (A)
```

The constants do not deteriorate with the number of copies. A sharper rank-partition inequality bounds the scalar ordering current by `O(r log(1/r))` when the base pair's maximal correlation r is small, again uniformly in tensor dimension. A fully explicit continuous-marginal model with ordering bias `0.01` has r equal to `0.03`: an exact rational certificate gives scalar ascent probability less than `9/16` for **every** number of copies and **every** scalar decoder. Edge majority, in contrast, tends to certainty. Thus irreversibility testing and scalar ordering amplification are different tasks.

There are also two exact arithmetic/algebraic conclusions:

* A unanimity-preserving aggregation of any number of the subpower-multiplier **gap-k copies** supplied by multiplicative stability has the original ordering mean, up to `o(1)`, uniformly in the number of copies.
* A Boolean rule that universally preserves genuine multiplicativity must be a character (a product of selected coordinates). On independent biased signs it cannot amplify their mean. Majority is not such a rule, so a near-certain majority event is not automatically a near-extremal correlation covered by 99%-Elliott.

Finally, product minorization explains a precise failure of a maximum-bias argument: stripping the largest possible symmetric product component produces a law with a **zero pair cell**. That law provably cannot be a natural-prefix law of the original quantized sequence, because the known lower-density theorem excludes that zero. Maximizing over actual natural-prefix laws does not bound its current.

No `.lean` file has been edited or used. In particular no assertion in `Spec.lean` is used as a theorem.

## 1. The fixed-resolution all-scale tensor inequality

### 1.1 A finite probability theorem

Let P be a probability coupling on a finite alphabet E, with the same strictly positive marginal pi at both endpoints. Suppose

```
P(i,j) >= eta pi(i) pi(j)       for every i,j,             (1)
```

where `0 < eta <= 1`. Let `(X_l,Y_l)`, `1 <= l <= d`, be **independent** pairs of law P, and write `X=(X_1,...,X_d)`, `Y=(Y_1,...,Y_d)`.

For every real-valued function H on `E^d`, put

```
u = Pr(H(Y)>H(X)),
v = Pr(H(Y)<H(X)),
t = Pr(H(Y)=H(X)).
```

Then, for every d,

```
min(u+t/2, v+t/2) >= eta/4,                              (2)
u,v <= 1-eta/4,
|u-v| <= 1-eta/2.                                       (3)
```

If the output marginal is nonatomic, t is zero. The same result holds on standard probability spaces whenever the centered conditional-expectation operator has norm at most `1-eta`; finite alphabets are not essential to the proof.

**Proof.** Write `Pi = pi tensor pi`. For `eta < 1`,

```
P = eta Pi + (1-eta) R
```

with R another coupling of pi with itself. Its Markov operator is an L2 contraction, by conditional Jensen. Therefore the centered conditional-expectation operator K of P satisfies

```
||K||_(L2_0 -> L2_0) <= 1-eta.                           (4)
```

For the product pair, decompose `L2(pi^d)` orthogonally according to the subsets of coordinates on which a tensor is mean zero. On a nonempty subset S the operator norm is at most `(1-eta)^|S|`. Hence the centered operator of the product pair still has norm at most `1-eta`, not a bound that tends to 1 as d grows.

First suppose the output marginal is nonatomic, and let A be its lower median set, of probability exactly `1/2`. Then

```
Pr(X in A, Y in A)
 <= 1/4 + (1-eta) ||1_A-1/2||_2^2
 = 1/2 - eta/4.
```

It follows that both crossing probabilities `Pr(X in A,Y notin A)` and `Pr(Y in A,X notin A)` are at least `eta/4`. The equality of the two probabilities uses only equality of the endpoint marginals. Each crossing forces the corresponding scalar order.

For an output with atoms, append independent uniform tie-breakers U,V to the two endpoints and order `(H(X),U)` and `(H(Y),V)` lexicographically. The appended independent pair has centered operator zero, so the same tensor bound applies. The two strict ordering probabilities after tie-breaking are exactly `u+t/2` and `v+t/2`. This proves (2)-(3), including arbitrary atoms. The case `eta=1` is covered directly by independence. QED.

More precisely, if the original centered operator has norm r, the argument gives

```
min(u+t/2,v+t/2) >= (1-r)/4,
u,v <= (3+r)/4,
|u-v| <= (1+r)/2.                                      (5)
```

This is a noninteractive tensor inequality: the *same* scalar map is used at both ends. An arbitrary function of the entire ordered pair is not subject to this conclusion.

### 1.2 Application to actual largest-prime-factor pair laws

Put `f(n)=log P(n)/log n`, let F be its continuous Dickman CDF, and partition the rank interval `[0,1]` into m equal intervals. Let z(n) be the corresponding bin of `F(f(n))`.

Every natural-prefix subsequential pair law P_m of `(z(n),z(n+1))` has marginal

```
pi(i)=1/m.
```

Moreover there is a constant `c_m > 0`, common to **all** these laws, such that

```
P_m(i,j) >= c_m             for all i,j.                 (6)
```

Here is the precise reason for uniformity. Each bin contains an exponent interval strictly inside `(0,1)` of positive length. For each of the finitely many pairs of such intervals, the known positive **lower natural density** theorem gives a strictly positive liminf. Take the minimum of these finitely many lower bounds, decreased if necessary. The continuous marginal removes boundary ambiguities. This is stronger than knowing that one selected limit assigns positive mass to each box.

One may take `eta_m = m^2 c_m`, with c_m decreased to keep `eta_m <= 1`. Thus (2)-(3) apply uniformly to every P_m, every tensor length d, and every H. No numerical value or mesh-uniform lower bound for eta_m is asserted.

There is also an exactly stationary finite-prefix implementation. Close the word `z(1),...,z(N)` into a cycle, replacing its last edge by `z(N)->z(1)`. Its pair law has exactly equal marginals pi_N. For all sufficiently large N, (6) and `pi_N(i)->1/m` imply a product minorization with a fixed positive constant depending only on m. The theorem then applies **simultaneously to every N sufficiently large and every d** for independent draws from this cyclic empirical law. Replacing it by the original d-fold pair law costs at most `d/N` in total variation; one must not suppress that factor if d grows.

This is an actual consequence of Hildebrand-type positivity, but not a contraction of the original limsup current toward zero. It instead shows that a fixed-resolution scalar tensor amplifier cannot have output ordering probability tending to 1 as d increases.

### 1.3 A sharper quantitative inequality: small maximal correlation stays small

Let r be the centered conditional-expectation operator norm of a coupling with equal marginals. For every tensor dimension d and every common scalar H, define

```
J_H = E sgn(H(Y)-H(X)).
```

Then, for every integer q>=2,

```
|J_H| <= (r/q) sum_(a=1)^(q-1) |cot(pi a/q)|
             + r + (1-r)/q.                            (Q1)
```

In particular, writing `H_m=sum_(a=1)^m 1/a`, with `H_0=0`,

```
|J_H| <= (2r/pi) H_floor((q-1)/2) + r + (1-r)/q.         (Q2)
```

If `0<r<=1/2`, choosing `q=ceil(1/r)` gives the explicit dimension-free bound

```
|J_H| <= 2r + (2r/pi)(1+log(2/r)).                       (Q3)
```

Thus the best possible scalar ordering current is `O(r log(1/r))` as r tends to zero. For r=0 let q tend to infinity in (Q1).

**Proof.** Use independent tie-breakers as in Section 1.1 and then the randomized distributional transform to obtain uniform rank variables U,V whose ordering current is J_H. Local postprocessing does not increase maximal correlation, and tensorization has not increased it either.

Quantize U,V into q equal rank bins. Let K be the resulting doubly stochastic transition matrix and let `J_q` denote the bin ordering current. Its centered operator has norm at most r. For `A_ij=sgn(j-i)`, with indices from 0 to q-1, write

```
E = (1/q) 11^T,       B = (I-E) A (I-E).
```

Since K is doubly stochastic, row and column gradients contribute zero, so

```
J_q = (1/q) tr(B^T (K-E)).
```

The centered order matrix B is skew-circulant:

```
B_ii=0,
B_ij = 1-2a/q,       a=(j-i mod q), 1<=a<=q-1.
```

Its eigenvalues are 0 and `i cot(pi a/q)`, `1<=a<=q-1`, up to the immaterial sign from the Fourier convention. Hence its nuclear norm is the cotangent sum in (Q1). Matrix norm duality gives

```
|J_q| <= (r/q) sum_(a=1)^(q-1) |cot(pi a/q)|.
```

The true and quantized signs differ only in a common bin, and

```
Pr(same bin) = tr(K)/q <= [1+(q-1)r]/q.
```

For the trace bound, use an orthonormal basis consisting of the constant vector and q-1 mean-zero vectors; the latter diagonal matrix elements are at most r. These two estimates prove (Q1). Pairing the cotangents and using `cot(x)<=1/x` on `(0,pi/2]` proves (Q2). Finally `H_m<=1+log m`, `1/q<=r`, and `q<=2/r` prove (Q3). QED.

One useful necessary condition follows: **scalar tensor orderings can approach certainty only if the original full pair law has maximal correlation 1.** A small nonzero ordering bias does not imply that condition. The fixed-bin laws of the actual f have maximal correlation strictly below 1 by Section 1.2; no claim about a uniform gap for their infinitely fine limit is made.

## 2. An explicit small-bias model that blocks scalar majority amplification

Fix `0 < lambda < 1`. On uniform ranks `u,v in [0,1)`, let `b(u)=floor(3u)` and define the pair density

```
k_lambda(u,v)
 = 1-lambda + 3 lambda 1_(b(v)=b(u)+1 mod 3).             (7)
```

Equivalently, with probability `1-lambda` choose independent uniform ranks; with probability lambda choose the next bin in the directed three-cycle, then choose a fresh uniform rank within that bin. Both marginals are uniform. Push both coordinates through the strictly increasing quantile Q of any continuous strictly increasing F, in particular the Dickman CDF.

### 2.1 Exact properties

1. **Small nonzero ordering bias:**

```
E sgn(Q(v)-Q(u)) = lambda/3 =: epsilon.                   (8)
```

The independent branch contributes zero. In the cycle branch two bin transitions ascend and one descends.

2. **Maximal correlation exactly lambda:** On mean-zero functions, the operator sends a function to lambda times its next-bin average. Conditional Jensen gives norm at most lambda, and equality holds on nonzero bin-constant mean-zero functions.

3. **Uniform full support:** The pair density relative to `F tensor F` lies between `1-lambda` and `1+2lambda`. In particular every product box has at least `(1-lambda)F(A)F(B)` mass.

4. **Near-diagonal nonconcentration:** If `omega_F(delta)=sup_{|x-y|<=delta}|F(x)-F(y)|`, then

```
Pr(|Q(v)-Q(u)|<=delta) <= 2(1+2lambda) omega_F(delta).     (9)
```

5. **Coordinate short-interval laws, even in every fixed progression:** Realize (7) as the transition law of a stationary Markov chain, with a fresh independent within-bin uniform at each time. For a centered coordinate test phi with variance sigma squared,

```
E |(1/L) sum_(h=1)^L phi(Z_(qh))|^2
 <= (sigma^2/L) (1+lambda^q)/(1-lambda^q),    q>=1.       (10)
```

Indeed the centered h-step transition norm is at most `lambda^h`; sum the covariance bounds. All finite consecutive-coordinate boxes have positive probability, bounded below by `(1-lambda)^(r-1)` times the product of their r marginal masses. Every finite quantization has finite entropy; the three-bin chain even has a strictly positive entropy rate.

These are properties of an explicit stationary model, not a claimed arithmetic realization. This model does **not** satisfy the full uniform arithmetic stability or logarithmic independence package. Its purpose is to test a claimed *universal tensor amplification operation*, for which a single genuine pair law is sufficient.

### 2.2 Majority succeeds as an edge test, but cannot be a scalar ordering

Take d independent pairs from (7), with d odd, and let

```
S_l = sgn(Y_l-X_l),
M_d = sgn(sum_(l=1)^d S_l).
```

There are no ties in the S_l. Hoeffding's inequality gives

```
Pr(M_d=-1) <= exp(-d epsilon^2/2).                       (11)
```

So edge majority really does approach certainty even for arbitrarily small fixed positive epsilon.

But for **every** common measurable scalar H of the d endpoint vectors, (5) gives

```
Pr(H(Y)>H(X)) <= (3+lambda)/4.                           (12)
```

Consequently, counting a zero scalar comparison as a disagreement with a nonzero majority,

```
Pr(sgn(H(Y)-H(X)) != M_d)
 >= (1-lambda)/4 - exp(-d epsilon^2/2).                  (13)
```

For example, with `epsilon=0.01`, `lambda=0.03`, and d large enough that the exponential is below `0.01`, edge majority is positive with probability at least `0.99`, whereas (12) puts every scalar ordering below `0.7575`.

The sharper inequality (Q2) improves this substantially. Set `r=3/100`, `q=48`. Using `pi>3` and the exact rational inequality

```
H_23 = 444316699/118982864 < 359/96,
```

we obtain, for every d and H,

```
|J_H| < H_23/50 + 3/100 + 97/4800 < 1/8.
```

Thus **every scalar ascent probability is less than `9/16=0.5625`**, and its disagreement with a 99%-positive edge majority exceeds `0.4275`. Taking the odd integer `d=100001` already makes the Hoeffding error smaller than `0.01`.

This is stronger than observing that multiplication only supplies dependent copies: it disproves a universal scalar-order amplifier **even after genuine independent copies are supplied**. The obstruction is the retained cyclic information, not a lack of marginal regularity or the possibility of ties.

### 2.3 Finite reversal entropy can saturate without producing a forbidden order

Let an independent fair bit O select either the d-fold pair law or its simultaneous transpose. The majority test above distinguishes the two cases with error at most `e_d=exp(-d epsilon^2/2)`. If `e_d<=1/2`, binary Fano gives

```
I(O; observed d pairs) >= log 2 - h_2(e_d),               (14)
```

where h_2 is binary entropy. Thus the divergence from the symmetrized law tends to its maximum `log 2`. Nevertheless (12) still holds for every scalar H, uniformly in d.

Bounded reversal entropy does not by itself make its saturation a nearly forbidden stable *ordering* pattern. A time-arrow test is a function of both endpoints, not necessarily a comparison of two common scalar observables. No symmetry has been transferred to ergodic components here.

## 3. The precise maximum-bias failure of noise subtraction

Let P_m be a non-independent finite-quantized natural-prefix pair law. Define its maximal product minorization coefficient

```
alpha = min_(i,j) P_m(i,j)/(pi(i)pi(j)).
```

Then `0 < alpha < 1`, and

```
R = (P_m - alpha pi tensor pi)/(1-alpha)                 (15)
```

is another coupling with the same marginals. For any antisymmetric current j, whose product-law mean is zero,

```
E_(P_m) j = (1-alpha) E_R j.                             (16)
```

It is tempting to choose P_m on a maximum-current subsequence and then bound `E_R j` by the same maximum, obtaining a strict contraction. This application of maximality is invalid for a demonstrable reason:

* The minimum defining alpha is attained. Hence R has at least one **zero** pair cell.
* Every natural-prefix pair law of the original z satisfies (6).
* Therefore R is **not** a natural-prefix pair law of that sequence.

Thus the natural-prefix family is not closed under the operation that produces the amplified current. It is not legitimate to treat R as a new admissible natural scale, residue-decoupled component, or ergodic component with inherited arithmetic properties.

For an explicit finite test, let C be the uniform directed three-cycle coupling and let

```
P_t = (1-t) Pi + t C,             0 <= t <= lambda < 1.   (17)
```

This is a compact convex family with common uniform marginal, uniform positive entries, and maximum ordering current `lambda/3 > 0`. Its associated Markov chains obey the coordinate short-interval bounds uniformly in t. At the maximizer, maximal product subtraction returns C, outside the family and with zero cells. The elementary properties of this family do not imply any inequality `B <= theta B`, `theta<1`.

The usual finite-block entropy monotonicity does not repair this lack of closure. For the three-bin Markov chain at t,

```
H(Z_0,...,Z_(L-1)) = log 3 + (L-1) h(t),                 (18)
```

where h(t) is the entropy of its positive transition row. A one-time pair entropy deficit is compatible with every L and a nonzero current; it does not generate a fresh fixed entropy loss at each refinement. Conditional-refinement entropy inequalities also do not compare different natural prefixes.

This excludes the product-noise-stripping version of maximum-bias/finite-entropy amplification. It does not exclude an arithmetic maximum principle that supplies a genuinely new closure or return property.

## 4. What the arithmetic copies actually permit

### 4.1 Uniform non-amplification of all subpower gap copies

For the actual largest prime factor, put

```
s_n = sgn(P(n+1)-P(n)),
M_n = max(P(n),P(n+1)),
S_k(n) = sgn(P(k(n+1))-P(kn)).
```

The elementary identity `P(kn)=max(P(k),P(n))` gives **exactly**

```
S_k(n) = s_n 1_(P(k)<M_n),              n,k>=1.           (19)
```

Thus no nonzero copy ever has the opposite sign: large multipliers can erase a sign, but cannot create a fresh sign.

Let `k_1,...,k_d <= K`, allowing both d and K to depend on N. Let T be any function from `{-1,0,1}^d` to `[-1,1]` satisfying

```
T(+1,...,+1)=+1,       T(-1,...,-1)=-1.
```

On `M_n>K` every input is exactly s_n, so

```
|E_(n<=N) T(S_(k_1)(n),...,S_(k_d)(n)) - E_(n<=N) s_n|
 <= (2/N) #{n<=N: M_n<=K}
 <= 2 Psi(N,K)/N.                                      (20)
```

For `log K=o(log N)`, the right side tends to zero by the continuous Dickman marginal at zero. For example, discard `n<sqrt N`; for each fixed delta>0, eventually `K<=n^delta` on the rest, and then let delta tend to zero after taking the natural-scale limsup. This proves the assertion uniformly in d, without a union bound over the copies.

**Conditioning audit:** S_k is a gap-k comparison based at a multiple of k, at changed scale kN. It is not `s_(kn)`, which compares `kn` and `kn+1`. Replacing S_k by the latter, or averaging its residue conditioning away, is an additional unproved step. Equation (20) is a no-amplification result for precisely the copies the arithmetic supplies, not an estimate of other residue classes.

With only the stated normalized stability bound, the analogous conclusion follows by excluding `n<sqrt N` and the strip

```
|f(n+1)-f(n)| <= 4 log K/log N.
```

Outside that strip all gap-k signs for `k<=K` agree simultaneously; the supplied all-scale diagonal nonconcentration makes its density `o(1)` for subpower K. The exact raw identity (19) is stronger.

### 4.2 Universal multiplicativity-preserving Boolean maps cannot amplify

Suppose a Boolean aggregation rule `T:{-1,+1}^d -> {-1,+1}` preserves multiplicativity for **arbitrary** tuples of completely multiplicative sign functions. Then

```
T(xy)=T(x)T(y),       T(1,...,1)=1.                      (21)
```

To see necessity, assign arbitrary vectors x and y as the values of the tuple at two different primes; multiplicativity at their product forces (21). Conversely (21) plainly suffices. Every such homomorphism of the sign cube is a character:

```
T(x)=product_(l in A) x_l                               (22)
```

for a subset A. If independent signs have common mean epsilon with `0<epsilon<1`, then for nonempty A,

```
E T(S_1,...,S_d) = epsilon^|A| <= epsilon.               (23)
```

The empty character is the constant 1 and has no non-pretentiousness. Majority is not a character. For three coordinates, the two vectors `(-,-,+)` and `(-,+,-)` both have majority minus, but their product `(+,-,-)` also has majority minus.

There is a related extraction barrier: under independent biased signs, **every nonconstant Walsh monomial** has mean at most epsilon, even though the majority mean tends to 1. Expanding majority into monomials therefore does not furnish a nearly extremal individual product correlation.

This is a statement about universal class-preserving operations, not a claim that every specially chosen arithmetic function obtainable by nonlinear operations fails to be multiplicative.

## 5. What the positive-density and 99%-Elliott theorems do not say

### 5.1 Near absence versus absence on logarithmic windows

A useful sharp mass-transport calculation makes the quantifier issue explicit. Let `0<=h<=1` on `[0,X]`, and suppose its natural mean is delta. For any `omega>1`, decreasing rearrangement against `1/t` gives

```
(1/log omega) integral_(X/omega)^X h(t) dt/t
 <= min(1, log(1+delta omega)/log omega).                (24)
```

If `delta <= 1-1/omega`, the maximum is attained by placing all the available mass on `[X/omega,X/omega+delta X]`; otherwise one fills the entire window. The discrete version has error `O(omega/(N log omega))`, harmless for the available `omega<=log(3N)` windows.

For a **fixed** positive delta, the right side tends to 1 as omega tends to infinity. If instead `delta=delta_j->0`, choosing, for example, `omega_j=delta_j^(-1/2)` (truncated to the permitted slowly growing range) makes it tend to zero. This is the distinction used in passing *zero* lower natural density to logarithmic-window absence.

A maximum-bias subsequence with current B below 1 only gives a fixed minority mass `(1-B)/2`; it does not supply the vanishing defect required by that argument. Bounded-width isolated logarithmic bad-scale neighborhoods remain compatible with the given log-window and log-Banach exceptional-scale results. Maximality gives no return from the amplified residual (15) to a natural scale.

### 5.2 The exact scope of 99%-Elliott

The relevant checked source is Teräväinen, *On the Liouville function at polynomial arguments*, arXiv:2010.07924, `main.tex:87-104`, Theorem `theo_multiplicative-nonpret`. It concerns **fixed genuinely multiplicative functions** in a product at fixed distinct affine forms; one function is root-of-unity-valued of fixed order q and non-pretentious relative to every Dirichlet character. Its conclusion is

```
limsup_X |E_(n<=X) product_(i=1)^k g_i(a_i n+h_i)|
 <= 1-delta(a_i,h_i,q).                                 (25)
```

“99%” does not mean the numerical cutoff 0.99 for arbitrary pattern statistics. The source explicitly notes that the available delta deteriorates like a tower of exponentials as k increases.

Consequently:

* The ordering sign s, a majority of ordering signs, and a likelihood-ratio test between a pair law and its transpose are not automatically correlations of the form (25).
* The elementary class-preserving rules (22) do not amplify. A Walsh expansion of majority does not solve this, by (23).
* Arbitrary Boolean operations preserve stability of already stable one-site sets, but a shifted **pair comparison** is not thereby a stable one-site set; dilation changes its gaps. Equation (19) specifies the actual change.
* A fixed event having very small but positive density does not contradict a qualitative positive-lower-density assertion. If complexity grows to make its defect vanish, the fixed-pattern lower bound or the gap in (25) cannot silently be held uniform. There is no supplied comparison between an amplified error and that complexity-dependent gap.

The positive box input used in Section 1 is Teräväinen, arXiv:1710.01195, `binary_correlations_arxiv2.tex:175-184`, Theorem `theo_hildebrand`. The zero-lower-density premise in the weakly stable-set correspondence principle can be checked directly in Tao--Teräväinen, arXiv:1904.05096, `main.tex:443-484`; it is not a correspondence preserving a small nonzero natural defect unchanged.

## 6. Conclusion

No new all-scale contraction of `limsup |E_(n<=N) s_n|` is established. Instead the following proposed amplifications have rigorous obstructions:

1. **Arithmetic dilation copies:** every unanimity-preserving subpower-copy amplifier obeys the non-amplification inequality (20), uniformly in the number of copies.
2. **Independent scalar tensor copies:** the actual fixed-bin positive-density input gives (2)-(3), uniformly in tensor dimension. The rank-partition estimate (Q1)-(Q3) further gives `O(r log(1/r))` control for small maximal correlation. In the explicit `epsilon=0.01` model every scalar ascent probability is below `9/16`, even though edge majority exceeds 99%.
3. **Finite reversal entropy:** even genuine independent products can saturate their bounded time-arrow information while (12) forbids a nearly certain scalar order.
4. **Maximum bias plus symmetric-noise stripping:** the amplified coupling has a zero cell and hence is provably outside the natural-prefix family. Maximality cannot be applied to it.
5. **99%-Elliott:** universal multiplicativity-preserving Boolean maps are characters and do not amplify; majority is not a single correlation in the theorem's class, and its complexity cannot be ignored.

A successful argument would have to add a genuine arithmetic way to retain or return to the admissible class while generating fresh directional information. These results neither supply that step nor assume it under a new name. They do not prove that the entire stated package is insufficient, or rule out all possible maximum-principle or entropy arguments.

## Verification

`python3 Submission/BiasAmplificationVerification.py` passes; its output is saved in `BiasAmplificationVerification.log`. The script checks the finite model, the raw gap-copy identity on actual integers, the tensor centered-operator norms, exact optimal finite scalar orderings in small dimensions, Boolean homomorphisms, majority amplification, and the finite decreasing-rearrangement extremizer. The probability and combinatorial checks use exact rational arithmetic where practical; floating-point spectral and tail checks are sanity checks of the proofs above.

Selected results:

* The raw identity (19) passed on **640,000** actual `(n,k)` pairs.
* The centered order-matrix singular-value formula passed for `q=2,...,64`.
* The exact rational current certificate for the `epsilon=0.01` model is `4458079583/35694859200 < 1/8`; no Monte Carlo estimate is used to prove its scalar obstruction.
* With `d=100001`, the Hoeffding error is below `0.006738`, while the rigorous scalar-majority disagreement bound exceeds `0.4308`.
* Uniform and nonuniform marginal examples both pass the tensor gap checks. For the uniform model at `lambda=1/5`, the exact optimal scalar currents on one and two discrete-bin copies are `1/15` and `19/225`, respectively. Thus **some modest scalar amplification is possible**; the result is not the false claim that every scalar decoder leaves the original bias unchanged.
* `python3 -m py_compile Submission/BiasAmplificationVerification.py` also passes.

The unchanged `Submission/Spec.lean` SHA-256 is

```
d48bb112dcd4fd5c98dae80077b7384df62a14ef9a919fe7d476b9c5ace427bb
```
