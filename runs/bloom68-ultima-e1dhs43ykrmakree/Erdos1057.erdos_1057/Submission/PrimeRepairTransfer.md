# Prime-pool repair transfer — informal research derivation

**Status.** This is not a Lean proof and does not settle `Spec.lean`. The derivation below was checked by the parent and independently audited by a research agent; neither found a fatal error in the mild-superpolynomial repair variant. Its analytic inputs are not formalized here. The numerical smooth-prime input was checked in a secondary source quoting Baker–Harman, not in the original Baker–Harman paper. No claim of a verified new record or priority is made.

## 1. Input and proposed conclusion

Fix `0 < gamma < 1/2`. Suppose that, at every sufficiently large real scale `z`, there are an integer `M` and a set `P` of primes satisfying

* `P` is contained in `[w,z]`, where `w=z^(1-o(1))`;
* `N=|P|=z^(1-o(1))`;
* `p-1 | M` and `gcd(p,M)=1` for every `p in P`;
* `log M = O(z^gamma)`.

The proposed implication is, for every fixed `epsilon>0`,

```
C(U) >= U^(1-gamma-epsilon)  for all sufficiently large U.
```

In particular, this alone does **not** give exponent one for a fixed positive `gamma`.

The exact-lambda mandatory-prime device in earlier notes is unnecessary: it is enough that all seed predecessors divide `M`. Use all `t`-subsets below. Since `p-1` are distinct divisors of `M`, `N <= tau(M)`. The standard divisor bound implies

```
log M / log z -> infinity.
```

Thus every fixed positive power of `M` eventually exceeds `z`.

Choose fixed `gamma < beta < 1`, put `t=floor(z^beta)`, `X=z^t`, and let `S` be the set of products of `t` distinct primes in `P`. Unique factorization gives

```
S_count = binom(N,t) = X^(1-beta+o(1)).
```

All seeds are units modulo `M`. Choose a residue `a mod M` containing at least `S_count/phi(M)` seeds; denote this subfamily by `S_a`.

## 2. Character estimates for the seed family

Call a nonprincipal primitive character `psi` bad if

```
|sum_{p in P} psi(p)| > 3N/4.
```

For every integer `h>=1`, let `a_h(n)` count ordered `h`-tuples of primes from `P` with product `n`. Then

```
sum_n a_h(n) = N^h,
0 <= a_h(n) <= h!,
sum_n a_h(n)^2 <= h! N^h,
support(a_h) subset [1,z^h].
```

The ordinary primitive multiplicative large sieve therefore gives

```
B(D) := #{bad primitive characters of conductor <= D}
     << (D^2+z^h) h! (4/3)^(2h) N^(-h).
```

There is one factorial, not its square, and no condition `h << sqrt(N)`.

Set

```
m = log M, u = log m, R = exp(m u^2), H_max = M R.
```

For any fixed `A>0` and `kappa` with `2 gamma < kappa < 1`, uniformly on

```
M^A <= D <= 2 M R,
```

take `h=ceil(2 log D/log z)`. The bounds

```
log h <= gamma log z + O(log log z),
log(z/N) = o(log z),
log z = o(log D)
```

give `B(D) <= D^kappa` eventually. The last bound handles rounding. Mildly increasing `R` has not changed the leading exponent `2 gamma`.

For a good character `chi` modulo a modulus `Q`, assume every seed prime is a unit modulo `Q`, and its primitive inducing character is good. The seed sum is an elementary-symmetric coefficient. Cauchy's coefficient estimate on the circle of radius `rho=t/N` gives

```
|sum_{n in S} chi(n)|
 <= (N/t)^t exp(3t/4 + O(t^2/N)).
```

Comparison with the binomial coefficient yields

```
|sum_{n in S} chi(n)| <= S_count exp(-c t)
```

for any fixed `c<1/4` eventually. Here `t^2/N=o(t)`, even when it is not `o(1)`.

## 3. A capped inverse progression

Let

```
K0 = lcm(M rad(M),24) <= 24 M^2.
```

Choose a unit `b mod K0` extending `a^(-1) mod M` such that

```
v_l(b-1) <= v_l(M)  for every prime l | M.
```

When the prescribed residue is `1 mod l^e`, choose a nonzero next base-`l` digit. Otherwise the cap is already forced. This also works at `2`: if `v_2(M)=1`, choose `b=3 mod 4`, then either lift modulo 8. If `3` does not divide `M`, choose `b=2 mod 3`. All conditions are compatible by CRT.

Any repair prime `q=b mod K0` now has no old-prime-power extension in `q-1`. The desired extra condition is

```
l | q-1 and l not dividing M  ==>  l >= Y,
Y = M^A.
```

Since `Y>z`, this will make every seed a unit modulo `lcm(M,q-1)`.

## 4. Sifted primes in a mildly superpolynomial interval

This section replaces the missing fixed-power repair-prime hypothesis from earlier notes. Let `s` be a sufficiently large fixed sieve parameter, `D_s=Y^s`, and choose a fixed `B>As+3`. All initial sieve moduli `K0 d`, `d<=D_s`, are at most `T1=M^B` eventually.

### Uniform prime theorem

Use Thorner–Zaman, *Refinements to the prime number theorem for arithmetic progressions*, `/corpus/src/2108.10878/RefinementsPNTAP-arXiv.tex`, main theorem, lines 18–37. With `x=R` and `h=R/2`, it gives log-weighted prime counts

```
sum_{R/2 < q <= R, q=c mod Q} log q
 = lambda(Q,c) R/(2 phi(Q)) (1+O(E_C)),
E_C << exp(-c_C u^2),
```

uniformly for `M <= Q <= M^C`, for every fixed `C`. Its hypothesis `lambda h/phi(Q) >= R^(theta+epsilon0)` is satisfied eventually with a fixed sufficiently small `epsilon0>0`: the effective exceptional-zero lower bound gives a polynomial-in-`M` lower bound for `lambda`, while `R` exceeds every fixed power of `M`.

If a local exceptional real character exists, its multiplier is

```
lambda(Q,c) = (2/R) integral_{R/2}^R (1-chi_*(c) v^(beta_*-1)) dv.
```

Otherwise it is 1. For an adverse exceptional sign, this is comparable to `min(1,(1-beta_*) log R)`; for the favorable sign it exceeds 1. Working directly with the interval theorem avoids any questionable subtraction of two close long-interval asymptotics.

Importantly, the theorem's error is **relative to this multiplier**, even in the adverse exceptional case. Also `E_C` beats every fixed negative power of `log M`. At the earlier choice `R=M^C`, it was only a fixed small constant, which was insufficient for the sieve.

### Exceptional-character alternatives

Fix a large constant `L`, e.g. `L=100`. Say an exceptional primitive real zero with conductor at most `T1` is dangerous when

```
(1-beta_*) log R <= L log log M,
```

or equivalently its gap is at most `L/(m u)`.

Landau–Page gives at most one such character eventually. Its strip constant need not equal the local Thorner–Zaman constant: `L/(m u)` is eventually smaller than any fixed positive multiple of `1/log(M^C)` for fixed `C`.

* **No dangerous zero.** Every local exceptional secondary term for the initial sieve moduli is `O((log M)^(-L+o(1)))`. The prime counts have their ordinary common main term with this additional error.

* **Dangerous conductor `f_* | K0`.** Every initial sieve modulus contains the same locally exceptional character. Its value on the CRT residue is `chi_*(b)`, independent of `d`, so the common multiplier factors out of the sieve. An effective Page bound at the primitive conductor, `1-beta_* >> f_*^(-1/2) (log f_*)^(-2)`, and `f_* <= 24 M^2`, give the safe lower bound `lambda_* >> M^(-2)` eventually. The sharper bound quoted by Thorner–Zaman also suffices.

* **Dangerous conductor `f_*` not dividing `K0`.** Refine to `K1=lcm(K0,f_*) <= M^(B+3)` eventually. A primitive real conductor has squarefree odd part and 2-part at most 8. Since `24 | K0`, there is an outside prime `l>=5`. Choose a unit residue `b1 mod K1` extending `b`, excluding `1 mod l` at every new prime, and satisfying `chi_*(b1)=-1`. This is possible because both Legendre signs occur among residues other than 0 and 1 for every prime at least 5. All later sieve moduli `K1 d` have size at most `M^(B+As+4)`, contain this character, and the dangerous gap places it inside each local exceptional strip eventually. Local uniqueness then ensures it is the character appearing in the prime theorem. Their common multiplier is at least 1. There is no endless iteration of new exceptions.

In the first two cases set `K1=K0,b1=b`. In every case `K1=M^O(1)`. Every prime factor of `K1` outside `M` is forced not to divide `q-1` by the chosen progression.

### Linear sieve

Sieve the log-weighted primes in `q=b1 mod K1` by primes below `Y` not dividing `K1`. For squarefree `d` coprime to `K1`, the CRT progression `q=1 mod d` has modulus `K1 d`. Its local density is `1/phi(d)`. In the common-exception cases its count is

```
W/phi(d) (1+O(E_C)),
W = lambda_* R/(2 phi(K1)).
```

In the no-danger case use `lambda_*=1` and error `E_C+O((log M)^(-L+o(1)))`.

Use lower fundamental-lemma weights, of level `D_s=Y^s`, with fixed sufficiently large `s`, bounded absolute value. The uniform upper sieve-dimension condition holds after excluding any set of primes. Do not assume a uniform two-sided dimension asymptotic. The needed bounds are

```
V(Y) = product_{l<Y, l not dividing K1} (1-1/(l-1)) >> 1/log Y,
sum_{d<=D_s} |weight_d|/phi(d) << log D_s.
```

Consequently the error/main ratio is

```
O((E_C+(log M)^(-L+o(1))) log D_s log Y) = o(1).
```

Dividing the log-weighted count by `log R` proves a candidate-prime lower bound

```
#Q_candidates >> R/(K1 M^2 log R log Y).
```

Every candidate satisfies the inverse progression, cap, and desired roughness. The extra modulus `K1` has fixed-power size, though its exponent can be large.

Sources checked: TZ main theorem and exceptional bounds above; Green `/corpus/src/2206.08001/2206.08001.tex`, lines 615–624 for Landau–Page and 725–727 for the effective Page bound; Koukoulopoulos `/corpus/src/0905.0163/0905.0163.tex`, fundamental lemma near lines 520–545. TZ's comparison with Gallagher, lines 279–291, also records a relative prime theorem sufficient in this modulus range.

## 5. Removing the bad character incidences

For a candidate prime `q`, put `Q(q)=lcm(M,q-1) <= M R`.

The old cap implies that any conductor `f | Q(q)` has the decomposition

```
f=f0 d, f0 | M, gcd(d,M)=1.
```

If `f` does not divide `M`, roughness implies `d>=Y`. The progression additionally implies `gcd(d,K1)=1`. Thus the incidence of a particular such conductor in candidate primes is bounded by

```
R/(K1 d)+1.
```

Without the old cap, using only `f/gcd(f,M) | q-1` would be incorrect: the exact required old-prime factors are full prime powers whose exponents in `f` exceed their exponents in `M`.

For `T<=d<2T`, all relevant primitive bad characters have conductor at most `2MT`, so their number is at most `(2MT)^kappa`. Dyadic summation gives

```
sum_{bad f=f0 d, d>=Y} 1/d << M^kappa Y^(kappa-1).
```

This counts characters, not just conductors; it already includes every possible old part `f0`. Hence the total number of bad non-`M` incidences is

```
I << (R/K1) M^kappa Y^(kappa-1) + (MR)^kappa.
```

The `+1` CRT endpoint contribution is essential. Divide by the candidate-prime lower bound to obtain

```
I/#Q_candidates
 << log R log Y *
    (M^(kappa+2-A(1-kappa)) + K1 M^(kappa+2) R^(kappa-1)).
```

Choose fixed `A` so that `A(1-kappa)>kappa+2`. Both terms tend to zero: the first by a strict power saving in `M`, the second because `K1` has fixed-power size and `R` exceeds every fixed power of `M`. For example `kappa=.60,A=10` gives first power `M^(-1.4)`.

There is therefore a candidate repair prime with no bad non-`M` conductor dividing `Q(q)`.

## 6. Projection, orthogonality, and Korselt

For this prime `q`, all seed primes are units modulo `Q=Q(q)`. Define

```
F(chi) = sum_{n in S} chi(n),
F_a(chi) = sum_{n in S_a} chi(n).
```

Projection gives

```
F_a(chi) = (1/phi(M)) sum_{theta mod M} conjugate(theta(a)) F(chi theta).
```

If `chi` is not induced from `M`, neither is `chi theta`; its primitive conductor divides `Q`, so every such twist is good. Thus `|F_a(chi)| <= S_count exp(-ct)` with no extra factor `phi(M)`.

Character orthogonality counts seeds satisfying `nq=1 mod Q`. For each character induced from `M`, its contribution `chi(q)F_a(chi)` is exactly `|S_a|`, because `aq=1 mod M`. There are `phi(M)` such characters. The remaining error is bounded by `S_count exp(-ct)`. Therefore

```
#{n in S_a : nq=1 mod Q}
 = phi(M)|S_a|/phi(Q) + O(S_count exp(-ct))
 >= S_count/(MR) - S_count exp(-ct).
```

Now

```
log(MR) = O(z^gamma (log z)^2) = o(t),
```

so this is at least `S_count/(2MR)` eventually.

Every resulting integer `nq` is squarefree and composite. Its seed-prime predecessors divide `M`, and `q-1` divides `Q`; all therefore divide `nq-1`. Korselt proves that `nq` is Carmichael. Multiplication by the one fixed prime `q>z` is injective on seeds. Consequently

```
C(XR) >= S_count/(2MR) = (XR)^(1-beta+o(1)).
```

## 7. All-scale conclusion and the remaining exponent-one gap

Pools at every sufficiently large `z` allow, for each large target `U`, a choice with `t log z=(1-delta+o(1))log U`, for fixed small `delta>0`. Since `log R=o(t log z)`, the constructed integers are at most `U` eventually. Letting the fixed losses `delta` and `beta-gamma` be sufficiently small gives the claimed bound `C(U)>=U^(1-gamma-epsilon)`.

Freiberg `/corpus/src/1008.1978/1008.1978.tex`, Theorem 2.1, lines 52–66, quotes Baker–Harman [1998, Theorem 1] as providing at least `z/(log z)^c` primes with `p-1` having largest prime factor at most `z^.2961`, for all sufficiently large `z`. Discard primes below `z/(log z)^(c+2)`. The master modulus

```
M = product_{l<=z^gamma, l prime} l^floor(log z/log l)
```

contains every remaining predecessor, has prime support disjoint from the pool, and satisfies `log M <= pi(z^gamma) log z = O_gamma(z^gamma)`. If this input and the transfer are used, the resulting exponent is `.7039-epsilon`, still not one.

To obtain the theorem in `Spec.lean` by this route one needs suitable pools for **arbitrarily small fixed gamma**, with all-scale coverage. No such input was proved. Lowering the transfer loss does not lower the fixed input gamma.

The previously audited localization gives no bootstrap. From exponent `1-gamma` it forces positive smooth-prime mass only at smoothness parameters

```
delta > gamma/(1-2gamma),
```

which is larger than gamma. For gamma `.2961`, that threshold is approximately `.72609122`, and the forced limsup prime-count exponent is only approximately `.27390878`. Neither inverse-lambda pigeonholing nor multiplying the certified blocks improves this arithmetic input.

**Final submission status:** `Spec.lean` has not been edited; both original `sorry`s remain. This research note is not a proof or a disproof of its conjecture.
