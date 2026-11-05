# Growing-parameter sieves and the pointwise Erdős–Straus gap

This is an analytic note, **not** a proof of the conjecture or of `Spec.lean`.
Nothing in `Spec.lean` has been edited. Throughout, a solution means positive,
strictly increasing denominators. The shifted-divisor construction and the
fixed-`K` sieve are described in `ShiftSieveNotes.md`; the exact type-II
criterion is in `Reduction.lean` and `IndependentNotes.md`.

## Scope of the shifted-prime-divisor test

Let `p ≡ 1 (mod 24)` be prime. If `1 ≤ k < p` and a *prime* `q | p+k`
satisfies `q ≡ -1 (mod 4k)`, write `q=4kw-1` and `t=(p+k)/q`. Then

    4/p = 1/(kwt) + 1/(pkw) + 1/(pwt),

and the denominators can be put in strict increasing order. The same formula
works for **composite** `q`; testing only prime `q` gives a sufficient, not a
necessary, condition. In particular, any insoluble prime `p>K` avoids all
prime-divisor tests with `1≤k≤K`. The restriction `p>K` matters when `K`
varies: a `q` from a shift `k≥p` need not produce an ordered solution.

For a prime `q>4(K+1)` define the forbidden residues

    R_q = {0} ∪ {-k (mod q) : 1≤k≤K and q ≡ -1 (mod 4k)}.

They are distinct; `ω(q):=|R_q|≤K+1` and `ρ(q):=ω(q)/q<1/4`.
The class `0` excludes integers divisible by `q`, while the other classes
exclude the corresponding shifted prime divisors. Let `G(z)` be the Selberg
normalizer

    g(q)=ρ(q)/(1-ρ(q)),
    G(z)=Σ_{d≤z, squarefree, prime factors q>4(K+1)} g(d),

where `g` is multiplicative and `g(1)=1`. The Selberg weights from `ShiftSieveNotes.md` are
`λ_d=μ(d)G_d(z/d)/(G(z)∏_{q|d}(1-ρ(q)))`. As `G_d(z/d)≤G(z)` and
`ρ(q)<1/4`, they satisfy `λ_1=1` and
`|λ_d|≤(4/3)^{Ω(d)}≤2^{Ω(d)}`, **uniformly** in `K`.
Their quadratic main term is `1/G(z)`. The CRT gives the following
bound for integers in **any interval of length X** avoiding all `R_q` for
`4(K+1)<q≤z`:

    S(X,z) ≤ X/G(z) + O((Σ_{d≤z} 2^{Ω(d)} ω(d))²).           (1)

The implied constant in this CRT error is absolute; no prime-distribution
theorem is being used. To use (1) for all putative insoluble primes in a
dyadic interval `[X,2X]`, take `K<X` and `z<X`. For a count up to `X`, add
at most `z+K` primes below the range where both conditions hold.

### A sharper **uniform** CRT error

The bound `z^{2+2 log_2(2(K+1))}` in the fixed-`K` note is valid, but unnecessarily
uses `2^{Ω(d)}≤d`. Every prime in `d` is actually greater than `4(K+1)`, so

    Ω(d) ≤ log d / log(4(K+1)).

Consequently, putting `σ_K=log(2(K+1))/log(4(K+1))<1`,

    Σ_{d≤z} 2^{Ω(d)} ω(d)
        ≤ Σ_{d≤z} [2(K+1)]^{Ω(d)}
        ≤ z^{1+σ_K}.

Thus (1) has an **absolute**, `K`-uniform error

    S(X,z) ≤ X/G(z) + O(z^{2+2σ_K}) ≤ X/G(z) + O(z⁴).       (2)

In particular, `K=X^θ`, `z=X^η` with `θ<η<1/4` is not excluded by the
CRT error *alone*: the earlier statement that polynomial `K` forces bounded
`z` refers only to the cruder `log_2` estimate. The further tasks of
bounding `G(z)` with variable moduli and overcoming the pointwise barrier
below are separate. This refinement does **not** prove that such polynomial
`K` is analytically useful.

### A rigorous growing-`K` improvement that still has exceptions

Here is one choice for which all the prime-distribution constants can be
kept independent of `X`. Fix `0<α<1` once and for all and, for sufficiently
large `X`, set

    K=⌊(log X)^α⌋,   z=X^(1/8),
    Z=z^[1/(8(K+1))],   T=exp(sqrt(log Z)).

In particular, `T>4(K+1)` and `Z>T` for large `X`. Take the Euler product
`P(Z)=∏_{4(K+1)<q≤Z}(1+g(q))`, over primes. Under probability weights
proportional to `g(d)` on its squarefree divisors, the expected `log d` is

    Σ_{4(K+1)<q≤Z} ρ(q) log q
       ≤ (K+1) Σ_{q≤Z} (log q)/q
       ≤ 2(K+1) log Z = (log z)/4.

The classical estimate `Σ_{q≤Z} (log q)/q = log Z + O(1)` justifies the
penultimate inequality for large `X`. Markov's inequality leaves at least
`3/4` of `P(Z)` on `d≤z`, hence `G(z)≥(3/4)P(Z)`.

Uniformly for `1≤k≤K`, apply the unconditional Siegel–Walfisz theorem to
primes `q` between `T` and `Z` with `q≡-1 (mod 4k)`. To make the uniformity
explicit, choose fixed exponents

    A > 2α/(1-α),       D > 1+2α/(1-α).

For every `t≥T`, `4K≤(log t)^A` eventually, since
`log T ≍_α (log X)^[(1-α)/2]`. The error in the weighted prime-reciprocal
sum for a single `k` is `O_{A,D}((log T)^(1-D))` by partial summation;
summing over `k≤K` makes it `o(1)`. Therefore, with
`κ_K=Σ_{k≤K} 1/φ(4k)`, one has

    Σ_{k≤K} Σ_{T<q≤Z, q≡-1 (mod 4k)} 1/q
       = κ_K log(log Z/log T) + o(1)
       = (κ_K/2) log log Z + o(1).                           (3)

There is **no** assumption that the `k`-conditions are independent: if one
prime `q` passes several tests, it contributes several times to `ρ(q)`.
Moreover `κ_K≥(1/4)Σ_{k≤K}1/k = (α/4)log log X+O(1)`, and
`log log Z=(1-α)log log X+O(1)`. Since
`log P(Z)=Σ_q -log(1-ρ(q))≥Σ_q ρ(q)`, (3) yields, for example,

    G(z) ≥ exp(c_α (log log X)²),   c_α=α(1-α)/16,           (4)

for sufficiently large `X` (decreasing the leading constant allows for
lower-order terms). Combining (2), (4), and `z⁴=X^(1/2)` gives the valid
unconditional bound

    #{hypothetical insoluble primes p≤X, p≡1 (mod 24)}
       ≪_α X exp(-c_α (log log X)²).                         (5)

The `O(X^(1/8)+X^(1/2))` terms and the finitely many `p≤K` are absorbed
in (5). This is smaller than `X/(log X)^C` for **each fixed** `C`, but
it still tends to infinity with `X`. Siegel–Walfisz has fixed `A,D`
chosen from the fixed `α`: no implicit constant or asymptotic is asserted
uniformly as `α` or `K` changes arbitrarily.

## Why the standard upper bounds cannot become `<1`

**An exact barrier in this Selberg/CRT argument.** For every sieving prime
`g(q)<1/3`; hence `g(d)≤1` and `G(z)≤#{d≤z}≤z`. On a dyadic interval
of length `X`, the nonnegative main term `X/G(z)` in (2) is therefore
**at least `X/z`**. When `z<X`, this upper bound cannot itself be `<1`,
even if its CRT error were magically zero or `K` were optimized.
For `z=X^(1/8)` it is at least `X^(7/8)`. The actual number of
exceptional primes might be zero: this is a limitation of the displayed
upper-bound argument, not a lower bound on the number of bad primes.

Sifting *primes* directly instead of adding the `0` residue does not fix
this standard level-of-distribution calculation. For `q>4(K+1)` the local
probability, conditional on primality, is
`ν(q)/(q-1)` with `ν(q)≤K`, and its corresponding Selberg factor is
still `<1`; thus its normalizer is also `≤z`. Even **assuming exact**
prime equidistribution for the relevant moduli, its main term is
`≍X/(8 log X G_prime(z)) ≳ X/(z log X)`. Using
Bombieri–Vinogradov for the `lcm(d,e)` moduli requires
`24 z²≤X^(1/2)/(log X)^{B}` (for an appropriate fixed `B`), so
`z≤X^(1/4)/(log X)^{B/2}` and this main term is `≫X^(3/4)/log X`.
Moreover BV itself supplies only averaged errors
`O_A(X/(log X)^A)` for *fixed* `A`; the multiplicities `ν(d)` and sieve
weights must also be paid for. Neither an unweighted BV estimate nor
this error can simply be assigned to each individual prime `p`.
Conventional large-sieve/second-moment bounds likewise control an
**average**; a single missed prime costs too little to violate them.

The fixed-`K` estimate `C_A X/(log X)^(1+A)` does not give zero for any
fixed `A`, because its right side grows without bound. To make even this
*formal expression* `<1`, one would need a varying exponent satisfying

    (1+A(X)) log log X > log X + log C_{A(X)}.               (6)

No estimate with constants `C_A` stated only for fixed `A` permits
substitution of `A(X)`. Here `κ_K=Θ(log K)`: the lower bound was used
in (3), while `φ(4k)≥φ(k)` and
`k/φ(k)=Σ_{d|k} μ²(d)/φ(d)` give
`κ_K≤(1+log K)Σ_{d≥1} μ²(d)/(dφ(d))≪log K`
(the last series has convergent Euler product
`∏_q(1+1/(q(q-1)))`). Naively extrapolating the fixed-`K`
exponent to reach (6) would therefore demand `log K` of order at least
`log X/log log X`.
But in the elementary product proof above,
`Z=z^[1/(8(K+1))]`; for such `K` and `z=X^η` with fixed `η`,
`Z<4(K+1)` eventually, so the Euler product contains no primes.
More fundamentally, `G(z)≤z` rules out the required extrapolation
regardless of whether stronger prime-distribution theorems could
estimate the product. The `X exp(-c sqrt(log X))`-scale errors from
classical zero-free-region prime-number theorems, and the fixed-`A`
errors from Siegel–Walfisz/BV, also remain much larger than `1`.
Siegel–Walfisz in its usual form has ineffective constants, so it
would not by itself provide the *explicit cutoff* needed for a finite
computer verification even if the pointwise gap disappeared.

## A concrete CRT obstruction to pointwise type-II counting

For `m≥1`, put `h=4m-1`. If `d|m²`, `d>0`, then

    h does not divide 1+4d.                                (7)

Indeed, put `e=m²/d`. Modulo `h`, `16m²≡1`, so
`h|1+4d` would give `h|1+4e`. Positive divisibility forces
`d,e≥m`; since `de=m²`, both equal `m`, and then
`1+4d=h+2` is not divisible by `h≥3`.

Let `L_B=24·lcm(1,...,4B)`. Dirichlet's theorem gives infinitely many
hard primes `p≡1 (mod L_B)`, for each `B`. For `m≤B`, `h|L_B`,
so (7) makes `h|p+4d` impossible **for every** `d|m²`.
Therefore **no fixed finite family** of type-II `(m,d)` congruence
classes covers all hard primes. Similarly, for any fixed finite set of
shifted-prime sieving divisors `q`, choose a prime `p≡1` modulo their
product and `24`: since `q≡-1 (mod 4k)` implies `q>k+1`, it has
`p+k≡1+k≠0 (mod q)` for all their associated `k`. Finite modular
covering by those tests cannot work either. Neither observation excludes
witnesses with **larger** `m`, untested `q`, or type I.

There is a quantitative pointwise strengthening of the first obstruction.
Since `log L_B=log 24+ψ(4B)=O(B)`, Linnik's theorem gives a least prime
`p_B≡1 (mod L_B)` with `log p_B≤C B` for an absolute `C`.
These primes tend to infinity (`p_B>L_B`), and infinitely many of them
have **no type-II witness with `m≤c log p_B`**, for a fixed absolute
`c>0`. This rules out a purported universal small-`m` count, not
unbounded type II or type I.

For an especially transparent version of the diagonal/off-diagonal issue,
take `B≤sqrt(p)/2`. Then `d|m²` implies `d≤p/4` and the strict-order
condition `d<(pm+d)/h` is automatic for any hit `h|p+4d`:
`(pm+d)/h=p/4+(p+4d)/(4h)>p/4`. The actual count of such pairs is

    N_II(p;B)=Σ_{m≤B} Σ_{d|m²} 1_{h|p+4d}.

Additive-character orthogonality gives the exact expression

    N_II(p;B)=D(B)+R_p(B),
    D(B)=Σ_{m≤B} τ(m²)/(4m-1)
        ~ (1/(4π²)) (log B)³,                                 (8)
    R_p(B)=Σ_{m≤B} [1/(4m-1)] Σ_{r=1}^{4m-2}
               exp(2πi rp/(4m-1)) Σ_{d|m²} exp(2πi 4rd/(4m-1)).

The diagonal asymptotic uses
`Σ_{n≥1} τ(n²)n^{-s}=ζ(s)³/ζ(2s)`; for
`B=⌊p^θ⌋`, fixed `0<θ<1/2`, it indeed has the heuristic size
`D(B)∼θ³(log p)³/(4π²)`. A uniform estimate
`|R_p(B)|<D(B)` would suffice for type-II positivity. Yet for the primes
`p_B≡1 (mod L_B)` the **actual** `N_II(p_B;B)` is zero, so
`R_{p_B}(B)=-D(B)`. For large `B`, these
primes also satisfy `B≤sqrt(p_B)/2`, since
`log L_B=log 24+ψ(4B)∼4B` and `p_B>L_B`.
Thus a uniform `o(D(B))` bound on the nonzero modes is *false* in this
logarithmic `B≍log p_B` regime. Estimating the average or the zero
frequency is not a uniform positivity proof. A new pointwise argument
at sufficiently larger `m`, or a type-I argument, is still possible
in principle but is not supplied by these bounds.

As a small finite diagnostic, the hard prime `p=73` has no **prime**
`q|p+k`, `1≤k<p`, with `q≡-1 (mod 4k)`, although the composite
`q=15|p+2` gives `4/73=1/20+1/292+1/730`. Indeed
`q≥4k-1` and `q≤p+k` imply `k≤(p+1)/3=24`; the **only**
valid divisor pairs `(k,q)` among these shifts are `(2,15)` and `(5,39)`,
both with composite `q`. Accordingly,
any assertion that the prime-divisor test has literally *no*
exceptional primes (rather than only no **large** exceptions after
separate verification) is already false; the test is stricter than
solubility.

**Conclusion.** The growing-`K` sieve can legitimately strengthen
exceptional-density estimates such as (5), but none of the cited
Selberg/large-sieve/PNT/BV inputs yields an upper bound `<1` on bad
primes in all sufficiently large dyadic intervals. The missing theorem
is a **pointwise** witness or a uniform estimate for the nonzero
correlations strong enough to force `N(p)>0` for every hard prime.
Nothing here proves that *every conceivable analytic method* must
fail; such a deterministic theorem would resolve the open prime cases
and, via `Reduction.lean`, the original assertion.
