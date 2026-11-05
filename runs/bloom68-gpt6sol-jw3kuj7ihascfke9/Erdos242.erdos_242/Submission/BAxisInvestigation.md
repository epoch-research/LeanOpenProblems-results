# B-axis for hard primes: pointwise arithmetic and finite verification

This is a **partial investigation, not a proof that every sufficiently large prime has a B witness**, and not a proof or disproof of `Spec.lean`. The code in the accompanying `BAxis*.cpp` files does not change `Spec.lean`. A B-free **prime** would refute only this stronger subfamily, not Erdős–Straus: type I or other type-II witnesses might remain.

Throughout, let `p ≡ 1 (mod 24)`, `p ≥ 73`; primality is required only where explicitly stated. Write `p=24k+1` and `x₀=(p+3)/4=6k+1`. The B assertion is

    ∃ m,d: 1≤m≤(p−1)/6, d|m, h=4m−1 | p+4d.

**Scope warning: `d|m` is not `d|m²`.** The three `NO_B` primes `193,2521,66529` are exceptions to the **restricted** condition displayed above, but all three satisfy the broader `d|m²`, `4d<p` condition from `Partial.lean`/`ReciprocityFamilies.lean`: respectively `(m,d)=(4,8),(12,16),(10,50)`. All have `d∤m`; see the sorry-free `FullSquareAxis.lean` and the analysis in `FullSquareAxis.md`. The `BAxis*.cpp` negative certificates and the one-candidate-per-`m` shortcut below **do not test** that broader condition. In fact `p=337,m=8` admits both `d=1` and `d=32` for `d|m²`.


## Exact bidirectional parametrization and shorter exhaustive searches

Given a modular pair, set

    h=4m−1,   a=(p+4d)/h,   n=m/d,
    x=ma−d=(p+a)/4,       t=na−1=x/d.

Because `h≡3 (mod 4)` and `p+4d≡1 (mod 4)`, `a≡3 (mod 4)` and `a≥3`; moreover `t≥2`, `t|x`, `t≡−1 (mod a)`. For `p≥73`, `a<p`, hence `p/4<x<p/2`: indeed `(4m−1)p > p+4m ≥ p+4d = (4m−1)a`. Conversely, given such `x,a,t`, let `d=x/t`, `n=(t+1)/a`, `m=dn`. Then `d|m` and

    p+4d=a(4m−1).

Also `p=a(4m−1)−4d ≥ 8m−3`, whence `m≤(p+3)/8≤(p−1)/6` for `p≥13`. These are exact equivalences, not probabilistic tests. The resulting ordered fraction identity uses `x=dt`, `y=pm`, `z=pmt`; its numerator is `pm+d(t+1)=m(p+a)=4mdt`, and `x<y<z`.

There is **at most one proper-divisor candidate per `m`**. Put `r=p mod h`. If `d=m`, the condition is `r=h−1`. If `d<m`, then `0<4d<h` and `0≤r<h`, so divisibility requires `r+4d=h`, i.e. the only candidate is `d=(h−r)/4`, and it must be an integer dividing `m`. This is the complete direct-search test.

The smallest quotient `a=3` has a particularly sharp criterion. Since `x₀≡1 (mod 3)` and `x₀` is odd,

> **`a=3` works if and only if `x₀` has a prime factor `r≡2 (mod 3)`.**

For necessity, a divisor `t≡−1 (mod 3)` must contain such a prime. For sufficiency, `s=x₀/r≡2 (mod 3)`, so set `d=r`, `m=r(s+1)/3=(x₀+r)/3`; then `p+4d=3(4m−1)`. Choose the smallest such `r`. Since `s` also has a prime factor `2 (mod 3)`, it is at least `r`; thus `r≤√x₀` and `m≤(x₀+√x₀)/3`.

If `a=7`, then `x=x₀+1=6k+2≡2 (mod 3)` and `t≡6 (mod 7)`. The first positive possibility `t=6` cannot divide `x`, so `t≥13`, `d=x/t≤x/13`, and

    m=(x+d)/7 ≤ (p+7)/26.

If `a≥11`, the elementary inequality `p≥4m(a−1)−a` gives

    m≤(p+a)/(4(a−1))≤(p+11)/40≤(p+7)/26.

Consequently an **exact** alternative for hard `p` is

    B(p) ↔ (x₀ has a prime factor 2 mod 3)
           OR (∃ m≤⌊(p+7)/26⌋, d|m, 4m−1 | p+4d).       (1)

In particular, if a B witness exists at all, some witness has `m≤⌊(x₀+⌊√x₀⌋)/3⌋`. Neither bound proves existence. For example, `p=1009`, `x₀=253=11·23`, has no witness at or below `⌊(p+7)/26⌋=39`, but has the `a=3` witness `(m,d)=(88,11)`.

A different exact **meet-in-the-middle certificate**, used by `BAxisCertificate.cpp`, is convenient for a single very large candidate. Choose `J≥1`; test *every* divisor `t|x₀+j` for `0≤j<J`, with `t>1` and `t≡−1 (mod 4j+3)`. Let `A=4J+3` and

    M=⌊(p+A)/(4(A−1))⌋.

Any remaining witness has `a≥A`. Since `d≤m`,

    p=(4m−1)a−4d ≥ (4m−1)A−4m,

so it necessarily has `m≤M`. Scan precisely these `m` by the one-residue test above. If both searches fail, `NO_B` is a *complete* integer-arithmetic certificate, whether or not `p` is prime. The code factors the **consecutive interval** `x₀,...,x₀+J−1` with an ordinary prime sieve to `⌊√(x₀+J−1)⌋`, then enumerates **all** divisors (including composite ones). Taking `J` of order `√p` makes both axes of the exhaustive search of order `√p` up to divisor-function factors. The inequality is a direct Nat-arithmetic lemma suitable for Lean; it provides a decision procedure, **not** an effective cutoff valid for all primes.

## Reciprocity: necessary signs, not sufficient residues

For `h=4m−1`, `gcd(h,m)=1`. If an odd prime `r|m`, quadratic reciprocity for the Jacobi symbol yields

    (r/h)=(-1/r)(h/r)=(-1/r)²=1,

because `h≡3 (mod 4)` and `h≡−1 (mod r)`. If `2|m`, then `h≡7 (mod 8)` and `(2/h)=1`. Hence `(d/h)=1` for every `d|m`. A B witness has `gcd(p,h)=1` and `p≡−4d (mod h)`, therefore

    (p/h)=(-4d/h)=−1.                                      (2)

For a **prime** `p≡1 (mod 4)`, reciprocity also makes `(h/p)=−1`. But (2) does not identify the required residue `−4d`: for example `p=193, m=3, h=11` has `(p/h)=(6/11)=−1`, whereas `d|3` only permits `p mod 11∈{7,10}`, not `6`.

This gives a rigorous infinite *composite*, **not prime**, B-free family: every odd square `p=q²≡1 (mod 24)` has no B witness at any `m`. Indeed a witness would imply `gcd(q,h)=1`, so `(p/h)=(q²/h)=+1`, contradicting (2). For instance `p=1000002000001=(1000001)²>10¹²` is B-free, and the independent finite certificate program reports `NO_B`. Primality really matters; this composite is **not** a counterexample to the question.

There is nevertheless an abundance of *locally eligible* moduli for each large prime: if `M≤⌊(p+7)/26⌋`, then `4m−1<p` for `m≤M`, and Pólya–Vinogradov gives

    #{m≤M:( (4m−1)/p )=−1}=M/2+O(√p log p),             (3)

uniformly in `p,M`, since `(4m−1/p)=(m−4⁻¹/p)` is an incomplete character sum over an interval. The prime `p=5179308386761` has exactly `497173` such eligible `m≤10⁶` (modular exponentiation), but **no B witness** there. Its *first* B witness is `(m,d)=(1586629,11)`: `h=6346515`, `p+44=816087·h`. An independent direct loop through all smaller `m` verified minimality. A recursive **Lucas primality certificate**, checked using only modular exponentiation and integer gcd, avoids reliance on an uncertified probable-prime label. In each row `(n;g;factorization of n−1)` below, the factors are earlier certified primes, the factorization multiplies to `n−1`, `g^(n−1)≡1 (mod n)`, and `gcd(g^((n−1)/q)−1,n)=1` for every distinct listed prime `q`:

    (2;1;1), (3;2;2), (5;2;2²), (13;2;2²·3),
    (17;3;2⁴), (53;2;2²·13), (107;2;2·53),
    (108499;14;2·3·13²·107),
    (42314611;3;2·3·5·13·108499),
    (14386967741;3;2²·5·17·42314611),
    (5179308386761;21;2³·3²·5·14386967741).

For `n=2` use the elementary base case; for `n>2`, these congruences force every prime divisor of `n` to be at least `n`, proving primality inductively. Thus this is a genuinely prime example of the gap between local signs and an actual divisor witness, not a pseudoprime artifact. Existence of roughly half the right Jacobi signs is therefore not the missing divisor correlation.

Three particularly cheap necessary conditions for B-freeness are: `x₀` has no prime factor `2 (mod 3)`; `p+4` has no prime factor `3 (mod 4)` (take `d=1`); and `(p+1)/2` has no prime factor `3 (mod 4)` (take `d=m`). In the second condition, a factor `q≡3 (mod 4)` has cofactor `(p+4)/q≡3 (mod 4)`, hence at least `3`, so `m=(q+1)/4≤(p−1)/6`; there is no hidden range assumption. In the third, `q|(p+1)/2` gives `m=(q+1)/4≤(p+3)/8≤(p−1)/6`. These are global factorization restrictions, not a proof that the residual primes vanish.

## Exact additive-divisor correlation and its obstruction

For any `M`, count modular pairs by

    N_B(p;M)=Σ_{m≤M} Σ_{d|m} 1_{4m−1 | p+4d}.

With `h=4m−1` and `e(u)=exp(2πiu)`, additive-character orthogonality gives the **identity**

    N_B(p;M)=D_B(M)+R_p(M),
    D_B(M)=Σ_{m≤M} τ(m)/(4m−1)
          =(log M)²/8+(γ/2)log M+O(1),
    R_p(M)=Σ_{m≤M} (1/h) Σ_{r=1}^{h−1} e(rp/h)
                                 Σ_{d|m} e(4rd/h).           (4)

The displayed diagonal follows by partial summation from `Σ_{m≤M}τ(m)=M log M+(2γ−1)M+O(√M)`; the difference between `1/(4m−1)` and `1/(4m)` is absolutely summable after weighting by `τ(m)`. It is **not a positive lower bound** on `N_B`.

For every square `p=q²≡1 (mod 24)`, `N_B(p;M)=0` for *every* `M`, hence `R_p(M)=−D_B(M)` exactly, even when `M` grows polynomially with `p`. This disproves any proposed pointwise diagonal domination that ignores primality. The certified prime `5179308386761` also has `R_p(10⁶)=−D_B(10⁶)`, a **finite** prime-scale illustration, not an asymptotic obstruction. Even among primes, for each fixed `B` let `Q_B=24·lcm(1,2,...,4B)`. Dirichlet supplies arbitrarily large primes `p≡1 (mod Q_B)`. For `m≤B`, `p≡1 (mod 4m−1)` and `4m−1∤1+4d` for every `d|m`: for `d<m` it lies strictly between `0` and `4m−1`, while for `d=m` it equals `(4m−1)+2`. Thus `N_B(p;B)=0`, `R_p(B)=−D_B(B)`. Moreover Chebyshev's `log Q_B=O(B)` and Linnik's theorem allow infinitely many such primes with `B≥c log p` for some absolute `c>0`. This obstructs a uniform off-diagonal `o(D_B)` assertion on logarithmic ranges. It does **not** exclude a witness with larger `m` or rule out a new pointwise estimate on polynomial ranges.

## A quantified B-specific sieve result, still not a cutoff

There is an alternate *sufficient* B test: if a prime `q | vp+1` satisfies `q≡−1 (mod 4v)`, set `d=(q+1)/(4v)` and `m=vd`; multiplication by `4d` modulo `q=4m−1` proves `q|p+4d`. No assumption that `q` is a prime factor of `p+4` is made.

Fix `K≥1` and set `κ_K=Σ_{1≤v≤K}1/φ(4v)`. **Unconditionally**, the number `E_B(X)` of B-free hard primes `p≤X` satisfies

    E_B(X) ≪_K X/(log X)^(1+κ_K).                           (5)

Consequently `E_B(X)≪_C X/(log X)^(1+C)` for *each fixed* `C>0`, because `κ_K≥(1/4)Σ_{v≤K}1/v` tends to infinity. Even `K=1` and partial summation show that the reciprocal sum `Σ_{p hard prime, B-free}1/p` converges; this **still** permits infinitely many exceptions. The count uses the prime number/Mertens theorem in each **fixed** arithmetic progression and elementary Selberg weights; it is not a statement that `E_B(X)=0`.

Here are the sieve details to keep (5) honest. For each sieving prime `q>4(K+1)`, forbid the residue `0` and each `−v⁻¹ (mod q)` for `v≤K` with `q≡−1 (mod 4v)`. These residues are distinct, because `q>K`, and any hard prime `p>z` lacking B avoids them. Set `ν(q)=#{v≤K:q≡−1 (mod 4v)}`, `ρ(q)=(1+ν(q))/q<1/4`, `g(q)=ρ(q)/(1−ρ(q))`, extended multiplicatively to squarefree products of sieving primes, and `G(z)=Σ_{d≤z}g(d)`. The CRT and the Selberg choice

    λ_d=μ(d)·[Σ_{e≤z/d,(e,d)=1} g(e)] /
                  [G(z) Π_{q|d}(1−ρ(q))]

have `λ₁=1`, main quadratic form `1/G(z)`, and `|λ_d|≤2^{Ω(d)}`. Since each squarefree CRT system contributes at most `Π_{q|d}(1+ν(q))` boundary errors, the number of sifted integers `n≤X` is at most

    X/G(z)+O_K(z^[2+2 log₂(2(K+1))]).                       (6)

For a lower bound on `G`, put `Z=z^[1/(8(K+1))]`. In the Euler product `P(Z)=Π_{4(K+1)<q≤Z}(1+g(q))`, the weighted mean of `log d` is `Σ_{q≤Z}ρ(q)log q≤2(K+1)log Z=(log z)/4`. Markov leaves at least `3/4` of its mass on `d≤z`, so `G(z)≥3P(Z)/4`. Fixed-progression prime Mertens estimates give

    log P(Z)≥Σ_{q≤Z}ρ(q)=(1+κ_K)log log Z+O_K(1).

Thus `G(z)≫_K(log z)^(1+κ_K)`. Choose `z=X^η` for fixed, sufficiently small `η(K)>0` to make the error in (6) a power-saving; add at most `z` small primes. This proves (5). Notice that `g(q)<1/3`, so `G(z)≤z`; the *upper bound's* main term `X/G(z)≥X/z` cannot itself be less than `1` for `z<X`. Neither (5) nor any density-one assertion yields an effective finite-exception cutoff. Varying `K` with `X` without uniform constants and an appropriate sieving range is invalid.

### A controlled growing-parameter bound, still with infinitely possible exceptions

The same **B-specific** sieve permits a stronger unconditional (but non-pointwise) statement if the growth of `K` and all uniform constants are specified. For each fixed `0<α<1` there is an `X_α` such that, for `X≥X_α`,

    # {prime p≤X: p≡1 mod 24, no B witness with m≤(X^(1/8)+1)/4}
        ≪_α X exp(−c_α (log log X)²),
    c_α=α(1−α)/16.                                      (7)

In particular the number of *completely* B-free hard primes satisfies the same estimate. The threshold and implied constant obtained from Siegel–Walfisz need not be numerically effective; (7) is emphatically **not** a bound on a largest counterexample.

Here is a derivation with `X`-uniform sieve truncation. Let `K=⌊(log X)^α⌋`, `z=X^(1/8)`, and keep precisely the residue classes and Selberg weights above. Since the primes in a squarefree `d` are all greater than `4(K+1)`, putting `σ_K=log(2(K+1))/log(4(K+1))<1` gives

    2^Ω(d)·Π_{q|d}(1+ν(q)) ≤ [2(K+1)]^Ω(d) ≤ d^σ_K.

The CRT error in (6) is therefore bounded by `z^(2+2σ_K)≤z⁴=X^(1/2)` **with an absolute constant**, despite varying `K`. Set `Z=z^[1/(8(K+1))]`, `T=exp(√(log Z))`. We have `log Z ≍_α (log X)^(1−α)` and `T>4(K+1)` for large `X`. The same Euler-product/Markov argument as above yields `G(z)≥(3/4)P(Z)`: indeed its mean `log d` is at most `2(K+1)log Z=(log z)/4`.

For fixed exponents `A>2α/(1−α)` and `D>1+2α/(1−α)`, every `4v`, `v≤K`, is at most `(log t)^A` throughout `t≥T`. Uniform Siegel–Walfisz followed by partial summation thus gives, uniformly in `v≤K`,

    Σ_{T<q≤Z, q≡−1 (mod 4v)} 1/q
      = [log(log Z/log T)]/φ(4v) + O_{α,A,D}((log T)^(1−D)).

The sum of these errors over `v≤K` is `o(1)`. Since `log T=√(log Z)`, summing the main terms and using `κ_K≥(1/4)Σ_{v≤K}1/v` gives

    log G(z) ≥ log(3/4)+log P(Z)
      ≥ log(3/4)+Σ_{T<q≤Z} ν(q)/q
      = (κ_K/2) log log Z+O(1)
      ≥ [α(1−α)/8+o(1)](log log X)².

Decrease the coefficient to `c_α=α(1−α)/16` for large `X`. The sieve estimate `S(X,z)≤X/G(z)+O(X^(1/2))`, plus at most `z` primes `p≤z`, proves (7): when `p>z`, a sieving prime `q≤z` dividing `vp+1` gives `m=(q+1)/4≤(z+1)/4`. In particular `E_B(X)` has this bound, because every B-free prime lacks such a *short* witness. Although (7) beats each fixed power of `log X`, its right side still grows without bound. The main term itself satisfies `X/G(z)≥X/z=X^(7/8)`; no cutoff follows even if one could explicitly compute every Siegel–Walfisz constant.

### A stronger unconditional bound using averaged prime progressions

Bombieri–Vinogradov and the upper-bound Brun–Titchmarsh theorem permit an even more aggressive, but **still non-pointwise**, conclusion: there exists an absolute `c>0` such that

    # {prime p≤X: p≡1 mod 24, no B witness with
                        m≤(exp(√(log X)/(16√2))+1)/4}
        ≪ X exp(−c√(log X)).                               (8)

Hence `E_B(X)≪X exp(−c√(log X))`. Here is a complete choice of the sieve ranges and a check that neither the distribution nor the CRT error is extrapolated past its valid range. Take `z=X^(1/8)`, `H=√(log z)`, `Z=exp(H/8)`, `T=exp(H/16)=√Z`, and `K=⌊T^(1/4)⌋`. Use only sieving primes `T<q≤Z`; for each, forbid `0` and `−v⁻¹ (mod q)` for every `v≤K` satisfying `q≡−1 (mod 4v)`. Recompute the Selberg normalizer `G(z)` and the sifted count `S(X,z)` using this restricted prime set. These classes are distinct, `q>T≫K`, and `ρ(q)=(1+ν(q))/q<1/4` for large `X`. A hard prime `p>z` avoiding a B witness must avoid them all. The Selberg identity from (6) gives `S(X,z)≤X/G(z)+O(z⁴)` **uniformly for this varying `K`**: since each prime factor of a squarefree `d` is greater than `T>2(K+1)`,

    |λ_d|·Π_{q|d}(1+ν(q)) ≤[2(K+1)]^Ω(d)≤d,

so the sum of boundary weights for `d≤z` is at most `z²`.

For clarity, both sides of the Euler-product truncation can be controlled without assuming independent divisor conditions. Let `P=Π_{T<q≤Z}(1+g(q))`, with `g(q)=ρ(q)/(1−ρ(q))`. The weighted mean of `log d` in this *finite product* is `Σ_{T<q≤Z}ρ(q)log q`. The elementary prime estimate `Σ_{q≤Z}(log q)/q≤2log Z` and Brun–Titchmarsh give a usable upper bound. Indeed `4v≤4K≤T^(1/3)` for large `X`, so for `t≥T`,

    π(t;4v,−1)≤2t/[φ(4v)log(t/(4v))]
               ≤4t/[φ(4v)log t].

Partial summation therefore gives

    Σ_{T<q≤Z, q≡−1 (mod 4v)} (log q)/q
        ≤4[1+log(Z/T)]/φ(4v).

Also `κ_K≤3(1+log K)`: expand `v/φ(v)=Σ_{d|v}μ²(d)/φ(d)`, use `φ(4v)≥φ(v)`, and bound the convergent Euler product `Σ_{d≥1}μ²(d)/(dφ(d))=Π_r(1+1/[r(r−1)])≤e<3`. Thus the mean is at most

    2log Z+4κ_K[1+log(Z/T)]
      ≤ H/4+12(1+H/64)(1+H/16) ≤ H²/4= (log z)/4

for sufficiently large `X`. Markov's inequality, applied to the product weights, then yields `G(z)≥(3/4)P` exactly as in the fixed-`K` proof.

For the **lower** bound on `P`, apply Bombieri–Vinogradov to the prime variable `q` and moduli `4v≤4K`, with residue `−1`. For every `t≥T`, the modulus range satisfies `4K≤t^(1/2)/(log t)^B` for any fixed `B` once `X` is large. The averaged theorem in the `π` formulation (take, say, logarithmic error exponent `A=5`) says

    Σ_{v≤K}|π(t;4v,−1)−Li(t)/φ(4v)|≪t/(log t)^5.

Partial summation over `T<q≤Z`, integrating this **sum** of errors (not asserting an error this small for each individual `v`), gives

    Σ_{T<q≤Z}ν(q)/q
      = Σ_{v≤K} Σ_{T<q≤Z, q≡−1 (mod 4v)}1/q
      = κ_K log(log Z/log T)+O((log T)^(−4))
      = κ_K log 2+o(1).

Here `κ_K≥(1/4)Σ_{v≤K}1/v≥H/256+O(1)`. Consequently `log G(z)≥log(3/4)+log P≥(log 2)H/256+O(1)`, and, for large `X`, one may take `c=(log 2)/(512√8)>0` in (8). The sieve error `z⁴=X^(1/2)` and the at most `z` primes below `z` are absorbed in (8). Any sieving prime supplies `m=(q+1)/4≤(Z+1)/4`, which is precisely the short-witness bound displayed there. The constants in the quoted averaged prime theorem need not be numerically effective; more decisively, `X exp(−c√log X)→∞` and `G(z)≤z`, so **even this stronger theorem proves no effective cutoff or finite-exception assertion**.

## Deterministic finite exploration, **not** a universal conclusion

`BAxisDirectSearch.cpp` independently checks each `p=24j+1` by the one-residue test to `m=1000`; for survivors it runs a *primality rejection* test, then tests to the specified larger `m`. `BAxisSegmentedSearch.cpp` instead premarks progressions: writing `g=gcd(24,4m−1)`, the congruence for `p=24j+1` has no solution unless `g|1+4d`; otherwise it defines exactly one residue of `j` modulo `(4m−1)/g`, found by a modular inverse. Both programs reject composites by a strong probable-prime test; **every actual prime passes that test**, regardless of whether one invokes the known 64-bit deterministic base theorem. Thus if every unmarked test survivor has an actual B witness, no prime in the enumerated interval was omitted. `UNRESOLVED` means only "no witness through the chosen search limit" and needs the separate complete certificate.

The direct program completed the entire interval `[1000000000001,10000000000000]`:

    examined=375000000000; prefix_survivors=731704273;
    probable_prime_survivors=37954341; unresolved=0;
    largest first m=1586629, at p=5179308386761, d=11.

These are counts of tested progression integers and filter survivors, **not** a claimed count of all primes in the interval. The *independently implemented segmented* program also completed the entire interval `[10000000000001,100000000000000]`:

    classes=5956; examined=3750000000000; unmarked=7304215007;
    probable_prime_survivors=351402932; unresolved=0;
    largest first m=4086040, at p=41715309381793, d=510755.

Here `p` is prime (PARI/GP `isprime(p)=1`), and an independent Python loop checked that `(4086040,510755)` is its **first** B pair: `4m−1=16344159` and `p+4d=2552307·16344159`. The other interval's largest first `m` was `1586629`, as above. Thus the two **finite intervals** `(10¹²,10¹³]` and `(10¹³,10¹⁴]` contain no B-free prime; they cannot establish a cutoff for all larger primes. The `unmarked` and primality-filter survivor totals are **not** counts of B-free primes or an inference about any untested range.

For independent audits, on `[73,10⁶]` both implementations with prefix `m=5` and remaining search `m≤10⁶` report exactly the unresolved `193,2521,66529`; `BAxisCertificate.cpp` gives complete `NO_B` certificates for those three. On each of two `10⁹`-wide intervals near `10¹²` and `10¹⁴`, the direct and segmented methods returned identical prefix-survivor counts, primality-filter survivors, and largest minimum `m`. The certificate program gives `NO_B` for the known composite square `1000002000001` without assuming primality, a useful negative-control test. All modular tests use integer arithmetic; the certificate program corrects its initial square-root estimate by integer division, so no floating-point approximation decides a search endpoint or divisor match.

Reproduce the searches with, for example:

```sh
g++ -O3 -std=c++17 -pthread Submission/BAxisDirectSearch.cpp -o /tmp/Bdirect
/tmp/Bdirect 1000000000001 10000000000000 48 1000 5000000 4194304
g++ -O3 -std=c++17 -pthread Submission/BAxisSegmentedSearch.cpp -o /tmp/Bseg
/tmp/Bseg 10000000000001 100000000000000 32 1000 10000000 4194304
g++ -O3 -std=c++17 Submission/BAxisCertificate.cpp -o /tmp/Bcert
/tmp/Bcert 193 200
/tmp/Bcert 2521 200
/tmp/Bcert 66529 200
/tmp/Bcert 1000002000001 50000  # composite square, not a prime
```

**Unresolved:** None of the reciprocity counts, additive-character diagonals, CRT bounds, sieve estimates, or finite computations proves that all sufficiently large hard primes have B. No prime `p>10¹²` lacking B was identified here. The missing input is *pointwise* control of the exact divisor congruence for each prime at growing parameters, not an average, local Jacobi sign, or finite-exception heuristic.
