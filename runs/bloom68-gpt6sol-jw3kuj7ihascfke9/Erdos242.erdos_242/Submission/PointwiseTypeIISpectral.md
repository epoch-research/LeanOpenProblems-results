# Prime-specific Type-II character main, and the missing pointwise divisor correlation

**Status:** This is a partial analytic result, **not** a proof that every hard
prime has a square-divisor witness or an Erdős–Straus decomposition. Nothing in
`Spec.lean` is changed. The exact modular-witness construction and the full
Type-I-or-II alternative are in `FullSquareAxis.lean` and `CoveringGap.lean`.

Throughout let `p ≡ 1 (mod 24)` be **prime**, `L=log p`, `1≤m≤(p−1)/6`,
`h=4m−1`, and

    D_m(p) = {d>0 : d|m² and 4d<p},       t_m(p)=|D_m(p)|.

The full square-divisor-axis pair count is

    N₂(p) = Σ_m Σ_{d∈D_m(p)} [h | p+4d].                    (1)

A positive count gives an ordered solution, but the full Type-I-or-II
criterion is weaker. In particular, a local failure at one `m` says nothing
about the prime at other `m`.

## Exact correction of the additive zero mode

For every prime factor `r|m`, `(r/h)=1` (Jacobi notation). For odd `r`,
quadratic reciprocity and `h≡−1 (mod r)`, `h≡3 (mod 4)` give
`(r/h)=(-1/r)(h/r)=(-1/r)²=1`; if `r=2`, then `h≡7 (mod 8)` and
`(2/h)=1`. Hence `(d/h)=1` for every `d|m²`. Also `h<p`,
`gcd(h,p)=gcd(h,m)=1`, and the Jacobi character `χ_h=(·/h)` is
nonprincipal because `χ_h(−1)=−1`. Reciprocity gives

    χ_h(p) = (h/p) =: χ_p(h) ∈ {−1,+1}.

Orthogonality of **all** characters of `(ℤ/hℤ)×` gives the exact identity

    N₂(p) = M₂(p)+E₂(p),
    M₂(p) = Σ_m [(1−χ_p(h)) t_m(p)]/φ(h),                 (2)
    E₂(p) = Σ_m (1/φ(h)) Σ_{ψ mod h; ψ≠1,χ_h}
                ψ(p) conjugate(ψ(−4))
                  Σ_{d∈D_m(p)} conjugate(ψ(d)).            (3)

In particular, `E₂(p)` is real. The additive zero frequency alone is
`Σ_m t_m(p)/h`; it is **not** the corrected main (2). If
`χ_p(h)=+1`, the principal and Jacobi contributions cancel exactly.
For an odd-square **composite** numerator coprime to `h`, its Jacobi
symbol modulo `h` is also `+1`; the prime-specific notation `χ_p` and
lower bound below do not apply to such squares. Neither main term is a
lower bound on `N₂(p)` without an estimate for the remaining characters.

**Pointwise proposition, with an explicit cutoff.** For every hard prime
with `L≥28`,

    M₂(p) ≥ L³ / (2²² log 2).                              (4)

This uses primality, rather than an average over primes. The bound also holds
for the main term of the *smaller* count restricted to the dyadic `m` below
and to `d≤m`.

**Proof.** For an interval of at most `p` consecutive integers and the
Legendre character modulo `p`, Fourier inversion and the elementary
geometric-sum bound give

    |Σ_{v∈J} χ_p(v)| ≤ B := √p(1+L).                       (5)

Indeed the nonzero Fourier coefficients have modulus `√p`, the zero
coefficient vanishes, and
`|Σ_{v∈J} exp(2πirv/p)|≤p/[2 min(r,p−r)]`; summing over
`1≤r<p` gives `√p H_{(p−1)/2}≤B`. The same bound holds for
`χ_p(4ℓv−1)` when `p∤ℓ`, since it is a shifted interval character
multiplied by `χ_p(4ℓ)`.

Take a dyadic `A=2^j` with `p^(3/4)≤A≤p/16`, and all `A≤m<2A`.
Put `U=⌊A^(1/16)⌋`. For coprime `u,v≤U`, set `ℓ=uv≤A^(1/8)`.
There are at least `A/ℓ−1` multiples of `ℓ` in this block. Applying
(5) to their `χ_p(4m−1)` signs shows that at least

    (A/ℓ−1−B)/2 ≥ A/(4ℓ)                              (6)

have sign `−1`. To justify the last inequality, `A/ℓ≥A^(7/8)≥
p^(21/32)≥2(1+B)` for `L≥28`; the last step follows from
`exp(5L/32)≥2(L+2)` (at `L=28`,
`exp(35/8)>54·(1+3/8)>60`, and the ratio to `L+2` increases
thereafter). All these `m` satisfy `0<4m−1<p`, so the character
never vanishes.

The prime-power identity

    τ(m²) = #{(u,v): u|m, v|m, gcd(u,v)=1}

and a union bound for pairs sharing a prime imply

    Σ_{u,v≤U, (u,v)=1} 1/(uv)
      ≥ (1−Σ_{q prime}1/q²) (Σ_{u≤U}1/u)²
      ≥ (log U)²/4 ≥ L²/2¹⁴.                              (7)

Here `Σ_{q prime}q^(−2)<3/4`, using
`1/4+Σ_{n≥3}1/[n(n−1)]=3/4`. Also `U≥A^(1/16)/2`, whence
`log U≥3L/64−log 2≥L/48` for `L≥28` (use
`log 2<7/10<35/48=5·28/192`), and `4·48²<2¹⁴`.
Equations (6)–(7) yield

    Σ_{A≤m<2A, χ_p(h)=−1} τ(m²) ≥ A L²/2¹⁶.          (8)

Every divisor `d|m²` with `d≤m` satisfies `4d<p`, because
`m<2A≤p/8`, and their number is `(τ(m²)+1)/2`. For each of these
negative-sign `m`, its contribution to (2), even retaining only
`d≤m`, is at least `τ(m²)/φ(h)≥τ(m²)/(8A)`.
Thus **each** chosen dyadic block supplies at least `L²/2¹⁹`
to the corrected main. The number of such blocks is at least
`L/(4 log 2)−5≥L/(8 log 2)` for `L≥28`. Summing proves (4).
`□`

The explicit threshold `p≥e²⁸≈1.446·10¹²` concerns **only** (4). It is
not a verified cutoff for existence: no sufficient estimate on (3) has
been proved, and a separate complete check below that threshold has
not been performed here.

## What a spectral/additive proof would still have to establish

Let `K_A(p)` restrict (1) to a dyadic block above and `d≤m`. Define its
`M_A` and `E_A` by (2)–(3) with the same restriction. We have proved
`M_A≥L²/2¹⁹`; the missing **pointwise** conclusion would be, for
example,

    E_A(p)>−L²/2¹⁹  for at least one such A.               (9)

It would imply `K_A(p)>0`. More generally, **exactly**

    E₂(p)>−M₂(p)                                          (10)

is necessary and sufficient for a full square-divisor-axis witness.
A much stronger sufficient theorem would be
`|E₂(p)| < L³/(2²² log 2)` for every hard prime `p≥e²⁸`,
**plus separate verification of all smaller hard primes**. No such theorem,
verification, or universal witness is claimed. The full Type-I-or-II
fallback has the analogous missing joint inequality
`T(p)>−M(p)` in `JacobiCorrectedJointCount.md`.

There is a precise obstacle to replacing (9) by a per-modulus spectral
norm. Fix `m`, let `G=(ℤ/hℤ)×`, restrict to `d|m², d≤m`, and set

    t=(τ(m²)+1)/2,
    ν_m(r)=#{d|m², d≤m : −4d≡r (mod h)},
    μ_m(r)=t(1−χ_h(r))/φ(h)       (r∈G).

All of `ν_m` lies in the `χ_h(r)=−1` half of `G`. Parseval gives the
**exact nonquadratic spectral energy**

    Σ_{r∈G}|ν_m(r)−μ_m(r)|²
      = (1/φ(h)) Σ_{ψ≠1,χ_h}|Σ_{d|m², d≤m} ψ(−4d)|²
      = Σ_{r∈G}ν_m(r)²−2t²/φ(h) ≥ t−2t²/φ(h).        (11)

In particular the other modes do not disappear just by removing the
quadratic character or applying Cauchy–Schwarz per modulus. Even if
`χ_h(p)=−1`, a missing target has local remainder `−2t/φ(h)`.
A sum over the **different, m-dependent moduli** must exhibit genuine
pointwise cancellation, not just small individual Legendre sums.
Generic errors of size `A^(1/2+ε)` for the block count cannot meet
the sufficient logarithmic-scale threshold (9) in `A≥p^(3/4)`;
any fixed positive power of `p` eventually dominates every fixed
power of `log p`.
A bound on an average over `p` (even exceptional density tending rapidly
to zero) likewise allows an isolated missed prime.
Quantitatively, a hypothetical bad prime `p∈[X,2X]`, `log X≥28`,
would have `E₂(p)=−M₂(p)` and
`|E₂(p)|²≥(log X)^6/(2⁴⁴(log 2)²)` by (4). To exclude even
one such prime using a second moment over that dyadic range, the
**whole** nonnegative moment would have to be smaller than this
polylogarithmic threshold. An estimate of size `X/(log X)^C` for any
fixed `C` does not do so.


There are arbitrarily large **prime** local examples with the correct
quadratic sign and complete higher-character cancellation. For any `s≥0`,
choose `s` distinct primes `r_i≡1 (mod 121)` and set
`Q=∏r_i`, `m=3Q`, `h=12Q−1=11h'`. Then `h≡11 (mod 121)`,
so `gcd(11,h')=1`; also `gcd(24,h)=1`. CRT and Dirichlet give
arbitrarily large primes `p>4m²` with

    p≡1 (mod 24),     p≡2 (mod 11),     p≡1 (mod h').

They satisfy `χ_h(p)=(2/11)(1/h')=−1`. Yet all the
`3^(s+1)` divisors of `m²` lie in `{1,3,9} (mod 11)`, and
`p+4d` then has residue in `{6,3,5} (mod 11)`. Thus **none**
is a witness at this `m`, even with no truncation, and its entire local
remainder in (3) is

    E_{2,m}(p) = −M_{2,m}(p) = −2·3^(s+1)/φ(h).        (12)

For the small fully checkable case `s=0`, take `p=409`, `m=3`, `h=11`;
trial division by primes at most `√409<21` verifies primality.
Here `p≡2 (mod 11)`, its three eligible divisors are `1,3,9`,
`χ_h(p)=−1`, `M_{2,m}=3/5`, and its actual count is zero.
**This is not a bad prime:** `(m,d)=(2,1)` works at `409`, since
`7 | 409+4=413`. Likewise (12) concerns only the displayed `m`, not
all moduli of the constructed primes.

The fixed-parameter CRT obstruction remains relevant: for any prescribed
`B`, primes `p≡1` modulo `24·lcm_{m≤B}(4m−1)` have no witness with
`m≤B` (`not_one_modular_divisor` in `Partial.lean`). Their corrected
quadratic main also vanishes there. The blocks used for (4), by
contrast, have `m≥p^(3/4)`; fixed cutoffs and CRT do not prove or
disprove the required global correlation (9)–(10).
