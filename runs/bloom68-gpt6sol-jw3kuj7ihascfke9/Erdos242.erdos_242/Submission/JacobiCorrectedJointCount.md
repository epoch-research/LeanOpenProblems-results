# A pointwise Jacobi-corrected joint count, and its missing error bound

**Status.** This is an ordinary mathematical argument, not a Lean proof of the
new analytic estimate, not a proof of Erdős–Straus, and not a prime
counterexample. `Spec.lean` is neither imported nor modified. The ordered
Type-I/Type-II equivalence is Lean-proved in `CoveringGap.lean`; the character
transfer used below is also proved in `PointwiseJacobi.lean`. The point here is
to count **both** types, remove the exact principal/Jacobi cancellation, and
still keep the unproved pointwise step explicit.

Let `p=24k+1` be prime. The candidate first denominators are
`x=6k+1+j`, `0≤j<6k`; put `a=4x−p=4j+3` and write `χ(v)=(v/p)`.
Then `a` is odd, `a≡3 (mod 4)`, `p/4<x<p/2`, and `gcd(a,x)=1` (a common
factor of `a,x` would divide `p`, whereas `x<p`). In particular **every**
divisor of `x²` is a unit modulo both `a` and `p`. Set

    D_x = τ(x²),    S_x = Σ_{c|x²} χ(c),    s_x = χ(x) ∈ {−1,+1}.

## An exact principal-plus-Jacobi decomposition for *both* types

For all `c|x²`, Jacobi reciprocity gives

    (c/a) = (c/p) = χ(c).                                    (1)

Indeed, for an odd prime `r|x`, we have `a≡−p (mod r)`,
`a≡3 (mod 4)` and `p≡1 (mod 4)`, so
`(r/a)=(a/r)(−1/r)=(−p/r)(−1/r)=(p/r)=(r/p)`.
If `2|x`, then `a≡7 (mod 8)` and `p≡1 (mod 8)`, so the equality
also holds for `r=2`. Multiplicativity proves (1), including for
`c>x`.

Let `t_I≡−4⁻¹ (mod a)` and `t_II≡−x (mod a)`. The two exact
ordered-witness pair counts at this `x` are

    I_x  = #{c|x² : c≡t_I (mod a)},
    II_x = #{d|x² : 0<d<x, d≡t_II (mod a)}.

Both target residues are units, and (1) gives
`(t_I/a)=−1`, `(t_II/a)=−s_x`. The sets of divisors with
the **necessary** character signs have cardinalities

    E_I(x)  = #{c|x² : χ(c)=−1}             = (D_x−S_x)/2,
    E_II(x) = #{d|x² : d<x, χ(d)=−s_x}      = (D_x−s_x S_x)/4.  (2)

For the second formula, pair `d|x²` with `x²/d`. The two have the
same `χ`-value; the sole fixed point is `x`, with sign `s_x`, so no
correct-sign Type-II divisor is fixed. Thus the correct-sign count
below `x` is exactly half the count among all divisors. In particular,
(2) is an *integer*, even though its last expression has denominator 4.

Write `φ=φ(a)` and let `ψ` range over all characters of the unit group
modulo `a`, extended by zero outside the units. The Jacobi character
`χ_a=(·/a)` is nonprincipal because `χ_a(−1)=−1`. Orthogonality gives
an **exact** identity, with no heuristic use of equidistribution:

    I_x+II_x = M_x+T_x,
    M_x = 2(E_I(x)+E_II(x))/φ(a)
        = [3D_x−(2+s_x)S_x]/[2φ(a)],                         (3)
    T_x = (1/φ(a)) Σ_{ψ ≠ 1,χ_a} [ conj(ψ(t_I)) Σ_{c|x²} ψ(c)
                     + conj(ψ(t_II)) Σ_{d|x², d<x} ψ(d) ].

Here `M_x` is the sum of **two** character contributions: the
principal and the Jacobi character. Their contributions cancel on
wrong-sign divisors; `T_x` is the sum of *all the other* characters.
Although displayed using complex characters, `T_x` is real. Define
`C(p)=Σ_x(I_x+II_x)`, `M(p)=Σ_x M_x`, and `T(p)=Σ_x T_x` over the
complete eligible list. Then

    C(p)=M(p)+T(p),   and   Good(p) ⇔ C(p)>0.                (4)

The second equivalence is the **full two-type** criterion, rather than
the stronger (and unproved) assertion that Type I alone always works.
For a factorization `x=∏r^{v_r}`, the divisor sum in (3) is explicitly

    S_x = ∏_{r|x, χ(r)=+1} (2v_r+1),
    D_x = ∏_{r|x} (2v_r+1).                                (5)

A factor with `χ(r)=−1` contributes `1` to `S_x`, because
`1−1+1−⋯+1=1` has `2v_r+1` terms. Thus `0<S_x≤D_x`.
If `s_x=−1`, some prime factor of `x` has sign `−1`, and (5) gives
`S_x≤D_x/3`. The *joint* corrected main term therefore satisfies

    s_x=−1  ==>  M_x=(3D_x−S_x)/(2φ(a)) ≥ 4D_x/(3φ(a)).  (6)

Notice that (6) is a lower bound on **`M_x`, not `I_x+II_x`**.

## A fully pointwise, explicit cubic-log lower bound on the corrected main

**Proposition.** For every prime `p≡1 (mod 24)` with `L=log p≥64`
(natural logarithm),

    M(p) ≥ L³ / (3·2¹⁸ log 2).                              (7)

In fact the same lower bound holds for the sub-sum with `a<p/8`.
Here `x<(p+p/8)/4=9p/32`, so `7x<63p/32<2p+4`: these indices
are not ruled out by the existing sharp *necessary size* bound for
Type II. Neither (7) nor this observation bounds `T(p)`.

**Proof.** We use the standard incomplete quadratic-character estimate
for any interval `J` of at most `p` consecutive integers:

    |Σ_{v∈J} χ(v)| ≤ √p (1+log p).                           (8)

For completeness, the nonzero Fourier coefficients of the Legendre
character modulo `p` have magnitude `√p`, and its zero coefficient is
zero. Fourier inversion bounds the interval sum by
`(√p/p) Σ_{r=1}^{p−1}|Σ_{v=0}^{|J|−1}e^{2πirv/p}|`.
The geometric sum has absolute value at most
`1/|sin(πr/p)| ≤ p/[2 min(r,p−r)]`, so the Fourier bound is
`√p·H_{(p−1)/2} ≤ √p(1+log p)`. This proves (8) with the displayed
constant, rather than invoking an averaged estimate.

Choose dyadic integers `A=2^h` with `p^{3/4}≤A≤p/16`. The set
`J_A={x : A≤4x−p<2A}` consists of exactly `H=A/4` consecutive
eligible `x`: the relevant `a` are precisely the `A/4` numbers
`3 (mod 4)` in `[A,2A)`. Moreover `a<2A≤p/8`. Put
`U=⌊A^{1/16}⌋`. For coprime `d,e≤U`, let `l=de≤A^{1/8}<p`.
Of the `H` consecutive `x` in `J_A`, at least `H/l−1` are divisible
by `l`. Since `x<p`, their Legendre signs are all `±1`; after
writing `x=lv`, (8) bounds the sum of these signs by
`B=√p(1+L)` in absolute value. For `L≥64`,

    H/l ≥ A^{7/8}/4 ≥ p^{21/32}/4 ≥ 2(1+B).

The last inequality follows from `p^{5/32}≥8(L+2)`:
`e^{10}>8·66` at `L=64`, and `e^{5L/32}/(L+2)` increases
for `L≥64`. Hence

    #{x∈J_A : l|x, χ(x)=−1} ≥ (H/l−1−B)/2 ≥ H/(4l).    (9)

The elementary identity
`τ(x²)=#{(d,e): d|x, e|x, gcd(d,e)=1}` follows prime
power by prime power. The coprime harmonic sum obeys

    Σ_{d,e≤U, (d,e)=1} 1/(de)
       ≥ (1−Σ_{q prime} 1/q²)(Σ_{d≤U} 1/d)²
       ≥ (log U)²/4 ≥ L²/2¹².                              (10)

For the first inequality discard pairs sharing a prime; the weighted
multiples of a prime `q` among `d≤U` sum to at most
`(1/q)Σ_{d≤U}1/d`. The prime reciprocal-square sum is `<3/4`:

    Σ_{q prime}q⁻² ≤ 1/4+Σ_{m≥3}m⁻²
                   < 1/4+Σ_{m≥3}1/[m(m−1)]=3/4.

For the last inequality, `U≥A^{1/16}/2` and
`log U≥3L/64−log 2≥L/32` when `L≥64`. Equations (9)–(10) yield

    Σ_{x∈J_A, χ(x)=−1} D_x ≥ H L²/2¹⁴.

By (6), `φ(a)≤a<2A`, and `H=A/4`, the block contributes at least

    Σ_{x∈J_A} M_x ≥ (4/(3·2A))·(H L²/2¹⁴)
                      = L²/(3·2¹⁵).                        (11)

The allowed dyadic exponents lie in
`[(3/4)L/log 2, L/log 2−4]`. Their number is at least
`L/(4 log 2)−5 ≥ L/(8 log 2)` for `L≥64`.
These `J_A` are disjoint. Summing (11) proves (7), **only for the
character main term**. `□`

## Correct-sign fake mass still cancels: one full fiber and an infinite subcollection

An exact *prime* example defeats a local inference even after both the
Jacobi correction and the Type-II alternative are included:

    p=13873,   x=3471=3·13·89,   a=11,   χ(x)=−1.

The prime has `p−1=2⁴·3·17²`; base `5` has power `1 (mod p)`
for exponent `p−1`, and its powers for exponents `(p−1)/2`,
`(p−1)/3`, `(p−1)/17` are respectively `13872,6834,4565`.
Thus its multiplicative order is `p−1`, certifying primality.
Here `D_x=27`, `S_x=9`, `E_I(x)=E_II(x)=9`, and

    M_x=2(9+9)/φ(11)=18/5 > 3.

Nevertheless the **entire** set of residues of divisors of `x²`
modulo 11 is `{3^i 2^j : 0≤i,j≤2}={1,2,3,4,6,7,9}`:
`89≡1 (mod 11)`. The Type-I target is `8`, and the Type-II
target is `−x≡5`; neither is present. So `I_x=II_x=0` and
`T_x=−18/5` exactly. The **prime is soluble at another x**:
`x=3470`, `a=7`, `c=5|x²`, `7|4c+1` is a Type-I witness.
The example refutes local positivity, *not* a hypothetical global
estimate involving all eligible `x`. Even a full-fiber corrected main
larger than the number of unit classes can miss: at the prime
`p=5511937`, `x=1377987=3·13·89·397`, `a=11`, the same divisor
residues and targets `8,5` occur, so both counts are zero, while
`D_x=81`, `S_x=27`, and `M_x=54/5>φ(11)=10`. A short primality
certificate is `p−1=2⁸·3·7177` (7177 is prime by trial division to
84); base 5 has `(p−1)`st power 1, and powers with exponents
`(p−1)/q` for `q=2,3,7177` yield `5511936,476674,1704966`,
none 1. This is still only **one** candidate denominator.

The obstruction is not bounded to a single chosen divisor pair.
Fix `t≥1`, choose `t` distinct primes `r_i≡1 (mod 264)`, and put
`Q=13∏_i r_i`. CRT and Dirichlet provide arbitrarily large primes
satisfying

    p≡1 (mod 24),   p≡8 (mod 11),   p≡−11 (mod Q).

The CRT class is reduced (`Q` is coprime to `264` and `11`).
Take `p>4Q²` and set `x=(p+11)/4`; then `p/4<x<p/2`,
`Q|x`, `x>Q²`, and `x≡2 (mod 11)`. Among the **selected** divisors
`v|Q²`, the only residues modulo 11 are `1,2,4`, since
`13≡2` and all `r_i≡1`. They all miss Type-I target `8` and
Type-II target `−x≡9`. Yet `χ(13)=−1` by (1), and exactly `3^t`
of these selected divisors have the *correct Type-I sign* (exponent
of 13 equal to 1). Exactly `2·3^t` have the *correct Type-II sign*
(exponent of 13 equal to 0 or 2); **all** the latter are `<x`.
The selected pairs' principal-plus-Jacobi contribution is

    2(3^t+2·3^t)/φ(11) = 3^{t+1}/5,

and their contribution from other characters is its exact negative.
**This is only a selected subcollection:** other divisors of `x²`
or other denominators may hit a target. No bad prime or failure of the
*full* global main-term estimate is asserted.

For scale, one can make this selected corrected mass exceed
`(log p)^K` for each fixed `K` along a sequence of primes, still
without a statement about the full count. Choose the first `t`
primes `r_i≡1 (mod 264)`, so fixed-progression PNT gives
`log Q=O(t log t)`. Bertrand supplies a prime
`4Q²<ℓ<8Q²`; add the reduced CRT condition `p≡1 (mod ℓ)`.
The least prime in this class satisfies `p>4Q²` and, by Linnik,
`log p=O(log(264Qℓ))=O(t log t)`. Since `3^t` exceeds every
fixed power of `t log t`, the assertion follows. PNT in a fixed
progression and Linnik are used **only** for this optional scaling;
the infinite selected-pair construction itself needs just Dirichlet.

## The exact missing pointwise estimate

Equation (4), for the *joint full count*, makes the necessary-and-
sufficient missing bound completely explicit:

    T(p) > −M(p)       for every hard prime p.              (12)

By `CoveringGap.all_good_iff_explicit_hard_cover`, (12) for all hard
primes is equivalent to the original statement for **all `n>2`**.
It is not an estimate inferred from the positivity of `M(p)`.
A sufficiently strong *uniform* bound `|T(p)|<(1−δ)M(p)` for all
large hard primes (with separate checks below a cutoff) would imply
(12). Neither bound is established. The elementary Legendre sum (8)
controls the **sign** of `x` for many `x`; it does **not** bound the
other Dirichlet characters modulo the changing `a=4x−p`, evaluated
at the exact divisor residues. The local prime example proves that
this remaining contribution can cancel more than three units of
correct-sign main mass at a fiber, and the CRT construction does the
same on arbitrarily large selected subcollections. Neither is a
counterexample to a possible new *global* pointwise argument.

In a dyadic range `p∈[X,2X]` with `log X≥64`, a single hypothetical
bad prime would contribute at least

    |T(p)|² = M(p)² ≥ (3·2¹⁸ log 2)⁻² (log X)^6

to a sum of squared errors over these primes.
Ordinary large-sieve/exceptional-density estimates of scale
`X/(log X)^C`, however strong for each *fixed* `C`, cannot by
themselves force the **zero** exceptional primes needed here. The
positive main term, even after filtering by the necessary Jacobi
character and combining both exact types, is **not** a positive
representation count without (12).
