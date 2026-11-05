# Pointwise Type-I counting: a cubic-log diagonal and the missing inequality

This is a mathematical **partial result and obstruction**, not a proof of
Erdős–Straus or of `Submission/Spec.lean`. No change to `Spec.lean` is made.
The exact ordered divisor criterion is proved in `Classification.lean` and
`CoveringGap.lean`.

Let `p ≡ 1 (mod 24)` be prime, write `p=4n+1`, and put

    x_j=n+1+j,       a_j=4x_j-p=4j+3,       0≤j<n.

Thus `p/4<x_j<p/2`, `3≤a_j<p`, and `gcd(x_j,a_j)=1`. Type I succeeds if
`a_j | 4c+1` for some `c | x_j²`. A square `c=t²` **never** succeeds:
`a_j≡3 (mod 4)` has a prime factor `q≡3 (mod 4)`, and
`q | 4t²+1` would make `−1` a square modulo `q`. Write `τ(v)` for the
number of positive divisors of `v` and `\mathcal D_j` for the
**nonsquare** divisors of `x_j²`. Then `|\mathcal D_j|=τ(x_j²)−τ(x_j)`.

Define the actual Type-I **pair count**, its zero-frequency term, and
its remaining terms by

    I(p) = Σ_{j<n} Σ_{c∈𝒟_j} 1_{a_j | 4c+1},
    D(p) = Σ_{j<n} |𝒟_j|/a_j,
    R(p) = Σ_{j<n} (1/a_j) Σ_{r=1}^{a_j−1} exp(2πir/a_j)
                                      Σ_{c∈𝒟_j} exp(2πi·4rc/a_j).

Additive-character orthogonality gives the **exact** identity
`I(p)=D(p)+R(p)`. In particular `R(p)` is real, although its displayed
summands need not be. Type I for *every* hard prime would follow from a
**pointwise** one-sided bound `R(p)>−D(p)` for every such prime. The
stronger estimate `|R(p)|≤(1−δ)D(p)` for some fixed `δ>0` and all
sufficiently large hard primes, plus separate verification of the
finitely many smaller ones, would also suffice. **Neither estimate is
proved here.** Type-I universality is stronger than the exact
Type-I-or-Type-II alternative needed for Erdős–Straus.

## What can be proved uniformly about the diagonal

**Proposition.** For every prime `p≡1 (mod 24)` with `log p≥32768`,

    D(p) ≥ (log p)³ / (2²⁰ log 2).                          (1)

The enormous cutoff and small constant merely make every estimate
explicit; this is a statement about the *zero mode*, not about `I(p)`.

**Proof.** Take all dyadic `A=2^k` with `√p≤A≤p/4`, and let `J_A`
be the consecutive integers `x` with `A≤4x−p<2A`. These are all
eligible first denominators. Their number `H` satisfies
`H≥A/4−1≥A/8`. Let `U=⌊A^(1/8)⌋`. For `d,e≤U` with
`gcd(d,e)=1`, we have `de≤A^(1/4)≤A/16≤H/2` (as
`A≥√p≥64`); at least `H/(2de)`
of these `x` are divisible by `de`. The identity

    τ(x²) = #{(d,e): d|x, e|x, gcd(d,e)=1}

follows prime-power by prime-power. Moreover, writing
`H_U=Σ_{d≤U}1/d`, the union bound over common prime factors gives

    Σ_{d,e≤U, gcd(d,e)=1} 1/(de)
      ≥ H_U² (1−Σ_{q prime}1/q²) ≥ H_U²/4.

Indeed `Σ_{d≤U,q|d}1/d≤H_U/q`, and
`Σ_{q prime}q^(−2)≤Σ_{m≥2}m^(−2)<3/4`: the terms with
`m≥3` are strictly less than `1/[m(m−1)]`, whose sum is `1/2`,
and the `m=2` term is `1/4`. Since `U≥A^(1/8)/2` and
`log A≥(log p)/2`, we have
`log U≥(log p)/16−log 2≥(log p)/32` under our assumption.
Consequently

    Σ_{x∈J_A} τ(x²) ≥ H (log p)² / 8192.                 (2)

For each `x<p/2`, every factor pair of `x` has a member at most
`√p`. Counting the multiples of each `d≤√p` in the `H` consecutive
integers, and using `H≥√p/8`, gives

    Σ_{x∈J_A} τ(x)
      ≤ 2 Σ_{d≤√p}(H/d+1)
      ≤ H(log p+2)+2√p ≤ H(log p+18).

For `log p≥32768`, this is at most `H(log p)²/16384`.
Subtracting it from (2), and using `a_j<2A`, shows that this block
contributes at least `(log p)²/262144` to `D(p)`. There are at least
`(log p)/(4 log 2)` such disjoint dyadic blocks: the number of
integers `k` in the specified interval is at least
`(log p)/(2 log 2)−3`. Summing proves (1). `□`

In particular there are `≫(log p)³` **weighted diagonal contributions**
for every sufficiently large hard prime, as already observed in
`UniformCountingNotes.md`. It would be incorrect to replace the
constant in (1) by `1` without another argument, or to identify the
zero mode with a count of witnesses.

## The residue obstruction is real, even after discarding squares

For each `a_j`, the Jacobi character `χ_a(v)=(v/a_j)` is nonprincipal:
`a_j≡3 (mod 4)` and `χ_a(−1)=−1`. Since `gcd(a_j,x_j)=1`, the
required Type-I residue `c≡−4^(−1) (mod a_j)` has `χ_a(c)=−1`.
If **every prime factor of `x_j` has Jacobi symbol `+1` modulo `a_j`**,
then every divisor of `x_j²` has symbol `+1`, so there is no Type-I
witness. Type II also fails at this `x_j`: its required residue
`d≡−x_j (mod a_j)` has symbol `−1`. In the multiplicative-character
expansion of the count of `c∈𝒟_j` in its target unit class, the
principal character contributes `|𝒟_j|/φ(a_j)` and the Jacobi
character contributes `−|𝒟_j|/φ(a_j)`. They cancel **exactly** in
this case; a nonsquare *integer* divisor need not be a quadratic
nonresidue modulo `a_j`.

For an exact finite example, `p=66529` is a hard prime and

    x=16650=2·3²·5²·37,     a=4x−p=71.

The factors `2,3,5,37` are quadratic residues modulo `71`: the
supplementary formulas handle `2` and `3`, reciprocity handles `5`,
and `(37/71)=(34/37)=+1` since `16²≡34 (mod 37)`. Thus the
`τ(x²)−τ(x)=225−36=189` nonsquare divisors **all** miss the
Type-I target `53 (mod 71)` and the Type-II target `35 (mod 71)`.
The local contribution to `D(p)` is `189/71>1`, but the local
nonzero-frequency contribution is **exactly `−189/71`**. Both types
fail *at this first denominator*; the prime is nevertheless soluble,
for instance at `x=17060`, `a=1711`, `d=50` in Type II.

Even a nonresidue prime factor and a primitive-root factor do not
repair this argument. `p=13873` is prime, `x=3471=3·13·89`, and
`a=11`. Here `13≡2 (mod 11)` is a primitive root, `(x/11)=−1`,
and `τ(x²)−τ(x)=27−8=19>11`. Nevertheless the residues of all
`c|x²` form only

    {3^i 2^j (mod 11) : 0≤i,j≤2} = {1,2,3,4,6,7,9};

neither the Type-I target `8` nor the Type-II target `−x≡5` is
present. This prime actually **does** have a solution at `x=3470`,
`a=7`, `c=5` (or a Type-II witness `d=2` there).

The primality statements in these examples have short Lucas
certificates. For `66529−1=2⁵·3³·7·11`, base `19` has
`19^66528≡1 (mod 66529)`, while its powers with exponents
`66528/q`, for `q=2,3,7,11`, have respective residues
`66528,24356,41061,21372`, none `1`. For
`13873−1=2⁴·3·17²`, base `5` has `5^13872≡1 (mod 13873)`
and its powers with exponents `13872/q`, `q=2,3,17`, have
residues `13872,6834,4565`, none `1`. Thus in each case the base
has order `p−1`, which cannot occur for a composite modulus.

## Arbitrarily many candidate moduli can have *selected* fake terms

**Simultaneous-seed lemma.** Let `S` be any fixed finite nonempty set
of integers `a≥3` with `a≡3 (mod 4)` and let `t≥1`. There are
infinitely many hard primes `p` such that, **for every `a∈S`**, the
candidate `x_a=(p+a)/4` has at least `3^t−2^t` nonsquare divisors
`c|x_a²` which all fail `a|4c+1`. There are also `3^t` divisors
`d|x_a²` which fail `a|x_a+d`; taking `p` sufficiently large makes
all these `d<x_a`. This says **nothing** about the *other* divisors
of `x_a²` or the other candidate moduli.

**Proof.** Put `A=24∏_{a∈S}a`. For each `a`, select `t` new distinct
primes `r≡1 (mod A)` (Dirichlet), and set `M_a` equal to their
product; make all the `M_a` pairwise coprime. CRT gives a reduced
residue class satisfying

    p≡1 (mod A),           p≡−a (mod M_a) for every a∈S.

The class is reduced because `gcd(M_a,A)=gcd(M_a,a)=1`.
Dirichlet supplies arbitrarily large primes in it. For such `p`,
`a<p`, `x_a=(p+a)/4` is eligible, and `M_a|x_a`: both `4` and
`M_a` divide `p+a` and are coprime. Every `c|M_a²` is `1 (mod a)`,
so `4c+1≡5 (mod a)` and cannot be divisible by an integer
`a≡3 (mod 4)`. Since `M_a` is squarefree, exactly `3^t−2^t`
of these divisors are nonsquares. Also `p≡1 (mod a)` gives
`4(x_a+d)≡1+4≡5 (mod a)` for every `d|M_a²`. Choose
`p>4 max_a M_a²` to ensure `d<x_a`. `□`

On **these selected Type-I pairs alone**, their joint zero-frequency
contribution is `(3^t−2^t)Σ_{a∈S}1/a` and their joint nonzero
contribution is its exact negative. This demonstrates why merely
accumulating many putative diagonal terms across several `a` is not
a pointwise error estimate. It does **not** prove that the full
`R(p)` cancels `D(p)`, or that any prime lacks Type I or Type II.

For perspective, one can even arrange the selected contribution to
exceed any fixed power of `log p` along a sequence of primes, but still
only for this *subsum*. Keep `S` fixed, use the first `|S|t` primes
`r≡1 (mod A)`, and take the least prime in the resulting CRT class.
PNT in this fixed progression gives `log(∏_a M_a)=O_S(t log t)`;
Linnik's theorem gives `log p=O_S(t log t)`. Since
`3^t−2^t` exceeds every fixed power of `t log t`, the selected
Type-I zero mode eventually exceeds `(log p)^K` for each fixed `K`.
Here `p≥4M_a−a` for every `a`, so these primes go to infinity; the
extra `d<x_a` assertion is not needed for this quantitative claim.
No such conclusion is asserted about the **full** off-diagonal sum.

## What remains genuinely unproved

The proof of (1) alone gives **no** lower bound on `I(p)`: the required
one-sided pointwise estimate is `R(p)>−D(p)`, or a different argument
forcing Type I or Type II at some `j`. The finite obstructions show
that large divisor counts, a nonresidue factor, a primitive root, and
summing chosen diagonal terms across candidate moduli do not supply
that estimate. They do **not** rule out a new global cancellation
argument involving *all* `j` and all divisors.

An averaged character/large-sieve estimate cannot by itself exclude a
single missed prime. Indeed, for `p∈[X,2X]`, (1) gives
`D(p)≥c(log X)³` when `X` is sufficiently large. If `I(p)=0` for
one such prime, then `|R(p)|²=D(p)²≥c²(log X)⁶`. A bound on the
*entire* second moment smaller than `c²(log X)⁶` would exclude even
one such prime; bounds of size `X/(log X)^C` for any fixed `C` do
not reach this threshold. Likewise a bound on the number of
exceptional primes that is `o(X/log X)`, even one beating every fixed
logarithmic power, need not make that number zero. A determinant-method
upper bound on solutions, or an averaged `q`-adic/large-sieve bound,
would require an **additional pointwise lower-bound or uniform-error
argument** to settle every fiber `p`; the examples above do not
rule out such a future global argument.

Nor can one silently replace the missing Type-I bound by a **fixed**
Type-II search cutoff: `hard_primes_escape_bounded_typeII` in
`CoveringGap.lean` proves that, for every `B`, there are arbitrarily
large hard primes without a Type-II witness with
`m=(x+d)/(4x−p)≤B`. Its CRT proof chooses
`p≡1 (mod 840·(4B)!)` and uses the proved fact that
`4m−1` never divides `1+4d` when `d|m²`. This does not rule out
Type II for larger `m` or Type I at any `x`.

No valid estimate `R(p)>−D(p)` for **every** hard prime is obtained
from these arguments. In particular no pointwise Type-I theorem, no
complete hard-prime covering, and no proof of `Spec.lean` is claimed.
