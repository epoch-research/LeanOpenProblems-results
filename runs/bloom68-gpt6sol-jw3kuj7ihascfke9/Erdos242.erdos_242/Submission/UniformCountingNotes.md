# Uniform first-denominator counts: a pointwise Erdős–Straus gap

This is an ordinary mathematical analysis, **not** a proof of Erdős–Straus or
of `Submission/Spec.lean`. The first-denominator criterion is the one already
proved independently in `IndependentNotes.md`. No Lean file is changed here.

Write `p=4n+1` for a prime `p≡1 (mod 24)`. All ordered first
denominators must lie in the following candidate list (not every candidate
works):

    x=n+1+j,  a=4x-p=4j+3,  0≤j<n.

In particular `gcd(a,x)=gcd(p,x)=1`. The two exact ways to succeed at `x` are

    (I)  c | x²,       a | 4c+1;
    (II) 0<d<x, d|x², a | x+d.

The counts below are uniform in **each** `p`; none counts actual successes
from below.

## A large uniform zero-frequency term is not a witness count

Let `τ(t)` denote the number of positive divisors of `t`, and set

    V(p) = Σ_{p/4<x<p/2} [τ(x²)−τ(x)]/(4x−p).

Here `τ(x²)−τ(x)` counts **nonsquare** divisors of `x²` (the square
divisors are precisely `t²`, `t|x`). For all sufficiently large
`p≡1 (mod 4)`, with absolute constants,

    V(p) ≫ (log p)³.                                          (1)

This remains true although *no square divisor `c` can satisfy (I)*:
`a≡3 (mod 4)` has a prime factor `q≡3 (mod 4)` and `q∤4t²+1`
for every `t` (otherwise `−1` would be a square modulo `q`).

**Proof of (1).** The elementary identity

    τ(x²) = #{(d,e): d|x, e|x, gcd(d,e)=1}                 (2)

holds prime power by prime power: a prime occurring to exponent `h` in `x`
can occur in either `d` or `e` to one of the exponents `1,...,h`, or in
neither, for `2h+1` possibilities. Choose a dyadic `A` with
`√p≤A≤p/4`, and take the consecutive `x` corresponding to
`A≤a=4x−p<2A`. There are `H=A/4+O(1)≍A` of them. Put
`R=⌊A^(1/8)⌋`. For all sufficiently large `A`, if `d,e≤R` are
coprime then `de≤A^(1/4)≤H/2`, so at least `H/(2de)` of these
consecutive `x` satisfy `de|x`. Consequently (2) gives

    Σ_block τ(x²) ≥ (H/2) Σ_{d,e≤R, gcd(d,e)=1} 1/(de)
                  ≥ (H/8) (Σ_{d≤R} 1/d)²
                  ≫ H (log A)².                              (3)

For the second inequality, discard noncoprime pairs by the union bound:
for each prime `q`, their weighted sum is at most
`(Σ_{d≤R, q|d}1/d)²≤(Σ_{d≤R}1/d)²/q²`, while
`Σ_{q prime}q^(-2)≤Σ_{j≥2}j^(-2)≤3/4`.

Also, since all these `x<p/2`, every divisor pair of `x` has one
member at most `√p`. Counting multiples of each such small member gives

    Σ_block τ(x) ≤ 2H Σ_{d≤√p}1/d + 2√p ≪ H log p,

uniformly because `H≳√p`. As `log A≥(log p)/2`, subtracting
this from (3) still leaves `≫H(log p)²` for sufficiently large `p`.
Since `a<2A`, each dyadic block contributes `≫(log p)²` to `V(p)`.
There are `≫log p` disjoint dyadic blocks, proving (1).

For clarity about the gap, put

    I(p) = Σ_x Σ_{c|x², c nonsquare} 1_{a|4c+1}.

Character orthogonality gives an **exact** expression

    I(p) = V(p)
         + Σ_x (1/a) Σ_{r=1}^{a−1} exp(2πir/a)
                    Σ_{c|x², c nonsquare} exp(2πi4rc/a).    (4)

Thus (1) controls the `r=0` term, not the oscillatory sum in (4).
Forcing (4) to be positive for **each** `p` requires an additional
pointwise estimate (indeed, type-I existence for every `p` would be a
stronger theorem than the requested type-I-or-II alternative). A
second-moment/large-sieve bound averaged over `p` cannot simply be
promoted to that pointwise estimate.

## Many *locally plausible* denominators, but no exact residue guarantee

Let `(·/a)` be the Jacobi symbol, and `(·/p)` the Legendre symbol.
Quadratic reciprocity, `p≡1 (mod 4)`, and `p≡4x (mod a)` give

    (x/a) = (p/a) = (a/p).                                  (5)

The Pólya–Vinogradov bound for the nonprincipal character `(·/p)`
therefore gives a genuinely **uniform-in-`p`** count:

    #{p/4<x<p/2 : (x/(4x−p))=−1}
         = (p−1)/8 + O(√p log p).                           (6)

Indeed, with `a=4j+3`, the character sum is
`Σ_{0≤j<n}(4j+3/p)=Σ_{0≤j<n}(j+3·4^(−1)/p)`, an incomplete
sum over consecutive residues. Hence a positive proportion of all `x`
has some prime factor `q|x` with `(q/a)=−1`. This excludes the
following simple local obstruction, but it does **not** supply (I) or
(II).

**Quadratic-subgroup obstruction.** If all prime factors `q|x` have
`(q/a)=+1`, *both* (I) and (II) fail: every divisor of `x²` has
Jacobi symbol `+1`, whereas (I) would require
`c≡−4^(−1) (mod a)`, whose symbol is `−1`, and (II) would require
`d≡−x (mod a)`, also of symbol `−1` because `(x/a)=+1`.

A large-divisor counterexample occurs already at the requested residual
prime `p=66529`: take `x=16650=2·3²·5²·37` and `a=71`.
All four factors are quadratic residues modulo 71: 2 and 3 by the
standard supplementary formulas, 5 because `71≡1 (mod 5)`, and 37
because `(37/71)=(34/37)=+1` (`16²≡34 (mod 37)`). There are
`τ(x²)=3·5·5·3=225` divisors, **189 of them nonsquare**; nevertheless
none gives (I) or (II). Their symbols are all `+1`, while the required
residues are `c≡53` and `d≡35 (mod 71)`, both nonsquares. Thus even
more than three times as many divisors as residue classes do not
justify pigeonholing a target class.

Nor does removing the quadratic obstruction or having a primitive-root
factor suffice. At `p=1201, x=303, a=11` we have `x=3·101`, and at
`p=2521, x=633, a=11` we have `x=3·211`. Both second factors are
`2 (mod 11)`, a primitive root modulo 11; `(x/11)=−1`. Yet divisors
of either `x²` have, modulo 11, only the residues

    {3^i 2^j : 0≤i,j≤2} = {1,2,3,4,6,7,9}.

The required type-I residue is `c≡8 (mod 11)`, and the required
type-II residue is `d≡−x≡5 (mod 11)`: both are absent. Having
`ord_11(2)=10` is irrelevant if its permitted exponent is only 0, 1
or 2. Conversely, `(x/a)=−1` is not *necessary* for a witness:
`p=2521,x=638,a=31` has `(x/31)=+1` but satisfies (II) with `d=44`.
The subgroup obstruction concerns the symbols of **each prime factor**
of `x`, not just the symbol of `x` itself. For an even sharper finite
counterexample, the prime
`p=1067761≡121 (mod 840)` has `p+4=5·213553` with both factors
`1 (mod 4)`; at `x=(p+11)/4=266943=3·101·881`, `a=11`,
`τ(x²)=27>11`, `(x/11)=−1`, and a primitive-root factor is present,
but the same seven divisor residues still rule out (I) and (II) **at
this x**. The prime itself is soluble, e.g. `x=266942,a=7,c=26`.

Direct exact enumeration for the three requested primes gives the
following diagnostic (the final column counts *first denominators*,
not the number of divisor choices):

    p        possible x    #(x/a)=−1     x satisfying (I) or (II)
    1201         300            154                   7
    2521         630            323                   7
    66529      16632           8345                  25

This illustrates the gap between the uniform character count (6) and
actual witnesses; the table is a finite check, not an asymptotic
claim.

## An infinite pointwise obstruction for type II away from `p/4`

For a type-II pair `(x,d)`, define `m=(x+d)/a`. Then, since
`gcd(a,d)=1` and `d|x²`, reduction of `x=am−d` modulo `d` shows
`d|m²`. Furthermore

    (4m−1)a=p+4d,        d=(4m−1)x−mp.                   (7)

For **every** `m≥1`, `h=4m−1`, and positive `d|m²`, one has

    h ∤ 1+4d.                                                  (8)

To prove (8), write `e=m²/d`. If `h|1+4d`, then also `h|1+4e`,
because `16m²=h(4m+1)+1` and
`(1+4d)·4e=4e+16m²`. Both divisibilities imply `d,e≥m`;
`de=m²` forces `d=e=m`, but then `h|1+4m=h+2`, impossible for
`h≥3`.

In particular `p≡1 (mod h)` makes a type-II witness with this `m`
impossible. As proved already in `Partial.lean`, Dirichlet's theorem
therefore supplies, **for every fixed `B`**, arbitrarily large primes
`p≡1 (mod 840)` with no type-II witness having `m≤B`.
Here is a quantitative strengthening using two standard unconditional
theorems. Put

    L_B = 840·lcm(1,2,...,4B).

The elementary Chebyshev estimate
`log lcm(1,...,t)=ψ(t)=O(t)` says `log L_B=O(B)`. Linnik's
theorem says that the least prime `p_B≡1 (mod L_B)` is at most
`O(L_B^C)` for absolute constants. These primes tend to infinity
(`p_B≥L_B+1`) and satisfy `log p_B=O(B)`. For each `m≤B`,
`h=4m−1|L_B`, so (7)–(8) rule it out. Hence, for an absolute
`c>0`, infinitely many hard primes have **no** type-II witness with
`m≤c log p`.

Finally, `d<x` in (7) implies

    x < mp/(4m−2) = p/4 + p/(8m−4).                       (9)

For the constructed primes, `m≥B+1`, so every type-II first
denominator must satisfy

    p/4 < x < p/4 + p/(8B+4) = p/4 + O(p/log p).           (10)

Thus, for infinitely many primes, all but `O(p/log p)` of the
`(p−1)/4` proposed first denominators are **provably type-II-free**.
This is not an obstruction to type I. In fact already for *every*
`p≡1 (mod 24)`, `m=1` is forbidden by (8) and `p≡1 (mod 3)`;
(9) with `m≥2` yields `x<p/3` for every type-II witness.

## Exact residual-prime witnesses and conclusion

The three requested primes satisfy `p mod 840 = 361, 1, 169`,
respectively, and `p+4 = 5·241, 5²·101, 66533`; all the odd factors
shown are `1 (mod 4)` (and `66533` is prime). The smallest proposed
denominator `x=(p+3)/4` fails at all three: the respective values are
`301=7·43`, `631` and `16633`; all their prime factors are
`1 (mod 3)`, so their `a=3` criterion fails. They are **not**
Erdős–Straus counterexamples:

    p       x      a     d    x²/d     (x, y, z)
    1201    306    23   108     867    (306, 21618, 61251)
    2521    638    31    44    9251    (638, 55462, 804199)
    66529  17060  1711   50 5820872   (17060, 665290, 226996948)

In each row `d|x²`, `0<d<x`, `a|x+d`; setting `b=x²/d` gives
the strictly ordered exact identity

    4/p = 1/x + 1/[p(x+d)/a] + 1/[p(x+b)/a].

All displayed primes and congruences were checked by integer
arithmetic, and all three fractional identities by exact rational
arithmetic. For `p=66529` there is also a type-I-only witness at
`x=16637=127·131`, `a=19`, `c=127·131²=2179447`:
`4c+1≡0 (mod 19)`, but none of the nine residues
`13^i17^j (mod 19)`, `0≤i,j≤2`, equals `−x≡7 (mod 19)`.
Thus discarding type I at an individual `x` is unsafe.

A pointwise proof must control the **nonzero** terms in (4), or another
correlation that forces one of the exact divisor congruences (I)/(II)
for each hard prime. The fixed-`K` shifted-factor sieve in
`ShiftSieveNotes.md` proves very small exceptional density, but its
constants and truncation are not uniform when `K` grows with `p`.
Concretely, its displayed elementary CRT error is
`z^(2+2 log₂(2(K+1)))`; keeping this below `X^(1/2)` when
`z=X^η` requires `η≲1/log K`. If one naively chooses `K=X^θ`,
then `z=exp(O(1))`, giving no growing sieving range or Mertens gain.
Arbitrarily strong bounds `O_C(X/log^C X)` for each *fixed* `C`
still allow an infinite exceptional set. Neither (1), (6), the
small-modulus/primitive-root
heuristics, nor the sieve supplies the missing pointwise estimate.
No deterministic existence theorem for every `p≡1 (mod 24)` has been
proved here.

For reproducibility, the table and the three ordered identities can be
checked by the following *finite* exact-arithmetic script (it makes no
claim for untested primes):

```python
from fractions import Fraction
from sympy import divisors, isprime, legendre_symbol

for p in (1201, 2521, 66529):
    assert isprime(p) and p % 24 == 1
    n = (p - 1) // 4
    nonresidues = successes = 0
    for x in range(n + 1, 2 * n + 1):
        a = 4 * x - p
        ds = divisors(x * x)
        nonresidues += int(legendre_symbol(a, p) == -1)
        successes += int(any((4 * c + 1) % a == 0 for c in ds) or
                         any(d < x and (x + d) % a == 0 for d in ds))
    print(p, n, nonresidues, successes)
    # 1201 300 154 7; 2521 630 323 7; 66529 16632 8345 25

for p, x, d in ((1201, 306, 108), (2521, 638, 44),
                (66529, 17060, 50)):
    a = 4 * x - p
    assert d < x and x * x % d == 0 and (x + d) % a == 0
    b = x * x // d
    y, z = p * ((x + d) // a), p * ((x + b) // a)
    assert x < y < z
    assert Fraction(4, p) == Fraction(1, x) + Fraction(1, y) + Fraction(1, z)
```

