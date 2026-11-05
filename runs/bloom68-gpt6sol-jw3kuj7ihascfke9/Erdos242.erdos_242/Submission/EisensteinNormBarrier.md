# Eisenstein norms and the missing full Erdős–Straus divisor

**Status.** `EisensteinNormBarrier.lean` proves the conditional Eisenstein-axis, paired-norm, and full-Type-I/II statements below without `sorry` and without importing or editing `Spec.lean`. The ideal-theoretic existence argument, general *twisted-line* formula, and the additional finite examples in this note are ordinary mathematical arguments, **not** claimed as Lean theorems. Nothing here proves that every hard prime has an ordered decomposition, or produces an insoluble prime.

## What split Eisenstein and Gaussian prime ideals actually imply

Let `p≡1 (mod 24)` be prime. In `Z[ω]`, where `ω²+ω+1=0`, the norm is `N(A+Bω)=A²−AB+B²`. Because `p≡1 (mod 3)`, the polynomial `T²+T+1` has a root in `F_p`; thus a prime ideal above `p` has norm `p`. The Eisenstein integers are Euclidean, hence that ideal has a generator of norm `p`. Unit rotations and conjugation give positive integers `B,C` with

    A=B+C,             p=A²−AB+B²=B²+AC=C²+AB.           (1)

We can swap `B,C` so that `B≥C`. For prime `p`, the coordinates are primitive: `gcd(A,B)=gcd(B,C)=gcd(A,C)=1`. This representation exists for every hard prime, but that **does not** mean any target divisor exists.

For each prime `r|ABC`:

* If `r|A` or `r|B`, the equality `p=C²+AB` makes `p` a nonzero square modulo `r`.
* If `r|C`, the equality `p=B²+AC` does the same.
* For odd `r`, reciprocity and `p≡1 (mod 4)` imply **`(r/p)=+1`**; for `r=2`, use `p≡1 (mod 8)`. Nonzeroness follows from `r<p` and primality of `p`. The Lean theorem `eisenstein_axis_factors_residue` proves this with the full Jacobi symbol (even primes included).

The Gaussian representation `p=u²+v²` likewise has **only** `p`-residue prime factors in `uv` (`GaussianNormBarrier.gaussian_coordinate_factors_residue`). Consequently every prime dividing `u v A B C` is a residue. The Lean theorems `eisenstein_supported_candidate_no_types` and `paired_norm_supported_candidate_no_types` show: if `p<4x`, `x<p`, and `x | (uvABC)^e` (or just `x | (ABC)^e`), **neither** complete criterion

    Type I:   c>0, c|x², 4x−p | 4c+1;
    Type II:  0<d<x, d|x², 4x−p | x+d                         (2)

can hold. This is a direct application of the full `c|x²` Jacobi obstruction in `PointwiseJacobi.lean`, not a restriction to `c|x`. `hard_paired_norm_solution_needs_external_prime` proves that **any** solution at such a prime needs an odd nonresidue prime `r≥5` dividing `x` **outside both norm coordinate products**. Multiplying coordinates of two norm representations therefore makes the original Gaussian difficulty *worse*, not better.

There is a particularly tempting Eisenstein candidate. From (1), with `B≥C`,

    p=(B−C)²+3BC,        x=BC,        4x−p=BC−(B−C)².      (3)

It lies below `p/3`; it is an ordered candidate precisely if `(B−C)²<BC`. **When eligible, it always fails both (2)**, because all its factors are Eisenstein-axis residues. Other eligible coordinate products, such as `x=AC`, fail identically. These are pointwise failures, not counterexample primes.

| hard prime and norm `(A,B,C)` | Gaussian `uv` | Eisenstein coordinate product and `4x−p` | outcome at that x |
|---|---:|---|---|
| `193`, `(16,9,7)` | `84` | `x=BC=63`, `a=59` | both types fail |
| `2521`, `(56,41,15)` | `1260` | `BC=615` is **below** `p/4`; `x=AC=840`, `a=839` | both types fail at `840` |
| `6553`, `(91,64,27)` | `2664` | `x=BC=1728`, `a=359`; also `x=AC=2457`, `a=3275` | both types fail at each |

The three Gaussian products also lie in the ordered interval and fail (`GaussianNormBarrier.lean`). The three advertised Eisenstein product failures at `63,840,1728` are proved in the new Lean file, including the full Type-I and Type-II predicates.

## Twisting the ideal: a local way to *find* nonresidues

Let `m,n` be coprime integers, put `L=mA+nB` and `K=m²+mn+n²=N(m−nω)`. The first coefficient of `(m−nω)(A+Bω)` is `L`, while its norm is `Kp`. For an **odd** prime `r<p` dividing `L`, the primitive vector `(A,B)` modulo `r` is a nonzero multiple of `(n,−m)`. Consequently

    p ≡ t² K (mod r), t≠0,    and therefore (r/p)=(K/r).     (4)

Here `r∤K`, or else `r|p`; the final equality uses `p≡1 (mod 4)`. This is an **exact local character relation**, not a source of `c|x²` or `d|x²`. For `r=2`, `(2/p)=+1` separately. The six unit directions have `K=1` and recover the axis obstruction above. The three `K=3` directions may have nonresidue factors: `L=A+B, 2A−B, A−2B`, and an odd factor `r` is a nonresidue exactly when `(3/r)=−1`. But at `p=2521`, these three values are

    A+B=97,       2A−B=71,       |A−2B|=26=2·13;

**all** their prime factors are `2521`-residues. Thus even the first natural nonunit Eisenstein twist does not always give the needed prime. More drastically, the prime `37489` has `(A,B,C)=(208,175,33)` and Gaussian coordinates `(25,192)`. Its three `K=3` direction values are `383,241,142=2·71`; all six `K=7` direction values are `591=3·197,558=2·3²·31,317,449,109,274=2·137`. **Every displayed factor is a residue modulo 37489**. Primality has the short order certificate `37488=2⁴·3·11·71`, `19^37488≡1 (mod 37489)`, while the powers at exponents `37488/q` for `q=2,3,11,71` are respectively `37488,11354,25136,21383`, none `1`. This example only refutes a *small-twist nonresidue guarantee*; it is soluble, e.g. `x=c=9378`, `a=23|4c+1`.

The `K=7` line `L=2A−3B` **does** give one external nonresidue prime and a genuine ordered witness at each of the three requested primes. Given such a prime factor `r` with `4r<p`, the explicit first eligible multiple is `x=r(⌊p/(4r)⌋+1)`; its eligibility says *nothing* about exact divisor targets:

| `p` | `L` and nonresidue factor `r` | `x` (first multiple of `r` exceeding `p/4`), `a=4x−p` | exact full certificate |
|---|---|---|---|
| `193` | `5`, `r=5` | `x=50`, `a=7` | Type I: `c=5|50²`, `7|21` |
| `2521` | `−11`, `r=11` | `x=638`, `a=31` | Type II: `d=44|638²`, `44<638`, `31|682`; also Type I: `c=116|638²`, `31|465` |
| `6553` | `−10=−2·5`, `r=5` | `x=1640`, `a=7` | Type I: `c=5|1640²`, `7|21` (Type II also works with `d=5`) |

The Type-I/II witnesses in the last table are Lean-checked (`eisenstein_twist_193_typeI`, `eisenstein_twist_2521_typeI`/`_typeII`, `eisenstein_twist_6553_typeI`/`_typeII`). The `eisenstein_twist_*_good` theorems certify strictly ordered positive denominators via `good_of_typeI`/`good_of_typeII`. For instance Type II at `2521` gives `(638,55462,804199)`; Type I at `6553` gives `(1640,1612120,32207995)`, with the exact fraction identity Lean-checked as `eisenstein_twist_6553_explicit`.

In fact a nonresidue-bearing eligible `x` is known **for every** hard prime, even without a norm. The dyadic-window lemma proved ordinarily in `GaussianNormBarrier.md` chooses any nonresidue `n<p/2` and doubles it until `p/4<x=2^e n<p/2`; `(2/p)=+1` preserves its sign. This still gives no `c` or `d` in (2). Taking the least nonresidue primes `r=5,11,5` and doubling gives `(p,x,a)=(193,80,127),(2521,704,295),(6553,2560,3687)`: **both full types fail at each of those x**, as the integer-only check below reconfirms. Thus obtaining an eligible nonresidue is not the all-prime covering step.

**The line is not a universal construction.** The prime `p=241=16²−16·15+15²` has `L=−13` and `(13/241)=−1`. Its first in-range multiple `x=65=5·13` has `a=19`. Every divisor of `x²=4225` has residue in `{1,2,5,6,7,8,9,13,17} (mod 19)`; the Type-I target `−4⁻¹≡14` and even the *unrestricted* Type-II target `−x≡11` are both missing. Indeed **all five** eligible multiples `65,78,91,104,117` of `13` fail both types, by direct divisor enumeration. This does not make `241` a counterexample: `x=62,a=7,d=1` satisfies Type II (`7|63`). Even the nonresidue requirement for this specific line fails at `p=337=21²−21·13+13²`, where `L=3` and `(3/337)=+1`.

## The exact extra conditions that norms do not force

A useful diagnostic for a *single-prime* Type-I cofactor `c=r` is an exact equivalence. Because `r` is prime, `r|x²` means `r|x`. Thus an eligible solution with `c=r` requires an **actual divisor** `a` satisfying

    a≡3 (mod 4),  0<a<p,  a|4r+1,  a≡−p (mod 4r),
    x=(p+a)/4.                                              (5)

Conversely such an `a` gives that Type-I witness if `p<4x<2p`; the displayed inequalities on `a` give this range. Merely knowing `(r/p)=−1` says nothing about the last two requirements. For `p=2521,r=11` the `3 (mod 4)` divisors of `4r+1=45` are `3,15`, but `−p≡31 (mod 44)`: **neither works as `c=11`**. Yet at `x=638` the larger cofactor `c=116` and Type-II divisor `d=44` do work. At `p=241,r=13`, `4r+1=53` is prime `1 (mod 4)`, so `c=13` is impossible for *any* `p≡1 (mod 4)`; this says nothing about cofactors containing other factors. At `p=6553,r=31`, similarly `4r+1=125=5³` has no `3 (mod 4)` divisor. At `p=193` and `6553`, the *other* nonresidue `r=5` has `a=7|4·5+1` and `p+7≡0 (mod 20)`, providing the table's successes.

One can make `a|p+4d` automatic from a norm identity but still **not** get Type II. Since `a=4x−p` is odd, `a|x+d` is equivalent to `a|p+4d`. For the Gaussian representation with `v≡0 (mod 4)`, set `d=uv/2`; then

    p+4d=(u+v)².                                           (6)

For an Eisenstein representation `p=s²+3t²`, `s,t>0`, `t≡0 (mod 4)`, set `d=st`; then

    p+4d=(s+t)(s+3t).                                      (7)

Any divisor `a≡3 (mod 4)`, `0<a<p`, of the right side gives an eligible `x=(p+a)/4` satisfying `a|x+d`. However **`d|x²` (and `d<x`) remain separate**, and need not hold. On the requested primes:

| `p` | Gaussian `(u,v)`, `d=uv/2`, eligible `a` and failure | Eisenstein `(s,t)`, `d=st`, exact result |
|---|---|---|
| `193` | `(7,12)`, `d=42`, `p+4d=19²`; `a=19`, `x=53`, but `42∤53²` | `(1,8)`, `d=8`, `p+4d=225`; **`a=15`, `x=52`, `8|52²`, `15|60` succeeds** |
| `2521` | `(35,36)`, `d=630`, `p+4d=71²`; `a=71`, `x=648`, but `630∤648²` | `(13,28)`, `d=364`, `p+4d=41·97`; every divisor is `1 (mod 4)`, so **no eligible `a`** |
| `6553` | `(37,72)`, `d=1332`, `p+4d=109²`; every divisor is `1 (mod 4)` | `(59,32)`, `d=1888`, `p+4d=91·155`; only eligible `a` with `x>d` is `2015` (`x=2142`), but `59∤2142`, so `1888∤x²` |

The Gaussian table entries are *failure of this selected d*, not the general Gaussian-coordinate theorem. The `193` Type-II success from (7) is another ordered decomposition, whereas the `2521` and `6553` failures are only failures of (6)–(7), not of those primes.

For reproducibility, this uses only integer arithmetic (the prime test is trial division, and Euler's criterion is applied after it):

```python
from math import isqrt

def prime(n):
    return n >= 2 and all(n % q for q in range(2, isqrt(n)+1))

def pf(n):
    assert n > 0
    factors = []
    q = 2
    while q*q <= n:
        if n % q == 0:
            factors.append(q)
            while n % q == 0:
                n //= q
        q += 1
    if n > 1:
        factors.append(n)
    return factors

def divs(n):
    return {d for i in range(1, isqrt(n)+1) if n % i == 0
            for d in (i, n//i)}

for p,A,B,x in [(193,16,9,63), (2521,56,41,840),
                (6553,91,64,1728), (6553,91,64,2457)]:
    assert prime(p) and p == A*A-A*B+B*B and p < 4*x < 2*p
    assert all(pow(r, (p-1)//2, p) == 1 for r in pf(A*B*(A-B)))
    a = 4*x-p
    assert not any((4*c+1) % a == 0 for c in divs(x*x))
    assert not any(d < x and (x+d) % a == 0 for d in divs(x*x))

for p,x,c in [(193,50,5), (2521,638,116), (6553,1640,5)]:
    a = 4*x-p
    assert p < 4*x < 2*p and c in divs(x*x) and (4*c+1) % a == 0
assert 44 < 638 and 44 in divs(638*638) and (638+44) % 31 == 0

for p,r,e in [(193,5,4), (2521,11,6), (6553,5,9)]:
    x = (2**e)*r
    a = 4*x-p
    assert prime(p) and pow(r,(p-1)//2,p) == p-1 and p < 4*x < 2*p
    assert not any((4*c+1) % a == 0 for c in divs(x*x))
    assert not any(d < x and (x+d) % a == 0 for d in divs(x*x))

for p,u,v,s,t in [(193,7,12,1,8), (2521,35,36,13,28),
                  (6553,37,72,59,32)]:
    assert p == u*u+v*v == s*s+3*t*t and v%4 == t%4 == 0
    dg, de = u*v//2, s*t
    assert p+4*dg == (u+v)**2 and p+4*de == (s+t)*(s+3*t)
    g = [(a,(p+a)//4) for a in divs(p+4*dg)
         if 0 < a < p and a%4 == 3]
    e = [(a,(p+a)//4) for a in divs(p+4*de)
         if 0 < a < p and a%4 == 3]
    assert not any(x*x % dg == 0 for a,x in g)
    good_e = [(a,x) for a,x in e if de < x and x*x % de == 0]
    assert good_e == ([(15,52)] if p == 193 else [])
    if p == 2521:
        assert not e
    if p == 6553:
        assert [(a,x) for a,x in e if de < x] == [(2015,2142)]

assert prime(241) and pow(13,120,241) == 240
assert {d % 19 for d in divs(65*65)} == {1,2,5,6,7,8,9,13,17}
for x in (65,78,91,104,117):
    a = 4*x-241
    assert not any((4*c+1) % a == 0 for c in divs(x*x))
    assert not any(d < x and (x+d) % a == 0 for d in divs(x*x))
assert 241 < 4*62 < 2*241 and (4*62-241) == 7 and (62+1) % 7 == 0
assert prime(337) and 337 == 21*21-21*13+13*13
assert pow(3,168,337) == 1  # the single norm-7 line gives only 3

assert prime(37489)
A,B,p = 208,175,37489
assert p-1 == 2**4*3*11*71 and pow(19,p-1,p) == 1
assert [pow(19,(p-1)//q,p) for q in (2,3,11,71)] == [37488,11354,25136,21383]
assert p < 4*9378 < 2*p and (4*9378-p) == 23 and (4*9378+1) % 23 == 0
assert p == A*A-A*B+B*B
for m,n in [(1,1),(2,-1),(1,-2), (2,1),(1,2),(1,-3),
            (3,-1),(2,-3),(3,-2)]:
    L = abs(m*A+n*B)
    assert all(pow(r,(p-1)//2,p) == 1 for r in pf(L))
```

## Precisely unresolved

The established reduction `CoveringGap.all_good_iff_explicit_hard_cover` asks that **for every** hard prime `p=24k+1` there be some `0≤j<6k`, `x=6k+1+j`, `a=4j+3` with **one of the actual divisors in (2)**. This investigation only proves that denominators supported on the two norms' axes cannot work, provides conditional nonresidue sources and three individual solutions, and exhibits failures of attractive candidate formulas. Even when a twisted coordinate has a nonresidue factor and a suitable `x` in the interval, neither (4) nor the factorization of `p+4d` implies `a|4c+1` for some `c|x²` or `a|x+d` for some `0<d<x`, `d|x²`. **That pointwise all-prime divisor existence, or a prime for which it fails at every candidate, remains entirely unproved.**

Verification: `lake env lean Submission/EisensteinNormBarrier.lean` and `lake build Submission.EisensteinNormBarrier` pass. `#print axioms` on the four general theorems and all three pointwise failures reports only `propext`, `Classical.choice`, `Quot.sound` (no `sorryAx`). `Spec.lean` is unchanged.
