# Two-axis search for hard primes: finite evidence, not a proof

This note and the standalone `AxisSearch.cpp` do **not** edit `Spec.lean` and do
**not** prove Erdős–Straus or the stronger two-axis assertion. A universal
assertion that every hard prime has axis A or B would imply the still-open
ordered Erdős–Straus assertion. The results below are **finite**, deterministic
integer computations.

Let `p ≡ 1 (mod 24)` be prime (`p ≥ 73`). Use the type-II canonical form
`m = a b c`, `d = a² b`, `gcd(a,c)=1` and `4abc−1 | cp+a`, with the strict
order conditions. An A witness has `c=1`; a B witness has `a=1`.

## Exhaustive search bounds and order

**A:** Write `q=4kb−1 | p+k`, `t=(p+k)/q`, with `k,b ≥ 1`. Necessarily
`q≥4k−1`, `q≤p+k`, so `3k≤p+1` and, since `p≡1 (mod 24)`,
`k≤(p−1)/3`. Conversely, provided `k<p`, the integer identity

    p = 4bkt − k − t,
    4/p = 1/(bkt) + 1/(pbk) + 1/(pbt)

is strictly ordered by sorting the last two terms: `k,t<p`, since
`q≥3` gives `t≤(p+k)/3<p`. Also `k≠t`, because equality would make
`p=4bk²−2k` even. Importantly, **composite** `q` are allowed.

A complete search is much shorter than `(p−1)/3` shifts. If `t<k`, then
`q'=4bt−1 | p+t` with cofactor `k`, so interchange `k,t`. With the
normalized `k<t`, one necessarily has

    p=4bkt−k−t ≥ 4k(k+1)−(2k+1) = 4k²+2k−1.

Thus testing **all** divisors of `p+k` for each
`k≥1` with `4k²+2k−1≤p` is logically equivalent to testing the full
`k≤(p−1)/3` range. In particular it does not silently discard unordered
representations: they are re-normalized and then ordered.

**B:** Put `m=bc`, `d=b | m`, `h=4m−1` and `t=(cp+1)/h`. The two exact
congruences are equivalent:

    h | cp+1    ⇔    h | p+4d.

Indeed multiply the first expression by `4d` or the second by `c`, and
use `4m≡1 (mod h)`. The denominators are `x=dt`, `y=pm`, `z=pmt`.
Writing `L=(t+1)/c=4bt−p`, we have `L≡−p≡3 (mod 4)`, so `L≥3` and
`t≥2`. Also `t=(cp+1)/h<cp` because `h≥3`; hence `x<y<z`.

Every B witness lies in the finite range **`m≤(p−1)/6`**. To see this,
`6m=6b(t+1)/L≤2b(t+1)`. Further `L≤t+1`, and
`2b(t−1)≥t+2≥L+1`: for `b≥2` this follows from `t≥2`; for `b=1`,
`p=4t−L≥73` rules out `t≤3`, and then `t≥4` suffices. Therefore
`p−1=4bt−L−1≥2b(t+1)≥6m`.

There is at most one potential proper divisor `d<m` to test for a given
`m`: set `r=p mod h`; if `h−r` is divisible by 4, its **only** candidate
is `d=(h−r)/4`, which must divide `m`. The additional case `d=m`
occurs exactly when `r=h−1`. This is exhaustive because
`0≤r<h`, `4d≤h−3` when `d<m`, and `4m=h+1`. All qualifying `d`
within `m≤(p−1)/6` satisfy the order; no heuristic cutoff is used.

A Dirichlet warning about extrapolation: for every **fixed** `M`, put
`L_M=24∏_{1≤m≤M}(4m−1)`. There are infinitely many primes
`p≡1 (mod L_M)`, but none has a B witness with `m≤M`. Indeed such a
witness would force `4m−1 | 1+4d`, `d|m`. For `m≥2`, the positive number
`1+4d` is less than `2(4m−1)`, so it would have to equal `4m−1`,
which is impossible modulo 4; `m=1` fails directly (`3∤5`). This
obstructs a *fixed* cutoff, **not** the required growing cutoff
`(p−1)/6`, and says nothing about unbounded A.

## Deterministic computation and outcome

`Submission/AxisSearch.cpp` uses a segmented Eratosthenes sieve for
`24j+1` and searches the **entire** B range above (stopping early if it
finds a witness). For a B-free prime, it tests `p+k` throughout the
normalized complete A range until a witness is found, enumerating
**every** divisor of each tested shift, including composite divisors.
If neither axis exists, both searches exhaust their full bounds. The
program uses integer arithmetic only: no probable-prime test,
floating-point bound, or probabilistic factorization. Its output in
five runs was:

| Inclusive interval for `p` | Hard primes | No B | Neither A nor B |
|---|---:|---:|---:|
| `[73,100000000000]` | 514742404 | 3 | 0 |
| `[100000000001,300000000000]` | 962540487 | 0 | 0 |
| `[300000000001,542918502385]` | 1135051760 | 0 | 0 |
| `[542918502386,750000000000]` | 952012137 | 0 | 0 |
| `[750000000001,1000000000000]` | 1136621477 | 0 | 0 |

Thus among the `4700968265` hard primes **at most** `10¹²`, B fails
exactly at `p=193,2521,66529`, and these three have the following A
witnesses (the displayed `q` are all composite):

| `p` | `k` | `b` | `q=4kb−1` | `t=(p+k)/q` | Ordered `(x,y,z)` |
|---:|---:|---:|---:|---:|---|
| 193 | 2 | 2 | 15 | 13 | `(52,772,5018)` |
| 2521 | 2 | 11 | 87 | 29 | `(638,55462,804199)` |
| 66529 | 5 | 2 | 39 | 1706 | `(17060,665290,226996948)` |

Each row is prime by deterministic trial division to `⌊√p⌋`, has
`p+k=qt`, and the displayed strict order and fraction identity follow
by the A formula; they were also independently checked with exact
rational numbers. A separate Python divisor enumeration, **not** using
the one-residue-per-`m` shortcut, found precisely these three B-free
primes for `p≤10⁶`. Likewise direct factorization of every required
normalized `p+k` confirmed the previously known nine A-free primes
below `10⁶`, plus five A-free primes between `10⁶` and `10⁷`:

    1134241, 1724209, 1726201, 5212561, 8813281.

These five all have B witnesses, with `(m,d)` respectively
`(2,1), (10,5), (434,31), (22,11), (28,2)`.

The following small *independent* Python audit checks primality by trial
division, exhausts `d|m` for each of the three B-free primes, and verifies
their A identities by rational arithmetic. It does **not** replace the
segmented all-prime search:

```python
from math import isqrt
from fractions import Fraction
for p, k, b, q, t in ((193, 2, 2, 15, 13),
                      (2521, 2, 11, 87, 29),
                      (66529, 5, 2, 39, 1706)):
    assert p % 24 == 1 and all(p % z for z in range(2, isqrt(p) + 1))
    for m in range(1, (p - 1) // 6 + 1):
        h = 4*m - 1
        for d in range(1, isqrt(m) + 1):
            if m % d == 0:
                assert (p + 4*d) % h != 0
                assert (p + 4*(m // d)) % h != 0
    assert q == 4*k*b - 1 and p + k == q*t
    x, y, z = b*k*t, p*b*min(k,t), p*b*max(k,t)
    assert 1 <= x < y < z
    assert Fraction(4,p) == Fraction(1,x) + Fraction(1,y) + Fraction(1,z)
```


To reproduce the entire principal finite check, compile and run (any
segmentation size greater than zero gives the same results):

```sh
g++ -O3 -std=c++17 Submission/AxisSearch.cpp -o /tmp/axis-search
/tmp/axis-search 73 100000000000
/tmp/axis-search 100000000001 300000000000
/tmp/axis-search 300000000001 542918502385
/tmp/axis-search 542918502386 750000000000
/tmp/axis-search 750000000001 1000000000000
```

The split is only to allow bounded runtimes/memory. The search cannot
be extrapolated to primes above `10¹²`; neither a universal theorem nor
a prime missing both axes has been established. Even if a B-free or
A-and-B-free prime is eventually found, it would **not** disprove the
original Erdős–Straus problem: a type-II solution with `a,c>1` or a
type-I solution could remain.
