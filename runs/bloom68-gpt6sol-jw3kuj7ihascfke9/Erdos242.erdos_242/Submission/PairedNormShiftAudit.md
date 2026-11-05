# A paired-Gaussian/48B-norm shift fails even with both full divisor tests

**Status:** This is an elementary proof and a reproducible finite audit of a
*specified candidate family*, not a proof or disproof of Erdős–Straus.
`Submission/Spec.lean` is neither imported nor edited. The script
`python3 Submission/PairedNormShiftAudit.py` performs deterministic trial
division for every claimed prime and checks the exact displayed rational
identities. Earlier Lean files (`Classification.lean`, `NormShiftDescent.lean`)
prove the full ordered Type-I/II construction and most of the four stress
prime witnesses; the new finite exclusions below are ordinary proofs.

For a prime `p=24k+1`, an eligible first denominator has `p/4<x<p/2`.
Write `a=4x−p`. The **complete**, ordered classification requires one of

* Type I: `c>0`, `c|x²`, `a|4c+1`;
* Type II: `0<d<x`, `d|x²`, `a|x+d`.

Replacing `c|x²` by `c|x`, or dropping Type II in a proposed counterexample,
is not valid.

## What the `t=4B−1` identity actually forces

Suppose `p=A²+48B²=24k+1`, with `B≥1`. Take

    t=4B−1,       c=3B−1,       x=(p+t)/4=6k+B.

The following are **polynomial identities for every** such `A,B`:

    4x−p=t,       4c+1=3t,
    12x=3A²+17+(3B−1)(48B+20).                       (1)

The first denominator is eligible: `0<t<p`, since
`p≥48B²+1>4B−1`, and `x=(p+t)/4`. But (1) does **not** imply
`c|x²`. If `B` is odd, then `x` is odd and `c` is even, so `c∤x²`.
If `B` is even, `c` is coprime to 12 and (1) instead gives the exact test

    c|x²    ⟺    c|(3A²+17)².                           (2)

For squarefree `c`, equivalently `c|3A²+17`. This extra arithmetic
congruence is not a consequence of primality or either norm. In particular,
`B=8,A=17` gives `p=3361`, `c=23`, `x=848` and
`848²≡9 (mod 23)`; even the **full** Type I and II fail at this x.
By contrast, the factors `5|3·1²+17` at `p=193` and
`41|3·239²+17` at `p=66529` are **individual factor coincidences**,
not polynomial identities forcing a solution for every representation.

## The norms `p+1` and `p+4` do not force a missing nonresidue

Suppose additionally every odd prime factor of both `p+1` and `p+4` is
`1 (mod 4)` (so both integers are Gaussian norms). For an odd factor
`r|p+1`, `p≡−1 (mod r)`; for `r|p+4`, `p≡−4 (mod r)`.
Quadratic reciprocity for `p≡1 (mod 4)` gives `(r/p)=+1` in either case.
For `r=2`, `(2/p)=+1` since `p≡1 (mod 8)`. Likewise all primes dividing
the Gaussian-coordinate product `uv` in `p=u²+v²` have symbol `+1`:
modulo a factor of one coordinate, `p` is the nonzero square of the other.
The already-proved **full** Jacobi obstruction in `PointwiseJacobi.lean`
requires a nonresidue prime dividing any successful eligible `x`.
Thus denominators supported on prime factors of `uv(p+1)(p+4)` cannot work.
This says nothing analogous about the *coordinates* of a Gaussian norm of
`p+1` or `p+4`: modulo a factor of one such coordinate, `p` is the other
coordinate's square **minus 1 or 4**. Those coordinates may contain
nonresidues, but their presence does not force either exact divisor target.

## A counterexample to a concrete set of norm-derived first denominators

The new small prime `p=3361` has **all** the proposed simultaneous data:

    3361=15²+56²=17²+48·8²,
    3362=2·41²=31²+49²=41²+41²,
    3365=5·673=1²+58²=34²+47².

`41` and `673` are primes `1 (mod 4)`; `3361` is prime (trial division
by `2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53` suffices, since
`⌊√3361⌋=57`). The finite script verifies these primalities independently.
The Gaussian representations listed above exhaust all **positive**
coordinate pairs up to signs/order: check `1≤r≤⌊√(n/2)⌋` and whether
`n−r²` is a square for `n=3361,3362,3365`.

Precisely define the candidate set to be the eligible products `rs` of
**every** Gaussian coordinate pair `p+e=r²+s²`, `e∈{0,1,4}`, plus the
48B-shift `x=(p+4B−1)/4`. At `p=3361`, the products from the three norms
are `840` (too small), `1519` (eligible), `1681` (too large), `58` (too
small), `1598` (eligible); the 48B shift contributes `848`. **Every one of
the three eligible denominators `848,1519,1598` fails both full types:**

* `x=848=2⁴·53`, `a=31`. The residues modulo 31 of all
  `c|x²=2⁸·53²` are
  `{1,2,4,8,16} ∪ {22,13,26,21,11} ∪ {19,7,14,28,25}`
  (the rows correspond to exponent `0,1,2` of `53`). Type I requires
  `c≡−4⁻¹≡23 (mod 31)`; Type II requires `d≡−x≡20 (mod 31)`.
  Neither is in the list, even without the Type-II bound `d<x`.
* `x=1519=7²·31`, `a=2715`, which is divisible by 3. Each divisor
  of `x²` is `1 (mod 3)`, as is `x`, but each full type would require
  a divisor `2 (mod 3)`.
* `x=1598=2·17·47`, `a=3031=7·433`. Both types require their chosen
  divisor to be `5 (mod 7)`. Among **all** divisors of
  `x²=2²·17²·47²`, the only possibilities are
  `47,68,37553,54332`. Their respective residues `4c+1 (mod 433)`
  are `189,273,395,396`, so none gives Type I. For Type II only `47,68`
  are `<1598`, and `1598+d (mod 433)` is respectively `346,367`,
  never zero.

This does **not** make `3361` insoluble: taking `x=841=29²`, `a=3`,
`d=29|x²`, `3|841+29`, gives the strictly ordered exact identity

    4/3361 = 1/841 + 1/974690 + 1/28266010.

Thus even simultaneous Gaussian norms of `p`, `p+1`, `p+4` and a 48B norm
do **not** force Type I or Type II at any of these explicitly defined,
norm-related candidate shifts. Other shifts can and do work.

## Four required stress primes

All four primes also satisfy the extra absence-of-`3 (mod 4)`-factor
assumption for `p+1,p+4`. Their 48B-shifts give:

| prime `p=u²+v²=A²+48B²` | `p+1`, `p+4` factorizations | `t`, `x`, `c` | `c|x²`? | full I / II at `x` |
|---|---|---|---|---|
| `193=7²+12²=1²+48·2²` | `2·97`, `197` | `(7,50,5)` | yes | both |
| `2521=35²+36²=13²+48·7²` | `2·13·97`, `5²·101` | `(27,637,20)` | no | neither |
| `66529=55²+252²=239²+48·14²` | `2·5·6653`, `66533` | `(55,16646,41)` | yes | both |
| `8803369=1360²+2637²=2251²+48·279²` | `2·5·880337`, `37·237929` | `(1115,2201121,836)` | no | neither |

The independent all-divisor script also enumerates **every** Gaussian
representation of each of these four `p,p+1,p+4`. Among their eligible
coordinate products, **both full types fail at every one**:

| `p` | eligible Gaussian-coordinate products with neither type |
|---|---|
| `193` | `65,84` |
| `2521` | `1118,1189,1258,1260` |
| `66529` | `23183,29393` |
| `8803369` | `2277826,3586320,4401523` |

This is a finite check of this specifically defined candidate set, **not**
a theorem about other norm-related first denominators. The B-shift works at
`193,66529`, but it fails along with every eligible Gaussian-coordinate
product at `2521,8803369`; the additional `3361` counterexample above
has the same joint failure with **even** `B`.

In particular `637=7²·13` has **only** factors `1 (mod 3)`, while its
modulus `27` is divisible by 3: neither full type can work at `637`.
For the larger case, `2201121=3³·13·6271`, with `6271` prime, and
`1115=5·223`. Modulo `223`, every divisor of `2201121²` has the form
`3^e·13^j` for `0≤e≤12`, `0≤j≤2` because `6271≡27=3³`.
The powers `3^e (mod 223)` are
`{1,3,9,27,81,20,60,180,94,59,177,85,32}`.
Type I demands `c≡167 (mod 223)`; Type II demands `d≡112 (mod 223)`.
After dividing either target by `13^j`, for `j=0,1,2` the three residues
are respectively `{167,30,191}` and `{112,163,64}`, disjoint from the
powers of 3. This excludes **all** divisors for both types, even if the
Type-II size restriction is discarded. `223` and `6271` are prime by
trial division to `⌊√223⌋=14`, `⌊√6271⌋=79`.

Nevertheless, strictly ordered decompositions exist: the two good B-shift
triples are `(50,1450,27985)` for `193` and
`(16646,20258182,3319597513)` for `66529`. At different shifts
`2521` works with Type II `(x,d)=(636,8)` and ordered triple
`(636,70588,5611746)`, and `8803369` works with Type II
`(x,d)=(2200869,121)` and triple
`(2200869,181085300330,3293760527702370)`. The separate audit checks
all four fraction identities, the exact full divisibilities, strict order,
and primality by exhaustive trial division up to the respective integer
square roots (`13,50,257,2967`). Existing `NormShiftDescent.lean` also
formally proves primality of `8803369` and its Type-II witness.

**Logical limit:** The all-prime quantifier over *every eligible first
denominator* is not covered here. This excludes a concrete norm-based
candidate set, not every possible norm identity, and is not a
counterexample to the conjecture in `Spec.lean`.
