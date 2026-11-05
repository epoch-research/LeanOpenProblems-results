# Exact small-shift Type-II restrictions; no universal hard-prime cover

**Status:** These are conditional constructions and exclusions, **not** an
Erdős–Straus proof or a bad prime. The new universal arithmetic lemmas,
the exact `p+2` and `p+3` subfamily equivalences, and numerical full-axis
witnesses are proved without `sorry` in `SmallShiftRigidity.lean`.
`SmallShiftRigidityAudit.py` independently checks factorization, primality,
all displayed rational identities, and the stated finite shift-fiber scans.
Neither file imports or edits `Spec.lean`.

Write `p=24k+1`, `h=4m−1`, `m,d>0`, `d∣m²`, `4d<p`. A Type-II witness has
`h∣p+4d`; if additionally `h∣p+r`, then `h∣4d−r`. If `h∣p−r`, then
`h∣r+4d`. The **additional factor test must not be mistaken for the full
Type-II criterion**: its modulus may depend on `p`, and witnesses outside a
chosen list of shifts are still available.

## Rigidity for `p+1`, `p+2`, `p+3`

**Lemma (fully general, without primality).** If `1≤r≤3`, `m,d>0`,
`d∣m²`, and `4m−1∣4d−r`, then **necessarily**

    d=rm,                 r∣m.                              (1)

For a proof put `e=m²/d`, `h=4m−1`. Since `4d−r>0`, write
`4d−r=t h`. Reducing modulo four gives `t≡r (mod 4)`; hence `t≥r`
and `4d≥r(h+1)=4rm`, so `d≥rm`. The exact identity
`16m²=h(4m+1)+1` also gives `h∣4re−1`. This positive number is at
least `h`, so `re≥m`. Thus

    m²=de≥(rm)(m/r)=m²;

both inequalities must be equalities. Consequently `d=rm` and `re=m`,
proving (1). The crucial positivity `4d−r>0` fails beginning with
`r=4`: there `d=1` gives `4d−r=0` for **every** `m`. In Lean the
universal statement is `short_positive_shift_rigid`; the version
allowing both factor divisibilities is `short_shift_only_canonical`.

**Exact shift classification for hard `p`.** Conversely, if `r∣m` and
`h∣p+r`, then `d=rm∣m²` and
`p+4d=(p+r)+rh`. The remaining inequality `4rm<p` is **automatic**
for each of `r=1,2,3`, not an extra unverified size assumption:

| `r` | required divisor `h∣p+r` | `m=(h+1)/4`, `d=rm` | `q=(p+r)/h` | `p−4d=(q−r)h−2r` |
|---:|---|---|---|---|
| 1 | `h≡3 (mod 4)` | any `m≥1` | `q≡2 (mod 4)`, `q≥2` | at least `h−2>0` |
| 2 | `h≡7 (mod 8)` | even `m≥2` | `q≡5 (mod 8)`, `q≥5` | at least `3h−4>0` |
| 3 | `h≡11 (mod 12)` | `3∣m`, `m≥3` | `q≡0 (mod 4)`, `q≥4` | at least `h−6>0` |

In particular, **noncanonical divisors of `m²` cannot repair any of
these three factor tests**. The exact `r=2,3` equivalences, including
the size bounds, are `plus_two_shift_exact` and `plus_three_shift_exact`
in Lean. A suitable `h` yields strictly ordered denominators via
`good_of_plus_two_seven_mod_eight_divisor` (or the analogous full-axis
construction for `r=3`). For `r=4`, *any* `h≡3 (mod 4)` dividing
`p+4` works with `d=1`; such a factor is not forced, e.g. the factors
of `66529+4=66533` and `2784961+4=5·293·1901` are all `1 (mod 4)`.

### What the forced factor of `p+2` actually says

`p+2=3(8k+1)` always has the factor `3≡3 (mod 8)`. It does **not**
force a `7 (mod 8)` divisor: the exact criterion above is

    a Type-II witness using a modulus h∣p+2
      ⇔ some divisor h∣p+2 is 7 (mod 8)
      ⇔ p+2 has a prime factor 5 or 7 (mod 8).               (2)

For the last equivalence, a prime factor `7 (mod 8)` serves as `h`; if
`q≡5 (mod 8)` is a prime factor, `(p+2)/q≡3·5≡7 (mod 8)` serves
as `h`. Conversely, if all prime factors are `1` or `3 (mod 8)`,
every divisor is `1` or `3 (mod 8)`. **A `5 (mod 8)` prime factor is
sufficient but not necessary**: the prime `1321` has
`1321+2=3³·7²`; `h=7`, `m=2`, `d=4` works.

| hard prime `p` | prime factorization of `p+2` | `p+2` factor witness `(h,m,d)` |
|---:|---|---|
| 193 | `3·5·13` | `(15,4,8)` |
| 2521 | `3·29²` | `(87,22,44)` |
| 18481 | `3·61·101` | `(183,46,92)` |
| 1321 | `3³·7²` | `(7,2,4)` |
| 66529 | `3·67·331` (all `3 mod 8`) | **none**, by (2) |
| 2784961 | `3·19·48859` (all `3 mod 8`) | **none**, by (2) |
| 12721 | `3·4241` (`4241≡1 mod 8`) | **none**, by (2) |

All listed factors and primes are trial-division-checked by the audit;
`additional_full_square_witnesses` kernel-checks the `18481` and
`1321` full-axis examples. The last three rows are **not** assertions
that those primes lack Type-II witnesses elsewhere. In particular the
forced `3` factor cannot be salvaged by some exotic `d∣m²`, by (1).
The `p+3` factor strategy similarly needs an `11 (mod 12)` divisor of
`(p+3)/4=6k+1`; for example `p=457`, `h=23`, `m=6`, `d=18` works,
whereas none is forced for all hard primes.

## Complementary factors and the residue-class gap

For every `d∣m²`, `gcd(d,h)=1` and the Jacobi symbol `(d/h)=+1`.
Thus a genuine modular witness has `(p/h)=(-4d/h)=−1`. If `h∣p+r`,
then `(r/h)=+1` is **necessary**; if `h∣p−r`, then `(r/h)=−1` is
necessary. These sign conditions are not sufficient for the exact
divisor residue; for instance `p=409`, `m=3`, `h=11` has the
permitted `(p/11)=(2/11)=−1` but `d∣9` gives only the residues
`−4d≡7,8,10 (mod 11)`, never `2`. That prime works elsewhere.

* **`p−s²`, for any integer `s`:** impossible as a Type-II modulus.
  Indeed `p≡s² (mod h)` would make `(p/h)` a square symbol `+1`
  (the witness ensures coprimality), contradicting `−1`. This covers
  the apparently useful forced factors of `p−1`, `p−4`, `p−9`, etc.
* **`p−2`:** no full `d∣m²` witness at its factor modulus. The
  stronger elementary result `MinusTwoBarrier.no_two_modular_divisor`
  proves `h∤2+4d` for all `m≥2`; `m=1,h=3` does not divide `p−2`
  since `p≡1 (mod 3)`. Thus the forced `3 (mod 4)` prime factor of
  `p−2≡3 (mod 4)` does not furnish this Type-II certificate.
* **`p−3`:** the only possible pair is `(m,d)=(2,1)`, `h=7`.
  To see this put `e=m²/d`, `t=(3+4d)/h`. Then `t≡1 (mod 4)`;
  the dual divisibility `h∣12e+1` has quotient `3 (mod 4)`, so
  `e≥m`. If `t≥5`, then `d≥5m−2>m`, contradicting `de=m²`.
  If `t=1`, then `d=m−1∣m²`, hence `d∣1` and `(m,d)=(2,1)`.
  This is proved in Lean by `minus_three_only_m2_d1` and
  `hard_minus_three_fiber`. The sole option requires `7∣p−3`,
  equivalently `7∣p+4`, already covered by the `r=4,d=1` test.

Thus the most obvious **forced** factors on the negative side provide
no complementary universal coverage of the failed `p+2` condition.
This is a restriction on *these exact Type-II factor moduli*, **not**
a proof that an unrelated Type-I certificate or another Type-II modulus
cannot work.

## Other shifts work pointwise, but do not force a theorem

For `p=66529`, where all four factor tests `p+1,…,p+4` fail, the
*next* shift gives `39∣p+5`, `m=10`, `d=50=5m∣m²` and `4d=200<p`.
For `p=2784961` a complete check of **all** factors `h∣p+r` and
**all** divisors `d∣m²` finds no witness for `1≤r≤15`, but
`767∣p+16` with `(m,d)=(192,4)` does work. A much smaller full
parameter is `(m,d,h)=(12,6,47)` with `47∣p+24`; here `d=6∣m²`
is *not* of the `d=rm` form for `r=24`.

The general ordered construction is explicit: with
`a=(p+4d)/h` and `x=(p+a)/4`, a valid witness gives

    4/p = 1/x + 1/(pm) + 1/(pmx/d),     x<pm<pmx/d.

For example the last two primes have, respectively, the exactly
verified triples

    66529:   (17060, 665290, 226996948),
    2784961: (711054, 33419532, 3960515317788).

The audit uses `fractions.Fraction` rather than floating-point
approximations. None of these examples supplies a **forced** factor
at the needed congruence for an arbitrary prescribed hard prime.

## Exact remaining pointwise obligation

For *each* prime `p=24k+1`, an ordered proof still needs **either**
`m,d>0`, `m≤(p−1)/6`, `d∣m²`, `4d<p`, `4m−1∣p+4d`, with **no
preassigned shift**, **or** a full Type-I witness at some
`x=6k+1+j`, `0≤j<6k`, namely `c>0`, `c∣x²`,
`4j+3∣4c+1`. The exact equivalence is in `TypeIIOffsetBound.lean`
and `CoveringGap.lean`. A proof for **every** hard prime of the first
alternative alone would be stronger than necessary. An alleged bad
prime instead needs proof that **both** alternatives fail everywhere.
The shift results, the Jacobi signs, any finite checking, and density
arguments provide neither global assertion. **`Spec.lean` is unchanged.**

Verification: `lake env lean Submission/SmallShiftRigidity.lean`,
`lake build Submission.SmallShiftRigidity`, and
`python3 Submission/SmallShiftRigidityAudit.py` succeed; the four
new universal shift lemmas and the two subfamily equivalences are
kernel-checked, while all finite scans are identified as such.
