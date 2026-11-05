# A nonsquare-3 norm coordinate and a ray-condition on `p²+4q`

**Status:** conditional ordered constructions and explicit counterexamples to the proposed *norm-to-factor* implication, **not** a proof or disproof of the Erdős–Straus conjecture. The mathematics below is an ordinary proof, not a newly formalized Lean theorem. `Spec.lean` is untouched. `QuadraticSlackRayAudit.py` independently checks every displayed finite prime, factorization, congruence and rational identity using Python's standard library.

## The exact, small-prime-slack factor test

Let `p≡1 (mod 4)` be a prime and `q<p` an odd prime. Put `N=p²+4q`. Suppose there is a **positive integer** `a` such that

    a<p,           a|N,           4q|(p+a).                  (R)

Define

    b=N/a,    t=(p+a)/(4q),    x=qt=(p+a)/4,
    y=(p+b)/4,                     z=pty.                     (1)

All three denominators are integers: `t≥1` by (R); `a≡−p≡3 (mod 4)`; `N≡1 (mod 4)` then forces `b≡3 (mod 4)`, since `3b≡1 (mod 4)`. Thus `y` is integral. Moreover `a<p` and `ab=p²+4q>p²` imply `b>p>a`. Consequently `p<4x=p+a<2p`, `0<x<y`, and `z=pty>y` since `pt>1`. In particular **none** of integrality, the upper bound on `x`, or the last strict order is merely assumed.

Expanding `(4x−p)(4y−p)=ab=p²+4q` gives

    4xy=p(x+y)+q.                                           (2)

As `q|x`, the last denominator is also `z=pxy/q`, and (2) yields the exact identity

    1/x+1/y+1/z = [p(x+y)+q]/(pxy) = 4/p.                 (3)

This is a **full Type-I** certificate. Indeed `c=x²/q=qt²>0` divides `x²`, and `a=4x−p` divides `4c+1`: modulo `a`, `p≡4qt`, so

    0≡p²+4q≡4q(4qt²+1) (mod a).

Here `gcd(a,4q)=1`: `a` is odd and, if `q|a`, then `q|ab=p²+4q` would imply `q|p`, contrary to `q<p` and primality. Cancel `4q` to obtain `a|4c+1`. Crucially `c` need not divide `x`.

The residue in (R) is **also necessary for the exact slack `q` factor method**, rather than an optional strengthening. If `0<a<p`, `ab=N` and `a≡b≡3 (mod 4)`, set `x=(p+a)/4`, `y=(p+b)/4`. Since `ab≡p² (mod q)` and `q∤p`, `q|y` implies `b≡−p (mod q)`, hence `a≡−p (mod q)` and `q|x`. Thus

    q|xy  ⇔  q|x  ⇔  4q|(p+a).                             (4)

The last equivalence uses the integer equality `p+a=4x`, not a cancellation of 4 modulo `4q`. It follows that factorization of `N` into two `3 (mod 4)` factors by itself is insufficient; the **particular ray residue** modulo `4q` must be hit. This is the prime-`A=q` specialization of the positive-slack viewpoint in `SlackFactor.lean`, strengthened by the exact (4) and automatic strict ordering; it asserts no existence of `a` for arbitrary primes.

## What the quadratic form supplies, and what it does not

Assume further that `p=u²+3v²`, `u,v>0`, and that `q|u` with `q≡5` or `7 (mod 12)`. Then `q≤u<√p<p`, and `q∤v`, since otherwise `q|p`. Quadratic reciprocity (the sign is positive because `p≡1 (mod 4)`) gives

    (q/p)=(p/q)=(3v²/q)=(3/q)=−1.                         (5)

Thus this **non-axis** quadratic-form coordinate actually produces the nonresidue sign required of a Type-I slack `A=q`; Gaussian/Eisenstein unit axes need not have this property. Here `q` has `(3/q)=−1` (inert in the *real* field `ℚ(√3)`), which must not be confused with inertness in the imaginary field `ℚ(√−3)`: for example, `q=7` is split in the latter. More explicitly, `p≡3v² (mod q)`, so the congruence in (R) is the *simultaneous* requirement `a≡3 (mod 4)` and `a≡−3v² (mod q)` (equivalent by the Chinese remainder theorem, since `q` is odd). But (5) puts **no** factor of `p²+4q` into this exact class. In particular the factor test is a valid conditional route from a binary quadratic form to a complete ordered Type-I witness, not a universal theorem or an ideal-class-group descent.

## A nontrivial success, and two independent failures

* **Success, requiring the full `c|x²` branch:** `1249=7²+3·20²` is a prime `1 (mod 24)`; take `q=7`. One has

      p²+4q=1560029=739·2111,      1249+739=28·71.

  Condition (R) holds with `a=739`, `b=2111` and `t=71`. Formula (1) yields the **strictly ordered** identity

      4/1249 = 1/497 + 1/840 + 1/74490360.

  Here `x=497=7·71`, `c=7·71²=35287>x`, `x²=7c`, and
  `4c+1=141149=739·191`. In the exact hard-prime indexing of
  `CoveringGap.lean`, `p=24·52+1`, `x=6·52+1+184`, `184<6·52`,
  `a=4·184+3`. The initial eligible denominator `x₀=313` fails both
  types: `313` is prime `1 (mod 3)`, so all divisors of `313²` are
  `1 (mod 3)`, while both targets modulo `a₀=3` require `2 (mod 3)`.
  Type II **fails at this particular `x=497`**: a divisor
  `0<d<497` with `739|497+d` would have to be `d=242`, which does not
  divide the odd number `497²`. No divisor of `x` meets the Type-I target
  either (`x` has divisors `1,7,71,497`), so this certificate genuinely
  uses a cofactor dividing `x²` but **not** `x`. The naive alternative
  `c=q=7` is impossible at *any* hard prime, since `4q+1=29` has no
  divisor `3 (mod 4)`; the complementary-slack construction bypasses it.

* **No proper factor, despite the nonresidue:** `97=7²+3·4²` is prime,
  with `q=7`, `(7/97)=−1`, yet `p²+4q=9437` is **prime** and
  `9437≡1 (mod 4)`. There is no factor `0<a<97` in (R), so this
  norm-coordinate choice `A=7` fails. The original conjecture does **not**
  fail: `4/97=1/25+1/970+1/4850` is strictly ordered and exact.

* **Factorization but wrong ray residue:** `73=5²+3·4²` is prime, with
  `q=5`, `(5/73)=−1`, and `p²+4q=5349=3·1783` (both factors prime
  `3 (mod 4)`). The **only** smaller factor `a<73` that is `3 (mod 4)`
  is `a=3`, but `p+a=76` is **not** divisible by `4q=20`. Its apparent
  `(x,y)=(19,464)` has `xy=8816≡1 (mod 5)`, so `pxy/5` is not an
  integer. Again the prime is soluble: `4/73=1/20+1/220+1/4015`.

The computational audit checks primality by complete trial division (in particular `9437` and `1783`), enumerates *all* eligible factors for these three `N`, and checks the ordered equalities with exact `Fraction` arithmetic. No result is extrapolated from those finitely many checks.

**Remaining gap.** Even existence of a `q|u` with `(3/q)=−1` is not automatic: `193=1²+3·8²` has **only** the positive representation `(u,v)=(1,8)` (`v` must be even and `v≤8`; only `v=8` leaves a square). The examples `73` and `97` demonstrate independently that such a `q`, when available, does not force (R). Other slack values and Type II remain available. Obtaining (R) for some suitable `q`, or otherwise hitting either exact divisor class at some `j` for **every** hard prime, is the still-open pointwise covering in `CoveringGap.lean`; none of the displayed local failures is an Erdős–Straus counterexample.
