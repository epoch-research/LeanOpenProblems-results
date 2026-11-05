# Hard Erdős–Straus primes: additional families and a pointwise obstruction

**Scope.** The new constructive statements and the explicit CRT example below
are checked in `ReciprocityFamilies.lean` (which does not import or edit
`Spec.lean`). The general reciprocity and divisor-count arguments below are
ordinary proofs. They do **not** settle Erdős–Straus or exhibit an insoluble
prime. Here `Good(p)` requires **positive, strictly increasing** denominators.

For a prime `p=24k+1`, the already-proved exact criterion in
`Classification.lean`/`CoveringGap.lean` searches precisely
`x_j=6k+1+j`, `0<=j<6k`, with `a_j=4j+3`: either
`c|x_j², c>0, a_j|4c+1` (type I), or
`d|x_j², 0<d<x_j, a_j|x_j+d` (type II). Both branches must fail at *every*
`j` to certify a counterexample. None of the tests below supplies such an
exclusion.

## A balanced, nonconsecutive type-I family

Let `s,r,t>0`, `r<t`, and `p>1` satisfy

    4srt = (r+t)p+1.                                           (1)

Then the following denominators are strictly increasing:

    x=sr,   y=st,   z=psrt,     4/p=1/x+1/y+1/z.             (2)

Indeed `r<t`, `pr>1`, and the numerator on the right, over `psrt`,
is `(r+t)p+1=4srt`. Moreover `c=sr²|x²` (with `x²/c=s`) is a type-I
witness: if `a=4x-p`, then

    (r+t)a=4sr²+1=4c+1.

The identity and `r,t>0` give `p<4x`, while `r<t` and `p>=2` give
`2x<p`. This covers **nonconsecutive** pairs; the prior near-half family
uses `t=r+1`.

A particularly clean choice `(r,t)=(2,13)` is

    p=10920u+10081,     s=1575u+1454,       u>=0.

Here `104s=15p+1`, `p≡1 (mod 840)`, and
`gcd(10081,10920)=1`. Dirichlet's theorem therefore gives infinitely
many hard **prime** values of `p`, each with the explicit ordered type-I
identity (2). This is an infinite selected progression, not a covering
of all hard primes. `balanced_typeI`, `balanced_progression`, and
`infinitely_many_balanced_residual_typeI` check these assertions in Lean.

At `u=11`, `p=130201` is prime and (2) gives

    4/130201 = 1/37558 + 1/244127 + 1/63571159054.          (3)

Here `a=20031`, `c=75116`, and `4c+1=15a`. In fact this specific
first denominator has **no** type-II witness: `x=2·89·211`, all three
factors prime; modulo 11 they are `2,1,2`. Every divisor of `x²` is
therefore `2^e (mod 11)` for `0<=e<=4`, in `{1,2,4,8,5}`. But
`11|a`, `x≡4 (mod 11)`, and type II would need `d≡-x≡7 (mod 11)`.
This does not claim that the prime has no type-II solution at a *different*
first denominator. This example also survives the previously convenient
small tests: `p≡1 (mod 840)`, `p≡5 (mod 11)`,
`(p+3)/4=43·757` (both factors `1 mod 3`), and
`p+4=5·26041` (both factors prime `1 mod 4`). Primality of `p` and
identity (3) are Lean-checked; the factorizations and local exclusion
can also be checked by trial division and the five listed residues.

## Divisors of `p+4d`, `p+t`, `p+4m`, and `4p+1`

For **arbitrary** positive integers `p,m,d`, put `q=4m-1`. If

    q | p+4d,             d | m²,            p>4d,          (4)

then `Good(p)`; primality is not needed. To see why the order condition
is automatic, let `b=(p+4d)/q` and `x=(pm+d)/q`. The latter is integral
because `(p+4d)m=(pm+d)+qd`. Then

    qx=pm+d,       4x=p+b,       x>p/4>d.

The modular-witness calculation gives the ordered denominators
`x, pm, p(mx/d)`; `d|m²` ensures that `mx/d` is integral.
`good_of_shifted_offset` is the Lean proof of (4).

For squarefree `d`, a factor `q≡-1 (mod 4d)` of `p+4d` has
`m=(q+1)/4` divisible by `d`, and thus meets `d|m²`. For nonsquarefree
`d`, only the prime powers `r^ceil(v_r(d)/2)` need divide `m`. For example,

    q≡15 (mod 16),   q | p+32,   p>32

is sufficient with `d=8` and `4|m`; there is **no** requirement that
`8|m`. In particular `(p,q,m,d)=(261241,47,12,8)` gives

    4/261241 = 1/66700 + 1/3134892 + 1/26137162050.      (5)

Here `p` is prime, `p≡1 (mod 840)`, `p≡2 (mod 11)`, its smallest
candidate `(p+3)/4=241·271` has no prime factor `2 (mod 3)`, and
`p+4=5·52249` has no prime factor `3 (mod 4)`; `47|p+32` and `8∤12`.
The even stronger pure modular statement `p>32, p≡15 (mod 47) =>
Good(p)` is Lean-checked. CRT gives the reduced progression
`p≡24361 (mod 39480)`, which is simultaneously `1 (mod 840)` and
`15 (mod 47)`; hence Dirichlet gives infinitely many prime members,
all solved by this `(m,d)=(12,8)` witness. Again, primes outside this
progression are not covered by that argument.

Some useful *equivalences* for a fixed `q=4m-1` explain the apparently
competing shifts:

    q|p+4m       iff  q|p+1;
    q|p+4mb      iff  q|p+b        (b|m);
    q|p+4m²      iff  q|4p+1.

The second case is the `p+t` axis with `t=b`, since `q≡-1 (mod 4b)`;
for `1<=b<p` it yields the ordered identity
`4/p=1/(bwu)+1/(pbw)+1/(pwu)`, where
`q=4bw-1` and `u=(p+b)/q` (sort the last two terms).
The `d=m²` case can require swapping the two factors of `4p+1` to meet
the order condition; the equivalence of divisibilities alone is **not**
a guarantee that a specified large `m` gives an ordered witness.

## Quadratic reciprocity: the needed residue is smaller than the sign class

Let `p≡1 (mod 4)` be prime. A type-II modular witness `q=4m-1|p+4d`,
`d|m²`, has Jacobi `(d/q)=+1`: for each odd prime `r|m`, reciprocity and
`q≡-1 (mod r)`, `q≡3 (mod 4)` give
`(r/q)=(-1/r)(q/r)=+1`; for `r=2`, `q≡7 (mod 8)` gives `(2/q)=+1`.
Thus `(p/q)=(-4d/q)=-1`, and reciprocity gives the **Legendre**
`(q/p)=-1`, even when `q` is composite. The same necessary sign holds
for the shifted `p+t` test: if `q|p+t`, `q≡-1 (mod 4t)` and `t<p`,
then `(t/q)=+1`, so `(q/p)=(p/q)=(-t/q)=-1`.

However the sign is far from enough. For **every prime** `q=4m-1>=11`
(`m>=3`) the allowed residues

    A_q={-4d (mod q) : d|m²}

are *strictly fewer* than all the quadratic nonresidues modulo `q`.
Indeed there are `(q-1)/2=2m-1` nonresidues; pairing divisors of `m²`
across `m` shows `tau(m²)<=2m-3`: among `1,...,m-1`, at least
`m-1` itself does not divide `m²` (as `gcd(m-1,m)=1`, `m>=3`). Hence
**at least two nonresidue classes** modulo every such `q` are missed by
*all* `d|m²`. For `q=11`, `m=3`, the allowed classes are `{7,8,10}`;
the missing nonresidues are `{2,6}`. The Lean theorem
`no_m3_if_two_or_six_mod11` excludes all divisors in that case.

More strongly, choose **any finite collection** of distinct primes
`q_i≡3 (mod 4)`, `q_i>=11`, and for each choose a missing
nonresidue `a_i∉A_{q_i}`. CRT and Dirichlet give infinitely many hard
primes

    p≡1 (mod 840),            p≡a_i (mod q_i) for all i.

All the Legendre signs `(q_i/p)=-1` are correct, but **none** of the
corresponding `m_i=(q_i+1)/4` has a modular witness. Taking `q_1=11`,
`a_1=2`, makes the least quadratic nonresidue of these primes equal to
**11** (2,3,5,7 are residues by `p≡1 mod 840`). The infinite `q=11`
subcase, `p≡2521 (mod 9240)`, is proved in Lean by
`infinitely_many_hard_two_mod11_without_m3`. This construction excludes
only the *listed parameters*; it does not exclude other `m` or Type I.

The same argument refutes the strategy **"take the least nonresidue and
use its corresponding `m`" for every prime `q≡3 (mod 4)`, `q>=11`**,
not merely for `q=11`. Select a missing nonresidue `a (mod q)`, and
apply CRT/Dirichlet to primes with `p≡a (mod q)` and `p≡1 (mod 8)`
and `p≡1` modulo *every* prime `r<q` (including 3). All these
congruences are compatible and reduced; such `p` are hard primes.
Quadratic reciprocity gives `(r/p)=+1` for all primes `r<q`, whereas
`(q/p)=(p/q)=-1`. Hence **the least quadratic nonresidue of `p` is
exactly `q`**, but `q∤p+4d` for every `d|((q+1)/4)²`. This is an
infinite family for *each fixed `q`*, not a counterexample to the
conjecture: other `m` and Type I remain unrestricted. If the least
nonresidue instead has residue `1 (mod 4)`, it is not even of the form
`4m-1`, so the direct least-nonresidue-as-modulus proposal cannot start.

Conversely, for any prescribed `T`, Dirichlet also supplies arbitrarily
large primes `p≡1` modulo `840` times every odd prime `<=T`. Reciprocity
and `p≡1 (mod 8)` make **every** integer `1<=n<=T` a quadratic residue
modulo `p`; the least nonresidue exceeds `T`. For those primes a type-II
witness must have `4m-1>T`, and every eligible divisor of a shifted
`p+t` or shifted-product family (below) must exceed `T`. This is a
uniform obstruction to *fixed small-modulus* strategies, not to
parameters that grow with `p`.

## Shifted-product divisors and an automatic strict split

The existing canonical type-II parameterization suggests a single
factorization test. For `v,w>0`, set

    M=4vw,       N=4v²wp+1= Mvp+1.

If `q|N`, `q≡-1 (mod M)`, its cofactor `h=N/q` is **also**
`-1 (mod M)` (because their product is `1 mod M`). Write
`q=Mr-1`, `h=Ms-1`. Expansion gives

    vp=4vwrs-r-s,

so `v|r+s`, `a=(r+s)/v`, `p=4wrs-a` and

    4/p=1/(wrs)+1/(pvwr)+1/(pvws).                          (6)

For `r<s` this is strictly ordered: `a<=r+s<2rs<=2wrs`, so
`p>2wrs`, and consequently `wrs<pvwr<pvws`.

The condition `q<h` in the earlier factor criterion can actually be
dropped **when `p≡1 (mod 4)` is prime**: if `q>h`, swap the factors;
if `q=h`, then `r=s`. In that case `a=2r/v` is an odd integer
`3 (mod 4)` because `p=4wr²-a≡1 (mod 4)`. Thus `a|r`, since
`a|2r` and `a` is odd. Consequently `a|p`, although
`1<a<4wr²-a=p` (`r>=a>=3`), contradicting primality.
The unit divisors `1,N` cannot be `-1 (mod M)` since `M>=4` and
`N≡1 (mod M)`. Thus **any** eligible divisor gives a strict split
*for these primes*. Primality matters: for the composite
`n=1441=11·131≡1 (mod 24)` and `(v,w)=(2,3)`, one has
`4v²wn+1=263²` with `263≡-1 (mod 24)`; the factors correspond to
`r=s=11`, so this split has two equal final denominators. It does not
say that `n` itself is insoluble. The prime-only simplification does not
manufacture an eligible divisor.

There is a second reciprocity check: **every** eligible (possibly
composite) `q|N`, `q≡-1 (mod M)` has `(q/p)=-1`. Indeed `q` is coprime
to `vw`, `(w/q)=+1` by the same prime-factor reciprocity as above,
and `4v²wp≡-1 (mod q)`. Hence `(p/q)=(-w/q)=-1`, followed by
reciprocity for `p≡1 (mod 4)`. Knowing only that some factor of `N`
is a nonresidue mod `p` does not establish that it equals `-1 mod M`;
the exact factor congruence remains the pointwise obstacle.

## Remaining gap

The families are genuinely infinite and cover primes missed by several
small tests, but **CRT constructs selected primes**, not witnesses for an
arbitrary prescribed hard prime. The divisor-count argument constructs
primes on which arbitrarily many *chosen* reciprocity signs fail to
produce the desired divisor; it does not rule out the unchosen
parameters or type I. No prime has been proved to exclude both exact
criteria for every `p/4<x<p/2`, and no universal divisor forcing theorem
is obtained from least nonresidues, character sums, or these products.
The conjectural pointwise covering remains open.
