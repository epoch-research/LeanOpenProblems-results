# Sharp bounds on the *location* of ordered witnesses (not an Erdős–Straus proof)

The unconditional ordered classification in `Classification.lean` and
`CoveringGap.lean` says that a hard prime `p=24k+1` is soluble exactly when
some `x=6k+1+j`, `0≤j<6k`, satisfies Type I or Type II. The following
additional assertions are checked in `HardTypeIISize.lean` and
`HardTypeISize.lean`, without importing or changing `Spec.lean` and without
adding `sorry` or an axiom. **Neither assertion supplies a witness for every
prime.**

## A sharp restriction on Type II

If Type II holds at `x`, take `d|x²`, `0<d<x`, `a=4x-p|x+d`, and set
`m=(x+d)/a`. Primality of `p` and `x<p` imply `gcd(a,x)=1`, so
`gcd(a,d)=1`; since `d|(x+d)²=a²m²`, it follows that `d|m²`. Algebra gives

    (4m−1)x=pm+d,             (4m−1)a=p+4d.

Because `p≡1 (mod 3)`, `m=1` would force `d=1` and `3|p+4`, an
impossibility. Thus `m≥2`. If `m=2`, the first identity and `d|4` give
`7x=2p+d≤2p+4`. If `m=3`, they give `11x=3p+d≤3p+9`, which implies
`7x≤2p+4` for `p≥19`. For `m≥4`, `d<x` gives `(4m−2)x<pm`; since
`7m≤2(4m−2)`, we even get `7x<2p`. Hence **for every hard prime**,

    Type II at x  ==>  7x≤2p+4  ==>  7j<6k.

It follows, rigorously, that the exact conjectural covering condition can
be shortened to

    (∃j<6k: Type I at x_j)  OR  (∃j: 7j<6k and Type II at x_j),
    x_j=6k+1+j.

The Type II range contains exactly `ceil(6k/7)` rather than `6k`
possible indices. This is a logically *equivalent* covering problem, not a
proof that one of its alternatives always holds.

The bound and index cutoff are best possible. For `t≥0`, put

    p=168t+145,    x=48t+42,    a=24t+23,    d=4.

Then `d|x²`, `x+d=2a`, and `7x=2p+4`. Whenever `p` is prime these
are ordered Type II solutions. In fact `gcd(145,168)=1`, so Dirichlet
supplies arbitrarily large prime members of this progression. At
`p=313` (`t=1`, `k=13`, `j=11`, and `7j=6k−1`):

    4/313 = 1/90 + 1/626 + 1/14085.

Thus the last permitted Type II index really occurs, even infinitely
often. Dirichlet here proves **some** primes have witnesses, not that an
arbitrary hard prime does.

## Type I can be arbitrarily near `p/2`

Let `r≡11 (mod 12)`, `r≥11`, and `s≥1`, and put

    p=4r(r+1)s−(2r+1),       n=(2r+1)s−1,       x=rn.

A direct calculation gives `4r(r+1)n=(2r+1)p+1`; hence the **strictly
ordered** identity (provided `p` is prime, indeed even for these
composite `p`) is

    4/p = 1/(r n) + 1/((r+1)n) + 1/(p r(r+1)n).

For the stated residue class of `r`, `p≡1 (mod 24)`. The modulus
`4r(r+1)` is coprime to the residue `−(2r+1)`, since
`(2r+1)²=4r(r+1)+1`. Dirichlet therefore gives infinitely many prime
`p` of this form for every fixed `r`. The first denominator satisfies

    x/p = (2r+1)/(4r+4) + 1/((4r+4)p)
        = 1/2 − (p−1)/((4r+4)p).

Since `r` can be taken arbitrarily large in `11 (mod 12)`, for every
`ε>0` and every threshold `N`, there is a hard prime `p>N` with a
Type I witness `x>(1/2−ε)p` and `x<p/2`. No universal replacement of
`x<p/2` by `x≤(1/2−ε)p` is possible **for all Type I witnesses**.
This does *not* prove that such a prime has no *different*, smaller
first denominator. The congruence condition required for this family is
also not universal: e.g. `p=73` is not of this form for any `r,s≥1`.

This family is genuinely Type I: take `c=r x|x²`; with `a=4x−p`,
`(2r+1)a=4c+1`. For instance `r=23,s=1` gives the prime
`p=2161`, `x=1058`, `c=24334`, and ordered triple
`(1058,1104,54872112)`. The smaller example `p=97,x=34,c=68`
also shows that the sharp Type II bound cannot be asserted *pointwise*
for Type I; `4/97=1/34+1/85+1/16490`.

## Why these bounds do not settle the covering problem

The precise unproved quantifier is **for every** prime `p=24k+1`, find
either a Type I divisor at some `j<6k` or a Type II divisor at some
`7j<6k`. Dirichlet gives infinite *selected* congruence classes, not a
witness for a specified prime; the near-half Type I family and the sharp
Type II family need not include it.

Nor does `τ(x²)>a` force a target divisor residue. For `p=66529` at
the eligible `x=16650`, `a=71`, and `x=2·3²·5²·37`, all prime factors
of `x` are quadratic residues mod `71`. Consequently all `225` divisors
of `x²` are residues, but the Type I target `−4⁻¹=53 (mod 71)` and
Type II target `−x=35 (mod 71)` are nonresidues. **Both fail at this x**
despite `225>71`. The prime is nevertheless soluble at other x, e.g.
`4/66529=1/17060+1/665290+1/226996948`.

Likewise, for every fixed `B`, choosing primes `p≡1` modulo
`24·lcm(1,...,4B)` by Dirichlet rules out **all** Type II modular
parameters `m≤B`: if `d|m²`, then `4m−1∤1+4d`. The proof and the
necessary quantifiers are in `Partial.lean` and `CoveringGap.lean`.
This says nothing about Type I or Type II with growing `m`. There is
no certified counterexample and no complete proof of the still-open
universal divisor cover in these files.
