# Quadratic norms in the remaining Erdős–Straus prime class

This is an **ordinary mathematical analysis, not a proof or disproof of
Erdős–Straus**. It does not change `Spec.lean`. All the displayed Egyptian
fraction examples have positive **strictly increasing** denominators.

## What the three representations really say

**Theorem.** For a prime `p > 3`, each of the following assertions is
equivalent to `p ≡ 1 (mod 24)` (the pairs `u,v` are *different* for the three
representations):

    p = u_24² + 24 v_24²,
    p = u_48² + 48 v_48²,
    p = u_72² + 72 v_72²,            with v_K > 0.

For the easy direction, every coefficient `K` is divisible by 24. If a prime
`p > 3` equals `u² + K v²`, then `u` is odd and is not divisible by 3.
Consequently `u² ≡ 1 (mod 24)` and so `p ≡ 1 (mod 24)`.

Here is one rigorous class-group explanation of the converse. The imaginary
quadratic fields with radicands `-2` and `-3` have class number one; the
Minkowski bound `2 sqrt(|D|)/π` is less than 2 for their discriminants `-8`
and `-3`. A prime `p ≡ 1 (mod 8)` splits in `Q(sqrt(-2))`, so
`p=s²+2t²`. Reduction modulo 8 makes `t` even, and reduction modulo 3
using `p ≡ 1 (mod 3)` makes `3 | t`; writing `t=6v` gives the `72`
representation. Similarly `p ≡ 1 (mod 3)` splits in `Q(sqrt(-3))`.
The norm form on its maximal order is `a²-ab+b²`. Multiplying a generator
of norm `p` by one of the six units makes it congruent to `1 (mod 2)`:
`O/2O ≅ F₄`, and the units reduce onto `F₄×`. It therefore belongs to
`Z[sqrt(-3)]` and has norm `p=s²+3t²`. Modulo 8, `s` must be odd and
`4 | t`; writing `t=4v` gives the `48` representation.

For `Q(sqrt(-6))`, the discriminant is `-24` and the Minkowski bound is
less than 4. Its only possible nontrivial ideal classes are represented by
the primes above 2 and 3. Both ramify, and their product is
`(sqrt(-6))`; hence the class number is two (the prime above 2 is not
principal, since `s²+6t²=2` has no integral solution). Since
`(-6/p)=1` for `p ≡ 1 (mod 24)`, `p` splits. If an ideal of norm `p`
were nonprincipal, multiplying it by the ideal of norm 2 would give an
element of norm `2p`, hence `p=2s²+3t²`. This is impossible modulo 3:
the right side is `0` or `2`, while `p ≡ 1`. Thus that ideal is principal
and `p=s²+6t²`. Reduction modulo 8 forces `t` even, giving
`p=s²+24v²`. Each `v` is nonzero, since a prime is not an integer square.

These existence statements are thus **not three extra congruence
restrictions** beyond `p ≡ 1 (mod 24)`. In particular one must not
identify the three `u`'s: a common `u` in the `24` and `48`
representations would give `v_24²=2v_48²`, which has no nonzero
integral solutions. For instance

    2521 = 11² + 24·10² = 13² + 48·7² = 37² + 72·4².

## Exact ordered algebra and the missing step

Let `p ≥ 5` be prime. An ordered identity
`4/p=1/x+1/y+1/z`, `0<x<y<z`, must have `p/4<x<p/2` and `p | z`.
Initially `p/4<x<3p/4`, so `x<p`. Clearing denominators gives
`p | xyz`. If `p ∤ z`, then `y=pm`; reduction of
`(4m-1)xz=pm(x+z)` modulo `p` shows `p | 4m-1`. Writing
`4m-1=pk` yields `(kx-m)z=mx>0`, hence `z≤mx<pm=y`, a
contradiction. Put `a=4x-p` and `N=px`. Here `0<a<2p`,
`a≠p` (since `p` is odd), and `gcd(a,N)=1`. Both `ay-N` and
`az-N` are positive, since `a/N=1/y+1/z` exceeds each separate
reciprocal. The remaining equation factors:

    (ay-N)(az-N)=N².                                             (1)

If `p ∤ y`, put `c=x²/(ay-N)`. Since `p | z` and `p ∤ (ay-N)`, the
product in (1) makes `c` a positive integer dividing `x²`. Also
`gcd(a,ay-N)=1` and `p≡4x (mod a)`, so `a | 4c+1` (**type I**).
If `p | y`, write `y=pm,z=pu` with `m<u`. Factoring the equation gives

    (am-x)(au-x)=x²,

so `d=am-x` satisfies `0<d<x`, `d | x²`, and `a | x+d` (**type II**).
To see the sharper bound `x<p/2`, otherwise `1/y+1/z≥2/p` but
`1/y+1/z<2/y`, so `y<p` and the type-I calculation applies. Set
`t=2x-p≥1`; `a=2x+t`, and `y>x` gives
`ay-N>(a-p)x=2tx`. Since `ay-N=x²/c`, this implies `x>2tc≥2c`,
so `0<4c+1≤2x<a`, contradicting `a | 4c+1`.

Conversely **either** criterion with `p/4<x<p/2`, `a=4x-p`, produces
an ordered identity. In type I let `d=x²/c` and use

    x, (px+d)/a, (px+p²c)/a.

In type II put `b=x²/d` and use

    x, p(x+d)/a, p(x+b)/a.

These are integers: in type I, modulo `a` one has `p≡4x`, hence
`px+d≡d(4c+1)≡0` and `px+p²c≡4x²(4c+1)≡0`. In type II,
`a | x+d` and `gcd(a,x)=1` give `gcd(a,d)=1`; the congruences
`x≡-d (mod a)` and `db=x²` imply `b≡d≡-x (mod a)`.
In each case `a<p` gives `x<y`; in type I, `p>x` gives
`p²c>x²/c=d` and hence `y<z`, while in type II `d<x` gives
`b>d` and hence `y<z`. Equation (1) proves both identities.
**A counterexample prime must rule out BOTH criteria for every integer
`p/4<x<p/2`.**

For type II this is also exactly the existing modular construction:
with `y=pm,z=pu`, set `h=4m-1` and `d=hx-pm=am-x`. Then
`du=mx`, `0<d<x<p`, and `hx=pm+d`. From `d | mx`, multiplying
this last equation by `m` gives `d | pm²`; as `d<p` and `p` is
prime, `d | m²`. Also `4hx=(h+1)p+4d`, so `h | p+4d` and
`x=(pm+d)/h`. For `d | m²`, `h | p+4d`, and `d<x`, the reverse
implication is already Lean-proved in `Reduction.lean`. Norm identities
for `p` do **not** supply the two required divisibilities automatically.

## Algebraic obstructions to tempting norm substitutions

* For `p ≡ 1 (mod 4)`, the number `a=4x-p` is `3 (mod 4)`.
  **No perfect square `c=t²` can work in type I**, because every prime
  divisor of `4t²+1` is `1 (mod 4)` (otherwise `-1` would be a square
  modulo a prime `3 (mod 4)`). Thus taking `c=1`, `c=v_K²`, or `c=x²`
  never yields the needed `a | 4c+1`.

* At the smallest possible `x₀=(p+3)/4`, one has `a=3` and
  `x₀≡1 (mod 3)`. Both criteria work at this `x₀` **if and only if**
  `x₀` has some prime factor `2 (mod 3)`: the necessary divisor `c`
  or `d` must be `2 (mod 3)`, and conversely such a prime factor can
  be taken as the type-II `d` (it is smaller than `x₀`). For the
  perfectly possible norm subfamily `p=1+48v²` with `p` prime,
  `x₀=1+12v²=1+3(2v)²`. Every prime factor of `x₀` is `1 (mod 3)`:
  a divisor `q≡2 (mod 3)` would make `-3` a square modulo `q`,
  which is impossible. Hence **none of these primes has an identity
  starting at `x₀`**. Examples include `p=193` (`x₀=49`) and
  `p=1201=5²+24·7²=1²+48·5²=7²+72·4²`
  (`x₀=301=7·43`). The latter has `(m,d)=(18,108)`,
  `4m-1=71 | 1201+4·108`, and the ordered identity
  `4/1201=1/306+1/21618+1/61251`. The failed `x₀` rules out a
  proposed first denominator, NOT the conjecture.

* A modular type-II witness requires the Jacobi symbol
  `(p/h)=-1` for `h=4m-1`. Indeed `gcd(h,m)=1`, and quadratic
  reciprocity gives `(r/h)=1` for every odd prime `r | m`: here
  `h≡3 (mod 4)` and `h≡-1 (mod r)`. If `2|m`, then `h≡7 (mod 8)`
  gives `(2/h)=1`. Since `d | m²`, `gcd(h,d)=1`, and
  `h | p+4d` then also gives `gcd(h,p)=1`. Thus `(d/h)=1`, while
  `p≡-4d (mod h)` gives `(p/h)=(-1/h)=-1`. In particular, if
  `p=u²+Kv²` and `h | Kv²`, then `p≡u² (mod h)` with
  `gcd(u,h)=1` (as `p` is prime), and no such `m` works. If one picks
  `h=u≡3 (mod 4)` from a norm representation, `(p/u)=(K/u)` must
  be `-1`; even this necessary condition need not provide a
  divisor `d | m²`. For example, `2521=11²+24·10²` has
  `(2521/11)=(2/11)=-1`, but with `m=(11+1)/4=3` the
  possibilities `d|9` are `1,3,9`; these require
  `p (mod 11)` to be `7,10,8`, respectively, not `2521 (mod 11)=2`.

* No bound on `m` can solve all these primes by this criterion.
  For `h=4m-1`, **no** divisor `d|m²` satisfies `h|1+4d`.
  Indeed, with `e=m²/d`, `h|1+4d` also implies `h|1+4e`, since
  `16m²=h(4m+1)+1`. Both divisibilities imply `d,e≥m`, hence
  `d=e=m`; but `1+4m=h+2` is not divisible by `h≥3`.
  Given a bound `B`, Dirichlet gives arbitrarily large primes
  `p≡1 (mod 24·∏_{1≤m≤B}(4m-1))`. Every such prime has all
  three norms, but `p≡1 (mod 4m-1)` prevents *every* `d|m²`
  for each `m≤B`. The stronger factorial-modulus version is
  Lean-proved as `hard_primes_escape_bounded_modular_parameters` in
  `Partial.lean`. This does not rule out unbounded `m` or type I.

## Finite counterexamples to more shortcuts (none to Erdős–Straus)

1. `p=2521` is prime, `p≡1 (mod 840)`, and has all three displayed
   norms. At `x₀=631`, which is a prime `1 (mod 3)`, both types fail.
   Moreover

       p+1=2·13·97,   p+4=5²·101,   4p+1=5·2017,

   where *all the odd displayed prime factors* are `1 (mod 4)`.
   Thus **no** `m` works with `d=1`, `d=m`, or `d=m²`: their required
   divisibilities reduce respectively to `4m-1 | p+4`, `p+1`,
   or `4p+1`. Nonetheless `m=22,d=44` works:
   `44 | 22²`, `4m-1=87`, `p+4d=2697=87·31`, and

       4/2521 = 1/638 + 1/55462 + 1/804199.

   In fact `p+2=3·29²`: the useful divisor `87=3·29≡7 (mod 8)`
   is **composite**, despite there being no prime factor `7 (mod 8)`.

2. Even picking `4m-1` from **any** of the three norm coordinates is
   not universal. The prime

       5113 = 47² + 24·11² = 35² + 48·9² = 71² + 72·1²

   has all three `u`'s `3 (mod 4)`. They give `m=12,9,18` and
   `h=47,35,71`, respectively. The condition `h|5113+4d`
   would require `d≡26 (mod 47)`, `d≡8 (mod 35)`, or
   `d≡53 (mod 71)`, respectively; direct enumeration of the
   divisors of `12²=144`, `9²=81`, and `18²=324` shows none
   qualifies. Yet `m=2,d=1` works (`7|5113+4`):

       4/5113 = 1/1461 + 1/10226 + 1/14940186.

3. Type I is a genuinely different branch, not safely omitted from a
   disproof attempt. For the prime `p=73`, take `x=22`, `a=15`,
   `c=11 | 22²` and `15 | 4·11+1`; this gives

       4/73 = 1/22 + 1/110 + 1/4015.

   At this **same** first denominator no type-II `d` works: the
   divisors of `22²` smaller than 22 are `1,2,4,11`, none
   congruent to `-22≡8 (mod 15)`. This is not a counterexample;
   for example `p=73` also has a type-II solution starting at `x=20`.

These examples were checked by exact rational arithmetic and primality
checks, not used to infer an all-prime conclusion. The three class-number
representations, elementary Jacobi restrictions, and arbitrarily strong
finite or density-one families leave the *pointwise* divisibility problem
for primes `p≡1 (mod 24)` unresolved. No valid proof of the universal
assertion in `Spec.lean`, and no genuine counterexample, follows here.
