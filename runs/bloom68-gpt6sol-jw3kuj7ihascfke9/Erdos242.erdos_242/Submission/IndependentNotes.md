# Independent ordered Erdős–Straus diagnostics (no universal proof)

This note is an ordinary mathematical proof of further **conditional** results, not
an edit of `Spec.lean` and not a proof or disproof of Erdős–Straus. Here `Good(p)`
means that positive integers `x<y<z` satisfy `4/p=1/x+1/y+1/z`.

## Exact prime divisor criterion, including the order

**Theorem.** Let `p≥5` be prime. Then `Good(p)` is equivalent to the existence
of an integer `p/4 < x < p/2`, with `a=4x−p>0`, satisfying at least one of

* **type I:** `c | x²` for some positive `c`, and `a | 4c+1`;
* **type II:** `d | x²` for some integer `0<d<x`, and `a | x+d`.

For type I, valid *ordered* denominators are

    x,  y=(p x + x²/c)/a,  z=(p x + p² c)/a.

For type II, writing `b=x²/d`, `m=(x+d)/a`, `u=(x+b)/a`, valid denominators
are `x, p m, p u`.

**Proof.** First, every ordered solution has `p/4<x<3p/4`, by comparing
`1/x` and `1/x+1/y+1/z` with `4/p` and `3/x`. In particular `x<p`.
Clearing denominators gives `p | xyz`. In fact **`p | z`**: otherwise
`p | y`, so write `y=p m` with `p∤z`. Clearing denominators again gives

    (4m−1) x z = p m (x+z).

Because `p∤xz`, primality implies `4m−1=p k`. Dividing by `p` and
rearranging, `(k x−m)z=m x>0`, so `k x−m≥1` and
`z≤m x<p m=y`, a contradiction.

Set `N=p x`, `a=4x−p`. Positivity of the remaining two reciprocals gives
`a>0`, and the standard exact factorization is

    d_y = a y−N > 0,  d_z = a z−N > d_y,
    d_y d_z = N².                                            (1)

Also `gcd(a,x)=gcd(p,x)=1` and `gcd(a,p)=1` (`0<a<2p` and `a≠p`, since
`p` is odd). Thus `gcd(a,N)=1`.

If `p∤y`, then `p∤d_y`, while `p|d_z` because `p|z`; equation (1) and
Euclid's lemma imply `d_y | x²`. Put `c=x²/d_y`. From `a|N+d_y` and
`p≡4x (mod a)` it follows that

    a | 4x²+d_y = d_y(4c+1).

Since `gcd(a,d_y)=1`, this proves `a|4c+1`.

For completeness, **any solution has the stronger bound `x<p/2`**. If
`x≥p/2`, then `1/y+1/z=4/p−1/x≥2/p`, whereas
`1/y+1/z<2/y`; hence `y<p`, so the preceding type-I argument applies.
Let `t=2x−p≥1`. Because `a=2x+t` and `y>x`, equation
`a y=p x+d_y` gives `d_y>(a−p)x=2t x`. From `d_y=x²/c` follows
`x>2t c≥2c`. Therefore `0<4c+1≤2x<2x+t=a`, contradicting
`a|4c+1`.

If `p|y`, we already know `p|z`. Write `y=p m`, `z=p u`, `m<u`.
The fraction equation becomes `a m u=x(m+u)`, and hence

    (a m−x)(a u−x)=x².

Both factors are positive and the first is smaller than the second. Thus
`d=a m−x` satisfies `0<d<x`, `d|x²`, and `a|x+d`.

Conversely, `a<p` whenever `x<p/2`. In type I put `d=x²/c`. The
congruences `p≡4x (mod a)` and `a|4c+1` imply
`a|px+d`, since `px+d≡d(4c+1)`, and `a|px+p²c`, since
`px+p²c≡4x²(4c+1)`. So the displayed denominators are integers;
`y>x` follows from `a<p`, and `z>y` from `p²c>d` (as `pc>x`).
Equation (1) with factors `d,p²c` proves the fraction identity.
In type II, `gcd(a,d)=1` follows from `a|x+d` and `gcd(a,x)=1`.
Writing `x²=db`, reduction modulo `a` gives `x≡−d`, then
`d b=x²≡d²`, so `b≡d` and `a|x+b`. Thus `m,u` are integers,
`u>m` since `b>d`, and `x<p m` since `a<p`. The factorization
`(a m−x)(a u−x)=d b=x²` yields `a m u=x(m+u)` and the required
fraction identity. This proves both directions with *strict* order.

**Further consequence (exactness of the existing type-II modular witness
for primes).** For an ordered solution with `y=p m`, `z=p u`, let

    h=4m−1,  d=h x−p m.

Clearing denominators shows `d u=m x`, so `0<d<x<p` and `d|m x`.
Multiplying `h x=p m+d` by `m` shows `d|p m²`. As `d<p` and `p` is
prime, `d|m²`. Multiplying `h x=p m+d` by `4`, and using `4m=h+1`,
shows `h|p+4d`. Hence all the hypotheses of
`good_of_modular_witness` from `Reduction.lean` are **necessary** as
well as sufficient for type-II solutions to prime `p`. This does not
say that every solution is of type II: the distinct type-I criterion
above must also be ruled out to certify a counterexample.

## Exactly when the minimal first denominator works

For prime `p≡1 (mod 24)`, put `x₀=(p+3)/4`. Then `x₀≡1 (mod 3)` and
`a=4x₀−p=3`.

**Theorem.** A strictly ordered solution *with first denominator exactly
`x₀`* exists if and only if `x₀` has a prime factor `r≡2 (mod 3)`.

If such `r` exists, `r<x₀`, and the type-II branch above applies with
`d=r`,

    m=(x₀+r)/3,  u=(x₀+x₀²/r)/3,
    (x,y,z)=(x₀,p m,p u).

For necessity, the factors `d_y,d_z` in (1) have product `(p x₀)²`
and obey `d_y≡−p x₀≡2 (mod 3)`. If every prime divisor of `x₀`
is `1 (mod 3)`, the same is true of `p`, so **every** positive divisor
of `(p x₀)²` is `1 (mod 3)`, impossible. Conversely a prime divisor
`r≡2 (mod 3)` gives `3|x₀+r`; the type-II integrality and order were
proved in the preceding theorem. No density or finite search is used.

Example genuinely beyond the sufficient cases stated in `Partial.lean`:
`p=3361` is prime, `p mod 840=1`, `p mod 11=6`, and
`p+4=3365=5·673` has no factor `3 (mod 4)`. Nevertheless
`x₀=841=29²`, `29≡2 (mod 3)`, giving the exact ordered identity

    4/3361 = 1/841 + 1/974690 + 1/28266010.

Conversely `p=1201` is prime and `x₀=301=7·43` has *only* prime
factors `1 (mod 3)`, so no solution has `x=301`. Nonetheless
`1201 mod 840=361`, `1201 mod 11=2`, and `1201+4=5·241` has no
factor `3 (mod 4)`, but it is **not** a counterexample:

    4/1201 = 1/306 + 1/21618 + 1/61251.

Indeed `1201+6=71·17`, `71=4·18−1`, and the last two denominators are
`1201·18` and `1201·51`. Thus restricting to the smallest possible
first denominator or to the existing three modulus tests is invalid.

## More shifted-divisor families; why they remain conditional

For `p≡1 (mod 8)` prime, suppose `q | p+2` and `q≡7 (mod 8)`;
`q` need not be prime. Write `q=4m−1` (so `m` is even) and
`r=(p+2)/q`. Since `p+2≡3 (mod 8)`, `r≡5 (mod 8)`, so `r≥5`;
also `r<p`. Then

    x=m r,   y=p m,   z=p m r/2

are ordered positive integers, and, because `p+2=(4m−1)r`,

    1/x+1/y+1/z = (p+r+2)/(p m r)=4/p.

For example `p=2521` has `p+2=87·29`, `87≡7 (mod 8)`, and

    4/2521 = 1/638 + 1/55462 + 1/804199.

This prime also has `p+1=2·13·97`, `p+4=5²·101`, and
`4p+1=5·2017`, with every listed odd prime `1 (mod 4)`: none of
those three natural shifts forces a `3 (mod 4)` factor.

A companion factorization: if a prime `p≥5` has a divisor
`q≡3 (mod 4)` of `4p+1`, write `4p+1=(4m−1)(4u−1)` with
`m<u` (swap the two factors if needed; equality would force
`p=t(t+1)`, not a prime ≥5). Then `p=4m u−m−u` and

    4/p = 1/(m u) + 1/(p m) + 1/(p u),

with `m u<p m<p u`. This is the `d=m²` subcase of the modular
witness, not a universal proof. For `p=1201`, `4p+1=5·31²` gives
`m=8,u=39` and `(x,y,z)=(312,9608,46839)`.

**Prime-first-denominator diagnostic.** Suppose additionally `p≡1 (mod 4)`
and the first denominator `x=r` is itself prime. In type I, the only
possible `c|r²` is `c=r`: `4·1+1=5` has no divisor `3 (mod 4)`, and
`4r²+1` cannot have one either (an odd prime `3 (mod 4)` dividing it
would make `−1` a quadratic residue). The condition `a|4r+1` then
implies `a|p+1`. In type II the only `d|r²` with `d<r` is `d=1`,
and `a|r+1` implies `a|p+4`. As `a=4r−p≡3 (mod 4)`, **if neither
`p+1` nor `p+4` has a divisor `3 (mod 4)`, no solution can have a
prime first denominator.** For instance `p=2521` has that property;
this says nothing about its displayed solution with composite `x=638`.

## Reciprocity obstructions, and the exact remaining gap

Let `h=4m−1≥3`, `d|m²`, and `h|p+4d`. For each odd prime `r|m`,
Jacobi reciprocity and `h≡3 (mod 4)`, `h≡−1 (mod r)` give

    (r/h) = (−1/r)(h/r) = (−1/r)² = 1.

For `2|m`, `h≡7 (mod 8)` gives `(2/h)=1`. Thus `(d/h)=1`.
Also `gcd(h,d)=gcd(h,p)=1`. The Jacobi symbol therefore satisfies

    (p/h) = (−4d/h) = −1.                                 (2)

In particular a type-II witness cannot exist for a given `m` when
`p` has Jacobi symbol `+1` modulo `4m−1`; this generalizes the
`p≡1 (mod 4m−1)` obstruction already formalized in `Partial.lean`.
However Jacobi `−1` is **not sufficient**: for `m=3`, `h=11`, the
possible `d|m²` are `1,3,9`, giving only `p mod 11=7,10,8`, whereas
`2` and `6` are also quadratic nonresidues modulo `11`. The soluble
prime `1201` has `1201 mod 11=2`.

For prime `p≡1 (mod 4)` and `a=4x−p`, quadratic reciprocity also
implies `(c/a)=(c/p)` for every positive `c|x²`. Indeed for an odd
prime `r|x`, `(r/a)=(−1/r)(a/r)=(p/r)=(r/p)`; for `r=2|x`,
`a≡−p (mod 8)` gives `(2/a)=(2/p)`. In type I,
`a|4c+1` forces `(c/a)=−1`. In type II, `a|x+d` forces
`(d/a)=−(x/a)`. Therefore **every** ordered solution for such a
prime has a first denominator `x` containing a prime quadratic
nonresidue modulo `p`. This condition is necessary, not sufficient.
At `a=3`, it specializes to the exact minimal-`x` criterion above,
since for `r|x₀`, `(r/p)=(p/r)=(−3/r)=(r/3)`.

A further soluble residual example demonstrates the limit of just a
few factorization criteria: `p=5569` is prime,
`p mod 840=529`, `p mod 11=3`, `p+4=5573` and `4p+1=22277`
are primes `1 (mod 4)`, `p+1=2·5·557`, and
`(p+2)/3=3·619` has no prime factor `5` or `7 (mod 8)`.
The minimal first denominator `1393=7·199` has no factor
`2 (mod 3)`. But `(m,d)=(204,34)` works:
`34|204²`, `4m−1=815`, `(p+4d)/815=7`,
`(p m+d)/815=1394>34`, and the exact identity is

    4/5569 = 1/1394 + 1/1136076 + 1/46579116.

The remaining issue is **pointwise**: prove, for every hard prime
`p≡1 (mod 24)`, one of the two exact divisor conditions above, or
prove that a specific prime satisfies neither for every
`p/4<x<p/2`. None of the congruence/reciprocity observations in this
note establishes that. The explicit identities and sample factorizations
were independently checked by exact rational arithmetic and primality
factorization; such finite diagnostics are *not* used as a proof for
all primes.
