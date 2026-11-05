# Pointwise Erdős–Straus covering: the exact remaining gap

`Submission/CoveringGap.lean` builds on the proved classification in
`Classification.lean` and reduction in `Reduction.lean`. It contains **no proof
of the conjecture**. In particular it does not import or edit `Spec.lean`.

## Exact universal obligation, not a computation

Write a hard prime as `p=24k+1`. Its possible ordered first denominators are
**exactly**

    x_j = 6k+1+j,   a_j = 4x_j-p = 4j+3,   0 <= j < 6k.

`all_good_iff_explicit_hard_cover` is a Lean proof that *every* `n>2` is
`Good` if and only if **for every** prime `24k+1` there is a `j` in this
range for which at least one condition holds:

    (I)  some c>0 divides x_j², and a_j divides 4c+1;
    (II) some 0<d<x_j divides x_j², and a_j divides x_j+d.

The equivalence supplies no such `j` for an arbitrary hard prime. Its
negation, formalized by `bad_prime_iff_no_divisors`, requires excluding **both
conditions for every candidate x**; ruling out a particular `j`, Type II
alone, or a parameter subfamily does not establish a counterexample.
`bad_has_hard_prime_divisor` proves that every hypothetical counterexample
`n>2` has a bad prime divisor `1 (mod 24)`. Consequently a *least* bad `n`
would itself be such a prime, but this minimality yields no missing divisor.

The smallest candidate is `x_0=(p+3)/4=6k+1`, with `a_0=3` and
`x_0=1 (mod 3)`. It works **if and only if** some prime factor of `x_0`
is `2 (mod 3)`: each of (I) or (II) requires a divisor of `x_0²` that is
`2 (mod 3)`, hence such a prime factor; conversely, take that prime factor
as `d` in (II). This is an exact factoring criterion at **one** `x`, not a
proof that all hard primes have a solution. For `p=193,2521,66529`, the
respective `x_0` are `49=7²`, `631` and `16633` (the last two are prime),
all with prime factors `1 (mod 3)`. Each therefore fails *at `x_0`*.

## Why a finite residue cover cannot settle Type II

The new Lean theorem `typeII_modular_parameter` proves necessity, not just
sufficiency, of the modular conditions in `Reduction.lean`. If (II) holds,
put `a=4x-p`, `m=(x+d)/a` and `h=4m-1`. Then

    h*a=p+4d,   h*x=pm+d,   0<m,   d|m².

For the last fact, `gcd(a,x)=1` follows from primality of `p` and `x<p`;
`a|x+d` then gives `gcd(a,d)=1`. Since `d|x²`, also
`d|(x+d)²=a²m²`; cancel the coprime `a²` to get `d|m²`.
Thus at a fixed `m`, the permitted residues of `p (mod 4m-1)` are the
**specific** residues `-4d`, `d|m²`, not all nonquadratic residues.

`hard_primes_escape_bounded_typeII` is an **infinite**, Lean-proved
obstruction: for each fixed `B` and each threshold `N`, some prime
`p>N`, `p=1 (mod 840)`, has **no Type-II witness whose actual parameter
`m=(x+d)/(4x-p)` is at most `B`**. It follows from the Dirichlet-prime
construction in `Partial.lean`: take primes `p=1 (mod 840*(4B)!)`.
If `m<=B`, then `4m-1|p-1`, whereas (II) would imply
`4m-1|p+4d` and therefore `4m-1|1+4d` with `d|m²`. The last
possibility is ruled out by the proved `not_one_modular_divisor`. This
**does not** rule out Type I, Type II with a parameter growing with `p`,
or the conjecture. It demonstrates why checking finitely many modular
residue families for `m` cannot yield the required pointwise statement.

Even a correct reciprocity sign does not close the gap. If `h=4m-1` and
`d|m²`, quadratic reciprocity gives Jacobi `(d/h)=+1`; hence a Type-II
modular witness requires `(p/h)=-1`. But for `p=193, m=3, h=11`, the
Legendre symbol `(p/11)=(6/11)=-1`, while `d|9` allows only `d=1,3,9`,
**none** of which satisfies `11|193+4d`. A sign count does not prove a
match to the precise divisor residues.

Likewise, a large number of divisors of `x²` does not automatically hit a
target residue. When `a=4x-p=3 (mod 4)`, `gcd(a,x)=1`, and every prime
factor `q|x` has Jacobi `(q/a)=+1`, all divisors of `x²` have symbol `+1`.
But (I) asks for `c=-1/4 (mod a)`, symbol `-1`, and (II) asks for
`d=-x (mod a)`, also symbol `-1`. Thus **both fail at that x** regardless
of the divisor count. For example, at `p=66529, x=16650, a=71`,
`x=2*3²*5²*37`, all four primes are quadratic residues modulo `71`;
`x²` has 225 positive divisors but neither type works at this `x`.
That prime succeeds at a *different* `x`, so this local obstruction is
not a counterexample.

## Stress tests (not evidence of a universal theorem)

Lean proves these three primes are good via Type II (including primality,
the required inequalities and divisor conditions); exact ordered
witnesses, also checked with rational arithmetic, are:

| `p` | `x` | `a` | `d` | `m=(x+d)/a` | ordered `(x,y,z)` |
|---:|---:|---:|---:|---:|---|
| 193 | 52 | 15 | 8 | 4 | (52, 772, 5018) |
| 2521 | 638 | 31 | 44 | 22 | (638, 55462, 804199) |
| 66529 | 17060 | 1711 | 50 | 10 | (17060, 665290, 226996948) |

Each displayed `d` divides `m²` but **does not** divide `m`.
The exhaustive finite B-subfamily certificate in `BAxisCertificate.cpp`
also returns `NO_B` for all three (it tests `d|m`). A direct bound makes
such a negative test finite: if `d|m` and `4m-1|p+4d`, then
`A=(p+4d)/(4m-1)` is `3 (mod 4)` and so `A>=3`; since `d<=m`,
`p+4m >= 3(4m-1)`, hence `m <= (p+3)/8`. Checking **all** such `m`
and divisors `d|m` gives no B witness for any of the three primes.
Thus restricting Type II to `d|m` cannot be universal. These finite
cases serve to **refute shortcuts**, not to prove the statement for all primes.

**Unproved input:** a *pointwise* argument ensuring that for **every** prime
`p=24k+1` at least one `x_j` hits the exact Type-I or Type-II divisor
residue in the first section. Character/average estimates and arbitrarily
many checked primes do not provide that quantifier. Neither an actual
prime excluding both types at every `x_j` nor a universal construction
has been supplied.
