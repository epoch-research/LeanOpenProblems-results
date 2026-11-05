# Variable-modulus polynomial progressions: what is pointwise, and what is not

**Status.** `VariableProgressions.lean` proves conditional, pointwise polynomial constructions and an exact counterexample to a simpler squareclass-based covering. It neither proves the universal nonsquare covering nor edits/imports `Spec.lean`. The question's quantifier is **at the specified input**, not just for sufficiently large members of an arithmetic progression.

## A genuinely primitive, positive Type-II progression

Let `n,m,d>0`, `h=4m−1`, `d|m²`, and `h|n+4d`. Define

    a=(n+4d)/h,   x=(nm+d)/h,   u=mx/d,   v=m²/d.

All four quantities are integers: `h x=nm+d` follows from
`nm+d+hd=m(n+4d)`; then `x+d=ma`, so `d|m(x+d)=m²a` and therefore
`d|mx`. **Furthermore, `gcd(n,h)=1` without any assumption that `n` is
prime:** `gcd(h,m)=1`, `d|m²`, and `h` is odd, hence `gcd(h,4d)=1`; as
`h|n+4d`, also `gcd(h,n)=1`. This is the Lean theorem
`modular_witness_primitive`.

If in addition `d<x`, the *integer-coefficient polynomial* denominators

    N(t)=n+ht,   X(t)=x+mt,   Y(t)=mN(t),   Z(t)=N(t)(u+vt)

satisfy, for **every** integer `t≥0` (in particular `t=0`),

    1≤X(t)<Y(t)<Z(t),          4/N(t)=1/X(t)+1/Y(t)+1/Z(t).

Indeed, `hX=mN+d`, `d(u+vt)=mX` and `h+1=4m` give the identity on
cross-multiplication. The inequality `d<X` implies `u+vt>m` and
`mN=hX−d>2X`; this proves the strict order and positivity at the
*initial* number, not just eventually. The entire statement, including
integrality of `u,v`, primitivity and the rational equation, is proved in
`modular_witness_polynomial_progression`. For `n≡1 (mod 24)`, replacing
the parameter `t` by `24t` keeps the entire primitive progression in
`1 (mod 24)`.

**Do not drop the order/positivity checks.** For example, `n=97`,
`m=28`, `d=392` meet `d|28²` and `111=4m−1|97+4d=1665`, but
`x=(97·28+392)/111=28<392=d`. The canonical polynomial labels at `t=0`
are `(X,Y,Z)=(28,2716,194)`, **not** in increasing order; this example
is still soluble by reordering and is *not* a counterexample. The
exact data and reversed fraction identity are Lean-checked in
`modular_divisor_without_order_condition`. Thus an asymptotic
polynomial identity or a Jacobi-sign test alone does not give
the required ordered positive witness at a prescribed base point.

## What Type I adds for prime base points

For a hard **prime** `p`, suppose `p<4x`, `2x<p`, `a=4x−p`, and some
`c>0` divides the **whole square** `x²` with `a|4c+1`. Set

    D=x²/c,  y₀=(px+D)/a,  z₀=(px+p²c)/a,  Q=4ac.

The integers `y₀,z₀` and their strict order are proved by
`Classification.good_of_typeI`. Since `0<a<p`, `x<p` and `c|x²`,
primality gives `gcd(p,Q)=1`. With `N=p+Qt`, `X=x+act`, the denominators
from that construction are the following integer-coefficient
polynomials:

    Y=y₀+(pc+4cx+2x)t + a(4c²+c)t²,
    Z=z₀+(pc+4cx+8pc²)t + a(4c²+16c³)t².

To check the formulas, expand `X²/c = D+2axt+a²ct²`; then
`aY=NX+X²/c` and `aZ=NX+N²c`. Thus
`(aY−NX)(aZ−NX)=(NX)²` and `a+N=4X`, which give the fraction
identity. The inequalities `N<4X` and `2X<N` persist for `t≥0`, the
same `c` still divides `X²`, and the explicit Type-I construction
shows `1≤X<Y<Z` **already at `t=0`**. Lean proves primitivity and
`Good(p+Qt)` for *every* `t≥0` in `typeI_primitive_progression`; the
quadratic formulas above follow from the displayed expansions. As an
independent Lean check with **all** coefficients exposed,
`polynomial_193_typeI_progression` proves, for every `t≥0`,

    4/(193+140t) = 1/(50+35t)
                   + 1/(1450+2065t+735t²)
                   + 1/(27985+40565t+14700t²),

with a primitive modulus `140` and strictly increasing denominators.

By `CoveringGap.good_iff_ordered_divisors`, *if* a hard prime `p` already
has an ordered solution, one of these **full** Type-I or Type-II
certificates exists. Hence it admits a primitive progression beginning
at `p` with positive ordered solutions; `hard_prime_good_primitive_progression`
is the corresponding Lean theorem. The further theorem
`hard_prime_good_hard_progression` chooses a primitive multiple of 24
for the modulus. The polynomial formulas above show that this
conditional construction actually has polynomial denominators, not
merely unrelated solutions at each progression member. Evaluating at
`t=0` gives the reverse implication for **hard primes**. This is a
conditional equivalence, **not** an existence proof at an arbitrary
hard prime.

For arbitrary nonsquare **composite** `n≡1 (mod 24)`, a Type-II
certificate still gives a primitive polynomial progression, but the
Type-I argument `gcd(n,4ac)=1` need not hold: `n` can share a
factor with `a` or `c|x²`. For the nonsquare `505=5·101≡1 (mod 24)`,
`(x,a,c)=(130,15,26)` meets the full Type-I criterion, but its
natural modulus is `4ac=1560`, with `gcd(505,1560)=5`. This is
Lean-checked by `composite_typeI_chosen_modulus_not_primitive`;
**another** Type-I certificate `(x,a,c)=(129,11,129)` gives a
coprime modulus at 505, so the example only refutes automatic
primitivity of an *arbitrary* composite certificate. Multiplying an
existing prime's solution by `n/p` also yields a progression of modulus
divisible by `n/p`, not a proof of primitivity. Consequently the proposed universal
nonsquare-integer claim would imply Erdős–Straus by applying it to
primes and using `Reduction.good_of_hard_primes`; the converse for **all
nonsquare composite integers** is not established here. The
prime-only formulation is equivalent to the conjecture. Calling the
stronger composite formulation equivalent without a separate lifting
argument would hide another gap.

## An exact counterexample to the nonresidue-modulus shortcut

The tempting simpler assertion

> For every hard prime `p`, if `q=4m−1` is a `3 (mod 4)` prime and
> `(p/q)=−1`, then some `d|m²` has `q|p+4d` (or at least the first
> denominator `x=(p+q)/4` meets a full Type-I or Type-II test)

is **false**. Take `p=97`, `q=19`, `m=5`. Here `p` is prime,
`p≡1 (mod 24)`, `p≡2 (mod 19)`, and `2` is **not** a square modulo 19.
Yet `d|5²=25` permits only `d∈{1,5,25}`, and

    (97+4d) mod 19 = 6, 3, 7, respectively: never zero.

Moreover `x=(97+19)/4=29` lies strictly in `p/4<x<p/2`.
All positive divisors of `x²=29²=841` are `1,29,841`, with residues
`{1,10,5}` modulo 19. Type I requires `c≡−4⁻¹≡14 (mod 19)`;
Type II requires `d≡−x≡9 (mod 19)` (as well as `d<x`). Neither
occurs. `nonresidue_mod19_not_a_certificate` verifies primality,
nonresiduosity **for every residue modulo 19**, the entire `d|m²`
list, and failure of **both full** divisor types at this candidate in
Lean; `no_ordered_97_first_29` then excludes every strictly ordered
solution with first denominator 29. This refutes the stated shortcut,
**not** Erdős–Straus or the existence of a different modulus for 97.

Indeed `(m,d,h)=(2,2,7)` works at 97, giving
`4/97=1/28+1/194+1/2716`. In fact
`polynomial_97_hard_progression` proves for **all** `t≥0`

    N=97+168t,      X=28+48t,    Y=2N,    Z=NX,
    gcd(97,168)=1,  1≤X<Y<Z,     4/N=1/X+1/Y+1/Z.

This positive example demonstrates *why* allowing variable moduli can
help, and simultaneously why merely finding a nonresidue modulus
cannot be the missing pointwise proof.

## Squareclass obstruction and the remaining quantifier

For the full Type-II parameters, `h=4m−1≡3 (mod 4)` and `d|m²` give
the **Jacobi** symbol `(d/h)=+1`. For each odd prime `r|m`,
`h≡−1 (mod r)` and reciprocity yields
`(r/h)=(-1/r)(h/r)=(-1/r)²=+1`. If `2|m`, then `h≡7 (mod 8)` and
`(2/h)=+1`. Coprimality of `h` with `d` is essential; it was checked
above. Thus `h|n+4d` forces `(n/h)=(-4d/h)=−1`; **square** `n`
can never meet these exact parameters. Full Type I has the analogous
Jacobi obstruction (`PointwiseJacobi.square_no_typeI_anywhere`),
but squares such as `25` can have ordinary ordered decompositions, so
this is *not* an obstruction to Erdős–Straus. For a nonsquare `n`, a
negative symbol is only a **necessary condition** at a particular
modulus, not a cofactor `d` or `c` in the demanded residue.

Mordell's fixed-modulus 840 reduction leaves the six square residues
`{1,121,169,289,361,529}` among hard primes; for example the
nonsquare **prime** 2521 lies in `1 (mod 840)`. Permitting the modulus
to depend on `p` removes the finite-list cutoff but does not supply an
exact divisor residue at `p`. `Partial.hard_primes_escape_bounded_modular_parameters`
proves that no fixed upper bound on Type-II `m` suffices, even for
arbitrarily large primes `1 (mod 840)`. The **unproved** remaining
statement is still: for every hard prime `p`, at least one eligible
first denominator has a **full Type-I or full Type-II divisor witness**
(`CoveringGap.all_good_iff_explicit_hard_cover`). Neither a density
argument for polynomial progressions nor the nonresidue sign turns
that universal pointwise statement into a theorem.

**Verification:** `lake env lean Submission/VariableProgressions.lean` and
`lake build Submission.VariableProgressions` pass. The new file has no
`sorry` and does not import or change `Submission/Spec.lean`. All
rational identities in the two displayed numerical progressions were
also checked with exact fractions for initial parameters. None of the
conditional results is substituted for the universal conjecture.
