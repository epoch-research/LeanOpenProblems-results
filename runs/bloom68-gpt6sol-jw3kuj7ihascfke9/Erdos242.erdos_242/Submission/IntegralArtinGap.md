# Exact Artin information versus quadratic information on an Erdős–Straus fiber

**Status.** This is an ordinary mathematical proof using standard local/global
class field theory and the Brauer group of the one-dimensional torus. It is
**not** a Lean formalization, a proof of Erdős–Straus, or a counterexample
prime. `Spec.lean` is not imported or edited. All claims about local points
below explicitly impose integrality at *every* finite place and positivity and
strict ordering at the real place. The example is a fixed failed fiber of the
**soluble** hard prime 193, not a failure at all its possible denominators.

## An exact theorem for all prime-modulus fibers

Let `p≡1 (mod 24)` be prime and let `p/4<x<p/2` be an integer such that
`q=4x−p` is prime. Then `q≡3 (mod 4)`, `3≤q<p`, and `q∤px`. Set `N=px`
and consider the affine curve over `ℤ`

    V: q*y*z = N*(y+z),
    u=q*y−N,  v=q*z−N,  u*v=N².                              (1)

Its generic fiber is `G_m` via the invertible coordinate `u`. Let `V⁺(ℤ)`
mean solutions with integers `x<y<z`; let `V⁺(A_ℤ)` mean real solutions
`x<y_∞<z_∞` and solutions `(y_ℓ,z_ℓ)∈V(ℤ_ℓ)` for **every** finite prime
`ℓ`. For a positive integer `M` coprime to `q`, set

    D_q(M)={ U mod q : U>0 and U | M² } ⊂ (ℤ/qℤ)×,
    t=−N mod q.

Write `B_q` for the cyclic-algebra classes `(χ,u)∈Br(V_ℚ)` as `χ` runs
through the characters of `Gal(ℚ(ζ_q)/ℚ)≅(ℤ/qℤ)×`. Brauer–Manin
orthogonality is imposed on the stated **integral adelic** set, using the
Brauer group of the generic fiber. Then:

1. `V⁺(ℤ)≠∅` if and only if `t∈D_q(N)`. By the ordered classification in
   `Classification.lean`, for this prime numerator this is exactly the
   Type-I-or-Type-II predicate at **this particular** first denominator.
2. `V⁺(A_ℤ)^{Br(V_ℚ)[2^∞]}≠∅` if and only if **some prime factor `r|x`
   has `(r/q)=−1`**. Equivalently, `D_q(N)` contains a divisor with the
   correct quadratic character `(U/q)=(t/q)=−1`. This tests every
   2-primary Brauer class, not merely one Jacobi symbol.
3. `V⁺(A_ℤ)^{B_q}≠∅` if and only if `t∈D_q(N)`. Consequently *full*
   integral Brauer–Manin orthogonality is also equivalent to `V⁺(ℤ)≠∅`
   on this specified fiber. This is an exact detection statement, **not**
   an existence theorem for any arbitrary `p` or for some other `x`.

Here `(r/q)` is the Legendre symbol, including the possibility `r=2`.
Statement 2 fails if one silently substitutes rational points or merely
local congruence points for the integral adelic set.

### Proof, including the integrality step

If `y,z>0` satisfy (1), then `q/N=1/y+1/z`, so `u,v>0`. Hence `u` is a
positive divisor of `N²` and `u≡−N (mod q)`. Conversely, if `U>0` divides
`N²` and `U≡−N (mod q)`, its complement `W=N²/U` has
`W≡N²/(−N)≡−N (mod q)` because `q∤N`. Thus
`y=(U+N)/q`, `z=(W+N)/q` are positive integers on (1). The fixed point
`U=W=N` cannot satisfy the residue condition (`q≥3` and `q∤N`), so
replace `U` by its complement if needed to have `U<N<W`. Then `y<z`
and `y>N/q=(p/q)x>x` since `q<p`. This proves assertion 1, including
*strict* ordering.

Next take **any** point of `V⁺(A_ℤ)`. At a finite prime `ℓ` write
`e_ℓ=v_ℓ(u_ℓ)`. Both `u_ℓ,v_ℓ` are in `ℤ_ℓ` and multiply to `N²`, so

    0≤e_ℓ≤2v_ℓ(N).

In particular `e_ℓ=0` for `ℓ∤N`, including `ℓ=q`. The *positive
integer* `U=∏_{ℓ|N} ℓ^{e_ℓ}` is therefore a divisor of `N²`. This
bounded-exponent conclusion uses **integrality**, not a Hasse norm
principle. The idele `(u_w/U)_w` is a unit at every finite `ℓ≠q` and
is positive at the real place. Each cyclotomic extension of conductor
`q` is unramified at `ℓ≠q`, so local reciprocity kills these units.
Global reciprocity kills the diagonal positive rational `U`. At `q`,
`u_q≡−N (mod q)`; the local Artin map of `ℤ_q×` onto
`Gal(ℚ_q(ζ_q)/ℚ_q)≅(ℤ/qℤ)×` is reduction modulo `q` (up to the harmless
choice of inversion). If every class in `B_q` is orthogonal, the
characters separate this finite group and force `u_q/U≡1 (mod q)`.
Thus `U≡−N (mod q)`. Conversely, an actual positive integral point
supplies a diagonal adelic point orthogonal to all Brauer classes.
This proves assertion 3 and the full-Brauer conclusion.

The unique nontrivial quadratic character of that cyclotomic group
comes from `K=ℚ(√−q)` (its discriminant is `−q`). Applying just this
character to the same valuation comparison proves that 2-primary
Brauer orthogonality **necessitates** `(U/q)=(−N/q)`. Since
`p≡4x (mod q)`, we have `N=px≡4x² (mod q)`; hence `(−N/q)=−1`.
A nonresidue divisor of `N²` has a nonresidue prime factor. If the only
such factor were `p`, then `(p/q)=(x/q)=−1` would itself force a
nonresidue prime factor of `x`. This gives the necessary factor `r|x`.

Conversely, choose such a factor `r|x`. The unit `−N/r (mod q)` is a
square, so choose an integer `s` coprime to `q` with
`s²r≡−N (mod q)`. At every place **except `q`**, including the real
place, take `u=r`, `v=N²/r`; at `q` take `u=s²r`,
`v=N²/(s²r)`. Formula (1) recovers `y,z`. At finite `ℓ≠q`, division
by `q` is integral, since `r,N²/r` are integers. At `q`, both `u,v`
are units and both are `−N (mod q)`, so `y,z∈ℤ_q`. At infinity,
`0<r<N`, `p>q`, and hence `x<y<z`. This produces an **ordered,
positive-real, everywhere integral adelic point**, not an integral
rational point.

It is orthogonal to **all** 2-primary Brauer classes: the split torus
has the standard decomposition

    Br(G_m)/Br(ℚ) ≅ H¹(ℚ, ℚ/ℤ),

whose character classes are represented by `(χ,u)`. The idele for `u`
differs from the diagonal rational `r` only by the square unit `s²`
at `q`. Every finite 2-power-order local character of `ℚ_q×` kills
square units in `ℤ_q×`: its restriction to `1+qℤ_q` (a pro-`q`
group) is trivial, and the 2-primary quotient of
`(ℤ/qℤ)×` has order **two**, as `q≡3 (mod 4)`. Global reciprocity
kills the diagonal `r`, and constant Brauer classes have zero global
invariant sum. This proves the sufficiency in assertion 2. It also
shows why quadratic splitting/genus characters or 2-primary Brauer
invariants **of these torus coordinates** cannot fill the odd-order
part of the exact ray-class residue without further arithmetic input.
It does not exclude a future form or narrow-class-group argument that
also controls the actual prime factors and their permitted exponents.

## A prime fiber passing all quadratic Brauer tests but having no positive integer point

Take

    p=193=24·8+1,   x=53,   q=4x−p=19,   N=px=10229.

The numbers `193`, `53`, and `19` are prime (trial division by primes
up to their respective square roots `13`, `7`, and `3` suffices), and
`193/4<53<193/2`. Modulo 19, `3` has order 18:
`3^9≡−1` and `3^6≡7≠1`. Also

    193≡3,       53≡15=3⁵,       −N≡12=3¹⁵ (mod 19).

As `N²=193²·53²`, the **entire** bounded set of positive-divisor
residues has logarithmic exponents

    {i+5j (mod 18): 0≤i,j≤2}={0,1,2,5,6,7,10,11,12}.

It misses 15: there are **no positive integer points on this fiber**.
In the Lean Type-I/II terms, the only residues of divisors of
`x²=53²` are `{1,15,16} (mod 19)`: neither the Type-I target
`−4⁻¹≡14` nor the Type-II target `−x≡4` occurs (indeed `d<x`
would require `d=1`). The Legendre obstruction, however, is absent:
`(193/19)=(−N/19)=−1` and `−N≡4·193 (mod 19)`, with
`4=2²` of order **nine** modulo 19. Both supported primes are
primitive roots modulo 19; **generation of the full Artin group is
not generation by divisors with the permitted exponents**.

For a completely explicit ordered-real, everywhere-integral adelic
point, use

    (y,z)=(10422/19, 552366/19)  at infinity and at every ℓ≠19;
    (y,z)=(579, 30687/4)        at ℓ=19.

Both pairs satisfy (1), and the first is strictly ordered after
`x=53`. Their respective `u=19y−N` are `193` and `772=4·193`;
the first pair is integral at every `ℓ≠19`, the second at `19`.
The ratio `4` at 19 is a unit whose image in the 2-primary local
Artin quotient is trivial, so **all** 2-primary Brauer classes are
orthogonal. Nevertheless a faithful Dirichlet character of order 18
modulo 19 has a cyclic Brauer class that obstructs *every* such
positive integral adele: by the valuation argument it would require
`193^i53^j≡12 (mod 19)` with `0≤i,j≤2`, contradicted above. On the
explicit quadratic-admissible adele, its residual obstruction has
odd order nine.

Even the ordinary ideal class group of `ℚ(√−19)` is trivial: its
Minkowski bound `2√19/π<3` leaves only norms 1 and 2, while 2 is
inert (`T²−T+5` is irreducible modulo 2). Thus neither a nontrivial
quadratic class group nor a nonprincipal binary form is responsible
for the missing exact target. This observation does **not** rule out
some future argument that uses more arithmetic than class-group or
quadratic-character data.

For comparison, at the **first** denominator `p=193,x=49,q=3` one
has `N=9457=193·7²`. Every positive divisor of `N²` is `1 (mod 3)`
but `−N≡2`, so already the *quadratic* Brauer class `(-3,u)` obstructs
the positive integral fiber; finite-place integral points and a
positive-real point still exist separately. The prime 193 itself is
soluble at the **next** denominator: `x=50,q=7,c=5|50²`, `7|4c+1`,
and

    4/193 = 1/50 + 1/1450 + 1/27985.

Hence neither failed fiber contradicts Erdős–Straus. Full Artin
reciprocity detects the exact bounded-divisor obstruction *at one
fiber*, but it does not prove that **some** `p/4<x<p/2` has a witness
for each hard prime. That unproved quantifier, and the separate
nonsquare-only Type-I conjecture, remain open; finite tests through
`10¹⁰` are not substitutes for either pointwise theorem.
