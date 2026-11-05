# A certified local failure of a pointwise first-moment argument

**Status:** This is a negative test of a proposed way to prove the ordered
Erdős–Straus conjecture, **not** a universal decomposition or a counterexample.
`Spec.lean` is not imported or modified. The exact global criterion is
`CoveringGap.all_good_iff_explicit_hard_cover`; the joint character expansion
and a uniform positive lower bound for its *main term* are established in
`JacobiCorrectedJointCount.md`.

For a hard prime `p=24k+1`, put `x=6k+1+j`, `a=4j+3` (`0≤j<6k`). Let

    I_x = #{c>0 : c|x², a|4c+1},
    II_x = #{0<d<x : d|x², a|x+d}.

A positive sum `C(p)=Σ_j(I_x+II_x)` is **equivalent** to an ordered solution.
In particular, a missing witness at *one* `x` says nothing about `C(p)`.
Primality and `x<p` imply `gcd(a,x)=1`. Put `D=τ(x²)`,
`S=Σ_{c|x²}(c/p)` and `s=(x/p)`, with Legendre symbols. Jacobi reciprocity
transfers `(c/a)=(c/p)` for `c|x²`. The Type-I target `−4⁻¹ (mod a)` has
Jacobi sign `−1`; the Type-II target `−x (mod a)` has sign `−s`.
Complementary divisors `d↔x²/d` have the same sign, and their fixed point
`d=x` has the **wrong** sign for Type II. Consequently the numbers of
*correct-sign*, but not necessarily successful, divisors are exactly

    E_I=(D−S)/2,       E_II=(D−sS)/4.

Orthogonality of unit-group characters gives the exact rational first-moment
identity

    I_x+II_x = M_x+T_x,
    M_x = 2(E_I+E_II)/φ(a) = [3D−(2+s)S]/[2φ(a)],

where `T_x` is the sum of **all nonprincipal, non-Jacobi character modes**.
Unlike `I_x+II_x`, `M_x` is not a witness count. Summing over the eligible
`j` gives `C(p)=M(p)+T(p)`. The bound proved in
`JacobiCorrectedJointCount.md` is
`M(p)≥(log p)³/(3·2¹⁸ log 2)` when `log p≥64`. A universal proof by
this route still needs the *pointwise* inequality `T(p)>−M(p)` (or a
separate argument forcing a hit). No such inequality is established here.

## A particularly small certified prime-local cancellation

Take

    p=218857=24·9119+1,
    x=54717=6·9119+3=3·13·23·61,
    a=4x−p=11.                         (j=2)

This really is a prime, not just a probable prime. We have
`p−1=2³·3·11·829`, with `829` prime by trial division up to `28`.
Modular exponentiation gives `5^(p−1)≡1 (mod p)` and the following
residues for the distinct prime divisors `q` of `p−1`:

    q                         2        3       11      829
    5^((p−1)/q) mod p     218856   143639   161910   158574

None is `1`, so `5` has order `p−1` modulo `p`; therefore `p` is prime
(Lucas's criterion). The candidate is ordered-eligible because
`p<4x<2p`.

Modulo `11`, the factors `3,13,23,61` are `3,2,1,6`. The element `2`
has order `10`, with `3=2⁸`, `6=2⁹` and the required target
`−4⁻¹=−x=8=2³` modulo `11`. Every divisor of the **full** square `x²`
has discrete logarithm

    8i+j+9h (mod 10),     0≤i,j,h≤2;

(the factor `23≡1` is harmless). The nine possible classes are
`{0,1,2,4,5,6,7,8,9}`; exponent `3` is missing. Thus **all 81 divisors
miss both exact targets**, even if the Type-II bound `d<x` is dropped:
`I_x=II_x=0`.

Nevertheless there is a large Jacobi-corrected local first moment.
The quadratic residues modulo `11` are `{1,3,4,5,9}`. The four prime
factors of `x` have signs `+,-,+,-`; hence

    D=3⁴=81,    S=3·1·3·1=9,    s=(x/p)=(x/11)=+1,
    E_I=36,     E_II=18,      M_x=2(36+18)/10=54/5>φ(11)=10.

The nonquadratic error is **exactly** `T_x=−54/5`. In particular, not
even the inequality `M_x>φ(a)`, or occupancy of **nine of the ten unit
classes**, forces the *specified* target residue. Discarding integer-square
Type-I divisors is insufficient either: `81−τ(x)=81−16=65` nonsquare
integer divisors give an additive zero mode `65/11>0`, although `I_x=0`.
This rules out a per-fiber pigeonhole, principal-mode, or
principal-plus-Jacobi domination as a proof; it does **not** rule out a
future *global* cross-`j` cancellation argument.

The prime itself is **soluble at a different candidate**: `x₀=54715`,
`a₀=3`, `d=5<x₀` with `d|x₀²` and `3|x₀+d`. Set `b=x₀²/d=598746245`.
Then the strict ordered identity is

    4/218857 = 1/54715 + 1/3991951680 + 1/43683927234240.

Indeed the last two denominators are `p(x₀+d)/3` and `p(x₀+b)/3`,
and `(x₀+d)(x₀+b)=x₀(2x₀+d+b)` proves the fraction identity.

## Why the global inequality remains open

The construction proves `T_x=−M_x` at one denominator of a *good* prime;
it does not prove `T(p)=−M(p)` for any prime. The index `x₀` above
contributes a genuine positive hit, so extrapolating the local zero would
be a logical error. A global first moment is only `C(p)=M(p)+T(p)`, and
showing `M(p)>0` is not a lower bound on `C(p)`. To rule out a single bad
prime, one must bound its **actual** `T(p)` from below by `−M(p)`, or
force a hit by another pointwise argument. An exceptional-density bound,
a finite scan, or a second moment of size `X/(log X)^A` does not exclude
one exceptional prime of size `X`. Likewise fixed Type-II modulus cutoffs
cannot cover every hard prime: the already Lean-proved
`CoveringGap.hard_primes_escape_bounded_typeII` provides arbitrarily large
primes evading each fixed cutoff. No universal argument or bad prime is
claimed.

## Reproducible exact-arithmetic audit (Python standard library only)

```python
from fractions import Fraction
from math import isqrt
from itertools import product
p, x, a = 218857, 54717, 11
assert p == 24*9119+1 and x == 3*13*23*61 and a == 4*x-p
assert p < 4*x < 2*p
assert p-1 == 2**3*3*11*829
assert all(829 % t for t in range(2, isqrt(829)+1))
assert pow(5, p-1, p) == 1
assert [pow(5, (p-1)//q, p) for q in (2,3,11,829)] == [
    218856, 143639, 161910, 158574]
D = [3**i * 13**j * 23**h * 61**l for i,j,h,l in product(range(3), repeat=4)]
assert len(D) == len(set(D)) == 81
assert {d % a for d in D} == set(range(1, 11)) - {8}
assert all((4*d+1) % a and (x+d) % a for d in D)
chi = lambda u: 1 if pow(u % p, (p-1)//2, p) == 1 else -1
S, s = sum(map(chi, D)), chi(x)
assert (S,s) == (9,1)
assert Fraction(3*len(D)-(2+s)*S, 2*10) == Fraction(54,5)
x0, d = 54715, 5
assert (x0+d) % 3 == 0 and (x0*x0) % d == 0
b = x0*x0//d
assert (x0+b) % 3 == 0
y, z = p*((x0+d)//3), p*((x0+b)//3)
assert (y,z) == (3991951680, 43683927234240) and x0 < y < z
assert Fraction(4,p) == Fraction(1,x0)+Fraction(1,y)+Fraction(1,z)
```
