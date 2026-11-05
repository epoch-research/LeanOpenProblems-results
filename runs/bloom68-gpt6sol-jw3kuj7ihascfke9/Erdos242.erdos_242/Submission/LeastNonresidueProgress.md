# Least nonresidues, first multiples, and the exact divisor gap

**Status.** `LeastNonresidueProgress.lean` proves the small-nonresidue
constructions below with the *full* `c | x²` criterion and the strict ordered
first-denominator bounds. It also certifies the least-nonresidue/primitive-root
finite example, *both full local failures*, and a different ordered solution.
It imports `Classification.lean`, not `Spec.lean`. The general group/analytic
discussion is an ordinary mathematical argument. **There is no theorem for
all hard primes and no counterexample to Erdős–Straus here.**

## The required finite, pointwise covering

For a prime `p=24k+1`, the already checked classification says that an
ordered solution is equivalent to some `0≤j<6k` with `x=6k+1+j`, `a=4j+3`,
and either

    0<c | x² and a | 4c+1,                   (I)
    0<d<x, d | x² and a | x+d.              (II)

Both are **exact** congruences, not Legendre-symbol conditions. Every
eligible `x` is coprime to `a`: a common factor divides the prime
`p=4x−a`, while `x<p`. Consequently every divisor of `x²` is a unit
modulo `a`. Set

    D(x;a) = { ∏ r_i^{b_i} (mod a) : x=∏r_i^{e_i}, 0≤b_i≤2e_i }.

Writing `t_I=−4⁻¹ (mod a)` and `t_II=−x (mod a)`, (I) holds **iff**
`t_I ∈ D(x;a)`. By `LocalResidues.small_divisor_iff_divisor_of_coprime`,
(II) holds **iff** `t_II ∈ D(x;a)` as well: if a divisor `e>x` hits
the target, its complement `x²/e<x` hits the same target, and `e=x`
is impossible since `a≥3` is odd and `gcd(a,x)=1`. Thus the search is
for two specified members of a **bounded exponent box** in the unit
group, not merely for the existence of a nonresidue in that group.

Let `q` be the *least positive* quadratic nonresidue of `p`. It is
prime: otherwise a prime factor is a smaller nonresidue. Since `p≡1
(mod 24)`, `(2/p)=(3/p)=+1`, so `q≥5`. For each eligible `x=q t`,
`PointwiseJacobi.jacobi_divisor_transfer` makes `(q/a)=(q/p)=−1`,
but this proves only that `D(x;a)` contains *some* nonsquares. Its two
targets might still be missing.

A nonresidue first denominator is guaranteed even without an analytic
bound: since `(−1/p)=1`, reflect some nonresidue into `(0,p/2)`;
its least prime nonresidue `q` is then `<p/2`. Double `q` until
`x=2^e q<p/2` is maximal. Now `p<4x` (equality is impossible
since `p` is odd), and `(x/p)=(q/p)=−1` because `(2/p)=1`.
This supplies no exact divisor hit.

The eligible multiples `x=qt` have `p/(4q)<t<p/(2q)`, hence number
`p/(4q)+O(1)`. Their moduli are

    a(t)=4qt−p=a₀+4q·(t−t₀),

where `t₀` is the smallest integer greater than `p/(4q)` and
`0<a₀<4q`, `a₀≡3 (mod 4)`. The first multiple lies below
`p/2` whenever `p>4q`. This makes `a₀` small, but does *not*
make either exact target appear in `D(qt₀;a₀)`.

## What *can* be proved for the first multiple: `q=5` or `7`

The following are **unconditional pointwise constructions for their
stated residue families**, not a construction for all primes. In each
case `good_of_typeI` yields a strictly ordered fraction identity.

* If `(5/p)=−1`, equivalently `p≡2,3 (mod 5)`, take
  `x=5(⌊p/20⌋+1)`. Then `a=4x−p` is `3` or `7` and the exact
  cofactor **`c=5`** works: `c|x²` and `4c+1=21`. The theorem
  `first_five_multiple_typeI` does not even require primality once
  the residue and hard-form assumptions are given.

* If `(7/p)=−1`, equivalently `p≡3,5,6 (mod 7)`, take
  `x=7(⌊p/28⌋+1)`. Now `a∈{11,15,23}`. When `a=11` or `23`,
  `x=(p+a)/4=6k+3` or `6k+6` is divisible by `3` as well as `7`.
  Hence **`c=63=3²·7`** divides `x²`, and
  `4c+1=253=11·23`. For `a=15`, we have `x=6k+4=14t`.
  The congruence `p=56t−15≡1 (mod 3)` gives `t≡2 (mod 3)`;
  since `p` is prime and `p>5`, `5∤t`. Thus
  `t mod 15 ∈{2,8,11,14}`, and the following *actual* cofactors
  cover all four cases:

      t mod 15          2     8     11     14
      c/t              28    7      1      4

  Each `c/t` divides `196`, so `c|x²=196t²`; also `c≡11 (mod 15)`,
  and therefore `15|4c+1`. The theorem
  `first_seven_multiple_typeI` checks all cases, and verifies
  `p<4x`, `2x<p` for both constructions. Notice that `c=63` often
  does **not** divide `x`; replacing the full criterion by `c|x`
  would lose this argument.

This supplies all hard primes whose least nonresidue is `5` or `7`.
It gives no uniform bound on the remaining least nonresidues.

## A certified miss at the *first* least-nonresidue multiple

Consider the hard prime `p=54121`. Its least nonresidue is **`q=13`**:
`p mod (5,7,11,13)=(1,4,1,2)` and the first three entries are
squares, while `2` is a nonsquare modulo `13`; `2,3` are residues
because `p≡1 (mod 24)`. The primality assertion has a short Lucas
certificate: `p−1=2³·3·5·11·41`, and for base `13` the modular powers
for exponents `p−1` and `(p−1)/r`, `r=2,3,5,11,41`, are respectively

    1; 54120, 18245, 53221, 32186, 31831.             (1)

The first is `1` and none of the others is `1`, so `13` has order
`p−1` modulo `p`, forcing `p` prime.

The first multiple of `13` after `p/4` is

    x=13533=3·13·347,   a=4x−p=11,   p/4<x<p/2.

Here `347` is prime. The nonresidue factor `q≡2 (mod 11)` is **a
primitive root modulo `a=11`**, with order ten. Nevertheless neither
(I) nor (II) holds at this `x`. Both target residues are `8 (mod 11)`:
`−4⁻¹=8`, and `−x=−3=8`. In the cyclic group generated by `2`,
`3≡2⁸`, `13≡2`, and `347≡6≡2⁹ (mod 11)`. Every divisor of
`x²` is `3^i 13^j 347^l`, with `0≤i,j,l≤2`; its discrete-log
exponent is

    8i+j+9l ≡ j−2i−l (mod 10),    −6≤j−2i−l≤2.

This range **excludes `3 (mod 10)`**, the log of `8`. Thus *all* 27
divisors miss the target, despite `27>φ(11)=10` and the primitive-root
factor. This is a failure of one candidate, **not** of the prime or of
all multiples of its least nonresidue: at `x=13532`, `a=7`,
`c=68|x`, and `4c+1=273=7·39`. At the later 13-multiple
`x=13559`, `a=115`, `c=2020291=149x|x²`, and
`4c+1=8081165=115·70271`.

The Lean declarations `least_quadratic_nonresidue_54121`,
`thirteen_primitive_mod_eleven`, `first_thirteen_multiple_54121_data`,
`no_types_54121_at_first_thirteen_multiple`, and `good_54121_at_13532`
check the stated primality, character, group order, first-multiple data,
**full** Type-I/II absence at that single `x`, and ordered escape.
The displayed later 13-multiple is also verified directly by the code below.


For an independently reproducible integer-only check of (1), the least
nonresidue, divisor box, and the two positive witnesses:

```python
from math import isqrt
p, q, x, a = 54121, 13, 13533, 11
assert p % 24 == 1 and p - 1 == 2**3 * 3 * 5 * 11 * 41
assert all(347 % r for r in (2, 3, 5, 7, 11, 13, 17))
assert pow(q, p-1, p) == 1
assert [pow(q, (p-1)//r, p) for r in (2, 3, 5, 11, 41)] == [
    54120, 18245, 53221, 32186, 31831]
assert all(pow(n, (p-1)//2, p) == 1 for n in range(1, q))
assert pow(q, (p-1)//2, p) == p-1
assert 4*x-p == a and p < 4*x < 2*p and x % q == 0
D = {3**i * 13**j * 347**l for i in range(3)
                             for j in range(3) for l in range(3)}
assert len(D) == 27 and {d % a for d in D} == set(range(1, 11)) - {8}
assert (-pow(4, -1, a)) % a == (-x) % a == 8
assert all((4*d+1) % a and (x+d) % a for d in D)
assert 4*13532-p == 7 and 13532 % 68 == 0 and (4*68+1) % 7 == 0
assert 4*13559-p == 115 and 13559 % 149 == 0
assert 2020291 == 149*13559 and (4*2020291+1) % 115 == 0
```

## Why the proposed general methods stop before an exact hit

* **Primitive roots and semigroups.** If a divisor `r|x` has order
  `m` modulo `a`, its powers *among divisors of `x²`* run only through
  `r^0,…,r^{2v_r(x)}`. The full cyclic subgroup is certainly covered
  if `2v_r(x)≥m−1`, but being a generator by itself supplies no such
  exponent bound. Several factors may create collisions; even
  `τ(x²)>φ(a)` does not imply either specified target belongs to the
  box (the example proves this directly). A useful *sufficient* but
  nonautomatic saturation criterion is in `LocalResidues.md`: divisors
  of a residue-supported `s²` cover all square classes modulo a prime
  `a≡3 (mod 4)`, and a nonresidue prime `q|x` coprime to `s` then
  supplies all nonsquare classes. Nothing ensures such an `s|x` for
  each prescribed `p` and some eligible `x`.

* **CRT and Jacobsthal.** Bounds on gaps between integers coprime to
  a fixed modulus cannot help with `gcd(a,x)`: it already equals `1`
  for every eligible `x`. CRT can force a chosen fixed prime into
  some `x=qt`, but `a(t)=4qt−p` changes with `t`, so neither
  `a(t)|4c+1` nor `a(t)|qt+d` follows. In particular, for a fixed
  `c`, the first divisibility requires `a(t)≤4c+1`; and the Type-II
  equation introduces a new, exact shifted divisor condition
  `4m−1|p+4d` with `d|m²` (`CoveringGap.typeII_modular_parameter`).
  No bound on a gap between convenient `t`-values forces those
  divisibilities. More decisively, for **every fixed** `B≥1`, there are
  infinitely many hard primes with no Type-II certificate of
  parameter `m≤B` (`CoveringGap.hard_primes_escape_bounded_typeII`).
  To see the exact obstruction, take Dirichlet primes
  `p≡1 (mod 24·lcm(1,…,4B))`. If `m≤B`, then `h=4m−1|p−1`, so a
  Type-II certificate would require `h|1+4d`, `d|m²`. Put `e=m²/d`.
  Since `16m²≡1 (mod h)`, the same assumption implies `h|1+4e`.
  As `h=4m−1`, these two positive divisibilities force `d,e≥m`;
  `de=m²` then forces `d=e=m`, but `1+4m=h+2` cannot be divisible
  by `h≥3`. This excludes only **bounded** `m`, not growing `m`.
  Dirichlet also gives primes `p≡1` modulo `24` and every prime
  `r≤T` for **any fixed `T`**; by reciprocity their least nonresidue
  exceeds `T`. Finite lists of small `q` or fixed modular parameters
  cannot cover all hard primes. None of these CRT facts obstructs
  *growing* parameters or Type I.

* **Burgess and interval character sums.** The classical unconditional
  least-nonresidue bound `q≪_ε p^{1/(4√e)+ε}` makes the window
  `p/(4q)<t<p/(2q)` have length
  `H≫_ε p^{1−1/(4√e)−ε}` for sufficiently large `p`.
  Pólya–Vinogradov gives
  `#{t: (t/p)=σ}=H/2+O(√p log p)` in this window for each
  `σ∈{−1,+1}` (with the appropriate rounding of `H`); the error
  is smaller than `H` for
  any fixed small `ε>0`. Burgess interval estimates can also
  control these *sign* counts. But `q|x=qt` already supplies a
  nonresidue factor regardless of `(t/p)`. None of these bounds
  places a divisor of `q²t²` into either **individual** target
  class modulo the *varying* `a(t)`. The first-multiple miss above
  already has a small modulus, a primitive root and `τ(x²)>φ(a)`;
  strengthening a sign count cannot reverse that local fact.

The exact character decomposition in `JacobiCorrectedJointCount.md`
makes a possible analytic route precise: write the count of *actual Type-I
plus Type-II pairs* as `C(p)=M(p)+T(p)`, where `M(p)` is its
principal-plus-Jacobi character contribution and admits a positive
pointwise cubic-log lower bound for sufficiently large `p`. An all-prime
proof would need the **one-sided pointwise** inequality `T(p)>−M(p)`
for every hard prime, or a different forcing
argument. Neither Burgess/Pólya–Vinogradov on ordinary intervals,
Jacobsthal, the finite semigroup examples, nor an averaged estimate
provides this inequality. The all-prime exact divisor covering in
`CoveringGap.all_good_iff_explicit_hard_cover` remains unproved.
