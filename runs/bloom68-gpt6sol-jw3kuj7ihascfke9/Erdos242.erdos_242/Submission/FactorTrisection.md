# Complementary Type-I factorizations for hard Erdős–Straus primes

**Scope.** The polynomial identities and conditional constructions below are
checked in `FactorTrisection.lean`, without editing or importing `Spec.lean`.
They do **not** prove an ordered decomposition for every prime
`p ≡ 1 (mod 24)`. For such a prime, `Classification.lean` proves the exact
criterion: for some `p/4 < x < p/2`, either

* **Type I:** `c | x²`, `c>0`, and `a=4x−p | 4c+1`; or
* **Type II:** `d | x²`, `0<d<x`, and `a | x+d`.

Both alternatives are required for a universal proof. The identities here
supply a new **factor test for Type I**, complementary to the existing
Type-II tests using `p+t`.

## A product identity, and how a cofactor of `p+t` chooses `x`

Suppose positive integers satisfy

    p+t=q s,      q+1=h t,      4c+1=h s,      h≥3, q>1.       (1)

Put `x=tc`, `y=qtc`, and `z=pqc`. Cancelling in (1) yields

    4x=p+s,       hp+1=4qc,
    4/p = 1/(tc) + 1/(qtc) + 1/(pqc).                         (2)

For clarity, the last equality follows from
`(q+1)/(qtc)+1/(pqc)=(hp+1)/(pqc)=4/p`.
The inequalities are **strict**: `x>0`, `q>1` gives `x<y`, and (1)
implies `t<p`, giving `y<z`. Indeed `hp+1=4qc`, `ht=q+1`, and
`q≥2,c≥1` imply `hp=4qc−1>q+1=ht`. Also `p<4x` and `2x<p`.
Crucially, `4x−p=s` and `c|x` (hence `c|x²`), while `s|4c+1`.
Thus this is specifically a **Type-I** witness at
`x=(p+s)/4`, where `s=(p+t)/q` is the *cofactor* of `q`.
The Lean theorems `typeI_ordered_of_factor_product`,
`good_of_factor_product`, and `typeI_good_of_shifted_factor` verify the
identity, order, and classification certificate for all natural parameters
satisfying (1); no primality hypothesis is used.

Here is a readily checked sufficient **factor residue** condition. If
`p≡1 (mod 4)`, `t>0` is **even**, and a divisor `q|p+t` satisfies

    q ≡ 3t−1 (mod 4t),                                        (3)

write `q+1=ht`; then `h≡3 (mod 4)` and `h≥3`. The factor `q` is odd.
Writing `s=(p+t)/q`, one has `s≡3 (mod 4)`: if `t≡0 (mod 4)`,
`q≡3 (mod 4)` and `p+t≡1 (mod 4)`; if `t≡2 (mod 4)`,
`q≡1 (mod 4)` and `p+t≡3 (mod 4)`. Thus `hs≡1 (mod 4)`, so
`c=(hs−1)/4` is a **positive integer** and (1) applies. This is a
sufficient test for a *specified* shift, not a theorem that every shift
has an eligible factor. For odd `t` the congruence alone need not give
`4 | hs−1`; the integral relation `4c+1=hs` must be checked separately.

The previously known Type-II `p+t` axis asks instead for a divisor
`q≡−1 (mod 4t)` (`ShiftSieveNotes.md`). These are distinct residue tests
at the specified shift. For `t=2`, they are `q≡7` and `q≡5 (mod 8)`,
respectively. `typeI_of_pplus_two_factor_five_mod_eight` formally proves
the Type-I test `p≡1 (mod 8), q|p+2, q≡5 (mod 8)`. This does **not**
yield an otherwise unknown all-primes result: for a **prime** factor
`q≡5 (mod 8)` of `p+2`, the hard-prime condition makes `3|(p+2)/q`,
and the composite factor `3q≡7 (mod 8)` already gives the existing
Type-II `t=2` solution. The present identity gives a different, genuine
Type-I witness.

One can also read (1) in reverse. Given Type I at some `x` with the
**extra condition `c|x`**, write `x=tc`, `s=4x−p`,
`h=(4c+1)/s`, and `q=ht−1`. For a hard prime, `s≡3 (mod 4)`,
`h≡3 (mod 4)`, hence `h≥3,q≥2`, and all three equations (1) follow.
So (1) repackages **exactly this subfamily of Type I**. General Type I
only requires `c|x²`, not `c|x`; e.g. the proven witness
`TypeI 97 34` with `c=68` is not covered at that first denominator.
Type II is different again. A pointwise proof that *every* hard prime
has a factor satisfying (1) would imply the open conjecture; no such
proof follows from the factorization.

## A particularly short new polynomial identity

For a hard prime `p=24k+1`, set

    M=(3p+1)/4=18k+1.                                        (4)

This is **odd** and `1 (mod 3)`. If `r|M` with `r≡2 (mod 3)`, its
cofactor `q=M/r` is also `2 (mod 3)`. Set

    x=(M+r)/3=r(q+1)/3,    y=q x,    z=pM.                  (5)

Then `x,y,z` are strictly increasing positive integers, and

    1/x+1/y = 3/M,   1/z=1/(pM),   3p+1=4M
       ==>  4/p = 1/x+1/y+1/z.                             (6)

This is Type I **with `c=r`**: `r|x`,
`4x−p=(4r+1)/3`, and `4r+1=3(4x−p)`. The Lean theorem
`hard_good_of_trisected_factor` supplies the exact first denominator
in (5). If `r` is the *least* prime factor of `M` that is `2 (mod 3)`,
then the cofactor `q≡2 (mod 3)` itself has such a prime factor, of size
at least `r`. Consequently `r²≤M` and this choice minimizes `x` **among
this particular family**:

    p/4 < x=(M+r)/3 ≤ (M+√M)/3.

There is no assertion that this is the smallest first denominator of
*all* decompositions. Restricting to the least prime factor is useful
for finding a small `x`, not for proving the factor exists.

Equivalently write `r=3u+2`, `q=3v+2`. Equation (4) gives the entirely
polynomial family

    p=12uv+8u+8v+5,
    x=(3u+2)(v+1),
    y=(3v+2)x,
    z=p(3u+2)(3v+2).                                      (7)

Here `4x−p=4u+3`, `p−2x=6uv+2u+4v+1>0`, and
`3p+1=4(3u+2)(3v+2)`. The identity and **all strict inequalities**
hold even for `u=v=0`: `4/5=1/2+1/4+1/20`.
`trisection_polynomial` and `good_trisection_polynomial` prove (7)
with `TypeI` in Lean. The Lean equivalence
`hard_polynomial_iff_aux_factor` proves precisely that a hard `p`
has representation (7) **iff `18k+1` has a factor `2 (mod 3)`**.
This equivalence is about (7), **not** an equivalence between that
factor condition and `Good p`.

There is even an exact characterization of the restricted choice of
**last** denominator `z=pM`. Indeed subtracting `1/(pM)` from `4/p`
leaves `3/M`. For any positive integer two-term split
`3/M=1/x+1/y`, one has

    (3x−M)(3y−M)=M²,       3x−M>0,
    3x−M ≡ −M ≡ 2 (mod 3).                                  (8)

Thus `M` must contain a prime `2 (mod 3)`; (5) supplies the ordered
converse. This does **not** exclude ordered solutions with another last
denominator, and it is not the full Type-I/II classification.

## Certified examples and stress tests

* **Residual hard prime `p=12721`**: Lean proves its primality and
  `p mod 840=121`, with

      x₀=(p+3)/4=3181 prime ≡1 (mod 3),
      p+1=2·6361,           p+2=3·4241,
      p+4=5²·509,           4p+1=5·10177.

  The listed odd factors of `p+1`, `p+4`, `4p+1` are primes `1 (mod 4)`;
  `4241≡1 (mod 8)`, so `p+2` has no `5` or `7 (mod 8)` factor.
  Thus the simplest shifted-factor tests and the first-denominator
  test do not yield a solution at this `p`. Nevertheless
  `M=9541=7·29·47`, so choose `r=29`, `q=329=7·47` and `(u,v)=(9,109)`.
  The **explicit, ordered Type-I** identity is

      4/12721 = 1/3190 + 1/1049510 + 1/121371061,
      4·3190−12721=39,   4·29+1=3·39.

  It is verified in Lean by `typeI_12721_trisected`,
  `good_12721_trisected`, `good_12721_explicit` and
  `residual_12721_factor_data`. The latter checks each displayed
  factorization and primality claim. This does **not** claim that
  `12721` is the first such prime or that no other construction works.

* **Failure of the `h=3` family at a soluble hard prime**:
  `p=2521` is prime, `M=1891=31·61`, and *every* divisor of `M` is
  `1 (mod 3)`. `no_trisected_factor_2521` and
  `not_trisection_polynomial_2521` certify that (7) cannot apply.
  Nevertheless `2521+2=29·87`, `29+1=15·2`, `4·326+1=15·87`.
  Formula (2) gives a **different** ordered Type-I solution

      4/2521 = 1/652 + 1/18908 + 1/23833534.

  This is checked by `typeI_2521_shifted` and
  `good_2521_typeI_explicit`. Its `p+2` factor `29≡5 (mod 8)` is
  *not* an eligible prime factor for the Type-II `7 (mod 8)` test;
  its composite factor `87=3·29` is eligible there, as already known.
  Also `p+4=5²·101`, `4p+1=5·2017` and `p+1=2·13·97` have no odd
  prime factor `3 (mod 4)`.

* **Even a failed `p+2` test is not a counterexample**: `p=5569` has
  `M=4177` prime `1 (mod 3)` and
  `p+2=3²·619`, with `619≡3 (mod 8)`; neither of the two preceding
  small families is available. With the **odd** shift `t=17`, however,
  `5569+17=798·7`, `798+1=47·17`, `4·82+1=47·7`, giving

      4/5569 = 1/1394 + 1/1112412 + 1/364413084.

  `typeI_5569_shifted` and `good_5569_typeI_explicit` check this
  Type-I solution. Its first denominator `1394` also has a different
  Type-II solution in `IndependentNotes.md`.

For small edges: `k=0` in (4) means `p=1`, which is not prime and has
`M=1`, so there is no eligible `r`. The first hard prime is `p=73`;
`M=55=5·11` gives `r=5` and the ordered identity
`4/73=1/20+1/220+1/4015`. Conversely `p=97` has
`M=73`, a prime `1 (mod 3)`, so it fails (7); the broader factor
test (1) still works with `(t,q,s,h,c)=(5,34,3,7,5)`, giving
`4/97=1/25+1/850+1/16490`. These checks do not extrapolate a
fixed-factor test to arbitrary primes.

## Why the other elementary forcing ideas do not close the gap

* **`n+4`, `p+1`, `4p+1`.** A divisor `3 (mod 4)` of `p+4` gives
  `Partial.good_of_three_mod_four_divisor`; an eligible divisor of
  `4p+1` gives the symmetric Type-II construction in
  `IndependentNotes.md`. But the exact factors at `p=12721` and
  `p=2521` show that all these odd divisors can be `1 (mod 4)`
  simultaneously. Multiplication by a small constant or swapping
  complementary divisors does not manufacture the missing residue.
  A factor of `p+t` must meet the *exact* residue and integrality
  conditions (1) or the existing Type-II criterion; being the least
  factor, by itself, does not do that (the least factor of `2521+2`
  is `3`, but the useful factors are `29` and `87`).

* **Continued fractions.** For `p=24k+1` with `k>0`, the rational
  number `4/p` has continued fraction `[0;6k,4]`. Rounding its first
  unit-fraction denominator gives `x₀=6k+1`, **not** the required
  Type-I/II divisibility. At `p=2521`, `x₀=631` is prime `1 (mod 3)`
  and has neither type of witness. The simple Euclidean expansion
  supplies no extra prime-factor forcing theorem; further candidate
  `x` must still satisfy `Classification.lean`.

* **Complement/involution and pigeonhole.** With `a=4x−p`, `N=px`,
  the exact ordered factorization is
  `(ay−N)(az−N)=N²`. Its natural involution sends a divisor
  `d` to `N²/d`; the integrality target `d≡−N (mod a)` is fixed
  under this involution, because the complementary factor has the
  same residue when `gcd(a,N)=1`. Pairing does **not** force a divisor
  into that residue. At `p=2521,x=631`, `a=3`, `N≡1 (mod 3)`, and
  every prime divisor of `N` is `1 (mod 3)`, so *all* divisors of
  `N²` miss `−N≡2 (mod 3)`. Even having more divisors than residue
  classes is insufficient: at `p=66529,x=16650,a=71`, all `225`
  divisors of `x²` miss **both** targets despite `225>71`
  (`PointwiseTypeICounting.md`). Merely expressing this hyperbola's
  involution using cotangents cannot turn a real/rational paired point
  into a divisor in the required integer residue class.

**Remaining problem.** Prove for **each** hard prime `p` that some
`p/4<x<p/2` satisfies **Type I or Type II**, or exhibit a genuine
prime and exclude both types at every such `x`. Explicitly, for
`p=24k+1` the unproved obligation is to find `j<6k` with
`x=6k+1+j`, `a=4j+3`, and **either** `c|x², a|4c+1`
**or** `0<d<x, d|x², a|x+d`. The Lean equivalence
`CoveringGap.all_good_iff_explicit_hard_cover` proves that this
*pointwise universal assertion* is exactly as strong as the original
ordered conjecture. Neither (3), the `h=3` factor condition, nor a
finite, density, character-sum or pigeonhole observation supplies it.
Claiming that every prime has an eligible factor of (1) would be a
**stronger** conjectural assertion (Type I with `c|x`) that implies the
open problem; it has not been proved by rearranging the identity.
