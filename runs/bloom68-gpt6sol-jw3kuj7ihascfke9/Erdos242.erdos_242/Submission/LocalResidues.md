# Saturating divisor residues at small first denominators

**Scope.** These are exact, *pointwise conditional* criteria, not a proof or
counterexample to the Erdős–Straus conjecture. They do not edit `Spec.lean`.
The complementary-divisor identity and the new `a=7` sufficient construction
are checked without `sorry` in `LocalResidues.lean`; the classification they
use is checked in `Classification.lean`.

Let `p=24k+1` be prime. Necessarily `k>=3`. For a strictly ordered solution,
`p/4 < x < p/2`. The candidate first denominators are exactly

    x_j=6k+1+j,  a_j=4x_j-p=4j+3,  0<=j<6k.

Here `gcd(x_j,a_j)=1`. The proved ordered classification says that this `x_j`
works iff at least one of the following holds:

    (I)  c|x_j², c>0, a_j|4c+1;
    (II) d|x_j², 0<d<x_j, a_j|x_j+d.

For (I) use `x_j, (p*x_j+x_j²/c)/a_j, (p*x_j+p²*c)/a_j`; for (II) use
`x_j, p*(x_j+d)/a_j, p*(x_j+x_j²/d)/a_j`. Both triples are integers in
strictly increasing order. A counterexample must fail **both** branches for
**every** candidate `j`.

## A complementary-divisor identity

**Lemma (Lean-checked).** Suppose `a>2`, `x>0`, and `gcd(a,x)=1`. Then

    (exists d|x²: 0<d<x and a|x+d)
      iff (exists e|x²: e>0 and a|x+e).                       (1)

For the nontrivial direction, an `e` on the right cannot equal `x`, because
`a|2x` would imply `a|2`. If `e<x`, use `d=e`; if `e>x`, put `d=x²/e`.
Then `d<x` and `ed=x²`. Since `e≡-x (mod a)` and `x` is invertible,
`d≡x²/e≡-x (mod a)`. Equivalently, use the integral identity
`e(x+d)=x(x+e)` and `gcd(a,e)=1`. Thus **the order restriction on (II)
can be omitted when testing the residue set of *all* divisors of `x²`**;
it is recovered by pairing complementary divisors. This lemma is
`small_divisor_iff_divisor_of_coprime` in `LocalResidues.lean`.

## Quadratic-residue saturation

Let the candidate modulus `a=ell` be a prime `3 (mod 4)`, with
`ell∤x`. If **every** prime factor of `x` is a square modulo `ell`, both
(I) and (II) fail. Indeed every divisor of `x²` is then a quadratic
residue, while (I) requires `c≡-4⁻¹ (mod ell)`, a nonresidue, and (II)
requires `d≡-x (mod ell)`, also a nonresidue. Conversely, the presence of
a nonresidue prime factor *alone* need not make either required divisor
available.

Here is a sufficient hypothesis that fills that exact gap. Suppose `s|x`
has the property that **divisors of `s²` represent every quadratic-residue
class modulo `ell`**, and a prime `r|x` is a quadratic nonresidue and
`gcd(r,s)=1`. Then divisors of `x²` represent *all* nonzero residues:
use `e|s²` for squares, and `r*e|x²` for nonsquares (as `rs|x`).
In particular (I) is possible; (1) also makes (II) possible. If all
prime factors of `s` are quadratic residues, the `gcd` requirement is
automatic for every nonresidue prime `r`; in this case the following is an
**equivalence at that specific first denominator**:

    (I) holds  iff  (II) holds  iff  x has a nonresidue prime factor.   (2)

One convenient way to manufacture `s`: if a prime `t|x` generates the
quadratic-residue subgroup modulo `ell` (order `(ell-1)/2`) and
`t^v|x` with `2v >= (ell-3)/2`, take `s=t^v`. Then the divisors
`1,t,...,t^(2v)` of `s²` contain every square class. This is a
factorization criterion, **not** a guarantee that `x` has the required
prime factors for every `p`.

### The second first denominator: an exact new criterion

At `j=1`, `x_1=(p+7)/4=6k+2` is even, `a_1=7` and
`gcd(x_1,7)=1`. The squares modulo 7 are `{1,2,4}`, **exactly** the
residues of the divisors `1,2,4` of `2²`. Since `2` is a quadratic
residue, (2) applies with `s=2`. Consequently:

> **A solution with first denominator `x_1=6k+2` exists if and only if
> `x_1` has a prime divisor `r≡3,5,6 (mod 7)`. In that event both
> type (I) and type (II) witnesses exist at `x_1`.**

For a completely explicit (I) witness, choose

    c=4r if r≡3 (mod 7),  c=r if r≡5 (mod 7),
    c=2r if r≡6 (mod 7).                                (3)

The prime `r` is odd, so `2r|x_1`; hence `c|x_1²`, and in each case
`7|4c+1`. This construction is formalized as
`good_hard_of_second_nonresidue_prime` in `LocalResidues.lean`.
The converse is the quadratic-residue argument above: **failure at
`x_1` says only that all prime factors of `x_1` lie in `{1,2,4}`
modulo 7, not that `p` is a counterexample.**

The familiar sufficient congruence `p mod 7 ∈ {3,5,6}` follows since
`x_1≡2p (mod 7)` and `2` is a square. But it is *not necessary*:
`p=193≡4 (mod 7)` has `x_1=50=2*5²`, and `5` is a nonresidue
modulo 7. Formula (3), with `c=5`, gives the strictly ordered identity

    4/193 = 1/50 + 1/1450 + 1/27985.

By contrast, `p=2521` has `x_0=631` with no `2 (mod 3)` prime
factor, and `x_1=632=2³*79` with `79≡2 (mod 7)`. Thus neither of
the **first two** possible first denominators works; this does *not*
rule out later denominators.

### Third and sixth first denominators

At `j=2`, `x_2=6k+3` is always divisible by 3, and `a_2=11`.
The quadratic residues modulo 11 are `{1,3,4,5,9}`, exactly the
residues of `1,3,9,27,81`, all divisors of `9²`. Thus **if `9|x_2`**
(equivalently `p≡25 (mod 72)`), (2) applies with `s=9`:

    x_2 works  iff  some prime r|x_2 is 2,6,7,8 or 10 (mod 11),
    and then both (I) and (II) work.                        (4)

Even when `9∤x_2`, a factor `r≡7,8,10 (mod 11)` already supplies both
branches. Write `x_2=3rt`; the following choices have
`c|x_2²`, `11|4c+1`, `0<d<x_2`, `d|x_2²`, and `11|x_2+d`:

    r mod 11       7             8            10
    c             9r            r            3r
    d             t             9t           3t.

For `r≡8`, the prime `r>=19>3` ensures `9t<3rt`; all other strict
bounds are immediate. One cannot drop the additional residue/seed
condition: for `p=193`, `x_2=51=3*17` has a nonresidue prime
`17≡6 (mod 11)`, but its nine divisors of `51²` include neither
`8 (mod 11)` (required for I) nor `4 (mod 11)` (required for II,
since `-51≡4`). The same prime nevertheless works at `x_1`.
For another example, `p=3049` fails at `x_0=763=7*109` and
`x_1=764=4*191` (all factors are squares modulo the respective 3 and
7), but `x_2=765=9*5*17` satisfies (4): `17≡6 (mod 11)`, and
`d=5` gives

    4/3049 = 1/765 + 1/213430 + 1/32654790.

At `j=5`, `x_5=6(k+1)` is divisible by both 2 and 3, and `a_5=23`.
The quadratic residues modulo 23 are
`{1,2,3,4,6,8,9,12,13,16,18}`. Direct enumeration of divisors
shows **both** `12²=2⁴*3²` and `18²=2²*3⁴` have *exactly*
these eleven distinct residues. Since 2 and 3 themselves are squares
modulo 23, if `2|(k+1)` **or** `3|(k+1)`, condition (2) applies
with `s=12` or `18`, respectively. Under this hypothesis, `x_5`
works iff it has a prime quadratic nonresidue modulo 23, and both
branches work. Two examples are

* `p=1201`, `x_5=306=18*17`, with `17` a nonresidue, `d=108`:
  `4/1201=1/306+1/21618+1/61251`;
* `p=2521`, `x_5=636=12*53`, with `53≡7 (mod 23)` a nonresidue,
  `d=8`: **`4/2521=1/636+1/70588+1/5611746`**.

The latter new, earlier ordered witness, and the `3049` witness, are
independently checked as `good_2521_early` and `good_3049_third` in
`LocalResidues.lean`. At `p=66529` the first four candidates fail but
`x_4=16637` has a *type-I-only* witness `c=2179447`, yielding
`4/66529=1/16637+1/58254900+1/507708871715100`;
so type I cannot be discarded even when type II often works elsewhere.

**Necessary multiplicative restrictions on a hypothetical bad prime.**
Combining the first-denominator criterion with the preceding tests, any
counterexample `p=24k+1` would have to satisfy simultaneously:

* every prime factor of `6k+1` is `1 (mod 3)`;
* every prime factor of `6k+2` is in `{1,2,4} (mod 7)`;
* no prime factor of `6k+3` is `7`, `8`, or `10 (mod 11)`;
  if `p≡25 (mod 72)`, **every** prime factor of `6k+3`
  is in `{1,3,4,5,9} (mod 11)`;
* if `2|(k+1)` or `3|(k+1)`, **every** prime factor of `6(k+1)`
  is in `{1,2,3,4,6,8,9,12,13,16,18} (mod 23)`.

These are genuine necessary factorization constraints at *different*
integers, but they can hold together for a soluble prime and are not
sufficient to certify a counterexample: all other `x_j` and both types
still must be excluded. Even when **both conditional clauses are active**,
these restrictions are not sufficient: `p=58921` is prime, `k=2455`, and

    x_0=14731,             x_1=14732=2²*29*127,
    x_2=14733=3²*1637,     x_5=14736=2⁴*3*307.

Every displayed prime factor lies in the respective allowed residue
set; `p≡25 (mod 72)` and `2|(k+1)`. Nevertheless
`(x,d,a)=(14735,1225,19)` works, giving

    4/58921 = 1/14735 + 1/49493640 + 1/595337784.

## Verification and remaining obstruction

`lake env lean Submission/LocalResidues.lean` and
`lake env lean Submission/CoveringGap.lean` succeed, including the
Lean-checked residual example `good_58921_residual`. An independent
integer-factorization enumeration below `p<100000` checked (I), (II)
and the exact second-denominator criterion at **all 1181** hard primes
in that finite range; 873 of them pass it. For `p<150000`, 566 of
the hard primes have `9|x_2` (384 pass (4)), while 1130 satisfy the
`x_5` seed hypothesis (870 pass its nonresidue criterion). Exact
rational arithmetic checks every displayed ordered identity. These
finite counts are **checks of the proven *conditional* equivalences**,
not a proof that some condition must hold at an untested prime.

Neither residue saturation nor knowing that roughly half the unit
classes are nonresidues proves that the *factorization of at least one*
`x_j` supplies the required saturated seed **and** nonresidue prime
for every hard prime. At `p=193,x_2=51` even a nonresidue factor does
not hit either target. Moreover, the independently Lean-proved
`hard_primes_escape_bounded_typeII` in `CoveringGap.lean` supplies,
for every fixed bound `B`, arbitrarily large hard primes with no type-II
solution of parameter `m=(x+d)/(4x-p) <= B`. Neither that obstruction
nor any finite verification rules out other first denominators or type I;
a universal *pointwise* covering proof or a genuine prime failing both
criteria at **all** `0<=j<6k` remains missing.
