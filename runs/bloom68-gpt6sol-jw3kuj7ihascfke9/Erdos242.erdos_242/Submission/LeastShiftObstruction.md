# Least nonresidue-factor shifts: an exact local counterexample, not an ESC proof

**Status.** `LeastShiftObstruction.lean` gives sorry-free, strictly pointwise
counterexamples to the implications “the first nonresidue-factor shift supplies
a full Type-II witness using a factor of that shifted number” and “the first
eligible multiple of one of its nonresidue prime factors supplies either full
Type-I or full Type-II.” It also proves that the prime in question **does**
have a strictly ordered solution elsewhere. Neither implication is equivalent
to the unrestricted Erdős–Straus conjecture. `Submission/Spec.lean` was not
imported or modified.

## What works for shifts 1 through 4

Let `p≡1 (mod 24)` be prime, and `r` be an odd prime dividing `p+u`.
Quadratic reciprocity gives `(r/p)=(p/r)=(-u/r)`. The existing conditional
constructions really do convert a **negative** character into an ordered
solution when `u` is one of the first four shifts:

| `u` | consequence of `(r/p)=-1` | exact certificate |
|---:|---|---|
| 1 | `r≡3 (mod 4)` | `h=r=4m−1`, `d=m`, `h∣p+4d` |
| 2 | `r≡5` or `7 (mod 8)` | `h=3r` in the first case (since `3∣p+2`) or `h=r` in the second; `h≡7 (mod 8)`, `d=2m∣m²` |
| 3 | `r≡2 (mod 3)` and `r∣q₀=(p+3)/4` | the first denominator `x=q₀`, `a=3`, `c=d=r` gives both full types |
| 4 | `r≡3 (mod 4)` | `h=r=4m−1`, `d=1` |

The relevant strict size bounds follow from the previously proved
constructions (`SmallShiftRigidity.plus_two_shift_exact`,
`FirstDenominatorNorm.first_denominator_iff_inert_prime_factor`, and the
`p+1,p+4` shifted-divisor families). The sign is *not* by itself an
unrestricted Type-II witness: that family requires

```
h=4m−1 ∣ p+u,       d>0,       d∣m²,       4d<p,
                                   h∣p+4d, i.e. h∣(4d−u) in ℤ.
```

For arbitrary `u`, reciprocity identifies only the quadratic sign of
`−u (mod r)`; it supplies neither a factor `h≡3 (mod 4)` nor a divisor
of `m²` in the prescribed residue class. Independently, Type I/II at a
first denominator `x` require **one of two specific residues of divisors of
`x²`**, not merely some factor of negative character:

```
a=4x−p:     c>0, c∣x², a∣4c+1;   or
             0<d<x, d∣x², a∣x+d.
```

## The general least-shift observation and its limitation

Let `q` be the least positive quadratic nonresidue modulo a hard prime `p`.
It is itself prime. Since `p+q≡q (mod p)` has negative Legendre symbol,
multiplicativity of that symbol over the prime factorization of `p+q` forces
**some** prime factor of `p+q` to be a nonresidue. Thus the first shift `u`
with a nonresidue prime factor satisfies `u≤q`. This is true but is not an
absolute bound `u≤4` and does not identify a divisor of a square.

If `r∣p+u` is nonresidue and `1≤t<u`, then `r≥q≥u`, whereas
`gcd(p+t,p+u)∣u−t<r`; hence **the chosen prime cannot divide any earlier
shift**. Earlier-shift minimality says their *other* prime factors are
residues; it does not create an exact cofactor in `m²` or an exact Type-I/II
residue at an eligible `x`. One cannot obtain a modular witness by merely
combining the gcd observation and CRT.

## Explicit false intermediate at the *first* shift

The sorry-free Lean theorem `first_nonresidue_factor_shift_ten` proves that
`p=2784961` is prime, `p≡1 (mod 24)`, **all** prime factors of `p+t`
for `1≤t<10` have Jacobi/Legendre symbol `+1` modulo `p`, and

```
p+10 = 2784971 = 7·191·2083,
(7/p)=+1,       (191/p)=(2083/p)=−1.
```

`least_quadratic_nonresidue_2784961` separately certifies that `q=37`:
every `1≤n<37` is a residue, and `37` is a nonresidue. In particular
`u=10<q`; at `p+10` the **two** negative prime factors have even parity
and the whole number has positive Legendre symbol.

The concrete proposed intermediate

> At the least nonresidue-factor shift `u`, some divisor `h=4m−1` of
> `p+u` and some `0<d∣m²` with `4d<p` satisfy `h∣p+4d`

is **false**: `shift_ten_no_full_typeII_factor` proves its negation at
`(p,u)=(2784961,10)` with *all* divisors `d∣m²`, not just `d∣m` or
`d=um`; `least_shift_does_not_force_shifted_typeII` bundles this failure
with proof of leastness and a positive `Good p` certificate into one Lean
theorem. Factorization leaves exactly these possible moduli and targets:

| `h∣p+10`, `h≡3 (mod 4)` | `m=(h+1)/4` | required `d (mod h)` | available residues among `d∣m²` |
|---:|---:|---:|---|
| 7 | 2 | 6 | `{1,2,4}` |
| 191 | 48 | 98 | `{2^i3^j mod 191: 0≤i≤8, 0≤j≤2}`, none equal 98 |
| 2083 | 521 | 1044 | `{1,521,651}` |
| 2784971 | 696243 | 1392488 | impossible: `4d<p` makes `|4d−10|<h`, while `4d−10≠0` |

In particular, *each* nonresidue factor `191` and `2083` is already
`3 (mod 4)`: failure is the **exact square-divisor residue**, not a lack
of a factor with the right quadratic sign or congruence mod 4. The Lean
proof decomposes an arbitrary proposed factor of `7·191·2083` into prime
factors, and decomposes `d∣48²` as `2^i3^j` in the **full** exponent
range; the other cases are treated exactly.

There is a second, independent failure of a proposed extraction from the
same shift. The *first eligible multiples* of its nonresidue primes are

```
r=191:   x=696386=2·191·1823,   a=4x−p=583=11·53;
r=2083:  x=697805=5·67·2083,   a=4x−p=6259=11·569.
```

`first_shift_ten_nonresidue_multiples_fail` rejects **both complete types
at both candidates**. For `r=191`, Type I requires `c≡13 (mod 53)`,
which no divisor of `x²` attains. Type II needs `d≡34 (mod 53)` and
`d≡2 (mod 11)` simultaneously. Only exponent choices `(i,j,k)=(1,0,2)`
and `(1,2,0)` in `d=2^i191^j1823^k`, `0≤i,j,k≤2`, attain `34 (mod 53)`;
their residues mod 11 are `7` and `10`, not `2`. For `r=2083` all divisors
of `x²=5²·67²·2083²` are in `{1,3,4,5,9} (mod 11)`, but Type I requires
`8 (mod 11)` and Type II requires `2 (mod 11)`. These are failures of two
particular first denominators, **not** of all denominators.

Indeed `first_six_fibers_fail_and_escape` proves `j=0,…,5` fail **both
full types**, but `j=6` works via Type I:

```
x=696247=89·7823,    a=27,    c=7823∣x²,
4c+1=31293=27·1159,
4/2784961 = 1/696247 + 1/71817878050 + 1/2247303252494450.
```

`least_shift_ten_explicit_ordered_fractions` proves this exact equality
and strict order in Lean; the audit checks it independently with rational
arithmetic. Another Type-II modulus `h=47` works with `m=12,d=6` and
`47∣p+24`. Among **shifted-factor subfamilies**, all `p+t`, `1≤t≤15`,
miss but `767∣p+16` works with `m=192,d=4` (the last statement is an
exact finite audit, not claimed as a Lean theorem).

## The other mandatory stress primes and square control

`LeastShiftObstructionAudit.py` factors all indicated shifted numbers by
trial division, tests Legendre signs by Euler's criterion, enumerates **all**
divisors of every candidate's whole square, and checks ordered identities
with `Fraction`. It reports:

| prime `p` | least nonresidue `q` | first nonresidue-factor shift `u` | first successful `j`, exact full certificate |
|---:|---:|---:|---|
| 2521 | 11 | 2, with `p+2=3·29²` and `(29/p)=−1` | 5, `x=636`, Type II `d=8` (the `p+2` modulus `h=87,m=22,d=44` only gives another denominator, `x=638`) |
| 66529 | 13 | 5, with `p+5=2·3·13·853` and `(13/p)=(853/p)=−1` | 4, `x=16637`, Type I `c=2179447=131x>x`; also `h=39,m=10,d=50` uses `p+5` at later `x=17060` |
| 2784961 | 37 | 10, with `p+10=7·191·2083` and the two negative factors above | 6, `x=696247`, Type I `c=7823`; **no** Type-II modulus divides `p+10` |

The `p=2521,66529` positive witnesses are independently proved in the
existing Lean files `FirstDenominatorNorm.lean` / `CoveringGap.lean`;
the *firstness* of their respective `j` is certified by the independent
exhaustive square-divisor checks, not falsely attributed to those older
Lean theorems. The new `p=2784961` firstness **is** a Lean theorem.

Finally a square modulus is a decisive control, **not a counterexample**:
`square_modulus_never_has_negative_jacobi` proves for *every* `s,r` that
`(r/s²)=(r/s)²∈{0,1}`. Thus an odd square has no negative-Jacobi
prime-factor shift at **any** `u`. Yet `square_25_has_no_shift_factor_but_is_good`
proves the strictly ordered solution
`4/25=1/10+1/20+1/100`. A Legendre symbol is defined only for a prime
modulus; Jacobi is the proper square-modulus comparison.

**Precise remaining gap:** It is still unknown whether for every hard prime
`p=24k+1` there exists **some** `0≤j<6k`, with `x=6k+1+j`, `a=4j+3`,
and either `c∣x², a∣4c+1` or `0<d<x, d∣x², a∣x+d`. This is the complete
pointwise equivalence `CoveringGap.all_good_iff_explicit_hard_cover`.
Minimality of a nonresidue-factor shift controls quadratic signs of
factors of *nearby numbers*, not membership in either prescribed finite
divisor-residue set. The explicit prime above refutes two natural bridge
lemmas without claiming a counterexample to the conjecture.

Verification: `lake env lean Submission/LeastShiftObstruction.lean`,
`lake build Submission.LeastShiftObstruction`, and
`python3 Submission/LeastShiftObstructionAudit.py`. No `sorry`, new
axiom, `native_decide`, or import of `Submission.Spec` occurs in the new
proofs. `#print axioms` reports only the usual `propext`,
`Classical.choice`, and `Quot.sound`.
