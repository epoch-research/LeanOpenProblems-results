# Least negative Jacobi index: a joint bounded-transfer counterexample

**Scope.** The proposed *specific* uniform rule `f(t)=t²` is false, even if
its conclusion is strengthened to allow **either** full type at every first
denominator `j≤f(m₀)`. This does not rule out a different, larger function
`f`, prove the conjecture, or produce a bad prime. The exact finite certificate
is independently reproducible with **only Python's standard library**:
`python3 Submission/LeastJacobiTransferAudit.py`. Its primality checks use
trial division; no heuristic primality or floating-point test is used. Neither
this note nor the audit modifies or imports `Submission/Spec.lean`.

## The global implication that reciprocity actually gives

For a hard prime `p≡1 (mod 24)`, let `h_m=4m−1`, and let `m₀` be the
least positive `m` with Jacobi `(p/h_m)=−1` (equivalently `(h_m/p)=−1`,
by reciprocity). For any `d|m²`, `gcd(d,h_m)=1` and `(d/h_m)=+1`:
if an odd prime `r|m`, then `h_m≡−1 (mod r)` and Jacobi reciprocity gives

    (r/h_m) = (−1/r)(h_m/r) = (−1/r)² = +1;

if `2|m`, then `h_m≡7 (mod 8)` and `(2/h_m)=+1`. Consequently the exact
Type-II congruence implies

    h_m | p+4d  =>  (p/h_m) = (−4d/h_m) = −1  =>  m≥m₀.       (1)

The **converse of (1) is not valid**. The missing arithmetic is precisely

    d | m²,       d ≡ −p·4⁻¹ ≡ −mp (mod 4m−1),       4d<p.       (2)

Here `4m≡1 (mod 4m−1)`, so `m` is the **exact** inverse of `4`;
there is no square-root or character-only substitution for (2).
The sign in (1) merely puts the target in the Jacobi-`+1` half in which
square divisors lie; it need not put the target in their *finite residue set*.
For composite `h_m`, a positive Jacobi symbol does not even guarantee an
ordinary modular square root: at the prime `p=1873` one has `m₀=4`,
`h_{m₀}=15`, and target `−p·4⁻¹≡8 (mod 15)`. Although `(8/15)=+1`,
`8≡2 (mod 3)` has no square root; nevertheless `d=8|4²` **is** an
actual witness (`15|1873+32`). Thus replacing (2) by a square-root
criterion would also lose valid witnesses. A full modular witness with
`4d<p` gives a strictly ordered solution by
`Reduction.good_of_modular_witness`.

There is a modest positive consequence of the least-index viewpoint:
`m₀=2` **does** give a witness at `m=2`. Indeed the negative residues
`p mod 7` are `{3,5,6}`, exactly `−4d mod 7` for `d∈{1,4,2}⊂Div(2²)`.
Also `m₀=4` gives a witness at `m=4`: as `(p/3)=+1`, negativity
`(p/15)=−1` implies `p mod 15∈{7,13}`, hit respectively by
`d=2` or `d=8`, both dividing `4²`. For hard primes `p≥73`, these
choices satisfy `4d<p`. These two small-index successes **do not extend**
to `m₀=3`.

For first-denominator indices `j<m₀−1`, write `x_j=(p+4j+3)/4` and
`a_j=4j+3`, and assume the usual eligible range `j<6k`, `p=24k+1`.
Since `a_j<p` and `p` is prime, `gcd(a_j,x_j)=1` (a common prime
factor would divide `4x_j−a_j=p`). Minimality and `4x_j=p+a_j` yield

    (p/a_j)=+1,         (x_j/a_j)=+1.                         (3)

Either full Type I (`c|x_j²`, `a_j|4c+1`) or Type II
(`d|x_j²`, `a_j|x_j+d`) would force a **negative-Jacobi divisor** of
`x_j²` modulo `a_j`: in Type I `(c/a_j)=−1`; in Type II
`(d/a_j)=−(x_j/a_j)=−1`. Because `(x_j/a_j)=+1`, the prime
factorization of `x_j` must then have at least two negative-Jacobi prime
factors **counted with multiplicity**. This is a genuine restriction on
early fibers, not a guarantee that a later fiber meets (2) or Type I.
The matching index `j=m₀−1` has `(x_j/a_j)=−1`, but still does not force
either target residue: see the `j=2` row below.

## A concrete false joint transfer: `f(m₀)=m₀²`

Consider the prime

    p=1915201=24·79800+1,     m₀=3,     x₀=(p+3)/4=478801.

For a short optional primality certificate, `p−1=2⁶·3²·5²·7·19`,
`11^(p−1)≡1 (mod p)`, and the powers `11^((p−1)/q) mod p` for
`q=2,3,5,7,19` are respectively
`1915200,1662771,1682006,699949,1084060`, none equal to one. Hence
`11` has order `p−1`, implying `p` is prime; the audit *also* checks
primality by trial division through `⌊√p⌋=1383`.
The Jacobi signs at `h_1=3`, `h_2=7`, `h_3=11` are `+1,+1,−1`:
`p≡1 (mod 3,7)` and `p≡2 (mod 11)`, where 2 is a nonresidue.
Thus `m₀=3` **exactly**, not an assumed upper bound.

**The entire modular search through `m=11` fails.** By (1), sign `+1`
excludes `m=1,2,4,5,7,9,11`. For the four indices having sign `−1`
below, the *complete* sets `{d mod h_m : d|m²}` miss the required
residue `t_m=−p·4⁻¹ mod h_m`:

| `m` | `h_m` | `t_m` | all available divisor residues modulo `h_m` |
|---:|---:|---:|---|
| 3 | 11 | 5 | `{1,3,9}` |
| 6 | 23 | 8 | `{1,2,3,4,6,9,12,13,18}` |
| 8 | 31 | 18 | `{1,2,4,8,16}` |
| 10 | 39 | 32 | `{1,2,4,5,10,11,20,22,25}` |

In fact for `m≤11` this rejects **all** `d|m²`, whether or not `4d<p`.
For instance, the negative sign at `m₀=3` needs `d≡5 (mod 11)`,
whereas `d|9` has residues only `1,3,9`. This already refutes the
naïve transfer at `m₀`, but the simultaneous bound below is stronger.

**Every full Type I *and* Type II fiber with `0≤j≤10` fails.** In the
following table, the displayed factors are *verified primes* (including
large single factors). For `x_j=x₀+j`, set `a_j=4j+3`. Each positive
divisor of `x_j²` has the form `∏r_i^e_i` for the displayed factorization
`x_j=∏r_i^{v_i}`, with **every** `0≤e_i≤2v_i` included. The two target
residues `(-4⁻¹, -x_j) mod a_j` are absent from those boxes:

| `j` | `x_j` (prime factorization) | `a_j` | Type-I, Type-II targets | complete divisor residues modulo `a_j` |
|---:|---|---:|---|---|
| 0 | `478801` | 3 | `(2,2)` | `{1}` |
| 1 | `2·53·4517` | 7 | `(5,5)` | `{1,2,4}` |
| 2 | `3·13·12277` | 11 | `(8,5)` | `{1,2,3,4,6,7,9}` |
| 3 | `2²·119701` | 15 | `(11,11)` | `{1,2,4,8}` |
| 4 | `5·17·43·131` | 19 | `(14,14)` | `{1,4,5,6,7,9,11,16,17}` |
| 5 | `2·3·79801` | 23 | `(17,8)` | `{1,2,3,4,5,6,7,9,10,11,12,13,14,15,16,18,19,21,22}` |
| 6 | `7·73·937` | 27 | `(20,11)` | `{1,4,7,10,13,16,19,22,25}` |
| 7 | `2³·11·5441` | 31 | `(23,18)` | `{1,2,4,7,8,11,13,14,16,19,21,22,25,26,28}` |
| 8 | `3²·53201` | 35 | `(26,26)` | `{1,3,9,11,27}` |
| 9 | `2·5·47881` | 39 | `(29,32)` | `{1,2,4,5,7,8,10,11,14,16,17,20,22,23,25,28,31,34,35,37}` |
| 10 | `478811` | 43 | `(32,37)` | `{1,6,36}` |

This checks **all divisors of the whole squares**, not just divisors of
`x_j` or a restricted `d|m`. The Type-II size restriction `d<x_j` is
irrelevant when the target is absent even among *all* square divisors.
It follows that the explicit proposed transfer

> Every hard prime with least negative-Jacobi index `m₀` has either a
> complete Type-II modular witness with `m≤m₀²`, or a complete Type-I
> witness at some eligible `j≤m₀²`

is **false**: here `m₀²=9`, but both branches fail even through `m=11`
and `j=10`, respectively. More strongly, there is no ordered solution
with *any* first denominator at these first eleven indices (the full
Type I/II classification), not just a Type-I miss.

**Escapes are explicit; this prime is not an ESC counterexample.** At
`j=11`, `x=478812`, `a=47`, `c=239406|x²`, `d=24|x²`, `d<x`,
`47|4c+1=957625`, and `47|x+d=478836`: *both* full types succeed.
At `m=12`, `d=24|12²`, `4d=96<p`, and

    h=47 | p+4d=1915297=47·40751,
    (x,y,z)=(488988, 22982412, 468255153294),
    0<x<y<z,            4/p=1/x+1/y+1/z.

For a direct Euclidean check, `47x=pm+d`, `x+d=12·40751`, and
`p+40751=4x`. Hence, with `z=p(mx/d)`, the fraction sum is
`(pm+x+d)/(pmx)=12(p+40751)/(12px)=4/p`; also `x<pm<z`
because `x>d=24`. The `m=12` witness has first-denominator index
`10187`, not `j=11`:
the two escapes are distinct and both are checked by exact rational
arithmetic in the audit. Negative Jacobi, leastness, quadratic-size
allowances, and these Euclidean identities do **not** force an earlier
exact divisor residue. Conversely, this *one finite counterexample* cannot
exclude a larger `f(m₀)` or an all-prime argument combining all growing
indices. The old CRT obstruction to **fixed absolute** `m` likewise does
not rule out an `m₀`-dependent bound, since its constructed `m₀` can
grow. The outstanding requirement is still a successful full Type-I
or Type-II fiber for **each** hard prime.
