# Full Type I for nonsquares: a large exact bound and an infinite CRT subfamily

**Status.** I found **no nonsquare counterexample** and **no proof** of the
universal nonsquare assertion. In particular this is not a proof of the
Erdős–Straus conjecture. I did not edit `Submission/Spec.lean`. The *full*
condition here is `c | x²`, **not** `c | x`; no Type-II condition is silently
substituted for it.

## The square obstruction really is universal

Let `n=s²≡1 (mod 24)`, `n/4<x<n/2`, `a=4x−n`, and `c>0` divide `x²`.
Then `a≡3 (mod 4)` is odd. For each odd prime `r|x`, reciprocity, also
valid when the symbols vanish, gives

    (r/a) = (a/r)(−1/r) = (−n/r)(−1/r) = (n/r) = (r/n).

If `2|x`, `n≡1 (mod 8)` and `a≡7 (mod 8)`, so `(2/a)=(2/n)=1`.
Multiplicativity therefore yields `(c/a)=(c/n)`. But `a|4c+1` implies
`(c/a)=(−1/a)=−1`, whereas `(c/n)=(c/s)²∈{0,1}`. Contradiction. This
excludes **all** full Type-I certificates for every such square, with no
primality or coprimality shortcuts. The more general Jacobi transfer and this
square theorem have already been checked in `PointwiseJacobi.lean`.
For example, `25` has no Type I but `4/25=1/10+1/20+1/100`: a square
obstruction does **not** disprove the original three-unit-fraction claim.

## Genuine infinite partial theorem: four tiny moduli

**Proposition.** Put `n=24k+1`, `k≥1`. If ANY of the following holds, a
full Type-I certificate occurs already at the indicated `j`, with
`x=6k+1+j`, `a=4j+3` and `n/4<x<n/2`:

| case | exact congruence hypotheses | `j`, `a` |
|:--|:--|:--|
| A | `n mod 5 ∈ {2,3}` | `0`, `3` if `2`; `1`, `7` if `3` |
| B | `n mod 7 ∈ {3,5,6}` | `1`, `7` |
| C | `k≡1 (mod 3)` and `n mod 11 ∈ {2,6,7,8,10}` | `2`, `11` |
| D | `2|(k+1)` or `3|(k+1)`, and `n mod 23 ∈ {5,7,10,11,14,15,17,19,20,21,22}` | `5`, `23` |

In A, take `c=5`: if `n≡2 (mod 5)`, then `n≡17 (mod 20)` so
`5|(n+3)/4`; if `n≡3 (mod 5)`, then `n≡13 (mod 20)` so
`5|(n+7)/4`. In both cases `4c+1=21` is divisible by the stated `a`.

For B–D, let `q=a∈{7,11,23}`. The displayed classes are precisely the
quadratic *nonresidues* modulo `q`. Since `4x≡n (mod q)`, `(x/q)=−1`.
Thus some prime `r|x` is a nonresidue mod `q`. Find a **residue-supported**
divisor `d|x²` such that `r d ≡ −4⁻¹ (mod q)`; then `c=rd|x²`
(the prescribed small primes in `d` are residues, so none is `r`).
All the necessary residue sets are exact finite identities:

* B: `x=6k+2` is even and `{2^i mod 7:0≤i≤2}` is the entire
  quadratic-residue subgroup `{1,2,4}`. The target is `5 (mod 7)`.
* C: `x=6k+3=3(2k+1)`; `k≡1 (mod 3)` gives `9|x`. The powers
  `{3^i mod 11:0≤i≤4}={1,3,4,5,9}` cover every quadratic residue.
  The target is `8 (mod 11)`.
* D: `x=6(k+1)`; if `2|(k+1)` then `12|x`, and the residues of
  `2^i3^h` for `0≤i≤4, 0≤h≤2` cover the eleven quadratic residues
  modulo 23. If `3|(k+1)`, then `18|x`, and instead
  `0≤i≤2, 0≤h≤4` has the same property. Both `2` and `3` are
  quadratic residues modulo 23. The target is `17 (mod 23)`.

In every case the allowed exponents ensure `d|x²`, not merely a residue
match. The subgroup identities and each constructed certificate for one full
CRT period are also checked with integer arithmetic in
`NonsquareTypeICRT.py`. The corresponding exponent-box argument is a genuine
proof for *all* integers in these classes, not an extrapolation from this
finite check. Since each case has `n` a nonresidue modulo at least one prime,
**none of the covered integers is a square**.

CRT on `k mod (6·5·7·11·23)=53130` gives **42822 of 53130** classes
covered by A–D, a relative natural density of `7137/8855 ≈ 80.5985%`
among *integers* `n≡1 (mod 24)`. An elementary count: after A and B,
the uncovered proportion is `(3/5)(4/7)=12/35`. For `k mod 6` equal
to `0,1,2,3,4,5`, respectively, the extra probabilities of *missing*
C and D are `1, (6/11)(12/23), 12/23, 12/23, 6/11, 12/23`.
Averaging yields the uncovered fraction `(12/35)(859/1518)=1718/8855`.
If one invokes the prime number theorem in fixed arithmetic progressions,
then among **hard primes** (`p≡1 (mod 24)`) the corresponding relative
density is `83/96`: in reduced classes the nonresidue proportions modulo
each of `5,7,11,23` are `1/2`, and the remaining fraction is
`(1/2)(1/2)(13/24)=13/96`. Neither density gives pointwise coverage.

## Exhaustive finite result, with the full divisor condition

`NonsquareTypeIAudit.cpp` is an exact, self-checking certificate for:

> Every nonsquare `n≡1 (mod 24)` with `25≤n≤10^10` has a Type-I witness
> at some `x=(n+3)/4+j`, `0≤j≤39`, `n/4<x<n/2`.

Run from the repository root:

```sh
g++ -std=c++17 -O3 -Wall -Wextra -o /tmp/nonsquare_typei Submission/NonsquareTypeIAudit.cpp
/tmp/nonsquare_typei 10000000000 64
```

Observed output: `nonsquares=416633334`, `squares=33332` (skipped by
the Jacobi theorem), `no_witness_in_first_J=0`, `max_first_j=39`
at `n=3153865`. The number of visited `n=24k+1`, `k≥1`, is exactly
`416666666`; the two counts sum to it. The program tests all
`0≤j<min(6k,64)`, not a selected list of cofactors: it factors each
`x` by a deterministic smallest-prime-factor sieve, and for each
`p^e||x` builds **all achievable residues** of divisors of `x²`
using exponents `0,…,2e`. Factors common to `a` can safely be omitted,
since a successful `c` must be coprime to `a`. A hit carries a saved
integer `c`, and assertions check `c>0`, `c|x²`, `a|4c+1` with
128-bit exact arithmetic; assertions must remain enabled. Since
**every** nonsquare hits by `j≤39`, the finite result does *not* rely
on an untested assumption about later `j` or about 64 being a universal
cutoff. The sieve uses about 10 GB RAM for the stated bound.

An independent Python method in `NonsquareTypeIIndependent.py` literally
enumerates **all** divisors of each `x²` (rather than using the C++ residue
DP). It checks every nonsquare `n≤30000`, exhausts every eligible `x`
for all 57 squares in that small interval, confirms the first-success
indices of the stubborn examples, and checks 1000 reproducibly sampled
inputs near `10^10`. This cross-check does not replace the C++ exhaustive
bounded verification.

The latest first-success record within the bound is a **nonsquare
composite with a square prime factor**, not an exception:

    n=3153865=5·11²·13·401,   x=788506=2·109·3617,
    a=4x−n=159,   c=3617 | x²,   4c+1=14469=159·91.

This example is **outside all four** small-modulus sufficient families:
`n mod (5,7,11,23)=(0,1,0,13)` and `k mod 6=5`.
The independent explicit-divisor audit checks that all 39 earlier
eligible `x` fail at this `n`. The audit genuinely tests the **full**
`c|x²` box: at `n=3985`, its first hit is `x=1003=17·59`,
`a=27`, `c=59177=59x>x`; `c∤x` but `c|x²` and
`4c+1=236709=27·8767`. Adjoining square factors does not reproduce
the obstruction for actual squares: e.g. even `n=7²·73=3577` has
`x=895`, `a=3`, `c=179`.

**Limit.** The statement for *every* nonsquare `n` is unresolved by
these arguments; a counterexample, if any, must exceed `10^10` and
miss all four proven CRT families (in addition to passing every actual
full-divisor test). Neither the finite bound nor the density theorem
is promoted to a universal assertion. A prime counterexample to this
Type-I-only claim would still not automatically disprove the original
Type-I-or-Type-II Erdős–Straus conjecture, and a composite counterexample
would not disprove the original prime reduction either.
