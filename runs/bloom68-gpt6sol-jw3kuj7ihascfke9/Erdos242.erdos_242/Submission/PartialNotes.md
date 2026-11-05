# Erdős–Straus: proved partial results and the remaining obstacle

The Lean theorems cited below are checked in `Submission/Partial.lean`. They
prove statements about **strictly increasing**, positive denominators, without
assuming Erdős–Straus. This note does not claim to settle the conjecture.

## An explicit shifted-divisor family

**Theorem.** Let `n ≥ 4` and let `q | n+4` satisfy `q ≡ 3 (mod 4)`; `q` need
not be prime. Set `m=(q+1)/4` and

    x=(nm+1)/q,  y=nm,  z=nm x.

These are integers with `1 ≤ x < y < z` and `4/n=1/x+1/y+1/z`.

**Proof.** Writing `q=4m−1` and reducing `n+4` modulo `q` gives
`nm+1 ≡ −4m+1 ≡ 0 (mod q)`. Therefore `qx=nm+1`. Since `n≥4`,
`nm+1>q`, so the integer `x` is at least 2. Also `q≥3` and `nm≥4`, so
`qx=nm+1<qnm`, whence `x<nm=y`; and `y<yx=z`. Finally

    1/x + 1/(nm) + 1/(nm x)
      = (nm+x+1)/(nm x)
      = (4m x)/(nm x) = 4/n,

using `(4m−1)x=nm+1`. This is formalized by
`good_of_shifted_divisor` and `good_of_three_mod_four_divisor`.

In particular the family handles every `n≥4` for which `n+4` has a prime
factor `3 (mod 4)`. Its converse is **not** asserted: the absence of such
a factor does not make `4/n` insoluble.

## Density-one corollary among hard primes (ordinary mathematical proof)

**Theorem.** Among primes `p ≡ 1 (mod 24)`, the primes handled by the
shifted-divisor family above have relative density **one**. In fact this
holds after restricting to any fixed primitive prime progression.

**Proof.** Let `S` be a finite set of primes `q ≡ 3 (mod 4)`, `q≥7`,
put `Q=∏_{q∈S}q`, and count primes `p ≡ 1 (mod 24)` for which no
`q∈S` divides `p+4`. Each prime `p` in this class lies in a reduced
residue class modulo `24Q`. For each `q∈S`, of its `q−1` possible nonzero
residues, exactly one, `−4`, is forbidden. The Chinese remainder theorem
and the prime number theorem in arithmetic progressions therefore give

    lim_{X→∞} #{p≤X: p≡1 (mod 24), q∤p+4 for all q∈S}
               / #{p≤X: p≡1 (mod 24)}
      = ∏_{q∈S} (1−1/(q−1)).

The reciprocal sum `∑_{q≡3 (mod 4)}1/q` diverges, e.g. by the prime
number theorem in progressions modulo 4 and partial summation. Hence the
finite products on the right tend to zero as `S` increases. The set
avoiding **every** such `q` is contained in each of the sets counted
above, so its upper relative density is zero. The proof for any fixed
reduced progression `p≡a (mod A)` is the same after excluding the
finitely many `q | A` and `q=3`. (This density corollary is proved on
paper using the indicated standard analytic theorem; it is **not**
formalized in Lean here.)

Existing literature gives stronger density-one results, including
Elsholtz–Tao, *Counting the number of solutions to the Erdős–Straus
equation on unit fractions* (arXiv:1107.1010). No novelty is claimed
for the density assertion.

## Improved finite prime reduction

For a hard prime `p≡1 (mod 24)`, the already-proved type-II witness lemma
with `(m,d)=(2,1),(2,2),(2,4)` handles `p mod 7 ∈ {3,5,6}`; with
`(m,d)=(4,2),(4,8)` it handles `p mod 5 ∈ {2,3}`. Prime coprimality and
the CRT leave exactly the six residue classes

    p mod 840 ∈ {1,121,169,289,361,529}.

The `m=3`, `d∈{1,3,9}` cases also handle `p mod 11 ∈ {7,8,10}`.
Consequently fixed parameters `m∈{2,3,4}` cover `33/40` of all primes
`p≡1 (mod 24)` in the relative-density sense (CRT plus PNT in AP).
Theorems `good_prime_outside_six_840`, `good_of_six_prime_classes`,
`good_of_mod11`, and `good_of_residual_prime_cases` are proved in Lean.
The six classes modulo 840 are classical, not a new result: compare
Ionascu–Wilson, *On the Erdos-Straus conjecture* (arXiv:1001.1100).

## Why finite modular families do not close the gap

For `m,d>0` with `d|m²`, put `h=4m−1`. Then **`h∤1+4d`**:
let `a=m²/d`. If `h|1+4d`, then

    (1+4d)(4a) − (4m−1)(4m+1) = 4a+1,

so `h|1+4a` as well. Positive divisibility `h|1+4d` and `h|1+4a`
forces `d≥m` and `a≥m`. As `da=m²`, this gives `d=a=m`. But then
`1+4d=h+2`, impossible for `h≥3` to divide. Consequently
`p≡1 (mod h)` excludes **all** the proposed `d` for this `m`.
The theorems `not_one_modular_divisor` and
`no_modular_divisor_if_one_remainder` formalize these assertions.

More strongly, for any proposed bound `B`, take
`L=840·(4B)!`. Dirichlet's theorem produces arbitrarily large primes
`p≡1 (mod L)`. For every `1≤m≤B`, `4m−1 | L`, hence
`p≡1 (mod 4m−1)` and no `d|m²` can meet `4m−1 | p+4d`.
This is formally proved in
`hard_primes_escape_bounded_modular_parameters`, using Mathlib's
proved Dirichlet theorem. This **only** excludes this restricted
parameter family for bounded `m`: it does not exclude other type-II
constructions, type-I solutions, or the Erdős–Straus conjecture.

## Exact open remainder for these methods

`good_of_residual_prime_cases` proves that it would suffice to handle
primes satisfying *all* of the following:

1. `p mod 840 ∈ {1,121,169,289,361,529}`;
2. `p mod 11 ∉ {7,8,10}`;
3. **no** divisor `q≡3 (mod 4)` of `p+4` (equivalently, `p+4` is a
   product of primes `1 (mod 4)`).

This remainder is a zero-density subset of the hard primes, **not** an
empty set proven by density. The missing step is to exhibit an ordered
Erdős–Straus decomposition for *every* such prime (perhaps using
unbounded `m,d` or a different type-I parametrization), or to provide
a genuine prime counterexample and prove no solutions of either type
exist. No finite check or density argument establishes that step.

The proposed parametrization `p=s²+24k`, `h=s+t=4m−1` is examined
separately in `Submission/SquareRootNotes.md`, with Lean-checked bounds
and a finite counterexample to the search restriction `s≤h≤4s`.

