# A common Jacobi obstruction for both full Erdős–Straus divisor criteria

**Status.** Every named assertion below has a sorry-free Lean proof in `PointwiseJacobi.lean`. The file imports the existing independent helpers, **not** `Submission/Spec.lean`, and supplies **necessary local conditions**, not a proof or a prime counterexample to the universal conjecture. Unlike `BilinearFactor.lean`, its central lemmas use the **full** condition `c∣x²`, not `c∣x`.

## Character transfer along a first denominator

Let `p≡1 (mod 8)`, `a≡3 (mod 4)`, and `a+p=4x`. For **every** positive divisor `c∣x²`, Lean proves (`jacobi_divisor_transfer`)

    (c/a) = (c/p),                                             (1)

where both sides are Jacobi symbols; no primality or coprimality of `p,a,c,x` is assumed. In fact the statement also allows `c=1`, and its hypotheses themselves rule out `c=0`.

Proof at the level of prime factors: if an odd prime `r∣c`, then `r∣x`, hence `a≡−p (mod r)`. Quadratic reciprocity, `p≡1 (mod 4)` and `a≡3 (mod 4)` make the two minus signs cancel, giving `(r/a)=(p/r)=(r/p)`, even if either side vanishes. If `r=2`, then `2∣x` gives `a≡−p≡7 (mod 8)`; both `(2/a)` and `(2/p)` are `+1`. Multiplication over all prime factors, with their actual exponents, proves (1). The private prime-factor lemma and strong induction on `c` are both checked in Lean.

## Exact consequences for Type I **and** Type II

For `p<4x`, put `a=4x−p`. Since `a≡3 (mod 4)`, `(−1/a)=−1` and `(4/a)=1`. An actual Type-I cofactor `c>0`, `c∣x²`, `a∣4c+1` therefore has

    (c/a)=−1,          **(c/p)=−1**.                       (Iχ)

This is `typeI_cofactor_jacobi_neg_one`; it applies also to composite `p≡1 (mod 8)` and does **not** impose `c∣x`. Factoring the negative-character `c` yields an **odd prime** `r∣x` with `(r/p)=−1` (`typeI_has_odd_prime_nonresidue`). The factor `2` is automatically a residue when `p≡1 (mod 8)`.

An actual Type-II divisor `d>0`, `d<x`, `d∣x²`, `a∣x+d` satisfies `(d/a)=(−x/a)=−(x/a)`. Applying (1) to *both* `d` and `x` gives the exact identity

    **(d/p) = −(x/p)**.                                    (IIχ)

`typeII_divisor_jacobi_opposite` needs only `d∣x²` and `a∣x+d`, not the size condition `d<x`. For a **prime** `p` and `0<x<p`, `(x/p)=±1`, so (IIχ) implies that either `d` or `x` has negative character. A prime factor of that number is again an odd nonresidue divisor of `x` (`typeII_has_odd_prime_nonresidue`). For hard numerators `p=24k+1`, both `2` and `3` have symbol `+1` modulo `p`; `hard_types_need_large_nonresidue` proves that success of *either full type* at any ordered candidate forces

    ∃ prime r≥5 with r∣x and (r/p)=−1.                      (2)

This is a **necessary**, by no means a sufficient, way to prune candidate denominators. The full pointwise sieve `no_types_if_prime_factors_residue` states: if a hard prime's candidate `x` has only Jacobi-`+1` prime factors, **neither** type works **at that x**. It does not assert failure at every `x` of that prime.

One rigorously Lean-checked illustration is

    p=66529 (prime, 1 mod 24),  x=16650=2·3²·5²·37,
    a=4x−p=71.

Each of `2,3,5,37` has symbol `+1` modulo `66529`. Thus `no_types_66529_at_16650` excludes **both full types at this single eligible first denominator**, even though `x²` has `(3)(5)(5)(3)=225` divisors. This is **not** a counterexample: `good_66529_via_different_x` verifies the *distinct ordered* identity

    4/66529 = 1/17060 + 1/665290 + 1/226996948.

The nonresidue requirement alone cannot force a divisor into the two exact residue classes `c≡−4⁻¹ (mod a)` or `d≡−x (mod a)`; a factor-residue group can miss both classes. In particular, (2) does **not** supply any `c` or `d`.

## Every square numerator fails **full Type I**, but not Type II

The Lean theorem `square_no_typeI_anywhere` establishes, for **all** natural numbers `s,x`,

    ¬ TypeI(s²,x).                                            (3)

For odd `s`, `s²≡1 (mod 8)`; (Iχ) would require `(c/s²)=−1`, impossible because `(c/s²)=(c/s)²` is `0` or `1`. This is a genuinely **full** `c∣x²` obstruction, stronger than `square_no_simple_typeI` in `SquareFactorObstruction.lean`. For even `s`, the proposed divisor `4x−s²` is a multiple of `4` (including the case zero) and cannot divide `4c+1`. The specialized hard-square corollary is `square_no_full_typeI`; its inputs are composite squares (except the irrelevant `s=1`), **not counterexample primes**.

Type II may still work for squares: `square_25_typeII` proves `p=25,x=10,d=5`, and `square_25_good` verifies the ordered triple `(10,20,100)`. For an odd-square Type-II solution with `s²<4x`, `odd_square_typeII_not_coprime` further proves `gcd(x,s)>1`: without a shared factor, (IIχ) would demand a negative Jacobi symbol modulo the square. The prime-only coprimality step is therefore essential to (2).

## What a universal resolution still requires

The original, verified reduction is **not** (1)–(3). For every prime `p=24k+1`, one must exhibit a **particular** `0≤j<6k` such that, writing `x=6k+1+j` and `a=4j+3`, either

    ∃ c>0 : c∣x² ∧ a∣4c+1,
    or  ∃ d : 0<d<x ∧ d∣x² ∧ a∣x+d.                         (4)

The sharp Type-II bound in `HardTypeIISize.lean` allows its alternative to be restricted to `7j<6k`, but provides no witness. Reciprocity (1) filters impossible local factors, and squares in (3) are **composite**; neither proves (4) for an arbitrary hard prime, nor supplies a prime failing both alternatives at **every** candidate `j`. The exact all-prime pointwise covering step remains missing.
