# An unbounded **local** nonsquare obstruction to character-plus-divisor counting

**Status:** This identifies a precise obstruction to a tempting proof strategy; it does **not** prove or refute universal Type I, nor the Erdős–Straus conjecture. The main construction and its exact *full* `c ∣ x²` assertion are proved without `sorry` in `NonsquareResidueBarrier.lean`. `Submission/Spec.lean` is unchanged.

## Exact infinite family

For every integer `t ≥ 0`, set

    x_t = 59·229^t,                 n_t = 4x_t − 19.

Both `59` and `229` are primes; `229 ≡ 1 (mod 114)`, and `59 ≡ 5 (mod 6)`. Thus `x_t ≡ 5 (mod 6)` and `n_t ≡ 1 (mod 24)`. In the usual notation `n_t=24k+1`, our candidate is **the fifth** first denominator `x_t=6k+5`, or `j=4`. Since `x_t ≥ 59`, it is strictly eligible: `n_t/4 < x_t < n_t/2`, and `4x_t−n_t=19`. Moreover,

    x_t ≡ 2 (mod 19),               n_t ≡ 8 (mod 19).

The squares modulo 19 are `{0,1,4,5,6,7,9,11,16,17}`; hence **every** `n_t` is nonsquare. The Lean results are `residueMiss_eligible`, `residueMissN_moduli`, and `residueMissN_nonsquare`. `arbitrarily_large_nonsquare_residue_misses` proves that such obstructed *candidates* occur beyond any threshold.

Every divisor of the **whole square** `x_t² = 59²·229^(2t)` is uniquely

    c = 59^i·229^h,            0 ≤ i ≤ 2,   0 ≤ h ≤ 2t.

Modulo 19, these divisors occupy exactly `{1,2,4}` because `59 ≡ 2` and `229 ≡ 1`. But the Type-I condition `19 ∣ 4c+1` needs `c ≡ 14 (mod 19)`; even the unrestricted Type-II condition `19 ∣ x_t+c` needs `c ≡ 17 (mod 19)`. **Both** target residues are absent. `residueMiss_divisor_residues` and `residueMiss_no_types` prove this for *every* divisor of `x_t²`, not merely for cofactors dividing `x_t`, and without relying on a finite scan.

The Jacobi/primitive-root tests nevertheless look as favorable as possible: `59 ≡ 2 (mod 19)` generates `(ℤ/19ℤ)ˣ` (order 18), so `(59/19)=−1`. The existing `jacobi_divisor_transfer` gives `(59/n_t)=(59/19)=−1`; Lean checks both `residueMiss_primitive_root` and `residueMiss_nonresidue_factor`. Primitive-root **order** does not create the seven copies of `59` required for the Type-I target `14 ≡ 2⁷`, or the ten copies for Type II's `17 ≡ 2¹⁰`: in divisors of `x_t²` the exponent of `59` is at most two. Multiplying by arbitrarily many powers of `229 ≡ 1` changes the number/size of divisors but none of their residues.

In particular `τ(x_t²)=3(2t+1)` (`residueMiss_divisor_count`), which is arbitrarily large. Even discarding square cofactors leaves **`4t+1` nonsquare divisors**: exactly `2(t+1)` of the `3(2t+1)` divisors have *both* exponents even. For the local Type-I pair count the zero-frequency contribution `(4t+1)/19` is unbounded, while the actual local count is identically zero; the sum of nonzero additive-character modes is **exactly** `−(4t+1)/19`. Thus neither the necessary negative quadratic symbol, a primitive-root factor, unusually smooth `x`, nor a pointwise lower bound for the *raw number* of divisor pairs forces the required exact residue class. `residueMiss_unbounded_local_obstruction` records the main combination in Lean.

**This is emphatically not a global failure.** For `t=0`, `n=217` and the bad candidate is `x=59`, but a different eligible denominator `x=55` works with `c=5`: `3 ∣ 4·5+1` and `5 ∣ 55²`. `residueMiss_zero_good` even proves an ordered three-unit-fraction decomposition for 217. Other denominators for the other `n_t` have **not** been excluded. The family makes no assertion that infinitely many `n_t` are prime; proving primality of `4·59·229^t−19` for infinitely many `t` would require separate work. In particular this obstruction does **not** refute the prime-only Type-I candidate, let alone Erdős–Straus.

## Many *distinct* prime factors also do not fix a single candidate

The obstruction is not caused just by using a high prime power. Dirichlet's theorem permits, for any `h ≥ 0`, `h` distinct primes `r₁,…,r_h ≡ 1 (mod 114)`. Define `x=59∏r_i`, `n=4x−19`. All the congruences, nonsquareness, Jacobi sign, eligibility and absent targets above remain valid: a divisor of `x²` has residue `2^i (mod 19)` for some `i∈{0,1,2}`. Now `x` has `h+1` distinct prime factors, `τ(x²)=3^(h+1)`, and the number of nonsquare divisors is `3^(h+1)−2^(h+1)`. Hence even exponentially many divisor choices arising from **distinct** prime factors and a primitive-root nonresidue cannot force the one selected residue at this `a=19`. This paragraph follows directly from Dirichlet and unique prime factorization; the Lean file formalizes the explicit `r=229` power subfamily, **not** the distinct-primes Dirichlet extension.

## What is still missing for nonsquares / hard primes

The global claim requires a single successful **index**, not positive contributions at an arbitrary index. For each `n=24k+1`, it asks for *some* `0≤j<6k` with `x_j=6k+1+j`, `a_j=4j+3`, and a divisor `c∣x_j²` satisfying the **specific** congruence `c ≡ −4⁻¹ (mod a_j)`. The transfer `(c/a_j)=(c/n)` supplies only a quadratic-character sign, not membership in this exact divisor-residue set. The family above rules out the inference from a favorable sign, smoothness and arbitrarily many divisors **at a single eligible index**; it does not rule out a genuinely global argument coupling the varying `a_j` with the multiplicative factors of the varying `x_j`. Such pointwise *simultaneous* control over `j` and `c` is exactly what the attempted method lacks. For primes, even the already Lean-checked `p=54121` example in `LeastNonresidueProgress.lean` has a primitive-root nonresidue but misses both divisor targets at one eligible `x`; it works at another. Separately, the pre-existing `InductionCRTBarrier.lean` proves that no **fixed** Type-I cofactor cutoff suffices even among soluble hard primes. The present construction does not rely on a fixed cofactor cutoff: its divisor count grows without bound, while its *residue set* stays small at the indicated `a`.

**Verification:** `lake env lean Submission/NonsquareResidueBarrier.lean` and `lake build Submission.NonsquareResidueBarrier` succeed. The file's `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`, no `sorryAx`. Neither this infinite local family, the earlier finite checks through `10^10`, nor a density statement is extrapolated into universal Type I.
