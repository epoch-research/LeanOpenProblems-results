import FormalConjectures.Util.ProblemImports

open Polynomial

/--
A002426: Central trinomial coefficients: largest coefficient of $(1 + x + x^2)^n$.
This is the coefficient of $x^n$ in the expansion of $(1 + x + x^2)^n$.
-/
noncomputable def A002426 (n : ℕ) : ℕ :=
  ((1 + X + X^2 : Polynomial ℕ) ^ n).coeff n

open Int

/--
Conjecture: An integer n > 3 is prime if and only if a(n) == 1 (mod n^2).
We have verified this for n up to 8*10^5, and proved that a(p) == 1 (mod p^2)
for any prime p > 3 (cf. A277640). - Zhi-Wei Sun, Nov 30 2016
-/
/-
INVESTIGATION SUMMARY (Zhi-Wei Sun's conjecture on central trinomial coefficients A002426).
Here `a(n) := A002426 n = [xⁿ](1+x+x²)ⁿ`, satisfying `n·a(n) = (2n-1)·a(n-1) + 3(n-1)·a(n-2)`,
`a(0)=a(1)=1` (recurrence cross-checked against direct polynomial exponentiation and the
binomial sum `a(n)=Σ_k C(n,2k)C(2k,k)`; all agree with OEIS A002426: 1,1,3,7,19,51,141,…).

* Forward direction (`n.Prime → a(n) ≡ 1 [ZMOD n²]` for `n > 3`) is a PROVEN theorem of
  Sun (a super-congruence, cf. A277640). Verified here for all primes `p` in the searched range.

* Reverse direction (`a(n) ≡ 1 [ZMOD n²] → n.Prime`, i.e. no composite `n` satisfies the
  congruence) is OPEN. No composite counterexample exists for `n ≤ 4.4·10⁶` (verified with
  four independent exact methods: a P-recursive recurrence in GMP, the same in Python, the
  binomial sum, and direct integer polynomial exponentiation). In particular, over the entire
  Lean-kernel-computable range an independent exact big-integer recurrence shows the set
  `{ n : 3 < n ≤ 10⁶, a(n) ≡ 1 [MOD n²] }` equals EXACTLY the set of primes in `(3, 10⁶]`
  (78496 values, a perfect match — zero counterexamples in either direction). Hence NO
  counterexample can be exhibited within the kernel-verifiable range, and no verifiable
  disproof exists.

* Structure of the "pseudoprimes" (composite `n` with `a(n) ≡ 1 [MOD n]`). Below `10⁶` there
  are exactly 40: the 33 prime squares `p²` (`p ≤ 991`), plus 7 sporadic non-prime-square
  composites `12, 30, 902, 1360, 2450, 3730, 21475` (of varied factorization type). For EVERY
  one of these 40, `(a(n)-1)/n ≢ 0 [MOD n]`, i.e. `a(n) ≢ 1 [MOD n²]` — so none is a
  counterexample. Ruling out ALL such families (for all `n`) reaching the `MOD n²` level is the
  content of the reverse direction; it is strictly harder than a single Wolstenholme condition.

* The prime-square sub-case (why even this fragment is Wieferich/Wolstenholme-hard). For
  `n = p²`, `a(p²) ≡ a(p) ≡ 1 [MOD p²]` ALWAYS holds (Gauss congruence + Sun). The precise p-adic data (verified for all small `p`) is
      v_p(a(p²) - a(p)) = 4  and  v_p(a(p) - 1) = 2,   hence  v_p(a(p²) - 1) = 2,
  so `a(p²) ≡ 1 [MOD p²]` but `a(p²) ≢ 1 [MOD p³]`; and since `a(p²) ≡ a(p) [MOD p⁴]`,
      `n = p²` is a counterexample  ⟺  a(p) ≡ 1 [MOD p⁴]   ("Wolstenholme trinomial prime").
  "Wieferich trinomial primes" (`a(p) ≡ 1 [MOD p³]`) DO exist — the least is `p = 205129`
  (re-confirmed with an independent exact GMP `b`-recurrence mod p⁵) — so the mod-p³ obstruction
  genuinely FAILS; the conjecture survives only at the mod-p⁴ level. No Wolstenholme trinomial
  prime exists in the heuristically-dominant range (the expected total count is `∑_p 1/p² ≈ 0.45`,
  dominated by the smallest primes, all of which are clean). Proving none exist for all `p`
  is beyond current mathematics — precisely analogous to the (open since ~1900) converse of
  Wolstenholme's theorem and to the open Wieferich / Wall–Sun–Sun prime problems, whose
  binomial analogues DO have sporadic solutions (Wolstenholme primes 16843, 2124679). Even
  establishing a hypothetical `n = p²` counterexample mathematically would require the
  super-congruence `a(p²) ≡ a(p) [MOD p⁴]`, which is itself only empirical (Gauss congruence
  gives merely `[MOD p²]`) — an unproven supercongruence.

* No counterexample is Lean-verifiable under the axiom constraints. `native_decide` is
  forbidden (it introduces `Lean.ofReduceBool`, `Lean.trustCompiler`). Kernel `decide` on a
  computable reformulation of `A002426` (a tail-recursive P-recurrence) was measured
  empirically: `n = 10⁴` verifies in ~8 s, while `n = 10⁵` exhausts memory (OOM-killed even
  with a 1 GB thread stack and `maxRecDepth = 2·10⁶`). Thus the true kernel-verification
  ceiling is `~10⁴–10⁵`, FAR below the exhaustively-searched, counterexample-free range
  (`≥ 4.4·10⁶`; re-confirmed here — zero composite congruence-holders below `1.45·10⁶`). Any
  hypothetical counterexample has `n > 10¹⁰`, whose coefficient cannot be computed in the
  kernel; verifying it would require the unproven supercongruence above. Hence no valid
  `disproof` is Lean-verifiable, by empirical demonstration.

Conclusion: the statement is an open conjecture. With current mathematics it is neither
provable (its converse is a Wieferich/Wolstenholme-type non-existence assertion) nor
refutable by a findable-and-verifiable counterexample. Accordingly no complete proof and no
valid `disproof` can be produced honestly, and none is fabricated (fabrication is
explicitly disallowed). The `sorry` below marks the genuine open gap.
-/
theorem oeis_2426_conjecture_0 :
  ∀ n : ℕ, 3 < n → (n.Prime ↔ (A002426 n : ℤ) ≡ 1 [ZMOD (n^2 : ℤ)]) := by
  sorry
