import FormalConjectures.Util.ProblemImports

open Nat

set_option maxRecDepth 100000
set_option exponentiation.threshold 1000000000
set_option maxHeartbeats 0

/-!
## Machinery for computing `minFac (fermatNumber n)`

Every prime factor `p` of `Fₙ = 2 ^ (2 ^ n) + 1` with `1 < n` has the form
`p = k * 2 ^ (n + 2) + 1` (Mathlib's `Nat.fermat_primeFactors_one_lt`).  Hence to
show that a given prime `P` is the *smallest* prime factor it suffices to check
that none of the finitely many candidates `k * 2 ^ (n + 2) + 1` with `1 ≤ k < K`
divide `Fₙ`, where `P = K * 2 ^ (n + 2) + 1`.  The candidates are enumerated by
`decide`; a nested (chunked) formulation keeps the kernel recursion depth low.
-/

/-- Reduce a flat bounded check `∀ k < K, …` to a nested one (chunks of size `C`).
Choosing `C ≈ √K` keeps the kernel's `decide` recursion depth ≈ `2√K`, well below
the C-stack limit (a flat check, or a badly-balanced chunking, overflows). -/
lemma nested_check (n S K C QMAX : ℕ) (hC : 0 < C) (hQ : K ≤ C * QMAX)
    (h : ∀ q, q < QMAX → ∀ r, r < C → 1 ≤ C * q + r → C * q + r < K →
          ¬ (((C * q + r) * S + 1) ∣ fermatNumber n)) :
    ∀ k, k < K → 1 ≤ k → ¬ ((k * S + 1) ∣ fermatNumber n) := by
  intro k hkK hk1
  have hcomm : C * QMAX = QMAX * C := Nat.mul_comm C QMAX
  have hq : k / C < QMAX := by apply Nat.div_lt_of_lt_mul; omega
  have hr : k % C < C := Nat.mod_lt _ hC
  have hdm : C * (k / C) + k % C = k := Nat.div_add_mod k C
  have := h (k / C) hq (k % C) hr (by omega) (by omega)
  rwa [hdm] at this

/-- If `P` is a prime divisor of `Fₙ` of the form `K * 2 ^ (n + 2) + 1` and no
smaller candidate `(C * q + r) * 2 ^ (n + 2) + 1` (`1 ≤ C * q + r < K`)
divides `Fₙ`, then `P` is the least prime factor of `Fₙ`. -/
lemma logfac (n P K C QMAX : ℕ) (hn : 1 < n) (hC : 0 < C) (hP : P.Prime)
    (hdvd : P ∣ fermatNumber n) (hPform : P = K * 2 ^ (n + 2) + 1) (hQ : K ≤ C * QMAX)
    (hchk : ∀ q, q < QMAX → ∀ r, r < C → 1 ≤ C * q + r → C * q + r < K →
          ¬ (((C * q + r) * 2 ^ (n + 2) + 1) ∣ fermatNumber n)) :
    minFac (fermatNumber n) = P := by
  have hK := nested_check n (2 ^ (n + 2)) K C QMAX hC hQ hchk
  have hF1 : fermatNumber n ≠ 1 := fermatNumber_ne_one n
  have hmp := minFac_prime hF1
  have hmdvd := minFac_dvd (fermatNumber n)
  have hle : minFac (fermatNumber n) ≤ P := minFac_le_of_dvd hP.two_le hdvd
  refine le_antisymm hle ?_
  obtain ⟨k, hk⟩ := fermat_primeFactors_one_lt n _ hn hmp hmdvd
  by_contra hlt; push_neg at hlt
  rw [hk] at hlt hmdvd; rw [hPform] at hlt
  have hkK : k < K := by
    have h2 : k * 2 ^ (n + 2) < K * 2 ^ (n + 2) := by omega
    exact lt_of_mul_lt_mul_right h2 (Nat.zero_le _)
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exfalso; rw [h, zero_mul, zero_add] at hk; exact hmp.one_lt.ne' hk
    · exact h
  exact hK k hkK hk1 hmdvd

/-- `minFac F₁₅ = 1214251009 = 9264·2¹⁷ + 1`. -/
theorem e15 : minFac (fermatNumber 15) = 1214251009 :=
  logfac 15 1214251009 9264 200 47 (by norm_num) (by norm_num) (by norm_num) (by decide)
    (by norm_num) (by norm_num) (by decide)

/-- `minFac F₁₆ = 825753601 = 3150·2¹⁸ + 1`. -/
theorem e16 : minFac (fermatNumber 16) = 825753601 :=
  logfac 16 825753601 3150 200 16 (by norm_num) (by norm_num) (by norm_num) (by decide)
    (by norm_num) (by norm_num) (by decide)

/-- `minFac F₁₈ = 13631489 = 13·2²⁰ + 1`. -/
theorem e18 : minFac (fermatNumber 18) = 13631489 :=
  logfac 18 13631489 13 200 1 (by norm_num) (by norm_num) (by norm_num) (by decide)
    (by norm_num) (by norm_num) (by decide)

/-- `minFac F₂₃ = 167772161 = 5·2²⁵ + 1`. -/
theorem e23 : minFac (fermatNumber 23) = 167772161 :=
  logfac 23 167772161 5 200 1 (by norm_num) (by norm_num) (by norm_num) (by decide)
    (by norm_num) (by norm_num) (by decide)

/--
A358684: $a(n)$ is the minimum integer $k$ such that the smallest prime factor of the $n$-th Fermat number exceeds $2^{2^n - k}$.
Let $F_n = 2^{2^n} + 1$ be the $n$-th Fermat number, and $P_n$ be its smallest prime factor.
The definition of $a(n)$ is equivalent to the closed form:
$$a(n) = 2^n - \lfloor \log_2(P_n) \rfloor$$
where $P_n = \operatorname{minFac}(\operatorname{fermatNumber} n)$.
The subtraction is defined in $\mathbb{N}$ and is safe since $P_n \le F_n$, implying $\log_2 P_n < 2^n$.
-/
def a (n : ℕ) : ℕ :=
  let pn := minFac (fermatNumber n)
  (2 ^ n) - (log2 pn)

/--
a(14) is probably equal to 16208; a(15) to a(19) are 32738, 65507, 131028, 262121, 524252;
a(20) is unknown; a(21) to a(23) are 2097110, 4194189, 8388581; a(24) is unknown.
-/
theorem oeis_358684_conjecture_1 :
    a 14 = 16208 ∧
    a 15 = 32738 ∧
    a 16 = 65507 ∧
    a 17 = 131028 ∧
    a 18 = 262121 ∧
    a 19 = 524252 ∧
    a 21 = 2097110 ∧
    a 22 = 4194189 ∧
    a 23 = 8388581 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- a 14 = 16208 : OPEN PROBLEM.  Requires that F₁₄ = 2^16384+1 has no prime
    -- factor below 2^176 (its smallest *known* factor is the 177-bit prime
    -- 116928085873074369829035993834596371340386703423373313).  This is only
    -- conjectural ("probably", per OEIS): ~2^160 candidates, not settled by anyone.
    sorry
  · rw [a, e15]; decide
  · rw [a, e16]; decide
  · -- a 17 = 131028 : true but computationally infeasible in the kernel.
    -- minFac F₁₇ = 31065037602817 requires ruling out ~5.9·10^7 candidates.
    sorry
  · rw [a, e18]; decide
  · -- a 19 = 524252 : true (minFac F₁₉ = 70525124609); provable in principle but
    -- the kernel `decide` over its ~3.4·10^4 candidates exceeds the C-stack here.
    sorry
  · -- a 21 = 2097110 : true but infeasible in the kernel (kernel OOMs on the
    -- ~5.3·10^5 candidate `decide`).  minFac F₂₁ = 4485296422913.
    sorry
  · -- a 22 = 4194189 : OPEN PROBLEM.  Requires that F₂₂ = 2^(2^22)+1 has no prime
    -- factor below 2^115 (its smallest known factor is the 116-bit prime
    -- 64658705994591851009055774868504577): ~2^91 candidates, not settled.
    sorry
  · rw [a, e23]; decide
