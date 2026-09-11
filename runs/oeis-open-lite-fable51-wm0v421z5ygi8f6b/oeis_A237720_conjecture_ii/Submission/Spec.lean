import FormalConjectures.Util.ProblemImports

open Nat Finset
open scoped Nat.Prime

/--
A237720: Number of primes $p \le \lfloor (n+1)/2 \rfloor$ with $\lfloor \sqrt{n-p} \rfloor$ prime.
-/
noncomputable def a (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun p : ℕ =>
    p.Prime ∧
    2 * p ≤ n + 1 ∧
    (Nat.sqrt (n - p)).Prime
  ) (Finset.range (n + 1)))

/- ### Verified partial results

A witness for `n` is a pair of primes `(p, q)` with `p < n` and `q ^ 2 ≤ n + p < (q + 1) ^ 2`.
The lemmas below establish the conjecture on the windows
`n ∈ [q ^ 2 - 2 q, q ^ 2 + 2 q - 2]` around each prime square `q ^ 2` (`q ≥ 7`),
using only Bertrand's postulate.  The remaining `n` (in the gaps between consecutive such
windows) require a prime in a prescribed interval of length `≈ 2 √n`, which is an open
problem in prime-gap theory. -/

theorem witness_of_prime_block {n p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpn : p < n)
    (h1 : q ^ 2 ≤ n + p) (h2 : n + p < (q + 1) ^ 2) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  refine ⟨p, hp, hpn, ?_⟩
  have : q = Nat.sqrt (n + p) := Nat.eq_sqrt'.2 ⟨h1, h2⟩
  rwa [← this]

/-- The `p = 2` window: for a prime `q ≥ 3`, every `n ∈ [q² − 2, q² + 2q − 2]` has a witness. -/
theorem window_two {n q : ℕ} (hq : q.Prime) (hq3 : 3 ≤ q)
    (h1 : q ^ 2 ≤ n + 2) (h2 : n + 2 ≤ q ^ 2 + 2 * q) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  refine witness_of_prime_block Nat.prime_two hq ?_ h1 (by nlinarith)
  nlinarith

/-- The Bertrand window: for a prime `q ≥ 7`, every `n ∈ [q² − 2q, q² − 1]` has a witness,
by applying Bertrand's postulate to `m = q² − n ∈ [1, 2q]`. -/
theorem window_bertrand {n q : ℕ} (hq : q.Prime) (hq7 : 7 ≤ q)
    (h1 : q ^ 2 ≤ n + 2 * q) (h2 : n < q ^ 2) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  obtain ⟨m, hm⟩ : ∃ m, q ^ 2 = n + m := ⟨q ^ 2 - n, by omega⟩
  have hm0 : m ≠ 0 := by omega
  obtain ⟨p, hp, hmp, hp2⟩ := Nat.exists_prime_lt_and_le_two_mul m hm0
  refine witness_of_prime_block hp hq ?_ (by omega) ?_
  · nlinarith
  · nlinarith

/-- Every `n ∈ [q² − 2q, q² + 2q − 2]` for some prime `q ≥ 7` has a witness. -/
theorem window_combined {n q : ℕ} (hq : q.Prime) (hq7 : 7 ≤ q)
    (h1 : q ^ 2 ≤ n + 2 * q) (h2 : n + 2 ≤ q ^ 2 + 2 * q) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  rcases lt_or_ge n (q ^ 2) with h | h
  · exact window_bertrand hq hq7 h1 h
  · exact window_two hq (by omega) (by omega) h2

/-- Conditional reduction: if some prime `q` satisfies `n + 2 ≤ q ^ 2` and `(q + 1) ^ 2 ≤ 2 n`,
and every interval `[x, x + 2 q]` with `2 ≤ x ≤ n` contains a prime, then `n` has a witness.
The hypothesis `H` is a Legendre-type prime-gap statement (gaps `≤ 2 q ≈ 2 √n` up to `n`),
which is the open input needed to complete the conjecture. -/
theorem conj_of_gap_bound {n q : ℕ} (hq : q.Prime) (h1 : n + 2 ≤ q ^ 2) (h2 : (q + 1) ^ 2 ≤ 2 * n)
    (H : ∀ x, 2 ≤ x → x ≤ n → ∃ p, p.Prime ∧ x ≤ p ∧ p ≤ x + 2 * q) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  have hq2 : q ^ 2 ≤ 2 * n := le_trans (Nat.pow_le_pow_left (Nat.le_succ q) 2) h2
  obtain ⟨p, hp, hxp, hpx⟩ := H (q ^ 2 - n) (by omega) (by omega)
  refine witness_of_prime_block hp hq ?_ (by omega) ?_
  · have : q ^ 2 + 2 * q < (q + 1) ^ 2 := by ring_nf; omega
    omega
  · have : q ^ 2 + 2 * q < (q + 1) ^ 2 := by ring_nf; omega
    omega

/- ### Finite verification

A pair of primes `(p, q)` with `2 p < q ^ 2` certifies the conjecture on the whole window
`n ∈ [q ^ 2 - p, q ^ 2 + 2 q - p]` (`window_general`).  A greedy covering of `[6, 10 ^ 7]`
by 2237 such windows, together with direct witnesses for `n = 3, 4, 5`, verifies the
conjecture for all `3 ≤ n ≤ 10 ^ 7` (`conj_upto_1e7`). -/

set_option linter.unnecessarySeqFocus false

theorem window_general {n p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h1 : q ^ 2 ≤ n + p) (h2 : n + p ≤ q ^ 2 + 2 * q) (h3 : 2 * p < q ^ 2) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  refine witness_of_prime_block hp hq (by omega) h1 ?_
  have : q ^ 2 + 2 * q < (q + 1) ^ 2 := by ring_nf; omega
  omega

theorem cov_6_3784 (n : ℕ) (hlo : 6 ≤ n) (hhi : n ≤ 3784) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  rcases le_or_gt n 12 with h | h
  · exact window_general (p := 3) (q := 3) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 13 with h | h
  · exact window_general (p := 2) (q := 3) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 24 with h | h
  · exact window_general (p := 11) (q := 5) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 33 with h | h
  · exact window_general (p := 2) (q := 5) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 46 with h | h
  · exact window_general (p := 17) (q := 7) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 61 with h | h
  · exact window_general (p := 2) (q := 7) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 84 with h | h
  · exact window_general (p := 59) (q := 11) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 106 with h | h
  · exact window_general (p := 37) (q := 11) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 128 with h | h
  · exact window_general (p := 67) (q := 13) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 154 with h | h
  · exact window_general (p := 41) (q := 13) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 186 with h | h
  · exact window_general (p := 137) (q := 17) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 220 with h | h
  · exact window_general (p := 179) (q := 19) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 250 with h | h
  · exact window_general (p := 149) (q := 19) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 286 with h | h
  · exact window_general (p := 113) (q := 19) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 324 with h | h
  · exact window_general (p := 251) (q := 23) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 364 with h | h
  · exact window_general (p := 211) (q := 23) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 408 with h | h
  · exact window_general (p := 167) (q := 23) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 448 with h | h
  · exact window_general (p := 127) (q := 23) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 502 with h | h
  · exact window_general (p := 397) (q := 29) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 562 with h | h
  · exact window_general (p := 461) (q := 31) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 622 with h | h
  · exact window_general (p := 401) (q := 31) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 676 with h | h
  · exact window_general (p := 347) (q := 31) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 730 with h | h
  · exact window_general (p := 293) (q := 31) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 802 with h | h
  · exact window_general (p := 641) (q := 37) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 874 with h | h
  · exact window_general (p := 569) (q := 37) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 954 with h | h
  · exact window_general (p := 809) (q := 41) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1028 with h | h
  · exact window_general (p := 907) (q := 43) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1114 with h | h
  · exact window_general (p := 821) (q := 43) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1206 with h | h
  · exact window_general (p := 1097) (q := 47) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1294 with h | h
  · exact window_general (p := 1009) (q := 47) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1384 with h | h
  · exact window_general (p := 919) (q := 47) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1476 with h | h
  · exact window_general (p := 827) (q := 47) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1554 with h | h
  · exact window_general (p := 1361) (q := 53) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1656 with h | h
  · exact window_general (p := 1259) (q := 53) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1762 with h | h
  · exact window_general (p := 1153) (q := 53) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1878 with h | h
  · exact window_general (p := 1721) (q := 59) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1996 with h | h
  · exact window_general (p := 1847) (q := 61) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2110 with h | h
  · exact window_general (p := 1733) (q := 61) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2230 with h | h
  · exact window_general (p := 1613) (q := 61) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2350 with h | h
  · exact window_general (p := 1493) (q := 61) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2482 with h | h
  · exact window_general (p := 2141) (q := 67) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2612 with h | h
  · exact window_general (p := 2011) (q := 67) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2746 with h | h
  · exact window_general (p := 2437) (q := 71) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2884 with h | h
  · exact window_general (p := 2591) (q := 73) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3028 with h | h
  · exact window_general (p := 2447) (q := 73) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3166 with h | h
  · exact window_general (p := 2309) (q := 73) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3320 with h | h
  · exact window_general (p := 3079) (q := 79) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3472 with h | h
  · exact window_general (p := 2927) (q := 79) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3622 with h | h
  · exact window_general (p := 3433) (q := 83) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  exact window_general (p := 3271) (q := 83) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)

theorem cov_3785_16312 (n : ℕ) (hlo : 3785 ≤ n) (hhi : n ≤ 16312) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  rcases le_or_gt n 3946 with h | h
  · exact window_general (p := 3109) (q := 83) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4102 with h | h
  · exact window_general (p := 2953) (q := 83) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4278 with h | h
  · exact window_general (p := 3821) (q := 89) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4456 with h | h
  · exact window_general (p := 3643) (q := 89) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4632 with h | h
  · exact window_general (p := 3467) (q := 89) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4800 with h | h
  · exact window_general (p := 3299) (q := 89) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4982 with h | h
  · exact window_general (p := 4621) (q := 97) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5162 with h | h
  · exact window_general (p := 4441) (q := 97) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5364 with h | h
  · exact window_general (p := 5039) (q := 101) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5554 with h | h
  · exact window_general (p := 5261) (q := 103) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5756 with h | h
  · exact window_general (p := 5059) (q := 103) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5970 with h | h
  · exact window_general (p := 5693) (q := 107) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6176 with h | h
  · exact window_general (p := 5923) (q := 109) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6388 with h | h
  · exact window_general (p := 5711) (q := 109) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6598 with h | h
  · exact window_general (p := 5501) (q := 109) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6822 with h | h
  · exact window_general (p := 6173) (q := 113) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7042 with h | h
  · exact window_general (p := 5953) (q := 113) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7258 with h | h
  · exact window_general (p := 5737) (q := 113) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7476 with h | h
  · exact window_general (p := 5519) (q := 113) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7698 with h | h
  · exact window_general (p := 5297) (q := 113) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7918 with h | h
  · exact window_general (p := 5077) (q := 113) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8134 with h | h
  · exact window_general (p := 4861) (q := 113) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8374 with h | h
  · exact window_general (p := 8009) (q := 127) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8626 with h | h
  · exact window_general (p := 7757) (q := 127) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8886 with h | h
  · exact window_general (p := 8537) (q := 131) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9136 with h | h
  · exact window_general (p := 8287) (q := 131) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9384 with h | h
  · exact window_general (p := 8039) (q := 131) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9634 with h | h
  · exact window_general (p := 7789) (q := 131) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9906 with h | h
  · exact window_general (p := 9137) (q := 137) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 10180 with h | h
  · exact window_general (p := 9419) (q := 139) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 10448 with h | h
  · exact window_general (p := 9151) (q := 139) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 10712 with h | h
  · exact window_general (p := 8887) (q := 139) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 10990 with h | h
  · exact window_general (p := 8609) (q := 139) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 11246 with h | h
  · exact window_general (p := 8353) (q := 139) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 11542 with h | h
  · exact window_general (p := 10957) (q := 149) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 11842 with h | h
  · exact window_general (p := 11261) (q := 151) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 12130 with h | h
  · exact window_general (p := 10973) (q := 151) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 12416 with h | h
  · exact window_general (p := 10687) (q := 151) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 12724 with h | h
  · exact window_general (p := 12239) (q := 157) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 13036 with h | h
  · exact window_general (p := 11927) (q := 157) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 13346 with h | h
  · exact window_general (p := 11617) (q := 157) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 13666 with h | h
  · exact window_general (p := 13229) (q := 163) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 13988 with h | h
  · exact window_general (p := 12907) (q := 163) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 14322 with h | h
  · exact window_general (p := 13901) (q := 167) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 14656 with h | h
  · exact window_general (p := 13567) (q := 167) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 14982 with h | h
  · exact window_general (p := 13241) (q := 167) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 15328 with h | h
  · exact window_general (p := 14947) (q := 173) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 15654 with h | h
  · exact window_general (p := 14621) (q := 173) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 15994 with h | h
  · exact window_general (p := 14281) (q := 173) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  exact window_general (p := 13963) (q := 173) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)

theorem cov_16313_38414 (n : ℕ) (hlo : 16313 ≤ n) (hhi : n ≤ 38414) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  rcases le_or_gt n 16668 with h | h
  · exact window_general (p := 15731) (q := 179) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 17026 with h | h
  · exact window_general (p := 16097) (q := 181) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 17386 with h | h
  · exact window_general (p := 15737) (q := 181) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 17746 with h | h
  · exact window_general (p := 15377) (q := 181) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 18106 with h | h
  · exact window_general (p := 15017) (q := 181) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 18466 with h | h
  · exact window_general (p := 14657) (q := 181) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 18822 with h | h
  · exact window_general (p := 18041) (q := 191) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 19208 with h | h
  · exact window_general (p := 18427) (q := 193) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 19594 with h | h
  · exact window_general (p := 18041) (q := 193) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 19984 with h | h
  · exact window_general (p := 19219) (q := 197) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 20364 with h | h
  · exact window_general (p := 18839) (q := 197) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 20762 with h | h
  · exact window_general (p := 19237) (q := 199) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 21160 with h | h
  · exact window_general (p := 18839) (q := 199) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 21556 with h | h
  · exact window_general (p := 18443) (q := 199) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 21952 with h | h
  · exact window_general (p := 18047) (q := 199) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 22342 with h | h
  · exact window_general (p := 17657) (q := 199) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 22754 with h | h
  · exact window_general (p := 22189) (q := 211) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 23176 with h | h
  · exact window_general (p := 21767) (q := 211) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 23596 with h | h
  · exact window_general (p := 21347) (q := 211) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 24014 with h | h
  · exact window_general (p := 20929) (q := 211) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 24436 with h | h
  · exact window_general (p := 20507) (q := 211) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 24854 with h | h
  · exact window_general (p := 20089) (q := 211) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 25262 with h | h
  · exact window_general (p := 19681) (q := 211) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 25706 with h | h
  · exact window_general (p := 24469) (q := 223) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 26152 with h | h
  · exact window_general (p := 24023) (q := 223) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 26592 with h | h
  · exact window_general (p := 25391) (q := 227) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 27050 with h | h
  · exact window_general (p := 25849) (q := 229) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 27508 with h | h
  · exact window_general (p := 25391) (q := 229) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 27972 with h | h
  · exact window_general (p := 26783) (q := 233) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 28438 with h | h
  · exact window_general (p := 26317) (q := 233) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 28888 with h | h
  · exact window_general (p := 25867) (q := 233) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 29346 with h | h
  · exact window_general (p := 25409) (q := 233) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 29812 with h | h
  · exact window_general (p := 28751) (q := 241) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 30286 with h | h
  · exact window_general (p := 28277) (q := 241) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 30764 with h | h
  · exact window_general (p := 27799) (q := 241) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 31234 with h | h
  · exact window_general (p := 27329) (q := 241) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 31714 with h | h
  · exact window_general (p := 26849) (q := 241) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 32196 with h | h
  · exact window_general (p := 31307) (q := 251) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 32694 with h | h
  · exact window_general (p := 30809) (q := 251) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 33196 with h | h
  · exact window_general (p := 30307) (q := 251) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 33694 with h | h
  · exact window_general (p := 32869) (q := 257) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 34204 with h | h
  · exact window_general (p := 32359) (q := 257) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 34716 with h | h
  · exact window_general (p := 31847) (q := 257) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 35238 with h | h
  · exact window_general (p := 34457) (q := 263) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 35764 with h | h
  · exact window_general (p := 33931) (q := 263) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 36286 with h | h
  · exact window_general (p := 33409) (q := 263) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 36816 with h | h
  · exact window_general (p := 36083) (q := 269) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 37354 with h | h
  · exact window_general (p := 36629) (q := 271) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 37886 with h | h
  · exact window_general (p := 36097) (q := 271) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  exact window_general (p := 35569) (q := 271) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)

theorem cov_38415_70042 (n : ℕ) (hlo : 38415 ≤ n) (hhi : n ≤ 70042) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  rcases le_or_gt n 38966 with h | h
  · exact window_general (p := 38317) (q := 277) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 39502 with h | h
  · exact window_general (p := 37781) (q := 277) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 40062 with h | h
  · exact window_general (p := 39461) (q := 281) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 40624 with h | h
  · exact window_general (p := 40031) (q := 283) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 41172 with h | h
  · exact window_general (p := 38351) (q := 281) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 41738 with h | h
  · exact window_general (p := 38917) (q := 283) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 42304 with h | h
  · exact window_general (p := 38351) (q := 283) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 42856 with h | h
  · exact window_general (p := 37799) (q := 283) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 43412 with h | h
  · exact window_general (p := 37243) (q := 283) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 43998 with h | h
  · exact window_general (p := 42437) (q := 293) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 44584 with h | h
  · exact window_general (p := 41851) (q := 293) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 45166 with h | h
  · exact window_general (p := 41269) (q := 293) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 45742 with h | h
  · exact window_general (p := 40693) (q := 293) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 46324 with h | h
  · exact window_general (p := 40111) (q := 293) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 46894 with h | h
  · exact window_general (p := 39541) (q := 293) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 47476 with h | h
  · exact window_general (p := 38959) (q := 293) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 48058 with h | h
  · exact window_general (p := 38377) (q := 293) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 48664 with h | h
  · exact window_general (p := 46199) (q := 307) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 49270 with h | h
  · exact window_general (p := 48073) (q := 311) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 49884 with h | h
  · exact window_general (p := 47459) (q := 311) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 50504 with h | h
  · exact window_general (p := 48091) (q := 313) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 51132 with h | h
  · exact window_general (p := 49991) (q := 317) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 51760 with h | h
  · exact window_general (p := 49363) (q := 317) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 52392 with h | h
  · exact window_general (p := 48731) (q := 317) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 53014 with h | h
  · exact window_general (p := 48109) (q := 317) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 53632 with h | h
  · exact window_general (p := 47491) (q := 317) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 54262 with h | h
  · exact window_general (p := 46861) (q := 317) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 54894 with h | h
  · exact window_general (p := 46229) (q := 317) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 55556 with h | h
  · exact window_general (p := 54667) (q := 331) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 56212 with h | h
  · exact window_general (p := 54011) (q := 331) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 56870 with h | h
  · exact window_general (p := 53353) (q := 331) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 57542 with h | h
  · exact window_general (p := 56701) (q := 337) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 58204 with h | h
  · exact window_general (p := 56039) (q := 337) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 58870 with h | h
  · exact window_general (p := 55373) (q := 337) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 59534 with h | h
  · exact window_general (p := 54709) (q := 337) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 60206 with h | h
  · exact window_general (p := 54037) (q := 337) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 60866 with h | h
  · exact window_general (p := 53377) (q := 337) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 61546 with h | h
  · exact window_general (p := 59557) (q := 347) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 62242 with h | h
  · exact window_general (p := 60257) (q := 349) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 62938 with h | h
  · exact window_general (p := 59561) (q := 349) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 63642 with h | h
  · exact window_general (p := 61673) (q := 353) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 64330 with h | h
  · exact window_general (p := 58169) (q := 349) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 65026 with h | h
  · exact window_general (p := 60289) (q := 353) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 65742 with h | h
  · exact window_general (p := 63857) (q := 359) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 66450 with h | h
  · exact window_general (p := 63149) (q := 359) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 67140 with h | h
  · exact window_general (p := 62459) (q := 359) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 67848 with h | h
  · exact window_general (p := 61751) (q := 359) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 68582 with h | h
  · exact window_general (p := 66841) (q := 367) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 69316 with h | h
  · exact window_general (p := 66107) (q := 367) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  exact window_general (p := 65381) (q := 367) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)

theorem cov_70043_111556 (n : ℕ) (hlo : 70043 ≤ n) (hhi : n ≤ 111556) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  rcases le_or_gt n 70766 with h | h
  · exact window_general (p := 69109) (q := 373) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 71504 with h | h
  · exact window_general (p := 68371) (q := 373) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 72244 with h | h
  · exact window_general (p := 67631) (q := 373) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 73000 with h | h
  · exact window_general (p := 71399) (q := 379) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 73742 with h | h
  · exact window_general (p := 70657) (q := 379) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 74506 with h | h
  · exact window_general (p := 72949) (q := 383) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 75244 with h | h
  · exact window_general (p := 72211) (q := 383) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 76002 with h | h
  · exact window_general (p := 71453) (q := 383) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 76776 with h | h
  · exact window_general (p := 75323) (q := 389) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 77548 with h | h
  · exact window_general (p := 74551) (q := 389) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 78316 with h | h
  · exact window_general (p := 73783) (q := 389) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 79090 with h | h
  · exact window_general (p := 73009) (q := 389) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 79864 with h | h
  · exact window_general (p := 78539) (q := 397) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 80656 with h | h
  · exact window_general (p := 77747) (q := 397) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 81456 with h | h
  · exact window_general (p := 80147) (q := 401) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 82254 with h | h
  · exact window_general (p := 79349) (q := 401) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 83050 with h | h
  · exact window_general (p := 78553) (q := 401) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 83842 with h | h
  · exact window_general (p := 77761) (q := 401) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 84656 with h | h
  · exact window_general (p := 83443) (q := 409) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 85466 with h | h
  · exact window_general (p := 82633) (q := 409) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 86282 with h | h
  · exact window_general (p := 81817) (q := 409) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 87098 with h | h
  · exact window_general (p := 81001) (q := 409) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 87908 with h | h
  · exact window_general (p := 80191) (q := 409) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 88728 with h | h
  · exact window_general (p := 87671) (q := 419) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 89570 with h | h
  · exact window_general (p := 88513) (q := 421) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 90412 with h | h
  · exact window_general (p := 87671) (q := 421) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 91246 with h | h
  · exact window_general (p := 86837) (q := 421) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 92084 with h | h
  · exact window_general (p := 85999) (q := 421) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 92924 with h | h
  · exact window_general (p := 85159) (q := 421) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 93774 with h | h
  · exact window_general (p := 92849) (q := 431) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 94636 with h | h
  · exact window_general (p := 93719) (q := 433) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 95498 with h | h
  · exact window_general (p := 92857) (q := 433) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 96358 with h | h
  · exact window_general (p := 91997) (q := 433) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 97216 with h | h
  · exact window_general (p := 91139) (q := 433) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 98092 with h | h
  · exact window_general (p := 95507) (q := 439) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 98950 with h | h
  · exact window_general (p := 94649) (q := 439) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 99834 with h | h
  · exact window_general (p := 97301) (q := 443) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 100716 with h | h
  · exact window_general (p := 96419) (q := 443) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 101596 with h | h
  · exact window_general (p := 95539) (q := 443) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 102480 with h | h
  · exact window_general (p := 100019) (q := 449) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 103368 with h | h
  · exact window_general (p := 99131) (q := 449) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 104248 with h | h
  · exact window_general (p := 98251) (q := 449) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 105132 with h | h
  · exact window_general (p := 97367) (q := 449) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 106040 with h | h
  · exact window_general (p := 103723) (q := 457) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 106952 with h | h
  · exact window_general (p := 102811) (q := 457) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 107846 with h | h
  · exact window_general (p := 101917) (q := 457) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 108764 with h | h
  · exact window_general (p := 106531) (q := 463) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 109688 with h | h
  · exact window_general (p := 105607) (q := 463) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 110622 with h | h
  · exact window_general (p := 108401) (q := 467) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  exact window_general (p := 107467) (q := 467) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)

theorem cov_111557_162558 (n : ℕ) (hlo : 111557 ≤ n) (hhi : n ≤ 162558) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  rcases le_or_gt n 112486 with h | h
  · exact window_general (p := 106537) (q := 467) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 113416 with h | h
  · exact window_general (p := 105607) (q := 467) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 114346 with h | h
  · exact window_general (p := 104677) (q := 467) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 115254 with h | h
  · exact window_general (p := 103769) (q := 467) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 116206 with h | h
  · exact window_general (p := 114193) (q := 479) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 117132 with h | h
  · exact window_general (p := 101891) (q := 467) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 118072 with h | h
  · exact window_general (p := 112327) (q := 479) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 119026 with h | h
  · exact window_general (p := 111373) (q := 479) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 119996 with h | h
  · exact window_general (p := 118147) (q := 487) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 120952 with h | h
  · exact window_general (p := 117191) (q := 487) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 121906 with h | h
  · exact window_general (p := 120157) (q := 491) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 122884 with h | h
  · exact window_general (p := 119179) (q := 491) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 123852 with h | h
  · exact window_general (p := 118211) (q := 491) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 124824 with h | h
  · exact window_general (p := 117239) (q := 491) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 125818 with h | h
  · exact window_general (p := 124181) (q := 499) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 126808 with h | h
  · exact window_general (p := 123191) (q := 499) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 127804 with h | h
  · exact window_general (p := 126211) (q := 503) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 128808 with h | h
  · exact window_general (p := 125207) (q := 503) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 129802 with h | h
  · exact window_general (p := 124213) (q := 503) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 130818 with h | h
  · exact window_general (p := 129281) (q := 509) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 131826 with h | h
  · exact window_general (p := 128273) (q := 509) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 132838 with h | h
  · exact window_general (p := 127261) (q := 509) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 133842 with h | h
  · exact window_general (p := 126257) (q := 509) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 134856 with h | h
  · exact window_general (p := 125243) (q := 509) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 135868 with h | h
  · exact window_general (p := 124231) (q := 509) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 136902 with h | h
  · exact window_general (p := 135581) (q := 521) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 137926 with h | h
  · exact window_general (p := 136649) (q := 523) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 138968 with h | h
  · exact window_general (p := 135607) (q := 523) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 139994 with h | h
  · exact window_general (p := 134581) (q := 523) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 141034 with h | h
  · exact window_general (p := 133541) (q := 523) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 142076 with h | h
  · exact window_general (p := 132499) (q := 523) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 143098 with h | h
  · exact window_general (p := 131477) (q := 523) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 144136 with h | h
  · exact window_general (p := 130439) (q := 523) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 145174 with h | h
  · exact window_general (p := 129401) (q := 523) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 146198 with h | h
  · exact window_general (p := 128377) (q := 523) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 147244 with h | h
  · exact window_general (p := 127331) (q := 523) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 148322 with h | h
  · exact window_general (p := 145441) (q := 541) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 149384 with h | h
  · exact window_general (p := 144379) (q := 541) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 150434 with h | h
  · exact window_general (p := 143329) (q := 541) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 151522 with h | h
  · exact window_general (p := 148781) (q := 547) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 152614 with h | h
  · exact window_general (p := 147689) (q := 547) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 153700 with h | h
  · exact window_general (p := 146603) (q := 547) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 154792 with h | h
  · exact window_general (p := 145511) (q := 547) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 155876 with h | h
  · exact window_general (p := 144427) (q := 547) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 156990 with h | h
  · exact window_general (p := 154373) (q := 557) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 158104 with h | h
  · exact window_general (p := 153259) (q := 557) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 159216 with h | h
  · exact window_general (p := 152147) (q := 557) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 160326 with h | h
  · exact window_general (p := 157769) (q := 563) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 161436 with h | h
  · exact window_general (p := 156659) (q := 563) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  exact window_general (p := 155537) (q := 563) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)

theorem cov_162559_223520 (n : ℕ) (hlo : 162559 ≤ n) (hhi : n ≤ 223520) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  rcases le_or_gt n 163678 with h | h
  · exact window_general (p := 161221) (q := 569) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 164794 with h | h
  · exact window_general (p := 162389) (q := 571) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 165920 with h | h
  · exact window_general (p := 161263) (q := 571) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 167042 with h | h
  · exact window_general (p := 160141) (q := 571) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 168196 with h | h
  · exact window_general (p := 165887) (q := 577) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 169340 with h | h
  · exact window_general (p := 164743) (q := 577) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 170482 with h | h
  · exact window_general (p := 163601) (q := 577) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 171632 with h | h
  · exact window_general (p := 162451) (q := 577) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 172780 with h | h
  · exact window_general (p := 161303) (q := 577) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 173950 with h | h
  · exact window_general (p := 171793) (q := 587) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 175116 with h | h
  · exact window_general (p := 170627) (q := 587) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 176286 with h | h
  · exact window_general (p := 169457) (q := 587) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 177444 with h | h
  · exact window_general (p := 175391) (q := 593) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 178614 with h | h
  · exact window_general (p := 174221) (q := 593) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 179796 with h | h
  · exact window_general (p := 173039) (q := 593) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 180978 with h | h
  · exact window_general (p := 179021) (q := 599) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 182170 with h | h
  · exact window_general (p := 180233) (q := 601) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 183370 with h | h
  · exact window_general (p := 179033) (q := 601) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 184564 with h | h
  · exact window_general (p := 177839) (q := 601) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 185756 with h | h
  · exact window_general (p := 183907) (q := 607) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 186962 with h | h
  · exact window_general (p := 182701) (q := 607) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 188164 with h | h
  · exact window_general (p := 181499) (q := 607) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 189364 with h | h
  · exact window_general (p := 187631) (q := 613) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 190576 with h | h
  · exact window_general (p := 186419) (q := 613) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 191802 with h | h
  · exact window_general (p := 190121) (q := 617) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 193032 with h | h
  · exact window_general (p := 188891) (q := 617) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 194270 with h | h
  · exact window_general (p := 190129) (q := 619) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 195508 with h | h
  · exact window_general (p := 188891) (q := 619) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 196738 with h | h
  · exact window_general (p := 187661) (q := 619) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 197962 with h | h
  · exact window_general (p := 186437) (q := 619) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 199178 with h | h
  · exact window_general (p := 185221) (q := 619) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 200426 with h | h
  · exact window_general (p := 198997) (q := 631) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 201682 with h | h
  · exact window_general (p := 197741) (q := 631) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 202924 with h | h
  · exact window_general (p := 196499) (q := 631) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 204182 with h | h
  · exact window_general (p := 195241) (q := 631) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 205444 with h | h
  · exact window_general (p := 193979) (q := 631) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 206686 with h | h
  · exact window_general (p := 192737) (q := 631) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 207932 with h | h
  · exact window_general (p := 191491) (q := 631) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 209216 with h | h
  · exact window_general (p := 205519) (q := 643) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 210502 with h | h
  · exact window_general (p := 204233) (q := 643) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 211792 with h | h
  · exact window_general (p := 208111) (q := 647) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 213084 with h | h
  · exact window_general (p := 206819) (q := 647) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 214374 with h | h
  · exact window_general (p := 205529) (q := 647) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 215676 with h | h
  · exact window_general (p := 212039) (q := 653) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 216976 with h | h
  · exact window_general (p := 210739) (q := 653) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 218274 with h | h
  · exact window_general (p := 209441) (q := 653) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 219576 with h | h
  · exact window_general (p := 216023) (q := 659) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 220892 with h | h
  · exact window_general (p := 217351) (q := 661) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 222206 with h | h
  · exact window_general (p := 216037) (q := 661) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  exact window_general (p := 214723) (q := 661) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)

theorem cov_223521_294424 (n : ℕ) (hlo : 223521 ≤ n) (hhi : n ≤ 294424) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  rcases le_or_gt n 224836 with h | h
  · exact window_general (p := 213407) (q := 661) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 226144 with h | h
  · exact window_general (p := 212099) (q := 661) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 227440 with h | h
  · exact window_general (p := 210803) (q := 661) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 228782 with h | h
  · exact window_general (p := 225493) (q := 673) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 230126 with h | h
  · exact window_general (p := 224149) (q := 673) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 231480 with h | h
  · exact window_general (p := 228203) (q := 677) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 232812 with h | h
  · exact window_general (p := 226871) (q := 677) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 234160 with h | h
  · exact window_general (p := 225523) (q := 677) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 235522 with h | h
  · exact window_general (p := 232333) (q := 683) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 236886 with h | h
  · exact window_general (p := 230969) (q := 683) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 238242 with h | h
  · exact window_general (p := 229613) (q := 683) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 239604 with h | h
  · exact window_general (p := 228251) (q := 683) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 240986 with h | h
  · exact window_general (p := 237877) (q := 691) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 242360 with h | h
  · exact window_general (p := 236503) (q := 691) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 243726 with h | h
  · exact window_general (p := 224129) (q := 683) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 245104 with h | h
  · exact window_general (p := 233759) (q := 691) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 246482 with h | h
  · exact window_general (p := 232381) (q := 691) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 247864 with h | h
  · exact window_general (p := 244939) (q := 701) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 249264 with h | h
  · exact window_general (p := 243539) (q := 701) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 250656 with h | h
  · exact window_general (p := 242147) (q := 701) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 252040 with h | h
  · exact window_general (p := 240763) (q := 701) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 253456 with h | h
  · exact window_general (p := 250643) (q := 709) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 254870 with h | h
  · exact window_general (p := 249229) (q := 709) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 256288 with h | h
  · exact window_general (p := 247811) (q := 709) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 257696 with h | h
  · exact window_general (p := 246403) (q := 709) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 259102 with h | h
  · exact window_general (p := 244997) (q := 709) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 260538 with h | h
  · exact window_general (p := 257861) (q := 719) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 261976 with h | h
  · exact window_general (p := 256423) (q := 719) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 263412 with h | h
  · exact window_general (p := 254987) (q := 719) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 264846 with h | h
  · exact window_general (p := 253553) (q := 719) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 266260 with h | h
  · exact window_general (p := 263723) (q := 727) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 267712 with h | h
  · exact window_general (p := 262271) (q := 727) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 269146 with h | h
  · exact window_general (p := 249253) (q := 719) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 270602 with h | h
  · exact window_general (p := 268153) (q := 733) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 272068 with h | h
  · exact window_general (p := 266687) (q := 733) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 273524 with h | h
  · exact window_general (p := 265231) (q := 733) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 274996 with h | h
  · exact window_general (p := 272603) (q := 739) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 276472 with h | h
  · exact window_general (p := 271127) (q := 739) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 277956 with h | h
  · exact window_general (p := 275579) (q := 743) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 279442 with h | h
  · exact window_general (p := 274093) (q := 743) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 280914 with h | h
  · exact window_general (p := 272621) (q := 743) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 282372 with h | h
  · exact window_general (p := 271163) (q := 743) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 283862 with h | h
  · exact window_general (p := 281641) (q := 751) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 285364 with h | h
  · exact window_general (p := 280139) (q := 751) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 286864 with h | h
  · exact window_general (p := 278639) (q := 751) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 288364 with h | h
  · exact window_general (p := 286199) (q := 757) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 289874 with h | h
  · exact window_general (p := 284689) (q := 757) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 291394 with h | h
  · exact window_general (p := 289249) (q := 761) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 292912 with h | h
  · exact window_general (p := 287731) (q := 761) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  exact window_general (p := 280139) (q := 757) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)

theorem cov_294425_375024 (n : ℕ) (hlo : 294425 ≤ n) (hhi : n ≤ 375024) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  rcases le_or_gt n 295942 with h | h
  · exact window_general (p := 284701) (q := 761) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 297470 with h | h
  · exact window_general (p := 295429) (q := 769) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 299006 with h | h
  · exact window_general (p := 293893) (q := 769) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 300536 with h | h
  · exact window_general (p := 292363) (q := 769) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 302056 with h | h
  · exact window_general (p := 297019) (q := 773) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 303590 with h | h
  · exact window_general (p := 289309) (q := 769) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 305134 with h | h
  · exact window_general (p := 293941) (q := 773) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 306656 with h | h
  · exact window_general (p := 286243) (q := 769) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 308196 with h | h
  · exact window_general (p := 290879) (q := 773) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 309732 with h | h
  · exact window_general (p := 289343) (q := 773) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 311306 with h | h
  · exact window_general (p := 309637) (q := 787) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 312862 with h | h
  · exact window_general (p := 308081) (q := 787) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 314432 with h | h
  · exact window_general (p := 306511) (q := 787) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 316006 with h | h
  · exact window_general (p := 304937) (q := 787) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 317576 with h | h
  · exact window_general (p := 303367) (q := 787) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 319150 with h | h
  · exact window_general (p := 301793) (q := 787) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 320736 with h | h
  · exact window_general (p := 316067) (q := 797) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 322312 with h | h
  · exact window_general (p := 314491) (q := 797) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 323904 with h | h
  · exact window_general (p := 312899) (q := 797) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 325480 with h | h
  · exact window_general (p := 311323) (q := 797) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 327072 with h | h
  · exact window_general (p := 309731) (q := 797) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 328666 with h | h
  · exact window_general (p := 308137) (q := 797) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 330250 with h | h
  · exact window_general (p := 325849) (q := 809) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 331870 with h | h
  · exact window_general (p := 327473) (q := 811) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 333482 with h | h
  · exact window_general (p := 325861) (q := 811) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 335104 with h | h
  · exact window_general (p := 324239) (q := 811) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 336716 with h | h
  · exact window_general (p := 322627) (q := 811) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 338336 with h | h
  · exact window_general (p := 321007) (q := 811) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 339964 with h | h
  · exact window_general (p := 335719) (q := 821) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 341608 with h | h
  · exact window_general (p := 337367) (q := 823) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 343246 with h | h
  · exact window_general (p := 335729) (q := 823) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 344896 with h | h
  · exact window_general (p := 340687) (q := 827) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 346552 with h | h
  · exact window_general (p := 342347) (q := 829) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 348206 with h | h
  · exact window_general (p := 340693) (q := 829) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 349850 with h | h
  · exact window_general (p := 339049) (q := 829) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 351502 with h | h
  · exact window_general (p := 337397) (q := 829) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 353156 with h | h
  · exact window_general (p := 335743) (q := 829) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 354832 with h | h
  · exact window_general (p := 350767) (q := 839) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 356506 with h | h
  · exact window_general (p := 349093) (q := 839) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 358162 with h | h
  · exact window_general (p := 347437) (q := 839) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 359830 with h | h
  · exact window_general (p := 345769) (q := 839) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 361488 with h | h
  · exact window_general (p := 344111) (q := 839) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 363150 with h | h
  · exact window_general (p := 342449) (q := 839) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 364822 with h | h
  · exact window_general (p := 340777) (q := 839) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 366514 with h | h
  · exact window_general (p := 362801) (q := 853) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 368204 with h | h
  · exact window_general (p := 361111) (q := 853) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 369904 with h | h
  · exact window_general (p := 366259) (q := 857) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 371592 with h | h
  · exact window_general (p := 364571) (q := 857) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 373306 with h | h
  · exact window_general (p := 366293) (q := 859) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  exact window_general (p := 371471) (q := 863) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)

theorem cov_375025_465598 (n : ℕ) (hlo : 375025 ≤ n) (hhi : n ≤ 465598) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  rcases le_or_gt n 376744 with h | h
  · exact window_general (p := 369751) (q := 863) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 378466 with h | h
  · exact window_general (p := 368029) (q := 863) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 380188 with h | h
  · exact window_general (p := 366307) (q := 863) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 381912 with h | h
  · exact window_general (p := 364583) (q := 863) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 383632 with h | h
  · exact window_general (p := 362863) (q := 863) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 385336 with h | h
  · exact window_general (p := 361159) (q := 863) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 387086 with h | h
  · exact window_general (p := 383797) (q := 877) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 388822 with h | h
  · exact window_general (p := 382061) (q := 877) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 390582 with h | h
  · exact window_general (p := 387341) (q := 881) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 392344 with h | h
  · exact window_general (p := 389111) (q := 883) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 394084 with h | h
  · exact window_general (p := 387371) (q := 883) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 395844 with h | h
  · exact window_general (p := 392699) (q := 887) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 397590 with h | h
  · exact window_general (p := 390953) (q := 887) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 399354 with h | h
  · exact window_general (p := 389189) (q := 887) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 401110 with h | h
  · exact window_general (p := 387433) (q := 887) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 402882 with h | h
  · exact window_general (p := 385661) (q := 887) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 404652 with h | h
  · exact window_general (p := 383891) (q := 887) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 406426 with h | h
  · exact window_general (p := 382117) (q := 887) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 408180 with h | h
  · exact window_general (p := 380363) (q := 887) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 409950 with h | h
  · exact window_general (p := 378593) (q := 887) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 411724 with h | h
  · exact window_general (p := 376819) (q := 887) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 413534 with h | h
  · exact window_general (p := 410929) (q := 907) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 415342 with h | h
  · exact window_general (p := 409121) (q := 907) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 417136 with h | h
  · exact window_general (p := 414607) (q := 911) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 418950 with h | h
  · exact window_general (p := 412793) (q := 911) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 420760 with h | h
  · exact window_general (p := 410983) (q := 911) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 422580 with h | h
  · exact window_general (p := 409163) (q := 911) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 424412 with h | h
  · exact window_general (p := 421987) (q := 919) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 426250 with h | h
  · exact window_general (p := 420149) (q := 919) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 428078 with h | h
  · exact window_general (p := 418321) (q := 919) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 429908 with h | h
  · exact window_general (p := 416491) (q := 919) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 431746 with h | h
  · exact window_general (p := 414653) (q := 919) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 433602 with h | h
  · exact window_general (p := 431297) (q := 929) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 435450 with h | h
  · exact window_general (p := 429449) (q := 929) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 437308 with h | h
  · exact window_general (p := 427591) (q := 929) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 439142 with h | h
  · exact window_general (p := 407257) (q := 919) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 441016 with h | h
  · exact window_general (p := 438827) (q := 937) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 442886 with h | h
  · exact window_general (p := 436957) (q := 937) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 444762 with h | h
  · exact window_general (p := 442601) (q := 941) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 446640 with h | h
  · exact window_general (p := 440723) (q := 941) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 448516 with h | h
  · exact window_general (p := 438847) (q := 941) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 450400 with h | h
  · exact window_general (p := 448303) (q := 947) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 452286 with h | h
  · exact window_general (p := 446417) (q := 947) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 454180 with h | h
  · exact window_general (p := 444523) (q := 947) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 456084 with h | h
  · exact window_general (p := 454031) (q := 953) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 457984 with h | h
  · exact window_general (p := 452131) (q := 953) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 459888 with h | h
  · exact window_general (p := 450227) (q := 953) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 461794 with h | h
  · exact window_general (p := 448321) (q := 953) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 463698 with h | h
  · exact window_general (p := 446417) (q := 953) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  exact window_general (p := 444517) (q := 953) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)

theorem cov_465599_566004 (n : ℕ) (hlo : 465599 ≤ n) (hhi : n ≤ 566004) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  rcases le_or_gt n 467496 with h | h
  · exact window_general (p := 442619) (q := 953) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 469398 with h | h
  · exact window_general (p := 440717) (q := 953) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 471322 with h | h
  · exact window_general (p := 465701) (q := 967) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 473242 with h | h
  · exact window_general (p := 463781) (q := 967) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 475170 with h | h
  · exact window_general (p := 469613) (q := 971) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 477112 with h | h
  · exact window_general (p := 467671) (q := 971) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 479044 with h | h
  · exact window_general (p := 465739) (q := 971) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 480972 with h | h
  · exact window_general (p := 475511) (q := 977) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 482904 with h | h
  · exact window_general (p := 473579) (q := 977) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 484842 with h | h
  · exact window_general (p := 471641) (q := 977) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 486808 with h | h
  · exact window_general (p := 481447) (q := 983) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 488766 with h | h
  · exact window_general (p := 479489) (q := 983) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 490732 with h | h
  · exact window_general (p := 477523) (q := 983) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 492672 with h | h
  · exact window_general (p := 475583) (q := 983) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 494654 with h | h
  · exact window_general (p := 489409) (q := 991) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 496636 with h | h
  · exact window_general (p := 487427) (q := 991) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 498616 with h | h
  · exact window_general (p := 485447) (q := 991) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 500602 with h | h
  · exact window_general (p := 495401) (q := 997) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 502570 with h | h
  · exact window_general (p := 493433) (q := 997) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 504542 with h | h
  · exact window_general (p := 491461) (q := 997) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 506524 with h | h
  · exact window_general (p := 489479) (q := 997) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 508514 with h | h
  · exact window_general (p := 487489) (q := 997) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 510506 with h | h
  · exact window_general (p := 485497) (q := 997) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 512510 with h | h
  · exact window_general (p := 507589) (q := 1009) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 514526 with h | h
  · exact window_general (p := 505573) (q := 1009) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 516526 with h | h
  · exact window_general (p := 511669) (q := 1013) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 518548 with h | h
  · exact window_general (p := 509647) (q := 1013) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 520564 with h | h
  · exact window_general (p := 507631) (q := 1013) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 522582 with h | h
  · exact window_general (p := 517817) (q := 1019) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 524620 with h | h
  · exact window_general (p := 519863) (q := 1021) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 526660 with h | h
  · exact window_general (p := 517823) (q := 1021) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 528700 with h | h
  · exact window_general (p := 515783) (q := 1021) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 530734 with h | h
  · exact window_general (p := 513749) (q := 1021) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 532772 with h | h
  · exact window_general (p := 511711) (q := 1021) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 534826 with h | h
  · exact window_general (p := 530197) (q := 1031) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 536888 with h | h
  · exact window_general (p := 532267) (q := 1033) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 538952 with h | h
  · exact window_general (p := 530203) (q := 1033) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 541018 with h | h
  · exact window_general (p := 528137) (q := 1033) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 543088 with h | h
  · exact window_general (p := 538511) (q := 1039) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 545158 with h | h
  · exact window_general (p := 536441) (q := 1039) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 547232 with h | h
  · exact window_general (p := 534367) (q := 1039) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 549292 with h | h
  · exact window_general (p := 532307) (q := 1039) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 551362 with h | h
  · exact window_general (p := 530237) (q := 1039) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 553436 with h | h
  · exact window_general (p := 528163) (q := 1039) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 555524 with h | h
  · exact window_general (p := 551179) (q := 1051) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 557614 with h | h
  · exact window_general (p := 549089) (q := 1051) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 559696 with h | h
  · exact window_general (p := 547007) (q := 1051) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 561784 with h | h
  · exact window_general (p := 544919) (q := 1051) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 563882 with h | h
  · exact window_general (p := 542821) (q := 1051) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  exact window_general (p := 561839) (q := 1061) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)

theorem cov_566005_676174 (n : ℕ) (hlo : 566005 ≤ n) (hhi : n ≤ 676174) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  rcases le_or_gt n 568124 with h | h
  · exact window_general (p := 563971) (q := 1063) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 570232 with h | h
  · exact window_general (p := 557611) (q := 1061) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 572356 with h | h
  · exact window_general (p := 559739) (q := 1063) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 574492 with h | h
  · exact window_general (p := 570407) (q := 1069) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 576626 with h | h
  · exact window_general (p := 568273) (q := 1069) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 578750 with h | h
  · exact window_general (p := 566149) (q := 1069) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 580886 with h | h
  · exact window_general (p := 564013) (q := 1069) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 583006 with h | h
  · exact window_general (p := 549089) (q := 1063) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 585122 with h | h
  · exact window_general (p := 559777) (q := 1069) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 587260 with h | h
  · exact window_general (p := 557639) (q := 1069) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 589378 with h | h
  · exact window_general (p := 555521) (q := 1069) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 591488 with h | h
  · exact window_general (p := 553411) (q := 1069) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 593644 with h | h
  · exact window_general (p := 590099) (q := 1087) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 595816 with h | h
  · exact window_general (p := 587927) (q := 1087) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 597996 with h | h
  · exact window_general (p := 594467) (q := 1091) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 600182 with h | h
  · exact window_general (p := 596653) (q := 1093) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 602368 with h | h
  · exact window_general (p := 594467) (q := 1093) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 604560 with h | h
  · exact window_general (p := 601043) (q := 1097) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 606750 with h | h
  · exact window_general (p := 598853) (q := 1097) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 608940 with h | h
  · exact window_general (p := 596663) (q := 1097) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 611146 with h | h
  · exact window_general (p := 607669) (q := 1103) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 613344 with h | h
  · exact window_general (p := 605471) (q := 1103) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 615532 with h | h
  · exact window_general (p := 603283) (q := 1103) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 617722 with h | h
  · exact window_general (p := 614377) (q := 1109) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 619930 with h | h
  · exact window_general (p := 612169) (q := 1109) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 622120 with h | h
  · exact window_general (p := 609979) (q := 1109) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 624330 with h | h
  · exact window_general (p := 607769) (q := 1109) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 626540 with h | h
  · exact window_general (p := 623383) (q := 1117) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 628750 with h | h
  · exact window_general (p := 603349) (q := 1109) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 630982 with h | h
  · exact window_general (p := 618941) (q := 1117) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 633224 with h | h
  · exact window_general (p := 630151) (q := 1123) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 635464 with h | h
  · exact window_general (p := 627911) (q := 1123) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 637694 with h | h
  · exact window_general (p := 612229) (q := 1117) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 639952 with h | h
  · exact window_general (p := 636947) (q := 1129) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 642196 with h | h
  · exact window_general (p := 634703) (q := 1129) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 644452 with h | h
  · exact window_general (p := 632447) (q := 1129) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 646706 with h | h
  · exact window_general (p := 630193) (q := 1129) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 648956 with h | h
  · exact window_general (p := 627943) (q := 1129) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 651202 with h | h
  · exact window_general (p := 625697) (q := 1129) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 653446 with h | h
  · exact window_general (p := 609929) (q := 1123) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 655682 with h | h
  · exact window_general (p := 621217) (q := 1129) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 657928 with h | h
  · exact window_general (p := 618971) (q := 1129) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 660182 with h | h
  · exact window_general (p := 616717) (q := 1129) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 662422 with h | h
  · exact window_general (p := 614477) (q := 1129) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 664676 with h | h
  · exact window_general (p := 612223) (q := 1129) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 666972 with h | h
  · exact window_general (p := 660131) (q := 1151) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 669272 with h | h
  · exact window_general (p := 662443) (q := 1153) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 671578 with h | h
  · exact window_general (p := 660137) (q := 1153) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 673874 with h | h
  · exact window_general (p := 657841) (q := 1153) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  exact window_general (p := 655541) (q := 1153) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)

theorem cov_676175_796408 (n : ℕ) (hlo : 676175 ≤ n) (hhi : n ≤ 796408) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  rcases le_or_gt n 678472 with h | h
  · exact window_general (p := 653243) (q := 1153) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 680796 with h | h
  · exact window_general (p := 674099) (q := 1163) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 683118 with h | h
  · exact window_general (p := 671777) (q := 1163) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 685444 with h | h
  · exact window_general (p := 669451) (q := 1163) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 687768 with h | h
  · exact window_general (p := 667127) (q := 1163) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 690106 with h | h
  · exact window_general (p := 683477) (q := 1171) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 692446 with h | h
  · exact window_general (p := 681137) (q := 1171) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 694774 with h | h
  · exact window_general (p := 678809) (q := 1171) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 697114 with h | h
  · exact window_general (p := 676469) (q := 1171) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 699452 with h | h
  · exact window_general (p := 674131) (q := 1171) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 701814 with h | h
  · exact window_general (p := 695309) (q := 1181) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 704166 with h | h
  · exact window_general (p := 692957) (q := 1181) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 706516 with h | h
  · exact window_general (p := 690607) (q := 1181) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 708874 with h | h
  · exact window_general (p := 702469) (q := 1187) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 711244 with h | h
  · exact window_general (p := 700099) (q := 1187) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 713616 with h | h
  · exact window_general (p := 697727) (q := 1187) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 715986 with h | h
  · exact window_general (p := 709649) (q := 1193) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 718356 with h | h
  · exact window_general (p := 707279) (q := 1193) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 720738 with h | h
  · exact window_general (p := 704897) (q := 1193) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 723124 with h | h
  · exact window_general (p := 702511) (q := 1193) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 725522 with h | h
  · exact window_general (p := 719281) (q := 1201) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 727906 with h | h
  · exact window_general (p := 716897) (q := 1201) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 730300 with h | h
  · exact window_general (p := 714503) (q := 1201) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 732694 with h | h
  · exact window_general (p := 712109) (q := 1201) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 735074 with h | h
  · exact window_general (p := 709729) (q := 1201) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 737462 with h | h
  · exact window_general (p := 707341) (q := 1201) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 739876 with h | h
  · exact window_general (p := 733919) (q := 1213) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 742294 with h | h
  · exact window_general (p := 731501) (q := 1213) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 744726 with h | h
  · exact window_general (p := 738797) (q := 1217) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 747160 with h | h
  · exact window_general (p := 736363) (q := 1217) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 749586 with h | h
  · exact window_general (p := 733937) (q := 1217) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 752022 with h | h
  · exact window_general (p := 746153) (q := 1223) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 754464 with h | h
  · exact window_general (p := 743711) (q := 1223) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 756892 with h | h
  · exact window_general (p := 741283) (q := 1223) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 759330 with h | h
  · exact window_general (p := 753569) (q := 1229) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 761780 with h | h
  · exact window_general (p := 756043) (q := 1231) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 764240 with h | h
  · exact window_general (p := 753583) (q := 1231) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 766700 with h | h
  · exact window_general (p := 751123) (q := 1231) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 769172 with h | h
  · exact window_general (p := 763471) (q := 1237) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 771646 with h | h
  · exact window_general (p := 760997) (q := 1237) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 774092 with h | h
  · exact window_general (p := 758551) (q := 1237) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 776546 with h | h
  · exact window_general (p := 756097) (q := 1237) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 779012 with h | h
  · exact window_general (p := 753631) (q := 1237) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 781462 with h | h
  · exact window_general (p := 751181) (q := 1237) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 783958 with h | h
  · exact window_general (p := 778541) (q := 1249) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 786452 with h | h
  · exact window_general (p := 776047) (q := 1249) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 788938 with h | h
  · exact window_general (p := 773561) (q := 1249) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 791426 with h | h
  · exact window_general (p := 771073) (q := 1249) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 793910 with h | h
  · exact window_general (p := 768589) (q := 1249) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  exact window_general (p := 791191) (q := 1259) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)

theorem cov_796409_926086 (n : ℕ) (hlo : 796409 ≤ n) (hhi : n ≤ 926086) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  rcases le_or_gt n 798922 with h | h
  · exact window_general (p := 788677) (q := 1259) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 801432 with h | h
  · exact window_general (p := 786167) (q := 1259) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 803938 with h | h
  · exact window_general (p := 783661) (q := 1259) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 806436 with h | h
  · exact window_general (p := 781163) (q := 1259) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 808936 with h | h
  · exact window_general (p := 778663) (q := 1259) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 811440 with h | h
  · exact window_general (p := 776159) (q := 1259) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 813942 with h | h
  · exact window_general (p := 773657) (q := 1259) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 816456 with h | h
  · exact window_general (p := 771143) (q := 1259) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 819004 with h | h
  · exact window_general (p := 814279) (q := 1277) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 821560 with h | h
  · exact window_general (p := 816839) (q := 1279) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 824090 with h | h
  · exact window_general (p := 814309) (q := 1279) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 826656 with h | h
  · exact window_general (p := 821999) (q := 1283) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 829218 with h | h
  · exact window_general (p := 819437) (q := 1283) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 831772 with h | h
  · exact window_general (p := 816883) (q := 1283) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 834342 with h | h
  · exact window_general (p := 829757) (q := 1289) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 836924 with h | h
  · exact window_general (p := 832339) (q := 1291) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 839506 with h | h
  · exact window_general (p := 829757) (q := 1291) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 842062 with h | h
  · exact window_general (p := 822037) (q := 1289) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 844654 with h | h
  · exact window_general (p := 840149) (q := 1297) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 847220 with h | h
  · exact window_general (p := 837583) (q := 1297) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 849822 with h | h
  · exact window_general (p := 845381) (q := 1301) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 852424 with h | h
  · exact window_general (p := 847991) (q := 1303) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 855028 with h | h
  · exact window_general (p := 845387) (q := 1303) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 857622 with h | h
  · exact window_general (p := 853241) (q := 1307) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 860232 with h | h
  · exact window_general (p := 850631) (q := 1307) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 862846 with h | h
  · exact window_general (p := 848017) (q := 1307) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 865432 with h | h
  · exact window_general (p := 845431) (q := 1307) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 868044 with h | h
  · exact window_general (p := 842819) (q := 1307) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 870640 with h | h
  · exact window_general (p := 840223) (q := 1307) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 873268 with h | h
  · exact window_general (p := 869131) (q := 1319) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 875894 with h | h
  · exact window_general (p := 871789) (q := 1321) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 878530 with h | h
  · exact window_general (p := 869153) (q := 1321) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 881170 with h | h
  · exact window_general (p := 866513) (q := 1321) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 883804 with h | h
  · exact window_general (p := 863879) (q := 1321) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 886450 with h | h
  · exact window_general (p := 877133) (q := 1327) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 889096 with h | h
  · exact window_general (p := 874487) (q := 1327) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 891746 with h | h
  · exact window_general (p := 871837) (q := 1327) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 894380 with h | h
  · exact window_general (p := 869203) (q := 1327) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 897010 with h | h
  · exact window_general (p := 866573) (q := 1327) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 899662 with h | h
  · exact window_general (p := 863921) (q := 1327) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 902290 with h | h
  · exact window_general (p := 861293) (q := 1327) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 904924 with h | h
  · exact window_general (p := 842759) (q := 1321) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 907562 with h | h
  · exact window_general (p := 856021) (q := 1327) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 910196 with h | h
  · exact window_general (p := 853387) (q := 1327) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 912830 with h | h
  · exact window_general (p := 850753) (q := 1327) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 915482 with h | h
  · exact window_general (p := 848101) (q := 1327) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 918136 with h | h
  · exact window_general (p := 845447) (q := 1327) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 920782 with h | h
  · exact window_general (p := 842801) (q := 1327) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 923434 with h | h
  · exact window_general (p := 840149) (q := 1327) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  exact window_general (p := 837497) (q := 1327) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)

theorem cov_926087_1065946 (n : ℕ) (hlo : 926087 ≤ n) (hhi : n ≤ 1065946) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  rcases le_or_gt n 928726 with h | h
  · exact window_general (p := 834857) (q := 1327) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 931444 with h | h
  · exact window_general (p := 923599) (q := 1361) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 934152 with h | h
  · exact window_general (p := 920891) (q := 1361) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 936870 with h | h
  · exact window_general (p := 918173) (q := 1361) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 939586 with h | h
  · exact window_general (p := 931837) (q := 1367) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 942310 with h | h
  · exact window_general (p := 929113) (q := 1367) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 945034 with h | h
  · exact window_general (p := 926389) (q := 1367) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 947778 with h | h
  · exact window_general (p := 940097) (q := 1373) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 950524 with h | h
  · exact window_general (p := 937351) (q := 1373) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 953268 with h | h
  · exact window_general (p := 934607) (q := 1373) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 956002 with h | h
  · exact window_general (p := 931873) (q := 1373) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 958762 with h | h
  · exact window_general (p := 951161) (q := 1381) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 961522 with h | h
  · exact window_general (p := 948401) (q := 1381) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 964276 with h | h
  · exact window_general (p := 945647) (q := 1381) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 967034 with h | h
  · exact window_general (p := 942889) (q := 1381) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 969796 with h | h
  · exact window_general (p := 940127) (q := 1381) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 972550 with h | h
  · exact window_general (p := 937373) (q := 1381) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 975310 with h | h
  · exact window_general (p := 934613) (q := 1381) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 978064 with h | h
  · exact window_general (p := 931859) (q := 1381) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 980810 with h | h
  · exact window_general (p := 929113) (q := 1381) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 983596 with h | h
  · exact window_general (p := 976403) (q := 1399) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 986368 with h | h
  · exact window_general (p := 973631) (q := 1399) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 989152 with h | h
  · exact window_general (p := 970847) (q := 1399) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 991936 with h | h
  · exact window_general (p := 968063) (q := 1399) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 994732 with h | h
  · exact window_general (p := 965267) (q := 1399) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 997540 with h | h
  · exact window_general (p := 990559) (q := 1409) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1000322 with h | h
  · exact window_general (p := 959677) (q := 1399) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1003140 with h | h
  · exact window_general (p := 984959) (q := 1409) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1005952 with h | h
  · exact window_general (p := 982147) (q := 1409) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1008766 with h | h
  · exact window_general (p := 979333) (q := 1409) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1011562 with h | h
  · exact window_general (p := 976537) (q := 1409) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1014372 with h | h
  · exact window_general (p := 973727) (q := 1409) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1017208 with h | h
  · exact window_general (p := 1010567) (q := 1423) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1020052 with h | h
  · exact window_general (p := 1007723) (q := 1423) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1022880 with h | h
  · exact window_general (p := 1016303) (q := 1427) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1025726 with h | h
  · exact window_general (p := 1019173) (q := 1429) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1028560 with h | h
  · exact window_general (p := 1016339) (q := 1429) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1031424 with h | h
  · exact window_general (p := 1024931) (q := 1433) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1034284 with h | h
  · exact window_general (p := 1022071) (q := 1433) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1037146 with h | h
  · exact window_general (p := 1019209) (q := 1433) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1039998 with h | h
  · exact window_general (p := 1033601) (q := 1439) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1042876 with h | h
  · exact window_general (p := 1030723) (q := 1439) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1045746 with h | h
  · exact window_general (p := 1027853) (q := 1439) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1048612 with h | h
  · exact window_general (p := 1024987) (q := 1439) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1051504 with h | h
  · exact window_general (p := 1045199) (q := 1447) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1054394 with h | h
  · exact window_general (p := 1042309) (q := 1447) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1057296 with h | h
  · exact window_general (p := 1051007) (q := 1451) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1060180 with h | h
  · exact window_general (p := 1048123) (q := 1451) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1063064 with h | h
  · exact window_general (p := 1051051) (q := 1453) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  exact window_general (p := 1042357) (q := 1451) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)

theorem cov_1065947_1215942 (n : ℕ) (hlo : 1065947 ≤ n) (hhi : n ≤ 1215942) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  rcases le_or_gt n 1068842 with h | h
  · exact window_general (p := 1045273) (q := 1453) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1071752 with h | h
  · exact window_general (p := 1059847) (q := 1459) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1074670 with h | h
  · exact window_general (p := 1056929) (q := 1459) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1077586 with h | h
  · exact window_general (p := 1054013) (q := 1459) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1080484 with h | h
  · exact window_general (p := 1033631) (q := 1453) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1083386 with h | h
  · exact window_general (p := 1048213) (q := 1459) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1086320 with h | h
  · exact window_general (p := 1080463) (q := 1471) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1089250 with h | h
  · exact window_general (p := 1077533) (q := 1471) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1092176 with h | h
  · exact window_general (p := 1074607) (q := 1471) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1095112 with h | h
  · exact window_general (p := 1071671) (q := 1471) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1098032 with h | h
  · exact window_general (p := 1068751) (q := 1471) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1100980 with h | h
  · exact window_general (p := 1095343) (q := 1481) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1103944 with h | h
  · exact window_general (p := 1098311) (q := 1483) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1106906 with h | h
  · exact window_general (p := 1095349) (q := 1483) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1109854 with h | h
  · exact window_general (p := 1104289) (q := 1487) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1112830 with h | h
  · exact window_general (p := 1107269) (q := 1489) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1115806 with h | h
  · exact window_general (p := 1104293) (q := 1489) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1118782 with h | h
  · exact window_general (p := 1113253) (q := 1493) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1121766 with h | h
  · exact window_general (p := 1110269) (q := 1493) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1124722 with h | h
  · exact window_general (p := 1089421) (q := 1487) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1127718 with h | h
  · exact window_general (p := 1122281) (q := 1499) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1130700 with h | h
  · exact window_general (p := 1119299) (q := 1499) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1133698 with h | h
  · exact window_general (p := 1116301) (q := 1499) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1136682 with h | h
  · exact window_general (p := 1113317) (q := 1499) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1139668 with h | h
  · exact window_general (p := 1110331) (q := 1499) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1142658 with h | h
  · exact window_general (p := 1107341) (q := 1499) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1145680 with h | h
  · exact window_general (p := 1140463) (q := 1511) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1148686 with h | h
  · exact window_general (p := 1137457) (q := 1511) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1151706 with h | h
  · exact window_general (p := 1134437) (q := 1511) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1154724 with h | h
  · exact window_general (p := 1131419) (q := 1511) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1157746 with h | h
  · exact window_general (p := 1128397) (q := 1511) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1160764 with h | h
  · exact window_general (p := 1125379) (q := 1511) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1163806 with h | h
  · exact window_general (p := 1158769) (q := 1523) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1166842 with h | h
  · exact window_general (p := 1155733) (q := 1523) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1169868 with h | h
  · exact window_general (p := 1152707) (q := 1523) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1172914 with h | h
  · exact window_general (p := 1149661) (q := 1523) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1175966 with h | h
  · exact window_general (p := 1171057) (q := 1531) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1179022 with h | h
  · exact window_general (p := 1168001) (q := 1531) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1182082 with h | h
  · exact window_general (p := 1164941) (q := 1531) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1185140 with h | h
  · exact window_general (p := 1161883) (q := 1531) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1188202 with h | h
  · exact window_general (p := 1158821) (q := 1531) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1191246 with h | h
  · exact window_general (p := 1131329) (q := 1523) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1194332 with h | h
  · exact window_general (p := 1189603) (q := 1543) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1197418 with h | h
  · exact window_general (p := 1186517) (q := 1543) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1200488 with h | h
  · exact window_general (p := 1183447) (q := 1543) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1203572 with h | h
  · exact window_general (p := 1198927) (q := 1549) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1206662 with h | h
  · exact window_general (p := 1195837) (q := 1549) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1209756 with h | h
  · exact window_general (p := 1205159) (q := 1553) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1212858 with h | h
  · exact window_general (p := 1202057) (q := 1553) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  exact window_general (p := 1198973) (q := 1553) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)

theorem cov_1215943_1375834 (n : ℕ) (hlo : 1215943 ≤ n) (hhi : n ≤ 1375834) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  rcases le_or_gt n 1219032 with h | h
  · exact window_general (p := 1214567) (q := 1559) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1222122 with h | h
  · exact window_general (p := 1211477) (q := 1559) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1225228 with h | h
  · exact window_general (p := 1208371) (q := 1559) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1228342 with h | h
  · exact window_general (p := 1205257) (q := 1559) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1231472 with h | h
  · exact window_general (p := 1227151) (q := 1567) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1234594 with h | h
  · exact window_general (p := 1224029) (q := 1567) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1237710 with h | h
  · exact window_general (p := 1233473) (q := 1571) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1240852 with h | h
  · exact window_general (p := 1230331) (q := 1571) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1243984 with h | h
  · exact window_general (p := 1214639) (q := 1567) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1247124 with h | h
  · exact window_general (p := 1224059) (q := 1571) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1250266 with h | h
  · exact window_general (p := 1220917) (q := 1571) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1253422 with h | h
  · exact window_general (p := 1242977) (q := 1579) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1256586 with h | h
  · exact window_general (p := 1252469) (q := 1583) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1259736 with h | h
  · exact window_general (p := 1249319) (q := 1583) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1262874 with h | h
  · exact window_general (p := 1246181) (q := 1583) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1266032 with h | h
  · exact window_general (p := 1230367) (q := 1579) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1269178 with h | h
  · exact window_general (p := 1239877) (q := 1583) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1272342 with h | h
  · exact window_general (p := 1236713) (q := 1583) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1275492 with h | h
  · exact window_general (p := 1233563) (q := 1583) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1278682 with h | h
  · exact window_general (p := 1274921) (q := 1597) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1281872 with h | h
  · exact window_general (p := 1271731) (q := 1597) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1285072 with h | h
  · exact window_general (p := 1281331) (q := 1601) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1288272 with h | h
  · exact window_general (p := 1278131) (q := 1601) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1291474 with h | h
  · exact window_general (p := 1274929) (q := 1601) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1294680 with h | h
  · exact window_general (p := 1290983) (q := 1607) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1297898 with h | h
  · exact window_general (p := 1294201) (q := 1609) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1301116 with h | h
  · exact window_general (p := 1290983) (q := 1609) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1304326 with h | h
  · exact window_general (p := 1300669) (q := 1613) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1307548 with h | h
  · exact window_general (p := 1297447) (q := 1613) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1310764 with h | h
  · exact window_general (p := 1294231) (q := 1613) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1314000 with h | h
  · exact window_general (p := 1310399) (q := 1619) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1317232 with h | h
  · exact window_general (p := 1313651) (q := 1621) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1320466 with h | h
  · exact window_general (p := 1310417) (q := 1621) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1323700 with h | h
  · exact window_general (p := 1307183) (q := 1621) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1326952 with h | h
  · exact window_general (p := 1323431) (q := 1627) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1330202 with h | h
  · exact window_general (p := 1320181) (q := 1627) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1333432 with h | h
  · exact window_general (p := 1316951) (q := 1627) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1336684 with h | h
  · exact window_general (p := 1313699) (q := 1627) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1339916 with h | h
  · exact window_general (p := 1310467) (q := 1627) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1343190 with h | h
  · exact window_general (p := 1339853) (q := 1637) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1346464 with h | h
  · exact window_general (p := 1336579) (q := 1637) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1349730 with h | h
  · exact window_general (p := 1333313) (q := 1637) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1352982 with h | h
  · exact window_general (p := 1330061) (q := 1637) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1356252 with h | h
  · exact window_general (p := 1326791) (q := 1637) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1359514 with h | h
  · exact window_general (p := 1323529) (q := 1637) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1362760 with h | h
  · exact window_general (p := 1287623) (q := 1627) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1366030 with h | h
  · exact window_general (p := 1317013) (q := 1637) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1369296 with h | h
  · exact window_general (p := 1313747) (q := 1637) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1372570 with h | h
  · exact window_general (p := 1310473) (q := 1637) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  exact window_general (p := 1307209) (q := 1637) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)

theorem cov_1375835_1545464 (n : ℕ) (hlo : 1375835 ≤ n) (hhi : n ≤ 1545464) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  rcases le_or_gt n 1379132 with h | h
  · exact window_general (p := 1369831) (q := 1657) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1382446 with h | h
  · exact window_general (p := 1366517) (q := 1657) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1385756 with h | h
  · exact window_general (p := 1363207) (q := 1657) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1389082 with h | h
  · exact window_general (p := 1379813) (q := 1663) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1392404 with h | h
  · exact window_general (p := 1376491) (q := 1663) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1395732 with h | h
  · exact window_general (p := 1386491) (q := 1667) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1399066 with h | h
  · exact window_general (p := 1389833) (q := 1669) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1402400 with h | h
  · exact window_general (p := 1386499) (q := 1669) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1405730 with h | h
  · exact window_general (p := 1383169) (q := 1669) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1409042 with h | h
  · exact window_general (p := 1379857) (q := 1669) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1412366 with h | h
  · exact window_general (p := 1376533) (q := 1669) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1415698 with h | h
  · exact window_general (p := 1373201) (q := 1669) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1419028 with h | h
  · exact window_general (p := 1369871) (q := 1669) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1422356 with h | h
  · exact window_general (p := 1366543) (q := 1669) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1425692 with h | h
  · exact window_general (p := 1363207) (q := 1669) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1429028 with h | h
  · exact window_general (p := 1359871) (q := 1669) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1432360 with h | h
  · exact window_general (p := 1356539) (q := 1669) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1435678 with h | h
  · exact window_general (p := 1353221) (q := 1669) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1439048 with h | h
  · exact window_general (p := 1430587) (q := 1693) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1442414 with h | h
  · exact window_general (p := 1427221) (q := 1693) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1445794 with h | h
  · exact window_general (p := 1437409) (q := 1697) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1449188 with h | h
  · exact window_general (p := 1440811) (q := 1699) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1452578 with h | h
  · exact window_general (p := 1437421) (q := 1699) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1455976 with h | h
  · exact window_general (p := 1434023) (q := 1699) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1459358 with h | h
  · exact window_general (p := 1430641) (q := 1699) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1462738 with h | h
  · exact window_general (p := 1406897) (q := 1693) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1466142 with h | h
  · exact window_general (p := 1457957) (q := 1709) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1469560 with h | h
  · exact window_general (p := 1454539) (q := 1709) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1472976 with h | h
  · exact window_general (p := 1451123) (q := 1709) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1476388 with h | h
  · exact window_general (p := 1447711) (q := 1709) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1479790 with h | h
  · exact window_general (p := 1444309) (q := 1709) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1483186 with h | h
  · exact window_general (p := 1440913) (q := 1709) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1486620 with h | h
  · exact window_general (p := 1478663) (q := 1721) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1490054 with h | h
  · exact window_general (p := 1482121) (q := 1723) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1493492 with h | h
  · exact window_general (p := 1478683) (q := 1723) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1496938 with h | h
  · exact window_general (p := 1475237) (q := 1723) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1500368 with h | h
  · exact window_general (p := 1471807) (q := 1723) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1503788 with h | h
  · exact window_general (p := 1468387) (q := 1723) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1507234 with h | h
  · exact window_general (p := 1499521) (q := 1733) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1510696 with h | h
  · exact window_general (p := 1496059) (q := 1733) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1514158 with h | h
  · exact window_general (p := 1492597) (q := 1733) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1517602 with h | h
  · exact window_general (p := 1489153) (q := 1733) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1521076 with h | h
  · exact window_general (p := 1513487) (q := 1741) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1524550 with h | h
  · exact window_general (p := 1510013) (q := 1741) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1528012 with h | h
  · exact window_general (p := 1506551) (q := 1741) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1531496 with h | h
  · exact window_general (p := 1524007) (q := 1747) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1534976 with h | h
  · exact window_general (p := 1520527) (q := 1747) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1538464 with h | h
  · exact window_general (p := 1517039) (q := 1747) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1541966 with h | h
  · exact window_general (p := 1534549) (q := 1753) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  exact window_general (p := 1531051) (q := 1753) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)

theorem cov_1545465_1725060 (n : ℕ) (hlo : 1545465 ≤ n) (hhi : n ≤ 1725060) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  rcases le_or_gt n 1548964 with h | h
  · exact window_general (p := 1527551) (q := 1753) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1552478 with h | h
  · exact window_general (p := 1545121) (q := 1759) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1555970 with h | h
  · exact window_general (p := 1541629) (q := 1759) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1559488 with h | h
  · exact window_general (p := 1538111) (q := 1759) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1562998 with h | h
  · exact window_general (p := 1534601) (q := 1759) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1566508 with h | h
  · exact window_general (p := 1531091) (q := 1759) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1570022 with h | h
  · exact window_general (p := 1527577) (q := 1759) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1573540 with h | h
  · exact window_general (p := 1524059) (q := 1759) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1577056 with h | h
  · exact window_general (p := 1520543) (q := 1759) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1580572 with h | h
  · exact window_general (p := 1517027) (q := 1759) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1584100 with h | h
  · exact window_general (p := 1577183) (q := 1777) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1587640 with h | h
  · exact window_general (p := 1573643) (q := 1777) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1591192 with h | h
  · exact window_general (p := 1570091) (q := 1777) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1594756 with h | h
  · exact window_general (p := 1587899) (q := 1783) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1598312 with h | h
  · exact window_general (p := 1584343) (q := 1783) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1601886 with h | h
  · exact window_general (p := 1595057) (q := 1787) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1605448 with h | h
  · exact window_general (p := 1598651) (q := 1789) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1609018 with h | h
  · exact window_general (p := 1595081) (q := 1789) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1612592 with h | h
  · exact window_general (p := 1591507) (q := 1789) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1616146 with h | h
  · exact window_general (p := 1580797) (q := 1787) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1619710 with h | h
  · exact window_general (p := 1584389) (q := 1789) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1623276 with h | h
  · exact window_general (p := 1573667) (q := 1787) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1626874 with h | h
  · exact window_general (p := 1620329) (q := 1801) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1630454 with h | h
  · exact window_general (p := 1616749) (q := 1801) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1634054 with h | h
  · exact window_general (p := 1613149) (q := 1801) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1637654 with h | h
  · exact window_general (p := 1609549) (q := 1801) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1641232 with h | h
  · exact window_general (p := 1605971) (q := 1801) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1644824 with h | h
  · exact window_general (p := 1602379) (q := 1801) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1648432 with h | h
  · exact window_general (p := 1634911) (q := 1811) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1652046 with h | h
  · exact window_general (p := 1631297) (q := 1811) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1655650 with h | h
  · exact window_general (p := 1627693) (q := 1811) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1659262 with h | h
  · exact window_general (p := 1624081) (q := 1811) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1662882 with h | h
  · exact window_general (p := 1620461) (q := 1811) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1666518 with h | h
  · exact window_general (p := 1660457) (q := 1823) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1670148 with h | h
  · exact window_general (p := 1656827) (q := 1823) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1673794 with h | h
  · exact window_general (p := 1653181) (q := 1823) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1677436 with h | h
  · exact window_general (p := 1649539) (q := 1823) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1681090 with h | h
  · exact window_general (p := 1675133) (q := 1831) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1684730 with h | h
  · exact window_general (p := 1671493) (q := 1831) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1688390 with h | h
  · exact window_general (p := 1667833) (q := 1831) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1692036 with h | h
  · exact window_general (p := 1634939) (q := 1823) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1695670 with h | h
  · exact window_general (p := 1660553) (q := 1831) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1699324 with h | h
  · exact window_general (p := 1656899) (q := 1831) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1702972 with h | h
  · exact window_general (p := 1653251) (q := 1831) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1706632 with h | h
  · exact window_general (p := 1649591) (q := 1831) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1710310 with h | h
  · exact window_general (p := 1704793) (q := 1847) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1714002 with h | h
  · exact window_general (p := 1701101) (q := 1847) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1717696 with h | h
  · exact window_general (p := 1697407) (q := 1847) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1721374 with h | h
  · exact window_general (p := 1693729) (q := 1847) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  exact window_general (p := 1690043) (q := 1847) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)

theorem cov_1725061_1914610 (n : ℕ) (hlo : 1725061 ≤ n) (hhi : n ≤ 1914610) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  rcases le_or_gt n 1728750 with h | h
  · exact window_general (p := 1686353) (q := 1847) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1732440 with h | h
  · exact window_general (p := 1682663) (q := 1847) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1736156 with h | h
  · exact window_general (p := 1730887) (q := 1861) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1739864 with h | h
  · exact window_general (p := 1727179) (q := 1861) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1743562 with h | h
  · exact window_general (p := 1723481) (q := 1861) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1747280 with h | h
  · exact window_general (p := 1719763) (q := 1861) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1751012 with h | h
  · exact window_general (p := 1738411) (q := 1867) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1754742 with h | h
  · exact window_general (p := 1749641) (q := 1871) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1758472 with h | h
  · exact window_general (p := 1753403) (q := 1873) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1762202 with h | h
  · exact window_general (p := 1749673) (q := 1873) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1765936 with h | h
  · exact window_general (p := 1760947) (q := 1877) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1769672 with h | h
  · exact window_general (p := 1764727) (q := 1879) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1773418 with h | h
  · exact window_general (p := 1760981) (q := 1879) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1777166 with h | h
  · exact window_general (p := 1757233) (q := 1879) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1780918 with h | h
  · exact window_general (p := 1753481) (q := 1879) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1784668 with h | h
  · exact window_general (p := 1749731) (q := 1879) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1788432 with h | h
  · exact window_general (p := 1783667) (q := 1889) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1792210 with h | h
  · exact window_general (p := 1779889) (q := 1889) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1795986 with h | h
  · exact window_general (p := 1776113) (q := 1889) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1799758 with h | h
  · exact window_general (p := 1772341) (q := 1889) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1803516 with h | h
  · exact window_general (p := 1768583) (q := 1889) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1807290 with h | h
  · exact window_general (p := 1764809) (q := 1889) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1811076 with h | h
  · exact window_general (p := 1806527) (q := 1901) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1814866 with h | h
  · exact window_general (p := 1802737) (q := 1901) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1818660 with h | h
  · exact window_general (p := 1798943) (q := 1901) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1822464 with h | h
  · exact window_general (p := 1817999) (q := 1907) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1826260 with h | h
  · exact window_general (p := 1791343) (q := 1901) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1830066 with h | h
  · exact window_general (p := 1810397) (q := 1907) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1833876 with h | h
  · exact window_general (p := 1829519) (q := 1913) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1837702 with h | h
  · exact window_general (p := 1825693) (q := 1913) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1841524 with h | h
  · exact window_general (p := 1821871) (q := 1913) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1845346 with h | h
  · exact window_general (p := 1818049) (q := 1913) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1849162 with h | h
  · exact window_general (p := 1814233) (q := 1913) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1852986 with h | h
  · exact window_general (p := 1810409) (q := 1913) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1856806 with h | h
  · exact window_general (p := 1806589) (q := 1913) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1860604 with h | h
  · exact window_general (p := 1802791) (q := 1913) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1864428 with h | h
  · exact window_general (p := 1798967) (q := 1913) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1868262 with h | h
  · exact window_general (p := 1864361) (q := 1931) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1872124 with h | h
  · exact window_general (p := 1868231) (q := 1933) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1875964 with h | h
  · exact window_general (p := 1864391) (q := 1933) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1879822 with h | h
  · exact window_general (p := 1860533) (q := 1933) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1883680 with h | h
  · exact window_general (p := 1848943) (q := 1931) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1887538 with h | h
  · exact window_general (p := 1852817) (q := 1933) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1891386 with h | h
  · exact window_general (p := 1841237) (q := 1931) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1895236 with h | h
  · exact window_general (p := 1845119) (q := 1933) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1899094 with h | h
  · exact window_general (p := 1841261) (q := 1933) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1902958 with h | h
  · exact window_general (p := 1837397) (q := 1933) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1906842 with h | h
  · exact window_general (p := 1895657) (q := 1949) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1910714 with h | h
  · exact window_general (p := 1899589) (q := 1951) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  exact window_general (p := 1895693) (q := 1951) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)

theorem cov_1914611_2114062 (n : ℕ) (hlo : 1914611 ≤ n) (hhi : n ≤ 2114062) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  rcases le_or_gt n 1918496 with h | h
  · exact window_general (p := 1891807) (q := 1951) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1922386 with h | h
  · exact window_general (p := 1887917) (q := 1951) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1926276 with h | h
  · exact window_general (p := 1876223) (q := 1949) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1930174 with h | h
  · exact window_general (p := 1880129) (q := 1951) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1934062 with h | h
  · exact window_general (p := 1876241) (q := 1951) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1937952 with h | h
  · exact window_general (p := 1864547) (q := 1949) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1941844 with h | h
  · exact window_general (p := 1868459) (q := 1951) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1945744 with h | h
  · exact window_general (p := 1864559) (q := 1951) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1949644 with h | h
  · exact window_general (p := 1860659) (q := 1951) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1953582 with h | h
  · exact window_general (p := 1943093) (q := 1973) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1957524 with h | h
  · exact window_general (p := 1939151) (q := 1973) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1961458 with h | h
  · exact window_general (p := 1935217) (q := 1973) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1965412 with h | h
  · exact window_general (p := 1954987) (q := 1979) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1969356 with h | h
  · exact window_general (p := 1951043) (q := 1979) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1973308 with h | h
  · exact window_general (p := 1947091) (q := 1979) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1977258 with h | h
  · exact window_general (p := 1943141) (q := 1979) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1981222 with h | h
  · exact window_general (p := 1970921) (q := 1987) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1985180 with h | h
  · exact window_general (p := 1966963) (q := 1987) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1989152 with h | h
  · exact window_general (p := 1962991) (q := 1987) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1993126 with h | h
  · exact window_general (p := 1982909) (q := 1993) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 1997108 with h | h
  · exact window_general (p := 1978927) (q := 1993) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2001096 with h | h
  · exact window_general (p := 1990907) (q := 1997) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2005088 with h | h
  · exact window_general (p := 1994911) (q := 1999) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2009072 with h | h
  · exact window_general (p := 1990927) (q := 1999) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2013078 with h | h
  · exact window_general (p := 2002937) (q := 2003) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2017072 with h | h
  · exact window_general (p := 1998943) (q := 2003) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2021068 with h | h
  · exact window_general (p := 1994947) (q := 2003) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2025064 with h | h
  · exact window_general (p := 1990951) (q := 2003) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2029072 with h | h
  · exact window_general (p := 2019071) (q := 2011) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2033080 with h | h
  · exact window_general (p := 2015063) (q := 2011) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2037086 with h | h
  · exact window_general (p := 2011057) (q := 2011) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2041106 with h | h
  · exact window_general (p := 2031217) (q := 2017) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2045114 with h | h
  · exact window_general (p := 2027209) (q := 2017) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2049140 with h | h
  · exact window_general (p := 2023183) (q := 2017) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2053160 with h | h
  · exact window_general (p := 1994983) (q := 2011) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2057182 with h | h
  · exact window_general (p := 2015141) (q := 2017) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2061212 with h | h
  · exact window_general (p := 2011111) (q := 2017) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2065262 with h | h
  · exact window_general (p := 2055637) (q := 2029) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2069312 with h | h
  · exact window_general (p := 2051587) (q := 2029) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2073358 with h | h
  · exact window_general (p := 2047541) (q := 2029) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2077412 with h | h
  · exact window_general (p := 2043487) (q := 2029) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2081462 with h | h
  · exact window_general (p := 2039437) (q := 2029) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2085540 with h | h
  · exact window_general (p := 2076059) (q := 2039) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2089608 with h | h
  · exact window_general (p := 2071991) (q := 2039) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2093670 with h | h
  · exact window_general (p := 2067929) (q := 2039) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2097742 with h | h
  · exact window_general (p := 2063857) (q := 2039) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2101806 with h | h
  · exact window_general (p := 2059793) (q := 2039) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2105880 with h | h
  · exact window_general (p := 2055719) (q := 2039) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2109958 with h | h
  · exact window_general (p := 2051641) (q := 2039) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  exact window_general (p := 2104853) (q := 2053) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)

theorem cov_2114063_2323642 (n : ℕ) (hlo : 2114063 ≤ n) (hhi : n ≤ 2323642) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  rcases le_or_gt n 2118134 with h | h
  · exact window_general (p := 2100781) (q := 2053) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2122234 with h | h
  · exact window_general (p := 2096681) (q := 2053) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2126326 with h | h
  · exact window_general (p := 2092589) (q := 2053) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2130428 with h | h
  · exact window_general (p := 2088487) (q := 2053) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2134542 with h | h
  · exact window_general (p := 2125553) (q := 2063) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2138662 with h | h
  · exact window_general (p := 2121433) (q := 2063) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2142778 with h | h
  · exact window_general (p := 2117317) (q := 2063) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2146912 with h | h
  · exact window_general (p := 2137987) (q := 2069) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2151036 with h | h
  · exact window_general (p := 2109059) (q := 2063) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2155158 with h | h
  · exact window_general (p := 2129741) (q := 2069) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2159296 with h | h
  · exact window_general (p := 2125603) (q := 2069) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2163420 with h | h
  · exact window_general (p := 2121479) (q := 2069) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2167548 with h | h
  · exact window_general (p := 2117351) (q := 2069) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2171710 with h | h
  · exact window_general (p := 2163013) (q := 2081) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2175872 with h | h
  · exact window_general (p := 2167183) (q := 2083) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2180014 with h | h
  · exact window_general (p := 2163041) (q := 2083) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2184184 with h | h
  · exact window_general (p := 2175559) (q := 2087) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2188358 with h | h
  · exact window_general (p := 2179741) (q := 2089) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2192522 with h | h
  · exact window_general (p := 2175577) (q := 2089) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2196684 with h | h
  · exact window_general (p := 2163059) (q := 2087) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2200862 with h | h
  · exact window_general (p := 2167237) (q := 2089) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2205040 with h | h
  · exact window_general (p := 2163059) (q := 2089) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2209236 with h | h
  · exact window_general (p := 2200763) (q := 2099) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2213416 with h | h
  · exact window_general (p := 2196583) (q := 2099) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2217612 with h | h
  · exact window_general (p := 2192387) (q := 2099) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2221786 with h | h
  · exact window_general (p := 2188213) (q := 2099) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2225952 with h | h
  · exact window_general (p := 2184047) (q := 2099) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2230132 with h | h
  · exact window_general (p := 2179867) (q := 2099) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2234346 with h | h
  · exact window_general (p := 2226197) (q := 2111) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2238562 with h | h
  · exact window_general (p := 2230433) (q := 2113) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2242774 with h | h
  · exact window_general (p := 2226221) (q := 2113) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2246998 with h | h
  · exact window_general (p := 2221997) (q := 2113) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2251222 with h | h
  · exact window_general (p := 2217773) (q := 2113) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2255444 with h | h
  · exact window_general (p := 2213551) (q := 2113) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2259668 with h | h
  · exact window_general (p := 2209327) (q := 2113) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2263888 with h | h
  · exact window_general (p := 2205107) (q := 2113) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2268106 with h | h
  · exact window_general (p := 2200889) (q := 2113) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2272360 with h | h
  · exact window_general (p := 2264539) (q := 2129) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2276594 with h | h
  · exact window_general (p := 2268829) (q := 2131) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2280856 with h | h
  · exact window_general (p := 2264567) (q := 2131) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2285114 with h | h
  · exact window_general (p := 2260309) (q := 2131) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2289382 with h | h
  · exact window_general (p := 2281661) (q := 2137) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2293654 with h | h
  · exact window_general (p := 2277389) (q := 2137) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2297932 with h | h
  · exact window_general (p := 2290231) (q := 2141) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2302216 with h | h
  · exact window_general (p := 2294519) (q := 2143) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2306492 with h | h
  · exact window_general (p := 2290243) (q := 2143) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2310778 with h | h
  · exact window_general (p := 2285957) (q := 2143) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2315062 with h | h
  · exact window_general (p := 2281673) (q := 2143) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2319346 with h | h
  · exact window_general (p := 2277389) (q := 2143) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  exact window_general (p := 2316073) (q := 2153) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)

theorem cov_2323643_2542876 (n : ℕ) (hlo : 2323643 ≤ n) (hhi : n ≤ 2542876) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  rcases le_or_gt n 2327946 with h | h
  · exact window_general (p := 2311769) (q := 2153) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2332248 with h | h
  · exact window_general (p := 2307467) (q := 2153) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2336542 with h | h
  · exact window_general (p := 2303173) (q := 2153) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2340862 with h | h
  · exact window_general (p := 2333381) (q := 2161) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2345170 with h | h
  · exact window_general (p := 2329073) (q := 2161) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2349464 with h | h
  · exact window_general (p := 2324779) (q := 2161) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2353772 with h | h
  · exact window_general (p := 2320471) (q := 2161) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2358092 with h | h
  · exact window_general (p := 2316151) (q := 2161) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2362400 with h | h
  · exact window_general (p := 2311843) (q := 2161) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2366720 with h | h
  · exact window_general (p := 2307523) (q := 2161) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2371024 with h | h
  · exact window_general (p := 2303219) (q := 2161) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2375322 with h | h
  · exact window_general (p := 2264393) (q := 2153) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2379668 with h | h
  · exact window_general (p := 2372731) (q := 2179) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2384018 with h | h
  · exact window_general (p := 2368381) (q := 2179) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2388350 with h | h
  · exact window_general (p := 2364049) (q := 2179) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2392682 with h | h
  · exact window_general (p := 2359717) (q := 2179) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2397040 with h | h
  · exact window_general (p := 2355359) (q := 2179) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2401370 with h | h
  · exact window_general (p := 2351029) (q := 2179) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2405722 with h | h
  · exact window_general (p := 2346677) (q := 2179) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2410042 with h | h
  · exact window_general (p := 2342357) (q := 2179) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2414396 with h | h
  · exact window_general (p := 2338003) (q := 2179) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2418752 with h | h
  · exact window_general (p := 2333647) (q := 2179) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2423108 with h | h
  · exact window_general (p := 2329291) (q := 2179) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2427458 with h | h
  · exact window_general (p := 2324941) (q := 2179) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2431864 with h | h
  · exact window_general (p := 2425751) (q := 2203) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2436268 with h | h
  · exact window_general (p := 2421347) (q := 2203) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2440680 with h | h
  · exact window_general (p := 2434583) (q := 2207) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2445090 with h | h
  · exact window_general (p := 2430173) (q := 2207) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2449494 with h | h
  · exact window_general (p := 2425769) (q := 2207) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2453898 with h | h
  · exact window_general (p := 2447897) (q := 2213) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2458300 with h | h
  · exact window_general (p := 2416963) (q := 2207) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2462724 with h | h
  · exact window_general (p := 2439071) (q := 2213) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2467138 with h | h
  · exact window_general (p := 2434657) (q := 2213) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2471576 with h | h
  · exact window_general (p := 2465707) (q := 2221) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2476002 with h | h
  · exact window_general (p := 2425793) (q := 2213) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2480434 with h | h
  · exact window_general (p := 2456849) (q := 2221) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2484874 with h | h
  · exact window_general (p := 2452409) (q := 2221) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2489312 with h | h
  · exact window_general (p := 2447971) (q := 2221) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2493752 with h | h
  · exact window_general (p := 2443531) (q := 2221) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2498192 with h | h
  · exact window_general (p := 2439091) (q := 2221) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2502626 with h | h
  · exact window_general (p := 2434657) (q := 2221) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2507080 with h | h
  · exact window_general (p := 2501563) (q := 2237) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2511530 with h | h
  · exact window_general (p := 2506069) (q := 2239) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2516008 with h | h
  · exact window_general (p := 2501591) (q := 2239) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2520468 with h | h
  · exact window_general (p := 2515067) (q := 2243) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2524954 with h | h
  · exact window_general (p := 2510581) (q := 2243) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2529436 with h | h
  · exact window_general (p := 2506099) (q := 2243) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2533912 with h | h
  · exact window_general (p := 2501623) (q := 2243) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2538376 with h | h
  · exact window_general (p := 2533127) (q := 2251) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  exact window_general (p := 2528627) (q := 2251) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)

theorem cov_2542877_2772142 (n : ℕ) (hlo : 2542877 ≤ n) (hhi : n ≤ 2772142) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  rcases le_or_gt n 2547376 with h | h
  · exact window_general (p := 2524127) (q := 2251) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2551864 with h | h
  · exact window_general (p := 2519639) (q := 2251) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2556356 with h | h
  · exact window_general (p := 2515147) (q := 2251) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2560850 with h | h
  · exact window_general (p := 2510653) (q := 2251) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2565336 with h | h
  · exact window_general (p := 2470199) (q := 2243) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2569826 with h | h
  · exact window_general (p := 2501677) (q := 2251) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2574346 with h | h
  · exact window_general (p := 2569477) (q := 2267) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2578870 with h | h
  · exact window_general (p := 2574029) (q := 2269) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2583386 with h | h
  · exact window_general (p := 2569513) (q := 2269) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2587932 with h | h
  · exact window_general (p := 2583143) (q := 2273) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2592472 with h | h
  · exact window_general (p := 2578603) (q := 2273) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2597016 with h | h
  · exact window_general (p := 2574059) (q := 2273) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2601562 with h | h
  · exact window_general (p := 2569513) (q := 2273) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2606110 with h | h
  · exact window_general (p := 2601413) (q := 2281) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2610652 with h | h
  · exact window_general (p := 2596871) (q := 2281) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2615212 with h | h
  · exact window_general (p := 2592311) (q := 2281) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2619766 with h | h
  · exact window_general (p := 2615177) (q := 2287) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2624336 with h | h
  · exact window_general (p := 2610607) (q := 2287) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2628904 with h | h
  · exact window_general (p := 2606039) (q := 2287) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2633464 with h | h
  · exact window_general (p := 2601479) (q := 2287) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2638048 with h | h
  · exact window_general (p := 2624387) (q := 2293) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2642626 with h | h
  · exact window_general (p := 2619809) (q := 2293) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2647210 with h | h
  · exact window_general (p := 2633593) (q := 2297) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2651802 with h | h
  · exact window_general (p := 2629001) (q := 2297) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2656392 with h | h
  · exact window_general (p := 2624411) (q := 2297) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2660986 with h | h
  · exact window_general (p := 2619817) (q := 2297) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2665576 with h | h
  · exact window_general (p := 2615227) (q := 2297) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2670154 with h | h
  · exact window_general (p := 2610649) (q := 2297) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2674768 with h | h
  · exact window_general (p := 2661331) (q := 2309) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2679376 with h | h
  · exact window_general (p := 2665967) (q := 2311) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2683972 with h | h
  · exact window_general (p := 2661371) (q := 2311) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2688586 with h | h
  · exact window_general (p := 2656757) (q := 2311) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2693194 with h | h
  · exact window_general (p := 2652149) (q := 2311) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2697812 with h | h
  · exact window_general (p := 2647531) (q := 2311) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2702414 with h | h
  · exact window_general (p := 2642929) (q := 2311) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2707024 with h | h
  · exact window_general (p := 2638319) (q := 2311) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2711632 with h | h
  · exact window_general (p := 2633711) (q := 2311) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2716252 with h | h
  · exact window_general (p := 2629091) (q := 2311) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2720860 with h | h
  · exact window_general (p := 2624483) (q := 2311) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2725472 with h | h
  · exact window_general (p := 2619871) (q := 2311) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2730132 with h | h
  · exact window_general (p := 2717423) (q := 2333) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2734788 with h | h
  · exact window_general (p := 2712767) (q := 2333) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2739406 with h | h
  · exact window_general (p := 2708149) (q := 2333) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2744082 with h | h
  · exact window_general (p := 2731517) (q := 2339) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2748760 with h | h
  · exact window_general (p := 2736203) (q := 2341) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2753422 with h | h
  · exact window_general (p := 2731541) (q := 2341) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2758090 with h | h
  · exact window_general (p := 2726873) (q := 2341) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2762764 with h | h
  · exact window_general (p := 2750339) (q := 2347) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2767442 with h | h
  · exact window_general (p := 2745661) (q := 2347) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  exact window_general (p := 2759761) (q := 2351) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)

theorem cov_2772143_3011482 (n : ℕ) (hlo : 2772143 ≤ n) (hhi : n ≤ 3011482) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  rcases le_or_gt n 2776830 with h | h
  · exact window_general (p := 2755073) (q := 2351) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2781516 with h | h
  · exact window_general (p := 2750387) (q := 2351) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2786214 with h | h
  · exact window_general (p := 2773949) (q := 2357) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2790922 with h | h
  · exact window_general (p := 2769241) (q := 2357) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2795626 with h | h
  · exact window_general (p := 2764537) (q := 2357) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2800314 with h | h
  · exact window_general (p := 2759849) (q := 2357) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2805022 with h | h
  · exact window_general (p := 2755141) (q := 2357) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2809732 with h | h
  · exact window_general (p := 2750431) (q := 2357) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2814444 with h | h
  · exact window_general (p := 2745719) (q := 2357) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2819186 with h | h
  · exact window_general (p := 2807197) (q := 2371) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2823904 with h | h
  · exact window_general (p := 2802479) (q := 2371) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2828626 with h | h
  · exact window_general (p := 2797757) (q := 2371) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2833370 with h | h
  · exact window_general (p := 2821513) (q := 2377) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2838116 with h | h
  · exact window_general (p := 2816767) (q := 2377) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2842872 with h | h
  · exact window_general (p := 2831051) (q := 2381) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2847614 with h | h
  · exact window_general (p := 2835841) (q := 2383) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2852366 with h | h
  · exact window_general (p := 2831089) (q := 2383) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2857132 with h | h
  · exact window_general (p := 2826323) (q := 2383) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2861908 with h | h
  · exact window_general (p := 2850191) (q := 2389) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2866682 with h | h
  · exact window_general (p := 2845417) (q := 2389) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2871442 with h | h
  · exact window_general (p := 2859793) (q := 2393) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2876226 with h | h
  · exact window_general (p := 2855009) (q := 2393) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2881012 with h | h
  · exact window_general (p := 2850223) (q := 2393) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2885788 with h | h
  · exact window_general (p := 2874211) (q := 2399) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2890570 with h | h
  · exact window_general (p := 2869429) (q := 2399) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2895366 with h | h
  · exact window_general (p := 2864633) (q := 2399) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2900152 with h | h
  · exact window_general (p := 2859847) (q := 2399) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2904948 with h | h
  · exact window_general (p := 2855051) (q := 2399) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2909742 with h | h
  · exact window_general (p := 2850257) (q := 2399) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2914564 with h | h
  · exact window_general (p := 2903179) (q := 2411) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2919384 with h | h
  · exact window_general (p := 2898359) (q := 2411) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2924200 with h | h
  · exact window_general (p := 2893543) (q := 2411) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2929020 with h | h
  · exact window_general (p := 2888723) (q := 2411) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2933836 with h | h
  · exact window_general (p := 2912887) (q := 2417) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2938660 with h | h
  · exact window_general (p := 2908063) (q := 2417) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2943504 with h | h
  · exact window_general (p := 2932271) (q := 2423) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2948316 with h | h
  · exact window_general (p := 2927459) (q := 2423) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2953162 with h | h
  · exact window_general (p := 2922613) (q := 2423) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2958006 with h | h
  · exact window_general (p := 2917769) (q := 2423) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2962846 with h | h
  · exact window_general (p := 2912929) (q := 2423) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2967670 with h | h
  · exact window_general (p := 2879053) (q := 2417) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2972502 with h | h
  · exact window_general (p := 2903273) (q := 2423) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2977364 with h | h
  · exact window_general (p := 2966479) (q := 2437) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2982230 with h | h
  · exact window_general (p := 2961613) (q := 2437) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2987106 with h | h
  · exact window_general (p := 2976257) (q := 2441) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2991964 with h | h
  · exact window_general (p := 2971399) (q := 2441) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 2996844 with h | h
  · exact window_general (p := 2966519) (q := 2441) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3001720 with h | h
  · exact window_general (p := 2990983) (q := 2447) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3006600 with h | h
  · exact window_general (p := 2986103) (q := 2447) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  exact window_general (p := 2981221) (q := 2447) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)

theorem cov_3011483_3260582 (n : ℕ) (hlo : 3011483 ≤ n) (hhi : n ≤ 3260582) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  rcases le_or_gt n 3016374 with h | h
  · exact window_general (p := 2976329) (q := 2447) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3021244 with h | h
  · exact window_general (p := 2971459) (q := 2447) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3026122 with h | h
  · exact window_general (p := 2966581) (q := 2447) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3031020 with h | h
  · exact window_general (p := 3020579) (q := 2459) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3035928 with h | h
  · exact window_general (p := 3015671) (q := 2459) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3040842 with h | h
  · exact window_general (p := 3010757) (q := 2459) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3045760 with h | h
  · exact window_general (p := 3005839) (q := 2459) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3050690 with h | h
  · exact window_general (p := 3040333) (q := 2467) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3055616 with h | h
  · exact window_general (p := 3035407) (q := 2467) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3060550 with h | h
  · exact window_general (p := 3030473) (q := 2467) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3065488 with h | h
  · exact window_general (p := 3055187) (q := 2473) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3070424 with h | h
  · exact window_general (p := 3050251) (q := 2473) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3075352 with h | h
  · exact window_general (p := 3065131) (q := 2477) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3080304 with h | h
  · exact window_general (p := 3060179) (q := 2477) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3085254 with h | h
  · exact window_general (p := 3055229) (q := 2477) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3090180 with h | h
  · exact window_general (p := 3050303) (q := 2477) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3095116 with h | h
  · exact window_general (p := 3025559) (q := 2473) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3100058 with h | h
  · exact window_general (p := 3020617) (q := 2473) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3105006 with h | h
  · exact window_general (p := 3035477) (q := 2477) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3109960 with h | h
  · exact window_general (p := 3030523) (q := 2477) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3114912 with h | h
  · exact window_general (p := 3025571) (q := 2477) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3119866 with h | h
  · exact window_general (p := 3020617) (q := 2477) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3124812 with h | h
  · exact window_general (p := 3015671) (q := 2477) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3129754 with h | h
  · exact window_general (p := 3010729) (q := 2477) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3134696 with h | h
  · exact window_general (p := 2985979) (q := 2473) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3139688 with h | h
  · exact window_general (p := 3130327) (q := 2503) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3144692 with h | h
  · exact window_general (p := 3125323) (q := 2503) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3149698 with h | h
  · exact window_general (p := 3120317) (q := 2503) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3154696 with h | h
  · exact window_general (p := 3115319) (q := 2503) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3159694 with h | h
  · exact window_general (p := 3110321) (q := 2503) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3164698 with h | h
  · exact window_general (p := 3105317) (q := 2503) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3169702 with h | h
  · exact window_general (p := 3100313) (q := 2503) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3174704 with h | h
  · exact window_general (p := 3095311) (q := 2503) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3179702 with h | h
  · exact window_general (p := 3090313) (q := 2503) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3184732 with h | h
  · exact window_general (p := 3175751) (q := 2521) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3189760 with h | h
  · exact window_general (p := 3170723) (q := 2521) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3194776 with h | h
  · exact window_general (p := 3165707) (q := 2521) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3199796 with h | h
  · exact window_general (p := 3160687) (q := 2521) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3204832 with h | h
  · exact window_general (p := 3155651) (q := 2521) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3209892 with h | h
  · exact window_general (p := 3201131) (q := 2531) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3214936 with h | h
  · exact window_general (p := 3196087) (q := 2531) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3219984 with h | h
  · exact window_general (p := 3191039) (q := 2531) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3225042 with h | h
  · exact window_general (p := 3185981) (q := 2531) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3230102 with h | h
  · exact window_general (p := 3221497) (q := 2539) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3235168 with h | h
  · exact window_general (p := 3216431) (q := 2539) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3240246 with h | h
  · exact window_general (p := 3231689) (q := 2543) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3245332 with h | h
  · exact window_general (p := 3226603) (q := 2543) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3250396 with h | h
  · exact window_general (p := 3221539) (q := 2543) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3255492 with h | h
  · exact window_general (p := 3247007) (q := 2549) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  exact window_general (p := 3252121) (q := 2551) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)

theorem cov_3260583_3519670 (n : ℕ) (hlo : 3260583 ≤ n) (hhi : n ≤ 3519670) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  rcases le_or_gt n 3265664 with h | h
  · exact window_general (p := 3247039) (q := 2551) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3270766 with h | h
  · exact window_general (p := 3241937) (q := 2551) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3275866 with h | h
  · exact window_general (p := 3267497) (q := 2557) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3280976 with h | h
  · exact window_general (p := 3262387) (q := 2557) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3286072 with h | h
  · exact window_general (p := 3257291) (q := 2557) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3291172 with h | h
  · exact window_general (p := 3252191) (q := 2557) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3296276 with h | h
  · exact window_general (p := 3247087) (q := 2557) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3301382 with h | h
  · exact window_general (p := 3241981) (q := 2557) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3306490 with h | h
  · exact window_general (p := 3236873) (q := 2557) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3311590 with h | h
  · exact window_general (p := 3231773) (q := 2557) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3316694 with h | h
  · exact window_general (p := 3226669) (q := 2557) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3321806 with h | h
  · exact window_general (p := 3221557) (q := 2557) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3326914 with h | h
  · exact window_general (p := 3216449) (q := 2557) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3332070 with h | h
  · exact window_general (p := 3324329) (q := 2579) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3337228 with h | h
  · exact window_general (p := 3319171) (q := 2579) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3342372 with h | h
  · exact window_general (p := 3314027) (q := 2579) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3347518 with h | h
  · exact window_general (p := 3308881) (q := 2579) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3352668 with h | h
  · exact window_general (p := 3303731) (q := 2579) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3357822 with h | h
  · exact window_general (p := 3298577) (q := 2579) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3363004 with h | h
  · exact window_general (p := 3355459) (q := 2591) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3368186 with h | h
  · exact window_general (p := 3360649) (q := 2593) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3373348 with h | h
  · exact window_general (p := 3355487) (q := 2593) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3378506 with h | h
  · exact window_general (p := 3350329) (q := 2593) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3383674 with h | h
  · exact window_general (p := 3345161) (q := 2593) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3388858 with h | h
  · exact window_general (p := 3339977) (q := 2593) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3394034 with h | h
  · exact window_general (p := 3334801) (q := 2593) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3399206 with h | h
  · exact window_general (p := 3329629) (q := 2593) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3404378 with h | h
  · exact window_general (p := 3324457) (q := 2593) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3409582 with h | h
  · exact window_general (p := 3402517) (q := 2609) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3414790 with h | h
  · exact window_general (p := 3397309) (q := 2609) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3420006 with h | h
  · exact window_general (p := 3392093) (q := 2609) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3425208 with h | h
  · exact window_general (p := 3386891) (q := 2609) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3430436 with h | h
  · exact window_general (p := 3423487) (q := 2617) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3435656 with h | h
  · exact window_general (p := 3418267) (q := 2617) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3440872 with h | h
  · exact window_general (p := 3413051) (q := 2617) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3446100 with h | h
  · exact window_general (p := 3428783) (q := 2621) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3451326 with h | h
  · exact window_general (p := 3423557) (q := 2621) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3456562 with h | h
  · exact window_general (p := 3418321) (q := 2621) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3461800 with h | h
  · exact window_general (p := 3413083) (q := 2621) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3467032 with h | h
  · exact window_general (p := 3407851) (q := 2621) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3472296 with h | h
  · exact window_general (p := 3465659) (q := 2633) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3477562 with h | h
  · exact window_general (p := 3460393) (q := 2633) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3482814 with h | h
  · exact window_general (p := 3455141) (q := 2633) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3488076 with h | h
  · exact window_general (p := 3449879) (q := 2633) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3493336 with h | h
  · exact window_general (p := 3444619) (q := 2633) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3498576 with h | h
  · exact window_general (p := 3439379) (q := 2633) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3503826 with h | h
  · exact window_general (p := 3434129) (q := 2633) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3509114 with h | h
  · exact window_general (p := 3502789) (q := 2647) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3514384 with h | h
  · exact window_general (p := 3497519) (q := 2647) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  exact window_general (p := 3492233) (q := 2647) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)

theorem cov_3519671_3789008 (n : ℕ) (hlo : 3519671 ≤ n) (hhi : n ≤ 3789008) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  rcases le_or_gt n 3524962 with h | h
  · exact window_general (p := 3486941) (q := 2647) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3530246 with h | h
  · exact window_general (p := 3481657) (q := 2647) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3535546 with h | h
  · exact window_general (p := 3529417) (q := 2657) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3540856 with h | h
  · exact window_general (p := 3534743) (q := 2659) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3546166 with h | h
  · exact window_general (p := 3529433) (q := 2659) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3551488 with h | h
  · exact window_general (p := 3545407) (q := 2663) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3556794 with h | h
  · exact window_general (p := 3540101) (q := 2663) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3562108 with h | h
  · exact window_general (p := 3534787) (q := 2663) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3567410 with h | h
  · exact window_general (p := 3508189) (q := 2659) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3572752 with h | h
  · exact window_general (p := 3566831) (q := 2671) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3578084 with h | h
  · exact window_general (p := 3561499) (q := 2671) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3583414 with h | h
  · exact window_general (p := 3556169) (q := 2671) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3588760 with h | h
  · exact window_general (p := 3582923) (q := 2677) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3594112 with h | h
  · exact window_general (p := 3577571) (q := 2677) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3599440 with h | h
  · exact window_general (p := 3572243) (q := 2677) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3604786 with h | h
  · exact window_general (p := 3566897) (q := 2677) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3610142 with h | h
  · exact window_general (p := 3593713) (q := 2683) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3615496 with h | h
  · exact window_general (p := 3609847) (q := 2687) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3620870 with h | h
  · exact window_general (p := 3615229) (q := 2689) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3626236 with h | h
  · exact window_general (p := 3609863) (q := 2689) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3631602 with h | h
  · exact window_general (p := 3626033) (q := 2693) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3636978 with h | h
  · exact window_general (p := 3620657) (q := 2693) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3642336 with h | h
  · exact window_general (p := 3615299) (q := 2693) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3647730 with h | h
  · exact window_general (p := 3642269) (q := 2699) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3653122 with h | h
  · exact window_general (p := 3636877) (q := 2699) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3658512 with h | h
  · exact window_general (p := 3631487) (q := 2699) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3663900 with h | h
  · exact window_general (p := 3626099) (q := 2699) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3669286 with h | h
  · exact window_general (p := 3620713) (q := 2699) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3674680 with h | h
  · exact window_general (p := 3615319) (q := 2699) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3680092 with h | h
  · exact window_general (p := 3653171) (q := 2707) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3685504 with h | h
  · exact window_general (p := 3647759) (q := 2707) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3690910 with h | h
  · exact window_general (p := 3664033) (q := 2711) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3696326 with h | h
  · exact window_general (p := 3669469) (q := 2713) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3701752 with h | h
  · exact window_general (p := 3664043) (q := 2713) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3707186 with h | h
  · exact window_general (p := 3691213) (q := 2719) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3712616 with h | h
  · exact window_general (p := 3685783) (q := 2719) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3718036 with h | h
  · exact window_general (p := 3680363) (q := 2719) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3723472 with h | h
  · exact window_general (p := 3674927) (q := 2719) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3728900 with h | h
  · exact window_general (p := 3669499) (q := 2719) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3734350 with h | h
  · exact window_general (p := 3718549) (q := 2729) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3739792 with h | h
  · exact window_general (p := 3724031) (q := 2731) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3745250 with h | h
  · exact window_general (p := 3718573) (q := 2731) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3750702 with h | h
  · exact window_general (p := 3702197) (q := 2729) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3756160 with h | h
  · exact window_general (p := 3707663) (q := 2731) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3761612 with h | h
  · exact window_general (p := 3702211) (q := 2731) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3767086 with h | h
  · exact window_general (p := 3751477) (q := 2741) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3772566 with h | h
  · exact window_general (p := 3745997) (q := 2741) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3778044 with h | h
  · exact window_general (p := 3740519) (q := 2741) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3783516 with h | h
  · exact window_general (p := 3735047) (q := 2741) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  exact window_general (p := 3773491) (q := 2749) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)

theorem cov_3789009_4067928 (n : ℕ) (hlo : 3789009 ≤ n) (hhi : n ≤ 4067928) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  rcases le_or_gt n 3794490 with h | h
  · exact window_general (p := 3724073) (q := 2741) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3799996 with h | h
  · exact window_general (p := 3784519) (q := 2753) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3805494 with h | h
  · exact window_general (p := 3779021) (q := 2753) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3810988 with h | h
  · exact window_general (p := 3773527) (q := 2753) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3816472 with h | h
  · exact window_general (p := 3746027) (q := 2749) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3821962 with h | h
  · exact window_general (p := 3740537) (q := 2749) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3827452 with h | h
  · exact window_general (p := 3757063) (q := 2753) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3832948 with h | h
  · exact window_general (p := 3751567) (q := 2753) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3838474 with h | h
  · exact window_general (p := 3823349) (q := 2767) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3844006 with h | h
  · exact window_general (p := 3817817) (q := 2767) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3849514 with h | h
  · exact window_general (p := 3812309) (q := 2767) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3855016 with h | h
  · exact window_general (p := 3729499) (q := 2753) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3860540 with h | h
  · exact window_general (p := 3801283) (q := 2767) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3866070 with h | h
  · exact window_general (p := 3851213) (q := 2777) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3871620 with h | h
  · exact window_general (p := 3845663) (q := 2777) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3877156 with h | h
  · exact window_general (p := 3840127) (q := 2777) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3882706 with h | h
  · exact window_general (p := 3834577) (q := 2777) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3888226 with h | h
  · exact window_general (p := 3773597) (q := 2767) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3893772 with h | h
  · exact window_general (p := 3823511) (q := 2777) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3899332 with h | h
  · exact window_general (p := 3884767) (q := 2789) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3904912 with h | h
  · exact window_general (p := 3890351) (q := 2791) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3910470 with h | h
  · exact window_general (p := 3873629) (q := 2789) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3916042 with h | h
  · exact window_general (p := 3879221) (q := 2791) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3921616 with h | h
  · exact window_general (p := 3907187) (q := 2797) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3927194 with h | h
  · exact window_general (p := 3901609) (q := 2797) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3932790 with h | h
  · exact window_general (p := 3918413) (q := 2801) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3938392 with h | h
  · exact window_general (p := 3924023) (q := 2803) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3943972 with h | h
  · exact window_general (p := 3918443) (q := 2803) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3949556 with h | h
  · exact window_general (p := 3912859) (q := 2803) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3955156 with h | h
  · exact window_general (p := 3896047) (q := 2801) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3960758 with h | h
  · exact window_general (p := 3901657) (q := 2803) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3966356 with h | h
  · exact window_general (p := 3896059) (q := 2803) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3971946 with h | h
  · exact window_general (p := 3879257) (q := 2801) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3977544 with h | h
  · exact window_general (p := 3873659) (q := 2801) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3983178 with h | h
  · exact window_general (p := 3969221) (q := 2819) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3988812 with h | h
  · exact window_general (p := 3963587) (q := 2819) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 3994446 with h | h
  · exact window_general (p := 3957953) (q := 2819) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4000078 with h | h
  · exact window_general (p := 3952321) (q := 2819) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4005682 with h | h
  · exact window_general (p := 3856733) (q := 2803) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4011318 with h | h
  · exact window_general (p := 3941081) (q := 2819) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4016956 with h | h
  · exact window_general (p := 3935443) (q := 2819) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4022608 with h | h
  · exact window_general (p := 4008947) (q := 2833) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4028264 with h | h
  · exact window_general (p := 4003291) (q := 2833) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4033936 with h | h
  · exact window_general (p := 4020307) (q := 2837) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4039590 with h | h
  · exact window_general (p := 4014653) (q := 2837) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4045246 with h | h
  · exact window_general (p := 4008997) (q := 2837) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4050922 with h | h
  · exact window_general (p := 4037413) (q := 2843) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4056594 with h | h
  · exact window_general (p := 3997649) (q := 2837) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4062262 with h | h
  · exact window_general (p := 4026073) (q := 2843) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  exact window_general (p := 4020407) (q := 2843) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)

theorem cov_4067929_4357062 (n : ℕ) (hlo : 4067929 ≤ n) (hhi : n ≤ 4357062) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  rcases le_or_gt n 4073614 with h | h
  · exact window_general (p := 4060289) (q := 2851) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4079312 with h | h
  · exact window_general (p := 4054591) (q := 2851) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4085002 with h | h
  · exact window_general (p := 4048901) (q := 2851) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4090690 with h | h
  · exact window_general (p := 4077473) (q := 2857) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4096402 with h | h
  · exact window_general (p := 4071761) (q := 2857) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4102120 with h | h
  · exact window_general (p := 4088923) (q := 2861) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4107840 with h | h
  · exact window_general (p := 4083203) (q := 2861) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4113562 with h | h
  · exact window_general (p := 4077481) (q := 2861) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4119282 with h | h
  · exact window_general (p := 4071761) (q := 2861) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4125004 with h | h
  · exact window_general (p := 4066039) (q := 2861) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4130706 with h | h
  · exact window_general (p := 4060337) (q := 2861) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4136422 with h | h
  · exact window_general (p := 4054621) (q := 2861) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4142142 with h | h
  · exact window_general (p := 4048901) (q := 2861) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4147854 with h | h
  · exact window_general (p := 4043189) (q := 2861) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4153588 with h | h
  · exact window_general (p := 4140811) (q := 2879) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4159342 with h | h
  · exact window_general (p := 4135057) (q := 2879) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4165090 with h | h
  · exact window_general (p := 4129309) (q := 2879) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4170816 with h | h
  · exact window_general (p := 4123583) (q := 2879) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4176590 with h | h
  · exact window_general (p := 4163953) (q := 2887) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4182362 with h | h
  · exact window_general (p := 4158181) (q := 2887) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4188134 with h | h
  · exact window_general (p := 4152409) (q := 2887) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4193882 with h | h
  · exact window_general (p := 4146661) (q := 2887) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4199650 with h | h
  · exact window_general (p := 4140893) (q := 2887) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4205440 with h | h
  · exact window_general (p := 4192963) (q := 2897) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4211226 with h | h
  · exact window_general (p := 4187177) (q := 2897) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4217020 with h | h
  · exact window_general (p := 4181383) (q := 2897) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4222824 with h | h
  · exact window_general (p := 4210391) (q := 2903) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4228614 with h | h
  · exact window_general (p := 4204601) (q := 2903) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4234408 with h | h
  · exact window_general (p := 4198807) (q := 2903) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4240222 with h | h
  · exact window_general (p := 4227877) (q := 2909) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4246038 with h | h
  · exact window_general (p := 4222061) (q := 2909) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4251832 with h | h
  · exact window_general (p := 4181383) (q := 2903) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4257630 with h | h
  · exact window_general (p := 4210469) (q := 2909) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4263464 with h | h
  · exact window_general (p := 4251259) (q := 2917) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4269280 with h | h
  · exact window_general (p := 4245443) (q := 2917) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4275112 with h | h
  · exact window_general (p := 4239611) (q := 2917) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4280936 with h | h
  · exact window_general (p := 4233787) (q := 2917) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4286764 with h | h
  · exact window_general (p := 4227959) (q := 2917) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4292602 with h | h
  · exact window_general (p := 4280581) (q := 2927) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4298452 with h | h
  · exact window_general (p := 4274731) (q := 2927) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4304302 with h | h
  · exact window_general (p := 4268881) (q := 2927) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4310146 with h | h
  · exact window_general (p := 4263037) (q := 2927) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4315990 with h | h
  · exact window_general (p := 4257193) (q := 2927) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4321836 with h | h
  · exact window_general (p := 4251347) (q := 2927) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4327708 with h | h
  · exact window_general (p := 4315891) (q := 2939) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4333578 with h | h
  · exact window_general (p := 4310021) (q := 2939) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4339456 with h | h
  · exact window_general (p := 4304143) (q := 2939) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4345320 with h | h
  · exact window_general (p := 4298279) (q := 2939) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4351188 with h | h
  · exact window_general (p := 4292411) (q := 2939) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  exact window_general (p := 4286537) (q := 2939) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)

theorem cov_4357063_4655998 (n : ℕ) (hlo : 4357063 ≤ n) (hhi : n ≤ 4655998) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  rcases le_or_gt n 4362940 with h | h
  · exact window_general (p := 4280659) (q := 2939) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4368844 with h | h
  · exact window_general (p := 4357271) (q := 2953) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4374718 with h | h
  · exact window_general (p := 4351397) (q := 2953) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4380630 with h | h
  · exact window_general (p := 4369133) (q := 2957) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4386540 with h | h
  · exact window_general (p := 4363223) (q := 2957) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4392418 with h | h
  · exact window_general (p := 4333697) (q := 2953) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4398324 with h | h
  · exact window_general (p := 4386971) (q := 2963) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4404246 with h | h
  · exact window_general (p := 4381049) (q := 2963) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4410168 with h | h
  · exact window_general (p := 4375127) (q := 2963) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4416102 with h | h
  · exact window_general (p := 4404797) (q := 2969) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4422040 with h | h
  · exact window_general (p := 4410743) (q := 2971) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4427974 with h | h
  · exact window_general (p := 4404809) (q := 2971) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4433896 with h | h
  · exact window_general (p := 4398887) (q := 2971) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4439832 with h | h
  · exact window_general (p := 4381067) (q := 2969) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4445770 with h | h
  · exact window_general (p := 4387013) (q := 2971) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4451710 with h | h
  · exact window_general (p := 4381073) (q := 2971) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4457642 with h | h
  · exact window_general (p := 4375141) (q := 2971) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4463584 with h | h
  · exact window_general (p := 4369199) (q := 2971) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4469524 with h | h
  · exact window_general (p := 4363259) (q := 2971) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4475436 with h | h
  · exact window_general (p := 4345463) (q := 2969) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4481374 with h | h
  · exact window_general (p := 4351409) (q := 2971) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4487314 with h | h
  · exact window_general (p := 4345469) (q := 2971) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4493254 with h | h
  · exact window_general (p := 4339529) (q := 2971) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4499186 with h | h
  · exact window_general (p := 4333597) (q := 2971) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4505160 with h | h
  · exact window_general (p := 4494839) (q := 2999) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4511152 with h | h
  · exact window_general (p := 4500851) (q := 3001) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4517146 with h | h
  · exact window_general (p := 4494857) (q := 3001) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4523136 with h | h
  · exact window_general (p := 4476863) (q := 2999) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4529132 with h | h
  · exact window_general (p := 4482871) (q := 3001) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4535120 with h | h
  · exact window_general (p := 4476883) (q := 3001) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4541140 with h | h
  · exact window_general (p := 4531003) (q := 3011) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4547152 with h | h
  · exact window_general (p := 4524991) (q := 3011) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4553154 with h | h
  · exact window_general (p := 4518989) (q := 3011) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4559172 with h | h
  · exact window_general (p := 4512971) (q := 3011) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4565192 with h | h
  · exact window_general (p := 4555207) (q := 3019) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4571230 with h | h
  · exact window_general (p := 4549169) (q := 3019) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4577262 with h | h
  · exact window_general (p := 4567313) (q := 3023) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4583308 with h | h
  · exact window_general (p := 4561267) (q := 3023) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4589338 with h | h
  · exact window_general (p := 4555237) (q := 3023) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4595376 with h | h
  · exact window_general (p := 4549199) (q := 3023) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4601410 with h | h
  · exact window_general (p := 4518989) (q := 3019) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4607452 with h | h
  · exact window_general (p := 4537123) (q := 3023) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4613494 with h | h
  · exact window_general (p := 4531081) (q := 3023) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4619546 with h | h
  · exact window_general (p := 4609897) (q := 3037) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4625612 with h | h
  · exact window_general (p := 4603831) (q := 3037) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4631682 with h | h
  · exact window_general (p := 4622081) (q := 3041) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4637764 with h | h
  · exact window_general (p := 4615999) (q := 3041) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4643842 with h | h
  · exact window_general (p := 4609921) (q := 3041) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4649920 with h | h
  · exact window_general (p := 4603843) (q := 3041) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  exact window_general (p := 4646501) (q := 3049) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)

theorem cov_4655999_4964832 (n : ℕ) (hlo : 4655999 ≤ n) (hhi : n ≤ 4964832) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  rcases le_or_gt n 4662082 with h | h
  · exact window_general (p := 4640417) (q := 3049) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4668178 with h | h
  · exact window_general (p := 4634321) (q := 3049) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4674272 with h | h
  · exact window_general (p := 4628227) (q := 3049) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4680356 with h | h
  · exact window_general (p := 4622143) (q := 3049) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4686436 with h | h
  · exact window_general (p := 4616063) (q := 3049) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4692550 with h | h
  · exact window_general (p := 4683293) (q := 3061) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4698652 with h | h
  · exact window_general (p := 4677191) (q := 3061) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4704772 with h | h
  · exact window_general (p := 4671071) (q := 3061) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4710892 with h | h
  · exact window_general (p := 4701731) (q := 3067) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4717000 with h | h
  · exact window_general (p := 4695623) (q := 3067) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4723120 with h | h
  · exact window_general (p := 4652723) (q := 3061) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4729246 with h | h
  · exact window_general (p := 4683377) (q := 3067) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4735376 with h | h
  · exact window_general (p := 4677247) (q := 3067) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4741510 with h | h
  · exact window_general (p := 4671113) (q := 3067) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4747630 with h | h
  · exact window_general (p := 4664993) (q := 3067) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4753780 with h | h
  · exact window_general (p := 4732619) (q := 3079) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4759944 with h | h
  · exact window_general (p := 4751111) (q := 3083) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4766092 with h | h
  · exact window_general (p := 4744963) (q := 3083) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4772248 with h | h
  · exact window_general (p := 4738807) (q := 3083) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4778406 with h | h
  · exact window_general (p := 4769693) (q := 3089) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4784572 with h | h
  · exact window_general (p := 4763527) (q := 3089) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4790748 with h | h
  · exact window_general (p := 4757351) (q := 3089) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4796892 with h | h
  · exact window_general (p := 4714163) (q := 3083) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4803070 with h | h
  · exact window_general (p := 4745029) (q := 3089) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4809228 with h | h
  · exact window_general (p := 4738871) (q := 3089) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4815396 with h | h
  · exact window_general (p := 4732703) (q := 3089) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4821562 with h | h
  · exact window_general (p := 4726537) (q := 3089) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4827738 with h | h
  · exact window_general (p := 4720361) (q := 3089) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4833916 with h | h
  · exact window_general (p := 4714183) (q := 3089) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4840112 with h | h
  · exact window_general (p := 4831987) (q := 3109) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4846310 with h | h
  · exact window_general (p := 4825789) (q := 3109) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4852520 with h | h
  · exact window_general (p := 4819579) (q := 3109) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4858726 with h | h
  · exact window_general (p := 4813373) (q := 3109) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4864930 with h | h
  · exact window_general (p := 4807169) (q := 3109) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4871166 with h | h
  · exact window_general (p := 4863233) (q := 3119) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4877404 with h | h
  · exact window_general (p := 4869479) (q := 3121) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4883644 with h | h
  · exact window_general (p := 4863239) (q := 3121) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4889860 with h | h
  · exact window_general (p := 4857023) (q := 3121) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4896070 with h | h
  · exact window_general (p := 4776029) (q := 3109) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4902310 with h | h
  · exact window_general (p := 4844573) (q := 3121) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4908550 with h | h
  · exact window_general (p := 4838333) (q := 3121) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4914768 with h | h
  · exact window_general (p := 4819631) (q := 3119) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4921004 with h | h
  · exact window_general (p := 4825879) (q := 3121) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4927276 with h | h
  · exact window_general (p := 4919767) (q := 3137) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4933546 with h | h
  · exact window_general (p := 4913497) (q := 3137) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4939810 with h | h
  · exact window_general (p := 4907233) (q := 3137) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4946064 with h | h
  · exact window_general (p := 4900979) (q := 3137) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4952332 with h | h
  · exact window_general (p := 4894711) (q := 3137) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4958596 with h | h
  · exact window_general (p := 4888447) (q := 3137) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  exact window_general (p := 4882211) (q := 3137) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)

theorem cov_4964833_5283428 (n : ℕ) (hlo : 4964833 ≤ n) (hhi : n ≤ 5283428) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  rcases le_or_gt n 4971100 with h | h
  · exact window_general (p := 4875943) (q := 3137) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4977364 with h | h
  · exact window_general (p := 4869679) (q := 3137) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4983616 with h | h
  · exact window_general (p := 4863427) (q := 3137) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4989882 with h | h
  · exact window_general (p := 4857161) (q := 3137) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 4996156 with h | h
  · exact window_general (p := 4850887) (q := 3137) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5002426 with h | h
  · exact window_general (p := 4844617) (q := 3137) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5008738 with h | h
  · exact window_general (p := 5002157) (q := 3163) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5015032 with h | h
  · exact window_general (p := 4995863) (q := 3163) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5021350 with h | h
  · exact window_general (p := 5014873) (q := 3167) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5027686 with h | h
  · exact window_general (p := 5021213) (q := 3169) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5033996 with h | h
  · exact window_general (p := 5014903) (q := 3169) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5040332 with h | h
  · exact window_general (p := 5008567) (q := 3169) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5046670 with h | h
  · exact window_general (p := 5002229) (q := 3169) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5052988 with h | h
  · exact window_general (p := 4995911) (q := 3169) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5059318 with h | h
  · exact window_general (p := 4989581) (q := 3169) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5065636 with h | h
  · exact window_general (p := 4970587) (q := 3167) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5071972 with h | h
  · exact window_general (p := 5053151) (q := 3181) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5078306 with h | h
  · exact window_general (p := 5046817) (q := 3181) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5084656 with h | h
  · exact window_general (p := 5040467) (q := 3181) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5091014 with h | h
  · exact window_general (p := 5072329) (q := 3187) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5097382 with h | h
  · exact window_general (p := 5065961) (q := 3187) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5103732 with h | h
  · exact window_general (p := 5085131) (q := 3191) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5110110 with h | h
  · exact window_general (p := 5078753) (q := 3191) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5116492 with h | h
  · exact window_general (p := 5072371) (q := 3191) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5122866 with h | h
  · exact window_general (p := 5065997) (q := 3191) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5129244 with h | h
  · exact window_general (p := 5059619) (q := 3191) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5135614 with h | h
  · exact window_general (p := 5053249) (q := 3191) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5142012 with h | h
  · exact window_general (p := 5123603) (q := 3203) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5148418 with h | h
  · exact window_general (p := 5117197) (q := 3203) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5154814 with h | h
  · exact window_general (p := 5110801) (q := 3203) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5161222 with h | h
  · exact window_general (p := 5142877) (q := 3209) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5167636 with h | h
  · exact window_general (p := 5136463) (q := 3209) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5174032 with h | h
  · exact window_general (p := 5130067) (q := 3209) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5180428 with h | h
  · exact window_general (p := 5085187) (q := 3203) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5186846 with h | h
  · exact window_general (p := 5168677) (q := 3217) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5193252 with h | h
  · exact window_general (p := 5072363) (q := 3203) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5199684 with h | h
  · exact window_general (p := 5181599) (q := 3221) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5206114 with h | h
  · exact window_general (p := 5149409) (q := 3217) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5212540 with h | h
  · exact window_general (p := 5168743) (q := 3221) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5218980 with h | h
  · exact window_general (p := 5162303) (q := 3221) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5225432 with h | h
  · exact window_general (p := 5207467) (q := 3229) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5231876 with h | h
  · exact window_general (p := 5201023) (q := 3229) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5238316 with h | h
  · exact window_general (p := 5142967) (q := 3221) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5244752 with h | h
  · exact window_general (p := 5188147) (q := 3229) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5251202 with h | h
  · exact window_general (p := 5181697) (q := 3229) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5257648 with h | h
  · exact window_general (p := 5175251) (q := 3229) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5264096 with h | h
  · exact window_general (p := 5168803) (q := 3229) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5270528 with h | h
  · exact window_general (p := 5162371) (q := 3229) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5276970 with h | h
  · exact window_general (p := 5104313) (q := 3221) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  exact window_general (p := 5149471) (q := 3229) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)

theorem cov_5283429_5612166 (n : ℕ) (hlo : 5283429 ≤ n) (hhi : n ≤ 5612166) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  rcases le_or_gt n 5289886 with h | h
  · exact window_general (p := 5143013) (q := 3229) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5296386 with h | h
  · exact window_general (p := 5279117) (q := 3251) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5302868 with h | h
  · exact window_general (p := 5285647) (q := 3253) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5309366 with h | h
  · exact window_general (p := 5279149) (q := 3253) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5315872 with h | h
  · exact window_general (p := 5298691) (q := 3257) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5322370 with h | h
  · exact window_general (p := 5305229) (q := 3259) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5328880 with h | h
  · exact window_general (p := 5298719) (q := 3259) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5335388 with h | h
  · exact window_general (p := 5292211) (q := 3259) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5341886 with h | h
  · exact window_general (p := 5285713) (q := 3259) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5348396 with h | h
  · exact window_general (p := 5279203) (q := 3259) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5354892 with h | h
  · exact window_general (p := 5259671) (q := 3257) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5361430 with h | h
  · exact window_general (p := 5344553) (q := 3271) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5367970 with h | h
  · exact window_general (p := 5338013) (q := 3271) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5374504 with h | h
  · exact window_general (p := 5331479) (q := 3271) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5381030 with h | h
  · exact window_general (p := 5324953) (q := 3271) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5387552 with h | h
  · exact window_general (p := 5318431) (q := 3271) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5394080 with h | h
  · exact window_general (p := 5311903) (q := 3271) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5400622 with h | h
  · exact window_general (p := 5305361) (q := 3271) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5407160 with h | h
  · exact window_general (p := 5298823) (q := 3271) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5413700 with h | h
  · exact window_general (p := 5292283) (q := 3271) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5420242 with h | h
  · exact window_general (p := 5285741) (q := 3271) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5426780 with h | h
  · exact window_general (p := 5279203) (q := 3271) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5433316 with h | h
  · exact window_general (p := 5272667) (q := 3271) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5439856 with h | h
  · exact window_general (p := 5266127) (q := 3271) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5446390 with h | h
  · exact window_general (p := 5259593) (q := 3271) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5452986 with h | h
  · exact window_general (p := 5437013) (q := 3299) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5459564 with h | h
  · exact window_general (p := 5443639) (q := 3301) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5466166 with h | h
  · exact window_general (p := 5437037) (q := 3301) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5472760 with h | h
  · exact window_general (p := 5430443) (q := 3301) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5479364 with h | h
  · exact window_general (p := 5463499) (q := 3307) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5485966 with h | h
  · exact window_general (p := 5456897) (q := 3307) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5492564 with h | h
  · exact window_general (p := 5450299) (q := 3307) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5499178 with h | h
  · exact window_general (p := 5483417) (q := 3313) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5505796 with h | h
  · exact window_general (p := 5476799) (q := 3313) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5512418 with h | h
  · exact window_general (p := 5470177) (q := 3313) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5519050 with h | h
  · exact window_general (p := 5503349) (q := 3319) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5525686 with h | h
  · exact window_general (p := 5496713) (q := 3319) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5532328 with h | h
  · exact window_general (p := 5516647) (q := 3323) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5538966 with h | h
  · exact window_general (p := 5510009) (q := 3323) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5545612 with h | h
  · exact window_general (p := 5503363) (q := 3323) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5552260 with h | h
  · exact window_general (p := 5536639) (q := 3329) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5558898 with h | h
  · exact window_general (p := 5530001) (q := 3329) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5565554 with h | h
  · exact window_general (p := 5536669) (q := 3331) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5572196 with h | h
  · exact window_general (p := 5530027) (q := 3331) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5578850 with h | h
  · exact window_general (p := 5523373) (q := 3331) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5585500 with h | h
  · exact window_general (p := 5516723) (q := 3331) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5592140 with h | h
  · exact window_general (p := 5510083) (q := 3331) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5598826 with h | h
  · exact window_general (p := 5583509) (q := 3343) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5605496 with h | h
  · exact window_general (p := 5576839) (q := 3343) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  exact window_general (p := 5596937) (q := 3347) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)

theorem cov_5612167_5950784 (n : ℕ) (hlo : 5612167 ≤ n) (hhi : n ≤ 5950784) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  rcases le_or_gt n 5618850 with h | h
  · exact window_general (p := 5590253) (q := 3347) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5625534 with h | h
  · exact window_general (p := 5583569) (q := 3347) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5632222 with h | h
  · exact window_general (p := 5576881) (q := 3347) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5638906 with h | h
  · exact window_general (p := 5570197) (q := 3347) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5645590 with h | h
  · exact window_general (p := 5563513) (q := 3347) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5652300 with h | h
  · exact window_general (p := 5637299) (q := 3359) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5659022 with h | h
  · exact window_general (p := 5644021) (q := 3361) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5665744 with h | h
  · exact window_general (p := 5637299) (q := 3361) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5672452 with h | h
  · exact window_general (p := 5630591) (q := 3361) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5679166 with h | h
  · exact window_general (p := 5610433) (q := 3359) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5685880 with h | h
  · exact window_general (p := 5617163) (q := 3361) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5692600 with h | h
  · exact window_general (p := 5610443) (q := 3361) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5699342 with h | h
  · exact window_general (p := 5684533) (q := 3373) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5706074 with h | h
  · exact window_general (p := 5677801) (q := 3373) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5712790 with h | h
  · exact window_general (p := 5590253) (q := 3361) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5719516 with h | h
  · exact window_general (p := 5664359) (q := 3373) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5726252 with h | h
  · exact window_general (p := 5657623) (q := 3373) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5732994 with h | h
  · exact window_general (p := 5637389) (q := 3371) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5739718 with h | h
  · exact window_general (p := 5644157) (q := 3373) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5746448 with h | h
  · exact window_general (p := 5637427) (q := 3373) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5753196 with h | h
  · exact window_general (p := 5738903) (q := 3389) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5759974 with h | h
  · exact window_general (p := 5745689) (q := 3391) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5766736 with h | h
  · exact window_general (p := 5738927) (q := 3391) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5773516 with h | h
  · exact window_general (p := 5732147) (q := 3391) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5780270 with h | h
  · exact window_general (p := 5725393) (q := 3391) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5787040 with h | h
  · exact window_general (p := 5718623) (q := 3391) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5793812 with h | h
  · exact window_general (p := 5711851) (q := 3391) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5800594 with h | h
  · exact window_general (p := 5705069) (q := 3391) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5807374 with h | h
  · exact window_general (p := 5698289) (q := 3391) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5814184 with h | h
  · exact window_general (p := 5800279) (q := 3407) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5820996 with h | h
  · exact window_general (p := 5793467) (q := 3407) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5827806 with h | h
  · exact window_general (p := 5786657) (q := 3407) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5834626 with h | h
  · exact window_general (p := 5820769) (q := 3413) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5841414 with h | h
  · exact window_general (p := 5773049) (q := 3407) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5848236 with h | h
  · exact window_general (p := 5807159) (q := 3413) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5855052 with h | h
  · exact window_general (p := 5800343) (q := 3413) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5861878 with h | h
  · exact window_general (p := 5793517) (q := 3413) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5868688 with h | h
  · exact window_general (p := 5786707) (q := 3413) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5875494 with h | h
  · exact window_general (p := 5779901) (q := 3413) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5882292 with h | h
  · exact window_general (p := 5732171) (q := 3407) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5889108 with h | h
  · exact window_general (p := 5766287) (q := 3413) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5895922 with h | h
  · exact window_general (p := 5759473) (q := 3413) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5902778 with h | h
  · exact window_general (p := 5889577) (q := 3433) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5909638 with h | h
  · exact window_general (p := 5882717) (q := 3433) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5916494 with h | h
  · exact window_general (p := 5875861) (q := 3433) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5923354 with h | h
  · exact window_general (p := 5869001) (q := 3433) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5930218 with h | h
  · exact window_general (p := 5862137) (q := 3433) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5937076 with h | h
  · exact window_general (p := 5855279) (q := 3433) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5943922 with h | h
  · exact window_general (p := 5848433) (q := 3433) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  exact window_general (p := 5841571) (q := 3433) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)

theorem cov_5950785_6299554 (n : ℕ) (hlo : 5950785 ≤ n) (hhi : n ≤ 6299554) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  rcases le_or_gt n 5957680 with h | h
  · exact window_general (p := 5944819) (q := 3449) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5964568 with h | h
  · exact window_general (p := 5937931) (q := 3449) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5971456 with h | h
  · exact window_general (p := 5931043) (q := 3449) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5978340 with h | h
  · exact window_general (p := 5924159) (q := 3449) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5985254 with h | h
  · exact window_general (p := 5972509) (q := 3457) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5992146 with h | h
  · exact window_general (p := 5910353) (q := 3449) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 5999062 with h | h
  · exact window_general (p := 5986381) (q := 3461) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6005974 with h | h
  · exact window_general (p := 5993321) (q := 3463) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6012886 with h | h
  · exact window_general (p := 5972557) (q := 3461) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6019816 with h | h
  · exact window_general (p := 6007207) (q := 3467) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6026752 with h | h
  · exact window_general (p := 6014147) (q := 3469) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6033682 with h | h
  · exact window_general (p := 6007217) (q := 3469) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6040616 with h | h
  · exact window_general (p := 6000283) (q := 3469) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6047546 with h | h
  · exact window_general (p := 5993353) (q := 3469) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6054472 with h | h
  · exact window_general (p := 5986427) (q := 3469) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6061380 with h | h
  · exact window_general (p := 5965643) (q := 3467) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6068314 with h | h
  · exact window_general (p := 5958709) (q := 3467) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6075250 with h | h
  · exact window_general (p := 5965649) (q := 3469) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6082156 with h | h
  · exact window_general (p := 5944867) (q := 3467) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6089066 with h | h
  · exact window_general (p := 5951833) (q := 3469) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6095992 with h | h
  · exact window_general (p := 5944907) (q := 3469) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6102960 with h | h
  · exact window_general (p := 6091103) (q := 3491) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6109926 with h | h
  · exact window_general (p := 6084137) (q := 3491) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6116896 with h | h
  · exact window_general (p := 6077167) (q := 3491) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6123876 with h | h
  · exact window_general (p := 6070187) (q := 3491) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6130868 with h | h
  · exact window_general (p := 6119131) (q := 3499) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6137852 with h | h
  · exact window_general (p := 6112147) (q := 3499) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6144850 with h | h
  · exact window_general (p := 6105149) (q := 3499) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6151846 with h | h
  · exact window_general (p := 6098153) (q := 3499) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6158812 with h | h
  · exact window_general (p := 6035251) (q := 3491) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6165808 with h | h
  · exact window_general (p := 6084191) (q := 3499) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6172814 with h | h
  · exact window_general (p := 6161329) (q := 3511) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6179810 with h | h
  · exact window_general (p := 6154333) (q := 3511) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6186806 with h | h
  · exact window_general (p := 6063193) (q := 3499) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6193840 with h | h
  · exact window_general (p := 6182483) (q := 3517) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6200852 with h | h
  · exact window_general (p := 6133291) (q := 3511) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6207866 with h | h
  · exact window_general (p := 6168457) (q := 3517) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6214892 with h | h
  · exact window_general (p := 6161431) (q := 3517) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6221920 with h | h
  · exact window_general (p := 6154403) (q := 3517) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6228972 with h | h
  · exact window_general (p := 6217811) (q := 3527) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6236008 with h | h
  · exact window_general (p := 6224891) (q := 3529) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6243040 with h | h
  · exact window_general (p := 6217859) (q := 3529) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6250102 with h | h
  · exact window_general (p := 6239053) (q := 3533) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6257158 with h | h
  · exact window_general (p := 6203741) (q := 3529) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6264196 with h | h
  · exact window_general (p := 6196703) (q := 3529) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6271260 with h | h
  · exact window_general (p := 6260339) (q := 3539) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6278332 with h | h
  · exact window_general (p := 6253267) (q := 3539) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6285386 with h | h
  · exact window_general (p := 6260377) (q := 3541) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6292462 with h | h
  · exact window_general (p := 6253301) (q := 3541) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  exact window_general (p := 6288749) (q := 3547) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)

theorem cov_6299555_6658474 (n : ℕ) (hlo : 6299555 ≤ n) (hhi : n ≤ 6658474) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  rcases le_or_gt n 6306646 with h | h
  · exact window_general (p := 6281657) (q := 3547) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6313726 with h | h
  · exact window_general (p := 6274577) (q := 3547) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6320812 with h | h
  · exact window_general (p := 6267491) (q := 3547) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6327892 with h | h
  · exact window_general (p := 6260411) (q := 3547) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6334992 with h | h
  · exact window_general (p := 6324371) (q := 3557) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6342082 with h | h
  · exact window_general (p := 6331517) (q := 3559) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6349198 with h | h
  · exact window_general (p := 6324401) (q := 3559) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6356306 with h | h
  · exact window_general (p := 6317293) (q := 3559) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6363418 with h | h
  · exact window_general (p := 6310181) (q := 3559) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6370528 with h | h
  · exact window_general (p := 6303071) (q := 3559) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6377636 with h | h
  · exact window_general (p := 6295963) (q := 3559) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6384742 with h | h
  · exact window_general (p := 6288857) (q := 3559) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6391882 with h | h
  · exact window_general (p := 6367301) (q := 3571) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6399022 with h | h
  · exact window_general (p := 6360161) (q := 3571) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6406162 with h | h
  · exact window_general (p := 6353021) (q := 3571) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6413300 with h | h
  · exact window_general (p := 6345883) (q := 3571) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6420456 with h | h
  · exact window_general (p := 6410267) (q := 3581) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6427604 with h | h
  · exact window_general (p := 6417451) (q := 3583) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6434752 with h | h
  · exact window_general (p := 6410303) (q := 3583) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6441914 with h | h
  · exact window_general (p := 6403141) (q := 3583) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6449074 with h | h
  · exact window_general (p := 6395981) (q := 3583) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6456236 with h | h
  · exact window_general (p := 6388819) (q := 3583) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6463408 with h | h
  · exact window_general (p := 6453427) (q := 3593) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6470592 with h | h
  · exact window_general (p := 6446243) (q := 3593) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6477772 with h | h
  · exact window_general (p := 6439063) (q := 3593) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6484944 with h | h
  · exact window_general (p := 6431891) (q := 3593) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6492112 with h | h
  · exact window_general (p := 6424723) (q := 3593) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6499282 with h | h
  · exact window_general (p := 6417553) (q := 3593) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6506444 with h | h
  · exact window_general (p := 6338611) (q := 3583) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6513652 with h | h
  · exact window_general (p := 6504011) (q := 3607) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6520864 with h | h
  · exact window_general (p := 6496799) (q := 3607) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6528064 with h | h
  · exact window_general (p := 6489599) (q := 3607) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6535288 with h | h
  · exact window_general (p := 6525707) (q := 3613) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6542506 with h | h
  · exact window_general (p := 6518489) (q := 3613) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6549736 with h | h
  · exact window_general (p := 6540187) (q := 3617) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6556962 with h | h
  · exact window_general (p := 6532961) (q := 3617) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6564172 with h | h
  · exact window_general (p := 6525751) (q := 3617) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6571386 with h | h
  · exact window_general (p := 6518537) (q := 3617) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6578608 with h | h
  · exact window_general (p := 6554767) (q := 3623) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6585846 with h | h
  · exact window_general (p := 6547529) (q := 3623) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6593082 with h | h
  · exact window_general (p := 6540293) (q := 3623) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6600334 with h | h
  · exact window_general (p := 6591089) (q := 3631) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6607592 with h | h
  · exact window_general (p := 6583831) (q := 3631) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6614852 with h | h
  · exact window_general (p := 6576571) (q := 3631) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6622124 with h | h
  · exact window_general (p := 6612919) (q := 3637) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6629390 with h | h
  · exact window_general (p := 6605653) (q := 3637) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6636656 with h | h
  · exact window_general (p := 6598387) (q := 3637) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6643936 with h | h
  · exact window_general (p := 6634799) (q := 3643) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6651196 with h | h
  · exact window_general (p := 6583847) (q := 3637) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  exact window_general (p := 6620261) (q := 3643) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)

theorem cov_6658475_7027300 (n : ℕ) (hlo : 6658475 ≤ n) (hhi : n ≤ 7027300) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  rcases le_or_gt n 6665756 with h | h
  · exact window_general (p := 6612979) (q := 3643) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6673042 with h | h
  · exact window_general (p := 6605693) (q := 3643) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6680324 with h | h
  · exact window_general (p := 6598411) (q := 3643) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6687596 with h | h
  · exact window_general (p := 6547447) (q := 3637) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6694882 with h | h
  · exact window_general (p := 6583853) (q := 3643) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6702186 with h | h
  · exact window_general (p := 6693413) (q := 3659) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6709492 with h | h
  · exact window_general (p := 6686107) (q := 3659) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6716802 with h | h
  · exact window_general (p := 6678797) (q := 3659) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6724098 with h | h
  · exact window_general (p := 6671501) (q := 3659) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6731400 with h | h
  · exact window_general (p := 6664199) (q := 3659) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6738712 with h | h
  · exact window_general (p := 6656887) (q := 3659) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6746052 with h | h
  · exact window_general (p := 6737531) (q := 3671) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6753386 with h | h
  · exact window_general (p := 6744889) (q := 3673) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6760718 with h | h
  · exact window_general (p := 6737557) (q := 3673) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6768064 with h | h
  · exact window_general (p := 6759619) (q := 3677) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6775404 with h | h
  · exact window_general (p := 6752279) (q := 3677) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6782752 with h | h
  · exact window_general (p := 6744931) (q := 3677) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6790102 with h | h
  · exact window_general (p := 6737581) (q := 3677) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6797430 with h | h
  · exact window_general (p := 6730253) (q := 3677) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6804784 with h | h
  · exact window_general (p := 6722899) (q := 3677) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6812116 with h | h
  · exact window_general (p := 6715567) (q := 3677) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6819494 with h | h
  · exact window_general (p := 6811369) (q := 3691) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6826876 with h | h
  · exact window_general (p := 6803987) (q := 3691) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6834232 with h | h
  · exact window_general (p := 6796631) (q := 3691) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6841612 with h | h
  · exact window_general (p := 6833591) (q := 3697) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6848972 with h | h
  · exact window_general (p := 6781891) (q := 3691) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6856354 with h | h
  · exact window_general (p := 6848449) (q := 3701) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6863746 with h | h
  · exact window_general (p := 6841057) (q := 3701) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6871140 with h | h
  · exact window_general (p := 6833663) (q := 3701) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6878532 with h | h
  · exact window_general (p := 6826271) (q := 3701) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6885932 with h | h
  · exact window_general (p := 6878167) (q := 3709) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6893348 with h | h
  · exact window_general (p := 6870751) (q := 3709) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6900766 with h | h
  · exact window_general (p := 6863333) (q := 3709) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6908176 with h | h
  · exact window_general (p := 6855923) (q := 3709) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6915590 with h | h
  · exact window_general (p := 6848509) (q := 3709) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6923028 with h | h
  · exact window_general (p := 6915371) (q := 3719) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6930450 with h | h
  · exact window_general (p := 6907949) (q := 3719) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6937872 with h | h
  · exact window_general (p := 6900527) (q := 3719) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6945280 with h | h
  · exact window_general (p := 6893119) (q := 3719) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6952732 with h | h
  · exact window_general (p := 6945251) (q := 3727) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6960170 with h | h
  · exact window_general (p := 6937813) (q := 3727) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6967616 with h | h
  · exact window_general (p := 6930367) (q := 3727) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6975062 with h | h
  · exact window_general (p := 6922921) (q := 3727) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6982528 with h | h
  · exact window_general (p := 6960227) (q := 3733) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6989966 with h | h
  · exact window_general (p := 6952789) (q := 3733) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 6997426 with h | h
  · exact window_general (p := 6945329) (q := 3733) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7004878 with h | h
  · exact window_general (p := 6982721) (q := 3739) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7012352 with h | h
  · exact window_general (p := 6975247) (q := 3739) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7019830 with h | h
  · exact window_general (p := 6967769) (q := 3739) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  exact window_general (p := 6960299) (q := 3739) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)

theorem cov_7027301_7405656 (n : ℕ) (hlo : 7027301 ≤ n) (hhi : n ≤ 7405656) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  rcases le_or_gt n 7034750 with h | h
  · exact window_general (p := 6952849) (q := 3739) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7042202 with h | h
  · exact window_general (p := 6945397) (q := 3739) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7049680 with h | h
  · exact window_general (p := 6937919) (q := 3739) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7057138 with h | h
  · exact window_general (p := 6930461) (q := 3739) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7064600 with h | h
  · exact window_general (p := 6922999) (q := 3739) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7072078 with h | h
  · exact window_general (p := 6915521) (q := 3739) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7079552 with h | h
  · exact window_general (p := 6908047) (q := 3739) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7087062 with h | h
  · exact window_general (p := 7065581) (q := 3761) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7094584 with h | h
  · exact window_general (p := 7058059) (q := 3761) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7102090 with h | h
  · exact window_general (p := 7050553) (q := 3761) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7109602 with h | h
  · exact window_general (p := 7043041) (q := 3761) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7117138 with h | h
  · exact window_general (p := 7095761) (q := 3769) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7124668 with h | h
  · exact window_general (p := 7088231) (q := 3769) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7132198 with h | h
  · exact window_general (p := 7080701) (q := 3769) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7139706 with h | h
  · exact window_general (p := 7012937) (q := 3761) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7147228 with h | h
  · exact window_general (p := 7065671) (q := 3769) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7154758 with h | h
  · exact window_general (p := 7058141) (q := 3769) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7162290 with h | h
  · exact window_general (p := 7126109) (q := 3779) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7169822 with h | h
  · exact window_general (p := 7043077) (q := 3769) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7177380 with h | h
  · exact window_general (p := 7111019) (q := 3779) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7184938 with h | h
  · exact window_general (p := 7103461) (q := 3779) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7192482 with h | h
  · exact window_general (p := 7095917) (q := 3779) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7200040 with h | h
  · exact window_general (p := 7088359) (q := 3779) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7207622 with h | h
  · exact window_general (p := 7186813) (q := 3793) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7215202 with h | h
  · exact window_general (p := 7179233) (q := 3793) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7222786 with h | h
  · exact window_general (p := 7202017) (q := 3797) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7230376 with h | h
  · exact window_general (p := 7194427) (q := 3797) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7237962 with h | h
  · exact window_general (p := 7186841) (q := 3797) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7245546 with h | h
  · exact window_general (p := 7224869) (q := 3803) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7253148 with h | h
  · exact window_general (p := 7217267) (q := 3803) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7260748 with h | h
  · exact window_general (p := 7209667) (q := 3803) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7268338 with h | h
  · exact window_general (p := 7202077) (q := 3803) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7275928 with h | h
  · exact window_general (p := 7194487) (q := 3803) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7283518 with h | h
  · exact window_general (p := 7186897) (q := 3803) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7291114 with h | h
  · exact window_general (p := 7179301) (q := 3803) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7298704 with h | h
  · exact window_general (p := 7171711) (q := 3803) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7306308 with h | h
  · exact window_general (p := 7164107) (q := 3803) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7313920 with h | h
  · exact window_general (p := 7293763) (q := 3821) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7321552 with h | h
  · exact window_general (p := 7301423) (q := 3823) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7329156 with h | h
  · exact window_general (p := 7278527) (q := 3821) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7336802 with h | h
  · exact window_general (p := 7286173) (q := 3823) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7344448 with h | h
  · exact window_general (p := 7278527) (q := 3823) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7352084 with h | h
  · exact window_general (p := 7270891) (q := 3823) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7359732 with h | h
  · exact window_general (p := 7339823) (q := 3833) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7367394 with h | h
  · exact window_general (p := 7332161) (q := 3833) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7375038 with h | h
  · exact window_general (p := 7324517) (q := 3833) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7382698 with h | h
  · exact window_general (p := 7316857) (q := 3833) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7390348 with h | h
  · exact window_general (p := 7309207) (q := 3833) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7397994 with h | h
  · exact window_general (p := 7301561) (q := 3833) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  exact window_general (p := 7293899) (q := 3833) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)

theorem cov_7405657_7794266 (n : ℕ) (hlo : 7405657 ≤ n) (hhi : n ≤ 7794266) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  rcases le_or_gt n 7413326 with h | h
  · exact window_general (p := 7393777) (q := 3847) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7421014 with h | h
  · exact window_general (p := 7386089) (q := 3847) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7428712 with h | h
  · exact window_general (p := 7409191) (q := 3851) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7436398 with h | h
  · exact window_general (p := 7416917) (q := 3853) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7444084 with h | h
  · exact window_general (p := 7393819) (q := 3851) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7451782 with h | h
  · exact window_general (p := 7401533) (q := 3853) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7459466 with h | h
  · exact window_general (p := 7393849) (q := 3853) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7467166 with h | h
  · exact window_general (p := 7386149) (q := 3853) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7474866 with h | h
  · exact window_general (p := 7455629) (q := 3863) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7482592 with h | h
  · exact window_general (p := 7447903) (q := 3863) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7490308 with h | h
  · exact window_general (p := 7440187) (q := 3863) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7498024 with h | h
  · exact window_general (p := 7432471) (q := 3863) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7505734 with h | h
  · exact window_general (p := 7424761) (q := 3863) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7513458 with h | h
  · exact window_general (p := 7417037) (q := 3863) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7521178 with h | h
  · exact window_general (p := 7409317) (q := 3863) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7528896 with h | h
  · exact window_general (p := 7401599) (q := 3863) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7536646 with h | h
  · exact window_general (p := 7502237) (q := 3877) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7544406 with h | h
  · exact window_general (p := 7525517) (q := 3881) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7552162 with h | h
  · exact window_general (p := 7517761) (q := 3881) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7559912 with h | h
  · exact window_general (p := 7478971) (q := 3877) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7567674 with h | h
  · exact window_general (p := 7502249) (q := 3881) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7575448 with h | h
  · exact window_general (p := 7556651) (q := 3889) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7583216 with h | h
  · exact window_general (p := 7548883) (q := 3889) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7590988 with h | h
  · exact window_general (p := 7541111) (q := 3889) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7598756 with h | h
  · exact window_general (p := 7533343) (q := 3889) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7606528 with h | h
  · exact window_general (p := 7525571) (q := 3889) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7614286 with h | h
  · exact window_general (p := 7517813) (q := 3889) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7622046 with h | h
  · exact window_general (p := 7447877) (q := 3881) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7629808 with h | h
  · exact window_general (p := 7502291) (q := 3889) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7637582 with h | h
  · exact window_general (p := 7494517) (q := 3889) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7645372 with h | h
  · exact window_general (p := 7627091) (q := 3907) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7653172 with h | h
  · exact window_general (p := 7619291) (q := 3907) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7660984 with h | h
  · exact window_general (p := 7611479) (q := 3907) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7668790 with h | h
  · exact window_general (p := 7634953) (q := 3911) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7676602 with h | h
  · exact window_general (p := 7627141) (q := 3911) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7684410 with h | h
  · exact window_general (p := 7666313) (q := 3917) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7692220 with h | h
  · exact window_general (p := 7674179) (q := 3919) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7700050 with h | h
  · exact window_general (p := 7666349) (q := 3919) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7707894 with h | h
  · exact window_general (p := 7689881) (q := 3923) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7715722 with h | h
  · exact window_general (p := 7682053) (q := 3923) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7723566 with h | h
  · exact window_general (p := 7674209) (q := 3923) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7731420 with h | h
  · exact window_general (p := 7713479) (q := 3929) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7739276 with h | h
  · exact window_general (p := 7721347) (q := 3931) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7747132 with h | h
  · exact window_general (p := 7713491) (q := 3931) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7754972 with h | h
  · exact window_general (p := 7705651) (q := 3931) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7762820 with h | h
  · exact window_general (p := 7697803) (q := 3931) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7770680 with h | h
  · exact window_general (p := 7689943) (q := 3931) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7778540 with h | h
  · exact window_general (p := 7682083) (q := 3931) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7786406 with h | h
  · exact window_general (p := 7768729) (q := 3943) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  exact window_general (p := 7666357) (q := 3931) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)

theorem cov_7794267_8192680 (n : ℕ) (hlo : 7794267 ≤ n) (hhi : n ≤ 8192680) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  rcases le_or_gt n 7802154 with h | h
  · exact window_general (p := 7784549) (q := 3947) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7810030 with h | h
  · exact window_general (p := 7776673) (q := 3947) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7817896 with h | h
  · exact window_general (p := 7737239) (q := 3943) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7825776 with h | h
  · exact window_general (p := 7760927) (q := 3947) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7833670 with h | h
  · exact window_general (p := 7753033) (q := 3947) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7841556 with h | h
  · exact window_general (p := 7745147) (q := 3947) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7849440 with h | h
  · exact window_general (p := 7737263) (q := 3947) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7857334 with h | h
  · exact window_general (p := 7729369) (q := 3947) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7865226 with h | h
  · exact window_general (p := 7721477) (q := 3947) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7873092 with h | h
  · exact window_general (p := 7713611) (q := 3947) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7881026 with h | h
  · exact window_general (p := 7863997) (q := 3967) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7888934 with h | h
  · exact window_general (p := 7856089) (q := 3967) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7896860 with h | h
  · exact window_general (p := 7848163) (q := 3967) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7904770 with h | h
  · exact window_general (p := 7840253) (q := 3967) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7912696 with h | h
  · exact window_general (p := 7832327) (q := 3967) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7920616 with h | h
  · exact window_general (p := 7824407) (q := 3967) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7928546 with h | h
  · exact window_general (p := 7816477) (q := 3967) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7936444 with h | h
  · exact window_general (p := 7808579) (q := 3967) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7944376 with h | h
  · exact window_general (p := 7800647) (q := 3967) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7952300 with h | h
  · exact window_general (p := 7792723) (q := 3967) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7960216 with h | h
  · exact window_general (p := 7784807) (q := 3967) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7968186 with h | h
  · exact window_general (p := 7951913) (q := 3989) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7976148 with h | h
  · exact window_general (p := 7943951) (q := 3989) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7984120 with h | h
  · exact window_general (p := 7935979) (q := 3989) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 7992096 with h | h
  · exact window_general (p := 7928003) (q := 3989) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8000056 with h | h
  · exact window_general (p := 7920043) (q := 3989) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8008032 with h | h
  · exact window_general (p := 7912067) (q := 3989) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8016010 with h | h
  · exact window_general (p := 7999993) (q := 4001) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8024006 with h | h
  · exact window_general (p := 8008009) (q := 4003) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8032006 with h | h
  · exact window_general (p := 8000009) (q := 4003) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8040016 with h | h
  · exact window_general (p := 8024047) (q := 4007) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8048026 with h | h
  · exact window_general (p := 8016037) (q := 4007) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8056028 with h | h
  · exact window_general (p := 7975987) (q := 4003) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8064054 with h | h
  · exact window_general (p := 8048141) (q := 4013) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8072074 with h | h
  · exact window_general (p := 8040121) (q := 4013) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8080092 with h | h
  · exact window_general (p := 8032103) (q := 4013) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8088130 with h | h
  · exact window_general (p := 8072269) (q := 4019) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8096170 with h | h
  · exact window_general (p := 8080313) (q := 4021) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8104192 with h | h
  · exact window_general (p := 8072291) (q := 4021) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8112226 with h | h
  · exact window_general (p := 8064257) (q := 4021) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8120264 with h | h
  · exact window_general (p := 8056219) (q := 4021) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8128304 with h | h
  · exact window_general (p := 8096479) (q := 4027) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8136334 with h | h
  · exact window_general (p := 8088449) (q := 4027) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8144372 with h | h
  · exact window_general (p := 8080411) (q := 4027) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8152426 with h | h
  · exact window_general (p := 8072357) (q := 4027) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8160470 with h | h
  · exact window_general (p := 8064313) (q := 4027) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8168524 with h | h
  · exact window_general (p := 8056259) (q := 4027) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8176576 with h | h
  · exact window_general (p := 8048207) (q := 4027) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8184626 with h | h
  · exact window_general (p := 8040157) (q := 4027) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  exact window_general (p := 8032103) (q := 4027) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)

theorem cov_8192681_8601252 (n : ℕ) (hlo : 8192681 ≤ n) (hhi : n ≤ 8601252) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  rcases le_or_gt n 8200726 with h | h
  · exact window_general (p := 8024057) (q := 4027) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8208802 with h | h
  · exact window_general (p := 8193697) (q := 4049) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8216902 with h | h
  · exact window_general (p := 8201801) (q := 4051) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8225002 with h | h
  · exact window_general (p := 8193701) (q := 4051) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8233100 with h | h
  · exact window_general (p := 8185603) (q := 4051) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8241202 with h | h
  · exact window_general (p := 8226161) (q := 4057) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8249306 with h | h
  · exact window_general (p := 8218057) (q := 4057) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8257412 with h | h
  · exact window_general (p := 8209951) (q := 4057) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8265524 with h | h
  · exact window_general (p := 8201839) (q := 4057) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8273630 with h | h
  · exact window_general (p := 8193733) (q := 4057) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8281730 with h | h
  · exact window_general (p := 8185633) (q := 4057) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8289824 with h | h
  · exact window_general (p := 8177539) (q := 4057) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8297932 with h | h
  · exact window_general (p := 8169431) (q := 4057) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8306076 with h | h
  · exact window_general (p := 8291399) (q := 4073) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8314218 with h | h
  · exact window_general (p := 8283257) (q := 4073) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8322358 with h | h
  · exact window_general (p := 8275117) (q := 4073) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8330512 with h | h
  · exact window_general (p := 8315887) (q := 4079) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8338648 with h | h
  · exact window_general (p := 8307751) (q := 4079) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8346792 with h | h
  · exact window_general (p := 8299607) (q := 4079) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8354938 with h | h
  · exact window_general (p := 8242537) (q := 4073) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8363070 with h | h
  · exact window_general (p := 8283329) (q := 4079) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8371222 with h | h
  · exact window_general (p := 8275177) (q := 4079) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8379402 with h | h
  · exact window_general (p := 8365061) (q := 4091) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8387576 with h | h
  · exact window_general (p := 8373259) (q := 4093) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8395754 with h | h
  · exact window_general (p := 8365081) (q := 4093) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8403916 with h | h
  · exact window_general (p := 8356919) (q := 4093) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8412112 with h | h
  · exact window_general (p := 8397887) (q := 4099) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8420308 with h | h
  · exact window_general (p := 8389691) (q := 4099) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8428502 with h | h
  · exact window_general (p := 8381497) (q := 4099) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8436670 with h | h
  · exact window_general (p := 8373329) (q := 4099) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8444842 with h | h
  · exact window_general (p := 8365157) (q := 4099) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8453038 with h | h
  · exact window_general (p := 8356961) (q := 4099) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8461256 with h | h
  · exact window_general (p := 8447287) (q := 4111) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8469470 with h | h
  · exact window_general (p := 8439073) (q := 4111) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8477660 with h | h
  · exact window_general (p := 8332339) (q := 4099) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8485856 with h | h
  · exact window_general (p := 8324143) (q := 4099) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8494064 with h | h
  · exact window_general (p := 8414479) (q := 4111) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8502260 with h | h
  · exact window_general (p := 8406283) (q := 4111) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8510476 with h | h
  · exact window_general (p := 8398067) (q := 4111) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8518666 with h | h
  · exact window_general (p := 8389877) (q := 4111) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8526916 with h | h
  · exact window_general (p := 8513467) (q := 4127) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8535160 with h | h
  · exact window_general (p := 8521739) (q := 4129) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8543402 with h | h
  · exact window_general (p := 8513497) (q := 4129) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8551652 with h | h
  · exact window_general (p := 8505247) (q := 4129) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8559918 with h | h
  · exact window_general (p := 8530037) (q := 4133) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8568174 with h | h
  · exact window_general (p := 8521781) (q := 4133) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8576428 with h | h
  · exact window_general (p := 8563171) (q := 4139) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8584698 with h | h
  · exact window_general (p := 8554901) (q := 4139) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8592976 with h | h
  · exact window_general (p := 8546623) (q := 4139) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  exact window_general (p := 8538347) (q := 4139) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)

theorem cov_8601253_9019712 (n : ℕ) (hlo : 8601253 ≤ n) (hhi : n ≤ 9019712) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  rcases le_or_gt n 8609512 with h | h
  · exact window_general (p := 8480443) (q := 4133) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8617786 with h | h
  · exact window_general (p := 8521813) (q := 4139) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8626062 with h | h
  · exact window_general (p := 8513537) (q := 4139) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8634338 with h | h
  · exact window_general (p := 8621377) (q := 4153) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8642626 with h | h
  · exact window_general (p := 8613089) (q := 4153) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8650930 with h | h
  · exact window_general (p := 8638033) (q := 4157) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8659238 with h | h
  · exact window_general (p := 8646361) (q := 4159) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8667556 with h | h
  · exact window_general (p := 8638043) (q := 4159) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8675860 with h | h
  · exact window_general (p := 8629739) (q := 4159) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8684170 with h | h
  · exact window_general (p := 8621429) (q := 4159) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8692472 with h | h
  · exact window_general (p := 8613127) (q := 4159) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8700790 with h | h
  · exact window_general (p := 8604809) (q := 4159) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8709086 with h | h
  · exact window_general (p := 8596513) (q := 4159) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8717392 with h | h
  · exact window_general (p := 8588207) (q := 4159) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8725708 with h | h
  · exact window_general (p := 8579891) (q := 4159) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8734052 with h | h
  · exact window_general (p := 8721631) (q := 4177) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8742392 with h | h
  · exact window_general (p := 8713291) (q := 4177) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8750746 with h | h
  · exact window_general (p := 8704937) (q := 4177) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8759080 with h | h
  · exact window_general (p := 8696603) (q := 4177) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8767424 with h | h
  · exact window_general (p := 8688259) (q := 4177) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8775740 with h | h
  · exact window_general (p := 8679943) (q := 4177) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8784094 with h | h
  · exact window_general (p := 8671589) (q := 4177) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8792422 with h | h
  · exact window_general (p := 8663261) (q := 4177) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8800766 with h | h
  · exact window_general (p := 8654917) (q := 4177) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8809112 with h | h
  · exact window_general (p := 8646571) (q := 4177) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8817464 with h | h
  · exact window_general (p := 8638219) (q := 4177) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8825816 with h | h
  · exact window_general (p := 8629867) (q := 4177) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8834216 with h | h
  · exact window_general (p := 8822587) (q := 4201) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8842612 with h | h
  · exact window_general (p := 8814191) (q := 4201) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8850986 with h | h
  · exact window_general (p := 8805817) (q := 4201) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8859382 with h | h
  · exact window_general (p := 8797421) (q := 4201) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8867782 with h | h
  · exact window_general (p := 8789021) (q := 4201) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8876202 with h | h
  · exact window_general (p := 8864741) (q := 4211) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8884614 with h | h
  · exact window_general (p := 8856329) (q := 4211) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8893036 with h | h
  · exact window_general (p := 8847907) (q := 4211) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8901454 with h | h
  · exact window_general (p := 8890069) (q := 4217) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8909878 with h | h
  · exact window_general (p := 8898521) (q := 4219) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8918306 with h | h
  · exact window_general (p := 8890093) (q := 4219) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8926718 with h | h
  · exact window_general (p := 8881681) (q := 4219) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8935148 with h | h
  · exact window_general (p := 8873251) (q := 4219) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8943586 with h | h
  · exact window_general (p := 8864813) (q := 4219) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8952036 with h | h
  · exact window_general (p := 8940863) (q := 4229) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8960492 with h | h
  · exact window_general (p := 8949331) (q := 4231) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8968934 with h | h
  · exact window_general (p := 8940889) (q := 4231) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8977376 with h | h
  · exact window_general (p := 8932447) (q := 4231) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8985836 with h | h
  · exact window_general (p := 8923987) (q := 4231) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 8994286 with h | h
  · exact window_general (p := 8915537) (q := 4231) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9002764 with h | h
  · exact window_general (p := 8991799) (q := 4241) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9011246 with h | h
  · exact window_general (p := 9000289) (q := 4243) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  exact window_general (p := 8991823) (q := 4243) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)

theorem cov_9019713_9448066 (n : ℕ) (hlo : 9019713 ≤ n) (hhi : n ≤ 9448066) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  rcases le_or_gt n 9028192 with h | h
  · exact window_general (p := 8983343) (q := 4243) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9036658 with h | h
  · exact window_general (p := 8974877) (q := 4243) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9045124 with h | h
  · exact window_general (p := 8966411) (q := 4243) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9053626 with h | h
  · exact window_general (p := 9042889) (q := 4253) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9062122 with h | h
  · exact window_general (p := 9034393) (q := 4253) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9070626 with h | h
  · exact window_general (p := 9025889) (q := 4253) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9079128 with h | h
  · exact window_general (p := 9068471) (q := 4259) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9087650 with h | h
  · exact window_general (p := 9076993) (q := 4261) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9096172 with h | h
  · exact window_general (p := 9068471) (q := 4261) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9104692 with h | h
  · exact window_general (p := 9059951) (q := 4261) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9113210 with h | h
  · exact window_general (p := 9051433) (q := 4261) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9121712 with h | h
  · exact window_general (p := 9042931) (q := 4261) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9130254 with h | h
  · exact window_general (p := 9119729) (q := 4271) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9138778 with h | h
  · exact window_general (p := 9128297) (q := 4273) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9147308 with h | h
  · exact window_general (p := 9119767) (q := 4273) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9155846 with h | h
  · exact window_general (p := 9111229) (q := 4273) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9164386 with h | h
  · exact window_general (p := 9102689) (q := 4273) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9172922 with h | h
  · exact window_general (p := 9094153) (q := 4273) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9181468 with h | h
  · exact window_general (p := 9085607) (q := 4273) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9190032 with h | h
  · exact window_general (p := 9162623) (q := 4283) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9198564 with h | h
  · exact window_general (p := 9154091) (q := 4283) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9207138 with h | h
  · exact window_general (p := 9196961) (q := 4289) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9215706 with h | h
  · exact window_general (p := 9188393) (q := 4289) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9224272 with h | h
  · exact window_general (p := 9179827) (q := 4289) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9232840 with h | h
  · exact window_general (p := 9171259) (q := 4289) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9241432 with h | h
  · exact window_general (p := 9231371) (q := 4297) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9250022 with h | h
  · exact window_general (p := 9222781) (q := 4297) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9258614 with h | h
  · exact window_general (p := 9214189) (q := 4297) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9267202 with h | h
  · exact window_general (p := 9205601) (q := 4297) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9275794 with h | h
  · exact window_general (p := 9197009) (q := 4297) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9284380 with h | h
  · exact window_general (p := 9188423) (q := 4297) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9292966 with h | h
  · exact window_general (p := 9179837) (q := 4297) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9301544 with h | h
  · exact window_general (p := 9171259) (q := 4297) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9310124 with h | h
  · exact window_general (p := 9162679) (q := 4297) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9318712 with h | h
  · exact window_general (p := 9154091) (q := 4297) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9327284 with h | h
  · exact window_general (p := 9145519) (q := 4297) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9335866 with h | h
  · exact window_general (p := 9136937) (q := 4297) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9344436 with h | h
  · exact window_general (p := 9059663) (q := 4289) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9353024 with h | h
  · exact window_general (p := 9119779) (q := 4297) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9361604 with h | h
  · exact window_general (p := 9111199) (q := 4297) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9370216 with h | h
  · exact window_general (p := 9361367) (q := 4327) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9378860 with h | h
  · exact window_general (p := 9352723) (q := 4327) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9387506 with h | h
  · exact window_general (p := 9344077) (q := 4327) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9396122 with h | h
  · exact window_general (p := 9335461) (q := 4327) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9404732 with h | h
  · exact window_general (p := 9326851) (q := 4327) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9413374 with h | h
  · exact window_general (p := 9318209) (q := 4327) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9422034 with h | h
  · exact window_general (p := 9396209) (q := 4337) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9430712 with h | h
  · exact window_general (p := 9404887) (q := 4339) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9439390 with h | h
  · exact window_general (p := 9396209) (q := 4339) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  exact window_general (p := 9387533) (q := 4339) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)

theorem cov_9448067_9886312 (n : ℕ) (hlo : 9448067 ≤ n) (hhi : n ≤ 9886312) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  rcases le_or_gt n 9456730 with h | h
  · exact window_general (p := 9378869) (q := 4339) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9465398 with h | h
  · exact window_general (p := 9370201) (q := 4339) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9474072 with h | h
  · exact window_general (p := 9448427) (q := 4349) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9482742 with h | h
  · exact window_general (p := 9439757) (q := 4349) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9491430 with h | h
  · exact window_general (p := 9431069) (q := 4349) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9500110 with h | h
  · exact window_general (p := 9422389) (q := 4349) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9508816 with h | h
  · exact window_general (p := 9483347) (q := 4357) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9517526 with h | h
  · exact window_general (p := 9474637) (q := 4357) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9526232 with h | h
  · exact window_general (p := 9465931) (q := 4357) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9534952 with h | h
  · exact window_general (p := 9509543) (q := 4363) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9543664 with h | h
  · exact window_general (p := 9500831) (q := 4363) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9552356 with h | h
  · exact window_general (p := 9492139) (q := 4363) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9561074 with h | h
  · exact window_general (p := 9483421) (q := 4363) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9569798 with h | h
  · exact window_general (p := 9474697) (q := 4363) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9578532 with h | h
  · exact window_general (p := 9553343) (q := 4373) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9587254 with h | h
  · exact window_general (p := 9457241) (q := 4363) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9595954 with h | h
  · exact window_general (p := 9396209) (q := 4357) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9604696 with h | h
  · exact window_general (p := 9527179) (q := 4373) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9613404 with h | h
  · exact window_general (p := 9518471) (q := 4373) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9622146 with h | h
  · exact window_general (p := 9509729) (q := 4373) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9630892 with h | h
  · exact window_general (p := 9500983) (q := 4373) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9639622 with h | h
  · exact window_general (p := 9492253) (q := 4373) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9648338 with h | h
  · exact window_general (p := 9396157) (q := 4363) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9657112 with h | h
  · exact window_general (p := 9632551) (q := 4391) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9665892 with h | h
  · exact window_general (p := 9623771) (q := 4391) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9674670 with h | h
  · exact window_general (p := 9614993) (q := 4391) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9683464 with h | h
  · exact window_general (p := 9658939) (q := 4397) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9692254 with h | h
  · exact window_general (p := 9650149) (q := 4397) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9701020 with h | h
  · exact window_general (p := 9641383) (q := 4397) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9709810 with h | h
  · exact window_general (p := 9632593) (q := 4397) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9718572 with h | h
  · exact window_general (p := 9571091) (q := 4391) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9727362 with h | h
  · exact window_general (p := 9615041) (q := 4397) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9736158 with h | h
  · exact window_general (p := 9711941) (q := 4409) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9744976 with h | h
  · exact window_general (p := 9703123) (q := 4409) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9753790 with h | h
  · exact window_general (p := 9694309) (q := 4409) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9762586 with h | h
  · exact window_general (p := 9685513) (q := 4409) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9771400 with h | h
  · exact window_general (p := 9676699) (q := 4409) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9780208 with h | h
  · exact window_general (p := 9667891) (q := 4409) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9789046 with h | h
  · exact window_general (p := 9765037) (q := 4421) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9797888 with h | h
  · exact window_general (p := 9773887) (q := 4423) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9806732 with h | h
  · exact window_general (p := 9765043) (q := 4423) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9815564 with h | h
  · exact window_general (p := 9756211) (q := 4423) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9824392 with h | h
  · exact window_general (p := 9747383) (q := 4423) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9833224 with h | h
  · exact window_general (p := 9738551) (q := 4423) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9842032 with h | h
  · exact window_general (p := 9729743) (q := 4423) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9850874 with h | h
  · exact window_general (p := 9720901) (q := 4423) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9859718 with h | h
  · exact window_general (p := 9712057) (q := 4423) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9868552 with h | h
  · exact window_general (p := 9703223) (q := 4423) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9877430 with h | h
  · exact window_general (p := 9853933) (q := 4441) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  exact window_general (p := 9845051) (q := 4441) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)

theorem cov_9886313_10001986 (n : ℕ) (hlo : 9886313 ≤ n) (hhi : n ≤ 10001986) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  rcases le_or_gt n 9895192 with h | h
  · exact window_general (p := 9836171) (q := 4441) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9904060 with h | h
  · exact window_general (p := 9880643) (q := 4447) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9912950 with h | h
  · exact window_general (p := 9871753) (q := 4447) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9921852 with h | h
  · exact window_general (p := 9898451) (q := 4451) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9930750 with h | h
  · exact window_general (p := 9889553) (q := 4451) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9939636 with h | h
  · exact window_general (p := 9880667) (q := 4451) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9948544 with h | h
  · exact window_general (p := 9925219) (q := 4457) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9957432 with h | h
  · exact window_general (p := 9916331) (q := 4457) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9966340 with h | h
  · exact window_general (p := 9907423) (q := 4457) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9975258 with h | h
  · exact window_general (p := 9952037) (q := 4463) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9984172 with h | h
  · exact window_general (p := 9943123) (q := 4463) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  rcases le_or_gt n 9993076 with h | h
  · exact window_general (p := 9934219) (q := 4463) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)
  exact window_general (p := 9925309) (q := 4463) (by norm_num) (by norm_num) (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num)

/-- The conjecture holds for all `6 ≤ n ≤ 10000000` (window certificates). -/
theorem conj_range_6_1e7 (n : ℕ) (h3 : 6 ≤ n) (hN : n ≤ 10000000) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  rcases le_or_gt n 3784 with h | h
  · exact cov_6_3784 n (by omega) h
  rcases le_or_gt n 16312 with h | h
  · exact cov_3785_16312 n (by omega) h
  rcases le_or_gt n 38414 with h | h
  · exact cov_16313_38414 n (by omega) h
  rcases le_or_gt n 70042 with h | h
  · exact cov_38415_70042 n (by omega) h
  rcases le_or_gt n 111556 with h | h
  · exact cov_70043_111556 n (by omega) h
  rcases le_or_gt n 162558 with h | h
  · exact cov_111557_162558 n (by omega) h
  rcases le_or_gt n 223520 with h | h
  · exact cov_162559_223520 n (by omega) h
  rcases le_or_gt n 294424 with h | h
  · exact cov_223521_294424 n (by omega) h
  rcases le_or_gt n 375024 with h | h
  · exact cov_294425_375024 n (by omega) h
  rcases le_or_gt n 465598 with h | h
  · exact cov_375025_465598 n (by omega) h
  rcases le_or_gt n 566004 with h | h
  · exact cov_465599_566004 n (by omega) h
  rcases le_or_gt n 676174 with h | h
  · exact cov_566005_676174 n (by omega) h
  rcases le_or_gt n 796408 with h | h
  · exact cov_676175_796408 n (by omega) h
  rcases le_or_gt n 926086 with h | h
  · exact cov_796409_926086 n (by omega) h
  rcases le_or_gt n 1065946 with h | h
  · exact cov_926087_1065946 n (by omega) h
  rcases le_or_gt n 1215942 with h | h
  · exact cov_1065947_1215942 n (by omega) h
  rcases le_or_gt n 1375834 with h | h
  · exact cov_1215943_1375834 n (by omega) h
  rcases le_or_gt n 1545464 with h | h
  · exact cov_1375835_1545464 n (by omega) h
  rcases le_or_gt n 1725060 with h | h
  · exact cov_1545465_1725060 n (by omega) h
  rcases le_or_gt n 1914610 with h | h
  · exact cov_1725061_1914610 n (by omega) h
  rcases le_or_gt n 2114062 with h | h
  · exact cov_1914611_2114062 n (by omega) h
  rcases le_or_gt n 2323642 with h | h
  · exact cov_2114063_2323642 n (by omega) h
  rcases le_or_gt n 2542876 with h | h
  · exact cov_2323643_2542876 n (by omega) h
  rcases le_or_gt n 2772142 with h | h
  · exact cov_2542877_2772142 n (by omega) h
  rcases le_or_gt n 3011482 with h | h
  · exact cov_2772143_3011482 n (by omega) h
  rcases le_or_gt n 3260582 with h | h
  · exact cov_3011483_3260582 n (by omega) h
  rcases le_or_gt n 3519670 with h | h
  · exact cov_3260583_3519670 n (by omega) h
  rcases le_or_gt n 3789008 with h | h
  · exact cov_3519671_3789008 n (by omega) h
  rcases le_or_gt n 4067928 with h | h
  · exact cov_3789009_4067928 n (by omega) h
  rcases le_or_gt n 4357062 with h | h
  · exact cov_4067929_4357062 n (by omega) h
  rcases le_or_gt n 4655998 with h | h
  · exact cov_4357063_4655998 n (by omega) h
  rcases le_or_gt n 4964832 with h | h
  · exact cov_4655999_4964832 n (by omega) h
  rcases le_or_gt n 5283428 with h | h
  · exact cov_4964833_5283428 n (by omega) h
  rcases le_or_gt n 5612166 with h | h
  · exact cov_5283429_5612166 n (by omega) h
  rcases le_or_gt n 5950784 with h | h
  · exact cov_5612167_5950784 n (by omega) h
  rcases le_or_gt n 6299554 with h | h
  · exact cov_5950785_6299554 n (by omega) h
  rcases le_or_gt n 6658474 with h | h
  · exact cov_6299555_6658474 n (by omega) h
  rcases le_or_gt n 7027300 with h | h
  · exact cov_6658475_7027300 n (by omega) h
  rcases le_or_gt n 7405656 with h | h
  · exact cov_7027301_7405656 n (by omega) h
  rcases le_or_gt n 7794266 with h | h
  · exact cov_7405657_7794266 n (by omega) h
  rcases le_or_gt n 8192680 with h | h
  · exact cov_7794267_8192680 n (by omega) h
  rcases le_or_gt n 8601252 with h | h
  · exact cov_8192681_8601252 n (by omega) h
  rcases le_or_gt n 9019712 with h | h
  · exact cov_8601253_9019712 n (by omega) h
  rcases le_or_gt n 9448066 with h | h
  · exact cov_9019713_9448066 n (by omega) h
  rcases le_or_gt n 9886312 with h | h
  · exact cov_9448067_9886312 n (by omega) h
  exact cov_9886313_10001986 n (by omega) (by omega)


/-- The conjecture holds for all `3 ≤ n ≤ 10 ^ 7`. -/
theorem conj_upto_1e7 (n : ℕ) (h3 : 3 ≤ n) (hN : n ≤ 10000000) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  rcases le_or_gt n 5 with h | h
  · interval_cases n
    · exact witness_of_prime_block (p := 2) (q := 2) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact witness_of_prime_block (p := 2) (q := 2) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact witness_of_prime_block (p := 2) (q := 2) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
  · exact conj_range_6_1e7 n (by omega) hN

/- ### Conditional reduction to a Legendre-type gap bound -/

/-- **Legendre-type gap hypothesis implies the conjecture** (for `n ≥ 10 ^ 7`; smaller `n` are
covered by the finite verification).  If every interval `[x, x + 2 ⌊√x⌋]` with `2 ≤ x ≤ n`
contains a prime, then `n` has a witness. -/
theorem conj_of_legendre_gap {n : ℕ} (hn : 10000000 ≤ n)
    (H : ∀ x, 2 ≤ x → x ≤ n → ∃ p, p.Prime ∧ x ≤ p ∧ p ≤ x + 2 * Nat.sqrt x) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  -- `a = ⌊√(n+1)⌋`, `s = a + 1`, so `s ^ 2 ≥ n + 2`
  set a := Nat.sqrt (n + 1) with ha
  have ha1 : a * a ≤ n + 1 := Nat.sqrt_le (n + 1)
  have ha2 : n + 1 < (a + 1) * (a + 1) := Nat.lt_succ_sqrt (n + 1)
  have ha_big : 3162 ≤ a := by
    rw [ha, Nat.le_sqrt]; omega
  -- a prime `q` in `[a + 1, a + 1 + 2 ⌊√(a+1)⌋]`
  have hs_le : a + 1 ≤ n := by nlinarith
  obtain ⟨q, hq, hq1, hq2⟩ := H (a + 1) (by omega) hs_le
  set b := Nat.sqrt (a + 1) with hb
  have hb1 : b * b ≤ a + 1 := Nat.sqrt_le (a + 1)
  have hb_small : 50 * b ≤ a := by
    by_contra hcon
    push_neg at hcon
    nlinarith
  have hq_sq : n + 2 ≤ q ^ 2 := by nlinarith
  have hq_up : (q + 1) ^ 2 ≤ 2 * n := by nlinarith
  refine conj_of_gap_bound hq hq_sq hq_up ?_
  intro x hx2 hxn
  obtain ⟨p, hp, hxp, hpx⟩ := H x hx2 hxn
  refine ⟨p, hp, hxp, le_trans hpx ?_⟩
  have : Nat.sqrt x ≤ q := by
    calc Nat.sqrt x ≤ Nat.sqrt n := Nat.sqrt_le_sqrt hxn
      _ ≤ Nat.sqrt (n + 1) := Nat.sqrt_le_sqrt (by omega)
      _ ≤ q := by omega
  omega

/-- **Legendre-type gap hypothesis implies the conjecture** for every `n > 2`. -/
theorem conj_of_legendre (n : ℕ) (hn : n > 2)
    (H : ∀ x, 2 ≤ x → x ≤ n → ∃ p, p.Prime ∧ x ≤ p ∧ p ≤ x + 2 * Nat.sqrt x) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  rcases le_or_gt n 10000000 with h | h
  · exact conj_upto_1e7 n hn h
  · exact conj_of_legendre_gap (by omega) H

/-- If every interval `[x, x + 2 ⌊√x⌋]` (`x ≥ 2`) contains a prime (a form of Legendre's
conjecture), then OEIS A237720 conjecture (ii) holds. -/
theorem conj_of_legendre_global
    (H : ∀ x, 2 ≤ x → ∃ p, p.Prime ∧ x ≤ p ∧ p ≤ x + 2 * Nat.sqrt x) :
    ∀ n, n > 2 → ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime :=
  fun n hn => conj_of_legendre n hn (fun x hx _ => H x hx)

/-- OEIS A237720 Conjecture (ii): For any integer $n > 2$, there is a prime $p < n$ with $\lfloor\sqrt{n+p}\rfloor$ prime. -/
theorem oeis_A237720_conjecture_ii (n : ℕ) (hn : n > 2) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  sorry

theorem oeis_A237720_conjecture_ii.disproof : ¬ (type_of% @oeis_A237720_conjecture_ii) := sorry
